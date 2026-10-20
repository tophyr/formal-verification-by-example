import LakeLevel.Spec.Decimal

/-!
# Spec: command-line syntax and URL safety

docs/02-formal-model.md §2.5, A17, A20.
-/

namespace LakeLevel

/-- `[0-9]{1,9}` -/
def SiteSyntax (s : String) : Prop :=
  1 ≤ s.length ∧ s.length ≤ 9 ∧ ∀ c ∈ s.toList, c.isDigit

/-- `[a-z]{1,32}` -/
def TypeSyntax (s : String) : Prop :=
  1 ≤ s.length ∧ s.length ≤ 32 ∧ ∀ c ∈ s.toList, 'a' ≤ c ∧ c ≤ 'z'

/-- ntfy's own rule, `^[-_A-Za-z0-9]{1,64}$` (checked against ntfy `server/server.go`). -/
def TopicSyntax (s : String) : Prop :=
  1 ≤ s.length ∧ s.length ≤ 64 ∧ ∀ c ∈ s.toList, c.isAlphanum ∨ c = '-' ∨ c = '_'

instance (s : String) : Decidable (SiteSyntax s) := by unfold SiteSyntax; infer_instance
instance (s : String) : Decidable (TypeSyntax s) := by unfold TypeSyntax; infer_instance
instance (s : String) : Decidable (TopicSyntax s) := by unfold TopicSyntax; infer_instance

/-- Every field of a configuration is syntactically valid, and a threshold's
value is exactly what its text denotes. -/
def CfgSound (cfg : Cfg) : Prop :=
  SiteSyntax cfg.site ∧ TypeSyntax cfg.type ∧ TopicSyntax cfg.topic ∧
  ∀ th, cfg.threshold = some th →
    ∃ neg a b, DecLit th.text neg a b ∧ th.value = DecLit.den neg a b

/-- PRD §5.5 defaults. -/
def defaultCfg : Cfg :=
  { site := "3963", type := "lakelevel", json := false, threshold := none, topic := "csarbora" }

/-- `url` is `pre` followed only by characters satisfying `ok`. -/
def UrlTail (pre url : String) (ok : Char → Prop) : Prop :=
  ∃ rest : List Char, url.toList = pre.toList ++ rest ∧ ∀ c ∈ rest, ok c

def hydrometPrefix : String := "https://hydromet.lcra.org/api/GetDataBySite/"
def ntfyPrefix : String := "https://ntfy.sh/"

end LakeLevel
