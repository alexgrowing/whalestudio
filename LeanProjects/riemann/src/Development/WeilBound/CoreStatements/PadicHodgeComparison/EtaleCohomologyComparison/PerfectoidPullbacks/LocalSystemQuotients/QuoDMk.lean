import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens

set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Ls

variable {W : Type} [CommRing W]

abbrev lpow (l : ℕ) (M : Type 1) [AddCommGroup M] [Module W M] (n : ℕ) : Submodule W M :=
  LinearMap.range (((l : W) ^ n) • LinearMap.id : M →ₗ[W] M)

def quo (l : ℕ) (K : Cx.{1} W) (n : ℕ) : Cx.{1} W where
  X i := K.X i ⧸ lpow l (K.X i) n
  d i := Submodule.mapQ _ _ (K.d i) (by
    rintro _ ⟨y, rfl⟩
    exact ⟨K.d i y, by simp⟩)
  dd i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [Submodule.mapQ_apply, K.dd]

def red (l : ℕ) (K : Cx.{1} W) (n : ℕ) : Cx.Hom (quo l K (n + 1)) (quo l K n) (RingHom.id W) where
  f i := Submodule.mapQ _ _ LinearMap.id (by
    rintro _ ⟨y, rfl⟩
    exact ⟨(l : W) • y, by simp [pow_succ, mul_smul, smul_comm ((l : W) ^ n) (l : W) y]⟩)
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

def qsys (l : ℕ) (K : Cx.{1} W) (j : ℕ) : Sys.{1} W where
  M n := (quo l K n).H j
  r n := (red l K n).mapH j

def redg (l : ℕ) (K : Cx.{1} W) {b c : ℕ} (h : b ≤ c) : Cx.Hom (quo l K c) (quo l K b) (RingHom.id W) where
  f i := Submodule.mapQ _ _ LinearMap.id (by
    rintro _ ⟨y, rfl⟩
    exact ⟨((l : W) ^ (c - b)) • y, by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add, Nat.add_sub_cancel' h]⟩)
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

def nug (l : ℕ) (K : Cx.{1} W) {a c : ℕ} (h : a ≤ c) : Cx.Hom (quo l K a) (quo l K c) (RingHom.id W) where
  f i := Submodule.mapQ _ _ (((l : W) ^ (c - a)) • LinearMap.id) (by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, by simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add, Nat.sub_add_cancel h]⟩)
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk ((K.d i).map_smul _ x)

def rhoH (l : ℕ) (K : Cx.{1} W) (j c b : ℕ) : (qsys l K j).M c →ₗ[W] (qsys l K j).M b :=
  if h : b ≤ c then (redg l K h).mapH j else 0

def nuH (l : ℕ) (K : Cx.{1} W) (j a c : ℕ) : (qsys l K j).M a →ₗ[W] (qsys l K j).M c :=
  if h : a ≤ c then (nug l K h).mapH j else 0

def TF (l : ℕ) (K : Cx.{1} W) : Prop := ∀ i (x : K.X i), (l : W) • x = 0 → x = 0

end CrystallineSemistableComparison.Ls

end
