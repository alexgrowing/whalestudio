import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk

set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Ls

variable {W : Type} [CommRing W]

def prj (l : ℕ) (K : Cx.{1} W) (n : ℕ) : Cx.Hom K (quo l K n) (RingHom.id W) where
  f i := Submodule.mkQ _
  comm i x := rfl

def qred (l : ℕ) {K L : Cx.{1} W} {c : ℕ} (f : Cx.Hom K (quo l L c) (RingHom.id W)) {b : ℕ} (h : b ≤ c) :
    Cx.Hom (quo l K b) (quo l L b) (RingHom.id W) where
  f i := Submodule.liftQ _ (((redg l L h).f i).comp (f.f i)) (by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (f.f i y)
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
    rw [← hz]
    change Submodule.Quotient.mk _ = (0 : (quo l L b).X i)
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩)
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (quo l L b).d i ((redg l L h).f i (f.f i x)) = (redg l L h).f (i + 1) (f.f (i + 1) (K.d i x))
    rw [(redg l L h).comm, f.comm]

def FlatL (l c : ℕ) (K : Cx.{1} W) : Prop :=
  ∀ i, (∀ x : K.X i, ((l : W) ^ c) • x = 0) ∧ ∀ a b, a + b = c → ∀ x : K.X i, ((l : W) ^ b) • x = 0 → x ∈ lpow (W := W) l (K.X i) a

def tsys (l : ℕ) (Kt : ℕ → Cx.{1} W) (ψ : ∀ n, Cx.Hom (Kt n) (quo l (Kt (n + 1)) n) (RingHom.id W))
    (hψ : ∀ n j, Function.Bijective ((ψ n).mapH j)) (j : ℕ) : Sys.{1} W where
  M n := (Kt n).H j
  r n := (LinearEquiv.ofBijective ((ψ n).mapH j) (hψ n j)).symm.toLinearMap ∘ₗ (prj l (Kt (n + 1)) n).mapH j

end CrystallineSemistableComparison.Ls

end
