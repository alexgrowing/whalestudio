import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

theorem indepToC_comp {K : Type*} [Field K] {σ : K →+* ℂ} {C C' : Type*} [AddCommGroup C] [Module K C]
    [AddCommGroup C'] [Module K C'] {W : Type*} [AddCommGroup W] [Module ℂ W] (J : C →ₛₗ[σ] W)
    (hJ : IndepToC J) (ι : C' →ₗ[K] C) (hι : Function.Injective ι) : IndepToC (J.comp ι) := by
  intro n b hb
  exact hJ n (fun i => ι (b i)) (hb.map' ι (LinearMap.ker_eq_bot.mpr hι))

variable {D : D7} {T : Top D}

def jRec (j : ℕ) (ka : WeightFamilies.Wt D j) :
    cutR T.C j ka →ₛₗ[T.σ₀] FDSec (T.U j T.σ₀).X :=
  (rdC (T.U j) T.σ₀ (wtA ka) ka.n).comp (Submodule.inclusion (cutR_le T.C j ka))

set_option synthInstance.maxHeartbeats 400000 in
theorem spanAt_rec (h : LawsP T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j)
    (hJ : JInjRd T j (wtA ka) ka.n) (A : Set (FDSec (T.U j T.σ₀).X))
    (hG : holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ A)
    (hA : A ⊆ Submodule.span ℂ (jRec (T := T) j ka ''
      (((recX h) j h1 h2).shortTh ka : Set ((recB h.toLawsCore).Cusp j ka)))) :
    SpanAt ((recX h) j h1 h2) ka :=
  spanAt_of_chain ((recX h) j h1 h2) ka (jRec (T := T) j ka)
    (indepToC_comp _ hJ _ (Submodule.inclusion_injective _))
    (holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n)) A
    (fun _ => rdC_mem_holSub0 T.good_σ₀ (wtA ka) ka.n _) hG hA

def GminFDSt : Prop :=
  ∀ (D : D7) (T : Full D) (_h : LawsFull T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j), badN D ≠ 0 →
    LastPos (T.Q.Dw j) (wtA ka) → 8 * D.R.f * D.R.r + 4 ≤ ka.n → Even ka.n →
    holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤
      Submodule.span ℂ (rdU (T.U j T.σ₀) '' T.sh j ka)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
