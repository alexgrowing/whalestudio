import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EigenFrames
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)
open GlobalTheory.LB (resG_resG le_iSup_inf)

variable {X : Scheme.{0}} {F G : X.Modules}

theorem isFrame_mkSec (N : Sub F) {U : X.Opens} {ν : Type} [Fintype ν] (e : ν → Γ(F, U))
    (he : ∀ i, e i ∈ N.sec U)
    (hli : ∀ (V : X.Opens) (h : V ≤ U), LinearIndependent Γ(X, V) fun i => resM F h (e i))
    (hsp : ∀ (V : X.Opens) (h : V ≤ U) (x : Γ(F, V)), x ∈ N.sec V →
      x ∈ Submodule.span Γ(X, V) (Set.range fun i => resM F h (e i))) :
    GlobalTheory.VB.IsFrame (F := N.toMod) fun i => N.mkSec (e i) (he i) := by
  rw [GlobalTheory.VB.isFrame_iff]
  intro V h
  have hcomp : (appLinear N.incl V) ∘ (fun i => resM N.toMod h (N.mkSec (e i) (he i))) =
      fun i => resM F h (e i) := funext fun i => by
    simp only [Function.comp, appLinear_apply]
    rw [app_resM]
    rfl
  refine ⟨LinearIndependent.of_comp (appLinear N.incl V) (hcomp ▸ hli V h), ?_⟩
  rintro y -
  have hx := hsp V h _ (N.incl_app_mem y)
  rw [← hcomp, Set.range_comp, Submodule.span_image] at hx
  obtain ⟨y', hy', e'⟩ := hx
  have : y' = y := N.incl_app_injective V (by rwa [appLinear_apply] at e')
  exact this ▸ hy'

section Frames

variable {O : Type} [CommRing O] (ρ : O →+* CategoryTheory.End F) {κ : Type} [Fintype κ]
  (τ : κ → (O →+* Γ(X, ⊤))) {m : κ → ℕ} {U : X.Opens} (B : (Σ i, Fin (m i)) → Γ(F, U))
  (hB : GlobalTheory.VB.IsFrame B)
  (hact : ∀ i k a, (act ρ a).app U (B ⟨i, k⟩) = resG X (le_top : U ≤ ⊤) (τ i a) • B ⟨i, k⟩)

end Frames

end GlobalTheory.EigenFrames
