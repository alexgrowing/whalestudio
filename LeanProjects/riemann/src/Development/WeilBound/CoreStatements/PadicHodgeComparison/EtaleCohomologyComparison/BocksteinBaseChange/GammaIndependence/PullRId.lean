import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory.LogCris

namespace CrystallineSemistableComparison

theorem catH_pull_eq_id {R : Type} [CommRing R] {C : Type*} [Category C] {F : C ⥤ ModuleCat.{0} R}
    (m : GlobalTheory.CatH.Mor F F (RingHom.id R)) (hG : m.G = 𝟭 C) (hτ : ∀ T x, HEq (m.τ T x) x) (n : ℕ) :
    m.pull n = LinearMap.id := by
  obtain ⟨G, τ, nat⟩ := m
  subst hG
  have e : ∀ T x, τ T x = x := fun T x => eq_of_heq (hτ T x)
  apply LinearMap.ext
  intro c
  induction c using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.mapQ _ _ _ _ (Submodule.Quotient.mk z) = Submodule.Quotient.mk z
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext s
    exact e _ _

theorem thick_eqToHom_φ {b : Base} {L : b.Fun} {A T : Thick L} (e : A = T) :
    HEq (eqToHom e).φ (RingHom.id T.B) := by
  subst e
  rfl

theorem smMor_id_functor {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K))
    (h : 𝟙 X ≫ p = p) : (smMor (𝟙 X) h).functor = 𝟭 _ := by
  have hobj : ∀ T : Thick (smFun X p), (smMor (𝟙 X) h).functor.obj T = T := by
    intro T
    cases T
    dsimp only [Mor.functor, Mor.obj]
    congr 1
    all_goals first
      | (funext j; exact j.elim)
      | (ext; simp [smMor])
  refine CategoryTheory.Functor.ext hobj ?_
  intro T T' f
  apply Thick.Hom.ext
  · change f.φ = (eqToHom (hobj T').symm).φ.comp (f.φ.comp (eqToHom (hobj T)).φ)
    rw [eq_of_heq (thick_eqToHom_φ (hobj T)), eq_of_heq (thick_eqToHom_φ (hobj T').symm)]
    rfl
  · funext j; exact j.elim

theorem pullR_id {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    (h : 𝟙 X ≫ p = p) : pullR n (𝟙 X) h = LinearMap.id :=
  catH_pull_eq_id _ (smMor_id_functor p h) (fun _ _ => HEq.rfl) n

theorem genMap_id {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K)
    (h : 𝟙 M.X ≫ M.p = M.p) : Model.genMap (𝟙 M.X) h = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [Model.genMap]

theorem pullR_genMap_id {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ)
    (h : 𝟙 M.X ≫ M.p = M.p) : pullR n (Model.genMap (𝟙 M.X) h) (Model.genMap_q _ h) = LinearMap.id := by
  have key : ∀ (f : M.gen ⟶ M.gen) (_ : f = 𝟙 _) (h' : f ≫ M.q = M.q), pullR n f h' = LinearMap.id := by
    rintro f rfl h'
    exact pullR_id _ n h'
  exact key _ (genMap_id M h) _

end CrystallineSemistableComparison
