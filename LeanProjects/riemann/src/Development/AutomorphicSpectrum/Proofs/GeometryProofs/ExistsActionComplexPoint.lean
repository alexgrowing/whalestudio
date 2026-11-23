import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

private theorem exists_isActOf_lemma {S : Scheme} {R : Type} [CommRing R]
    {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {V : Type} [AddCommGroup V]
    [Module R V] (M : GlobalTheory.CompanionTheory.Ar.LieModel G x V) {O : Type} [CommRing O]
    (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) :
    ∃ ρ : O →+* Module.End R V, M.IsActOf act.act ρ := by
  have hpt0 : M.pt 0 = 1 := by
    have h : M.pt 0 * 1 = M.pt 0 * M.pt 0 := by
      rw [_root_.mul_one, ← M.add, add_zero]
    exact (mul_left_cancel h).symm
  have hact0 : act.act 0 = 1 := by
    have h : act.act 0 * 1 = act.act 0 * act.act 0 := by
      rw [_root_.mul_one, ← act.add, add_zero]
    exact (mul_left_cancel h).symm
  have htan : ∀ (a : O) (e : V), GlobalTheory.CompanionTheory.Ar.IsTanAt G x (M.pt e ≫ act.act a) := by
    intro a e
    haveI := act.hom a
    have h1 := M.tan e
    unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at h1 ⊢
    rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
  choose f hf using fun (a : O) (e : V) => M.onto _ (htan a e)
  have hadd : ∀ (a : O) (e e' : V), f a (e + e') = f a e + f a e' := by
    intro a e e'
    haveI := act.hom a
    apply M.inj
    rw [hf, M.add, M.add, hf, hf, MonObj.mul_comp]
  have hsmul : ∀ (a : O) (r : R) (e : V), f a (r • e) = r • f a e := by
    intro a r e
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hf, M.smul, hf, Over.comp_left, Over.comp_left, M.smul, Category.assoc]
  refine ⟨{
      toFun := fun a => { toFun := f a, map_add' := hadd a, map_smul' := hsmul a }
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }, ?_⟩
  · ext e
    show f 1 e = e
    apply M.inj
    rw [hf, act.one, Category.comp_id]
  · intro a b
    ext e
    show f (a * b) e = f a (f b e)
    apply M.inj
    rw [hf, hf, hf, mul_comm a b, act.mul, Category.assoc]
  · ext e
    show f 0 e = 0
    apply M.inj
    rw [hf, hact0, MonObj.comp_one, hpt0]
  · intro a b
    ext e
    show f (a + b) e = f a e + f b e
    apply M.inj
    rw [hf, M.add, hf, hf, act.add, MonObj.comp_mul]
  · unfold GlobalTheory.CompanionTheory.Ar.LieModel.IsActOf GlobalTheory.CompanionTheory.Ar.LieModel.IsDiffOf
    intro a e
    exact hf a e

theorem exists_lieModel_tied_isEigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (y : Sp ℂ ⟶ Xo.XF c), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module ℂ EC) (N : LieModel Y.t.G (y ≫ Y.j) EC) (ρ : 𝓞 E →+* Module.End ℂ EC), N.IsActOf Y.t.act.act ρ ∧ ∀ (ch : 𝓞 E →+* ℂ) (n : ℕ) (v : Vecs y n) (w : Fin n → EC), LieMult Xo.univ.t.act (under y) ch n → (∀ i, SameVec Y y (v i) (N.pt (w i))) → LinearIndependent ℂ w → (∀ i, w i ∈ eigSp ρ ch) → IsEigFrame Xo.univ.t.act (under y) ch v := by
  intro E _ _ _ H D l Xo c O _ β Y y
  haveI := Xo.univ.t.comm
  obtain ⟨V, i1, i2, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Xo.univ.t.G ℂ (under y)
  obtain ⟨ρ, hρ⟩ := exists_isActOf_lemma M₀ Xo.univ.t.act
  obtain ⟨M', hM'⟩ :=
    (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Y.m0.toSABMap.cart ℂ y V).1 M₀
  obtain ⟨N, hN⟩ := (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Y.m.cart ℂ y V).2 M'
  have hsame : ∀ e, SameVec Y y (M₀.pt e) (N.pt e) := by
    intro e
    unfold GlobalTheory.CompanionTheory.Ar.Flat.SameVec
    exact ⟨(M'.pt e).left, Over.w (M'.pt e), hM' e, hN e⟩
  have hK : ∀ (a : 𝓞 E) (e : V),
      (M'.pt (ρ a e)).left = (M'.pt e).left ≫ (Y.oF.t.act.act a).left := by
    intro a e
    refine Y.m0.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [hM', Category.assoc, Y.m0.toSABMap.act a, ← Category.assoc, hM', ← Over.comp_left,
        ← hρ a e]
    · rw [Over.w, Category.assoc, Over.w, Over.w]
  have hNact : N.IsActOf Y.t.act.act ρ := by
    unfold GlobalTheory.CompanionTheory.Ar.LieModel.IsActOf GlobalTheory.CompanionTheory.Ar.LieModel.IsDiffOf
    intro a e
    apply Over.OverMorphism.ext
    rw [← hN, hK, Over.comp_left, ← hN, Category.assoc, Category.assoc, Y.m.act a]
  refine ⟨V, i1, i2, N, ρ, hNact, ?_⟩
  intro ch n v w hmult hsv hli hmem
  have hv : v = fun k => M₀.pt (w k) := by
    funext k
    exact SameVec.unique_left (hsv k) (hsame (w k))
  obtain ⟨v₀, hv₀⟩ := hmult
  have hfr₀ : IsEigFrame Xo.univ.t.act (under y) ch v₀ := hv₀
  have htan₀ : ∀ k, IsTanAt Xo.univ.t.G (under y) (v₀ k) := fun k => (hfr₀.1 k).1
  choose u hu using fun k => M₀.onto (v₀ k) (htan₀ k)
  have hI := (GlobalTheory.T.lie_model_eigenvectors_action _ ℂ Xo.univ.t.G (under y) V M₀).2 _ Xo.univ.t.act ρ ch hρ
  have hv₀' : v₀ = fun k => M₀.pt (u k) := funext fun k => (hu k).symm
  rw [hv₀'] at hfr₀
  obtain ⟨hu_li, hu_span⟩ := (hI.2 n u).1 hfr₀
  haveI : FiniteDimensional ℂ (eigSp ρ ch) := by
    rw [← hu_span]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have hspan : Submodule.span ℂ (Set.range w) = eigSp ρ ch := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hmem k
    · rw [finrank_span_eq_card hli, ← hu_span, finrank_span_eq_card hu_li]
  rw [hv]
  exact (hI.2 n w).2 ⟨hli, hspan⟩

end GlobalTheory.CompanionTheory.Ar.Flat
