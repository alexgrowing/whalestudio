import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomAlgebraisationOfReductionTowerStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSystem

variable {X X' X'' Z : Scheme.{0}}

def Rel {H : LB X} {H' : LB X'} (β : X' ⟶ X) (w : LB.Iso H' (H.pull β)) (s : LB.Sec H) (s' : LB.Sec H') : Prop :=
  ∀ z (k : H.ι) (k' : H'.ι), β z ∈ H.U k → z ∈ H'.U k' →
    gs β z _ (s.f k) = (gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k')

theorem gs_stalkMap (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U) (a : Γ(X, U)) :
    (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem Rel.pull {H : LB X} {H' : LB X'} {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)} {s : LB.Sec H} {s' : LB.Sec H'}
    (h : Rel β w s s') (r : Z ⟶ X') (z : Z) (k : H.ι) (k' : H'.ι) (hk : β (r z) ∈ H.U k) (hk' : r z ∈ H'.U k') :
    gs (r ≫ β) z _ (s.f k) = (gw w r z k k').val * gs r z _ (s'.f k') := by
  have hm : r z ∈ (H.pull β).U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have e := congrArg (r.stalkMap z).hom (h (r z) k k' hk hk')
  rw [map_mul, gs_stalkMap r β z _ hk, gs_stalkMap r (𝟙 _) z _ hk', Category.comp_id] at e
  refine e.trans (congrArg (· * _) ?_)
  refine (congrArg (r.stalkMap z).hom (gs_unit (𝟙 X') (r z) _ hm _).symm).trans
    ((gs_stalkMap r (𝟙 _) z _ hm _).trans ?_)
  rw [Category.comp_id]
  exact gs_unit r z _ hm _

theorem Rel.comp {H : LB X} {H' : LB X'} {H'' : LB X''} {β : X' ⟶ X} {β' : X'' ⟶ X'} {w : LB.Iso H' (H.pull β)}
    {w' : LB.Iso H'' (H'.pull β')} {w'' : LB.Iso H'' (H.pull (β' ≫ β))} (T : Tri w w' w'') (hH' : H'.IsLB)
    {s : LB.Sec H} {s' : LB.Sec H'} {s'' : LB.Sec H''} (h : Rel β w s s') (h' : Rel β' w' s' s'') :
    Rel (β' ≫ β) w'' s s'' := by
  intro z k k'' hk hk''
  obtain ⟨i, hi⟩ := exists_chart hH' (β' z)
  rw [h.pull β' z k i hk hi, h' z i k'' hi hk'', T _ (𝟙 _) z k i k'' hk hi hk'', Category.id_comp, Units.val_mul,
    _root_.mul_assoc]

theorem surjective_thickTrans (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Surjective (thickTrans R I e) := by
  refine ⟨fun x => ?_⟩
  have h : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1 + 1))) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (e + 1) := by
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using ha
    refine x.2.mem_of_pow_mem 2 ?_
    have : Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) * 2 by omega) ?_
      rw [pow_mul]
      exact Ideal.pow_mem_pow ha' 2
    rw [this]
    exact Ideal.zero_mem _
  exact hx

theorem exists_lb_of_generated_system : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k'))) → (⨆ i, nonzeroLocus (s 0 i) = ⊤) → ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (H e) (M.pull (b e)) := by
  intro R _ _ _ I hI hc Y β hβ B b hB hfl hb hbb H v hH n s hs h0
  have hgen : ∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤ := by
    intro e
    induction e with
    | zero => exact h0
    | succ e ih =>
      have hsur : Surjective (β e) :=
        MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (surjective_thickTrans R I e)
      refine top_le_iff.1 fun y _ => ?_
      obtain ⟨z, rfl⟩ := hsur.surj y
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
        (show z ∈ ⨆ i, nonzeroLocus (s e i) by rw [ih]; trivial)
      rw [(GlobalTheory.SecPullIso.section_pull _ _ (β e) _ _ (v e) (hH (e + 1)).1 (hH e).1 (hH e).2 (s (e + 1) i)).2
        (s e i) (hs e i)] at hi
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  obtain ⟨P, f, O, t, hO, hva, hP⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose c w hc' hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy R P f O n t hO hva _
    ((Y e).hom ≫ thick R I e) (H e) (s e) (hH e).1 (hgen e) (fun d F hF h k => by
      obtain ⟨m, hm⟩ := (hP d F hF).1 h 0
      have : F = 0 := by
        rw [Ideal.mem_bot] at hm
        exact ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1)))).pow m).left (by simpa using hm)
      rw [this, map_zero])
  have hcc : ∀ e, β e ≫ c (e + 1) = c e := fun e => by
    have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hO (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections R P f O n t hO hva _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hc', hc', c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_hom_algebraisation_of_reductionTower R I hI hc Y β hβ B b hB hfl hb hbb (Over.mk f) ⟨O, hO, n, t, hva⟩ c hc' hcc
  refine ⟨O.pull g.left, pull_isLB hO _, fun e => ?_⟩
  exact LBIso.trans (hH e).1 (pull_isLB hO _) (pull_isLB (pull_isLB hO _) _) ⟨w e, hw e⟩
    (GlobalTheory.GenSpread.lbIso_pull_pull hO (b e) (hg e).symm)

end GlobalTheory.GenSystem
