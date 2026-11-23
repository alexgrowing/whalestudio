import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombEqZeroIffExpansionCombEqZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpansionFunction

open FieldBaseChange

theorem eq_iff_comb_eq_zero {R : Type} [CommRing R] [IsDomain R] {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ}
    (π : Y ⟶ Spec (CommRingCat.of R)) (π' : Y' ⟶ Spec (CommRingCat.of (FractionRing R))) {p : Y' ⟶ Y}
    (hp : p ≫ π = π' ≫ jK R) (hφ : ∀ k, φ' k = p ≫ φ k) (hinj : ∀ W : Y.Opens, Function.Injective (p.app W))
    (π₀ : Y' ⟶ Spec (CommRingCat.of R)) (h₀ : π₀ = π' ≫ jK R)
    {s s' : LB.Sec (LB.LinComb L φ' ε)} {σ σ' : LB.Sec (LB.LinComb L φ ε)} {r r' : R} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (H : GeneratorPullback.SecScal L φ' ε s φ ε σ p (scal π₀ r)) (H' : GeneratorPullback.SecScal L φ' ε s' φ ε σ' p (scal π₀ r')) :
    s = s' ↔ ∀ j, ∑ i : Fin 2, resTop _ (scal π (![r', -r] i)) * (![σ, σ'] i).f j = 0 := by
  let t : SecOver π' (LB.LinComb L φ' ε) := s
  let t' : SecOver π' (LB.LinComb L φ' ε) := s'
  let τ : SecOver π (LB.LinComb L φ ε) := σ
  let τ' : SecOver π (LB.LinComb L φ ε) := σ'
  have E : pullOver L ε hp hφ τ = algebraMap R (FractionRing R) r • t :=
    (secScal_iff hp hφ hL t τ π₀ _ h₀ r).1 H
  have E' : pullOver L ε hp hφ τ' = algebraMap R (FractionRing R) r' • t' :=
    (secScal_iff hp hφ hL t' τ' π₀ _ h₀ r').1 H'
  have hi : ∀ x : SecOver π (LB.LinComb L φ ε), pullOver L ε hp hφ x = 0 → x = 0 := fun x hx =>
    SecOver.ext _ _ fun j => hinj _ (by
      have e := congrArg (chartFun π' _ j) hx
      have hw := wchart_eq (L := L) hφ j
      refine Geo.Tor.fn_ext fun y hy => ?_
      have hy' : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L φ' j := hw.ge hy
      have e₂ := congrArg (Geo.Tor.gs (𝟙 Y') y (LB.wchart L φ' j)) e
      refine (Geo.Tor.gs_pull _ p y _ hy _).trans ((gs_pullFn hp hw.le _ (𝟙 Y') y hy').symm.trans
        (e₂.trans ((gs_zero' _ y _ hy').trans ?_)))
      exact ((Geo.Tor.gs_pull _ p y _ hy _).trans (gs_zero' (𝟙 Y' ≫ p) y (LB.wchart L φ j) hy)).symm)
  have ha : algebraMap R (FractionRing R) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr
  have ha' : algebraMap R (FractionRing R) r' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr'
  have key : pullOver L ε hp hφ (r' • τ + (-r) • τ') =
      (algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) r') • (t - t') := by
    rw [map_add, map_smulₛₗ, map_smulₛₗ, E, E', map_neg, smul_smul, smul_smul, smul_sub, sub_eq_add_neg,
      ← neg_smul, neg_mul, mul_comm (algebraMap R (FractionRing R) r')]
  have main : t = t' ↔ r' • τ + (-r) • τ' = 0 := by
    constructor
    · intro h
      exact hi _ (by rw [key, h, sub_self, smul_zero])
    · intro h
      rw [h, map_zero] at key
      exact sub_eq_zero.1 ((smul_eq_zero_iff_right (mul_ne_zero ha ha')).1 key.symm)
  refine main.trans ⟨fun h j => ?_, fun h => SecOver.ext _ _ fun j => ?_⟩
  · rw [Fin.sum_univ_two]
    exact congrArg (chartFun π _ j) h
  · have := h j
    rw [Fin.sum_univ_two] at this
    exact this

end ExpansionFunction

theorem eq_iff_expansion_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (s s' : U.SecK k) (F F' : Fam D.toPre (FractionRing R) k), U.Expands k s F → U.Expands k s' F' → (s = s' ↔ F = F') := by
  intro R _ _ I hR D A G _ _ hG U k s s' F F' ⟨r, hr, σ, f, hσ, hf, hE⟩ ⟨r', hr', σ', f', hσ', hf', hE'⟩
  have := U.smooth
  have := D.toPre.P.isAb.smooth
  have : Flat G.hom := inferInstance
  have : Flat D.toPre.P.A.hom := inferInstance
  have e : (TF (R := R) (FractionRing R)).hom = jK R := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have hd : IsDominant (TF (R := R) (FractionRing R)).hom := DVR.GC.isDominant_jFR (V := R) (FractionRing R)
  have h₁ : IsSchemeTheoreticallyDominant (TF (R := R) (FractionRing R)).hom := .of_isDominant _
  have h₂ : IsSchemeTheoreticallyDominant (jK R) := e ▸ h₁
  have h₅ : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have h₃ : QuasiCompact (TF (R := R) (FractionRing R)).hom := e ▸ h₅
  have h₄ : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  have hs := ExpansionFunction.eq_iff_comb_eq_zero U.LG.isLB G.hom (pullback.snd G.hom (jK R))
    pullback.condition (fun _ => (Category.comp_id _).symm) (pullback.fst G.hom (jK R)).app_injective _ rfl
    hr hr' hσ hσ'
  have hw : (DegPre.BF D.toPre (FractionRing R)).hom =
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R := by
    rw [← e]; exact (Over.w _).symm
  have hF := fun α => ExpansionFunction.eq_iff_comb_eq_zero D.toPre.P.isLB D.toPre.P.A.hom
    (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left
    ((Over.w (DegPre.prB D.toPre (FractionRing R))).trans hw) (DVR.GC.famφ_eq D.toPre (FractionRing R) α)
    (pullback.snd (TF (R := R) (FractionRing R)).hom D.toPre.P.A.hom).app_injective _ hw hr hr' (hf α) (hf' α)
  have H := comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k 2 ![r', -r] ![σ, σ'] ![f, f']
    (fun i => by fin_cases i; exacts [hE, hE'])
  have hc : ∀ α (i : Fin 2), (![f, f'] i) α = ![f α, f' α] i := fun α i => by fin_cases i <;> rfl
  simp only [hc] at H
  constructor
  · intro h
    exact DVR.fam_ext fun α j => by rw [(hF α).2 (H.1 (hs.1 h) α)]
  · intro h
    exact hs.2 (H.2 hG fun α => (hF α).1 (by rw [h]))

end GlobalTheory
