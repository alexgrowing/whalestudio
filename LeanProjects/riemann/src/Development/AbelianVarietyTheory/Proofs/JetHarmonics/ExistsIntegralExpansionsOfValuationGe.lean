import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FamEqOnClassOfEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFieStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFamilyOfStrictMin

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace IntComb

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)}

theorem exists_int_of_vge (hϖ : Irreducible ϖ) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))} {r : ℚ}
    (hr : 0 ≤ r) (hs : VGe D (FractionRing V) (FamInt.ordVal hϖ) k α s r) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, hva, hsum⟩ := hs
  have hint : ∀ i, ∃ b : V, a i = algebraMap V (FractionRing V) b := fun i => by
    obtain ⟨b, hb⟩ := (FamInt.le_ordFn_iff hϖ (a i) 0).1 (le_trans (by exact_mod_cast hr) (hva i))
    exact ⟨b, by rw [hb, zpow_zero, _root_.one_mul]⟩
  choose b hb using hint
  refine ⟨FamInt.secLin (fun i => scal D.toPre.P.A.hom (b i)) σ,
    SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_⟩
  rw [SectionScalarValuation.sval_lin (fun i => scal D.toPre.P.A.hom (b i)) σ (fun _ => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF (fun j => hsum j) (𝟙 _) y hJ]
  refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (SectionScalarValuation.secScal_sval (hσ i) _ y hJ)
  have e1 : gs (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y ⊤ (scal D.toPre.P.A.hom (b i)) =
      cst ((𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom) y (b i) :=
    gs_pull _ _ y ⊤ trivial _
  have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (a i)) =
      cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (a i) :=
    gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
  have e3 : (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) ≫
        spMap (algebraMap (FractionRing V) (FractionRing V))) ≫ spMap (algebraMap V (FractionRing V)) := by
    rw [Category.id_comp, Category.id_comp, Category.assoc, Over.w]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e1, e2, e3, cst_comp, cst_comp, hb i]
  rfl

theorem integralFamily_of_min (hL : Laws) (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {q : ℕ} (hq : 1 ≤ q) (χ : D.toPre.X) (β : D.toPre.SecB q χ) (hmin : ∀ z, Q χ ≤ Q (χ + q • z)) :
    ∃ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α),
      (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) ∧
      f χ = β ∧ ∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := FamInt.exists_pull (F := FractionRing V) β
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing V) hL.globalFns D.tau_bimult q χ (fun a b h => by
    have h' : (q : ℤ) • a = (q : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : (q : ℤ) ≠ 0) h') σ
  have h0 : VGe D (FractionRing V) (FamInt.ordVal hϖ) q χ (Φ.s χ) 0 := by
    refine ⟨1, fun _ => 1, fun _ => β, fun _ => Φ.s χ, fun _ => hΦ ▸ hσ, fun _ => ?_, fun j => ?_⟩
    · simp
    · simp [DegPre.constBF]
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB q α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      (∀ h : χ = α, f = h ▸ β) ∧ ((∀ z, α ≠ χ + q • z) → ∀ j, f.f j = 0) := by
    intro α
    by_cases hα : χ = α
    · subst hα
      exact ⟨β, hΦ ▸ hσ, fun _ => rfl, fun h => absurd (by simp) (h 0)⟩
    by_cases hc : ∃ z, α = χ + q • z
    · obtain ⟨z, rfl⟩ := hc
      have H := SectionScalarValuation.fe_move hϖ hQ (FamInt.valOver_ordVal hϖ) q z χ Φ h0
      have hle := hmin z
      rw [q_shift hϖ hQ, le_add_iff_nonneg_right] at hle
      have hpos : (0 : ℤ) ≤ q * Q z + QForm.bOf D.toPre Q z χ :=
        nonneg_of_mul_nonneg_right hle (by omega)
      obtain ⟨f, h1⟩ := exists_int_of_vge hϖ (by rw [zero_add]; exact_mod_cast hpos) H
      exact ⟨f, h1, fun h => absurd h hα, fun h => absurd rfl (h z)⟩
    · refine ⟨SecOps.secZero, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun h => absurd h hα,
        fun _ _ => rfl⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e.symm⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 using key
  exact ⟨Φ, f, h1, h2 χ rfl, h3⟩

theorem exists_min_reps (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {q : ℕ} (hq : 1 ≤ q) : ∃ (N : ℕ) (χ : Fin N → D.toPre.X), (∀ α, ∃ i m, α = χ i + q • m) ∧
      (∀ i i', i' ≠ i → ∀ z, χ i ≠ χ i' + q • z) ∧ ∀ i z, Q (χ i) ≤ Q (χ i + q • z) := by
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X q hq
  have hnn : ∀ x, 0 ≤ Q x := fun x => by
    by_cases hx : x = 0
    · rw [hx, QForm.Q_zero hϖ D hQ]
    · exact le_trans zero_le_one (QForm.Q_pos hϖ D hQ hx)
  have hm : ∀ i, ∃ m : D.toPre.X, ∀ z, Q (e i + q • m) ≤ Q (e i + q • z) := fun i => by
    refine ⟨Function.argmin (fun z : D.toPre.X => (Q (e i + q • z)).toNat), fun z => ?_⟩
    have h := Function.argmin_le (fun z : D.toPre.X => (Q (e i + q • z)).toNat) z
    have h1 := hnn (e i + q • z)
    omega
  choose m hm using hm
  refine ⟨_, fun i => e i + q • m i, fun α => ?_, fun i i' hi z h => hi ?_, fun i z => ?_⟩
  · obtain ⟨i, ⟨z, hz⟩, -⟩ := he α
    exact ⟨i, z - m i, by rw [hz, smul_sub, add_assoc, add_sub_cancel]⟩
  · exact (he (e i + q • m i)).unique ⟨m i' + z, by rw [smul_add, ← add_assoc]; exact h⟩ ⟨m i, rfl⟩
  · have := hm i (m i + z)
    rwa [smul_add, ← add_assoc] at this

variable {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ}

theorem sum_f {n : ℕ} (S : Finset (Fin n)) (t : Fin n → Fam D.toPre F k) (α : D.toPre.X) (j) :
    ((∑ i ∈ S, t i).s α).f j = ∑ i ∈ S, ((t i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem sval_comb {n : ℕ} (c : Fin n → F) (t : Fin n → Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) :
    sval ((∑ i, c i • t i).s α) r z J =
      ∑ i, gs r z ⊤ (scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) * sval ((t i).s α) r z J :=
  SectionScalarValuation.sval_lin (fun i => gF D.toPre F (c i)) (fun i => (t i).s α) (fun j => sum_f _ _ α j) r z hJ

end IntComb

theorem exists_integral_expansions_of_vge : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (q : ℕ), 1 ≤ q → ∀ (s : Fam D.toPre F q) (r : ℚ), (∀ χ, VGe D F v q χ (s.s χ) r) → ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α), (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i)) ∧ (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε q) (s.s α) (D.toPre.famφB α) (DegPre.famε q) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) := by
  intro hL V _ _ _ ϖ hϖ D A G _ _ U Q hQ F _ _ v _ q hq s r hs
  classical
  obtain ⟨N, χ, hrep, hdis, hmin⟩ := IntComb.exists_min_reps hϖ hQ hq
  choose n a β βF hβ hva hsum using fun i => hs (χ i)
  choose Φ f hf hfβ hf0 using fun p : (Σ i : Fin N, Fin (n i)) =>
    IntComb.integralFamily_of_min hL hϖ hQ hq (χ p.1) (β p.1 p.2) (hmin p.1)
  choose σ hσ using fun p => IntegralExpansion.main hL V D A G U q hq (Φ p) (f p) (hf p)
  choose θ hθ using fun p => GlobalTheory.T.integralDegenerationFamily_baseChange_extensionField hL.globalFns V _ D q (Φ p) (f p) (hf p) F
  let E := (Fintype.equivFin (Σ i : Fin N, Fin (n i))).symm
  have hst : s = ∑ x, a (E x).1 (E x).2 • θ (E x) := by
    refine fam_ext fun α => ?_
    obtain ⟨i, m, rfl⟩ := hrep α
    refine fam_eq_on_class_of_eq hL.globalFns V D.toPre F q _ _ (χ i) ?_ m
    refine sec_ext_val D.toPre.P.isLB fun y J hJ => ?_
    rw [IntComb.sval_comb _ _ _ _ _ hJ,
      SectionScalarValuation.sval_lin (fun x => gF D.toPre F (a i x)) (βF i) (fun j => hsum i j) (𝟙 _) y hJ,
      E.sum_comp (fun p => gs (𝟙 _) y ⊤ (scal (fst (TF (R := V) F) D.toPre.P.A).left (a p.1 p.2)) *
        sval ((θ p).s (χ i)) (𝟙 _) y J), Fintype.sum_sigma, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun x _ => congrArg₂ (· * ·) rfl ?_
      rw [← SectionScalarValuation.secScal_sval (hβ i x) _ y hJ, ← SectionScalarValuation.secScal_sval (hθ ⟨i, x⟩ (χ i)) _ y hJ, hfβ ⟨i, x⟩]
    · refine fun i' _ hi => Finset.sum_eq_zero fun x _ => ?_
      rw [← SectionScalarValuation.secScal_sval (hθ ⟨i', x⟩ (χ i)) _ y hJ,
        UUA.sval_zero_of (hf0 ⟨i', x⟩ (χ i) (hdis i i' hi)) _ y J (hJ.mem _ _), mul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  refine ⟨_, fun x => a (E x).1 (E x).2, fun x => σ (E x), fun x => f (E x), fun x => hva _ _,
    fun x e => hσ _ e, fun α => ?_⟩
  refine (FieldBaseChange.secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
  rw [hst, IntComb.sval_comb _ _ _ _ _ hJ]
  exact Finset.sum_congr rfl fun x _ => by rw [SectionScalarValuation.secScal_sval (hθ _ α) _ _ hJ]

end GlobalTheory
