import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLeStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionPullbackSourceLevelOneStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralExpansionUniqueOfUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFieStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PullAlExtensionFieldOfFractionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PullAlLinearCombinationStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PullExpField

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange

section Generic

variable {X Y Y₁ Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem secLin_val {φ₁ : K' → (Y₁ ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y₁ ⟶ Y} {c : Fin n → Γ(Y₁, ⊤)}
    (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y₁) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ r z J = ∑ i, gs r z ⊤ (c i) * sval (s i) (r ≫ h) z J := by
  simp only [sval_of (s _) (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) :=
    ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have a₂ : LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) :=
    inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  refine (gs_res _ z _ hm _).symm.trans ((congrArg (gs r z _) e).trans ?_)
  refine ((gs_eq _ z _ hm _).trans (by rw [map_sum, map_sum])).trans (Finset.sum_congr rfl fun i _ =>
    (gs_eq _ z _ hm _).symm.trans ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hm _)
      ((gs_res _ z a₂ hm _).trans (gs_pull _ h z _ (a₂ hm) _)))))

theorem secScal_val {φ₁ : K' → (Y₁ ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} {h : Y₁ ⟶ Y} {c : Γ(Y₁, ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y₁) (z : Z) {J} (hJ : Good L z J) :
    sval s (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) :=
    ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have a₂ : LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) :=
    inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  exact ((gs_res _ z a₂ hm _).trans (gs_pull _ h z _ (a₂ hm) _)).symm.trans ((congrArg (gs r z _) e).trans
    ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hm _) (gs_res _ z _ hm _))))

theorem sval_secScale {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε))
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem constVal_mul {R : Type} [CommRing R] (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    constVal q z (a * b) = constVal q z a * constVal q z b := by
  rw [constVal, map_mul, gs_mul q z ⊤ trivial]; rfl

end Generic

section Fam

variable {V : Type} [CommRing V] [IsDomain V]

abbrev toF (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F] : V →+* F :=
  (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))

theorem toF_ne_zero (F : Type) [Field F] [Algebra (FractionRing V) F] {r : V} (hr : r ≠ 0) : toF V F r ≠ 0 := by
  intro h
  apply hr
  apply IsFractionRing.injective V (FractionRing V)
  apply (algebraMap (FractionRing V) F).injective
  simpa using h

theorem hom_TF (F : Type) [Field F] [Algebra (FractionRing V) F] :
    jFK (R := V) F ≫ jK V = Spec.map (CommRingCat.ofHom (toF V F)) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F]

theorem hom_BF : (DegPre.BF D F).hom =
    (fst (TF (R := V) F) D.P.A).left ≫ Spec.map (CommRingCat.ofHom (toF V F)) := by
  rw [← hom_TF]
  exact (Over.w (fst (TF (R := V) F) D.P.A)).symm

abbrev IsBC {k : ℕ} (θ : Fam D F k) (g : ∀ α : D.X, D.SecB k α) : Prop :=
  ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (θ.s α) (D.famφB α) (DegPre.famε k) (g α)
    (DegPre.prB D F).left 1

variable {D F} {k : ℕ}

theorem sval_smul (ζ : F) (θ : Fam D F k) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J}
    (hJ : Good D.P.L z J) :
    sval ((ζ • θ).s α) r z J = constVal (r ≫ (fst (TF (R := V) F) D.P.A).left) z ζ * sval (θ.s α) r z J :=
  (sval_secScale (gF D F ζ) (θ.s α) r z hJ).trans
    (congrArg (· * _) (gs_scal (fst (TF (R := V) F) D.P.A).left r z ζ))

theorem sum_f {n : ℕ} (S : Finset (Fin n)) (t : Fin n → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, t i).s α).f j = ∑ i ∈ S, ((t i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem sval_comb {n : ℕ} (c : Fin n → F) (t : Fin n → Fam D F k) (α : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval ((∑ i, c i • t i).s α) r z J =
      ∑ i, gs r z ⊤ (scal (fst (TF (R := V) F) D.P.A).left (c i)) * sval ((t i).s α) r z J :=
  SectionScalarValuation.sval_lin (fun i => gF D F (c i)) (fun i => (t i).s α) (fun j => sum_f _ _ α j) r z hJ

theorem IsBC.smul {θ : Fam D F k} {g : ∀ α : D.X, D.SecB k α} (h : IsBC D F θ g) (t : V) :
    IsBC D F (toF V F t • θ) (fun α => SecOps.secScale (scal D.P.A.hom t) (g α)) := fun α =>
  SectionScalarValuation.secScal_of_sval D.P.isLB fun y J hJ => by
    rw [sval_secScale _ _ _ _ hJ, sval_smul _ _ _ _ _ hJ, SectionScalarValuation.secScal_sval (h α) _ _ hJ, gs_scal,
      Category.assoc, Over.w, hom_BF, ← Category.assoc, constVal_specMap]

theorem isBC_of_scal {θ : Fam D F k} {g : ∀ α : D.X, D.SecB k α} {t : V}
    (h : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (θ.s α) (D.famφB α) (DegPre.famε k) (g α)
      (DegPre.prB D F).left (scal (DegPre.BF D F).hom t)) : IsBC D F (toF V F t • θ) g := fun α =>
  SectionScalarValuation.secScal_of_sval D.P.isLB fun y J hJ => by
    rw [sval_smul _ _ _ _ _ hJ, secScal_val (h α) _ _ hJ, gs_scal, hom_BF, ← Category.assoc, constVal_specMap]

theorem secLin_iff_comb {n : ℕ} (c : Fin n → F) {θ : Fin n → Fam D F k} {f : Fin n → ∀ α : D.X, D.SecB k α}
    (h : ∀ i, IsBC D F (θ i) (f i)) (s : Fam D F k) :
    (∀ α : D.X, GeneratorPullback.SecLin D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α)
        (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D F).left
        (fun i => scal (fst (TF (R := V) F) D.P.A).left (c i))) ↔ s = ∑ i, c i • θ i := by
  constructor
  · intro H
    refine fam_ext fun α => sec_ext_val D.P.isLB fun y J hJ => ?_
    rw [sval_comb _ _ _ _ _ hJ, secLin_val (H α) _ _ hJ]
    exact Finset.sum_congr rfl fun i _ => by rw [SectionScalarValuation.secScal_sval (h i α) _ _ hJ]
  · rintro rfl α
    refine (secLin_iff_val D.P.isLB _ _ _ _).2 fun y J hJ => ?_
    rw [sval_comb _ _ _ _ _ hJ]
    exact Finset.sum_congr rfl fun i _ => by rw [SectionScalarValuation.secScal_sval (h i α) _ _ hJ]

end Fam

section Term

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

theorem expandsAt_zero (U : UnifPre (maximalIdeal V) D A G) (e k : ℕ) :
    U.ExpandsAt e k SecOps.secZero (fun _ => SecOps.secZero) := by
  refine ⟨∅, fun α _ j => map_zero _, fun p j₁ jf jt _ _ => ?_⟩
  rw [Finset.attach_empty, Finset.sum_empty]
  erw [map_zero, map_zero, mul_zero]

theorem term (hL : Laws) (U : Unif (maximalIdeal V) D A G) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]
    (oa : D.toPre.OAct O) (a : O) (φ : G ⟶ G) (k N : ℕ) (hk : 1 ≤ k)
    (hB : ∀ (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E → ∀ s' : U.SecK (k * N),
      IsPullByEnd U φ k N s s' → ∃ E' : Fam D.toPre (FractionRing V) (k * N), U.Expands (k * N) s' E' ∧
        PullAl D (FractionRing V) oa a k N E E')
    (u : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![gK, endK φ ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)])) (hu : u.IsGen)
    (hc : LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u unitK)
      (LB.pullGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig (k * (N - 1))) (jK V)))
    (F : Type) [Field F] [Algebra (FractionRing V) F]
    (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hf : ∀ e, U.ExpandsAt e k σ f) :
    ∃ (t : V) (σ' : H0 U.LG.L (k * N)) (f' : ∀ α : D.toPre.X, D.toPre.SecB (k * N) α)
      (θ : Fam D.toPre F k) (θ' : Fam D.toPre F (k * N)), t ≠ 0 ∧ (∀ e, U.ExpandsAt e (k * N) σ' f') ∧
      IsBC D.toPre F θ f ∧ IsBC D.toPre F θ' f' ∧ PullAl D F oa a k N (toF V F t • θ) θ' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK V)) (z : Z) (J), Good U.LG.L z J →
        sval σ' (r ≫ gK) z J = constVal (r ≫ pullback.snd G.hom (jK V) ≫ jK V) z t *
          (sval σ ((r ≫ endK φ) ≫ gK) z J * (val u r z J).val) := by
  have hLG := U.LG.isLB
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨s, hs⟩ : ∃ s : U.SecK k, ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK V)) (z : Z) (J),
      Good U.LG.L z J → sval s r z J = sval σ (r ≫ gK) z J := by
    obtain ⟨s, hs⟩ := exists_sec hLG (φ' := fun _ : Fin 1 => (gK : pullback G.hom (jK V) ⟶ G.left))
      (ε' := fun _ => (k : ℤ)) (fun W _ g => Finset.prod_congr rfl fun i _ => by rw [Category.comp_id])
      (pullSec U.LG.L _ _ σ (gK : pullback G.hom (jK V) ⟶ G.left))
    exact ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ r z hJ)⟩
  obtain ⟨s', hs'⟩ : ∃ s' : U.SecK (k * N), ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK V)) (z : Z) (J),
      Good U.LG.L z J → sval s' r z J = sval s (r ≫ endK φ) z J * (val u r z J).val := by
    obtain ⟨s', hs'⟩ := exists_sec hLG (φ' := fun _ : Fin 1 => (gK : pullback G.hom (jK V) ⟶ G.left))
      (ε' := fun _ => ((k * N : ℕ) : ℤ)) (fun W _ g => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
          Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
        rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
      (pullMulSec s (endK φ) u hu)
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (sval_pullMulSec _ _ _ hu r z hJ)⟩
  obtain ⟨E, hE, -⟩ := (U.expand k hk).1 s
  obtain ⟨g, hg, hEg⟩ := GlobalTheory.T.expansion_of_integral_section_is_integral V ϖ hϖ D A G U.toUnifPre k σ s
    (SectionScalarValuation.secScal_of_sval hLG fun y J hJ => (hs _ _ y J hJ).symm) E hE
  obtain rfl : f = g := GlobalTheory.T.integralExpansion_unique_of_uniformization hL.lemmaB V D A G U.toUnifPre k σ f g hf hg
  obtain ⟨E', ⟨t, ht, σ', f', h₁, h₂, h₃⟩, hP⟩ := hB s E hE s' ⟨u, hu, hc,
    (secRel_iff hLG _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => hs' _ _ y J hJ⟩
  have h₂' : IsBC D.toPre (FractionRing V) (toF V (FractionRing V) t • E') f' := isBC_of_scal h₂
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.integralDegenerationFamily_baseChange_extensionField hL.globalFns V _ D k E f hEg F
  obtain ⟨θ', hθ'⟩ := GlobalTheory.T.integralDegenerationFamily_baseChange_extensionField hL.globalFns V _ D (k * N) _ f' h₂' F
  have hP' := GlobalTheory.T.pullAl_linear_combination hL.globalFns V D (FractionRing V) O oa a k N 1 one_pos
    (fun _ => toF V (FractionRing V) t) (fun _ => E) (fun _ => E') (fun _ => hP)
  rw [Fin.sum_univ_one, Fin.sum_univ_one] at hP'
  refine ⟨t, σ', f', θ, θ', ht, h₃, hθ, hθ', GlobalTheory.T.pullAl_extension_field_of_fraction V D F O oa a k N _ _ _ f' _ θ'
    (IsBC.smul hEg t) h₂' (IsBC.smul hθ t) hθ' hP', fun Z r z J hJ => ?_⟩
  rw [secScal_val h₁ r z hJ, gs_scal, hs' _ r z J hJ, hs _ _ z J hJ]

end Term

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

theorem of_generic (hL : Laws) (U : Unif (maximalIdeal V) D A G) {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (φ : G ⟶ G) (k N : ℕ) (hk : 1 ≤ k)
    (hB : ∀ (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E → ∀ s' : U.SecK (k * N),
      IsPullByEnd U φ k N s s' → ∃ E' : Fam D.toPre (FractionRing V) (k * N), U.Expands (k * N) s' E' ∧
        PullAl D (FractionRing V) oa a k N E E')
    (u : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![gK, endK φ ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)])) (hu : u.IsGen)
    (hc : LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u unitK)
      (LB.pullGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig (k * (N - 1))) (jK V)))
    (F : Type) [Field F] [Algebra (FractionRing V) F]
    (σ' : U.SecGF F k) (s : Fam D.toPre F k) (hs : U.ExpandsG F k σ' s) (σ'' : U.SecGF F (k * N))
    (hσ : ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval σ'' (𝟙 _) y J =
      sval σ' ((TFK (R := V) F) ◁ (Over.pullback (jK V)).map φ).left y J *
        (val u (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left y J).val) :
    ∃ s'' : Fam D.toPre F (k * N), PullAl D F oa a k N s s'' ∧ U.ExpandsG F (k * N) σ'' s'' := by
  obtain ⟨n, c, σ, f, h₁, h₂, h₃⟩ := hs
  choose t τ f' θ θ' ht hτ hθ hθ' hP hv using fun i => term hL U oa a φ k N hk hB u hu hc F (σ i) (f i) (h₁ i)
  have hs := (secLin_iff_comb c hθ s).1 h₃
  let c' : Fin n → F := fun i => c i * (toF V F (t i))⁻¹
  have hc' : ∀ i, c' i * toF V F (t i) = c i := fun i => inv_mul_cancel_right₀ (toF_ne_zero F (ht i)) _
  refine ⟨∑ i, c' i • θ' i, ?_, n, c', τ, f', hτ, ?_, (secLin_iff_comb c' hθ' _).2 rfl⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨t₀, -, -, θ₀, θ₀', -, -, -, -, hP₀, -⟩ :=
        term hL U oa a φ k N hk hB u hu hc F _ _ (fun e => expandsAt_zero U.toUnifPre e k)
      have := GlobalTheory.T.pullAl_linear_combination hL.globalFns V D F O oa a k N 1 one_pos (fun _ => 0) _ _ (fun _ => hP₀)
      rw [Fin.sum_univ_one, Fin.sum_univ_one, zero_smul, zero_smul] at this
      rw [hs, Fin.sum_univ_zero, Fin.sum_univ_zero]
      exact this
    · have := GlobalTheory.T.pullAl_linear_combination hL.globalFns V D F O oa a k N n hn c' _ _ hP
      simp only [smul_smul, hc'] at this
      rw [hs]
      exact this
  · refine (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_
    rw [hσ y J hJ, secLin_val h₂ _ y hJ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e₁ : ((TFK (R := V) F) ◁ (Over.pullback (jK V)).map φ).left ≫
        (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left =
        (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    have e₂ : ((TFK (R := V) F) ◁ (Over.pullback (jK V)).map φ).left ≫ UnifPre.gFK (G := G) F =
        ((snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ endK φ) ≫ gK := by
      rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
        Category.assoc]
      rfl
    have e₃ : (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ pullback.snd G.hom (jK V) ≫ jK V =
        (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ Spec.map (CommRingCat.ofHom (toF V F)) := by
      rw [← hom_TF, ← Category.assoc, ← Category.assoc]
      congr 1
      exact (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G))).trans
        (Over.w (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G))).symm
    have e₄ := hv i _ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left y J hJ
    rw [e₃, constVal_specMap] at e₄
    rw [gs_scal, gs_scal, e₁, e₂, Category.id_comp, Category.id_comp]
    refine Eq.trans ?_ (congrArg _ e₄.symm)
    rw [← hc' i, constVal_mul]
    ring

end Main

theorem main : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, (k = 1 ∨ 4 ≤ k) → ∀ (u : LB.Gen (LB.LinComb P.U.LG.L (K := Fin 2) ![gK, endK (t.act.act a) ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)])), u.IsGen → LB.Gen.Corr P.U.LG.L _ _ _ _ (LB.pullGen P.U.LG.L _ _ u unitK) (LB.pullGen P.U.LG.L _ _ (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig (k * (N - 1))) (jK V)) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (σ' : P.U.SecGF F k) (s : Fam P.D.toPre F k), P.U.ExpandsG F k σ' s → ∀ σ'' : P.U.SecGF F (k * N), (∀ (y : (UnifPre.GF (G := t.G) F).left) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ'' (𝟙 _) y J = Geo.Tor.sval σ' ((TFK (R := V) F) ◁ (Over.pullback (jK V)).map (t.act.act a)).left y J * (Geo.Tor.val u (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left y J).val) → ∃ s'' : Fam P.D.toPre F (k * N), PullAl P.D F P.oD a k N s s'' ∧ P.U.ExpandsG F (k * N) σ'' s'' := by
  intro hL V _ _ _ E _ _ _ H t P a N hN hN0 k hk u hu hc F _ _ σ' s hs σ'' hσ
  letI := H.starRing
  refine of_generic hL P.U P.oD a (t.act.act a) k N (by omega) ?_ u hu hc F σ' s hs σ'' hσ
  rcases hk with rfl | hk
  · exact GlobalTheory.T.expansion_pullback_sourceLevelOne hL V E H t P a N hN hN0
  · exact GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le hL V E H t P a N hN hN0 k hk

end GlobalTheory.PullExpField
