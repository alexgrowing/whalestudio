import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunction
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ChiEqOneOrOfSym
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenMultipleHermitianPositiveCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndomorphismOfLatticePreservingLinearStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecC

theorem frame_power_identity : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L M : LB A.left) (g : ℕ) (uL : HolUnif A L g) (uM : HolUnif A M g)
    (HL HM : Matrix (Fin g) (Fin g) ℂ) (χL : uL.Λ → ℂ) (χM : uM.Λ → ℂ), uM.ex = uL.ex →
    GlobalTheory.TorusRM.IsFactorAH uL HL χL → GlobalTheory.TorusRM.IsFactorAH uM HM χM →
    (∀ l, χL l = 1 ∨ χL l = -1) → (∀ l, χM l = 1 ∨ χM l = -1) →
    ∀ (N : ℕ) (K : Type) [Fintype K] (F : K → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ε : K → ℤ), Even N → (∀ k, Even (ε k)) →
    (∀ k, ∀ l ∈ uL.Λ, F k l ∈ uM.Λ) →
    (∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ HL.mulVec (star w)) = ∑ k, (ε k : ℂ) * (F k z ⬝ᵥ HM.mulVec (star (F k w)))) →
    ∀ (l : uL.Λ) (i : L.ι) (j : K → M.ι) (z : Fin g → ℂ), ⊤ ≤ (uL.ex z).left ⁻¹ᵁ L.U i →
      (∀ k, ⊤ ≤ (uM.ex (F k z)).left ⁻¹ᵁ M.U (j k)) →
      uL.fr i z ^ N * ∏ k, uM.fr (j k) (F k (z + l)) ^ ε k = uL.fr i (z + l) ^ N * ∏ k, uM.fr (j k) (F k z) ^ ε k := by
  intro A _ L M g uL uM HL HM χL χM _ hfL hfM hχL hχM N K _ F ε hN hε hF hdec l i j z hi hj
  have hL1 := hfL.2.2 l i z hi
  have hM1 : ∀ k, uM.fr (j k) (F k z) = χM ⟨F k l, hF k l l.2⟩ *
      Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) * uM.fr (j k) (F k (z + l)) := fun k => by
    rw [map_add]
    exact hfM.2.2 ⟨F k l, hF k l l.2⟩ (j k) (F k z) (hj k)
  have hcL : χL l ^ N = 1 := by
    rcases hχL l with h | h <;> rw [h]
    · exact one_pow N
    · exact hN.neg_one_pow
  have hcM : ∀ k, χM ⟨F k l, hF k l l.2⟩ ^ ε k = 1 := fun k => by
    rcases hχM ⟨F k l, hF k l l.2⟩ with h | h <;> rw [h]
    · exact one_zpow _
    · exact (hε k).neg_one_zpow
  have hR : ∏ k, uM.fr (j k) (F k z) ^ ε k = (∏ k, χM ⟨F k l, hF k l l.2⟩ ^ ε k) *
      (∏ k, Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) ^ ε k) * ∏ k, uM.fr (j k) (F k (z + l)) ^ ε k := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hM1 k, mul_zpow, mul_zpow]
  have key : Complex.exp (Real.pi * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) ^ N =
      ∏ k, Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) ^ ε k := by
    rw [← Complex.exp_nat_mul, Finset.prod_congr rfl (fun k _ => (Complex.exp_int_mul _ (ε k)).symm),
      ← Complex.exp_sum]
    congr 1
    have h1 := hdec z l
    have h2 := hdec l l
    calc (N : ℂ) * (Real.pi * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))))
        = Real.pi * ((N : ℂ) * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) +
          Real.pi / 2 * ((N : ℂ) * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) := by ring
      _ = Real.pi * ∑ k, (ε k : ℂ) * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
          Real.pi / 2 * ∑ k, (ε k : ℂ) * (F k l ⬝ᵥ HM.mulVec (star (F k l))) := by rw [h1, h2]
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
  rw [hR, hL1, mul_pow, mul_pow, hcL, Finset.prod_eq_one (fun k _ => hcM k), key]
  ring

theorem lbIso_of_sameFactor (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) (X Y : LB A.left) (g : ℕ)
    (u : HolUnif A X g) (v : HolUnif A Y g) (hX : X.IsLB) (hY : Y.IsLB) (hex : v.ex = u.ex)
    (hper : ∀ (l : u.Λ) i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ X.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ Y.U j →
      u.fr i z * v.fr j (z + l) = u.fr i (z + l) * v.fr j z) : LBIso X Y := by
  haveI := hA.comm
  haveI := hA.smooth
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨s, hs⟩ := HolUnifSec.exists_isFn (SameFactor.divUnif u v hex) hA hp (LB.isLB_div hY hX)
    (θ := fun _ => 1) (differentiable_const _) (by
      intro l hl p z hz
      obtain ⟨hz1, hz2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have e := hper ⟨l, hl⟩ p.2 p.1 z hz2 hz1
      have hl' : u.ex (z + l) = u.ex z := by
        rw [u.ex_add, (u.ker _).2 hl, _root_.mul_one]
      have n1 := u.fr_ne p.2 z hz2
      have n2 := u.fr_ne p.2 (z + l) (by rw [hl']; exact hz2)
      change 1 * (v.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹) = 1 * (v.fr p.1 z * (u.fr p.2 z)⁻¹)
      field_simp
      linear_combination e)
  exact SameFactor.exists_gen_of_isFn _ s _ hs fun _ => one_ne_zero

theorem sqDec_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB →
    RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L →
    LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → SqDec A L M := by
  intro A _ hA L M hL hM haL haM hsL hsM
  haveI := hA.comm
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim ℂ A hA
  obtain ⟨L₀, ⟨u₀⟩⟩ := HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨uL, HL, χL, hexL, hfL⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ L hL
  obtain ⟨uM, HM, χM, hexM, hfM⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  have hposL := AmpleHermPos.re_form_pos_of_relAmple A hA L hL haL g uL HL χL hfL.1 hfL.2.1 hfL.2.2
  have hposM := AmpleHermPos.re_form_pos_of_relAmple A hA M hM haM g uM HM χM hfM.1 hfM.2.1 hfM.2.2
  have hAHL := TorusRM.isAH_of_isFactorAH hfL hposL
  have hAHM := TorusRM.isAH_of_isFactorAH hfM hposM
  have hex : uM.ex = uL.ex := hexM.trans hexL.symm
  have hΛ : ∀ z, z ∈ uM.Λ ↔ z ∈ uL.Λ := fun z => by rw [← uM.ker, ← uL.ker, hex]
  have hχL := ThetaUnifCompare.chi_eq_one_or_of_sym hL (sym_of_lbIso_neg hsL.symm) hAHL
  have hχM := ThetaUnifCompare.chi_eq_one_or_of_sym hM (sym_of_lbIso_neg hsM.symm) hAHM
  have hiL : ∀ l ∈ uL.Λ, ∀ m ∈ uL.Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ HL.mulVec (star m)).im :=
    fun l hl m hm => FrameValue.exists_int_im hL hAHL ⟨l, hl⟩ ⟨m, hm⟩
  have hiM : ∀ l ∈ uL.Λ, ∀ m ∈ uL.Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ HM.mulVec (star m)).im :=
    fun l hl m hm => FrameValue.exists_int_im hM hAHM ⟨l, (hΛ l).2 hl⟩ ⟨m, (hΛ m).2 hm⟩
  obtain ⟨N, a₀, r, a, F, hN, ha₀, hNe, ha₀e, hae, hF, hdec⟩ :=
    GlobalTheory.T.exists_even_multiple_hermitian_positive_combination g uL.Λ uL.discrete uL.full HL HM hAHL.1 hAHM.1 hposL hposM hiL hiM
  choose β hβ hβF using fun i => GlobalTheory.T.exists_endomorphism_of_lattice_preserving_linear A hA L g uL (F i) (hF i)
  let f : Option (Fin r) → (A ⟶ A) := fun o => o.elim (𝟙 A) β
  let FF : Option (Fin r) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun o => o.elim LinearMap.id F
  let ε : Option (Fin r) → ℤ := fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)
  have hfF : ∀ k z, uM.ex (FF k z) = uL.ex z ≫ f k := by
    intro k z
    cases k with
    | none => simp [FF, f, hex]
    | some i => simpa [FF, f, hex] using hβF i z
  obtain ⟨u₁, hex₁, -, hfr₁⟩ := exists_holUnif_linComb A A L M g g uL uM _ f FF ε hfF
  have hcomb : LB.LinComb M (fun k => (f k).left) ε = LB.LinComb M (fun (o : Option (Fin r)) => o.elim (𝟙 A.left) fun i => (β i).left)
      (fun (o : Option (Fin r)) => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) := by
    congr 1
    funext o
    cases o <;> rfl
  refine ⟨N, a₀, r, a, β, hN, ha₀, hβ, ?_⟩
  rw [← hcomb]
  refine lbIso_of_sameFactor A hA _ _ g (ThetaGAGA.powFrame uL N) u₁ (isLB_lbPow hL N) (LB.isLB_linComb hM _ _)
    hex₁ ?_
  intro l i j z hi hj
  refine (congrArg₂ (· * ·) rfl (hfr₁ j (z + l))).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (hfr₁ j z)).symm)
  have hi' := ThetaGAGA.top_le_of_lbPow uL N i hi
  have hj' : ∀ k, ⊤ ≤ (uM.ex (FF k z)).left ⁻¹ᵁ M.U (j k) := fun k => by
    rw [hfF k z]
    exact (CubeValues.le_preimage_wchart (uL.ex z).left M (fun k => (f k).left) j).1 hj k
  exact frame_power_identity A L M g uL uM HL HM χL χM hex hfL hfM hχL hχM N _ FF ε hNe
    (fun k => by cases k with | none => exact (Int.even_coe_nat _).2 ha₀e | some i => exact (Int.even_coe_nat _).2 (hae i))
    (fun k l hl => by cases k with | none => exact (hΛ l).2 hl | some i => exact (hΛ _).2 (hF i l hl))
    (fun z w => by rw [Fintype.sum_option, hdec z w]; simp [FF, ε]) l (i PUnit.unit) j z hi' hj'

end GlobalTheory.SqDecC
