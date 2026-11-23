import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast

set_option maxHeartbeats 400000

noncomputable section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace A5x6

theorem pt_det_isUnit {K : Type} [CommRing K] (h : Point K) : IsUnit (pt h.1 h.2).det :=
  Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI h.1 h.2)

theorem isPSD_zero {X : Type} (F : Finset X) (k : X → X → ℂ)
    (h : ∀ x ∈ F, ∀ y ∈ F, k x y = 0) : IsPSD F k := by
  unfold IsPSD
  intro a
  have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y = 0 :=
    Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => by rw [h x hx y hy, mul_zero]
  rw [e]
  simp

theorem mulR_eq {K : Type} [CommRing K] (R : Subring K) (d e : K) (hd : d ∈ R) (he : e ∈ R)
    (hde : d * e = 1) : mulR R d = R.toAddSubgroup := by
  unfold mulR
  ext z
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact R.mul_mem hd hy
  · intro hz
    exact ⟨e * z, R.mul_mem he hz, by rw [← mul_assoc, hde, one_mul]⟩

theorem modK_eq_one {K : Type} [CommRing K] (R : Subring K) (d e : K) (hd : d ∈ R) (he : e ∈ R)
    (hde : d * e = 1) : modK R d = 1 := by
  unfold modK
  rw [mulR_eq R d e hd he hde]
  simp [AddSubgroup.relIndex_self]

theorem det_mem {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : IsInt R M) : M.det ∈ R := by
  rw [Matrix.det_apply]
  refine R.sum_mem fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => hM _ _)

theorem glr_det {K : Type} [CommRing K] (R : Subring K) (h : Point K) (hh : InGLR R h) :
    (pt h.1 h.2).det ∈ R ∧ (pt h.1 h.2)⁻¹.det ∈ R ∧ (pt h.1 h.2).det * (pt h.1 h.2)⁻¹.det = 1 := by
  obtain ⟨h1, h2⟩ := hh
  refine ⟨det_mem R _ h1, det_mem R _ h2, ?_⟩
  rw [Matrix.det_nonsing_inv, Ring.mul_inverse_cancel _ (pt_det_isUnit h)]

theorem cSize_glr {K : Type} [CommRing K] (R : Subring K) (h : Point K) (hh : InGLR R h) :
    cSize R h = 1 := by
  obtain ⟨h1, h2, h3⟩ := glr_det R h hh
  unfold cSize
  rw [modK_eq_one R _ _ h1 h2 h3]
  simp

theorem first_theta_equality_of_kernel_facts (hPer : SingleBlockPeriodic) (hGram : SingleBlockPosSemidef) (hPars : SingleBlockParseval) (hSup : NsSupport)
    (hBD : NsBlockDiag) : SingleBlockThetaProps := by
  intro K _ _ _ R ψ hL m
  classical
  have hrep : ∀ x : K ⧸ R.toAddSubgroup, ∃ u : Kˣ, ((u : K) : K ⧸ R.toAddSubgroup) = x := by
    intro x
    obtain ⟨r, hr, hu⟩ := hL.unitRep (Quotient.out x)
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff r).mpr hr,
      add_zero]
    exact QuotientAddGroup.out_eq' x
  choose cr hcr using hrep
  have hcrsub : ∀ x : K, ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x ∈ R := by
    intro x
    have h1 := QuotientAddGroup.eq.mp (hcr (x : K ⧸ R.toAddSubgroup))
    have h2 := R.toAddSubgroup.neg_mem h1
    have e : -(-((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) + x) =
      ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x := by ring
    rw [e] at h2; exact h2
  let Θ : K → Point K → Point K → ℂ := fun x h h' =>
    Ns R ψ 1 h h' (cr (x : K ⧸ R.toAddSubgroup)) (cr (x : K ⧸ R.toAddSubgroup))
  have hΘt : ∀ (t : Kˣ) (h h' : Point K), h.1.sum = h'.1.sum →
      Θ (t : K) h h' = Ns R ψ 1 h h' t t :=
    fun t h h' e => hPer K R ψ hL h h' _ _ e (hcrsub t)
  have hsum : ∀ h h' : Point K, h.1.sum = h'.1.sum →
      ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
        ((cSize R h * cSize R h' : ℝ) : ℂ) * N0 R ψ h h' := by
    intro h h' e
    rw [← (hPars K R ψ hL h h' e cr hcr).2]
    apply finsum_congr
    intro x
    simp only [Θ]
    rw [QuotientAddGroup.out_eq']
  have hglr : ∀ h h' : Point K, InGLR R h → ∀ y : K ⧸ R.toAddSubgroup,
      Ns R ψ 1 h h' (cr y) (cr y) ≠ 0 → y = 0 := by
    intro h h' hh y h0
    obtain ⟨h1, h2, h3⟩ := glr_det R h hh
    have h4 := (hSup K R ψ 1 le_rfl h h' _ _ h0).1
    have h5 : ((cr y : Kˣ) : K) ∈ R := by
      have := R.mul_mem h2 h4
      rwa [← mul_assoc, mul_comm _ (pt h.1 h.2).det, h3, one_mul] at this
    rw [← hcr y]
    exact (QuotientAddGroup.eq_zero_iff _).mpr h5
  refine ⟨Θ, fun t h h' e e' => hΘt t h h' (e.trans e'.symm),
    fun h h' e e' => hsum h h' (e.trans e'.symm), fun F hF => ?_⟩
  have hFF : ∀ h ∈ F, ∀ h' ∈ F, h.1.sum = h'.1.sum := fun h hh h' hh' =>
    (hF h hh).trans (hF h' hh').symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x r hr
    have : ((x + r : K) : K ⧸ R.toAddSubgroup) = (x : K ⧸ R.toAddSubgroup) := by
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff r).mpr hr, add_zero]
    funext h h'
    simp only [Θ]
    rw [this]
  · intro x
    exact hGram K R ψ hL m F hF (cr x)
  · obtain ⟨ϖ, hϖ, hϖx⟩ := hL.unif
    choose M hM using fun h : Point K => hϖx (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)
    let N := F.sup M
    let L : Submodule R K :=
      { carrier := {x | (ϖ : K) ^ N * x ∈ R}
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [mul_add]; exact R.add_mem ha hb
        zero_mem' := by simp [R.zero_mem]
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_ofPred_eq] at hx ⊢
          rw [Subring.smul_def, smul_eq_mul, mul_left_comm]
          exact R.mul_mem c.2 hx }
    refine ⟨L, ?_, ?_, ?_⟩
    · exact hL.isOpen.preimage (continuous_const_mul ((ϖ : K) ^ N))
    · have : (L : Set K) = (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ N * x) '' (R : Set K) := by
        ext x
        constructor
        · intro hx
          refine ⟨(ϖ : K) ^ N * x, hx, ?_⟩
          simp only
          rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
        · rintro ⟨y, hy, rfl⟩
          show (ϖ : K) ^ N * (((ϖ⁻¹ : Kˣ) : K) ^ N * y) ∈ R
          rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
          exact hy
      rw [this]
      exact hL.isCompact.image (continuous_const_mul _)
    · intro x hx h hh h' _
      by_contra h0
      apply hx
      have h4 := (hSup K R ψ 1 le_rfl h h' _ _ h0).1
      have hle : M h ≤ N := Finset.le_sup (f := M) hh
      show (ϖ : K) ^ N * x ∈ R
      have hpN : (ϖ : K) ^ N ∈ R := R.pow_mem hϖ N
      have e1 : (ϖ : K) ^ N * x = (ϖ : K) ^ (N - M h) *
          (((ϖ : K) ^ M h * (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K)) *
            ((pt h.1 h.2).det * ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K))) -
          (ϖ : K) ^ N * (((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x) := by
        have e2 : (((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) * (pt h.1 h.2).det = 1 :=
          IsUnit.val_inv_mul (pt_det_isUnit h)
        have e3 : (ϖ : K) ^ N = (ϖ : K) ^ (N - M h) * (ϖ : K) ^ M h := by
          rw [← pow_add, Nat.sub_add_cancel hle]
        calc (ϖ : K) ^ N * x = (ϖ : K) ^ N * ((((pt_det_isUnit h).unit⁻¹ : Kˣ) : K) *
              (pt h.1 h.2).det) * ((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) -
              (ϖ : K) ^ N * (((cr (x : K ⧸ R.toAddSubgroup) : Kˣ) : K) - x) := by
                rw [e2]; ring
          _ = _ := by rw [e3]; ring
      rw [e1]
      exact R.sub_mem (R.mul_mem (R.pow_mem hϖ _) (R.mul_mem (hM h) h4))
        (R.mul_mem hpN (hcrsub x))
  · intro t
    apply isPSD_zero
    intro h hh h' hh'
    rw [hΘt t h h' (hFF h hh h' hh'), sub_self]
  · apply isPSD_zero
    intro h hh h' hh'
    rw [hsum h h' (hFF h hh h' hh'), pow_one, pow_one, sub_self]
  · intro x h hh h' hh' hne
    by_contra h0
    exact hne ((hBD K R ψ hL h h' (hFF h hh h' hh')).2 1 _ h0)
  · intro hGL x
    apply isPSD_zero
    intro h hh h' hh'
    by_cases hx : x ∈ R
    · rw [if_pos hx]
      have P := (hPars K R ψ hL h h' (hFF h hh h' hh') cr hcr).2
      rw [finsum_eq_single _ (0 : K ⧸ R.toAddSubgroup) (fun y hy => by
        by_contra h0; exact hy (hglr h h' (hGL h hh) y h0)),
        cSize_glr R h (hGL h hh), cSize_glr R h' (hGL h' hh')] at P
      have hx0 : (x : K ⧸ R.toAddSubgroup) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hx
      simp only [Θ]
      rw [hx0, P]
      simp
    · rw [if_neg hx, zero_sub, neg_eq_zero]
      by_contra h0
      exact hx ((QuotientAddGroup.eq_zero_iff _).mp (hglr h h' (hGL h hh) _ h0))

theorem first_theta_eq_of_equality (h : SingleBlockThetaProps) : Th1Eq := by
  unfold Th1Eq
  unfold SingleBlockThetaProps at h
  intro K _ _ _ R ψ hLD m
  obtain ⟨Θ, h1, h2, h3⟩ := h K R ψ hLD m
  obtain ⟨hp, -⟩ := h3 ∅ (by simp)
  exact ⟨Θ, hp, h1, h2⟩

theorem first_level_of_equality (h : SingleBlockThetaProps) : A13 1 := by
  unfold A13 ThetaExists
  unfold SingleBlockThetaProps at h
  intro K _ _ _ R ψ hLD _ m F hF
  obtain ⟨Θ, -, -, h3⟩ := h K R ψ hLD m
  exact ⟨Θ, h3 F hF⟩

section KRfacts

variable {K : Type} [CommRing K] (R : Subring K)

theorem mem_rangeR (a : K) : a ∈ LinearMap.range (Algebra.linearMap R K) ↔ a ∈ R := by
  constructor
  · intro h
    obtain ⟨r, rfl⟩ := LinearMap.mem_range.mp h
    exact r.2
  · intro ha
    exact LinearMap.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩

theorem psiKR_mk (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (a : K) :
    psiKR R ψ (Submodule.Quotient.mk a : KR R) = ψ a := by
  unfold psiKR
  set b := Quotient.out (Submodule.Quotient.mk a : KR R) with hb
  have h1 : b - a ∈ R := by
    rw [← mem_rangeR R, ← Submodule.Quotient.eq]
    exact Quotient.out_eq _
  calc ψ b = ψ (a + (b - a)) := by congr 1; abel
    _ = ψ a := by rw [AddChar.map_add_eq_mul, hψ _ h1, mul_one]

theorem psiKR_add (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (x y : KR R) :
    psiKR R ψ (x + y) = psiKR R ψ x * psiKR R ψ y := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_add, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ,
    AddChar.map_add_eq_mul]

theorem latZ_le_ker {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) :
    latZ R Z ≤ LinearMap.ker (lamLin R Z) := by
  intro v hv
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hv)
  rw [LinearMap.mem_ker]
  simp only [lamLin, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [← hw]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hZ, Matrix.one_mulVec]
  rw [mem_rangeR]
  unfold lastCoord
  rw [LinearMap.sum_apply]
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · simp [coeLin]
    exact (w j).2
  · simp

def muZ {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) : coker R Z →ₗ[R] KR R :=
  (latZ R Z).liftQ (lamLin R Z) (latZ_le_ker R Z hZ)

theorem muZ_mk {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (v : Fin n → R) :
    muZ R Z hZ (Submodule.Quotient.mk v) = lamLin R Z v := rfl

theorem lamLin_out {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (β : coker R Z) :
    lamLin R Z (Quotient.out β) = muZ R Z hZ β := by
  rw [← muZ_mk R Z hZ (Quotient.out β)]
  congr 1
  exact Quotient.out_eq β

theorem mem_isoZZ_iff {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K)
    (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det) (θ : coker R Z ≃ₗ[R] coker R Z') :
    θ ∈ isoZZ R Z Z' ↔ eZ R Z - θ.symm (eZ R Z') = 0 ∧
      muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap = 0 := by
  rw [sub_eq_zero, sub_eq_zero, LinearEquiv.eq_symm_apply]
  simp only [isoZZ, Set.mem_setOf_eq]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h v v' hv => ?_⟩
  · refine LinearMap.ext fun β => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ β
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, muZ_mk]
    rw [← lamLin_out R Z' hZ']
    exact (h v _ (Quotient.out_eq _).symm).symm
  · rw [← muZ_mk R Z' hZ' v', ← hv, ← muZ_mk R Z hZ v, h]
    rfl

end KRfacts

theorem finsum_fiber {X Y T : Type} [AddGroup Y] [Fintype T] (κ : X → Y)
    (hκ : Function.Bijective κ) (g : T → Y) (f : T → ℂ) [∀ τ x, Decidable (g τ = -κ x)] :
    (Function.support fun x => ∑ τ : T, if g τ = -κ x then f τ else 0).Finite ∧
      ∑ᶠ x, ∑ τ : T, (if g τ = -κ x then f τ else 0) = ∑ τ : T, f τ := by
  have hfin : ∀ τ : T, (Function.support fun x => if g τ = -κ x then f τ else 0).Finite := by
    intro τ
    apply Set.Subsingleton.finite
    intro x hx y hy
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx hy
    apply hκ.1
    rw [← neg_inj, ← hx.1, ← hy.1]
  refine ⟨?_, ?_⟩
  · refine (Set.finite_iUnion hfin).subset ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    by_contra hcon
    apply hx
    apply Finset.sum_eq_zero
    intro τ _
    by_contra h0
    exact hcon (Set.mem_iUnion.mpr ⟨τ, h0⟩)
  · rw [finsum_sum_comm _ _ (fun τ _ => hfin τ)]
    apply Finset.sum_congr rfl
    intro τ _
    obtain ⟨x0, hx0⟩ := hκ.2 (-g τ)
    rw [finsum_eq_single _ x0]
    · rw [if_pos (by rw [hx0, neg_neg])]
    · intro x hx
      rw [if_neg]
      intro h
      apply hx
      apply hκ.1
      rw [hx0, h, neg_neg]

theorem first_kernel_inner_sum {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
    (hψ : ∀ r ∈ R, ψ r = 1) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det)
    (hC : Finite (coker R Z)) (hC' : Finite (coker R Z')) (hD : Finite (coker R Z →ₗ[R] KR R))
    (hOD1 : ∀ x : coker R Z, x = 0 →
      ∑ᶠ α : coker R Z →ₗ[R] KR R, psiKR R ψ (α x) = (Nat.card (coker R Z) : ℂ))
    (hOD2 : ∀ x : coker R Z, x ≠ 0 → ∑ᶠ α : coker R Z →ₗ[R] KR R, psiKR R ψ (α x) = 0)
    (hO1 : ∀ μ : coker R Z →ₗ[R] KR R, μ = 0 →
      ∑ᶠ β : coker R Z, psiKR R ψ (μ β) = (Nat.card (coker R Z) : ℂ))
    (hO2 : ∀ μ : coker R Z →ₗ[R] KR R, μ ≠ 0 → ∑ᶠ β : coker R Z, psiKR R ψ (μ β) = 0)
    {X : Type} (κ : X → K)
    (hκ : Function.Bijective (fun x => (Submodule.Quotient.mk (κ x) : KR R))) :
    (Function.support fun x => singleBlockInner R ψ Z Z' (κ x)).Finite ∧
      ∑ᶠ x, singleBlockInner R ψ Z Z' (κ x) = (Nat.card (coker R Z) : ℂ) * (Nat.card (coker R Z') : ℂ) *
        (Nat.card (isoZZ R Z Z') : ℂ) := by
  classical
  have : Finite (coker R Z ≃ₗ[R] coker R Z') :=
    Finite.of_injective (fun θ : coker R Z ≃ₗ[R] coker R Z' => (θ : coker R Z → coker R Z'))
      (fun x y h => LinearEquiv.ext (congrFun h))
  let _ := Fintype.ofFinite (coker R Z ≃ₗ[R] coker R Z')
  let _ := Fintype.ofFinite (coker R Z →ₗ[R] KR R)
  let _ := Fintype.ofFinite (coker R Z)
  let f : (coker R Z ≃ₗ[R] coker R Z') × (coker R Z →ₗ[R] KR R) × coker R Z → ℂ := fun τ =>
    psiKR R ψ (τ.2.1 (eZ R Z - τ.1.symm (eZ R Z')) +
      (lamLin R Z (Quotient.out τ.2.2) - lamLin R Z' (Quotient.out (τ.1 τ.2.2))))
  let g : (coker R Z ≃ₗ[R] coker R Z') × (coker R Z →ₗ[R] KR R) × coker R Z → KR R :=
    fun τ => τ.2.1 τ.2.2
  have hform : ∀ c : K, singleBlockInner R ψ Z Z' c =
      ∑ τ, if g τ = -(Submodule.Quotient.mk c : KR R) then f τ else 0 := by
    intro c
    unfold singleBlockInner
    rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro θ _
    rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro α _
    rw [finsum_eq_sum_of_fintype]
  have key := finsum_fiber (fun x => (Submodule.Quotient.mk (κ x) : KR R)) hκ g f
  simp only [hform]
  refine ⟨key.1, ?_⟩
  rw [key.2]
  have hf : ∀ τ, f τ = psiKR R ψ (τ.2.1 (eZ R Z - τ.1.symm (eZ R Z'))) *
      psiKR R ψ ((muZ R Z hZ - (muZ R Z' hZ').comp τ.1.toLinearMap) τ.2.2) := by
    intro τ
    simp only [f]
    rw [psiKR_add R ψ hψ, lamLin_out R Z hZ, lamLin_out R Z' hZ']
    rfl
  simp only [hf]
  rw [Fintype.sum_prod_type]
  have hθ : ∀ θ : coker R Z ≃ₗ[R] coker R Z',
      ∑ y : (coker R Z →ₗ[R] KR R) × coker R Z,
        psiKR R ψ (y.1 (eZ R Z - θ.symm (eZ R Z'))) *
          psiKR R ψ ((muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap) y.2) =
      if θ ∈ isoZZ R Z Z' then (Nat.card (coker R Z) : ℂ) * (Nat.card (coker R Z') : ℂ) else 0 := by
    intro θ
    rw [Fintype.sum_prod_type]
    simp only
    rw [← Finset.sum_mul_sum, ← finsum_eq_sum_of_fintype, ← finsum_eq_sum_of_fintype]
    by_cases h1 : eZ R Z - θ.symm (eZ R Z') = 0
    · by_cases h2 : muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap = 0
      · rw [hOD1 _ h1, hO1 _ h2, if_pos ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mpr ⟨h1, h2⟩),
          ← Nat.card_congr θ.toEquiv]
      · rw [hO2 _ h2, mul_zero, if_neg]
        intro h; exact h2 ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mp h).2
    · rw [hOD2 _ h1, zero_mul, if_neg]
      intro h; exact h1 ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mp h).1
  rw [Finset.sum_congr rfl (fun θ _ => hθ θ), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul,
    Nat.subtype_card (Finset.univ.filter (· ∈ isoZZ R Z Z')) (by simp)]
  ring

theorem orbZ_det {K : Type} [CommRing K] (w : Point K)
    (p : lowW K w.1 w.2 × upUniG K w.1.sum) : (orbZ w p).det = (pt w.1 w.2).det := by
  unfold orbZ
  rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K p.1.2.1, isUpUni_det K p.2.2, one_mul,
    mul_one]

theorem first_kernel_periodic_of_formula (hF : SingleBlockFormula) : SingleBlockPeriodic := by
  unfold SingleBlockPeriodic
  unfold SingleBlockFormula at hF
  intro K _ _ _ R ψ hLD h h' c c' hs hc
  rw [hF K R ψ hLD h h' c hs, hF K R ψ hLD h h' c' hs]
  have e : (Submodule.Quotient.mk (c : K) : KR R) = Submodule.Quotient.mk (c' : K) := by
    rw [Submodule.Quotient.eq, mem_rangeR]
    exact hc
  have e2 : ∀ {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K),
      singleBlockInner R ψ Z Z' (c : K) = singleBlockInner R ψ Z Z' (c' : K) := by
    intro n n' Z Z'
    unfold singleBlockInner
    rw [e]
  simp only [e2]

theorem first_kernel_parseval_of_formula (hF : SingleBlockFormula) (hI : IntFinite) (hCD : CharOrthDual) (hCO : CharOrth)
    (hCC : CokerCard) : SingleBlockParseval := by
  intro K _ _ _ R ψ hL h h' e cr hcr
  classical
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    simpa using (hL.selfDual 1).mpr R.one_mem r hr
  have hκ : Function.Bijective (fun x : K ⧸ R.toAddSubgroup =>
      (Submodule.Quotient.mk ((cr x : Kˣ) : K) : KR R)) := by
    constructor
    · intro x y hxy
      have h1 := (mem_rangeR R _).mp ((Submodule.Quotient.eq _).mp hxy)
      rw [← hcr x, ← hcr y]
      exact QuotientAddGroup.eq_iff_sub_mem.mpr h1
    · intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      refine ⟨(a : K ⧸ R.toAddSubgroup), ?_⟩
      apply (Submodule.Quotient.eq _).mpr
      rw [mem_rangeR]
      exact QuotientAddGroup.eq_iff_sub_mem.mp (hcr (a : K ⧸ R.toAddSubgroup))
  let G : (K ⧸ R.toAddSubgroup) → Cos R h × Cos R h' → ℂ := fun x q =>
    (if IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2)) then
      singleBlockInner R ψ (orbZ h (rep R q.1)) (orbZ h' (rep R q.2)) ((cr x : Kˣ) : K) else 0) *
      phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))
  have hG : ∀ q, (Function.support fun x => G x q).Finite ∧
      ∑ᶠ x, G x q = ((cSize R h * cSize R h' : ℝ) : ℂ) * pairTerm R ψ h h' q := by
    intro q
    by_cases hq : IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2))
    · have hZ : IsUnit (orbZ h (rep R q.1)).det := by rw [orbZ_det]; exact pt_det_isUnit h
      have hZ' : IsUnit (orbZ h' (rep R q.2)).det := by rw [orbZ_det]; exact pt_det_isUnit h'
      obtain ⟨hC, hcard⟩ := hCC K R ψ hL _ _ hq.1 hZ
      obtain ⟨hC', hcard'⟩ := hCC K R ψ hL _ _ hq.2 hZ'
      obtain ⟨hD, hOD⟩ := hCD K R ψ hL _ _ hq.1 hZ
      have hO := hCO K R ψ hL _ _ hq.1 hZ
      have key := first_kernel_inner_sum R ψ hψ _ _ hZ hZ' hC hC' hD
        (fun x hx => by rw [hOD x, if_pos hx]) (fun x hx => by rw [hOD x, if_neg hx]; simp)
        (fun μ hμ => by rw [hO μ, if_pos hμ]) (fun μ hμ => by rw [hO μ, if_neg hμ]; simp)
        (fun x : K ⧸ R.toAddSubgroup => ((cr x : Kˣ) : K)) hκ
      have hc : (Nat.card (coker R (orbZ h (rep R q.1))) : ℂ) = ((cSize R h : ℝ) : ℂ) := by
        rw [cSize, ← orbZ_det h (rep R q.1), ← hcard]; simp
      have hc' : (Nat.card (coker R (orbZ h' (rep R q.2))) : ℂ) = ((cSize R h' : ℝ) : ℂ) := by
        rw [cSize, ← orbZ_det h' (rep R q.2), ← hcard']; simp
      simp only [G, if_pos hq, mul_assoc]
      constructor
      · refine key.1.subset ?_
        intro x hx
        simp only [Function.mem_support, ne_eq] at hx ⊢
        intro h0; apply hx; rw [h0, zero_mul]
      · rw [← finsum_mul, key.2, hc, hc']
        unfold pairTerm
        rw [if_pos hq]
        push_cast
        ring
    · simp only [G, if_neg hq, pairTerm]
      simp
  have hS := (hI K R ψ hL h).prod (hI K R ψ hL h')
  have hNs : ∀ x, Ns R ψ 1 h h' (cr x) (cr x) = ∑ q ∈ hS.toFinset, G x q := by
    intro x
    rw [hF K R ψ hL h h' (cr x) e]
    apply finsum_eq_sum_of_support_subset
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    rw [Set.Finite.coe_toFinset]
    by_contra hcon
    apply hq
    rw [if_neg (fun hI' => hcon ⟨hI'.1, hI'.2⟩)]
    simp
  have hKp : N0 R ψ h h' = ∑ q ∈ hS.toFinset, pairTerm R ψ h h' q := by
    unfold N0 Kp
    apply finsum_eq_sum_of_support_subset
    intro q hq
    simp only [Function.mem_support, ne_eq, pairTerm] at hq
    rw [Set.Finite.coe_toFinset]
    by_contra hcon
    apply hq
    rw [if_neg (fun hI' => hcon ⟨hI'.1, hI'.2⟩)]
    simp
  simp only [hNs]
  constructor
  · refine (Set.Finite.biUnion hS.toFinset.finite_toSet (fun q _ => (hG q).1)).subset ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    by_contra hcon
    apply hx
    apply Finset.sum_eq_zero
    intro q hq
    by_contra h0
    exact hcon (Set.mem_biUnion (Finset.mem_coe.mpr hq) h0)
  · rw [finsum_sum_comm _ _ (fun q _ => (hG q).1), hKp, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => (hG q).2)

theorem addBlock_sum {K : Type} [CommRing K] (h : Point K) (s : ℕ) (t : Kˣ) :
    (addBlock h s t).1.sum = h.1.sum + s := by
  simp [addBlock]

theorem second_vanishing_of_triple_form (hTF : TripleForm) (hAvg : AvgClaim) (hEnd : TTEnd) : BlockKernelSupport := by
  intro K _ _ _ R ψ hL s hs h h' t t' hsz hN
  have hKp : Kp R ψ (addBlock h s t) (addBlock h' s t') ≠ 0 := by
    intro h0; apply hN; simp [Ns, h0]
  have e1 : (addBlock h s t).1.sum = (h.1.sum + (s - 1)) + 1 := by rw [addBlock_sum]; omega
  have e2 : (addBlock h' s t').1.sum = (h.1.sum + (s - 1)) + 1 := by rw [addBlock_sum]; omega
  rw [hTF K R ψ _ _ _ e1 e2] at hKp
  have desc : ∀ d, d + 1 ≤ s → intTT R ψ (h.1.sum + d) (addBlock h s t) (addBlock h' s t') =
      intTT R ψ h.1.sum (addBlock h s t) (addBlock h' s t') := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      rw [← ih (by omega)]
      exact hAvg K R ψ hL h h' s t t' (h.1.sum + d) hsz (by omega) (by omega)
  rw [desc (s - 1) (by omega)] at hKp
  unfold intTT at hKp
  by_contra hcon
  apply hKp
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  split_ifs with hI
  · have : IsEmpty {φ : coker R (orbZ (addBlock h s t) (rep R q.1)) ≃ₗ[R]
        coker R (orbZ (addBlock h' s t') (rep R q.2)) //
        φ ∈ isoZZ R (orbZ (addBlock h s t) (rep R q.1)) (orbZ (addBlock h' s t') (rep R q.2)) ∧
        InTT R h.1.sum (orbZ (addBlock h s t) (rep R q.1))
          (orbZ (addBlock h' s t') (rep R q.2)) φ} := by
      constructor
      rintro ⟨φ, hφ, hT⟩
      exact hcon (hEnd K R h h' s t t' hsz hs _ _ _ _ (rep R q.1).1.2.1 (rep R q.1).2.2
        (rep R q.2).1.2.1 (rep R q.2).2.2 φ hφ hT)
    simp [Nat.card_of_isEmpty]
  · simp

private lemma sum_mul_comp_eq_sum_image_filter {X Y : Type} [DecidableEq Y] (F : Finset X) (f : X → Y)
    (a : X → ℂ) (g : Y → ℂ) :
    ∑ x ∈ F, a x * g (f x) =
      ∑ y ∈ F.image f, (∑ x ∈ F.filter (fun x => f x = y), a x) * g y := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)
    (fun x => a x * g (f x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

theorem psd_comap {X Y : Type} [DecidableEq Y] (k : Y → Y → ℂ) (f : X → Y) (F : Finset X)
    (h : IsPSD (F.image f) k) : IsPSD F (fun x y => k (f x) (f y)) := by
  unfold IsPSD at h ⊢
  intro a
  obtain ⟨h1, h2⟩ := h (fun z => ∑ u ∈ F.filter (fun u => f u = z), a u)
  have e1 : ∀ z, ∑ y ∈ F, conj (a y) * k z (f y) =
      ∑ w ∈ F.image f, conj (∑ u ∈ F.filter (fun u => f u = w), a u) * k z w := by
    intro z
    rw [sum_mul_comp_eq_sum_image_filter F f (fun y => conj (a y)) (k z)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_sum]
  have key : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (f x) (f y) =
      ∑ x ∈ F.image f, ∑ y ∈ F.image f, (∑ u ∈ F.filter (fun u => f u = x), a u) *
        conj (∑ u ∈ F.filter (fun u => f u = y), a u) * k x y := by
    calc ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (f x) (f y)
        = ∑ x ∈ F, a x * ∑ y ∈ F, conj (a y) * k (f x) (f y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = ∑ z ∈ F.image f, (∑ u ∈ F.filter (fun u => f u = z), a u) *
            ∑ y ∈ F, conj (a y) * k z (f y) :=
          sum_mul_comp_eq_sum_image_filter F f a (fun z => ∑ y ∈ F, conj (a y) * k z (f y))
      _ = _ := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [e1 z, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
  rw [key]
  exact ⟨h1, h2⟩

private lemma isPSD_real_rescale {X : Type} (F : Finset X) (k : X → X → ℂ) (c : X → ℝ)
    (h : IsPSD F k) : IsPSD F (fun x y => (c x : ℂ) * (c y : ℂ) * k x y) := by
  unfold IsPSD at h ⊢
  intro a
  have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c x : ℂ) * (c y : ℂ) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, (a x * c x) * conj (a y * c y) * k x y := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [e]
  exact h _

theorem second_gram_of_kernel_gram (hG : KpGram) (hM : ModMul) : BlockKernelPosSemidef := by
  classical
  unfold BlockKernelPosSemidef
  unfold KpGram at hG
  unfold ModMul at hM
  intro K _ _ _ R ψ hLD s hs m F hF
  have hK := psd_comap (Kp R ψ) (fun x : Point K × Kˣ => addBlock x.1 s x.2) F
    (hG K R ψ hLD _)
  have hc := isPSD_real_rescale F _ (fun x : Point K × Kˣ => modK R (x.2 : K) ^ (s * (s - 1) / 2)) hK
  have e : (fun x y : Point K × Kˣ => Ns R ψ s x.1 y.1 x.2 y.2) = fun x y =>
      ((modK R (x.2 : K) ^ (s * (s - 1) / 2) : ℝ) : ℂ) *
        ((modK R (y.2 : K) ^ (s * (s - 1) / 2) : ℝ) : ℂ) *
        Kp R ψ (addBlock x.1 s x.2) (addBlock y.1 s y.2) := by
    funext x y
    unfold Ns
    rw [(hM K R ψ hLD x.2 y.2).2, mul_pow, Complex.ofReal_mul]
  rw [e]
  exact hc

theorem first_kernel_gram_of_second (h : BlockKernelPosSemidef) : SingleBlockPosSemidef := by
  classical
  unfold SingleBlockPosSemidef
  unfold BlockKernelPosSemidef at h
  intro K _ _ _ R ψ hLD m F hF c
  have hI := h K R ψ hLD 1 le_rfl m (F.image fun x => (x, c)) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hF y hy)
  exact psd_comap (fun x y : Point K × Kˣ => Ns R ψ 1 x.1 y.1 x.2 y.2) (fun x => (x, c)) F hI

end A5x6

open A5x6

theorem second_gram_of_gram_and_modulus : Formalism.FourierDecayAlt.A5.KpGram → Formalism.FourierDecayAlt.A5.ModMul → Formalism.FourierDecayAlt.A5.BlockKernelPosSemidef := fun hG hM => second_gram_of_kernel_gram hG hM

theorem second_gram_vanishing_of_parts : Formalism.FourierDecayAlt.A5.BlockKernelPropertiesOfSteps := by
  unfold Formalism.FourierDecayAlt.A5.BlockKernelPropertiesOfSteps Formalism.FourierDecayAlt.A5.A2
  intro hG hM hTF hAvg hEnd
  exact ⟨second_gram_of_kernel_gram hG hM, second_vanishing_of_triple_form hTF hAvg hEnd⟩

theorem first_kernel_properties_of_hypotheses : Formalism.FourierDecayAlt.A5.SingleBlockOfSteps := by
  unfold Formalism.FourierDecayAlt.A5.SingleBlockOfSteps
  intro hF hI hCD hCO hCC hG
  exact ⟨first_kernel_periodic_of_formula hF, first_kernel_gram_of_second hG, first_kernel_parseval_of_formula hF hI hCD hCO hCC⟩

theorem first_theta_properties_of_parts : Formalism.FourierDecayAlt.A5.SingleBlockThetaOfSteps := by
  unfold Formalism.FourierDecayAlt.A5.SingleBlockThetaOfSteps
  intro hPer hGram hPars hSup hBD _
  have h := first_theta_equality_of_kernel_facts hPer hGram hPars hSup hBD
  exact ⟨first_theta_eq_of_equality h, h⟩

theorem lattice_average_lemma_from_parts : Formalism.FourierDecayAlt.A5.LemmaAAssemble := by
  unfold Formalism.FourierDecayAlt.A5.LemmaAAssemble Formalism.FourierDecayAlt.A5.LemmaA
  intro hA2 hPars hTh hA13 hStep hN0 hSup hBD
  refine ⟨hA2, ?_, hTh, hA13, hN0, hSup, hBD⟩
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact first_level_of_equality hA13
  | succ s hs ih =>
    unfold Formalism.FourierDecayAlt.A5.A13 at ih ⊢
    intro K _ _ _ R ψ hLD hU
    unfold Formalism.FourierDecayAlt.A5.ThetaExistsStep at hStep
    exact hStep hA2 hPars K R ψ hLD hU s hs (ih K R ψ hLD hU)

end Formalism.FourierDecayAlt.P
