import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyProductPartialSumsDvdPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescEqXPowSmulNablaPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NablaPowApplySmulLeibnizStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescNEqXPowMulIterateDerivativeStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TaylorBasis

theorem cauchy_dvd {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R)
    (hA : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p)
    (hB : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) :=
  GlobalTheory.T.cauchy_product_partial_sums_dvd_pow x α β A B hA hB r

theorem desc_eq {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (v : Vec K a ι) : C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v :=
  GlobalTheory.T.desc_eq_X_pow_smul_nabla_pow' C k v

theorem nabla_pow_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (f : ZMod a → K⟦X⟧) (v : Vec K a ι) : (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) :=
  GlobalTheory.T.nabla_pow_apply_smul_leibniz C k f v

theorem descN_eq (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) :
    descN K p f = X ^ p * (⇑(derivative K))^[p] f :=
  GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' K p f

theorem muDiv_mul_choose {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {k p : ℕ} (h : p ≤ k) :
    ϖ.muDiv a O g k * (k.choose p : OCr l O) = ϖ.muDiv a O g p * ϖ.muDiv a O g (k - p) := by
  have hx := ϖ.theta_mu (ϖ.gal_pi a g)
  have key : dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) = dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p) := by
    apply sub_eq_zero.1
    refine acris_nat_cancel (Nat.factorial_ne_zero k) ?_
    have hf : (k.factorial : Per.Acris l) = (k.choose p : Per.Acris l) * p.factorial * (k - p).factorial := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial h]
    rw [show (k.factorial : Per.Acris l) * (dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) -
        dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p)) = (k.choose p : Per.Acris l) * ((k.factorial : Per.Acris l) *
        dpow (ϖ.mu g) hx k) - (k.choose p : Per.Acris l) * (((p.factorial : Per.Acris l) * dpow (ϖ.mu g) hx p) *
        (((k - p).factorial : Per.Acris l) * dpow (ϖ.mu g) hx (k - p))) by
      linear_combination (-(dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p))) * hf]
    rw [factorial_mul_dpow, factorial_mul_dpow, factorial_mul_dpow, ← pow_add, Nat.add_sub_cancel' h, sub_self]
  have hm : ∀ n, ϖ.muDiv a O g n =
      (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) (dpow (ϖ.mu g) hx n) := fun n => rfl
  rw [hm, hm, hm, ← map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O), ← map_mul,
    ← map_mul, key]

theorem galOCr_iC_taylor {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) (c : ZMod a → S O K e) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ galOCr O (g : GQ l) (ϖ.iC t K c) -
      ∑ p ∈ Finset.range n, ϖ.muDiv a O g p * ϖ.iC t K (fun τ => ⟨descN K p (c τ), descN_mem_S e p (c τ).2⟩) := by
  choose N hN using fun τ : ZMod a => ϖ.taylor_S a O K g (c τ) r
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun τ => hN τ n ((Finset.le_sup (Finset.mem_univ τ)).trans hn)
  refine ⟨∑ τ, idem (constC t) τ * z τ, ?_⟩
  simp only [PiSys.iC, glue_apply, map_sum, map_mul, galOCr_idem, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_left_comm, ← hz τ, mul_sub, Finset.mul_sum]
  simp only [mul_left_comm (idem (constC t) τ)]

theorem coord_desc {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (m : Vec K a ι) (k : ℕ) (τ : ZMod a) (i : ι) :
    (P.mxInv τ *ᵥ C.desc k m τ) i = ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) *
      (descN K p ((P.mxInv τ *ᵥ m τ) j) * (X ^ (k - p) * (P.mxInv τ *ᵥ (C.nabla ^ (k - p)) (P.phi (bas j)) τ) i)) := by
  have hΦ : ∀ (f : ZMod a → K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (f • w) τ) i = f τ * (P.mxInv τ *ᵥ w τ) i := fun f w => by
    rw [Pi.smul_apply', Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦs : ∀ (s : K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (s • w) τ) i = s * (P.mxInv τ *ᵥ w τ) i := fun s w => by
    rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦsum : ∀ {J : Type} (s : Finset J) (w : J → Vec K a ι),
      (P.mxInv τ *ᵥ (∑ x ∈ s, w x) τ) i = ∑ x ∈ s, (P.mxInv τ *ᵥ w x τ) i := fun s w => by
    rw [Finset.sum_apply, Matrix.mulVec_sum, Finset.sum_apply]
  conv_lhs => rw [desc_eq, P.eq_sum_phi_bas m]
  rw [hΦs, map_sum, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nabla_pow_smul, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
  rw [hΦs, hΦ, descN_eq]
  have hX : (X : K⟦X⟧) ^ k = X ^ p * X ^ (k - p) := by rw [← pow_add, Nat.add_sub_cancel' hpk]
  rw [hX]
  ring

theorem taylor_of_basis {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type}
    [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (C : Conn P)
    (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι),
      (X : K⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S O K e)
    (hΓ : ∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (l : OCr l O) ^ r ∣ toOCr l O (Γ i j) -
        ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ j k i⟩)) :
    I.Taylor C := by
  intro g
  obtain ⟨Γ, hΓL, hconv⟩ := hΓ g
  refine ⟨Γ, hΓL, fun m r => ?_⟩
  let c : ι → ZMod a → ↥(S O K e) := coordL P (S O K e) m
  have hcj : ∀ j τ, (c j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m : Vec K a ι) τ) j := fun j τ => rfl
  have hcm : ∀ j, toCris t ϖ P m j = ϖ.iC t K (c j) := fun j => rfl
  have F3 : ∀ k i, toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩ i =
      ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : OCr l O) *
        (ϖ.iC t K (fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) *
          ϖ.iC t K (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
    intro k i
    have h1 : coordL P (S O K e) ⟨C.desc k m, C.desc_mem k m.2⟩ i =
        ∑ j, ∑ p ∈ Finset.range (k + 1), ((k.choose p : ℕ) : ZMod a → ↥(S O K e)) *
          ((fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) * (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
      funext τ
      apply Subtype.ext
      refine (coord_desc C m k τ i).trans ?_
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, AddSubmonoidClass.coe_finset_sum,
        MulMemClass.coe_mul, SubringClass.coe_natCast, hcj]
    rw [toCris_apply, h1]
    simp only [map_sum, map_mul, map_natCast]
  have key : ∀ p : ι × ι, ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      galOCr O (g : GQ l) (ϖ.iC t K (c p.2)) * toOCr l O (Γ p.1 p.2) -
        ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c p.2 τ), descN_mem_S e q (c p.2 τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 (k - q) p.1⟩)) :=
    fun p => cauchy_dvd _ _ (fun k => ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 k p.1⟩)) _ _
      (fun r => galOCr_iC_taylor t ϖ g (c p.2) r) (fun r => hconv p.1 p.2 r) r
  choose N hN using key
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun p : ι × ι => hN p n ((Finset.le_sup (Finset.mem_univ p)).trans hn)
  refine ⟨fun i => ∑ j, z (i, j), funext fun i => ?_⟩
  have e1 : (Γ.map (toOCr l O) *ᵥ fun j => galOCr O (g : GQ l) (toCris t ϖ P m j)) i =
      ∑ j, galOCr O (g : GQ l) (ϖ.iC t K (c j)) * toOCr l O (Γ i j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hcm]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : (∑ k ∈ Finset.range n, ϖ.muDiv a O g k • toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩) i =
      ∑ j, ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c j τ), descN_mem_S e q (c j τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ j (k - q) i⟩)) := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, F3, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
    rw [← mul_assoc, muDiv_mul_choose a O ϖ g (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))]
    ring
  rw [Pi.sub_apply, e1, e2, ← Finset.sum_sub_distrib, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => hz (i, j)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : Lat a ↥(OL LL) ↥LL.1 ϖ) (I : Ident (thetaW a LL) ϖ P T) (C : Conn P) (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e), (∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩)) → I.Taylor C :=
  fun _ _ _ _ _ _ ϖ LL _ _ _ _ _ _ _ _ I C hS hΓ => taylor_of_basis (thetaW _ LL) ϖ I C hS hΓ

end GlobalTheory.TaylorBasis
