import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationVStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowMulPhiMatrixInvAhatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HsumMulEisensteinCompletionPowIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRImageBcrisEqAinfHatCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisImagesBasisBdRplusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR.CmpFil

theorem amulG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ∀ o o', ι' (o * o') = ι' o * ι' o') (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (x y : OD l O) (v : V ⊗[ℚ_[l]] R) : A (x * y) v = A x (A y v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul v c =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [add_mul, map_add, AddMonoidHom.add_apply, hx, hx']
    | tmul o b =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
      | add y y' hy hy' => simp only [mul_add, map_add, AddMonoidHom.add_apply, hy, hy']
      | tmul o' b' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hA, hA, hA, map_mul, mul_assoc, h1, mul_smul]

theorem aoneG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ι' 1 = 1) (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (v : V ⊗[ℚ_[l]] R) : A 1 v = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul v c => rw [Algebra.TensorProduct.one_def, hA, map_one, one_mul, h1, one_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem amulL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (x y : OD l ↥(OL LL)) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A (x * y) v = A x (A y v) :=
  amulG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) (fun _ _ => rfl) (GlobalTheory.BKGal.JumpDR.cD Td) A hA x y v

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem aoneL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A 1 v = v :=
  aoneG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) rfl (GlobalTheory.BKGal.JumpDR.cD Td) A hA v

set_option maxHeartbeats 1000000 in
theorem coreG {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {W : Type} [AddCommGroup W] (A : OD l O →+ (W →+ W)) (Fil : ℤ → W → Prop)
    (amul : ∀ x y v, A (x * y) v = A x (A y v)) (aone : ∀ v, A 1 v = v)
    (hbij : Function.Bijective (A (ϖ.iD t K (fun _ => Ehat O K l e))))
    (hS : ∀ (y : W) (j : ℤ), Fil j y ↔ Fil (j + 1) (A (ϖ.iD t K (fun _ => Ehat O K l e)) y))
    (gB : ι → W) (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e)
    (hy : ∀ τ j i, algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i))
    (f : ι → W) (hf1 : ∀ i, A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i) = ∑ j, A (ϖ.iD t K (fun τ => y τ j i)) (gB j))
    (hspan : ∀ v, Fil 0 v ↔ ∃ d : ι → OD l O, v = ∑ i, A (d i) (f i))
    (hind : ∀ d : ι → OD l O, ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0)
    {n : ℕ} (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (g : Fin n → W)
    (hC : ∀ (s' : Fin n → ZMod a → Ahat O K l e) (c : ZMod a → ι → Ahat O K l e), (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD t K (s' k)) (g k) = ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j))
    (hE1 : ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i)
    (j : ℤ) :
    GlobalTheory.BKGal.JumpDR.InEhat O K l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ Fil j (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
  classical
  have hbijN : ∀ N : ℕ, Function.Bijective (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) := by
    intro N
    induction N with
    | zero =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ 0)) = id := funext fun v => by rw [pow_zero]; exact aone v
      rw [h0]; exact Function.bijective_id
    | succ N ih =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1))) = ⇑(A (ϖ.iD t K (fun _ => Ehat O K l e))) ∘ ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) :=
        funext fun v => by rw [pow_succ', amul]; rfl
      rw [h0]; exact hbij.comp ih
  have hSh : ∀ (N : ℕ) (y : W) (j : ℤ), Fil j y ↔ Fil (j + N) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by
    intro N
    induction N with
    | zero => intro y j; rw [pow_zero, aone, Nat.cast_zero, add_zero]
    | succ N ih =>
      intro y j
      have e1 : (j + ((N + 1 : ℕ) : ℤ)) = (j + N) + 1 := by push_cast; ring
      have e2 : A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1)) y = A (ϖ.iD t K (fun _ => Ehat O K l e)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by rw [pow_succ', amul]
      rw [e1, e2]
      exact (ih y j).trans (hS _ _)
  have Fb : ∀ (d : ι → OD l O) (kk : ℕ), Fil kk (∑ i, A (d i) (f i)) ↔ ∀ i, d i ∈ Ideal.span {(ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk} := by
    intro d kk
    constructor
    · intro hd
      obtain ⟨v', hv'⟩ := (hbijN kk).2 (∑ i, A (d i) (f i))
      have h0 : Fil 0 v' := (hSh kk v' 0).2 (by rw [hv', zero_add]; exact hd)
      obtain ⟨z, rfl⟩ := (hspan v').1 h0
      have h4 : ∑ i, A (d i - (ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk * z i) (f i) = 0 := by
        simp only [map_sub, AddMonoidHom.sub_apply, Finset.sum_sub_distrib, amul]
        rw [← map_sum, hv', sub_self]
      intro i
      have h5 := hind _ h4 i
      rw [sub_eq_zero] at h5
      rw [h5]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hd
      choose z hz using fun i => Ideal.mem_span_singleton'.1 (hd i)
      have h6 : ∑ i, A (d i) (f i) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk) (∑ i, A (z i) (f i)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hz i, mul_comm, amul]
      have h7 := (hSh kk _ 0).1 ((hspan _).2 ⟨z, rfl⟩)
      rw [zero_add] at h7
      rw [h6]; exact h7
  have key : ∀ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), (∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
      A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) (∑ k, A (ϖ.iD t K (s k)) (g k)) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i) := by
    intro N x hx
    let s' : Fin n → ZMod a → Ahat O K l e := fun k => (fun _ => Ehat O K l e) ^ (N + β) * s k
    let c : ZMod a → ι → Ahat O K l e := fun τ j => ∑ i, y τ j i * x τ i
    have hw : ∀ τ i, GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N + β) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i
      simp only [GlobalTheory.BKGal.JumpDR.hsum, s', Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, Finset.mul_sum, mul_assoc]
    have hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i := by
      intro τ j
      simp only [c, map_sum, map_mul, hy, hx, hw]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hC' := hC s' c hc
    have h1 : ∑ k, A (ϖ.iD t K (s' k)) (g k) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + β)) (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [s', map_mul, map_pow]
      rw [amul]
    have h2' : ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) := by
      have h3 : ∀ j, (fun τ => c τ j) = ∑ i, (fun τ => x τ i) * (fun τ => y τ j i) := by
        intro j; funext τ; simp only [c, Finset.sum_apply, Pi.mul_apply, mul_comm]
      simp only [h3, map_sum, AddMonoidHom.finset_sum_apply, map_mul, amul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf1 i, map_sum]
    rw [h1, h2'] at hC'
    have h3 : ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← amul, ← amul, mul_comm]
    rw [h3, pow_add, mul_comm, amul] at hC'
    exact (hbijN β).1 hC'
  constructor
  · rintro ⟨N, hN, hx⟩
    choose x' hx' using hx
    have hkj : (((j + N).toNat : ℕ) : ℤ) = j + N := Int.toNat_of_nonneg hN
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ (j + N).toNat * x' τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; rw [← map_pow]; exact hx' τ i
    have hK := key N x hxx
    have hmem : Fil (((j + N).toNat : ℕ) : ℤ) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      refine (Fb _ _).2 fun i => ?_
      have h8 : (fun τ => x τ i) = (fun _ => Ehat O K l e) ^ (j + N).toNat * fun τ => x' τ i := by
        funext τ; simp only [x, Pi.mul_apply, Pi.pow_apply]
      rw [h8, map_mul, map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [← hK, hkj] at hmem
    exact (hSh N _ j).2 hmem
  · intro hF
    obtain ⟨N₁, x₁, hx₁⟩ := hE1
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ j.natAbs * x₁ τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N₁ + j.natAbs) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; simp only [x, map_mul, map_pow, hx₁, pow_add]; ring
    have hK := key _ x hxx
    have hN : 0 ≤ j + ((N₁ + j.natAbs : ℕ) : ℤ) := by push_cast; have := neg_abs_le j; omega
    have hkj : (((j + ((N₁ + j.natAbs : ℕ) : ℤ)).toNat : ℕ) : ℤ) = j + ((N₁ + j.natAbs : ℕ) : ℤ) := Int.toNat_of_nonneg hN
    have h1 := (hSh (N₁ + j.natAbs) _ j).1 hF
    rw [hK, ← hkj] at h1
    have h2 := (Fb _ _).1 h1
    refine ⟨N₁ + j.natAbs, hN, fun τ i => ?_⟩
    obtain ⟨z, hz⟩ := PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ _ _ (h2 i)
    refine ⟨z τ, ?_⟩
    have h9 := congrFun hz τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h9
    rw [← h9, map_pow]
    exact hxx τ i

end GlobalTheory.BKGal.JumpDR.CmpFil

open GlobalTheory.BKGal.JumpDR.CmpFil in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.BKGal.JumpDR.inEhat_iff_filV : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (j : ℤ), GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j := by
  intro hFont l _ a e _ _ ϖ LL _ _ h2 ι _ _ P T I jB Pl AI Td hcmp X hX A hA n s m j
  obtain ⟨hbij, hS⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td A hA
  obtain ⟨β, y, hy⟩ := GlobalTheory.T.exists_eisenstein_pow_mul_phiMatrix_inv_ahat l a e ϖ LL ι P
  obtain ⟨f, hf1, hspan, hind⟩ := GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus hFont l a e ϖ LL h2 ι P T I jB Pl AI Td hcmp X hX A hA β y hy
  exact coreG (thetaW a LL) ϖ P A (fun j y => y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j)
    (amulL A hA) (aoneL A hA) hbij hS (fun j => X (jB (Pi.single j 1))) β y hy f hf1 hspan hind s m
    (fun k => X (jB (toBcris (thetaW a LL) ϖ P (m k))))
    (fun s' c h => GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates hFont l a e ϖ LL h2 ι P T jB Pl AI Td X hX A hA n s' m c h)
    (GlobalTheory.T.hsum_mul_eisensteinCompletion_pow_integral l a e ϖ LL ι P n s m) j
