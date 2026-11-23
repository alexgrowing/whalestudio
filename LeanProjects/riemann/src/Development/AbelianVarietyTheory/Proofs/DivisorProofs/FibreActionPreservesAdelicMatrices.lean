import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KronIdentity
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibAdel

open Formalism.HermitianLatticesTheory (localization₂)

section General

variable {K : Type} [Field K] [NumberField K]

theorem valuation_eq_one_of_vAdd (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) (h : vAdd w x = 0) :
    w.valuation K x = 1 := by
  unfold vAdd at h
  have h0 : w.valuation K x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, neg_eq_zero.mp h, WithZero.exp_zero]

theorem kron_mul {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] {R : Type} [CommRing R]
    (M M' : ∀ t, Matrix (J t) (J t) R) : kron M * kron M' = kron fun t => M t * M' t := by
  ext I I''
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun I' _ => ?_
  rw [Finset.prod_mul_distrib]

theorem kron_one {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
    {R : Type} [CommRing R] : (kron fun t => (1 : Matrix (J t) (J t) R)) = 1 := by
  first
  | exact @_root_.GlobalTheory.KroneckerIdentity.kron_identity
  | exact _root_.GlobalTheory.KroneckerIdentity.kron_identity
  | (apply _root_.GlobalTheory.KroneckerIdentity.kron_identity <;> assumption)
  | (intros; apply _root_.GlobalTheory.KroneckerIdentity.kron_identity <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KroneckerIdentity.kron_identity <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KroneckerIdentity.kron_identity ..)

theorem rhoMat_mul {n : ℕ} (la : Fin n → ℕ) (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la g * rhoMat la h = rhoMat la (h * g) := by
  rw [GlobalTheory.DefPt.rhoMat, GlobalTheory.DefPt.rhoMat, GlobalTheory.DefPt.rhoMat, Matrix.transpose_mul, map_mul, LinearMap.toMatrix_mul]

theorem rhoMat_one {n : ℕ} (la : Fin n → ℕ) : rhoMat la (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [GlobalTheory.DefPt.rhoMat, Matrix.transpose_one, map_one, LinearMap.toMatrix_one]

theorem exists_int_scale (w : HeightOneSpectrum (𝓞 K)) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {M : Matrix ι κ K} (hM : IntAt w M) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix ι κ (𝓞 K),
      A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • M := by
  have h1 : ∀ p : ι × κ, ∃ r : 𝓞 K, ∃ d ∈ w.asIdeal.primeCompl,
      M p.1 p.2 * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K r := fun p => by
    obtain ⟨r, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer (M p.1 p.2) (hM p.1 p.2)
    exact ⟨r, d, d.2, h⟩
  choose r d hd h using h1
  refine ⟨∏ p, d p, Submonoid.prod_mem _ fun p _ => hd p,
    Matrix.of fun i j => (∏ p ∈ Finset.univ.erase (i, j), d p) * r (i, j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul, ← h]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), map_mul]
  ring

theorem valuation_repr_le_one (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} {la : Fin n → ℕ} {f : nabla la K}
    (hf : f ∈ localization₂ w.asIdeal (stdLat la K)) (i : Idx la) : w.valuation K ((basis la K).repr f i) ≤ 1 := by
  obtain ⟨s, hs, hf⟩ := hf
  rw [stdLat_eq_span, Submodule.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  have hc' : ∑ i, (algebraMap (𝓞 K) K (c i)) • basis la K i = (algebraMap (𝓞 K) K s) • f := hc
  have h1 := congrArg (fun x => (basis la K).repr x i) hc'
  simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  have h2 : w.valuation K (algebraMap (𝓞 K) K s) = 1 := (w.valuation_eq_one_iff_notMem).2 hs
  have h3 : w.valuation K (algebraMap (𝓞 K) K (c i)) ≤ 1 := w.valuation_le_one (c i)
  rw [h1, map_mul, h2, one_mul] at h3
  exact h3

theorem intAt_rhoMat (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (la : Fin n → ℕ) {g : Matrix (Fin n) (Fin n) K}
    (hg : IntAt w g) : IntAt w (rhoMat la g) := by
  obtain ⟨t, ht, A, hA⟩ := exists_int_scale w (M := gᵀ) (fun i j => hg j i)
  intro i j
  have hj : basis la K j ∈ localization₂ w.asIdeal (stdLat la K) :=
    ⟨1, Submonoid.one_mem _, by rw [one_smul, stdLat_eq_span]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  have h := rho_mem_locP w ht hA hj
  rw [GlobalTheory.DefPt.rhoMat, LinearMap.toMatrix_apply]
  exact valuation_repr_le_one w h i

theorem intAt_smul (w : HeightOneSpectrum (𝓞 K)) {ι κ : Type} [Fintype ι] [DecidableEq ι] {c : K}
    (hc : w.valuation K c ≤ 1) {M : Matrix ι κ K} (hM : IntAt w M) : IntAt w (c • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc (hM i j)

theorem intAt_kron (w : HeightOneSpectrum (𝓞 K)) {T : Type} [Fintype T] [DecidableEq T] {J : T → Type}
    [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] {M : ∀ t, Matrix (J t) (J t) K} (hM : ∀ t, IntAt w (M t)) :
    IntAt w (kron M) := fun I I' => by
  rw [kron, Matrix.of_apply, map_prod]
  exact Finset.prod_le_one' fun t _ => hM t (I t) (I' t)

end General

theorem fibA_isAdelic : ∀ (K : Type) [Field K] [NumberField K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ)
    (la : ∀ t, Fin (N t) → ℕ) (a : HeightOneSpectrum (𝓞 K) → K)
    (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K), (∀ w, a w ≠ 0) →
    (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) →
    IsAdelic fun w => fibA la (a w) (B w) := by
  intro K _ _ T _ _ N la a B ha hfin hB
  have hinv : ∀ w, (a w)⁻¹ • kron (fun t => rhoMat (la t) (B w t)⁻¹) * fibA la (a w) (B w) = 1 := by
    intro w
    have e : ∀ t, rhoMat (la t) (B w t)⁻¹ * rhoMat (la t) (B w t) = 1 := fun t => by
      rw [rhoMat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ((hB t).1 w)), rhoMat_one]
    rw [fibA, Matrix.smul_mul, Matrix.mul_smul, kron_mul, smul_smul, inv_mul_cancel₀ (ha w), one_smul]
    simp only [e]
    exact kron_one
  have hinv' : ∀ w, (fibA la (a w) (B w))⁻¹ = (a w)⁻¹ • kron (fun t => rhoMat (la t) (B w t)⁻¹) :=
    fun w => Matrix.inv_eq_left_inv (hinv w)
  refine ⟨fun w h => ?_, ?_⟩
  · have h1 := congrArg Matrix.det (hinv w)
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  · refine (hfin.union (Set.finite_iUnion fun t => (hB t).2)).subset fun w hw => ?_
    by_contra hw'
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, Function.mem_support, not_or, not_exists,
      not_not] at hw'
    obtain ⟨h0, h1⟩ := hw'
    have hv : w.valuation K (a w) = 1 := valuation_eq_one_of_vAdd w (ha w) h0
    refine hw ⟨intAt_smul w hv.le (intAt_kron w fun t => intAt_rhoMat w _ (h1 t).1), ?_⟩
    rw [hinv' w]
    exact intAt_smul w (by rw [map_inv₀, hv, inv_one]) (intAt_kron w fun t => intAt_rhoMat w _ (h1 t).2)

end GlobalTheory.FibAdel

end
