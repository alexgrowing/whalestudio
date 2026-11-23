import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open Polynomial
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.CyclicCocycle

theorem infinite_of_localField (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Infinite K := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation K)
  by_contra h
  rw [not_infinite_iff_finite] at h
  have hr : r ≠ 0 := fun h0 => hr0 (by simp [h0])
  obtain ⟨m, hm, hmm⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (Units.mk0 r hr))
  have h1 : r ^ m = 1 := by simpa using congrArg Units.val hmm
  have h2 : (ValuativeRel.valuation K r) ^ m = 1 := by rw [← map_pow, h1, map_one]
  exact absurd h2 (pow_lt_one₀ zero_le' hr1 hm.ne').ne

theorem exists_det_ne_zero {k E : Type*} [Field k] [Field E] [Algebra k E] [Infinite k]
    {m n : ℕ} (y : Fin m → Matrix (Fin n) (Fin n) E) (a : Fin m → E)
    (h : (∑ j, a j • y j).det ≠ 0) :
    ∃ t : Fin m → k, (∑ j, algebraMap k E (t j) • y j).det ≠ 0 := by
  classical
  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) E) :=
    ∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) E) • (y j).map MvPolynomial.C
  have hev : ∀ v : Fin m → E, MvPolynomial.eval v A.det = (∑ j, v j • y j).det := by
    intro v
    rw [RingHom.map_det]
    congr 1
    ext p q
    simp [A, Matrix.sum_apply]
  by_contra hcon
  push Not at hcon
  have hzero : A.det = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap k E)) (fun _ => ?_)
      (fun v hv => ?_)
    · exact Set.infinite_range_of_injective (algebraMap k E).injective
    · have hv' : ∀ i, ∃ t : k, algebraMap k E t = v i := fun i => hv i (Set.mem_univ i)
      choose t ht using hv'
      rw [hev, map_zero]
      have := hcon t
      simpa [ht] using this
  exact h (by rw [← hev, hzero, map_zero])

theorem exists_dual {k E : Type*} [Field k] [Field E] [Algebra k E] {ℓ : ℕ} (σ : E ≃ₐ[k] E)
    (hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Set.Iio ℓ)) (b : Module.Basis (Fin ℓ) k E) :
    ∃ a : Fin ℓ → E, ∀ i : Fin ℓ,
      ∑ j, a j * (σ ^ (i : ℕ)) (b j) = if (i : ℕ) = 0 then 1 else 0 := by
  classical
  let M : Matrix (Fin ℓ) (Fin ℓ) E := Matrix.of fun i j => (σ ^ (i : ℕ)) (b j)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    have hvj : ∀ j, ∑ i, v i * (σ ^ (i : ℕ)) (b j) = 0 := by
      intro j
      have := congrFun hv j
      simpa [Matrix.vecMul, dotProduct, M] using this
    have hall : ∀ z : E, ∑ i, v i * (σ ^ (i : ℕ)) z = 0 := by
      intro z
      rw [← b.sum_repr z]
      simp only [map_sum, map_smul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrArg (fun w => b.repr z j • w) (hvj j)
      simp only [smul_zero, Finset.smul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm]
    let f : Fin ℓ → (E →* E) := fun i => ((σ ^ (i : ℕ) : E ≃ₐ[k] E) : E →* E)
    have hf : Function.Injective f := by
      intro i j hij
      have h1 : (σ ^ (i : ℕ) : E ≃ₐ[k] E) = σ ^ (j : ℕ) := by
        ext z
        exact DFunLike.congr_fun hij z
      exact Fin.ext (hinj i.2 j.2 h1)
    have li := (linearIndependent_monoidHom E E).comp f hf
    have hz := Fintype.linearIndependent_iff.mp li v (by
      funext z
      simpa [f] using hall z)
    exact hv0 (funext hz)
  let e : Fin ℓ → E := fun i => if (i : ℕ) = 0 then 1 else 0
  refine ⟨M⁻¹.mulVec e, fun i => ?_⟩
  have h1 : M.mulVec (M⁻¹.mulVec e) = e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have h2 := congrFun h1 i
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply] at h2
  simp only [e] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem inv_mem_range {E : Type*} [Field E] {n : ℕ} (Γ X : Matrix (Fin n) (Fin n) E)
    (hX : ∃ p : E[X], X = aeval Γ p) (hd : X.det ≠ 0) : ∃ q : E[X], X⁻¹ = aeval Γ q := by
  obtain ⟨p, hp⟩ := hX
  have hc : X.charpoly.coeff 0 ≠ 0 := by
    intro h0
    apply hd
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  set c := X.charpoly.coeff 0 with hcdef
  have h1 : aeval X (divX X.charpoly) * X + algebraMap E _ c = 0 := by
    have h := Matrix.aeval_self_charpoly X
    rw [← divX_mul_X_add X.charpoly] at h
    simpa [map_add, map_mul, aeval_X, aeval_C, ← hcdef] using h
  have h2 : (-(c⁻¹) • aeval X (divX X.charpoly)) * X = 1 := by
    rw [Matrix.smul_mul, eq_neg_of_add_eq_zero_left h1, smul_neg, neg_smul, neg_neg,
      Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨C (-(c⁻¹)) * (divX X.charpoly).comp p, ?_⟩
  rw [Matrix.inv_eq_left_inv h2, map_mul, aeval_C, aeval_comp, ← hp,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

variable {k E : Type*} [Field k] [Field E] [Algebra k E] {n : ℕ}

theorem map_aeval_incl (σ : E ≃ₐ[k] E) (γ : GL (Fin n) k) (p : E[X]) :
    (aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p).map σ =
      aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
        (p.map (σ.toAlgHom.toRingHom)) := by
  set Γ := ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hΓ
  have hfix : (σ.toAlgHom.toRingHom).mapMatrix Γ = Γ := by
    ext i j
    have : Γ i j = algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j) := rfl
    simp [this]
  have h1 : (aeval Γ p).map σ = (σ.toAlgHom.toRingHom).mapMatrix (aeval Γ p) := rfl
  rw [h1, aeval_def, aeval_def, hom_eval₂, hfix, eval₂_map]
  congr 1
  ext a i j
  by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]

def cMat (σ : E ≃ₐ[k] E) (u : GL (Fin n) E) (i : ℕ) : Matrix (Fin n) (Fin n) E :=
  ((twNorm (sigmaGL σ) i u : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)

def res (σ : E ≃ₐ[k] E) (ℓ : ℕ) (u : GL (Fin n) E) (s : E) : Matrix (Fin n) (Fin n) E :=
  ∑ i ∈ Finset.range ℓ, ((σ ^ i) s) • cMat σ u i

theorem cMat_succ (σ : E ≃ₐ[k] E) (u : GL (Fin n) E) (i : ℕ) :
    (u : Matrix (Fin n) (Fin n) E) * (cMat σ u i).map σ = cMat σ u (i + 1) := by
  have h : u * sigmaGL σ (twNorm (sigmaGL σ) i u) = twNorm (sigmaGL σ) (i + 1) u := by
    rw [map_twNorm, twNorm_succ]
    group
  exact congrArg Units.val h

theorem mul_map_res (σ : E ≃ₐ[k] E) {ℓ : ℕ} (hℓ : σ ^ ℓ = 1) (u : GL (Fin n) E)
    (hN : twNorm (sigmaGL σ) ℓ u = 1) (s : E) :
    (u : Matrix (Fin n) (Fin n) E) * (res σ ℓ u s).map σ = res σ ℓ u s := by
  set f : ℕ → Matrix (Fin n) (Fin n) E := fun i => ((σ ^ i) s) • cMat σ u i with hf
  have h1 : (res σ ℓ u s).map σ = ∑ i ∈ Finset.range ℓ, ((σ ^ (i + 1)) s) • (cMat σ u i).map σ := by
    ext p q
    simp [res, Matrix.sum_apply, pow_succ']
  have h2 : (u : Matrix (Fin n) (Fin n) E) * (res σ ℓ u s).map σ =
      ∑ i ∈ Finset.range ℓ, f (i + 1) := by
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, cMat_succ]
  have h3 : f ℓ = f 0 := by
    have hs : (σ ^ ℓ) s = s := by rw [hℓ]; rfl
    change ((σ ^ ℓ) s) • cMat σ u ℓ = ((σ ^ 0) s) • cMat σ u 0
    rw [hs]
    simp [cMat, hN]
  have h4 := Finset.sum_range_succ f ℓ
  rw [Finset.sum_range_succ' f ℓ, h3] at h4
  rw [h2]
  exact add_right_cancel h4

theorem exists_res_det_ne_zero [FiniteDimensional k E] [IsGalois k E] [Infinite k]
    (σ : E ≃ₐ[k] E) (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (u : GL (Fin n) E) :
    ∃ s : E, (res σ (Module.finrank k E) u s).det ≠ 0 := by
  classical
  have hord : orderOf σ = Module.finrank k E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Set.Iio (Module.finrank k E)) := by
    rw [← hord]
    exact pow_injOn_Iio_orderOf
  have hpos : 0 < Module.finrank k E := Module.finrank_pos
  let b := Module.finBasis k E
  obtain ⟨a, ha⟩ := exists_dual σ hinj b
  let y : Fin (Module.finrank k E) → Matrix (Fin n) (Fin n) E :=
    fun j => res σ (Module.finrank k E) u (b j)
  have hone : ∑ j, a j • y j = 1 := by
    have h1 : ∀ j, a j • y j = ∑ i : Fin (Module.finrank k E),
        (a j * (σ ^ (i : ℕ)) (b j)) • cMat σ u i := by
      intro j
      simp only [y, res]
      rw [Finset.sum_range, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
    simp only [h1]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ha]
    rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin (Module.finrank k E))]
    · simp [cMat]
    · intro i _ hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]
    · simp
  obtain ⟨t, ht⟩ := exists_det_ne_zero (k := k) y a (by rw [hone]; simp)
  refine ⟨∑ j, t j • b j, ?_⟩
  have : res σ (Module.finrank k E) u (∑ j, t j • b j) = ∑ j, algebraMap k E (t j) • y j := by
    simp only [y, res, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_smul, Algebra.smul_def (t j)]
  rwa [this]

theorem cocycle [FiniteDimensional k E] [IsGalois k E] [Infinite k]
    (σ : E ≃ₐ[k] E) (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin n) k) (u : GL (Fin n) E)
    (hu : ∃ p : E[X], (u : Matrix (Fin n) (Fin n) E) =
      aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p)
    (hN : normGL σ u = 1) :
    ∃ x : GL (Fin n) E,
      (∃ q : E[X], (x : Matrix (Fin n) (Fin n) E) =
        aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) q) ∧
      u = x⁻¹ * sigmaGL σ x := by
  classical
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  set Γ := ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hΓ
  let S := (aeval Γ : E[X] →ₐ[E] Matrix (Fin n) (Fin n) E).range
  have hmemS : ∀ {M : Matrix (Fin n) (Fin n) E}, M ∈ S ↔ ∃ p : E[X], M = aeval Γ p := by
    intro M
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, rfl⟩
  have hmap : ∀ {M : Matrix (Fin n) (Fin n) E}, M ∈ S → M.map σ ∈ S := by
    intro M hM
    obtain ⟨p, rfl⟩ := hmemS.mp hM
    exact hmemS.mpr ⟨_, map_aeval_incl σ γ p⟩
  have hc : ∀ i, cMat σ u i ∈ S := by
    intro i
    induction i with
    | zero =>
      have : cMat σ u 0 = 1 := by simp [cMat]
      rw [this]
      exact S.one_mem
    | succ i ih =>
      rw [← cMat_succ]
      exact S.mul_mem (hmemS.mpr hu) (hmap ih)
  obtain ⟨s, hs⟩ := exists_res_det_ne_zero σ hgen u
  set X := res σ (Module.finrank k E) u s with hX
  have hXS : X ∈ S := S.sum_mem fun i _ => S.smul_mem (hc i) _
  let Xu : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero X hs
  have hXu : (Xu : Matrix (Fin n) (Fin n) E) = X := rfl
  have hfun : u * sigmaGL σ Xu = Xu := Units.ext (mul_map_res σ hℓ u hN s)
  refine ⟨Xu⁻¹, ?_, ?_⟩
  · rw [Matrix.coe_units_inv, hXu]
    exact inv_mem_range Γ X (hmemS.mp hXS) hs
  · rw [inv_inv, map_inv]
    exact eq_mul_inv_of_mul_eq hfun

theorem cyclicCocycleLemma : PositivityTheory.Rg.Tf.Loc.A2 → PositivityTheory.Rg.Tf.Loc.A3 := by
  intro _ k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n γ _ u hu hN
  haveI := infinite_of_localField k
  exact cocycle σ hgen γ u hu hN

end GlobalTheory.CompanionTheory.CyclicCocycle
