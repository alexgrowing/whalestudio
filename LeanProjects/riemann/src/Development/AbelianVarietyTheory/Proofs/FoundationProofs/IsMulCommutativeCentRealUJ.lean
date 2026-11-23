import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ

open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.AdelicU NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.ClassParam (krylov exists_cyclic)
open Formalism.UG (cT IsHerm cT_mul cT_one)
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.Orb

section Cyclic

variable {A : Type} [CommRing A] {r : ℕ}

def companionMat (r : ℕ) (P : A[X]) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun i j => (X ^ ((j : ℕ) + 1) %ₘ P).coeff i

theorem mul_krylov_eq (h : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    h * krylov h v = krylov h v * companionMat r h.charpoly := by
  nontriviality A
  ext i j
  have hr : 0 < r := j.pos
  have hd : (X ^ ((j : ℕ) + 1) %ₘ h.charpoly).natDegree < r := by
    have := natDegree_modByMonic_lt (X ^ ((j : ℕ) + 1)) h.charpoly_monic (fun e => by
      have := h.charpoly_natDegree_eq_dim
      rw [e, natDegree_one, Fintype.card_fin] at this
      omega)
    rwa [h.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  have e1 : (h * krylov h v) i j = ((h ^ ((j : ℕ) + 1)) *ᵥ v) i := by
    rw [pow_succ', ← mulVec_mulVec]; rfl
  rw [e1, Matrix.pow_eq_aeval_mod_charpoly, aeval_eq_sum_range' hd, Finset.sum_range, Matrix.sum_mulVec,
    Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [krylov, companionMat, Matrix.smul_mulVec, mul_comm]

theorem mul_krylov_of_commute {M N : Matrix (Fin r) (Fin r) A} (h : Commute N M) (v : Fin r → A) :
    N * krylov M v = krylov M (N *ᵥ v) := by
  ext i j
  have : (N * krylov M v) i j = (N *ᵥ ((M ^ (j : ℕ)) *ᵥ v)) i := rfl
  rw [this, mulVec_mulVec, (h.pow_right j).eq, ← mulVec_mulVec]; rfl

theorem exists_aeval_of_commute_fin [IsArtinianRing A] {M N : Matrix (Fin r) (Fin r) A} (hM : IsRegSS M)
    (h : Commute N M) : ∃ p : A[X], N = aeval M p := by
  obtain ⟨v, hv⟩ := exists_cyclic M hM
  let c := (krylov M v)⁻¹ *ᵥ (N *ᵥ v)
  let p : A[X] := ∑ j : Fin r, monomial (j : ℕ) (c j)
  have hp : aeval M p *ᵥ v = N *ᵥ v := by
    have : krylov M v *ᵥ c = N *ᵥ v := by rw [mulVec_mulVec, mul_nonsing_inv _ hv, one_mulVec]
    rw [← this]
    ext i
    simp [p, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hc : Commute (aeval M p) M := by
    have := congrArg (aeval M) (mul_comm p X)
    rwa [map_mul, map_mul, aeval_X] at this
  refine ⟨p, ((isUnit_iff_isUnit_det _).2 hv).mul_right_cancel ?_⟩
  rw [mul_krylov_of_commute h, mul_krylov_of_commute hc, hp]

theorem continuous_krylov [TopologicalSpace A] [IsTopologicalRing A] (v : Fin r → A) :
    Continuous fun h : Matrix (Fin r) (Fin r) A => krylov h v :=
  continuous_matrix fun i j => (continuous_apply i).comp ((continuous_pow (j : ℕ)).matrix_mulVec continuous_const)

variable {n : Type} [Fintype n] [DecidableEq n]

theorem IsRegSS.reindex {m : Type} [Fintype m] [DecidableEq m] {M : Matrix n n A} (hM : IsRegSS M) (e : n ≃ m) :
    IsRegSS (reindexAlgEquiv A A e M) := by
  rwa [IsRegSS, reindexAlgEquiv_apply, charpoly_reindex]

theorem IsRegSS.map {B : Type} [CommRing B] {M : Matrix n n A} (hM : IsRegSS M) (f : A →+* B) :
    IsRegSS (M.map f) := by
  rw [IsRegSS, charpoly_map]; exact Separable.map hM

theorem IsRegSS.exists_aeval [IsArtinianRing A] {M N : Matrix n n A} (hM : IsRegSS M) (h : N * M = M * N) :
    ∃ p : A[X], N = aeval M p := by
  let φ := reindexAlgEquiv A A (Fintype.equivFin n)
  obtain ⟨p, hp⟩ := exists_aeval_of_commute_fin (N := φ N) (hM.reindex _) (Commute.map h φ)
  exact ⟨p, φ.injective (hp.trans (aeval_algHom_apply φ M p))⟩

theorem IsRegSS.commute [IsArtinianRing A] {M N N' : Matrix n n A} (hM : IsRegSS M) (h : N * M = M * N)
    (h' : N' * M = M * N') : N * N' = N' * N := by
  obtain ⟨p, rfl⟩ := hM.exists_aeval h
  obtain ⟨q, rfl⟩ := hM.exists_aeval h'
  rw [← map_mul, ← map_mul, mul_comm]

theorem IsRegSS.exists_conj [IsArtinianRing A] {M N : Matrix n n A} (hM : IsRegSS M) (h : N.charpoly = M.charpoly) :
    ∃ x : GL n A, N * x = x * M := by
  let φ := reindexAlgEquiv A A (Fintype.equivFin n)
  have hN : IsRegSS N := by rwa [IsRegSS, h]
  obtain ⟨v, hv⟩ := exists_cyclic _ (hM.reindex (Fintype.equivFin n))
  obtain ⟨w, hw⟩ := exists_cyclic _ (hN.reindex (Fintype.equivFin n))
  have e : (φ N).charpoly = (φ M).charpoly := by simp only [φ, reindexAlgEquiv_apply, charpoly_reindex, h]
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have h1 := mul_krylov_eq (φ M) v
  have h2 := mul_krylov_eq (φ N) w
  rw [← ha] at h1
  rw [← hb, e] at h2
  obtain ⟨x, e2⟩ : ∃ x : GL n A, φ x = b * a⁻¹ :=
    ⟨Units.map φ.symm.toMonoidHom (b * a⁻¹), φ.apply_symm_apply _⟩
  refine ⟨x, φ.injective ?_⟩
  rw [map_mul, map_mul, e2, ← mul_assoc, h2, Units.mul_inv_eq_iff_eq_mul, mul_assoc, mul_assoc, h1,
    Units.inv_mul_cancel_left]

theorem IsRegSS.exists_intertwiner [IsArtinianRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {M : Matrix n n A} (hM : IsRegSS M) : ∃ Y : Matrix n n A → Matrix n n A, Continuous Y ∧ Y M = 1 ∧
      ∀ N, N.charpoly = M.charpoly → N * Y N = Y N * M := by
  let φ := reindexAlgEquiv A A (Fintype.equivFin n)
  obtain ⟨v, hv⟩ := exists_cyclic _ (hM.reindex (Fintype.equivFin n))
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  refine ⟨fun N => φ.symm (krylov (φ N) v * a⁻¹), ?_, ?_, fun N h => φ.injective ?_⟩
  · have h1 : Continuous φ := continuous_id.matrix_reindex _ _
    have h2 : Continuous φ.symm :=
      continuous_id.matrix_reindex (Fintype.equivFin n).symm (Fintype.equivFin n).symm
    exact h2.comp (((continuous_krylov v).comp h1).mul continuous_const)
  · simp only [φ, ← ha, Units.mul_inv, map_one]
  · have e : (φ N).charpoly = (φ M).charpoly := by simp only [φ, reindexAlgEquiv_apply, charpoly_reindex, h]
    have h1 := mul_krylov_eq (φ M) v
    have h2 := mul_krylov_eq (φ N) v
    rw [← ha] at h1
    rw [e] at h2
    rw [map_mul, map_mul, φ.apply_symm_apply, ← mul_assoc, h2, Units.mul_inv_eq_iff_eq_mul, mul_assoc, mul_assoc, h1,
      Units.inv_mul_cancel_left]

theorem isClosed_charpoly_eq [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] (P : A[X]) :
    IsClosed {N : Matrix n n A | N.charpoly = P} := by
  simp only [Polynomial.ext_iff, setOf_forall]
  refine isClosed_iInter fun i => isClosed_eq ?_ continuous_const
  have : (fun N : Matrix n n A => N.charpoly.coeff i) =
      fun N => MvPolynomial.eval (fun p : n × n => N p.1 p.2) ((Matrix.charpoly.univ A n).coeff i) :=
    funext fun N => (Matrix.charpoly.univ_coeff_eval₂Hom n (RingHom.id A) (fun p : n × n => N p.1 p.2) i).symm
  rw [this]
  exact (MvPolynomial.continuous_eval _).comp (by fun_prop)

end Cyclic

section Sqrt

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k]

theorem eventually_exists_sq_normed {V : Type} [NormedAddCommGroup V] [NormedSpace k V] [FiniteDimensional k V]
    (h2 : (2 : k) ≠ 0) (B : V →ₗ[k] V →ₗ[k] V) {e : V} (hl : ∀ v, B e v = v) (hr : ∀ v, B v e = v) :
    ∀ᶠ l in 𝓝 e, ∃ z, B z z = l := by
  have := FiniteDimensional.complete k V
  let B' : V →L[k] V →L[k] V :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (V →ₗ[k] V) ≃ₗ[k] _).toLinearMap ∘ₗ B)
  let D : V ≃L[k] V := (LinearEquiv.smulOfNeZero k V 2 h2).toContinuousLinearEquiv
  have hd : HasStrictFDerivAt (fun z => B' z z) (D : V →L[k] V) e := by
    refine (B'.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id e) (hasStrictFDerivAt_id e)).congr_fderiv ?_
    ext v
    simp [B', D, hl, hr, two_smul]
  have h := hd.map_nhds_eq_of_equiv
  rw [show B' e e = e from hl e] at h
  rw [← h]
  exact range_mem_map

theorem eventually_exists_sq {V : Type} [AddCommGroup V] [Module k V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul k V] [T2Space V] [FiniteDimensional k V]
    (h2 : (2 : k) ≠ 0) (B : V →ₗ[k] V →ₗ[k] V) {e : V} (hl : ∀ v, B e v = v) (hr : ∀ v, B v e = v) :
    ∀ᶠ l in 𝓝 e, ∃ z, B z z = l := by
  let φ : V ≃L[k] (Fin (Module.finrank k V) → k) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have := eventually_exists_sq_normed h2 ((B.compl₁₂ φ.symm.toLinearMap φ.symm.toLinearMap).compr₂ φ.toLinearMap)
    (e := φ e) (fun v => by simp [hl]) (fun v => by simp [hr])
  filter_upwards [φ.continuous.continuousAt.eventually this] with l ⟨z, hz⟩
  exact ⟨φ.symm z, φ.injective hz⟩

variable (k) {R : Type} [Ring R] [Algebra k R] [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul k R] [T2Space R]
  [FiniteDimensional k R]

include k in

theorem eventually_isUnit : ∀ᶠ x in 𝓝 (1 : R), IsUnit x := by
  let b := Module.finBasis k R
  have hc : Continuous fun x : R => (Algebra.leftMulMatrix b x).det :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional.matrix_det
  filter_upwards [hc.continuousAt.eventually_ne (y := 0) (by simp)] with x hx
  rw [← Algebra.lmul_isUnit_iff (R := k), LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix b]
  exact hx.isUnit

variable {k} in

theorem eventually_exists_unitary (h2 : (2 : k) ≠ 0) (s : R →ₗ[k] R) (hm : ∀ a b, s (a * b) = s b * s a)
    (hs : ∀ a, s (s a) = a) {g : R} (hg : g * s g = 1) :
    ∀ᶠ y in 𝓝 (1 : R), ∀ h, s h * h = 1 → h * y = y * g → ∃ u : Rˣ, s u * u = 1 ∧ h * u = u * g := by
  have h1 : s 1 = 1 := by simpa [hs] using (hm (s 1) 1).symm
  let V : Submodule k R :=
    { carrier := {l | s l = l ∧ l * g = g * l}
      add_mem' := fun ha hb => ⟨by rw [map_add, ha.1, hb.1], by rw [add_mul, mul_add, ha.2, hb.2]⟩
      zero_mem' := ⟨map_zero _, by simp⟩
      smul_mem' := fun c _ ha => ⟨by rw [map_smul, ha.1], by rw [smul_mul_assoc, mul_smul_comm, ha.2]⟩ }
  let f : V → V → V := fun a b => (2 : k)⁻¹ • ⟨a.1 * b.1 + b.1 * a.1, by rw [map_add, hm, hm, a.2.1, b.2.1, add_comm],
      (Commute.add_left (Commute.mul_left a.2.2 b.2.2) (Commute.mul_left b.2.2 a.2.2)).eq⟩
  let B : V →ₗ[k] V →ₗ[k] V := LinearMap.mk₂ k f
    (fun a b c => Subtype.ext (by simp [f, add_mul, mul_add]; abel))
    (fun a b c => Subtype.ext (by simp [f, smul_comm a]))
    (fun a b c => Subtype.ext (by simp [f, add_mul, mul_add]; abel))
    (fun a b c => Subtype.ext (by simp [f, smul_comm a]))
  have hB : ∀ a b : V, (B a b).1 = (2 : k)⁻¹ • (a.1 * b.1 + b.1 * a.1) := fun _ _ => rfl
  have half : ∀ a : R, (2 : k)⁻¹ • (a + a) = a := fun a => by rw [← two_smul k a, inv_smul_smul₀ h2]
  have := eventually_exists_sq h2 B (e := ⟨1, h1, by simp⟩) (fun v => Subtype.ext (by simp only [hB, one_mul, mul_one, half]))
    (fun v => Subtype.ext (by simp only [hB, one_mul, mul_one, half]))
  rw [nhds_subtype, eventually_comap] at this
  have hc : Tendsto (fun y => s y * y) (𝓝 1) (𝓝 (1 : R)) :=
    (s.continuous_of_finiteDimensional.mul continuous_id).tendsto' _ _ (by simp [h1])
  filter_upwards [hc.eventually this, hc.eventually (eventually_isUnit k), eventually_isUnit k]
    with y hy hl ⟨y', hy'⟩ h hh e
  have e' : s g * (s y * y) * g = s y * y := by
    rw [← mul_assoc, ← hm, mul_assoc, ← e, hm, mul_assoc, ← mul_assoc (s h), hh, one_mul]
  obtain ⟨z, hz⟩ := hy ⟨s y * y, by rw [hm, hs], by
    conv_rhs => rw [← e', ← mul_assoc, ← mul_assoc, hg, one_mul]⟩ rfl
  have hz' : z.1 * z.1 = s y * y := by simpa only [hB, half] using congrArg Subtype.val hz
  obtain ⟨z', hz''⟩ : IsUnit z.1 := isUnit_mul_self_iff.1 (hz' ▸ hl)
  have hsz : s (z'⁻¹ : Rˣ) = (z'⁻¹ : Rˣ) := by
    refine Units.eq_inv_of_mul_eq_one_right ?_
    rw [hz'', ← z.2.1, ← hm, ← hz'', Units.mul_inv, h1]
  refine ⟨y' * z'⁻¹, ?_, ?_⟩
  · rw [Units.val_mul, hm, hsz, hy', mul_assoc, ← mul_assoc (s y), ← hz', ← hz'', Units.mul_inv_cancel_right,
      Units.inv_mul]
  · have : Commute (z'⁻¹ : Rˣ).1 g := Commute.units_inv_left (hz''.symm ▸ z.2.2)
    rw [Units.val_mul, hy', ← mul_assoc, e, mul_assoc, mul_assoc, this.eq]

end Sqrt

section Cent

variable {A n H : Type} [CommRing A] [IsArtinianRing A] [Fintype n] [DecidableEq n] [Group H]

theorem isMulCommutative_cent {ι : H →* Matrix n n A} (hι : Function.Injective ι) {s : H} (hs : IsRegSS (ι s)) :
    IsMulCommutative (cent s) :=
  ⟨⟨fun a b => Subtype.ext (hι (by
    have ha := congrArg ι (mem_cent.1 a.2)
    have hb := congrArg ι (mem_cent.1 b.2)
    rw [map_mul, map_mul] at ha hb
    simpa only [Subgroup.coe_mul, map_mul] using hs.commute ha hb))⟩⟩

theorem isMulRightInvariant_cent [MeasurableSpace H] {s : H} (h : IsMulCommutative (cent s)) (dt : Measure (cent s))
    [dt.IsMulLeftInvariant] : dt.IsMulRightInvariant :=
  ⟨fun g => by
    rw [show (fun x => x * g) = fun x => g * x from funext fun x => h.1.1 x g]
    exact map_mul_left_eq_self dt g⟩

theorem isMulCommutative_cent_GL {g : GL n A} (hg : IsRegSS g.1) : IsMulCommutative (cent g) :=
  isMulCommutative_cent (ι := Units.coeHom (Matrix n n A)) (s := g) Units.val_injective hg

theorem isMulCommutative_cent_HA {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {k : Type} [Field k] [Algebra F k] {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {g : HA k σ J}
    (hg : IsRegSS (matHom k σ J g).1) : IsMulCommutative (cent g) :=
  haveI : IsArtinianRing (k ⊗[F] E) := IsArtinianRing.of_finite k _
  isMulCommutative_cent (ι := (Units.coeHom _).comp (matHom k σ J))
    (Units.val_injective.comp (matHom_injective k σ J)) hg

end Cent

section Classes

variable {A n : Type} [CommRing A] [IsArtinianRing A] [Fintype n] [DecidableEq n]

omit [IsArtinianRing A] in

theorem charpoly_conj_GL (g x : GL n A) : (x⁻¹ * g * x).1.charpoly = g.1.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]

theorem range_conj_GL {g : GL n A} (hg : IsRegSS g.1) :
    (range fun x : GL n A => x⁻¹ * g * x) = {h | h.1.charpoly = g.1.charpoly} := by
  refine Set.ext fun h => ⟨fun ⟨x, hx⟩ => hx ▸ charpoly_conj_GL g x, fun hh => ?_⟩
  obtain ⟨x, hx⟩ := hg.exists_conj hh
  refine ⟨x⁻¹, ?_⟩
  simp only [inv_inv, mul_inv_eq_iff_eq_mul]
  exact Units.ext hx.symm

variable [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]

theorem isClosed_class_GL {g : GL n A} (hg : IsRegSS g.1) : IsClosed (range fun x : GL n A => x⁻¹ * g * x) :=
  range_conj_GL hg ▸ (isClosed_charpoly_eq _).preimage Units.continuous_val

theorem isProperOrbit_GL [LocallyCompactSpace A] [SecondCountableTopology A] {g : GL n A} (hg : IsRegSS g.1) :
    IsProperOrbit (cent g) g := by
  have : LocallyCompactSpace (Matrix n n A) := inferInstanceAs (LocallyCompactSpace (n → n → A))
  have : SecondCountableTopology (Matrix n n A) := inferInstanceAs (SecondCountableTopology (n → n → A))
  have : LocallyCompactSpace (Matrix n n A)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (Matrix n n A)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace (GL n A) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (GL n A) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact isProperOrbit_of_isClosed (isClosed_class_GL hg)

end Classes

section Unitary

variable (k : Type) [NontriviallyNormedField k] [CompleteSpace k] {A n : Type} [CommRing A] [Algebra k A]
  [FiniteDimensional k A] [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul k A] [T2Space A]
  [Fintype n] [DecidableEq n] {σ : A →+* A} {J : Matrix n n A}

theorem eventually_isConj_UJ (h2 : (2 : k) ≠ 0) (hk : ∀ (c : k) a, σ (c • a) = c • σ a) (hσ : ∀ a, σ (σ a) = a)
    (hJ : IsHerm σ J) (hd : IsUnit J.det) {g : Formalism.UG.UJ σ J} (hg : IsRegSS g.1.1) :
    ∀ᶠ h : Formalism.UG.UJ σ J in 𝓝 g, h.1.1.charpoly = g.1.1.charpoly → IsConj g h := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k _
  let s : Matrix n n A →ₗ[k] Matrix n n A :=
    { toFun := fun a => J⁻¹ * cT σ a * J
      map_add' := fun a b => by
        rw [show cT σ (a + b) = cT σ a + cT σ b from Matrix.ext fun i j => map_add σ _ _, mul_add, add_mul]
      map_smul' := fun c a => by
        rw [show cT σ (c • a) = c • cT σ a from Matrix.ext fun i j => hk _ _, mul_smul_comm, smul_mul_assoc]; rfl }
  have hs : ∀ a, J * s a = cT σ a * J := fun a => by
    change J * (J⁻¹ * cT σ a * J) = _
    rw [mul_assoc, mul_nonsing_inv_cancel_left _ _ hd]
  have hu := (isUnit_iff_isUnit_det _).2 hd
  have hm : ∀ a b, s (a * b) = s b * s a := fun a b => hu.mul_left_cancel (by
    rw [hs, ← mul_assoc, hs, mul_assoc, hs, cT_mul, mul_assoc])
  have hcc : ∀ a : Matrix n n A, cT σ (cT σ a) = a := fun a => Matrix.ext fun i j => hσ _
  have hss : ∀ a, s (s a) = a := fun a => hu.mul_left_cancel (by
    have := congrArg (cT σ) (hs a)
    rwa [cT_mul, cT_mul, hcc, show cT σ J = J from hJ, ← hs] at this)
  have hU : ∀ u : GL n A, u ∈ Formalism.UG.UJ σ J ↔ s u * u = 1 := fun u => by
    change cT σ u.1 * J * u.1 = J ↔ _
    rw [← hs, mul_assoc, ← hu.mul_right_inj (b := s u * u), mul_one]
  obtain ⟨Y, hY, h1, hi⟩ := hg.exists_intertwiner
  have hc : Tendsto (fun h : Formalism.UG.UJ σ J => Y h.1.1) (𝓝 g) (𝓝 1) :=
    (hY.comp (Units.continuous_val.comp continuous_subtype_val)).tendsto' _ _ h1
  filter_upwards [hc.eventually (eventually_exists_unitary h2 s hm hss (mul_eq_one_comm.1 ((hU _).1 g.2)))]
    with h hh e
  obtain ⟨u, hu1, hu2⟩ := hh _ ((hU _).1 h.2) (hi _ e)
  exact isConj_iff.2 ⟨⟨u, (hU u).2 hu1⟩, mul_inv_eq_iff_eq_mul.2 (Subtype.ext (Units.ext hu2.symm))⟩

theorem isClosed_class_UJ (h2 : (2 : k) ≠ 0) (hk : ∀ (c : k) a, σ (c • a) = c • σ a) (hσ : ∀ a, σ (σ a) = a)
    (hJ : IsHerm σ J) (hd : IsUnit J.det) {g : Formalism.UG.UJ σ J} (hg : IsRegSS g.1.1) :
    IsClosed (range fun x : Formalism.UG.UJ σ J => x⁻¹ * g * x) := by
  refine isClosed_of_closure_subset fun g' hg' => ?_
  have hsub : (range fun x : Formalism.UG.UJ σ J => x⁻¹ * g * x) ⊆ {h | h.1.1.charpoly = g.1.1.charpoly} :=
    fun h ⟨x, hx⟩ => hx ▸ charpoly_conj_GL g.1 x.1
  have e : g'.1.1.charpoly = g.1.1.charpoly := closure_minimal hsub
    ((isClosed_charpoly_eq _).preimage (Units.continuous_val.comp continuous_subtype_val)) hg'
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := ((mem_closure_iff_frequently.1 hg').and_eventually
    (eventually_isConj_UJ k h2 hk hσ hJ hd (g := g') (by rwa [IsRegSS, e]))).exists
  obtain ⟨c, hc⟩ := isConj_iff.1 (hx ((hsub ⟨x, rfl⟩).trans e.symm))
  refine ⟨x * c, ?_⟩
  simp only at hc ⊢
  rw [_root_.mul_inv_rev, mul_assoc c⁻¹, ← mul_assoc, mul_assoc c⁻¹, ← hc]
  group

end Unitary

section Points

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin m) (Fin m) E}

theorem isClosed_class_HA (h : IsCMExt F E σ) (hJ : IsHermND σ J) (k : Type) [NontriviallyNormedField k] [CompleteSpace k]
    [Algebra F k] {g : HA k σ J} (hg : IsRegSS (matHom k σ J g).1) :
    IsClosed (range fun x : HA k σ J => x⁻¹ * g * x) := by
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap F k).injective
  have : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) k
  have : T2Space (k ⊗[F] E) := e.isEmbedding.t2Space
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  refine isClosed_class_UJ k (σ := sigR k σ) (J := JR k J) two_ne_zero (fun c a => ?_) (fun a => ?_) ?_ ?_ hg
  · exact map_smul (Algebra.TensorProduct.map (AlgHom.id k k) σ) c a
  · induction a with
    | zero => simp
    | tmul a b => simp [sigR, hσ]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  · ext i j
    simp [cT, JR, sigR, inclR, hJ.1]
  · rw [JR, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hJ.2.isUnit.map _

theorem isClosed_class_GLoc (h : IsCMExt F E σ) (hJ : IsHermND σ J) {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v}
    (hg : IsRegSS (matHom _ σ J g).1) : IsClosed (range fun x : GLoc σ J v => x⁻¹ * g * x) :=
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField _ _
  isClosed_class_HA h hJ (Fv F v) hg

theorem isClosed_class_GArch (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} {g : GArch σ J w}
    (hg : IsRegSS (matHom _ σ J g).1) : IsClosed (range fun x : GArch σ J w => x⁻¹ * g * x) :=
  letI : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by
        rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_ofNat]
        simp⟩ }
  isClosed_class_HA h hJ w.Completion hg

theorem isClosed_class_realUJ {ε : Fin m → Bool} {g : Formalism.REAL.UJ ε} (hg : IsRegSS (ujMat ε g)) :
    IsClosed (range fun x : Formalism.REAL.UJ ε => x⁻¹ * g * x) :=
  isClosed_class_UJ ℝ (σ := starRingEnd ℂ) (J := Formalism.REAL.Jm ε) two_ne_zero (fun c a => by simp)
    (fun a => star_star a) (Formalism.REAL.Jm_conjTranspose ε)
    (Matrix.isUnit_det_of_left_inverse (Formalism.REAL.Jm_mul_self ε)) (g := g) hg

theorem isProperOrbit_GLoc (h : IsCMExt F E σ) (hJ : IsHermND σ J) {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v}
    (hg : IsRegSS (matHom _ σ J g).1) : IsProperOrbit (cent g) g :=
  isProperOrbit_of_isClosed (isClosed_class_GLoc h hJ hg)

theorem isProperOrbit_GArch (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} {g : GArch σ J w}
    (hg : IsRegSS (matHom _ σ J g).1) : IsProperOrbit (cent g) g :=
  isProperOrbit_of_isClosed (isClosed_class_GArch h hJ hg)

theorem isProperOrbit_realUJ {ε : Fin m → Bool} {g : Formalism.REAL.UJ ε} (hg : IsRegSS (ujMat ε g)) :
    IsProperOrbit (cent g) g :=
  isProperOrbit_of_isClosed (isClosed_class_realUJ hg)

theorem isMulCommutative_cent_realUJ {ε : Fin m → Bool} {g : Formalism.REAL.UJ ε} (hg : IsRegSS (ujMat ε g)) :
    IsMulCommutative (cent g) :=
  isMulCommutative_cent (ι := ujMat ε) (Units.val_injective.comp Subtype.val_injective) hg

theorem isRegSS_archMat_iff (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {g : GArch σ J w} :
    IsRegSS (archMat σ J τ g) ↔ IsRegSS (matHom _ σ J g).1 := by
  refine ⟨fun hg => ?_, fun hg => (archMat_apply σ J τ g).symm ▸ hg.map (infEmb τ)⟩
  let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
  convert hg.map e.symm.toRingHom using 1
  exact Matrix.ext fun i j => (e.symm_apply_apply _).symm

end Points

def IsRegClosed {H : Type} [Group H] [TopologicalSpace H] (g : H) : Prop :=
  IsMulCommutative (cent g) ∧
    (∀ [MeasurableSpace H] (dt : Measure (cent g)) [dt.IsMulLeftInvariant], dt.IsMulRightInvariant) ∧
    IsClosed (range fun x : H => x⁻¹ * g * x) ∧ IsProperOrbit (cent g) g

theorem IsRegClosed.of {H : Type} [Group H] [TopologicalSpace H] {g : H} (h1 : IsMulCommutative (cent g))
    (h2 : IsClosed (range fun x : H => x⁻¹ * g * x)) (h3 : IsProperOrbit (cent g) g) : IsRegClosed g :=
  ⟨h1, fun dt _ => isMulRightInvariant_cent h1 dt, h2, h3⟩

end GlobalTheory.Orb
