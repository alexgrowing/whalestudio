import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi

noncomputable section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
namespace GlobalTheory.MemN.SerInhab

theorem trace_mulLeft {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ a) = (Fintype.card G : ℂ) * a.coeff 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  have : ∀ x : G, (LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
      (LinearMap.mulLeft ℂ a)).diag x = a.coeff 1 := by
    intro x
    simp [Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis]
  rw [Finset.sum_congr rfl fun x _ => this x]
  simp

theorem coeff_mem {G : Type} [Group G] [Finite G] {N : ℕ} (hN : 0 < N) (hG : Nat.card G ∣ N)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) (hc : ∀ a, e * a = a * e) (x : G) :
    e.coeff x ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  classical
  haveI := Fintype.ofFinite G
  set K := IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} with hK
  set s : MonoidAlgebra ℂ G := MonoidAlgebra.single x⁻¹ 1 with hs
  have hsN : s ^ N = 1 := by
    rw [hs, MonoidAlgebra.single_pow, one_pow,
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard x⁻¹).trans hG)]
    rfl
  have hpow : (e * s) ^ (N + 1) = e * s := by
    rw [Commute.mul_pow (hc s), IsIdempotentElem.pow_succ_eq N he, pow_succ, hsN, one_mul]
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  have hζK : Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K :=
    IntermediateField.mem_adjoin_simple_self _ _
  have htr : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ (e * s)) ∈ K := by
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    refine multiset_sum_mem _ fun μ hμ => ?_
    have hroot := isRoot_of_mem_roots hμ
    have h1 := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot
    obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
    have h2 := hv.pow_apply (N + 1)
    rw [LinearMap.pow_mulLeft, hpow, hv.apply_eq_smul] at h2
    have h3 : μ = μ ^ (N + 1) := smul_left_injective ℂ hv.2 h2
    by_cases h0 : μ = 0
    · rw [h0]; exact zero_mem _
    · have h4 : μ ^ N = 1 := by
        rw [pow_succ] at h3
        exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h3.symm)
      haveI : NeZero N := ⟨hN.ne'⟩
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h4
      rw [← hi]; exact pow_mem hζK i
  rw [trace_mulLeft] at htr
  have h5 : (e * s).coeff 1 = e.coeff x := by simp [hs]
  rw [h5] at htr
  have h6 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have := mul_mem (inv_mem (natCast_mem K (Fintype.card G))) htr
  rwa [← mul_assoc, inv_mul_cancel₀ h6, one_mul] at this

theorem exists_primitive (G : Type) [Group G] [Finite G] :
    ∃ (n : ℕ) (p : Fin n → MonoidAlgebra ℂ G), (∀ i, p i * p i = p i) ∧ (∀ i a, p i * a = a * p i) ∧
      (∀ i j, i ≠ j → p i * p j = 0) ∧ (∀ i, p i ≠ 0) ∧ ∑ i, p i = 1 ∧
      ∀ z, (∀ a, z * a = a * z) → z ∈ Submodule.span ℂ (Set.range p) := by
  classical
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨n, d, hd, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  refine ⟨n, fun i => φ.symm (Pi.single i 1), fun i => ?_, fun i a => ?_, fun i j hij => ?_, fun i => ?_, ?_,
    fun z hz => ?_⟩
  · rw [← map_mul, ← Pi.single_mul, one_mul]
  · apply φ.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply]
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  · rw [← map_mul, map_eq_zero_iff _ φ.symm.injective]
    funext k
    by_cases h : k = i
    · subst h; simp [hij]
    · simp [h]
  · rw [ne_eq, map_eq_zero_iff _ φ.symm.injective]
    intro h
    haveI := hd i
    have h' := congrFun h i
    rw [Pi.single_eq_same] at h'
    exact one_ne_zero h'
  · rw [← map_sum, Finset.univ_sum_single, ← map_one φ.symm]; rfl
  · have hc : ∀ y, φ z * y = y * φ z := by
      intro y
      obtain ⟨x, rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, hz]
    have h1 : ∀ i, ∃ c : ℂ, φ z i = c • 1 := by
      intro i
      have hci : ∀ M : Matrix (Fin (d i)) (Fin (d i)) ℂ, φ z i * M = M * φ z i := by
        intro M
        have := congrFun (hc (Pi.single i M)) i
        simpa using this
      obtain ⟨c, hcc⟩ := Matrix.mem_range_scalar_of_commute_single (M := φ z i) (fun a b _ => (hci _).symm)
      exact ⟨c, by rw [← hcc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
    choose c hc' using h1
    have h2 : z = ∑ i, c i • φ.symm (Pi.single i 1) := by
      apply φ.injective
      simp only [map_sum, map_smul, AlgEquiv.apply_symm_apply]
      funext j
      rw [hc', Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb.symm]
      · simp
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_family {G S : Type} [Group G] [Finite G] (c : G → S) (hc : Function.Surjective c)
    (hconj : ∀ x y, c (x * y) = c (y * x)) [Fintype S] :
    ∃ (q : S → MonoidAlgebra ℂ G), (∀ i, q i * q i = q i) ∧ (∀ i a, q i * a = a * q i) ∧
      (∀ i j, i ≠ j → q i * q j = 0) ∧ (∀ i, q i ≠ 0) ∧ ∑ i, q i = 1 := by
  classical
  obtain ⟨n, p, h1, h2, h3, h4, h5, h6⟩ := exists_primitive G
  let z : S → MonoidAlgebra ℂ G := fun s =>
    .ofCoeff (Finsupp.equivFunOnFinite.symm fun x => if c x = s then 1 else 0)
  have hz : ∀ s x, (z s).coeff x = if c x = s then 1 else 0 := fun s x => rfl
  have hzc : ∀ s a, z s * a = a * z s := by
    intro s a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
    | single x r =>
      ext y
      simp [hz, hconj y, mul_comm]
  have hli : LinearIndependent ℂ z := by
    rw [Fintype.linearIndependent_iff]
    intro a ha s
    obtain ⟨x, rfl⟩ := hc s
    have := congrArg (fun w : MonoidAlgebra ℂ G => w.coeff x) ha
    simpa [hz, Finsupp.finset_sum_apply] using this
  have hcard : Fintype.card S ≤ Fintype.card (Fin n) := by
    have := linearIndependent_le_span_aux' z hli (Set.range p) (by rintro _ ⟨s, rfl⟩; exact h6 _ (hzc s))
    exact this.trans (Fintype.card_range_le p)
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  haveI : Nonempty S := ⟨c 1⟩
  obtain ⟨π, hπ⟩ : ∃ π : Fin n → S, Function.Surjective π :=
    ⟨Function.invFun ι, Function.invFun_surjective ι.injective⟩
  let q : S → MonoidAlgebra ℂ G := fun s => ∑ i ∈ Finset.univ.filter (fun i => π i = s), p i
  have hpq : ∀ i s, p i * q s = if π i = s then p i else 0 := by
    intro i s
    simp only [q, Finset.mul_sum]
    rw [Finset.sum_filter, Finset.sum_eq_single i]
    · rw [h1]
    · intro b _ hb; rw [h3 i b hb.symm]; simp
    · simp
  refine ⟨q, fun s => ?_, fun s a => ?_, fun s t hst => ?_, fun s h => ?_, ?_⟩
  · conv_lhs => enter [1]; simp only [q]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [hpq, if_pos (by simpa using hi)]
  · simp only [q, Finset.sum_mul, Finset.mul_sum, h2]
  · conv_lhs => enter [1]; simp only [q]
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : π i = s := by simpa using hi
    rw [hpq, if_neg (this ▸ hst)]
  · obtain ⟨i, rfl⟩ := hπ s
    have := hpq i (π i)
    rw [h, mul_zero, if_pos rfl] at this
    exact h4 i this.symm
  · rw [← h5]; exact Finset.sum_fiberwise _ _ _

theorem exists_charpoly {F : Type} [Field F] {r : ℕ} (f : F[X]) (hm : f.Monic) (hd : f.natDegree = r)
    (h0 : f.coeff 0 ≠ 0) : ∃ x : GL (Fin r) F, (x : Matrix (Fin r) (Fin r) F).charpoly = f := by
  subst hd
  let pb := AdjoinRoot.powerBasis' hm
  have h : (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = f := by
    rw [charpoly_leftMulMatrix]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hm
  let M : Matrix (Fin f.natDegree) (Fin f.natDegree) F := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = f := h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) h0
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hM⟩

theorem exists_isSer : ∀ (r g N : ℕ), g.Prime → 0 < N → Nat.card (GL (Fin r) (ZMod g)) ∣ N →
    ∃ e, IsSer r g N e := by
  intro r g N hg hN hG
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  let P : (ZMod g)[X] → Prop := fun f => f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0
  let c : GL (Fin r) (ZMod g) → {f // P f} := fun x =>
    ⟨(x : Matrix (Fin r) (Fin r) (ZMod g)).charpoly, Matrix.charpoly_monic _, by simp, by
      intro h
      have h2 := Matrix.det_eq_sign_charpoly_coeff (x : Matrix (Fin r) (Fin r) (ZMod g))
      rw [h, mul_zero] at h2
      exact x.det_ne_zero h2⟩
  have hc : Function.Surjective c := by
    rintro ⟨f, h1, h2, h3⟩
    obtain ⟨x, hx⟩ := exists_charpoly f h1 h2 h3
    exact ⟨x, Subtype.ext hx⟩
  haveI : Finite {f // P f} := Finite.of_surjective c hc
  haveI := Fintype.ofFinite {f // P f}
  obtain ⟨q, h1, h2, h3, h4, h5⟩ := exists_family c hc (fun x y => Subtype.ext (by
    simp only [c, Units.val_mul]; exact Matrix.charpoly_mul_comm _ _))
  let e : (ZMod g)[X] → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) := fun f => if h : P f then q ⟨f, h⟩ else 0
  have hi : ∀ f, e f * e f = e f := by
    intro f; by_cases h : P f <;> simp [e, h, h1]
  have hce : ∀ f a, e f * a = a * e f := by
    intro f a; by_cases h : P f <;> simp [e, h, h2]
  refine ⟨e, hi, hce, fun f f' hf => ?_, fun f => ?_, ⟨Finset.univ.map (Function.Embedding.subtype P), fun f => ?_, ?_⟩,
    fun f x => coeff_mem hN hG _ (hi f) (hce f) x⟩
  · by_cases h : P f
    · by_cases h' : P f'
      · simp only [e, dif_pos h, dif_pos h']
        exact h3 _ _ (fun hh => hf (congrArg Subtype.val hh))
      · simp [e, h']
    · simp [e, h]
  · change e f = 0 ↔ ¬ P f
    by_cases h : P f <;> simp [e, h, h4]
  · change _ ↔ P f
    simp
  · rw [Finset.sum_map, ← h5]
    exact Finset.sum_congr rfl fun s _ => by simp [e, s.2]

end GlobalTheory.MemN.SerInhab
