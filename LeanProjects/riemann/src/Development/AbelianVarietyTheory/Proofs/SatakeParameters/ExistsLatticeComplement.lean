import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenvectorOfTraceEqAddCharacter

noncomputable section

namespace GlobalTheory.LatticeComplement

open Formalism.MainNotions.N Polynomial Matrix

variable {Γ : Type} [Group Γ]

open Polynomial Matrix in
variable {Γ : Type} [Group Γ] in

theorem _root_.GlobalTheory.LatticeComplement.isSSRep_of_intertwine {k : Type} [Field k] {a b : ℕ} (ρ : Γ →* GL (Fin a) k)
    (ρ₁ : Γ →* GL (Fin b) k) (E : Matrix (Fin b) (Fin a) k) (P : Matrix (Fin a) (Fin b) k)
    (hEP : E * P = 1)
    (hint : ∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) * P =
      P * ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k))
    (hρ : _root_.Formalism.MainNotions.N.IsSSRep ρ) : _root_.Formalism.MainNotions.N.IsSSRep ρ₁ := by
  unfold _root_.Formalism.MainNotions.N.IsSSRep at hρ ⊢
  intro W hW
  unfold _root_.Formalism.MainNotions.N.IsInv at hW
  have hinj : ∀ v : Fin b → k, P *ᵥ v = 0 → v = 0 := fun v hv => by
    have h := congrArg (fun w => E *ᵥ w) hv
    simpa [Matrix.mulVec_mulVec, hEP] using h
  obtain ⟨U, hU, hc⟩ := hρ (W.map (Matrix.mulVecLin P)) (by
    unfold _root_.Formalism.MainNotions.N.IsInv
    rintro g _ ⟨w, hw, rfl⟩
    refine ⟨((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) *ᵥ w, hW g w hw, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint g])
  unfold _root_.Formalism.MainNotions.N.IsInv at hU
  refine ⟨U.comap (Matrix.mulVecLin P), ?_, ?_⟩
  · unfold _root_.Formalism.MainNotions.N.IsInv
    intro g v hv
    simp only [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hint g, ← Matrix.mulVec_mulVec]
    exact hU g _ hv
  · constructor
    · rw [Submodule.disjoint_def]
      intro v hvW hvU
      apply hinj
      have h1 : Matrix.mulVecLin P v ∈ W.map (Matrix.mulVecLin P) := Submodule.mem_map_of_mem hvW
      exact (Submodule.disjoint_def.mp hc.disjoint) _ h1 hvU
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : Matrix.mulVecLin P v ∈ W.map (Matrix.mulVecLin P) ⊔ U := by
        rw [hc.codisjoint.eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, u, hu, hyu⟩ := Submodule.mem_sup.mp hv
      obtain ⟨w, hw, rfl⟩ := hy
      have hsplit : v = w + (v - w) := by abel
      rw [hsplit]
      refine Submodule.add_mem_sup hw ?_
      rw [Submodule.mem_comap, map_sub, ← hyu]
      simpa using hu

open Polynomial Matrix in
variable {Γ : Type} [Group Γ] in
private theorem exists_smul_primitive_vector_of_dvr {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m : ℕ} (x : Fin m → O) (hx : x ≠ 0) :
    ∃ d : O, d ≠ 0 ∧ ∃ y : Fin m → O, x = d • y ∧ ∃ i, IsUnit (y i) := by
  classical
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range x))).principal
  have hmem : ∀ i, x i ∈ Ideal.span {d} := fun i => by
    rw [← Ideal.submodule_span_eq, ← hd]; exact Ideal.subset_span ⟨i, rfl⟩
  choose y hy using fun i => Ideal.mem_span_singleton'.mp (hmem i)
  have hdI : d ∈ Ideal.span (Set.range x) := by
    rw [hd]; exact Submodule.mem_span_singleton_self d
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hdI
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hx
    funext i
    rw [← hy i, mul_zero]
    rfl
  have hsum : ∑ i, c i * y i = 1 := by
    apply mul_left_cancel₀ hd0
    rw [mul_one, Finset.mul_sum]
    conv_rhs => rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hy i]; ring
  refine ⟨d, hd0, y, funext fun i => by simp [← hy i, mul_comm], ?_⟩
  by_contra hno
  push_neg at hno
  have hmax : ∑ i, c i * y i ∈ IsLocalRing.maximalIdeal O :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
      ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hno i)))
  rw [hsum] at hmax
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmax)) isUnit_one

open Polynomial Matrix in
variable {Γ : Type} [Group Γ] in
private theorem isSSRep_of_intertwining_quotient {k : Type} [Field k] {a b : ℕ} (ρ : Γ →* GL (Fin a) k)
    (ρ₁ : Γ →* GL (Fin b) k) (Q : Matrix (Fin b) (Fin a) k) (S : Matrix (Fin a) (Fin b) k)
    (hQS : Q * S = 1)
    (hint : ∀ g, Q * ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) * Q)
    (hρ : _root_.Formalism.MainNotions.N.IsSSRep ρ) : _root_.Formalism.MainNotions.N.IsSSRep ρ₁ := by
  unfold _root_.Formalism.MainNotions.N.IsSSRep at hρ ⊢
  intro W hW
  unfold _root_.Formalism.MainNotions.N.IsInv at hW
  obtain ⟨U, hU, hc⟩ := hρ (W.comap (Matrix.mulVecLin Q)) (by
    unfold _root_.Formalism.MainNotions.N.IsInv
    intro g v hv
    simp only [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hint g, ← Matrix.mulVec_mulVec]
    exact hW g _ hv)
  unfold _root_.Formalism.MainNotions.N.IsInv at hU
  refine ⟨U.map (Matrix.mulVecLin Q), ?_, ?_⟩
  · unfold _root_.Formalism.MainNotions.N.IsInv
    rintro g _ ⟨u, hu, rfl⟩
    refine ⟨((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) *ᵥ u, hU g u hu, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint g]
  · constructor
    · rw [Submodule.disjoint_def]
      rintro _ hxW ⟨u, hu, rfl⟩
      have hu0 : u = 0 := (Submodule.disjoint_def.mp hc.disjoint) u hxW hu
      simp [hu0]
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : S *ᵥ x ∈ W.comap (Matrix.mulVecLin Q) ⊔ U := by
        rw [hc.codisjoint.eq_top]; exact Submodule.mem_top
      obtain ⟨p, hp, u, hu, hpu⟩ := Submodule.mem_sup.mp hx
      have hxeq : x = Q *ᵥ p + Q *ᵥ u := by
        rw [← Matrix.mulVec_add, hpu, Matrix.mulVec_mulVec, hQS, Matrix.one_mulVec]
      rw [hxeq]
      exact Submodule.add_mem_sup hp (Submodule.mem_map_of_mem hu)

open Polynomial Matrix in
variable {Γ : Type} [Group Γ] in
private theorem exists_quotient_of_eigenvector_lemma_2 {O K : Type} [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [Field K] [TopologicalSpace Γ] (φ : O →+* K) {n : ℕ}
    (ρ : Γ →* GL (Fin (n + 1)) O) (χ : Γ →* Oˣ) (v : Fin (n + 1) → O) (i₀ : Fin (n + 1))
    (hu : IsUnit (v i₀))
    (hv : ∀ g, ((ρ g : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O) *ᵥ v =
      ((χ g : Oˣ) : O) • v)
    (hc : Continuous fun g => ((ρ g : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O))
    (hss : _root_.Formalism.MainNotions.N.IsSSRep (_root_.Formalism.MainNotions.N.mapRep φ ρ)) :
    ∃ ρ' : Γ →* GL (Fin n) O,
      Continuous (fun g => ((ρ' g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) ∧
      _root_.Formalism.MainNotions.N.IsSSRep (_root_.Formalism.MainNotions.N.mapRep φ ρ') ∧
      ∀ g, ((ρ g : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O).charpoly =
        ((ρ' g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).charpoly * (X - C ((χ g : Oˣ) : O)) := by
  classical
  obtain ⟨u, hu'⟩ := hu
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) O := Matrix.of fun i k =>
    Fin.cases (v i) (fun j => if i = i₀.succAbove j then (1 : O) else 0) k
  let T' : Matrix (Fin (n + 1)) (Fin (n + 1)) O := Matrix.of fun k x =>
    Fin.cases (if x = i₀ then ((u⁻¹ : Oˣ) : O) else 0)
      (fun j => (if x = i₀.succAbove j then (1 : O) else 0) -
        if x = i₀ then v (i₀.succAbove j) * ((u⁻¹ : Oˣ) : O) else 0) k
  have hT : T' * T = 1 := by
    ext k l
    refine Fin.cases ?_ (fun j => ?_) k <;> refine Fin.cases ?_ (fun m => ?_) l <;>
      simp [T, T', Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib, ← hu', Matrix.one_apply,
        Fin.succAbove_ne, Fin.succ_ne_zero, eq_comm]

  have hT2 : T * T' = 1 := mul_eq_one_comm.mp hT
  let B : Γ → Matrix (Fin (n + 1)) (Fin (n + 1)) O := fun g =>
    T' * ((ρ g : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O) * T
  have hB0 : ∀ g i, B g i 0 = ((χ g : Oˣ) : O) * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) O) i 0 := by
    intro g i
    have hcol : ∀ x, (((ρ g : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O) * T) x 0 =
        ((χ g : Oˣ) : O) * T x 0 := by
      intro x
      have h := congrFun (hv g) x
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, T] using h
    simp only [B, Matrix.mul_assoc]
    rw [← hT, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hcol]; ring
  have hBmul : ∀ g h, B (g * h) = B g * B h := by
    intro g h
    have e : B g * B h = T' * ((ρ g : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O) *
        (T * T') * (((ρ h : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O) * T) := by
      simp only [B, Matrix.mul_assoc]
    rw [e, hT2, Matrix.mul_one]
    simp only [B, map_mul, Units.val_mul, Matrix.mul_assoc]
  have hB1 : B 1 = 1 := by simp [B, hT]
  have hBT : ∀ g, T' * ((ρ g : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O) = B g * T' := by
    intro g
    simp only [B, Matrix.mul_assoc, hT2, Matrix.mul_one]
  let σ : Γ →* Matrix (Fin n) (Fin n) O :=
    { toFun := fun g => (B g).submatrix Fin.succ Fin.succ
      map_one' := by
        ext i j
        simp [hB1, Matrix.one_apply]
      map_mul' := by
        intro g h
        ext i k
        simp only [Matrix.submatrix_apply]
        rw [hBmul, Matrix.mul_apply, Fin.sum_univ_succ, hB0]
        simp [Matrix.mul_apply, Matrix.one_apply, Fin.succ_ne_zero] }
  have hσ : ∀ g, σ g = (B g).submatrix Fin.succ Fin.succ := fun g => rfl
  have hmap : ∀ {m : ℕ} (τ : Γ →* GL (Fin m) O) (g : Γ),
      ((_root_.Formalism.MainNotions.N.mapRep φ τ g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        ((τ g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map φ := by
    intro m τ g
    unfold _root_.Formalism.MainNotions.N.mapRep
    simp
  refine ⟨σ.toHomUnits, ?_, ?_, ?_⟩
  · simp only [MonoidHom.coe_toHomUnits, hσ]
    exact (((continuous_const.matrix_mul hc).matrix_mul continuous_const)).matrix_submatrix _ _
  · refine isSSRep_of_intertwining_quotient (_root_.Formalism.MainNotions.N.mapRep φ ρ) (_root_.Formalism.MainNotions.N.mapRep φ σ.toHomUnits)
      ((T'.submatrix Fin.succ id).map φ) ((T.submatrix id Fin.succ).map φ) ?_ ?_ hss
    · rw [← Matrix.map_mul, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hT]
      ext i j
      simp [Matrix.one_apply]
    · intro g
      rw [hmap, hmap, MonoidHom.coe_toHomUnits, hσ, ← Matrix.map_mul, ← Matrix.map_mul]
      congr 1
      ext i x
      have h2 : (B g * T') i.succ x = ∑ j : Fin n, B g i.succ j.succ * T' j.succ x := by
        rw [Matrix.mul_apply, Fin.sum_univ_succ, hB0]
        simp [Matrix.one_apply, Fin.succ_ne_zero]
      have h := congrFun (congrFun (hBT g) (Fin.succ i)) x
      rw [h2] at h
      simpa [Matrix.mul_apply] using h
  · intro g
    let M : (Matrix (Fin (n + 1)) (Fin (n + 1)) O)ˣ := ⟨T', T, hT, hT2⟩
    have hconj : (B g).charpoly =
        ((ρ g : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O).charpoly := by
      have h := Matrix.charpoly_units_conj M
        ((ρ g : GL (Fin (n + 1)) O) : Matrix (Fin (n + 1)) (Fin (n + 1)) O)
      rw [← Matrix.coe_units_inv] at h
      exact h
    rw [← hconj, MonoidHom.coe_toHomUnits, hσ, Matrix.charpoly, Matrix.charpoly,
      Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hsub : (B g).charmatrix.submatrix (Fin.succAbove 0) Fin.succ =
        ((B g).submatrix Fin.succ Fin.succ).charmatrix := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.charmatrix_apply_eq]
      · rw [Matrix.submatrix_apply, Fin.succAbove_zero, Matrix.charmatrix_apply_ne _ _ _ (by simpa using hij),
          Matrix.charmatrix_apply_ne _ _ _ hij]
        rfl
    have hrest : ∀ i : Fin n, (B g).charmatrix i.succ 0 = 0 := by
      intro i
      rw [Matrix.charmatrix_apply_ne _ _ _ (Fin.succ_ne_zero i), hB0]
      simp [Matrix.one_apply, Fin.succ_ne_zero]
    simp only [hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, hsub]
    rw [Matrix.charmatrix_apply_eq, hB0]
    simp only [Matrix.one_apply_eq, mul_one, Fin.val_zero, pow_zero, one_mul]
    ring

open Polynomial Matrix in
variable {Γ : Type} [Group Γ] in

theorem _root_.GlobalTheory.LatticeComplement.exists_lattice_complement : ∀ (Γ O K : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ρ : Γ →* GL (Fin (r + t)) O) (χ : Fin t → Γ →* Oˣ), Continuous (fun g => ((ρ g : GL (Fin (r + t)) O) : Matrix (Fin (r + t)) (Fin (r + t)) O)) → _root_.Formalism.MainNotions.N.IsSSRep (_root_.Formalism.MainNotions.N.mapRep (algebraMap O K) ρ) → (∃ (L : Type) (_ : Field L) (f : K →+* L) (ρ₀ : Γ →* GL (Fin r) L), ∀ g, (((ρ g : GL (Fin (r + t)) O) : Matrix (Fin (r + t)) (Fin (r + t)) O).charpoly).map (f.comp (algebraMap O K)) = ((ρ₀ g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L).charpoly * ∏ c, (X - C (f (algebraMap O K ((χ c g : Oˣ) : O))))) → ∃ ρ' : Γ →* GL (Fin r) O, Continuous (fun g => ((ρ' g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O)) ∧ _root_.Formalism.MainNotions.N.IsSSRep (_root_.Formalism.MainNotions.N.mapRep (algebraMap O K) ρ') ∧ ∀ g, ((ρ g : GL (Fin (r + t)) O) : Matrix (Fin (r + t)) (Fin (r + t)) O).charpoly = ((ρ' g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).charpoly * ∏ c, (X - C ((χ c g : Oˣ) : O)) := by
  intro Γ O K _ _ _ _ _ _ _ _ _ _ _ _ _ r t
  induction t with
  | zero =>
    intro ρ χ hc hss _
    exact ⟨ρ, hc, hss, fun g => by simp⟩
  | succ t ih =>
    intro ρ χ hc hss hL
    classical
    obtain ⟨L, _, f, ρ₀, hρ₀⟩ := hL
    let τ : Γ →* Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) L :=
      { toFun := fun g => Matrix.fromBlocks ((ρ₀ g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) 0 0
          (Matrix.diagonal fun c => f (algebraMap O K ((χ c.castSucc g : Oˣ) : O)))
        map_one' := by simp
        map_mul' := by
          intro g h
          simp [Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal] }
    let χK : Γ →* Kˣ := (Units.map (algebraMap O K : O →* K)).comp (χ (Fin.last t))
    have hmapK : ∀ g, ((_root_.Formalism.MainNotions.N.mapRep (algebraMap O K) ρ g : GL (Fin (r + (t + 1))) K) :
        Matrix (Fin (r + (t + 1))) (Fin (r + (t + 1))) K) =
        ((ρ g : GL (Fin (r + (t + 1))) O) : Matrix (Fin (r + (t + 1))) (Fin (r + (t + 1))) O).map
          (algebraMap O K) := by
      intro g
      unfold _root_.Formalism.MainNotions.N.mapRep
      simp
    have htr : ∀ g, f (LinearMap.trace K (Fin (r + (t + 1)) → K)
        (_root_.GlobalTheory.TraceConj.colRep (_root_.Formalism.MainNotions.N.mapRep (algebraMap O K) ρ) g)) =
        (τ g).trace + f ((χK g : Kˣ) : K) := by
      intro g
      have hF := hρ₀ g
      rw [← Matrix.charpoly_map] at hF
      have h1 := congrArg Polynomial.nextCoeff hF
      rw [(Matrix.charpoly_monic _).nextCoeff_mul
          (monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _),
        Monic.nextCoeff_prod _ _ (fun c _ => monic_X_sub_C _)] at h1
      simp only [nextCoeff_X_sub_C] at h1
      rw [Fin.sum_univ_castSucc] at h1
      have e1 : f (LinearMap.trace K (Fin (r + (t + 1)) → K)
          (_root_.GlobalTheory.TraceConj.colRep (_root_.Formalism.MainNotions.N.mapRep (algebraMap O K) ρ) g)) =
          (((ρ g : GL (Fin (r + (t + 1))) O) : Matrix (Fin (r + (t + 1))) (Fin (r + (t + 1))) O).map
            (f.comp (algebraMap O K))).trace := by
        rw [_root_.GlobalTheory.TraceConj.colRep_apply, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K _),
          LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', hmapK,
          AddMonoidHom.map_trace f, Matrix.map_map]
        rfl
      have e2 : (τ g).trace = ((ρ₀ g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L).trace +
          ∑ c : Fin t, f (algebraMap O K ((χ c.castSucc g : Oˣ) : O)) := by
        simp [τ, Matrix.trace, Fintype.sum_sum_type]
      rw [e1, e2, Matrix.trace_eq_neg_charpoly_nextCoeff,
        Matrix.trace_eq_neg_charpoly_nextCoeff ((ρ₀ g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L), h1]
      simp only [χK, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.comp_apply,
        Finset.sum_neg_distrib]
      ring
    haveI : CharZero L := (RingHom.charZero_iff f.injective).mp inferInstance
    obtain ⟨v, hv0, hv⟩ := _root_.GlobalTheory.exists_eigenvector_of_trace_eq_add_character K L Γ
      (Fin (r + (t + 1)) → K) (Fin r ⊕ Fin t) f
      (_root_.GlobalTheory.TraceConj.colRep (_root_.Formalism.MainNotions.N.mapRep (algebraMap O K) ρ)) τ χK
      (_root_.GlobalTheory.TraceConj.colRep_semisimple _ hss) htr
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ v
    choose x hx using fun i => hb i (Finset.mem_univ i)
    have hbK : algebraMap O K (b : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    have hxv : ∀ i, algebraMap O K (x i) = algebraMap O K (b : O) * v i := by
      intro i; rw [hx i, Algebra.smul_def]
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hv0
      funext i
      have h := hxv i
      simp only [Pi.zero_apply, map_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hbK
    have hxe : ∀ g, ((ρ g : GL (Fin (r + (t + 1))) O) : Matrix (Fin (r + (t + 1))) (Fin (r + (t + 1))) O) *ᵥ x =
        ((χ (Fin.last t) g : Oˣ) : O) • x := by
      intro g
      funext i
      apply IsFractionRing.injective O K
      have hvg := congrFun (hv g) i
      rw [_root_.GlobalTheory.TraceConj.colRep_apply, Matrix.toLin'_apply, hmapK] at hvg
      have hfx : (algebraMap O K) ∘ x = (algebraMap O K (b : O)) • v := by
        funext j; simp [hxv j, smul_eq_mul]
      rw [RingHom.map_mulVec, hfx, Matrix.mulVec_smul, Pi.smul_apply, hvg]
      simp [χK, hxv i, smul_eq_mul]
      ring
    obtain ⟨d, hd0, y, rfl, i₀, hi₀⟩ := exists_smul_primitive_vector_of_dvr x hx0
    have hy : ∀ g, ((ρ g : GL (Fin (r + (t + 1))) O) : Matrix (Fin (r + (t + 1))) (Fin (r + (t + 1))) O) *ᵥ y =
        ((χ (Fin.last t) g : Oˣ) : O) • y := by
      intro g
      apply smul_right_injective (Fin (r + (t + 1)) → O) hd0
      have h := hxe g
      rw [Matrix.mulVec_smul, smul_comm] at h
      exact h
    obtain ⟨ρ₁, hc₁, hss₁, hch₁⟩ := exists_quotient_of_eigenvector_lemma_2 (n := r + t) (algebraMap O K) ρ
      (χ (Fin.last t)) y i₀ hi₀ hy hc hss
    obtain ⟨ρ', hc', hss', hch'⟩ := ih ρ₁ (fun c => χ c.castSucc) hc₁ hss₁ ⟨L, inferInstance, f, ρ₀, by
      intro g
      have h := hρ₀ g
      rw [hch₁ g, Polynomial.map_mul, Fin.prod_univ_castSucc, ← mul_assoc] at h
      apply mul_right_cancel₀ (X_sub_C_ne_zero (f (algebraMap O K ((χ (Fin.last t) g : Oˣ) : O))))
      simpa [Polynomial.map_sub] using h⟩
    refine ⟨ρ', hc', hss', fun g => ?_⟩
    rw [hch₁ g, hch' g, Fin.prod_univ_castSucc, mul_assoc]

end GlobalTheory.LatticeComplement

end
