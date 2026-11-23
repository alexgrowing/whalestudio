import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EiiUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private def bp (X : M4 R) : M4 R := Matrix.of fun i j => if lamW i = lamW j then X i j else 0

private theorem bp_apply (X : M4 R) (i j : Fin 4) : bp X i j = if lamW i = lamW j then X i j else 0 := rfl

private def Tri (s : ℤ) (X : M4 R) : Prop := ∀ i j, s * lamW i < s * lamW j → X i j = 0

private theorem bp_one : bp (1 : M4 R) = 1 := by
  ext i j
  rw [bp_apply]
  split_ifs with h
  · rfl
  · exact (Matrix.one_apply_ne fun e => h (by rw [e])).symm

private theorem bp_add (X Y : M4 R) : bp (X + Y) = bp X + bp Y := by
  ext i j
  simp only [bp_apply, Matrix.add_apply]
  split_ifs <;> simp

private theorem bp_smul (a : R) (X : M4 R) : bp (a • X) = a • bp X := by
  ext i j
  simp only [bp_apply, Matrix.smul_apply]
  split_ifs <;> simp

private theorem bp_mul {s : ℤ} (hs : s ≠ 0) {X Y : M4 R} (hX : Tri s X) (hY : Tri s Y) : bp (X * Y) = bp X * bp Y := by
  ext i j
  simp only [bp_apply, Matrix.mul_apply]
  have key : ∀ k, lamW i ≠ lamW k → lamW i = lamW j → X i k * Y k j = 0 := fun k h1 h2 => by
    rcases lt_or_gt_of_ne (fun e => h1 (mul_left_cancel₀ hs e) : s * lamW i ≠ s * lamW k) with h | h
    · rw [hX i k h, zero_mul]
    · rw [hY k j (h2 ▸ h), mul_zero]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : lamW i = lamW k
    · rw [if_pos h1, if_pos (h1.symm.trans h)]
    · rw [if_neg h1, zero_mul, key k h1 h]
  · refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases h1 : lamW i = lamW k
    · rw [if_neg (fun e : lamW k = lamW j => h (h1.trans e)), mul_zero]
    · rw [if_neg h1, zero_mul]

private theorem lam_rev (i : Fin 4) : lamW i.rev = 1 - lamW i := by revert i; decide

private theorem adj_bp (X : M4 R) : adj (bp X) = bp (adj X) := by
  ext i j
  simp only [bp_apply, adj_apply, lam_rev]
  by_cases h : lamW i = lamW j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun e => h (by linarith)), smul_zero]

private theorem Tri.adj {s : ℤ} {X : M4 R} (hX : Tri s X) : Tri s (adj X) := fun i j h => by
  rw [adj_apply, hX _ _ (by rw [lam_rev, lam_rev]; linarith), smul_zero]

private theorem gsp_bp {s : ℤ} (hs : s ≠ 0) {X : M4 R} (hX : Tri s X) {ν : R} (h : IsGSp ν X) : IsGSp ν (bp X) := by
  unfold IsGSp at *
  rw [adj_bp, ← bp_mul hs hX.adj hX, h, bp_smul, bp_one]

private def bpRep {H : Type} [Group H] {s : ℤ} (hs : s ≠ 0) (r : H →* M4 R) (h : ∀ g, Tri s (r g)) : H →* M4 R where
  toFun g := bp (r g)
  map_one' := by rw [map_one, bp_one]
  map_mul' a b := by rw [map_mul, bp_mul hs (h a) (h b)]

private def ee : M4 R := !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]

private theorem ee_mul : (ee : M4 R) * ee = ee := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ee, Matrix.mul_apply, Fin.sum_univ_four]

private theorem bp_eq (X : M4 R) : bp X = ee * X * ee + (1 - ee) * X * (1 - ee) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four, bp_apply]
  fin_cases i <;> fin_cases j <;> simp [ee, lamW, Matrix.one_apply]

private theorem up_diag {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) : (X * Y) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]

private theorem up_mul {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := fun i j h => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with h' | h'
  · rw [hX i k h', zero_mul]
  · rw [hY k j (h.trans_le h'), mul_zero]

private theorem up_one : IsUp (1 : M4 R) := fun _ _ h => Matrix.one_apply_ne h.ne'

private theorem flag_bp {u v X : M4 R} (h1 : v * u = 1) (he : IsUp (v * ee * u)) (hX : IsUp (v * X * u)) :
    IsUp (v * bp X * u) ∧ ∀ i, (v * bp X * u) i i = (v * X * u) i i := by
  have h2 : u * v = 1 := mul_eq_one_comm.1 h1
  have k : ∀ A B : M4 R, v * (A * B) * u = (v * A * u) * (v * B * u) := fun A B => by
    calc v * (A * B) * u = v * A * (u * v) * B * u := by rw [h2]; noncomm_ring
      _ = _ := by noncomm_ring
  have hf : v * (1 - ee) * u = 1 - v * ee * u := by rw [mul_sub, sub_mul, mul_one, h1]
  have hF : IsUp (1 - v * ee * u) := fun i j h => by rw [Matrix.sub_apply, up_one i j h, he i j h, sub_zero]
  have e : v * bp X * u = (v * ee * u) * (v * X * u) * (v * ee * u) +
      (1 - v * ee * u) * (v * X * u) * (1 - v * ee * u) := by
    rw [bp_eq, mul_add, add_mul, k, k, k, k, hf]
  rw [e]
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.add_apply, up_mul (up_mul he hX) he i j h, up_mul (up_mul hF hX) hF i j h, add_zero]
  · have id := up_diag he he i
    rw [← k, ee_mul] at id
    rw [Matrix.add_apply, up_diag (up_mul he hX) he, up_diag (up_mul hF hX) hF, up_diag he hX, up_diag hF hX,
      Matrix.sub_apply, Matrix.one_apply_eq]
    linear_combination (-2 * (v * X * u) i i) * id

private theorem ee_mem (A : Subalgebra R (M4 R)) (X : M4 R) (hX : X ∈ A) (hb : IsBlock X)
    (hu : IsUnit ((X 0 0 * X 0 0 + X 0 2 * X 2 0 - (X 1 1 + X 3 3) * X 0 0 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) *
      (X 2 0 * X 0 2 + X 2 2 * X 2 2 - (X 1 1 + X 3 3) * X 2 2 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) -
      (X 0 0 * X 0 2 + X 0 2 * X 2 2 - (X 1 1 + X 3 3) * X 0 2) * (X 2 0 * X 0 0 + X 2 2 * X 2 0 - (X 1 1 + X 3 3) * X 2 0))) :
    ee ∈ A := by
  have step : ∀ y0 y1 y2 y3 : R, (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) ∈ A →
      IsUnit (y0 * y3 - y1 * y2) → ee ∈ A := fun y0 y1 y2 y3 hY hu => by
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    convert A.smul_mem (A.sub_mem (A.smul_mem hY (y0 + y3)) (A.mul_mem hY hY)) v using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ee, Matrix.mul_apply, Fin.sum_univ_four] <;>
      first | linear_combination -hv | ring
  have b01 := hb 0 1 (by decide)
  have b03 := hb 0 3 (by decide)
  have b10 := hb 1 0 (by decide)
  have b12 := hb 1 2 (by decide)
  have b21 := hb 2 1 (by decide)
  have b23 := hb 2 3 (by decide)
  have b30 := hb 3 0 (by decide)
  have b32 := hb 3 2 (by decide)
  refine step _ _ _ _ ?_ hu
  convert A.add_mem (A.sub_mem (A.mul_mem hX hX) (A.smul_mem hX (X 1 1 + X 3 3)))
    (A.smul_mem A.one_mem (X 1 1 * X 3 3 - X 1 3 * X 3 1)) using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, b01, b03, b10, b12, b21, b23, b30, b32] <;> ring

private def stab {u v : M4 R} (h1 : v * u = 1) : Subalgebra R (M4 R) where
  carrier := {X | IsUp (v * X * u)}
  mul_mem' {A B} hA hB := by
    have h2 : u * v = 1 := mul_eq_one_comm.1 h1
    have : v * (A * B) * u = (v * A * u) * (v * B * u) := by
      calc v * (A * B) * u = v * A * (u * v) * B * u := by rw [h2]; noncomm_ring
        _ = _ := by noncomm_ring
    show IsUp _
    rw [this]
    exact up_mul hA hB
  add_mem' {A B} hA hB i j h := by
    rw [mul_add, add_mul, Matrix.add_apply, hA i j h, hB i j h, add_zero]
  algebraMap_mem' a i j h := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, h1, Matrix.smul_apply, up_one i j h, smul_zero]

private theorem ee_up [IsLocalRing R] {u v X : M4 R} (h1 : v * u = 1) (hX : IsUp (v * X * u)) (hb : IsBlock X)
    (ho : ∀ i j, i ≠ j → residue R (X i j) = 0) (hd : ∀ i j, lamW i ≠ lamW j → residue R (X i i) ≠ residue R (X j j)) :
    IsUp (v * ee * u) := by
  refine ee_mem (stab h1) X hX hb ?_
  rw [← residue_ne_zero_iff_isUnit]
  simp only [map_sub, map_mul, map_add, ho 0 2 (by decide), ho 2 0 (by decide), ho 1 3 (by decide)]
  have k := mul_ne_zero (mul_ne_zero (sub_ne_zero.2 (hd 0 1 (by decide))) (sub_ne_zero.2 (hd 0 3 (by decide))))
    (mul_ne_zero (sub_ne_zero.2 (hd 2 1 (by decide))) (sub_ne_zero.2 (hd 2 3 (by decide))))
  convert k using 1
  ring

private theorem span_bp {H K : Type} [Group H] [Field K] (ρ : H →* M4 R) (y : R →+* K) (r₁ : H →* M4 K)
    (h : ∀ g, r₁ g = bp (mapRep y ρ g)) (X : M4 R) (hX : X ∈ Submodule.span R (Set.range ρ)) :
    bp (X.map y) ∈ Submodule.span K (Set.range r₁) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, h g⟩
  | zero =>
    have : bp ((0 : M4 R).map y) = 0 := by ext i j; simp [bp_apply]
    rw [this]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    rw [Matrix.map_add _ (map_add y), bp_add]; exact Submodule.add_mem _ ha hb
  | smul a x _ hx =>
    have : (a • x).map y = y a • x.map y := by ext i j; simp
    rw [this, bp_smul]; exact Submodule.smul_mem _ _ hx

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.blockPart :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r, VPt D 𝔞 r → ∀ u, KPair D 𝔞 r u → Ge r 0 2 → Ge r 2 0 → ((∀ i j, lamW i < lamW j → ¬ Ge r i j) ∨ ∀ i j, lamW j < lamW i → ¬ Ge r i j) →
      ∃ r₁ u₁, KPair D 𝔞 r₁ u₁ ∧ (∀ g, IsBlock (r₁ g)) ∧
        Submodule.span 𝔞.K (Set.range fun g => (mapRep 𝔞.toK r₁ g).submatrix ixA ixA) = ⊤ := by
  intro Ω _ _ _ l _ c D hD 𝔞 r hV u hK h02 h20 ht
  obtain ⟨s, hs, hT⟩ : ∃ s : ℤ, s ≠ 0 ∧ ∀ g, Tri s (r g) := by
    rcases ht with h | h
    · exact ⟨1, one_ne_zero, fun g i j hij => by_contra fun hn => h i j (by linarith) ⟨g, hn⟩⟩
    · exact ⟨-1, by decide, fun g i j hij => by_contra fun hn => h i j (by linarith) ⟨g, hn⟩⟩
  obtain ⟨-, R, _, _, _, ρ, y, hpt, -, -, hr⟩ := hV
  obtain ⟨-, hTT, -, -, -, -, -, -, hphG, hph, -⟩ := facts D hD
  have hl := (hTT l (Finset.mem_insert_self _ _)).2.2
  have h1 : adj u * u = 1 := by simpa [IsGSp] using hK.sp
  have hred : ∀ g i j, residue 𝔞.V (r g i j) = 𝔞.j c (D.rbar g i j) := fun g i j => by
    have := (residue_eq_zero_iff _).2 (hK.red g i j)
    rw [map_sub, sub_eq_zero] at this
    rw [this]
    rfl
  have hee : IsUp (adj u * ee * u) := by
    refine ee_up h1 (hK.flag _ hphG) (fun i j h => ?_) (fun i j h => ?_) fun i j h => ?_
    · rw [hr, mapRep_apply, hpt.nrm.1 i j h, map_zero]
    · rw [hred]
      simp [Raw.rbar, Raw.r0, diagRep, h]
    · rw [hred, hred, hph]
      refine fun e => hl i j h ?_
      simpa [Raw.rbar, Raw.r0, diagRep] using (𝔞.j c).injective e
  have hb : ∀ g, IsBlock (bpRep hs r hT g) := fun g i j h => if_neg h
  have hm : ∀ g, IsGSp (𝔞.a c (D.th g)) (bpRep hs r hT g) := fun g => gsp_bp hs (hT g) (hK.mult g)
  have h_one : ∀ g, r g = 1 → bpRep hs r hT g = 1 := fun g h => by
    show bp (r g) = 1
    rw [h, bp_one]
  refine ⟨bpRep hs r hT, u, ⟨?_, fun g i j => ?_, hm, fun A hA g hg h => h_one g (hK.unr A hA g hg h),
    fun p hp g hg => h_one g (hK.atP p hp g hg), hK.sp, fun t ht => (flag_bp h1 hee (hK.flag t ht)).1,
    fun t ht i => ?_, fun t ht i => ?_⟩, hb, ?_⟩
  · obtain ⟨A, _, _, _, f, P, hf, hc, hP⟩ := hK.small
    have e1 : ∀ g i j, f (P.r g i j) = r g i j := fun g i j => congrArg (fun Q : PD Unit _ _ => Q.r g i j) hP
    have hT' : ∀ g, Tri s (P.r g) := fun g i j h => hf.inj (by rw [e1, hT g i j h, map_zero])
    refine ⟨A, inferInstance, inferInstance, inferInstance, f, ⟨bpRep hs P.r hT', P.n⟩, hf, fun i j => ?_, ?_⟩
    · show AdicCont _ fun g => if lamW i = lamW j then P.r g i j else 0
      split_ifs
      · exact hc i j
      · exact fun n => IsLocallyConstant.const _
    · have e2 := congrArg PD.n hP
      refine PD.ext ?_ e2
      ext g i j
      show ((f (if lamW i = lamW j then P.r g i j else 0) : 𝔞.V) : 𝔞.K) = ((if lamW i = lamW j then r g i j else 0 : 𝔞.V) : 𝔞.K)
      split_ifs
      · rw [e1]
      · rw [map_zero]
  · show (if lamW i = lamW j then r g i j else 0) - _ ∈ _
    split_ifs with h
    · exact hK.red g i j
    · have : i ≠ j := fun e => h (by rw [e])
      simp [Raw.r0, diagRep, this]
  · show (adj u * bp (r t) * u) i i - _ ∈ _
    rw [(flag_bp h1 hee (hK.flag t ht)).2]
    exact hK.char t ht i
  · show (adj u * bp (r t) * u) i i = _
    rw [(flag_bp h1 hee (hK.flag t (Ine_le_Dec _ ht))).2]
    exact hK.inert t ht i
  · have he : ∀ i, Matrix.single i i (1 : 𝔞.K) ∈ Submodule.span 𝔞.K (Set.range (mapRep 𝔞.toK (bpRep hs r hT))) := fun i => by
      have := span_bp ρ.hom (𝔞.toK.comp y) (mapRep 𝔞.toK (bpRep hs r hT)) (fun g => by
        ext a b
        show 𝔞.toK (if lamW a = lamW b then r g a b else 0) = if lamW a = lamW b then 𝔞.toK (y (ρ.hom g a b)) else 0
        split_ifs
        · rw [hr]; rfl
        · rfl) _ (eii D hD R ρ hpt.mult hpt.nrm i)
      convert this using 1
      ext a b
      rw [bp_apply, Matrix.map_apply, Matrix.single_apply, Matrix.single_apply]
      by_cases h : i = a ∧ i = b
      · rw [if_pos h, if_pos h, if_pos (by rw [← h.1, ← h.2]), map_one]
      · simp [h]
    refine (geAlg 𝔞.K (mapRep 𝔞.toK (bpRep hs r hT)) (fun g => 𝔞.toK (𝔞.a c (D.th g))) (fun g => ?_) he).2.2.2.2.2 ?_ ?_
      fun g i j h => ?_
    · ext a b
      have := congrArg 𝔞.toK (congrFun (congrFun (hm g) a) b)
      simp only [Matrix.mul_apply, adj_apply, map_sum, map_mul, map_zsmul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at this ⊢
      rw [apply_ite 𝔞.toK, map_one, map_zero] at this
      exact this
    · obtain ⟨g, hg⟩ := h02
      exact ⟨g, fun e => hg (𝔞.V.subtype_injective (e.trans (map_zero _).symm))⟩
    · obtain ⟨g, hg⟩ := h20
      exact ⟨g, fun e => hg (𝔞.V.subtype_injective (e.trans (map_zero _).symm))⟩
    · rw [mapRep_apply, hb g i j h, map_zero]
