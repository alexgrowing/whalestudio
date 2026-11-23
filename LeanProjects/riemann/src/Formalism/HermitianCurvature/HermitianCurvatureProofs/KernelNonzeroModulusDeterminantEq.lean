import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5

namespace Formalism.FourierDecayAlt.P.A5x5

section Index

variable {V W : Type} [AddCommGroup V] [AddCommGroup W]

def gi (A B : AddSubgroup V) : ℝ := (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

theorem gi_self (A : AddSubgroup V) : gi A A = 1 := by
  simp [gi]

theorem gi_of_le {A B D : AddSubgroup V} (hA : D ≤ A) (hB : D ≤ B) (hDA : D.relIndex A ≠ 0)
    (hDB : D.relIndex B ≠ 0) : gi A B = (D.relIndex A : ℝ) / (D.relIndex B : ℝ) := by
  have e1 : D.relIndex (A ⊓ B) * B.relIndex A = D.relIndex A := by
    have h := AddSubgroup.relIndex_inf_mul_relIndex (H := D) (K := B) (L := A)
    rw [inf_eq_left.mpr hB, inf_comm] at h
    exact h
  have e2 : D.relIndex (A ⊓ B) * A.relIndex B = D.relIndex B := by
    have h := AddSubgroup.relIndex_inf_mul_relIndex (H := D) (K := A) (L := B)
    rw [inf_eq_left.mpr hA] at h
    exact h
  have hc : D.relIndex (A ⊓ B) ≠ 0 := fun h0 => hDA (by rw [← e1, h0, zero_mul])
  unfold gi
  rw [← e1, ← e2]
  push_cast
  rw [mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hc)]

theorem gi_map {f : V →+ W} (hf : Function.Injective f) (A B : AddSubgroup V) :
    gi (A.map f) (B.map f) = gi A B := by
  unfold gi
  rw [← AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_comap,
    AddSubgroup.comap_map_eq_self_of_injective hf, AddSubgroup.comap_map_eq_self_of_injective hf]

private theorem relIndex_eq_of_mem_iff {H H' K : AddSubgroup V} (h : ∀ v ∈ K, v ∈ H ↔ v ∈ H') :
    H.relIndex K = H'.relIndex K := by
  have e : H.addSubgroupOf K = H'.addSubgroupOf K := by
    ext x
    simp only [AddSubgroup.mem_addSubgroupOf]
    exact h x x.2
  unfold AddSubgroup.relIndex
  rw [e]

theorem gi_comap (f : V →+ W) (A L : AddSubgroup V) (A' L' : AddSubgroup W)
    (h1 : ∀ v ∈ L, v ∈ A ↔ f v ∈ A') (h2 : ∀ v ∈ A, v ∈ L ↔ f v ∈ L')
    (h3 : L.map f = L') (h4 : A.map f = A') : gi A L = gi A' L' := by
  subst h3 h4
  unfold gi
  rw [← AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_comap]
  have k1 : ((L.map f).comap f).relIndex A = L.relIndex A :=
    relIndex_eq_of_mem_iff fun v hv => by rw [AddSubgroup.mem_comap, h2 v hv]
  have k2 : ((A.map f).comap f).relIndex L = A.relIndex L :=
    relIndex_eq_of_mem_iff fun v hv => by rw [AddSubgroup.mem_comap, h1 v hv]
  rw [k1, k2]

variable [TopologicalSpace V] [IsTopologicalAddGroup V]

structure Lat (A : AddSubgroup V) : Prop where
  op : IsOpen (A : Set V)
  cp : IsCompact (A : Set V)

theorem relIndex_ne_zero {U A : AddSubgroup V} (hU : IsOpen (U : Set V))
    (hA : IsCompact (A : Set V)) : U.relIndex A ≠ 0 := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have ho : IsOpen ((U.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hU.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen (U.addSubgroupOf A) ho
  exact AddSubgroup.index_ne_zero_of_finite

theorem gi_pos {A B : AddSubgroup V} (hA : Lat A) (hB : Lat B) : 0 < gi A B := by
  unfold gi
  have h1 : B.relIndex A ≠ 0 := relIndex_ne_zero hB.op hA.cp
  have h2 : A.relIndex B ≠ 0 := relIndex_ne_zero hA.op hB.cp
  exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h1)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h2))

theorem gi_trans {A B C : AddSubgroup V} (hA : Lat A) (hB : Lat B) (hC : Lat C) :
    gi A B * gi B C = gi A C := by
  have hD : IsOpen ((A ⊓ B ⊓ C : AddSubgroup V) : Set V) := by
    simp only [AddSubgroup.coe_inf]
    exact (hA.op.inter hB.op).inter hC.op
  rw [gi_of_le (D := A ⊓ B ⊓ C) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      (relIndex_ne_zero hD hA.cp) (relIndex_ne_zero hD hB.cp),
    gi_of_le (D := A ⊓ B ⊓ C) (inf_le_left.trans inf_le_right) inf_le_right
      (relIndex_ne_zero hD hB.cp) (relIndex_ne_zero hD hC.cp),
    gi_of_le (D := A ⊓ B ⊓ C) (inf_le_left.trans inf_le_left) inf_le_right
      (relIndex_ne_zero hD hA.cp) (relIndex_ne_zero hD hC.cp)]
  have hb : ((A ⊓ B ⊓ C).relIndex B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (relIndex_ne_zero hD hB.cp)
  rw [div_mul_div_comm, mul_comm ((A ⊓ B ⊓ C).relIndex B : ℝ), mul_div_mul_right _ _ hb]

end Index

section Mod

variable {K : Type} [CommRing K] {R : Subring K}

theorem modK_eq (x : K) : modK R x = gi (mulR R x) R.toAddSubgroup := rfl

theorem modK_one : modK R (1 : K) = 1 := by
  have h : mulR R (1 : K) = R.toAddSubgroup := by
    ext x
    simp [mulR]
  rw [modK_eq, h, gi_self]

theorem modK_neg (x : K) : modK R (-x) = modK R x := by
  have h : mulR R (-x) = mulR R x := by
    ext y
    simp only [mulR, AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨-r, R.neg_mem hr, by ring⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨-r, R.neg_mem hr, by ring⟩
  simp only [modK_eq, h]

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem lat_R (ho : IsOpen (R : Set K)) (hc : IsCompact (R : Set K)) : Lat R.toAddSubgroup := ⟨ho, hc⟩

theorem lat_mulR (ho : IsOpen (R : Set K)) (hc : IsCompact (R : Set K)) (x : Kˣ) :
    Lat (mulR R (x : K)) := by
  constructor
  · have h : ((mulR R (x : K)) : Set K) = (fun y => ((x⁻¹ : Kˣ) : K) * y) ⁻¹' (R : Set K) := by
      ext y
      simp only [mulR, AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        AddMonoidHom.coe_mulLeft, Subring.coe_toAddSubgroup]
      constructor
      · rintro ⟨r, hr, rfl⟩
        simpa using hr
      · intro hy
        exact ⟨_, hy, by simp⟩
    rw [h]
    exact ho.preimage (continuous_mul_left _)
  · have h : ((mulR R (x : K)) : Set K) = (fun y => (x : K) * y) '' (R : Set K) := by
      ext y
      simp [mulR]
    rw [h]
    exact hc.image (continuous_mul_left _)

theorem modK_pos (ho : IsOpen (R : Set K)) (hc : IsCompact (R : Set K)) (x : Kˣ) :
    0 < modK R (x : K) := by
  rw [modK_eq]
  exact gi_pos (lat_mulR ho hc x) (lat_R ho hc)

theorem modK_mul (ho : IsOpen (R : Set K)) (hc : IsCompact (R : Set K)) (x y : Kˣ) :
    modK R ((x : K) * (y : K)) = modK R (x : K) * modK R (y : K) := by
  have hf : Function.Injective (AddMonoidHom.mulLeft (x : K)) := fun a b h =>
    (Units.mul_right_inj x).mp h
  have e1 : (mulR R (y : K)).map (AddMonoidHom.mulLeft (x : K)) = mulR R ((x : K) * (y : K)) := by
    ext z
    simp [mulR, mul_assoc]
  have h1 := gi_trans (lat_mulR ho hc (x * y)) (lat_mulR ho hc x) (lat_R ho hc)
  rw [Units.val_mul] at h1
  have h2 : gi (mulR R ((x : K) * (y : K))) (mulR R (x : K)) = gi (mulR R (y : K)) R.toAddSubgroup := by
    rw [← e1, show mulR R (x : K) = R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : K)) from rfl,
      gi_map hf]
  simp only [modK_eq]
  rw [← h1, h2, mul_comm]

end Mod

section Mat

variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}

def mv (M : Matrix ι ι K) : (ι → K) →+ (ι → K) := M.mulVecLin.toAddMonoidHom

@[simp] theorem mv_apply (M : Matrix ι ι K) (v : ι → K) : mv M v = M *ᵥ v := rfl

def LL (R : Subring K) (ι : Type) : AddSubgroup (ι → K) :=
  AddSubgroup.pi Set.univ (fun _ => R.toAddSubgroup)

theorem mem_LL {v : ι → K} : v ∈ LL R ι ↔ ∀ i, v i ∈ R := by
  simp [LL, AddSubgroup.mem_pi]

def dl (R : Subring K) (M : Matrix ι ι K) : ℝ := gi ((LL R ι).map (mv M)) (LL R ι)

theorem mv_injective {M : Matrix ι ι K} (h : IsUnit M.det) : Function.Injective (mv M) := by
  intro v w hvw
  have h' : M *ᵥ v = M *ᵥ w := by simpa using hvw
  have h'' := congrArg (fun u => M⁻¹ *ᵥ u) h'
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h] using h''

theorem map_mv_mul (M N : Matrix ι ι K) (A : AddSubgroup (ι → K)) :
    A.map (mv (M * N)) = (A.map (mv N)).map (mv M) := by
  rw [AddSubgroup.map_map]
  congr 1
  refine AddMonoidHom.ext fun v => ?_
  simp [Matrix.mulVec_mulVec]

theorem map_le_of_int {M : Matrix ι ι K} (hM : ∀ i j, M i j ∈ R) :
    (LL R ι).map (mv M) ≤ LL R ι := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := AddSubgroup.mem_map.mp hx
  rw [mem_LL] at hv ⊢
  intro i
  simp only [mv_apply, Matrix.mulVec, dotProduct]
  exact R.sum_mem fun j _ => R.mul_mem (hM i j) (hv j)

theorem dl_eq_one {M N : Matrix ι ι K} (hMN : M * N = 1) (hM : ∀ i j, M i j ∈ R)
    (hN : ∀ i j, N i j ∈ R) : dl R M = 1 := by
  have h1 := map_le_of_int (ι := ι) hM
  have h2 : LL R ι ≤ (LL R ι).map (mv M) := by
    intro v hv
    refine AddSubgroup.mem_map.mpr ⟨N *ᵥ v, ?_, ?_⟩
    · exact map_le_of_int hN (AddSubgroup.mem_map.mpr ⟨v, hv, rfl⟩)
    · simp [Matrix.mulVec_mulVec, hMN]
  unfold dl
  rw [le_antisymm h1 h2, gi_self]

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem lat_LL (ho : IsOpen (R : Set K)) (hc : IsCompact (R : Set K)) : Lat (LL R ι) := by
  have e : ((LL R ι : AddSubgroup (ι → K)) : Set (ι → K)) = Set.pi Set.univ (fun _ => (R : Set K)) := by
    ext v
    simp [mem_LL]
  constructor
  · rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => ho
  · rw [e]
    exact isCompact_univ_pi fun _ => hc

theorem lat_map {M : Matrix ι ι K} (h : IsUnit M.det) {A : AddSubgroup (ι → K)} (hA : Lat A) :
    Lat (A.map (mv M)) := by
  have ht : ((A.map (mv M) : AddSubgroup (ι → K)) : Set (ι → K)) =
      (fun v => M⁻¹ *ᵥ v) ⁻¹' (A : Set (ι → K)) := by
    ext v
    simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe, mv_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h] using hu
    · intro hv
      exact ⟨_, hv, by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h]⟩
  have hi : ((A.map (mv M) : AddSubgroup (ι → K)) : Set (ι → K)) =
      (fun v => M *ᵥ v) '' (A : Set (ι → K)) := by
    ext v
    simp [mv_apply]
  constructor
  · rw [ht]
    exact hA.op.preimage (continuous_const.matrix_mulVec continuous_id)
  · rw [hi]
    exact hA.cp.image (continuous_const.matrix_mulVec continuous_id)

theorem dl_mul (hL : Lat (LL R ι)) {M N : Matrix ι ι K} (hM : IsUnit M.det) (hN : IsUnit N.det) :
    dl R (M * N) = dl R M * dl R N := by
  unfold dl
  rw [map_mv_mul, ← gi_trans (lat_map hM (lat_map hN hL)) (lat_map hM hL) hL,
    gi_map (mv_injective hM), mul_comm]

theorem dl_pos (hL : Lat (LL R ι)) {M : Matrix ι ι K} (hM : IsUnit M.det) : 0 < dl R M := by
  unfold dl
  exact gi_pos (lat_map hM hL) hL

end Mat

section Block

variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}

def resL : (ι ⊕ Unit → K) →+ (ι → K) where
  toFun v i := v (Sum.inl i)
  map_zero' := rfl
  map_add' _ _ := rfl

def evR : (ι ⊕ Unit → K) →+ K where
  toFun v := v (Sum.inr ())
  map_zero' := rfl
  map_add' _ _ := rfl

theorem blockL_mulVec (S : Matrix ι ι K) (w : ι ⊕ Unit → K) :
    fromBlocks S 0 0 (1 : Matrix Unit Unit K) *ᵥ w =
      Sum.elim (S *ᵥ (w ∘ Sum.inl)) (w ∘ Sum.inr) := by
  simp [Matrix.fromBlocks_mulVec]

theorem blockR_mulVec (D : Matrix Unit Unit K) (w : ι ⊕ Unit → K) :
    fromBlocks (1 : Matrix ι ι K) 0 0 D *ᵥ w =
      Sum.elim (w ∘ Sum.inl) (fun _ => D () () * w (Sum.inr ())) := by
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  congr 1
  funext u
  cases u
  simp [Matrix.mulVec, dotProduct]

theorem dl_blockL (S : Matrix ι ι K) :
    dl R (fromBlocks S 0 0 (1 : Matrix Unit Unit K)) = dl R S := by
  unfold dl
  have hB : ∀ w : ι ⊕ Unit → K, mv (fromBlocks S 0 0 (1 : Matrix Unit Unit K)) w =
      Sum.elim (S *ᵥ (w ∘ Sum.inl)) (w ∘ Sum.inr) := fun w => by
    rw [mv_apply, blockL_mulVec]
  have hres : ∀ w : ι ⊕ Unit → K, resL w = w ∘ Sum.inl := fun w => rfl
  refine gi_comap resL _ _ _ _ ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_LL] at hv
    constructor
    · intro hA
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hA
      refine AddSubgroup.mem_map.mpr ⟨x ∘ Sum.inl, ?_, ?_⟩
      · rw [mem_LL] at hx ⊢
        intro i
        exact hx (Sum.inl i)
      · rw [hres, hB, Sum.elim_comp_inl, mv_apply]
    · intro hA
      obtain ⟨y, hy, hyv⟩ := AddSubgroup.mem_map.mp hA
      refine AddSubgroup.mem_map.mpr ⟨Sum.elim y (v ∘ Sum.inr), ?_, ?_⟩
      · rw [mem_LL] at hy ⊢
        rintro (i | u)
        · exact hy i
        · exact hv (Sum.inr u)
      · rw [hB]
        funext j
        rcases j with i | u
        · have h := congrFun hyv i
          rw [mv_apply, hres] at h
          simpa using h
        · rfl
  · intro v hA
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hA
    constructor
    · intro h
      rw [mem_LL] at h ⊢
      intro i
      exact h (Sum.inl i)
    · intro h
      rw [mem_LL] at h hx ⊢
      rintro (i | u)
      · exact h i
      · rw [hB]
        exact hx (Sum.inr u)
  · ext u
    constructor
    · intro hu
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hu
      rw [mem_LL] at hw ⊢
      intro i
      exact hw (Sum.inl i)
    · intro hu
      refine AddSubgroup.mem_map.mpr ⟨Sum.elim u 0, ?_, rfl⟩
      rw [mem_LL] at hu ⊢
      rintro (i | j)
      · exact hu i
      · exact R.zero_mem
  · ext u
    constructor
    · intro hu
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hu
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hw
      refine AddSubgroup.mem_map.mpr ⟨x ∘ Sum.inl, ?_, ?_⟩
      · rw [mem_LL] at hx ⊢
        intro i
        exact hx (Sum.inl i)
      · rw [hres, hB, Sum.elim_comp_inl, mv_apply]
    · intro hu
      obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hu
      refine AddSubgroup.mem_map.mpr
        ⟨mv (fromBlocks S 0 0 (1 : Matrix Unit Unit K)) (Sum.elim y 0),
          AddSubgroup.mem_map.mpr ⟨Sum.elim y 0, ?_, rfl⟩, ?_⟩
      · rw [mem_LL] at hy ⊢
        rintro (i | j)
        · exact hy i
        · exact R.zero_mem
      · rw [hres, hB, Sum.elim_comp_inl, Sum.elim_comp_inl, mv_apply]

theorem dl_blockR (D : Matrix Unit Unit K) :
    dl R (fromBlocks (1 : Matrix ι ι K) 0 0 D) = modK R (D () ()) := by
  unfold dl
  rw [modK_eq]
  have hB : ∀ w : ι ⊕ Unit → K, mv (fromBlocks (1 : Matrix ι ι K) 0 0 D) w =
      Sum.elim (w ∘ Sum.inl) (fun _ => D () () * w (Sum.inr ())) := fun w => by
    rw [mv_apply, blockR_mulVec]
  have hev : ∀ w : ι ⊕ Unit → K, evR w = w (Sum.inr ()) := fun w => rfl
  refine gi_comap evR _ _ _ _ ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_LL] at hv
    constructor
    · intro hA
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hA
      rw [hev, hB]
      exact AddSubgroup.mem_map.mpr ⟨x (Sum.inr ()), mem_LL.mp hx _, rfl⟩
    · intro hA
      obtain ⟨r, hr, hrv⟩ := AddSubgroup.mem_map.mp hA
      refine AddSubgroup.mem_map.mpr ⟨Sum.elim (v ∘ Sum.inl) (fun _ => r), ?_, ?_⟩
      · rw [mem_LL]
        rintro (i | u)
        · exact hv _
        · exact hr
      · rw [hB]
        funext j
        rcases j with i | u
        · rfl
        · exact hrv
  · intro v hA
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hA
    constructor
    · intro h
      exact (mem_LL.mp h) (Sum.inr ())
    · intro h
      rw [mem_LL]
      rintro (i | u)
      · rw [hB]
        exact mem_LL.mp hx (Sum.inl i)
      · exact h
  · ext r
    constructor
    · intro hr
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hr
      exact mem_LL.mp hw (Sum.inr ())
    · intro hr
      exact AddSubgroup.mem_map.mpr ⟨fun _ => r, mem_LL.mpr fun _ => hr, rfl⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hw
      exact AddSubgroup.mem_map.mpr ⟨x (Sum.inr ()), mem_LL.mp hx _, by rw [hev, hB] <;> rfl⟩
    · intro hz
      obtain ⟨r, hr, rfl⟩ := AddSubgroup.mem_map.mp hz
      exact AddSubgroup.mem_map.mpr ⟨mv (fromBlocks (1 : Matrix ι ι K) 0 0 D) (fun _ => r),
        AddSubgroup.mem_map.mpr ⟨fun _ => r, mem_LL.mpr fun _ => hr, rfl⟩, by rw [hev, hB] <;> rfl⟩

theorem dl_reindex (e : ι ≃ κ) (M : Matrix ι ι K) : dl R (reindex e e M) = dl R M := by
  unfold dl
  let f : (ι → K) →+ (κ → K) :=
    { toFun := fun u => u ∘ e.symm, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hf_apply : ∀ u, f u = u ∘ e.symm := fun u => rfl
  have hf : Function.Injective f := fun a b h => by
    funext i
    have := congrFun h (e i)
    simpa [hf_apply] using this
  have hL : (LL R ι).map f = LL R κ := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hv
      rw [mem_LL] at hu ⊢
      intro k
      rw [hf_apply]
      exact hu _
    · intro hv
      refine AddSubgroup.mem_map.mpr ⟨v ∘ e, ?_, ?_⟩
      · rw [mem_LL] at hv ⊢
        intro i
        exact hv _
      · rw [hf_apply]
        funext k
        simp
  have hM : ((LL R ι).map (mv M)).map f = (LL R κ).map (mv (reindex e e M)) := by
    rw [← hL, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    refine AddMonoidHom.ext fun u => ?_
    simp only [AddMonoidHom.comp_apply, mv_apply, hf_apply]
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv] <;> simp [Function.comp_assoc]
  rw [← hM, ← hL, gi_map hf]

end Block

section Elim

variable {K : Type} [CommRing K]

theorem sr1 [IsArtinianRing K] [IsReduced K] (a b x : K) (h : a * x + b = 1) :
    ∃ c, IsUnit (a + c * b) := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : K)
  have hy' : a ^ (n + 1) * y = a ^ n := by simpa using hy
  have hz : a * a * y = a := by
    have h1 : a ^ n * (a * (1 - a * y)) = 0 := by
      have e : a ^ n * (a * (1 - a * y)) = a ^ (n + 1) - a * (a ^ (n + 1) * y) := by ring
      rw [e, hy']
      ring
    have h2 : (a * (1 - a * y)) ^ (n + 1) = 0 := by
      have e : (a * (1 - a * y)) ^ (n + 1) = a ^ n * (a * (1 - a * y)) * (1 - a * y) ^ n := by
        rw [mul_pow, pow_succ, pow_succ]
        ring
      rw [e, h1, zero_mul]
    have h3 : a * (1 - a * y) = 0 := IsReduced.eq_zero _ ⟨n + 1, h2⟩
    linear_combination (-1 : K) * h3
  refine ⟨1 - a * y, ?_⟩
  have key : a + (1 - a * y) * b = a + 1 - a * y := by
    have hb : b = 1 - a * x := by linear_combination h
    rw [hb]
    linear_combination x * hz
  rw [key]
  exact ⟨⟨a + 1 - a * y, a * y * y + 1 - a * y, by linear_combination (2 * y - y ^ 2 - 1) * hz,
    by linear_combination (2 * y - y ^ 2 - 1) * hz⟩, rfl⟩

theorem exists_pow_mem {R : Subring K} {ϖ : K} (hϖ : ϖ ∈ R) (h : ∀ x : K, ∃ m : ℕ, ϖ ^ m * x ∈ R)
    {α : Type} [Fintype α] (f : α → K) : ∃ m : ℕ, ∀ a, ϖ ^ m * f a ∈ R := by
  choose g hg using fun a => h (f a)
  refine ⟨∑ a, g a, fun a => ?_⟩
  have hle : g a ≤ ∑ b, g b := Finset.single_le_sum (fun b _ => Nat.zero_le (g b)) (Finset.mem_univ a)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, pow_add, mul_comm (ϖ ^ g a) (ϖ ^ k), mul_assoc]
  exact R.mul_mem (R.pow_mem hϖ k) (hg a)

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}

theorem int_lower {s : Matrix Unit ι K} (hs : ∀ i, s () i ∈ R) (a b : ι ⊕ Unit) :
    (fromBlocks (1 : Matrix ι ι K) 0 s (1 : Matrix Unit Unit K)) a b ∈ R := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply] <;>
    (try split_ifs) <;>
    first | exact R.one_mem | exact R.zero_mem | exact hs _

theorem int_upper {s : Matrix ι Unit K} (hs : ∀ i, s i () ∈ R) (a b : ι ⊕ Unit) :
    (fromBlocks (1 : Matrix ι ι K) s 0 (1 : Matrix Unit Unit K)) a b ∈ R := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply] <;>
    (try split_ifs) <;>
    first | exact R.one_mem | exact R.zero_mem | exact hs _

variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}

theorem modK_mul' (hd : LocalDatum K R ψ) {x y : K} (hx : IsUnit x) (hy : IsUnit y) :
    modK R (x * y) = modK R x * modK R y := by
  have := modK_mul hd.isOpen hd.isCompact hx.unit hy.unit
  simpa using this

theorem dl_lower (hd : LocalDatum K R ψ) (r : Matrix Unit ι K) :
    dl R (fromBlocks (1 : Matrix ι ι K) 0 r (1 : Matrix Unit Unit K)) = 1 := by
  obtain ⟨ϖ, hϖR, hϖ⟩ := hd.unif
  obtain ⟨m, hm⟩ := exists_pow_mem hϖR hϖ (fun i => r () i)
  have hL : Lat (LL R (ι ⊕ Unit)) := lat_LL hd.isOpen hd.isCompact
  set u : Kˣ := ϖ ^ m with hu
  set D : Matrix Unit Unit K := Matrix.diagonal fun _ => (u : K) with hD
  set Di : Matrix Unit Unit K := Matrix.diagonal fun _ => ((u⁻¹ : Kˣ) : K) with hDi
  have hDD : Di * D = 1 := by
    rw [hD, hDi, Matrix.diagonal_mul_diagonal]
    simp
  set s : Matrix Unit ι K := D * r with hs_def
  have hs : ∀ i, s () i ∈ R := by
    intro i
    rw [hs_def, hD, Matrix.diagonal_mul]
    simpa [hu] using hm i
  have hfac : fromBlocks (1 : Matrix ι ι K) 0 r (1 : Matrix Unit Unit K) =
      fromBlocks (1 : Matrix ι ι K) 0 0 Di * fromBlocks (1 : Matrix ι ι K) 0 s 1 *
        fromBlocks (1 : Matrix ι ι K) 0 0 D := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
    rw [hs_def, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
  have hdet1 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 Di).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, hDi, Matrix.det_diagonal]
    simp
  have hdet2 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 s (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    simp
  have hdet3 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 D).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, hD, Matrix.det_diagonal]
    simp
  have h12 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 Di *
      fromBlocks (1 : Matrix ι ι K) 0 s (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_mul]
    exact hdet1.mul hdet2
  have hone : dl R (fromBlocks (1 : Matrix ι ι K) 0 s (1 : Matrix Unit Unit K)) = 1 :=
    dl_eq_one (N := fromBlocks (1 : Matrix ι ι K) 0 (-s) 1)
      (by rw [Matrix.fromBlocks_multiply]; simp) (int_lower hs)
      (int_lower fun i => by simpa using R.neg_mem (hs i))
  rw [hfac, dl_mul hL h12 hdet3, dl_mul hL hdet1 hdet2, hone, dl_blockR, dl_blockR, mul_one, hDi, hD]
  simp only [Matrix.diagonal_apply_eq]
  rw [← modK_mul' hd (Units.isUnit _) (Units.isUnit _)]
  simp [modK_one]

theorem dl_upper (hd : LocalDatum K R ψ) (r : Matrix ι Unit K) :
    dl R (fromBlocks (1 : Matrix ι ι K) r 0 (1 : Matrix Unit Unit K)) = 1 := by
  obtain ⟨ϖ, hϖR, hϖ⟩ := hd.unif
  obtain ⟨m, hm⟩ := exists_pow_mem hϖR hϖ (fun i => r i ())
  have hL : Lat (LL R (ι ⊕ Unit)) := lat_LL hd.isOpen hd.isCompact
  set u : Kˣ := ϖ ^ m with hu
  set D : Matrix Unit Unit K := Matrix.diagonal fun _ => (u : K) with hD
  set Di : Matrix Unit Unit K := Matrix.diagonal fun _ => ((u⁻¹ : Kˣ) : K) with hDi
  have hDD : D * Di = 1 := by
    rw [hD, hDi, Matrix.diagonal_mul_diagonal]
    simp
  set s : Matrix ι Unit K := r * D with hs_def
  have hs : ∀ i, s i () ∈ R := by
    intro i
    rw [hs_def, hD, Matrix.mul_diagonal, mul_comm]
    simpa [hu] using hm i
  have hfac : fromBlocks (1 : Matrix ι ι K) r 0 (1 : Matrix Unit Unit K) =
      fromBlocks (1 : Matrix ι ι K) 0 0 D * fromBlocks (1 : Matrix ι ι K) s 0 1 *
        fromBlocks (1 : Matrix ι ι K) 0 0 Di := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
    rw [hs_def, Matrix.mul_assoc, hDD, Matrix.mul_one]
  have hdet1 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 D).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, hD, Matrix.det_diagonal]
    simp
  have hdet2 : IsUnit (fromBlocks (1 : Matrix ι ι K) s 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp
  have hdet3 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 Di).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, hDi, Matrix.det_diagonal]
    simp
  have h12 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 D *
      fromBlocks (1 : Matrix ι ι K) s 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_mul]
    exact hdet1.mul hdet2
  have hone : dl R (fromBlocks (1 : Matrix ι ι K) s 0 (1 : Matrix Unit Unit K)) = 1 :=
    dl_eq_one (N := fromBlocks (1 : Matrix ι ι K) (-s) 0 1)
      (by rw [Matrix.fromBlocks_multiply]; simp) (int_upper hs)
      (int_upper fun i => by simpa using R.neg_mem (hs i))
  rw [hfac, dl_mul hL h12 hdet3, dl_mul hL hdet1 hdet2, hone, dl_blockR, dl_blockR, mul_one, hDi, hD]
  simp only [Matrix.diagonal_apply_eq]
  rw [← modK_mul' hd (Units.isUnit _) (Units.isUnit _)]
  simp [modK_one]

def Good (R : Subring K) (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ M : Matrix ι ι K, IsUnit M.det → dl R M = modK R M.det

theorem good_corner (hd : LocalDatum K R ψ) (hG : Good R ι) (M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K)
    (hM : IsUnit M.det) (hc : IsUnit (M (Sum.inr ()) (Sum.inr ()))) : dl R M = modK R M.det := by
  have hL : Lat (LL R (ι ⊕ Unit)) := lat_LL hd.isOpen hd.isCompact
  set A := M.toBlocks₁₁ with hA
  set B := M.toBlocks₁₂ with hB
  set C := M.toBlocks₂₁ with hC
  set D := M.toBlocks₂₂ with hD
  have hDd : D.det = D () () := Matrix.det_unique D
  have hc1 : IsUnit (D () ()) := hc
  have hDdet : IsUnit D.det := by rw [hDd]; exact hc1
  letI := Matrix.invertibleOfIsUnitDet D hDdet
  have hMeq : M = fromBlocks A B C D := (Matrix.fromBlocks_toBlocks M).symm
  have hfac := Matrix.fromBlocks_eq_of_invertible₂₂ A B C D
  have hdet := Matrix.det_fromBlocks₂₂ A B C D
  rw [← hMeq] at hfac hdet
  set S := A - B * ⅟D * C with hS
  have hSdet : IsUnit S.det := by
    have h : IsUnit (D.det * S.det) := hdet ▸ hM
    exact isUnit_of_mul_isUnit_right h
  have hU : IsUnit (fromBlocks (1 : Matrix ι ι K) (B * ⅟D) 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp
  have hLw : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 (⅟D * C) (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    simp
  have hDg : IsUnit (fromBlocks S 0 0 D).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    exact hSdet.mul hDdet
  have hDg' : fromBlocks S 0 0 D =
      fromBlocks S 0 0 (1 : Matrix Unit Unit K) * fromBlocks (1 : Matrix ι ι K) 0 0 D := by
    rw [Matrix.fromBlocks_multiply]
    simp
  have hS1 : IsUnit (fromBlocks S 0 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simpa using hSdet
  have hD1 : IsUnit (fromBlocks (1 : Matrix ι ι K) 0 0 D).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simpa using hDdet
  have hUD : IsUnit (fromBlocks (1 : Matrix ι ι K) (B * ⅟D) 0 (1 : Matrix Unit Unit K) *
      fromBlocks S 0 0 D).det := by
    rw [Matrix.det_mul]
    exact hU.mul hDg
  conv_lhs => rw [hfac]
  rw [dl_mul hL hUD hLw, dl_mul hL hU hDg, dl_upper hd, dl_lower hd, hDg', dl_mul hL hS1 hD1,
    dl_blockL, dl_blockR, hG S hSdet, hdet, one_mul, mul_one, hDd, modK_mul' hd hc1 hSdet, mul_comm]

theorem good_step (hd : LocalDatum K R ψ) (hG : Good R ι) : Good R (ι ⊕ Unit) := by
  intro M hM
  haveI := hd.artin
  haveI := hd.red
  have hL : Lat (LL R (ι ⊕ Unit)) := lat_LL hd.isOpen hd.isCompact
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hrow : (∑ i : ι, M (Sum.inr ()) (Sum.inl i) * M⁻¹ (Sum.inl i) (Sum.inr ())) +
      M (Sum.inr ()) (Sum.inr ()) * M⁻¹ (Sum.inr ()) (Sum.inr ()) = 1 := by
    have h := congrFun (congrFun hinv (Sum.inr ())) (Sum.inr ())
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h
    simpa using h
  obtain ⟨c', hc'⟩ := sr1 (M (Sum.inr ()) (Sum.inr ()))
    (∑ i : ι, M (Sum.inr ()) (Sum.inl i) * M⁻¹ (Sum.inl i) (Sum.inr ()))
    (M⁻¹ (Sum.inr ()) (Sum.inr ())) (by rw [add_comm]; exact hrow)
  set q : Matrix ι Unit K := fun i _ => c' * M⁻¹ (Sum.inl i) (Sum.inr ()) with hq
  have hE : IsUnit (fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp
  have hME : IsUnit (M * fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K)).det := by
    rw [Matrix.det_mul]
    exact hM.mul hE
  have hcorner : IsUnit ((M * fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K))
      (Sum.inr ()) (Sum.inr ())) := by
    have e : (M * fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K)) (Sum.inr ()) (Sum.inr ()) =
        M (Sum.inr ()) (Sum.inr ()) +
          c' * ∑ i : ι, M (Sum.inr ()) (Sum.inl i) * M⁻¹ (Sum.inl i) (Sum.inr ()) := by
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Finset.mul_sum]
      have h1 : ∑ u : Unit, M (Sum.inr ()) (Sum.inr u) *
          (fromBlocks (1 : Matrix ι ι K) q 0 (1 : Matrix Unit Unit K)) (Sum.inr u) (Sum.inr ()) =
          M (Sum.inr ()) (Sum.inr ()) := by
        simp
      rw [h1, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.fromBlocks_apply₁₂, hq]
      ring
    rw [e]
    exact hc'
  have key := good_corner hd hG _ hME hcorner
  rw [dl_mul hL hM hE, dl_upper hd, mul_one, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁] at key
  simpa using key

theorem good_equiv (e : ι ≃ κ) (hG : Good R ι) : Good R κ := by
  intro M hM
  have h1 : reindex e e (reindex e.symm e.symm M) = M := by
    ext i j
    simp
  have h2 : IsUnit (reindex e.symm e.symm M).det := by
    rwa [Matrix.det_reindex_self]
  rw [← h1, dl_reindex, hG _ h2]
  simp only [Matrix.det_reindex_self]

theorem good_fin (hd : LocalDatum K R ψ) : ∀ n : ℕ, Good R (Fin n)
  | 0 => by
    intro M _
    rw [det_isEmpty, modK_one]
    exact dl_eq_one (N := 1) (Subsingleton.elim _ _) (fun i => i.elim0) (fun i => i.elim0)
  | n + 1 =>
    good_equiv (Fintype.equivOfCardEq (by simp)) (good_step hd (good_fin hd n))

theorem cokernel_finite_card_eq_inv_modulus (hd : LocalDatum K R ψ) (n : ℕ) (Z : Matrix (Fin n) (Fin n) K)
    (hZ : IsInt R Z) (hdet : IsUnit Z.det) :
    Finite (coker R Z) ∧ (Nat.card (coker R Z) : ℝ) = (modK R Z.det)⁻¹ := by
  have hL := lat_LL (ι := Fin n) hd.isOpen hd.isCompact
  have hgood := good_fin hd n Z hdet
  have hle := map_le_of_int (ι := Fin n) (R := R) (M := Z) hZ
  set A := (LL R (Fin n)).map (mv Z) with hA
  have hne : A.relIndex (LL R (Fin n)) ≠ 0 := relIndex_ne_zero (lat_map hdet hL).op hL.cp
  have hone : (LL R (Fin n)).relIndex A = 1 := AddSubgroup.relIndex_eq_one.mpr hle
  have hdl : dl R Z = 1 / (A.relIndex (LL R (Fin n)) : ℝ) := by
    unfold dl
    rw [← hA]
    unfold gi
    rw [hone, Nat.cast_one]
  have hrange : (coeLin R : (Fin n → R) →ₗ[R] (Fin n → K)).toAddMonoidHom.range = LL R (Fin n) := by
    ext v
    constructor
    · intro hv
      obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hv
      rw [mem_LL]
      intro i
      exact (y i).2
    · intro hv
      rw [mem_LL] at hv
      exact AddMonoidHom.mem_range.mpr ⟨fun i => ⟨v i, hv i⟩, rfl⟩
  have hlat : (latZ R Z).toAddSubgroup =
      A.comap (coeLin R : (Fin n → R) →ₗ[R] (Fin n → K)).toAddMonoidHom := by
    ext x
    rw [Submodule.mem_toAddSubgroup, Formalism.DoubleCosetMeasures.P.mem_latZ, AddSubgroup.mem_comap, hA]
    constructor
    · rintro ⟨y, hy⟩
      exact AddSubgroup.mem_map.mpr ⟨coeLin R y, mem_LL.mpr fun i => (y i).2, hy⟩
    · intro hx
      obtain ⟨v, hv, hvx⟩ := AddSubgroup.mem_map.mp hx
      rw [mem_LL] at hv
      exact ⟨fun i => ⟨v i, hv i⟩, hvx⟩
  have hcard : Nat.card (coker R Z) = A.relIndex (LL R (Fin n)) := by
    have h : Nat.card (coker R Z) = (latZ R Z).toAddSubgroup.index := rfl
    rw [h, hlat, AddSubgroup.index_comap, hrange]
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne), ?_⟩
  rw [hcard, ← hgood, hdl, one_div, inv_inv]

end Elim

section Kern

variable {K : Type} [CommRing K] {R : Subring K}

theorem det_orbZ (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    (orbZ w p).det = (pt w.1 w.2).det := by
  obtain ⟨h1, -⟩ := p.1.2
  have h2 : IsUpUni ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := p.2.2
  unfold orbZ
  rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det _ h1, isUpUni_det _ h2, one_mul, mul_one]

theorem isUnit_det_pt (s : List ℕ) (t : ℕ → Kˣ) : IsUnit (pt s t).det := Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI s t)

theorem modK_det_pt (s : List ℕ) (t : ℕ → Kˣ) :
    modK R (pt s t).det = modK R (∏ a : Fin s.sum, ((t (blk s a) : Kˣ) : K)) := by
  set σ : Equiv.Perm (Fin s.sum) :=
    Function.Involutive.toPerm (Formalism.DoubleCosetMeasures.P.Phase.revF s)
      (show Function.Involutive (Formalism.DoubleCosetMeasures.P.Phase.revF s) from Formalism.DoubleCosetMeasures.P.Phase.revF_revF s) with hσ
  have hpt : pt s t = Matrix.diagonal (fun a : Fin s.sum => ((t (blk s a) : Kˣ) : K)) *
      (σ.toPEquiv.toMatrix : Matrix (Fin s.sum) (Fin s.sum) K) := by
    ext a b
    simp only [Formalism.DoubleCosetMeasures.pt, Matrix.diagonal_mul, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, hσ, Function.Involutive.coe_toPerm]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (Fin.ext (by simp only [Function.Involutive.coe_toPerm, Formalism.DoubleCosetMeasures.P.Phase.revF_val]; exact h1.symm)) h2
    · exact absurd (by rw [← h2]; simp only [Function.Involutive.coe_toPerm, Formalism.DoubleCosetMeasures.P.Phase.revF_val]) h1
    · simp
  rw [hpt, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp [modK_neg]

theorem blk_lt : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s j < s.length
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [blk, List.length_cons]
    split_ifs with hj
    · omega
    · have := blk_lt s (j - a) (by simp only [List.sum_cons] at h; omega)
      omega

theorem blk_append_lt : ∀ (s : List ℕ) (k j : ℕ), j < s.sum → blk (s ++ [k]) j = blk s j
  | [], k, j, h => by simp at h
  | a :: s, k, j, h => by
    simp only [List.cons_append, blk]
    split_ifs with hj
    · rfl
    · rw [blk_append_lt s k (j - a) (by simp only [List.sum_cons] at h; omega)]

theorem blk_append_ge : ∀ (s : List ℕ) (k j : ℕ), j < k → blk (s ++ [k]) (s.sum + j) = s.length
  | [], k, j, h => by simp [blk, h]
  | a :: s, k, j, h => by
    simp only [List.cons_append, blk, List.sum_cons, List.length_cons]
    rw [if_neg (by omega)]
    have : a + s.sum + j - a = s.sum + j := by omega
    rw [this, blk_append_ge s k j h]; omega

theorem prod_addBlock (h : Point K) (s : ℕ) (t : Kˣ) :
    (∏ a : Fin (addBlock h s t).1.sum,
      (((addBlock h s t).2 (blk (addBlock h s t).1 a) : Kˣ) : K)) =
      (∏ a : Fin h.1.sum, ((h.2 (blk h.1 a) : Kˣ) : K)) * (t : K) ^ s := by
  have e1 : (∏ a : Fin (addBlock h s t).1.sum,
      (((addBlock h s t).2 (blk (addBlock h s t).1 a) : Kˣ) : K)) =
      ∏ i ∈ Finset.range (addBlock h s t).1.sum,
        (((addBlock h s t).2 (blk (addBlock h s t).1 i) : Kˣ) : K) :=
    Fin.prod_univ_eq_prod_range (fun i => (((addBlock h s t).2 (blk (addBlock h s t).1 i) : Kˣ) : K)) _
  have e2 : (∏ a : Fin h.1.sum, ((h.2 (blk h.1 a) : Kˣ) : K)) =
      ∏ i ∈ Finset.range h.1.sum, ((h.2 (blk h.1 i) : Kˣ) : K) :=
    Fin.prod_univ_eq_prod_range (fun i => ((h.2 (blk h.1 i) : Kˣ) : K)) _
  rw [e1, e2]
  simp only [addBlock]
  rw [List.sum_append, List.sum_singleton, Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [blk_append_lt h.1 s i hi, Function.update_of_ne (blk_lt h.1 i hi).ne]
  · have e : ∀ j ∈ Finset.range s,
        (((Function.update h.2 h.1.length t) (blk (h.1 ++ [s]) (h.1.sum + j)) : Kˣ) : K) = (t : K) :=
      fun j hj => by
        rw [Finset.mem_range] at hj
        rw [blk_append_ge h.1 s j hj, Function.update_self]
    rw [Finset.prod_congr rfl e, Finset.prod_const, Finset.card_range]

theorem isUnit_prod {n : ℕ} (f : Fin n → Kˣ) : IsUnit (∏ a : Fin n, ((f a : Kˣ) : K)) := by
  rw [← Units.coe_prod]
  exact Units.isUnit _

variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}

theorem kernel_nonzero_modulus_determinant_eq (hd : LocalDatum K R ψ) (w w' : Point K) (h : Kp R ψ w w' ≠ 0) :
    modK R (pt w.1 w.2).det = modK R (pt w'.1 w'.2).det := by
  obtain ⟨q, hq⟩ : ∃ q, pairTerm R ψ w w' q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (finsum_eq_zero_of_forall_eq_zero hc)
  unfold pairTerm at hq
  by_cases hc : IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))
  swap
  · rw [if_neg hc, zero_mul, zero_mul] at hq
    exact absurd rfl hq
  rw [if_pos hc] at hq
  have hcard : Nat.card (isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2))) ≠ 0 := by
    intro h0
    apply hq
    rw [h0]
    simp
  obtain ⟨⟨φ, -⟩⟩ := (Nat.card_ne_zero.mp hcard).1
  have hZ : IsUnit (orbZ w (rep R q.1)).det := by
    rw [det_orbZ]
    exact isUnit_det_pt _ _
  have hZ' : IsUnit (orbZ w' (rep R q.2)).det := by
    rw [det_orbZ]
    exact isUnit_det_pt _ _
  have e1 := (cokernel_finite_card_eq_inv_modulus hd _ _ hc.1 hZ).2
  have e2 := (cokernel_finite_card_eq_inv_modulus hd _ _ hc.2 hZ').2
  have e3 : Nat.card (coker R (orbZ w (rep R q.1))) = Nat.card (coker R (orbZ w' (rep R q.2))) :=
    Nat.card_congr φ.toEquiv
  rw [e3, e2, det_orbZ, det_orbZ] at e1
  exact (inv_inj.mp e1).symm

theorem added_block_kernel_modulus_det_eq (hd : LocalDatum K R ψ) (h h' : Point K) (s : ℕ) (t : Kˣ)
    (hne : Ns R ψ s h h' t t ≠ 0) :
    modK R (pt h.1 h.2).det = modK R (pt h'.1 h'.2).det := by
  have hK : Kp R ψ (addBlock h s t) (addBlock h' s t) ≠ 0 := by
    intro h0
    apply hne
    unfold Ns
    rw [h0, mul_zero]
  have e := kernel_nonzero_modulus_determinant_eq hd _ _ hK
  rw [modK_det_pt, modK_det_pt, prod_addBlock, prod_addBlock] at e
  rw [modK_det_pt, modK_det_pt]
  have hu : IsUnit ((t : K) ^ s) := (Units.isUnit t).pow s
  rw [modK_mul' hd (isUnit_prod _) hu, modK_mul' hd (isUnit_prod _) hu] at e
  have hpos : 0 < modK R ((t : K) ^ s) := by
    have := modK_pos hd.isOpen hd.isCompact (t ^ s)
    simpa using this
  exact mul_right_cancel₀ hpos.ne' e

end Kern

end Formalism.FourierDecayAlt.P.A5x5

namespace Formalism.FourierDecayAlt.P

open A5x5

theorem modulus_positive_multiplicative : Formalism.FourierDecayAlt.A5.ModMul := by
  intro K _ _ _ R ψ hd x y
  exact ⟨modK_pos hd.isOpen hd.isCompact x, modK_mul hd.isOpen hd.isCompact x y⟩

theorem cokernel_card_inverse_modulus : Formalism.FourierDecayAlt.A5.CokerCard := by
  intro K _ _ _ R ψ hd n Z hZ hdet
  exact cokernel_finite_card_eq_inv_modulus hd n Z hZ hdet

theorem kernel_block_diagonal_by_modulus : Formalism.FourierDecayAlt.A5.KpBlockDiag := by
  intro K _ _ _ R ψ hd w w' h
  exact kernel_nonzero_modulus_determinant_eq hd w w' h

theorem added_block_kernel_block_diagonal : Formalism.FourierDecayAlt.A5.NsBlockDiag := by
  intro K _ _ _ R ψ hd h h' _
  exact ⟨fun h0 => kernel_nonzero_modulus_determinant_eq hd h h' h0, fun s t hne => added_block_kernel_modulus_det_eq hd h h' s t hne⟩

end Formalism.FourierDecayAlt.P
