import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.StepData
open GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k]

def IntM {m n : Type*} (M : Matrix m n k) : Prop := ∀ i j, M i j ∈ 𝒪[k]

def MaxM {m n : Type*} (M : Matrix m n k) : Prop := ∀ i j, valuation k (M i j) < 1

section Arith
variable {l m n : Type*}

theorem MaxM.intM {M : Matrix m n k} (h : MaxM M) : IntM M := fun i j => (h i j).le

theorem intM_zero : IntM (0 : Matrix m n k) := fun _ _ => zero_mem _

theorem maxM_zero : MaxM (0 : Matrix m n k) := fun _ _ => by simp

theorem intM_one [DecidableEq n] : IntM (1 : Matrix n n k) := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  exacts [one_mem _, zero_mem _]

theorem IntM.add {M M' : Matrix m n k} (h : IntM M) (h' : IntM M') : IntM (M + M') :=
  fun i j => add_mem (h i j) (h' i j)

theorem IntM.neg {M : Matrix m n k} (h : IntM M) : IntM (-M) := fun i j => neg_mem (h i j)

theorem MaxM.add {M M' : Matrix m n k} (h : MaxM M) (h' : MaxM M') : MaxM (M + M') :=
  fun i j => Valuation.map_add_lt _ (h i j) (h' i j)

theorem MaxM.neg {M : Matrix m n k} (h : MaxM M) : MaxM (-M) := fun i j => by
  simpa using h i j

theorem IntM.mul [Fintype m] {M : Matrix l m k} {M' : Matrix m n k} (h : IntM M) (h' : IntM M') :
    IntM (M * M') := fun i j => sum_mem fun s _ => mul_mem (h i s) (h' s j)

theorem IntM.mul_maxM [Fintype m] {M : Matrix l m k} {M' : Matrix m n k} (h : IntM M) (h' : MaxM M') :
    MaxM (M * M') := fun i j => by
  refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_right (h i s) zero_le (h' s j)

theorem MaxM.mul_intM [Fintype m] {M : Matrix l m k} {M' : Matrix m n k} (h : MaxM M) (h' : IntM M') :
    MaxM (M * M') := fun i j => by
  refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (h i s) (h' s j)

end Arith

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem mem_KO {g : GL n k} : g ∈ KO k n ↔ IntM g.val ∧ IntM (g⁻¹).val := SplitFlip.mem_KO_iff g

theorem intM_of_mem_KO {g : GL n k} (h : g ∈ KO k n) : IntM g.val := (mem_KO.1 h).1

theorem KOne_le_KO : KOne k n ≤ KO k n := SplitWeil.Model.KOne_le_KO n

theorem residue_eq_zero_iff_lt (x : 𝒪[k]) : IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem residue_eq_iff_lt (x y : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = IsLocalRing.residue 𝒪[k] y ↔ valuation k ((x : k) - y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_lt]; rfl

theorem exists_mem_KOne {M : Matrix n n k} (h : MaxM (M - 1)) : ∃ g ∈ KOne k n, g.val = M := by
  have hM : IntM M := by simpa using h.intM.add (intM_one (k := k) (n := n))
  let A : Matrix n n 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have hA : (IsLocalRing.residue 𝒪[k]).mapMatrix A = 1 := by
    ext i j
    have : (1 : Matrix n n (IsLocalRing.ResidueField 𝒪[k])) i j =
        IsLocalRing.residue 𝒪[k] ((1 : Matrix n n 𝒪[k]) i j) := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    rw [this]
    refine (residue_eq_iff_lt _ _).2 ?_
    convert h i j using 2
    simp only [Matrix.sub_apply, Matrix.one_apply, A]; split_ifs <;> simp
  have hd : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hA]; simp
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hd
  refine ⟨_, ⟨u, ?_, rfl⟩, ?_⟩
  · exact Units.ext (show (IsLocalRing.residue 𝒪[k]).mapMatrix u.val = 1 by rw [hu, hA])
  · change (algebraMap 𝒪[k] k).mapMatrix u.val = M
    rw [hu]; rfl

theorem mem_KOne {g : GL n k} : g ∈ KOne k n ↔ MaxM (g.val - 1) := by
  constructor
  · rintro ⟨u, hu, rfl⟩ i j
    have h1 : IsLocalRing.residue 𝒪[k] (u.val i j) = IsLocalRing.residue 𝒪[k] ((1 : Matrix n n 𝒪[k]) i j) := by
      have h0 : (IsLocalRing.residue 𝒪[k]).mapMatrix u.val = 1 := congrArg Units.val hu
      refine (congrFun (congrFun h0 i) j).trans ?_
      simp only [Matrix.one_apply]; split_ifs <;> simp
    convert (residue_eq_iff_lt _ _).1 h1 using 2
    simp only [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp <;> rfl
  · intro h
    obtain ⟨g', h1, h2⟩ := exists_mem_KOne h
    rwa [← Units.ext h2]

theorem det_of_mem_KOne {g : GL n k} (h : g ∈ KOne k n) :
    valuation k (((Matrix.GeneralLinearGroup.det g : kˣ) : k) - 1) < 1 := by
  obtain ⟨u, hu, rfl⟩ := h
  have h1 : IsLocalRing.residue 𝒪[k] u.val.det = IsLocalRing.residue 𝒪[k] 1 := by
    rw [RingHom.map_det, map_one]
    have : (IsLocalRing.residue 𝒪[k]).mapMatrix u.val = 1 := congrArg Units.val hu
    rw [this, det_one]
  convert (residue_eq_iff_lt _ _).1 h1 using 3
  · exact ((algebraMap 𝒪[k] k).map_det u.val).symm
  · rfl

theorem tame_det_of_mem_KOne {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {g : GL n k} (h : g ∈ KOne k n) :
    μ (Matrix.GeneralLinearGroup.det g) = 1 := hμ _ (det_of_mem_KOne h)

theorem valuation_det_of_mem_KO {g : GL n k} (h : g ∈ KO k n) :
    valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨u, rfl⟩ := h
  have hu : IsUnit u.val.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have := (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 hu
  convert this using 2
  exact ((algebraMap 𝒪[k] k).map_det u.val).symm

theorem exists_mul_KOne {g : GL n k} (hg : g ∈ KO k n) {M : Matrix n n k} (h : MaxM (M - g.val)) :
    ∃ u ∈ KOne k n, (g * u).val = M := by
  obtain ⟨u, hu, hu'⟩ := exists_mem_KOne (M := (g⁻¹).val * M) (by
    have := (mem_KO.1 hg).2.mul_maxM h
    rwa [Matrix.mul_sub, Units.inv_mul] at this)
  exact ⟨u, hu, by rw [Units.val_mul, hu', ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩

theorem inv_mul_mem_KOne {g g' : GL n k} (hg : g ∈ KO k n) (h : MaxM (g'.val - g.val)) : g⁻¹ * g' ∈ KOne k n := by
  obtain ⟨u, hu, hu'⟩ := exists_mul_KOne hg h
  rwa [← Units.ext hu', inv_mul_cancel_left]

def blockGL {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
    (g : GL a k) (B : Matrix a t k) (D : GL t k) : GL (a ⊕ t) k :=
  ⟨fromBlocks g.val B 0 D.val, fromBlocks (g⁻¹).val (-((g⁻¹).val * B * (D⁻¹).val)) 0 (D⁻¹).val,
    by simp [fromBlocks_multiply, ← Matrix.mul_assoc], by simp [fromBlocks_multiply, Matrix.mul_assoc]⟩

section Block
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] in
theorem intM_fromBlocks {a' t' : Type*} {A : Matrix a a' k} {B : Matrix a t' k} {C : Matrix t a' k} {D : Matrix t t' k} :
    IntM (fromBlocks A B C D) ↔ IntM A ∧ IntM B ∧ IntM C ∧ IntM D :=
  ⟨fun h => ⟨fun i j => h (.inl i) (.inl j), fun i j => h (.inl i) (.inr j), fun i j => h (.inr i) (.inl j),
    fun i j => h (.inr i) (.inr j)⟩, by
    rintro ⟨h1, h2, h3, h4⟩ (i | i) (j | j)
    exacts [h1 i j, h2 i j, h3 i j, h4 i j]⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] in
theorem maxM_fromBlocks {a' t' : Type*} {A : Matrix a a' k} {B : Matrix a t' k} {C : Matrix t a' k} {D : Matrix t t' k} :
    MaxM (fromBlocks A B C D) ↔ MaxM A ∧ MaxM B ∧ MaxM C ∧ MaxM D :=
  ⟨fun h => ⟨fun i j => h (.inl i) (.inl j), fun i j => h (.inl i) (.inr j), fun i j => h (.inr i) (.inl j),
    fun i j => h (.inr i) (.inr j)⟩, by
    rintro ⟨h1, h2, h3, h4⟩ (i | i) (j | j)
    exacts [h1 i j, h2 i j, h3 i j, h4 i j]⟩

theorem blockGL_mem_KO {g : GL a k} {B : Matrix a t k} {D : GL t k} (hg : g ∈ KO k a) (hB : IntM B)
    (hD : D ∈ KO k t) : blockGL g B D ∈ KO k (a ⊕ t) := by
  obtain ⟨g1, g2⟩ := mem_KO.1 hg
  obtain ⟨d1, d2⟩ := mem_KO.1 hD
  exact mem_KO.2 ⟨intM_fromBlocks.2 ⟨g1, hB, intM_zero, d1⟩,
    intM_fromBlocks.2 ⟨g2, ((g2.mul hB).mul d2).neg, intM_zero, d2⟩⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_blockGL (g : GL a k) (B : Matrix a t k) (D : GL t k) :
    Matrix.GeneralLinearGroup.det (blockGL g B D) =
      Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det D :=
  Units.ext (by simp [blockGL, Matrix.GeneralLinearGroup.val_det_apply])

theorem blocks_inv {h : GL (a ⊕ t) k} (hh : h ∈ KO k (a ⊕ t)) (hC : MaxM h.val.toBlocks₂₁) :
    MaxM (h.val.toBlocks₁₁ * (h⁻¹).val.toBlocks₁₁ - 1) ∧ MaxM (h.val.toBlocks₂₂ * (h⁻¹).val.toBlocks₂₂ - 1) ∧
      MaxM (h⁻¹).val.toBlocks₂₁ := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hh
  have e := h.mul_inv
  have e' := h.inv_mul
  rw [← fromBlocks_toBlocks h.val] at h1
  rw [← fromBlocks_toBlocks (h⁻¹).val] at h2
  rw [← fromBlocks_toBlocks h.val, ← fromBlocks_toBlocks (h⁻¹).val, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj] at e e'
  obtain ⟨i1, i2, -, i4⟩ := intM_fromBlocks.1 h1
  obtain ⟨j1, j2, j3, j4⟩ := intM_fromBlocks.1 h2
  have m1 : MaxM ((h⁻¹).val.toBlocks₁₁ * h.val.toBlocks₁₁ - 1) := by
    rw [← e'.1]; simpa using (j2.mul_maxM hC).neg
  have m2 : MaxM (h.val.toBlocks₂₂ * (h⁻¹).val.toBlocks₂₂ - 1) := by
    rw [← e.2.2.2]; simpa using (hC.mul_intM j2).neg
  obtain ⟨u, hu, hu'⟩ := exists_mem_KOne m1
  have iu := (mem_KO.1 (KOne_le_KO hu)).2
  have hinv : h.val.toBlocks₁₁ * ((u⁻¹).val * (h⁻¹).val.toBlocks₁₁) = 1 := by
    rw [mul_eq_one_comm, Matrix.mul_assoc, ← hu', Units.inv_mul]
  have m3 : MaxM (h⁻¹).val.toBlocks₂₁ := by
    have : (h⁻¹).val.toBlocks₂₁ = -((h⁻¹).val.toBlocks₂₂ * h.val.toBlocks₂₁) * ((u⁻¹).val * (h⁻¹).val.toBlocks₁₁) := by
      rw [← eq_neg_of_add_eq_zero_left e'.2.2.1, Matrix.mul_assoc, hinv, Matrix.mul_one]
    rw [this]
    exact (j4.mul_maxM hC).neg.mul_intM (iu.mul j1)
  refine ⟨?_, m2, m3⟩
  rw [← e.1]; simpa using (i2.mul_maxM m3).neg

theorem exists_mem_KO_of_mul {A A' : Matrix n n k} (hA : IntM A) (hA' : IntM A') (h : MaxM (A * A' - 1)) :
    ∃ g ∈ KO k n, g.val = A := by
  obtain ⟨u, hu, hu'⟩ := exists_mem_KOne h
  have e : A * (A' * (u⁻¹).val) = 1 := by rw [← Matrix.mul_assoc, ← hu', Units.mul_inv]
  exact ⟨⟨A, A' * (u⁻¹).val, e, mul_eq_one_comm.1 e⟩,
    mem_KO.2 ⟨hA, hA'.mul (mem_KO.1 (KOne_le_KO hu)).2⟩, rfl⟩

theorem exists_diag_blocks {h : GL (a ⊕ t) k} (hh : h ∈ KO k (a ⊕ t)) (hC : MaxM h.val.toBlocks₂₁) :
    (∃ g ∈ KO k a, g.val = h.val.toBlocks₁₁) ∧ ∃ D ∈ KO k t, D.val = h.val.toBlocks₂₂ := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hh
  obtain ⟨m1, m2, -⟩ := blocks_inv hh hC
  exact ⟨exists_mem_KO_of_mul (fun i j => h1 _ _) (fun i j => h2 _ _) m1,
    exists_mem_KO_of_mul (fun i j => h1 _ _) (fun i j => h2 _ _) m2⟩

theorem tame_det_blocks {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {h : GL (a ⊕ t) k} (hh : h ∈ KO k (a ⊕ t))
    (hC : MaxM h.val.toBlocks₂₁) {g : GL a k} (hg : g.val = h.val.toBlocks₁₁) {D : GL t k}
    (hD : D.val = h.val.toBlocks₂₂) :
    μ (Matrix.GeneralLinearGroup.det h) =
      μ (Matrix.GeneralLinearGroup.det g) * μ (Matrix.GeneralLinearGroup.det D) := by
  obtain ⟨⟨g', hg1, hg2⟩, D', hD1, hD2⟩ := exists_diag_blocks hh hC
  obtain rfl : g' = g := Units.ext (hg2.trans hg.symm)
  obtain rfl : D' = D := Units.ext (hD2.trans hD.symm)
  have hb := blockGL_mem_KO hg1 (B := h.val.toBlocks₁₂) (fun i j => intM_of_mem_KO hh _ _) hD1
  have hu := inv_mul_mem_KOne (g' := h) hb (by
    rw [← fromBlocks_toBlocks h.val]
    change MaxM (_ - fromBlocks g'.val h.val.toBlocks₁₂ 0 D'.val)
    rw [hg, hD, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp only [add_neg_cancel, neg_zero, add_zero]
    exact maxM_fromBlocks.2 ⟨maxM_zero, maxM_zero, hC, maxM_zero⟩)
  have := tame_det_of_mem_KOne hμ hu
  rw [map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one, det_blockGL, map_mul] at this
  exact this.symm

end Block

theorem isOpen_KOne : IsOpen (KOne k n : Set (GL n k)) := by
  have e : (KOne k n : Set (GL n k)) = ⋂ i, ⋂ j, (fun g : GL n k => (g.val - 1) i j) ⁻¹' {x | valuation k x < 1} := by
    ext g; simp only [SetLike.mem_coe, mem_KOne, Set.mem_iInter]; rfl
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · have := Units.continuous_val (M := Matrix n n k)
    fun_prop
  · simpa using (valuation k).isOpen_ball 1

theorem volN_ne_zero_ne_top [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {c : ℕ} (p : ℕ)
    {H : Subgroup (GL (n ⊕ Fin c) k)} (ho : IsOpen (H : Set (GL (n ⊕ Fin c) k)))
    (hc : IsCompact (H : Set (GL (n ⊕ Fin c) k))) :
    RootEx.volN ν n c p (H.subgroupOf (RootEx.N k n c p)) ≠ 0 ∧
      RootEx.volN ν n c p (H.subgroupOf (RootEx.N k n c p)) ≠ ⊤ := by
  classical
  haveI := secondCountable k
  haveI := t2Space k
  unfold RootEx.volN
  rw [(RootEx.Model.coord_embedding (k := k) (n := n) (c := c) p).1.comap_apply]
  constructor
  · have hcont : Continuous fun e => (RootEx.Model.mkNel (k := k) (n := n) (c := c) p e : GL (n ⊕ Fin c) k) := by
      rw [SplitFlip.isEmbedding_val_GL.continuous_iff]
      refine continuous_pi fun r => continuous_pi fun s => ?_
      change Continuous fun e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // RootEx.lev p rs.1 < RootEx.lev p rs.2} → k =>
        RootEx.Model.mkN (k := k) p e r s
      by_cases h : RootEx.lev p r < RootEx.lev p s
      · simp only [RootEx.Model.mkN, Matrix.of_apply, dif_pos h]; exact continuous_apply _
      · simp only [RootEx.Model.mkN, Matrix.of_apply, dif_neg h]; exact continuous_const
    refine (lt_of_lt_of_le ((ho.preimage hcont).measure_pos _ ⟨0, ?_⟩) (measure_mono fun e he => ?_)).ne'
    · have : (RootEx.Model.mkNel (k := k) (n := n) (c := c) p 0 : GL (n ⊕ Fin c) k) = 1 := by
        ext r s
        change RootEx.Model.mkN (k := k) p 0 r s = (1 : Matrix _ _ k) r s
        by_cases h : RootEx.lev p r < RootEx.lev p s
        · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
          simp [RootEx.Model.mkN, this]
        · simp [RootEx.Model.mkN, h]
      simp [this]
    · refine ⟨RootEx.Model.mkNel p e, he, funext fun rs => ?_⟩
      change RootEx.Model.mkN p e _ _ = _
      simp [RootEx.Model.mkN, rs.2]
  · have hcont : Continuous fun (g : GL (n ⊕ Fin c) k)
        (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // RootEx.lev p rs.1 < RootEx.lev p rs.2}) => g.val rs.1.1 rs.1.2 := by
      have := Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
      fun_prop
    refine (lt_of_le_of_lt (measure_mono ?_) (hc.image hcont).measure_lt_top).ne
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

end GlobalTheory.StepData
