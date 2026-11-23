import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open ValuativeRel
open scoped Matrix

open Filter Topology GlobalTheory.SplitWeil GlobalTheory.SplitFlip

noncomputable section
namespace GlobalTheory.SBInvSpan

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section IntLemmas
variable {m p q : Type}

theorem int_add {X Y : Matrix m p k} (hX : ∀ i j, X i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ 𝒪[k]) :
    ∀ i j, (X + Y) i j ∈ 𝒪[k] := fun i j => by simpa using add_mem (hX i j) (hY i j)

theorem int_neg {X : Matrix m p k} (hX : ∀ i j, X i j ∈ 𝒪[k]) : ∀ i j, (-X) i j ∈ 𝒪[k] :=
  fun i j => by simpa using neg_mem (hX i j)

theorem int_mul [Fintype p] {X : Matrix m p k} {Y : Matrix p q k} (hX : ∀ i j, X i j ∈ 𝒪[k])
    (hY : ∀ i j, Y i j ∈ 𝒪[k]) : ∀ i j, (X * Y) i j ∈ 𝒪[k] := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => mul_mem (hX i l) (hY l j)

theorem int_smul {a : k} (ha : a ∈ 𝒪[k]) {X : Matrix m p k} (hX : ∀ i j, X i j ∈ 𝒪[k]) :
    ∀ i j, (a • X) i j ∈ 𝒪[k] := fun i j => by simpa using mul_mem ha (hX i j)

theorem int_zero : ∀ i j, (0 : Matrix m p k) i j ∈ 𝒪[k] := fun i j => by simp [zero_mem]

theorem int_one [DecidableEq m] : ∀ i j, (1 : Matrix m m k) i j ∈ 𝒪[k] := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

end IntLemmas

theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem exists_smul_int_subset {m p : Type} [Fintype m] [Fintype p] {S : Set (Matrix m p k)}
    (hS : S ∈ 𝓝 (0 : Matrix m p k)) :
    ∃ c : k, c ≠ 0 ∧ valuation k c < 1 ∧ ∀ B : Matrix m p k, (∀ i j, B i j ∈ 𝒪[k]) → c • B ∈ S := by
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ B ∈ {B : Matrix m p k | ∀ i j, B i j ∈ 𝒪[k]}, c • B ∈ S := by
    refine (isCompact_intMatrix (k := k) (m := m) (n := p)).eventually_forall_of_forall_eventually
      fun y _ => ?_
    have hc : Continuous fun z : k × Matrix m p k => z.1 • z.2 := continuous_fst.smul continuous_snd
    have h0 : (fun z : k × Matrix m p k => z.1 • z.2) (0, y) = 0 := by simp
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hS)
  have hv : ∀ᶠ c in 𝓝 (0 : k), valuation k c < 1 :=
    IsOpen.mem_nhds (by simpa using (valuation k).isOpen_ball 1) (by simp)
  haveI := nhdsNE_zero_neBot (k := k)
  obtain ⟨c, ⟨h1, h2⟩, h3⟩ :=
    (((hev.and hv).filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and
      (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists
  exact ⟨c, h3, h2, fun B hB => h1 B hB⟩

theorem exists_period {m p : Type} [Fintype m] [Fintype p] (φ : Matrix m p k → ℂ)
    (hφ : φ ∈ SB (Matrix m p k)) :
    ∃ s : k, s ≠ 0 ∧ ∀ Y B : Matrix m p k, (∀ i j, B i j ∈ 𝒪[k]) → φ (Y + s • B) = φ Y := by
  obtain ⟨hl, hc⟩ : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hK : IsCompact (tsupport φ) := hc
  have hev : ∀ᶠ y in 𝓝 (0 : Matrix m p k), ∀ x ∈ tsupport φ, φ (x + y) = φ x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have h1 : IsLocallyConstant fun z : Matrix m p k × Matrix m p k => φ (z.2 + z.1) :=
      hl.comp_continuous (by fun_prop)
    have h2 : IsLocallyConstant fun z : Matrix m p k × Matrix m p k => φ z.2 :=
      hl.comp_continuous (by fun_prop)
    filter_upwards [h1.eventually_eq (0, x), h2.eventually_eq (0, x)] with z e1 e2
    rw [e1, e2, add_zero]
  obtain ⟨s, hs, -, hM⟩ := exists_smul_int_subset hev
  refine ⟨s, hs, fun x B hB => ?_⟩
  by_cases hx : x ∈ tsupport φ
  · exact hM B hB x hx
  by_cases hxy : x + s • B ∈ tsupport φ
  · have := hM (-B) (int_neg hB) _ hxy
    rw [smul_neg, add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxy]

theorem exists_int_inv_one_add_small {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n k)
    (hE : ∀ i j, valuation k (E i j) < 1) :
    ∃ N : Matrix n n k, (∀ i j, N i j ∈ 𝒪[k]) ∧ (1 + E) * N = 1 := by
  have hI : ∀ i j, (1 + E) i j ∈ 𝒪[k] := fun i j => by
    rw [Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ (hE i j).le
    rw [Matrix.one_apply]; split_ifs <;> simp
  have hEI : ∀ i j, E i j ∈ 𝒪[k] := fun i j => (Valuation.mem_integer_iff _ _).2 (hE i j).le
  let M : Matrix n n 𝒪[k] := fun i j => ⟨(1 + E) i j, hI i j⟩
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    have : M i j - (1 : Matrix n n 𝒪[k]) i j = ⟨E i j, hEI i j⟩ := by
      apply Subtype.ext
      by_cases h : i = j <;> simp [M, Matrix.one_apply, h]
    have hm : M i j - (1 : Matrix n n 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact hE i j
    have e2 : (IsLocalRing.residue 𝒪[k]) (M i j) =
        (IsLocalRing.residue 𝒪[k]) ((1 : Matrix n n 𝒪[k]) i j) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hm
    rw [e2]; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hres, Matrix.det_one]
    exact one_ne_zero
  refine ⟨(algebraMap 𝒪[k] k).mapMatrix M⁻¹, fun i j => (M⁻¹ i j).2, ?_⟩
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = 1 + E := rfl
  rw [← hM, ← map_mul, Matrix.mul_nonsing_inv M hdet, map_one]

theorem exists_one_add_mem {n : Type} [Fintype n] [DecidableEq n] (K : Subgroup (GL n k))
    (hK : IsOpen (K : Set (GL n k))) :
    ∃ t : k, t ≠ 0 ∧ valuation k t < 1 ∧ ∀ A : Matrix n n k, (∀ i j, A i j ∈ 𝒪[k]) →
      ∃ g ∈ K, (g : Matrix n n k) = 1 + t • A := by
  obtain ⟨O, hO, hOK⟩ := (isEmbedding_val_GL (k := k) (n := n)).isInducing.isOpen_iff.1 hK
  have h1 : (1 : Matrix n n k) ∈ O := by
    have : (1 : GL n k) ∈ (fun g : GL n k => g.val) ⁻¹' O := by rw [hOK]; exact K.one_mem
    simpa using this
  have hS : {E : Matrix n n k | 1 + E ∈ O} ∈ 𝓝 (0 : Matrix n n k) :=
    (hO.preimage (by fun_prop)).mem_nhds (by simpa using h1)
  obtain ⟨t, ht, hv, hE⟩ := exists_smul_int_subset hS
  refine ⟨t, ht, hv, fun A hA => ?_⟩
  have hsmall : ∀ i j, valuation k ((t • A) i j) < 1 := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    calc valuation k t * valuation k (A i j) ≤ valuation k t * 1 :=
          mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).1 (hA i j))
      _ < 1 := by rwa [mul_one]
  obtain ⟨N, -, hN⟩ := exists_int_inv_one_add_small (t • A) hsmall
  let g : GL n k := ⟨1 + t • A, N, hN, mul_eq_one_comm.1 hN⟩
  refine ⟨g, ?_, rfl⟩
  have : g ∈ (fun g : GL n k => g.val) ⁻¹' O := hE A hA
  rwa [hOK] at this

section Rel
variable {m p : Type} [Fintype m] [DecidableEq m]

def Rel (t c : k) (X Y : Matrix m p k) : Prop :=
  ∃ (A : Matrix m m k) (B : Matrix m p k), (∀ i j, A i j ∈ 𝒪[k]) ∧ (∀ i j, B i j ∈ 𝒪[k]) ∧
    Y = X + t • (A * X + c • B)

theorem rel_refl (t c : k) (X : Matrix m p k) : Rel t c X X :=
  ⟨0, 0, int_zero, int_zero, by simp⟩

theorem rel_trans {t c : k} (ht : t ∈ 𝒪[k]) {X Y Z : Matrix m p k} (h1 : Rel t c X Y) (h2 : Rel t c Y Z) :
    Rel t c X Z := by
  obtain ⟨A, B, hA, hB, rfl⟩ := h1
  obtain ⟨A', B', hA', hB', rfl⟩ := h2
  refine ⟨A + A' + t • (A' * A), B + t • (A' * B) + B', int_add (int_add hA hA') (int_smul ht (int_mul hA' hA)),
    int_add (int_add hB (int_smul ht (int_mul hA' hB))) hB', ?_⟩
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_add]
  module

theorem rel_symm {t c : k} (hv : valuation k t < 1) {X Y : Matrix m p k} (h : Rel t c X Y) : Rel t c Y X := by
  obtain ⟨A, B, hA, hB, rfl⟩ := h
  have hsmall : ∀ i j, valuation k ((t • A) i j) < 1 := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    calc valuation k t * valuation k (A i j) ≤ valuation k t * 1 :=
          mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).1 (hA i j))
      _ < 1 := by rwa [mul_one]
  obtain ⟨N, hNi, hN⟩ := exists_int_inv_one_add_small (t • A) hsmall
  have hN' : N * (1 + t • A) = 1 := mul_eq_one_comm.1 hN
  have P : N + t • (A * N) = 1 := by
    rw [← hN, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have Q : N + t • (N * A) = 1 := by
    rw [← hN', Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  refine ⟨-(A * N), -(N * B), int_neg (int_mul hA hNi), int_neg (int_mul hNi hB), ?_⟩
  have hQ' : A * N * X + t • (A * N * A * X) = A * X := by
    have : A * ((N + t • (N * A)) * X) = A * N * X + t • (A * N * A * X) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [← this, Q, Matrix.one_mul]
  have hP' : N * B + t • (A * N * B) = B := by
    have : (N + t • (A * N)) * B = N * B + t • (A * N * B) := by
      simp only [Matrix.add_mul, Matrix.smul_mul]
    rw [← this, P, Matrix.one_mul]
  have key : X + t • (A * X + c • B) + t • (-(A * N) * (X + t • (A * X + c • B)) + c • -(N * B)) =
      X + t • (A * X - (A * N * X + t • (A * N * A * X))) + (t * c) • (B - (N * B + t • (A * N * B))) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
      Matrix.neg_mul, Matrix.mul_neg, smul_add, smul_neg, smul_sub]
    module
  rw [key, hQ', hP']
  simp

theorem rel_equivalence {t c : k} (hv : valuation k t < 1) : Equivalence (Rel (m := m) (p := p) t c) :=
  ⟨rel_refl t c, rel_symm hv, rel_trans ((Valuation.mem_integer_iff _ _).2 hv.le)⟩

variable [Fintype p]

theorem rel_iff {t c : k} (ht : t ≠ 0) {X : Matrix m p k} {h : Matrix p p k}
    (hh : ∀ Y : Matrix m p k, (∃ (A : Matrix m m k) (B : Matrix m p k), (∀ i j, A i j ∈ 𝒪[k]) ∧
      (∀ i j, B i j ∈ 𝒪[k]) ∧ Y = A * X + c • B) ↔ ∀ i j, (Y * h) i j ∈ 𝒪[k]) (Y : Matrix m p k) :
    Rel t c X Y ↔ ∀ i j, (t⁻¹ • (Y * h - X * h)) i j ∈ 𝒪[k] := by
  rw [← Matrix.sub_mul, ← Matrix.smul_mul, ← hh]
  constructor
  · rintro ⟨A, B, hA, hB, rfl⟩
    exact ⟨A, B, hA, hB, by rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]⟩
  · rintro ⟨A, B, hA, hB, e⟩
    exact ⟨A, B, hA, hB, by rw [← e, smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel]⟩

end Rel

section Box
variable {m p : Type} [Fintype m] [Fintype p]

open Classical in

def boxInd (t : k) (X' : Matrix m p k) : Matrix m p k → ℂ := fun Z =>
  if ∀ i j, (t⁻¹ • (Z - X')) i j ∈ 𝒪[k] then 1 else 0

theorem boxInd_mem_SB {t : k} (ht : t ≠ 0) (X' : Matrix m p k) : boxInd t X' ∈ SB (Matrix m p k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hcont : Continuous fun Z : Matrix m p k => t⁻¹ • (Z - X') := by fun_prop
  have hUo : IsOpen {Z : Matrix m p k | ∀ i j, (t⁻¹ • (Z - X')) i j ∈ 𝒪[k]} :=
    (isOpen_intMatrix (k := k) (m := m) (n := p)).preimage hcont
  have hUc : IsClosed {Z : Matrix m p k | ∀ i j, (t⁻¹ • (Z - X')) i j ∈ 𝒪[k]} :=
    (isCompact_intMatrix (k := k) (m := m) (n := p)).isClosed.preimage hcont
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases hx : ∀ i j, (t⁻¹ • (x - X')) i j ∈ 𝒪[k]
    · refine ⟨_, hUo, hx, fun y hy => ?_⟩
      have hy' : ∀ i j, (t⁻¹ • (y - X')) i j ∈ 𝒪[k] := hy
      simp only [boxInd]; rw [if_pos hy', if_pos hx]
    · refine ⟨_, hUc.isOpen_compl, hx, fun y hy => ?_⟩
      have hy' : ¬ ∀ i j, (t⁻¹ • (y - X')) i j ∈ 𝒪[k] := hy
      simp only [boxInd]; rw [if_neg hy', if_neg hx]
  · refine HasCompactSupport.intro ((isCompact_intMatrix (k := k) (m := m) (n := p)).image
      (f := fun Z => X' + t • Z) (by fun_prop)) fun x hx => ?_
    simp only [boxInd]
    rw [if_neg]
    intro hc
    exact hx ⟨t⁻¹ • (x - X'), hc, by simp [smul_smul, mul_inv_cancel₀ ht]⟩

open Classical in
theorem boxInd_congr {t : k} {X₁ X₂ : Matrix m p k} (h : ∀ i j, (t⁻¹ • (X₁ - X₂)) i j ∈ 𝒪[k]) :
    boxInd t X₁ = boxInd t X₂ := by
  funext Z
  simp only [boxInd]
  refine if_congr ⟨fun hZ => ?_, fun hZ => ?_⟩ rfl rfl
  · have e : t⁻¹ • (Z - X₂) = t⁻¹ • (Z - X₁) + t⁻¹ • (X₁ - X₂) := by rw [← smul_add]; congr 1; abel
    rw [e]; exact int_add hZ h
  · have e : t⁻¹ • (Z - X₁) = t⁻¹ • (Z - X₂) + -(t⁻¹ • (X₁ - X₂)) := by
      rw [← smul_neg, ← smul_add]; congr 1; abel
    rw [e]; exact int_add hZ (int_neg h)

end Box

open Classical in

theorem mem_span_classes {T : Type} [TopologicalSpace T] (R : T → T → Prop) (hR : Equivalence R)
    (hopen : ∀ x, IsOpen {y | R x y}) (f : T → ℂ) (hf : HasCompactSupport f)
    (hconst : ∀ x y, R x y → f y = f x) :
    f ∈ Submodule.span ℂ {g : T → ℂ | ∃ x, g = fun y => if R x y then 1 else 0} := by
  let r : Setoid T := ⟨R, hR⟩
  obtain ⟨S, hS⟩ := (hf : IsCompact (tsupport f)).elim_finite_subcover (fun x : T => {y | R x y}) hopen
    (fun y _ => Set.mem_iUnion.2 ⟨y, hR.refl y⟩)
  let Q : Finset (Quotient r) := S.image (Quotient.mk r)
  have hQ : ∀ y, y ∈ tsupport f → Quotient.mk r y ∈ Q := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.1 (hS hy)
    exact Finset.mem_image.2 ⟨x, hx, Quotient.sound hxy⟩
  have hiff : ∀ (q : Quotient r) (y : T), R q.out y ↔ q = Quotient.mk r y := fun q y => by
    conv_rhs => rw [← Quotient.out_eq q]
    exact (Quotient.eq (r := r)).symm
  have e : f = ∑ q ∈ Q, f q.out • (fun y => if R q.out y then (1 : ℂ) else 0) := by
    funext y
    rw [Finset.sum_apply]
    have : ∀ q ∈ Q, (f q.out • (fun y => if R q.out y then (1 : ℂ) else 0)) y =
        if q = Quotient.mk r y then f y else 0 := fun q _ => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hq : q = Quotient.mk r y
      · rw [if_pos ((hiff q y).2 hq), if_pos hq, hconst _ _ ((hiff q y).2 hq)]
      · rw [if_neg (fun h' => hq ((hiff q y).1 h')), if_neg hq]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    split_ifs with hy
    · rfl
    · exact image_eq_zero_of_notMem_tsupport fun h' => hy (hQ y h')
  rw [e]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.out, rfl⟩)

open Classical in

theorem span_translates_of_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ),
    (∀ (X : Matrix (Fin n) (Fin d) k) (c : k), c ≠ 0 → ∃ h : GL (Fin d) k, ∀ Y : Matrix (Fin n) (Fin d) k,
      (∃ (A : Matrix (Fin n) (Fin n) k) (B : Matrix (Fin n) (Fin d) k), (∀ i j, A i j ∈ 𝒪[k]) ∧ (∀ i j, B i j ∈ 𝒪[k]) ∧ Y = A * X + c • B) ↔
        ∀ i j, (Y * (h : Matrix (Fin d) (Fin d) k)) i j ∈ 𝒪[k]) →
    ∀ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) →
    ∃ A : Set (Matrix (Fin n) (Fin d) k → ℂ), A.Finite ∧ (∀ a ∈ A, a ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)) ∧
      ∀ φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k), (∀ g ∈ K, ∀ Y, φ ((g : Matrix (Fin n) (Fin n) k) * Y) = φ Y) →
        φ ∈ Submodule.span ℂ {χ : Matrix (Fin n) (Fin d) k → ℂ | ∃ a ∈ A, ∃ h : GL (Fin d) k, χ = fun Y => a (Y * (h : Matrix (Fin d) (Fin d) k))} := by
  intro k _ _ _ _ n d H K hK
  obtain ⟨t, ht, htv, hgK⟩ := exists_one_add_mem K hK
  obtain ⟨F, hF⟩ := (isCompact_intMatrix (k := k) (m := Fin n) (n := Fin d)).elim_finite_subcover
    (fun X' : {X' : Matrix (Fin n) (Fin d) k // ∀ i j, X' i j ∈ 𝒪[k]} =>
      {Z : Matrix (Fin n) (Fin d) k | ∀ i j, (t⁻¹ • (Z - X'.1)) i j ∈ 𝒪[k]})
    (fun X' => (isOpen_intMatrix (k := k) (m := Fin n) (n := Fin d)).preimage (by fun_prop))
    (fun Z hZ => Set.mem_iUnion.2 ⟨⟨Z, hZ⟩, by simpa using int_zero (k := k) (m := Fin n) (p := Fin d)⟩)
  refine ⟨(fun X' : {X' : Matrix (Fin n) (Fin d) k // ∀ i j, X' i j ∈ 𝒪[k]} => boxInd t X'.1) '' (F : Set _), F.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨X', -, rfl⟩; exact boxInd_mem_SB ht _
  intro φ hφ hinv
  obtain ⟨s, hs, hper⟩ := exists_period φ hφ
  have hc : s / t ≠ 0 := div_ne_zero hs ht
  have htc : t * (s / t) = s := mul_div_cancel₀ s ht
  have hR := rel_equivalence (m := Fin n) (p := Fin d) (c := s / t) htv
  have hopen : ∀ X, IsOpen {Y | Rel t (s / t) X Y} := fun X => by
    obtain ⟨h, hh⟩ := H X (s / t) hc
    have e : {Y | Rel t (s / t) X Y} = (fun Y : Matrix (Fin n) (Fin d) k =>
        t⁻¹ • (Y * (h : Matrix (Fin d) (Fin d) k) - X * (h : Matrix (Fin d) (Fin d) k))) ⁻¹'
          {Z | ∀ i j, Z i j ∈ 𝒪[k]} := Set.ext fun Y => rel_iff ht hh Y
    rw [e]
    exact (isOpen_intMatrix (k := k) (m := Fin n) (n := Fin d)).preimage (by fun_prop)
  have hconst : ∀ X Y, Rel t (s / t) X Y → φ Y = φ X := by
    rintro X _ ⟨A, B, hA, hB, rfl⟩
    obtain ⟨g, hgK', hgv⟩ := hgK A hA
    have e : X + t • (A * X + (s / t) • B) = (g : Matrix (Fin n) (Fin n) k) * X + s • B := by
      rw [hgv, Matrix.add_mul, Matrix.one_mul, smul_add, Matrix.smul_mul, smul_smul, htc, add_assoc]
    rw [e, hper _ _ hB, hinv g hgK' X]
  refine Submodule.span_mono ?_ (mem_span_classes _ hR hopen φ hφ.2 hconst)
  rintro _ ⟨X, rfl⟩
  obtain ⟨h, hh⟩ := H X (s / t) hc
  have hXh : ∀ i j, (X * (h : Matrix (Fin d) (Fin d) k)) i j ∈ 𝒪[k] :=
    (hh X).1 ⟨1, 0, int_one, int_zero, by simp⟩
  obtain ⟨X', hX'F, hX'⟩ := Set.mem_iUnion₂.1 (hF hXh)
  refine ⟨boxInd t X'.1, ⟨X', hX'F, rfl⟩, h, ?_⟩
  rw [← boxInd_congr hX']
  funext Y
  simp only [boxInd]
  by_cases hr : Rel t (s / t) X Y
  · rw [if_pos hr, if_pos ((rel_iff ht hh Y).1 hr)]
  · rw [if_neg hr, if_neg (fun h' => hr ((rel_iff ht hh Y).2 h'))]

end GlobalTheory.SBInvSpan
