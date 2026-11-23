import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity

noncomputable section

namespace Formalism.MainNotions.S.Inh

section TopsChoicePartA

open Matrix MeasureTheory
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

def degenerateLevel : Lev where
  k0 := 0
  r := 0
  z := 0
  z' := 0
  Wp := ℂ
  Wq := ℂ
  π := fun _ => 0
  π' := fun _ => 0
  μsec := fun _ => 0

theorem level_type_nonempty : Nonempty Lev := ⟨degenerateLevel⟩

theorem haar_data_nonempty (L : Lev) : Nonempty L.Haar := ⟨⟨0, 0, 0⟩⟩

theorem module_datum_nonempty (m : ℕ) (E : Type*) [AddCommGroup E] [Module ℂ E] (n : ℕ) : Nonempty (Mod m E n) :=
  ⟨⟨fun _ _ => zeroOp, fun _ _ _ => zeroOp, fun _ => 0⟩⟩

theorem base_datum_nonempty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Nonempty (Base E) :=
  ⟨{ k0 := 0, T := 1, T' := 1, u := 0, u' := 0, I := ∅, sgn := 1, hs := fun _ _ => 0, fadj := id, Rho := Unit,
     IsType := fun _ => True, rhoP := fun _ => 0 }⟩

def degenerateContext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Base E) (r : ℕ) : Ctx B r where
  Dom := ∅
  cls := ∅
  clsF := ∅
  beta := fun _ _ => 0
  P := fun _ _ => 0
  Q := fun _ _ _ _ _ => 0
  AA := ∅
  RR := fun _ _ _ _ _ => 0
  TT := fun _ _ _ _ _ _ _ _ => 0
  qw := fun _ _ => 0
  uw := fun _ _ _ _ => 0

theorem context_nonempty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Base E) (r : ℕ) :
    Nonempty (Ctx B r) := ⟨degenerateContext B r⟩

theorem nonempty_GCtx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) : Nonempty (GCtx E r) :=
  ⟨{ nV := r, Eop := fun _ _ _ _ => 0, H := 0, eIdx := id, Rad := fun _ _ => False, PolyInv := ∅ }⟩

theorem size_condition_exists (C : ℝ) (L : Lev) (N : ℕ) : ∃ (A : ℝ) (mm : ℕ), Big C L N A mm := by
  obtain ⟨mm, hmm⟩ := exists_nat_ge
    (C * ((L.r : ℝ) + 1) ^ 4 * ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3))
  exact ⟨_, mm, le_rfl, hmm⟩

def RadialOperatorsWellDefinedOnGerms (L : Lev) : Prop :=
  ∀ (Y : ℂ) (a b : Fin 2), ∀ J₁ ∈ L.KKop, ∀ J₂ ∈ L.KKop, ∀ U : Set (Fin (L.r + 1) → ℂ), IsOpen U → U ⊆ L.BD →
    (∀ x ∈ U, L.B J₁ x = L.B J₂ x) → ∀ x ∈ U, L.B (L.QQ Y a b J₁) x = L.B (L.QQ Y a b J₂) x

theorem bounded_domain_isOpen (L : Lev) : IsOpen L.BD := by
  have h1 : IsOpen {x : Fin (L.r + 1) → ℂ | ∀ l, x l ≠ 0} := by
    have : {x : Fin (L.r + 1) → ℂ | ∀ l, x l ≠ 0} = ⋂ l, {x | x l ≠ 0} := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have h2 : IsOpen {x : Fin (L.r + 1) → ℂ |
      Tz (L.k0 + 1) L.r L.z * Tz (L.k0 + 1) L.r L.z' < Complex.normSq (zOf x)} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))
  exact h1.inter h2

open Classical in

def germRadialPart (L : Lev) (Y : ℂ) (a b : Fin 2) : L.POp := fun φ x =>
  if h : ∃ J, J ∈ L.KKop ∧ ∃ U : Set (Fin (L.r + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ U ⊆ L.BD ∧ ∀ y ∈ U, φ y = L.B J y
  then L.B (L.QQ Y a b h.choose) x else 0

theorem germ_radial_part_eq_of_local_picture (L : Lev) (hw : RadialOperatorsWellDefinedOnGerms L) (Y : ℂ) (a b : Fin 2) (φ : L.PF) (x : Fin (L.r + 1) → ℂ)
    (J : L.GF) (hJ : J ∈ L.KKop) (U : Set (Fin (L.r + 1) → ℂ)) (hU : IsOpen U) (hx : x ∈ U) (hUB : U ⊆ L.BD)
    (hφ : ∀ y ∈ U, φ y = L.B J y) : germRadialPart L Y a b φ x = L.B (L.QQ Y a b J) x := by
  have h : ∃ J, J ∈ L.KKop ∧ ∃ U : Set (Fin (L.r + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ U ⊆ L.BD ∧ ∀ y ∈ U, φ y = L.B J y :=
    ⟨J, hJ, U, hU, hx, hUB, hφ⟩
  unfold germRadialPart
  rw [dif_pos h]
  obtain ⟨hJ', U', hU', hx', hUB', hφ'⟩ := h.choose_spec
  exact hw Y a b _ hJ' _ hJ (U' ∩ U) (hU'.inter hU) (fun y hy => hUB hy.2)
    (fun y hy => (hφ' y hy.1).symm.trans (hφ y hy.2)) x ⟨hx', hx⟩

theorem germ_radial_part_local (L : Lev) (hw : RadialOperatorsWellDefinedOnGerms L) (Y : ℂ) (a b : Fin 2) (V : Set (Fin (L.r + 1) → ℂ))
    (hV : IsOpen V) : LocalOn V (germRadialPart L Y a b) := by
  intro φ ψ hφψ x hx
  by_cases h : ∃ J, J ∈ L.KKop ∧ ∃ U : Set (Fin (L.r + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ U ⊆ L.BD ∧ ∀ y ∈ U, φ y = L.B J y
  · obtain ⟨J, hJ, U, hU, hxU, hUB, hφ⟩ := h
    rw [germ_radial_part_eq_of_local_picture L hw Y a b φ x J hJ U hU hxU hUB hφ,
      germ_radial_part_eq_of_local_picture L hw Y a b ψ x J hJ (U ∩ V) (hU.inter hV) ⟨hxU, hx⟩ (fun y hy => hUB hy.1)
        (fun y hy => (hφψ y hy.2).symm.trans (hφ y hy.1))]
  · have h' : ¬ ∃ J, J ∈ L.KKop ∧ ∃ U : Set (Fin (L.r + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ U ⊆ L.BD ∧
        ∀ y ∈ U, ψ y = L.B J y := by
      rintro ⟨J, hJ, U, hU, hxU, hUB, hψ⟩
      exact h ⟨J, hJ, U ∩ V, hU.inter hV, ⟨hxU, hx⟩, fun y hy => hUB hy.1,
        fun y hy => (hφψ y hy.2).trans (hψ y hy.1)⟩
    unfold germRadialPart
    rw [dif_neg h, dif_neg h']

theorem radial_part_exists_iff_well_defined (L : Lev) : (∃ R, L.IsRadQQ R) ↔ RadialOperatorsWellDefinedOnGerms L := by
  constructor
  · rintro ⟨R, hR⟩ Y a b J₁ h₁ J₂ h₂ U hU hUB hJ x hx
    obtain ⟨hrad, -, hloc⟩ := hR Y a b
    have e₁ := hrad J₁ ⟨h₁.1, h₁⟩ x (hUB hx)
    have e₂ := hrad J₂ ⟨h₂.1, h₂⟩ x (hUB hx)
    exact e₁.trans ((hloc U hU hUB _ _ hJ x hx).trans e₂.symm)
  · intro hw
    refine ⟨fun Y => Matrix.of fun a b => germRadialPart L Y a b, fun Y a b => ⟨?_, ?_, ?_⟩⟩
    · intro J hJ x hx
      exact (germ_radial_part_eq_of_local_picture L hw Y a b _ x J hJ.2 L.BD (bounded_domain_isOpen L) hx subset_rfl (fun _ _ => rfl)).symm
    · exact germ_radial_part_local L hw Y a b _ (bounded_domain_isOpen L)
    · intro U hU _
      exact germ_radial_part_local L hw Y a b U hU

theorem radial_part_exists_of_trivial_hom (L : Lev) [Subsingleton L.Hom] : ∃ R, L.IsRadQQ R :=
  (radial_part_exists_iff_well_defined L).2 fun _ _ _ _ _ _ _ _ _ _ _ _ _ => Subsingleton.elim _ _

theorem hermitian_form_basis_vectors {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : herm H (bvec i) (bvec j) = H j i := by
  simp [herm, bvec, dotProduct, Pi.single_apply, Matrix.col_apply]

def negativeBasisVector (k0 r : ℕ) : Vec k0 r := bvec (wI (k0 + 1) r (Fin.last (k0 + 1)))

theorem hermitian_norm_negative_vector_eq_one (k0 r : ℕ) : Tz (k0 + 1) r (negativeBasisVector k0 r) = 1 := by
  unfold Tz negativeBasisVector
  rw [hermitian_form_basis_vectors]
  simp [Hpk, wI]

theorem negative_basis_vector_mem_Wb (k0 r : ℕ) : inWb (k0 + 1) r (negativeBasisVector k0 r) := by
  intro i hi
  unfold negativeBasisVector bvec
  rw [Pi.single_apply, if_neg]
  intro h
  have := congrArg Fin.val h
  simp [wI] at this
  omega

theorem definite_part_negative_vector (k0 r : ℕ) : wbPart (k0 + 1) r (negativeBasisVector k0 r) = bvec (Fin.last (k0 + 1)) := by
  funext j
  simp only [wbPart, negativeBasisVector, bvec, Pi.single_apply, wI, Fin.ext_iff, Fin.val_last]
  congr 1
  simp

def hyperbolicU11Element (ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-star ζ, ((Real.sqrt (Complex.normSq ζ - 1) : ℝ) : ℂ); ((Real.sqrt (Complex.normSq ζ - 1) : ℝ) : ℂ), -ζ]

def bigCellSectionMatrix (k0 : ℕ) (ζ : ℂ) : Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ :=
  (Matrix.fromBlocks 1 0 0 (hyperbolicU11Element ζ)).submatrix (finSumFinEquiv (m := k0) (n := 2)).symm
    (finSumFinEquiv (m := k0) (n := 2)).symm

theorem signature_form_block_decomposition (k0 : ℕ) : Hb (k0 + 1) =
    (Matrix.fromBlocks 1 0 0 !![1, 0; 0, -1]).submatrix (finSumFinEquiv (m := k0) (n := 2)).symm
      (finSumFinEquiv (m := k0) (n := 2)).symm := by
  ext i j
  obtain ⟨a, rfl⟩ := (finSumFinEquiv (m := k0) (n := 2)).surjective i
  obtain ⟨b, rfl⟩ := (finSumFinEquiv (m := k0) (n := 2)).surjective j
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b
  · simp only [Matrix.fromBlocks_apply₁₁, Hb, Matrix.diagonal_apply, Matrix.one_apply, finSumFinEquiv_apply_left,
      Fin.ext_iff, Fin.val_castAdd, Fin.val_last]
    have := a.2
    split_ifs <;> first | rfl | omega
  · simp only [Matrix.fromBlocks_apply₁₂, Hb, Matrix.diagonal_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, Matrix.zero_apply]
    have := a.2
    rw [if_neg (by omega)]
  · simp only [Matrix.fromBlocks_apply₂₁, Hb, Matrix.diagonal_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, Matrix.zero_apply]
    have := b.2
    rw [if_neg (by omega)]
  · simp only [Matrix.fromBlocks_apply₂₂, Hb, Matrix.diagonal_apply,
      finSumFinEquiv_apply_right, Fin.ext_iff, Fin.val_natAdd, Fin.val_last]
    fin_cases a <;> fin_cases b <;> simp

theorem normSq_contDiff_smooth : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
  have : (fun ζ : ℂ => Complex.normSq ζ) = fun ζ : ℂ => Complex.reCLM ζ * Complex.reCLM ζ + Complex.imCLM ζ * Complex.imCLM ζ := by
    funext ζ; simp [Complex.normSq_apply]
  rw [this]
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

theorem sqrt_normSq_sub_one_contDiffOn :
    ContDiffOn ℝ ∞ (fun ζ : ℂ => ((Real.sqrt (Complex.normSq ζ - 1) : ℝ) : ℂ)) {ζ : ℂ | 1 < Complex.normSq ζ} := by
  have h : ContDiffOn ℝ ∞ (fun ζ : ℂ => Real.sqrt (Complex.normSq ζ - 1)) {ζ : ℂ | 1 < Complex.normSq ζ} :=
    ContDiffOn.sqrt (normSq_contDiff_smooth.sub contDiff_const).contDiffOn (fun x hx => by
      have : (1 : ℝ) < Complex.normSq x := hx
      exact ne_of_gt (by linarith))
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h

theorem hyperbolic_element_contDiffOn (i j : Fin 2) : ContDiffOn ℝ ∞ (fun ζ : ℂ => hyperbolicU11Element ζ i j) {ζ : ℂ | 1 < Complex.normSq ζ} := by
  fin_cases i <;> fin_cases j
  · show ContDiffOn ℝ ∞ (fun ζ : ℂ => -star ζ) _
    exact (Complex.conjCLE.contDiff.neg).contDiffOn
  · exact sqrt_normSq_sub_one_contDiffOn
  · exact sqrt_normSq_sub_one_contDiffOn
  · show ContDiffOn ℝ ∞ (fun ζ : ℂ => -ζ) _
    exact contDiff_id.neg.contDiffOn

theorem hyperbolic_element_preserves_form (ζ : ℂ) (hζ : 1 < Complex.normSq ζ) :
    (hyperbolicU11Element ζ)ᴴ * !![1, 0; 0, -1] * hyperbolicU11Element ζ = !![1, 0; 0, -1] := by
  have hs : ((Real.sqrt (Complex.normSq ζ - 1) : ℝ) : ℂ) * ((Real.sqrt (Complex.normSq ζ - 1) : ℝ) : ℂ) =
      (Complex.normSq ζ : ℂ) - 1 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    push_cast; ring
  have hz : ζ * (starRingEnd ℂ) ζ = (Complex.normSq ζ : ℂ) := Complex.mul_conj ζ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicU11Element, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    first
      | linear_combination hz - hs
      | linear_combination hs - hz
      | ring

theorem big_cell_section_negative_vector (k0 r : ℕ) : IsSection (k0 + 1) r (negativeBasisVector k0 r) (negativeBasisVector k0 r) (bigCellSectionMatrix k0) := by
  unfold IsSection
  rw [hermitian_norm_negative_vector_eq_one, definite_part_negative_vector]
  simp only [mul_one]
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [bigCellSectionMatrix, Matrix.submatrix_apply]
    generalize (finSumFinEquiv (m := k0) (n := 2)).symm i = a
    generalize (finSumFinEquiv (m := k0) (n := 2)).symm j = b
    rcases a with a | a <;> rcases b with b | b
    · simp only [Matrix.fromBlocks_apply₁₁]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₁₂]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₁]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₂]; exact hyperbolic_element_contDiffOn a b
  · intro ζ hζ
    constructor
    · rw [signature_form_block_decomposition, bigCellSectionMatrix, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hyperbolic_element_preserves_form ζ hζ]
    · have hl : (finSumFinEquiv (m := k0) (n := 2)).symm (Fin.last (k0 + 1)) = Sum.inr 1 := by
        rw [Equiv.symm_apply_eq]
        simp [Fin.ext_iff]
      have h1 : bigCellSectionMatrix k0 ζ *ᵥ bvec (Fin.last (k0 + 1)) = fun i => bigCellSectionMatrix k0 ζ i (Fin.last (k0 + 1)) := by
        funext i
        simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [h1]
      simp [herm, bvec, dotProduct, Pi.single_apply, Matrix.mulVec, Hb, Matrix.diagonal_apply, bigCellSectionMatrix, hl, hyperbolicU11Element]
      rw [Finset.sum_eq_single (Fin.last (k0 + 1))]
      · simp [hl]
      · intro b _ hb; simp [hb]
      · simp

def upperBlockOfMatrix (k0 r : ℕ) (g : Mat k0 r) : Matrix (Fin (k0 + 1)) (Fin (k0 + 1)) ℂ :=
  fun i j => g (wI (k0 + 1) r i.castSucc) (wI (k0 + 1) r j.castSucc)

theorem upper_block_of_blockW_eq (k0 r : ℕ) (h : Matrix (Fin (k0 + 1)) (Fin (k0 + 1)) ℂ) :
    upperBlockOfMatrix k0 r (Formalism.MainNotions.S.blockW (k0 + 1) r h) = h := by
  funext i j
  have h1 : ∀ a : Fin (k0 + 1), r ≤ (wI (k0 + 1) r a.castSucc).val ∧ (wI (k0 + 1) r a.castSucc).val < r + (k0 + 1) := by
    intro a
    have := a.2
    simp only [wI, Fin.val_castSucc]
    omega
  have e : ∀ (a : Fin (k0 + 1)) (p : (wI (k0 + 1) r a.castSucc).val - r < k0 + 1),
      (⟨(wI (k0 + 1) r a.castSucc).val - r, p⟩ : Fin (k0 + 1)) = a :=
    fun a p => Fin.ext (by simp [wI])
  unfold upperBlockOfMatrix Formalism.MainNotions.S.blockW
  rw [dif_pos (h1 i), dif_pos (h1 j), e, e]

def levelFromCompactRepresentations (k0 r : ℕ) (Hp Hq : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [FiniteDimensional ℂ Hp]
    [NormedAddCommGroup Hq] [InnerProductSpace ℂ Hq] [FiniteDimensional ℂ Hq]
    (σ : Matrix (Fin (k0 + 1)) (Fin (k0 + 1)) ℂ → (Hp →L[ℂ] Hp))
    (σ' : Matrix (Fin (k0 + 1)) (Fin (k0 + 1)) ℂ → (Hq →L[ℂ] Hq)) : Lev where
  k0 := k0
  r := r
  z := negativeBasisVector k0 r
  z' := negativeBasisVector k0 r
  Wp := Hp
  Wq := Hq
  π := fun g => σ (upperBlockOfMatrix k0 r g)
  π' := fun g => σ' (upperBlockOfMatrix k0 r g)
  μsec := bigCellSectionMatrix k0

section LG

variable (k0 r : ℕ) (Hp Hq : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [FiniteDimensional ℂ Hp]
    [NormedAddCommGroup Hq] [InnerProductSpace ℂ Hq] [FiniteDimensional ℂ Hq]
    (σ : Matrix (Fin (k0 + 1)) (Fin (k0 + 1)) ℂ → (Hp →L[ℂ] Hp))
    (σ' : Matrix (Fin (k0 + 1)) (Fin (k0 + 1)) ℂ → (Hq →L[ℂ] Hq))

theorem level_from_representations_standard : (levelFromCompactRepresentations k0 r Hp Hq σ σ').Std :=
  ⟨negative_basis_vector_mem_Wb k0 r, negative_basis_vector_mem_Wb k0 r, by show 0 < Tz (k0 + 1) r (negativeBasisVector k0 r); rw [hermitian_norm_negative_vector_eq_one]; norm_num,
    by show 0 < Tz (k0 + 1) r (negativeBasisVector k0 r); rw [hermitian_norm_negative_vector_eq_one]; norm_num, big_cell_section_negative_vector k0 r⟩

theorem block_rep_is_hc_type_W {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : Fin (k0 + 1) → ℝ)
    (τ : Matrix (Fin (k0 + 1)) (Fin (k0 + 1)) ℂ → (H →L[ℂ] H)) (hτ : Formalism.MainNotions.S.IsHCTypeU (k0 + 1) u τ) :
    Formalism.MainNotions.S.IsHCTypeW (k0 + 1) r (negativeBasisVector k0 r) u (fun g => τ (upperBlockOfMatrix k0 r g)) := by
  refine ⟨1, ⟨?_, fun a => ⟨by simp, by simp⟩, ?_⟩, ?_⟩
  · show (1 : Mat k0 r)ᴴ * _ * 1 = _
    simp
  · rw [hermitian_norm_negative_vector_eq_one]
    simp [negativeBasisVector]
  · simpa [upper_block_of_blockW_eq] using hτ

theorem level_from_reps_harish_chandra (u u' : Fin (k0 + 1) → ℝ) (h : Formalism.MainNotions.S.IsHCTypeU (k0 + 1) u σ)
    (h' : Formalism.MainNotions.S.IsHCTypeU (k0 + 1) u' σ') (hint : ∀ i, ∃ m : ℤ, u i - u' i = m) :
    (levelFromCompactRepresentations k0 r Hp Hq σ σ').HC u u' :=
  ⟨block_rep_is_hc_type_W k0 r u σ h, block_rep_is_hc_type_W k0 r u' σ' h', hint⟩

end LG

theorem standard_level_exists_all_ranks (k0 r : ℕ) : ∃ L : Lev, L.k0 = k0 ∧ L.r = r ∧ L.Std :=
  ⟨levelFromCompactRepresentations k0 r ℂ ℂ (fun _ => 0) (fun _ => 0), rfl, rfl, level_from_representations_standard _ _ _ _ _ _⟩

theorem low_part_rank_one_eq (x : ℝ) : lowK (Formalism.MainNotions.S.allPos 1) (fun _ => x) = fun _ => x := by
  funext a
  have h1 : ∀ a b : Fin 1, ¬ a < b := by decide
  simp [lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, h1]

theorem diagonal_torus_mem_maximal_compact (θ : Fin 1 → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset (Formalism.MainNotions.S.allPos 1) := by
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi; subst hj
    simp [Matrix.mul_apply, Matrix.star_apply, ← Complex.exp_conj, ← Complex.exp_add]
  · ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi; subst hj
    simp [Matrix.mul_apply, Formalism.REAL.Jm, Formalism.MainNotions.S.allPos]

def powerCharacterU1 (m : ℕ) : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ → (ℂ →L[ℂ] ℂ) :=
  fun h => (h 0 0) ^ m • ContinuousLinearMap.id ℂ ℂ

theorem character_power_is_hc_type_U1 (m : ℕ) : Formalism.MainNotions.S.IsHCTypeU (0 + 1) (fun _ => (m : ℝ)) (powerCharacterU1 m) := by
  have hσ : ∀ h, powerCharacterU1 m h = (h 0 0) ^ m • ContinuousLinearMap.id ℂ ℂ := fun _ => rfl
  generalize powerCharacterU1 m = σ at hσ
  refine ⟨inferInstance, inferInstance, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hσ]; ext; simp
  · intro a _ b _
    rw [hσ, hσ, hσ]
    ext
    simp [Matrix.mul_apply, mul_pow, mul_comm]
  · intro g hg v
    have h0 := congrFun (congrFun (show gᴴ * Formalism.REAL.Jm (Formalism.MainNotions.S.allPos 1) * g = _ from hg) 0) 0
    simp [Matrix.mul_apply, Formalism.REAL.Jm, Formalism.MainNotions.S.allPos] at h0
    have h1 : ‖g 0 0‖ = 1 := by
      have h2 : ((‖g 0 0‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [← h0]; push_cast; exact (Complex.conj_mul' (g 0 0)).symm
      have h3 : ‖g 0 0‖ ^ 2 = 1 := by exact_mod_cast h2
      nlinarith [norm_nonneg (g 0 0)]
    rw [hσ]
    simp [h1]
  · intro v
    simp only [hσ]
    refine Continuous.continuousOn ?_
    have : Continuous fun g : Matrix (Fin 1) (Fin 1) ℂ => g 0 0 := Continuous.matrix_elem continuous_id 0 0
    have h2 : Continuous fun g : Matrix (Fin 1) (Fin 1) ℂ => g 0 0 ^ m * v := (this.pow m).mul continuous_const
    simpa using h2
  · show Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos 1) σ (lowK (Formalism.MainNotions.S.allPos 1) fun _ => (m : ℝ)) ⊤
    rw [low_part_rank_one_eq]
    refine ⟨inferInstance, fun _ _ _ _ => Submodule.mem_top, fun S' _ _ => eq_bot_or_eq_top S', ⟨1, Submodule.mem_top, one_ne_zero, ?_⟩, ?_⟩
    · intro θ _
      rw [hσ]
      simp [← Complex.exp_nat_mul]
      congr 1
      ring
    · intro μ v _ hv hw
      refine ⟨0, fun a b h => absurd rfl h, ?_⟩
      simp only [Pi.zero_apply, Nat.cast_zero, zero_smul, Finset.sum_const_zero]
      by_contra hne
      have hd : (m : ℝ) - μ 0 ≠ 0 := by
        intro h
        apply hne
        funext a
        have ha : a = 0 := Subsingleton.elim _ _
        subst ha
        simpa using h
      have e := hw (fun _ => Real.pi / ((m : ℝ) - μ 0)) (diagonal_torus_mem_maximal_compact _)
      rw [hσ] at e
      simp [← Complex.exp_nat_mul] at e
      rcases e with e | e
      · have e2 : Complex.exp ((m : ℂ) * (((Real.pi / ((m : ℝ) - μ 0) : ℝ) : ℂ) * Complex.I) -
            ((μ 0 * (Real.pi / ((m : ℝ) - μ 0)) : ℝ) : ℂ) * Complex.I) = 1 := by
          rw [Complex.exp_sub]
          push_cast
          rw [e]
          exact div_self (Complex.exp_ne_zero _)
        have e3 : (m : ℂ) * (((Real.pi / ((m : ℝ) - μ 0) : ℝ) : ℂ) * Complex.I) -
            ((μ 0 * (Real.pi / ((m : ℝ) - μ 0)) : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I := by
          have hd' : ((m : ℂ) - (μ 0 : ℂ)) ≠ 0 := by exact_mod_cast hd
          push_cast
          field_simp
        rw [e3, Complex.exp_pi_mul_I] at e2
        norm_num at e2
      · exact hv e

def rankOneLevel (r m m' : ℕ) : Lev := levelFromCompactRepresentations 0 r ℂ ℂ (powerCharacterU1 m) (powerCharacterU1 m')

theorem cut_condition_zero_four : Formalism.MainNotions.S.IsCutS (fun _ : Fin (0 + 1) => ((0 : ℕ) : ℝ)) (fun _ => ((4 : ℕ) : ℝ)) (Set.Icc (-2) (-2)) := by
  refine ⟨0, -2, -2, by norm_num, le_rfl, rfl, by norm_num, by norm_num, ?_⟩
  intro y hy
  have : y = -2 := le_antisymm hy.2 hy.1
  subst this
  norm_num

theorem hyp_rank_one_level (r : ℕ) :
    HypC (rankOneLevel r 0 4) (fun _ => ((0 : ℕ) : ℝ)) (fun _ => ((4 : ℕ) : ℝ)) (Set.Icc (-2) (-2)) :=
  ⟨level_from_representations_standard _ _ _ _ _ _, level_from_reps_harish_chandra 0 r ℂ ℂ _ _ _ _ (character_power_is_hc_type_U1 0) (character_power_is_hc_type_U1 4) (fun _ => ⟨-4, by norm_num⟩), cut_condition_zero_four,
    ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩⟩

theorem hyp_level_nonempty (r : ℕ) : ∃ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), L.r = r ∧ HypC L u u' I :=
  ⟨rankOneLevel r 0 4, _, _, _, rfl, hyp_rank_one_level r⟩

def HighestWeightRepExists (k : ℕ) (u : Fin k → ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsHCTypeU k u σ

theorem highest_weight_rank_one (m : ℕ) : HighestWeightRepExists (0 + 1) (fun _ => (m : ℝ)) := ⟨ℂ, _, _, _, character_power_is_hc_type_U1 m⟩

theorem hyp_level_of_highest_weight (k0 r : ℕ) (u u' : Fin (k0 + 1) → ℝ) (I : Set ℝ) (h : HighestWeightRepExists (k0 + 1) u)
    (h' : HighestWeightRepExists (k0 + 1) u') (hint : ∀ i, ∃ m : ℤ, u i - u' i = m) (hI : Formalism.MainNotions.S.IsCutS u u' I)
    (hρ : ∃ ρ : Fin k0 → ℝ, Interlace u ρ ∧ Interlace u' ρ) :
    ∃ (L : Lev) (hk : L.k0 = k0), L.r = r ∧
      HypC L (fun i => u (Fin.cast (by rw [hk]) i)) (fun i => u' (Fin.cast (by rw [hk]) i)) I := by
  obtain ⟨H, i1, i2, σ, hσ⟩ := h
  obtain ⟨H', i1', i2', σ', hσ'⟩ := h'
  have := hσ.2.1
  have := hσ'.2.1
  exact ⟨levelFromCompactRepresentations k0 r H H' σ σ', rfl, rfl, level_from_representations_standard _ _ _ _ _ _, level_from_reps_harish_chandra k0 r H H' σ σ' u u' hσ hσ' hint, hI, hρ⟩

section Two

variable (k0 r : ℕ) (Hp Hq : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [FiniteDimensional ℂ Hp]
    [NormedAddCommGroup Hq] [InnerProductSpace ℂ Hq] [FiniteDimensional ℂ Hq]
    (σ : Matrix (Fin (k0 + 1)) (Fin (k0 + 1)) ℂ → (Hp →L[ℂ] Hp))
    (σ' : Matrix (Fin (k0 + 1)) (Fin (k0 + 1)) ℂ → (Hq →L[ℂ] Hq))

theorem negative_basis_vector_restrict_level (i r' : ℕ) (h : i + r' = r) :
    (fun p : Fin (2 * r' + (k0 + 1) + 1) => negativeBasisVector k0 r ⟨p.val + i, by omega⟩) = negativeBasisVector k0 r' := by
  funext p
  simp only [negativeBasisVector, bvec, Pi.single_apply, wI, Fin.ext_iff, Fin.val_last]
  congr 1
  apply propext
  omega

theorem upper_block_restrict_down_eq (i r' : ℕ) (h : i + r' = r) (g : Mat k0 r') :
    upperBlockOfMatrix k0 r (fun p q => ιLev (k0 + 1) i r' g (Fin.cast (by omega) p) (Fin.cast (by omega) q)) =
      upperBlockOfMatrix k0 r' g := by
  funext a b
  have h1 : ∀ a : Fin (k0 + 1), i ≤ (wI (k0 + 1) r a.castSucc).val ∧
      (wI (k0 + 1) r a.castSucc).val < 2 * r' + (k0 + 1) + 1 + i := by
    intro a
    have := a.2
    simp only [wI, Fin.val_castSucc]
    omega
  have e : ∀ (a : Fin (k0 + 1)) (p : (wI (k0 + 1) r a.castSucc).val - i < 2 * r' + (k0 + 1) + 1),
      (⟨(wI (k0 + 1) r a.castSucc).val - i, p⟩ : Fin (2 * r' + (k0 + 1) + 1)) = wI (k0 + 1) r' a.castSucc :=
    fun a p => Fin.ext (by simp only [wI, Fin.val_castSucc]; omega)
  unfold upperBlockOfMatrix ιLev
  simp only [Fin.val_cast]
  rw [dif_pos (h1 a), dif_pos (h1 b), e, e]

theorem level_from_reps_restrict_down (i r' : ℕ) (h : i + r' = r) :
    (levelFromCompactRepresentations k0 r Hp Hq σ σ').down i r' h = levelFromCompactRepresentations k0 r' Hp Hq σ σ' := by
  have hz := negative_basis_vector_restrict_level k0 r i r' h
  have hb := upper_block_restrict_down_eq k0 r i r' h
  unfold Lev.down levelFromCompactRepresentations
  simp only [hz, hb]

theorem hyp_transport_along_level_eq (L : Lev) (e : L = levelFromCompactRepresentations k0 r Hp Hq σ σ') (u u' : Fin (k0 + 1) → ℝ) (I : Set ℝ)
    (H : HypC (levelFromCompactRepresentations k0 r Hp Hq σ σ') u u' I) :
    ∃ hk : L.k0 = k0, HypC L (fun i => u (Fin.cast (by rw [hk]) i)) (fun i => u' (Fin.cast (by rw [hk]) i)) I := by
  subst e
  exact ⟨rfl, H⟩

variable (u u' : Fin (k0 + 1) → ℝ) (I : Set ℝ)

theorem level_from_reps_hyp (hσ : Formalism.MainNotions.S.IsHCTypeU (k0 + 1) u σ) (hσ' : Formalism.MainNotions.S.IsHCTypeU (k0 + 1) u' σ')
    (hint : ∀ i, ∃ m : ℤ, u i - u' i = m) (hI : Formalism.MainNotions.S.IsCutS u u' I)
    (hρ : ∃ ρ : Fin k0 → ℝ, Interlace u ρ ∧ Interlace u' ρ) : HypC (levelFromCompactRepresentations k0 r Hp Hq σ σ') u u' I :=
  ⟨level_from_representations_standard _ _ _ _ _ _, level_from_reps_harish_chandra k0 r Hp Hq σ σ' u u' hσ hσ' hint, hI, hρ⟩

theorem level_from_reps_hyp_restrict_down (hσ : Formalism.MainNotions.S.IsHCTypeU (k0 + 1) u σ) (hσ' : Formalism.MainNotions.S.IsHCTypeU (k0 + 1) u' σ')
    (hint : ∀ i, ∃ m : ℤ, u i - u' i = m) (hI : Formalism.MainNotions.S.IsCutS u u' I)
    (hρ : ∃ ρ : Fin k0 → ℝ, Interlace u ρ ∧ Interlace u' ρ) (i r' : ℕ) (h : i + r' = r) :
    HypC ((levelFromCompactRepresentations k0 r Hp Hq σ σ').down i r' h) u u' I := by
  obtain ⟨_, H''⟩ := hyp_transport_along_level_eq k0 r' Hp Hq σ σ' _ (level_from_reps_restrict_down k0 r Hp Hq σ σ' i r' h) u u' I
    (level_from_reps_hyp k0 r' Hp Hq σ σ' u u' I hσ hσ' hint hI hρ)
  exact H''

theorem negative_basis_vector_lift_rank : liftVectorLevel (negativeBasisVector k0 r) = negativeBasisVector k0 (r + 1) := by
  funext p
  have hp := p.2
  simp only [liftVectorLevel, liftVec, negativeBasisVector, bvec, Pi.single_apply, wI, Fin.ext_iff, Fin.val_last, Fin.val_cast]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem upper_block_lift_rank_eq (g : Mat k0 r) : upperBlockOfMatrix k0 (r + 1) (ι1 g) = upperBlockOfMatrix k0 r g := by
  funext a b
  have h1 : ∀ a : Fin (k0 + 1), 1 ≤ (wI (k0 + 1) (r + 1) a.castSucc).val ∧
      (wI (k0 + 1) (r + 1) a.castSucc).val < 2 * r + (k0 + 1) + 1 + 1 := by
    intro a
    have := a.2
    simp only [wI, Fin.val_castSucc]
    omega
  have e : ∀ (a : Fin (k0 + 1)) (p : (wI (k0 + 1) (r + 1) a.castSucc).val - 1 < 2 * r + (k0 + 1) + 1),
      (⟨(wI (k0 + 1) (r + 1) a.castSucc).val - 1, p⟩ : Fin (2 * r + (k0 + 1) + 1)) = wI (k0 + 1) r a.castSucc :=
    fun a p => Fin.ext (by simp only [wI, Fin.val_castSucc]; omega)
  unfold upperBlockOfMatrix ι1 ιLev
  simp only [Fin.val_cast]
  rw [dif_pos (h1 a), dif_pos (h1 b), e, e]

theorem level_from_reps_lift_rank : (levelFromCompactRepresentations k0 r Hp Hq σ σ').up (fun g => σ (upperBlockOfMatrix k0 (r + 1) g)) (fun g => σ' (upperBlockOfMatrix k0 (r + 1) g)) =
    levelFromCompactRepresentations k0 (r + 1) Hp Hq σ σ' := by
  have hz := negative_basis_vector_lift_rank k0 r
  unfold Lev.up levelFromCompactRepresentations
  simp only [hz]

theorem level_from_reps_compatible : (levelFromCompactRepresentations k0 r Hp Hq σ σ').Compat (fun g => σ (upperBlockOfMatrix k0 (r + 1) g))
    (fun g => σ' (upperBlockOfMatrix k0 (r + 1) g)) := by
  intro g
  have hb := upper_block_lift_rank_eq k0 r g
  exact ⟨by show σ (upperBlockOfMatrix k0 r g) = σ (upperBlockOfMatrix k0 (r + 1) (ι1 g)); rw [hb],
    by show σ' (upperBlockOfMatrix k0 r g) = σ' (upperBlockOfMatrix k0 (r + 1) (ι1 g)); rw [hb]⟩

theorem level_from_reps_hyp_lift_rank (hσ : Formalism.MainNotions.S.IsHCTypeU (k0 + 1) u σ) (hσ' : Formalism.MainNotions.S.IsHCTypeU (k0 + 1) u' σ')
    (hint : ∀ i, ∃ m : ℤ, u i - u' i = m) (hI : Formalism.MainNotions.S.IsCutS u u' I)
    (hρ : ∃ ρ : Fin k0 → ℝ, Interlace u ρ ∧ Interlace u' ρ) :
    HypC ((levelFromCompactRepresentations k0 r Hp Hq σ σ').up (fun g => σ (upperBlockOfMatrix k0 (r + 1) g)) (fun g => σ' (upperBlockOfMatrix k0 (r + 1) g))) u u' I := by
  obtain ⟨_, H''⟩ := hyp_transport_along_level_eq k0 (r + 1) Hp Hq σ σ' _ (level_from_reps_lift_rank k0 r Hp Hq σ σ') u u' I
    (level_from_reps_hyp k0 (r + 1) Hp Hq σ σ' u u' I hσ hσ' hint hI hρ)
  exact H''

end Two

theorem hyp_two_levels_exist (r : ℕ) : ∃ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r),
    Lt.r = r ∧ HypC Lt u u' I ∧ HypC (Lt.down Lt.r 0 hr) u u' I :=
  ⟨rankOneLevel r 0 4, _, _, _, rfl, rfl, hyp_rank_one_level r,
    level_from_reps_hyp_restrict_down 0 r ℂ ℂ _ _ _ _ _ (character_power_is_hc_type_U1 0) (character_power_is_hc_type_U1 4) (fun _ => ⟨-4, by norm_num⟩) cut_condition_zero_four
      ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩ r 0 rfl⟩

theorem hyp_lifted_levels_exist (r : ℕ) : ∃ (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp))
    (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq)) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ),
    L.r = r ∧ L.Std ∧ L.Compat pb pb' ∧ HypC (L.up pb pb') u u' I :=
  ⟨rankOneLevel r 0 4, _, _, _, _, _, rfl, level_from_representations_standard _ _ _ _ _ _, level_from_reps_compatible 0 r ℂ ℂ _ _,
    level_from_reps_hyp_lift_rank 0 r ℂ ℂ _ _ _ _ _ (character_power_is_hc_type_U1 0) (character_power_is_hc_type_U1 4) (fun _ => ⟨-4, by norm_num⟩) cut_condition_zero_four
      ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩⟩

def HighestWeightTheoremUnitary (k : ℕ) : Prop := ∀ u : Fin k → ℝ, IsHCParam u → HighestWeightRepExists k u

theorem hc_parameters_interlacing_exist (k0 : ℕ) : ∃ (u u' : Fin (k0 + 1) → ℝ) (I : Set ℝ), IsHCParam u ∧ IsHCParam u' ∧
    (∀ i, ∃ m : ℤ, u i - u' i = m) ∧ Formalism.MainNotions.S.IsCutS u u' I ∧ ∃ ρ : Fin k0 → ℝ, Interlace u ρ ∧ Interlace u' ρ := by
  refine ⟨fun i => (k0 : ℝ) / 2 - 10 * (i : ℕ), fun i => (k0 : ℝ) / 2 - 10 * (i : ℕ) + 4,
    Set.Icc (-((k0 : ℝ) / 2) - 2) (-((k0 : ℝ) / 2) - 2), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a b hab
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    show (k0 : ℝ) / 2 - 10 * (b : ℕ) < (k0 : ℝ) / 2 - 10 * (a : ℕ)
    linarith
  · intro a
    exact ⟨-10 * ((a : ℕ) : ℤ), by push_cast; ring⟩
  · intro a b hab
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    show (k0 : ℝ) / 2 - 10 * (b : ℕ) + 4 < (k0 : ℝ) / 2 - 10 * (a : ℕ) + 4
    linarith
  · intro a
    exact ⟨-10 * ((a : ℕ) : ℤ) + 4, by push_cast; ring⟩
  · intro i
    exact ⟨-4, by push_cast; ring⟩
  · refine ⟨0, _, _, ?_, le_rfl, rfl, ?_, ?_, ?_⟩
    · simp
    · simp only [Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero]
      rw [min_eq_right (by linarith)]
      linarith
    · simp only [Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero]
      rw [max_eq_left (by linarith)]
      linarith
    · intro y hy
      have : y = -((k0 : ℝ) / 2) - 2 := le_antisymm hy.2 hy.1
      subst this
      simp only [Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero]
      constructor
      · rw [show -((k0 : ℝ) / 2) - 2 + (k0 : ℝ) / 2 = -2 by ring]; norm_num
      · rw [show -((k0 : ℝ) / 2) - 2 + ((k0 : ℝ) / 2 + 4) = 2 by ring]; norm_num
  · refine ⟨fun j => (k0 : ℝ) / 2 - 10 * (j : ℕ) - 3, fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩ <;>
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] <;> linarith

theorem hyp_level_exists_highest_weight (k0 r : ℕ) (h : HighestWeightTheoremUnitary (k0 + 1)) :
    ∃ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), L.k0 = k0 ∧ L.r = r ∧ HypC L u u' I := by
  obtain ⟨u, u', I, hu, hu', hint, hI, hρ⟩ := hc_parameters_interlacing_exist k0
  obtain ⟨L, hk, hr, H⟩ := hyp_level_of_highest_weight k0 r u u' I (h u hu) (h u' hu') hint hI hρ
  exact ⟨L, _, _, I, hk, hr, H⟩

theorem degenerate_context_frame_datum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Base E) (r : ℕ)
    (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    (degenerateContext B r).IsFrameDatum h SS :=
  ⟨fun _ _ _ hφ => absurd hφ (Set.notMem_empty _), fun _ hx => absurd hx (Set.notMem_empty _),
    fun _ hx => absurd hx (Set.notMem_empty _), fun _ _ hx => absurd hx (Set.notMem_empty _)⟩

theorem idempotent_connection_algebra {A : Type*} [Ring A] (P D a h : A) (hP : P * P = P) (hD : D = D * P + P * D)
    (hh : h = P * a * P + P * D * (1 - P) - (1 - P) * D * P) :
    D + h * P = P * h ∧ (1 - P) * h * (1 - P) = 0 ∧ P * h * P = P * a * P := by
  have hPDP : P * D * P = 0 := by
    have e : P * D * P = P * D * P + P * D * P := by
      calc P * D * P = P * (D * P + P * D) * P := by rw [← hD]
        _ = P * D * (P * P) + (P * P) * D * P := by noncomm_ring
        _ = P * D * P + P * D * P := by rw [hP]
    exact left_eq_add.mp e
  have e0 : h = P * a * P + P * D - D * P := by
    calc h = P * a * P + P * D - P * D * P - D * P + P * D * P := by rw [hh]; noncomm_ring
      _ = P * a * P + P * D - D * P := by rw [hPDP]; simp
  have e1 : h * P = P * a * P - D * P := by
    calc h * P = P * a * (P * P) + P * D * P - D * (P * P) := by rw [e0]; noncomm_ring
      _ = P * a * P - D * P := by rw [hP, hPDP]; simp
  have e2 : P * h = P * a * P + P * D := by
    calc P * h = (P * P) * a * P + (P * P) * D - P * D * P := by rw [e0]; noncomm_ring
      _ = P * a * P + P * D := by rw [hP, hPDP]; simp
  have hD2 : D - D * P = P * D := by
    rw [sub_eq_iff_eq_add, add_comm]; exact hD
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, e2]
    calc D + (P * a * P - D * P) = P * a * P + (D - D * P) := by abel
      _ = P * a * P + P * D := by rw [hD2]
  · calc (1 - P) * h * (1 - P) = h - h * P - P * h + P * (h * P) := by noncomm_ring
      _ = h - (P * a * P - D * P) - (P * a * P + P * D) + P * (P * a * P - D * P) := by rw [e1, e2]
      _ = (P * a * P + P * D - D * P) - (P * a * P - D * P) - (P * a * P + P * D) + P * (P * a * P - D * P) := by
          rw [← e0]
      _ = -(P * a * P) + (P * P) * a * P - P * D * P := by noncomm_ring
      _ = 0 := by rw [hP, hPDP]; simp
  · calc P * h * P = P * (h * P) := by noncomm_ring
      _ = (P * P) * a * P - P * D * P := by rw [e1]; noncomm_ring
      _ = P * a * P := by rw [hP, hPDP]; simp

theorem projection_frame_connection_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ} (C : Ctx B r)
    (a dP : (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (hid : ∀ x ∈ C.Dom, C.PiL x * C.PiL x = C.PiL x)
    (hd : ∀ x ∈ C.Dom, ∀ e : E, dZ r (fun y => C.PiL y e) x = dP x e)
    (hl : ∀ x ∈ C.Dom, dP x = dP x * C.PiL x + C.PiL x * dP x) :
    ∃ h : (Fin (r + 1) → ℂ) → E →L[ℂ] E,
      (∀ x ∈ C.Dom, ∀ e : E, dZ r (fun y => C.PiL y e) x + h x (C.PiL x e) = C.PiL x (h x e)) ∧
      (∀ x ∈ C.Dom, ∀ e : E, h x (e - C.PiL x e) - C.PiL x (h x (e - C.PiL x e)) = 0) ∧
      ∀ x ∈ C.Dom, C.PiL x * h x * C.PiL x = C.PiL x * a x * C.PiL x := by
  refine ⟨fun x => C.PiL x * a x * C.PiL x + C.PiL x * dP x * (1 - C.PiL x) - (1 - C.PiL x) * dP x * C.PiL x,
    fun x hx e => ?_, fun x hx e => ?_, fun x hx => ?_⟩
  · have k := (idempotent_connection_algebra (C.PiL x) (dP x) (a x) _ (hid x hx) (hl x hx) rfl).1
    have k2 := congrArg (fun T : E →L[ℂ] E => T e) k
    rw [hd x hx e]
    simpa using k2
  · have k := (idempotent_connection_algebra (C.PiL x) (dP x) (a x) _ (hid x hx) (hl x hx) rfl).2.1
    have k2 := congrArg (fun T : E →L[ℂ] E => T e) k
    simpa using k2
  · exact (idempotent_connection_algebra (C.PiL x) (dP x) (a x) _ (hid x hx) (hl x hx) rfl).2.2

theorem standard_datum_of_level_data (D : Formalism.BasicNotions.D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS) (I : Set ℝ)
    (hε : ∀ i, L.ε i = epsSH D.R (Fin.cast (by rw [hk]) i)) (hc : L.c = cStd)
    (hz : L.z = negativeBasisVector k0 D.R.rS) (hz' : L.z' = negativeBasisVector k0 D.R.rS) (hI : Formalism.MainNotions.S.IsCutS L.u L.u' I)
    (hρ : ∃ ρ : Fin k0 → ℝ, Interlace L.u ρ ∧ Interlace L.u' ρ) : UnitaryLevelOperators.Std D hk L (bigCellSectionMatrix k0) I :=
  ⟨hε, hc, by rw [hz, hz']; exact big_cell_section_negative_vector k0 D.R.rS, hI, hρ⟩

section GenSec

theorem big_cell_section_properties (k0 : ℕ) :
    (∀ i j, ContDiffOn ℝ ∞ (fun ζ => bigCellSectionMatrix k0 ζ i j) {ζ : ℂ | 1 < Complex.normSq ζ}) ∧
    ∀ ζ : ℂ, 1 < Complex.normSq ζ → (bigCellSectionMatrix k0 ζ)ᴴ * Hb (k0 + 1) * bigCellSectionMatrix k0 ζ = Hb (k0 + 1) ∧
      herm (Hb (k0 + 1)) (bigCellSectionMatrix k0 ζ *ᵥ bvec (Fin.last (k0 + 1))) (bvec (Fin.last (k0 + 1))) = ζ := by
  have h := big_cell_section_negative_vector k0 0
  unfold IsSection at h
  rw [hermitian_norm_negative_vector_eq_one, definite_part_negative_vector] at h
  simpa only [mul_one] using h

variable (k r : ℕ)

theorem middle_block_index_injective : Function.Injective (wI k r) := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simpa [wI] using this)

theorem outside_middle_block_index (m : Fin (2 * r + k + 1)) (hm : m ∉ Set.range (wI k r)) : m.val < r ∨ r + k < m.val := by
  by_contra hc
  apply hm
  exact ⟨⟨m.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩

theorem hermitian_form_dual_basis_row (a : Fin r) (m : Fin (2 * r + k + 1)) : Hpk k r (esI k r a) m = if m = eI k r a then 1 else 0 := by
  have := a.2
  have := m.2
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hermitian_form_basis_row (a : Fin r) (m : Fin (2 * r + k + 1)) : Hpk k r (eI k r a) m = if m = esI k r a then 1 else 0 := by
  have := a.2
  have := m.2
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem split_form_middle_block_eq (i j : Fin (k + 1)) : Hpk k r (wI k r i) (wI k r j) = Hb k i j := by
  have hi := i.2
  have hj := j.2
  unfold Hpk Hb
  rw [Matrix.diagonal_apply, if_neg (by simp only [wI]; omega), if_neg (by simp only [wI]; omega)]
  by_cases hij : i = j
  · subst hij
    rw [if_pos ⟨by simp only [wI]; omega, by simp only [wI]; omega, rfl⟩, if_pos rfl]
    by_cases hl : i = Fin.last k
    · rw [if_pos hl, if_pos (by rw [hl]; simp [wI])]
    · rw [if_neg hl, if_neg (by
        intro h
        apply hl
        apply Fin.ext
        simp only [wI] at h
        simp only [Fin.val_last]
        omega)]
  · rw [if_neg hij, if_neg (fun h => hij (middle_block_index_injective k r h.2.2))]

theorem conjugate_form_entry_of_fixed_column {n : ℕ} (g H : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (hcol : ∀ l, g l p = if l = p then 1 else 0) :
    (gᴴ * H * g) p q = ∑ m, H p m * g m q := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  simp [apply_ite]

theorem column_eq_basis_of_fixes_vector {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) (h : g *ᵥ bvec c = bvec c) (l : Fin n) :
    g l c = if l = c then 1 else 0 := by
  have e := congrFun h l
  simpa [bvec, Matrix.mulVec, dotProduct, Pi.single_apply] using e

variable {k r}

theorem fixed_frame_zero_off_middle_block (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : g ∈ UH (Hpk k r))
    (hfix : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (m : Fin (2 * r + k + 1)) (hm : m ∉ Set.range (wI k r)) (j : Fin (k + 1)) : g m (wI k r j) = 0 := by
  have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
  have hj := j.2
  rcases outside_middle_block_index k r m hm with h | h
  ·
    have e := congrFun (congrFun hU' (esI k r ⟨m.val, h⟩)) (wI k r j)
    rw [conjugate_form_entry_of_fixed_column g _ _ _ (column_eq_basis_of_fixes_vector g _ (hfix ⟨m.val, h⟩).2)] at e
    simp only [hermitian_form_dual_basis_row] at e
    rw [if_neg (by simp only [wI, eI, Fin.ext_iff]; omega)] at e
    have hme : eI k r ⟨m.val, h⟩ = m := Fin.ext rfl
    rw [hme, Finset.sum_eq_single m (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, one_mul] at e
    exact e
  · have hm2 := m.2
    have ha : 2 * r + k - m.val < r := by omega
    have e := congrFun (congrFun hU' (eI k r ⟨2 * r + k - m.val, ha⟩)) (wI k r j)
    rw [conjugate_form_entry_of_fixed_column g _ _ _ (column_eq_basis_of_fixes_vector g _ (hfix ⟨2 * r + k - m.val, ha⟩).1)] at e
    simp only [hermitian_form_basis_row] at e
    rw [if_neg (by simp only [wI, esI, Fin.ext_iff]; omega)] at e
    have hme : esI k r ⟨2 * r + k - m.val, ha⟩ = m := Fin.ext (by simp only [esI]; omega)
    rw [hme, Finset.sum_eq_single m (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, one_mul] at e
    exact e

theorem frame_gives_unitary_block (z : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : Formalism.MainNotions.S.IsFrameW k r z g) :
    ∃ A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, Aᴴ * Hb k * A = Hb k ∧
      wbPart k r z = A *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (Fin.last k)) := by
  obtain ⟨hU, hfix, hz⟩ := hg
  have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
  have h0 := fixed_frame_zero_off_middle_block g hU hfix
  refine ⟨g.submatrix (wI k r) (wI k r), ?_, ?_⟩
  · ext i j
    have e := congrFun (congrFun hU' (wI k r i)) (wI k r j)
    rw [split_form_middle_block_eq] at e
    rw [← e]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
    refine Fintype.sum_of_injective (wI k r) (middle_block_index_injective k r) _ _ (fun m hm => by rw [h0 m hm j, mul_zero]) (fun b => ?_)
    congr 1
    refine Fintype.sum_of_injective (wI k r) (middle_block_index_injective k r) _ _ (fun l hl => by rw [h0 l hl i]; simp)
      (fun a => by rw [split_form_middle_block_eq])
  · conv_lhs => rw [← hz]
    funext i
    simp only [wbPart, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    symm
    refine Fintype.sum_of_injective (wI k r) (middle_block_index_injective k r) _ _ (fun m hm => ?_) (fun b => ?_)
    · have : m ≠ wI k r (Fin.last k) := fun h => hm ⟨_, h.symm⟩
      simp [bvec, this]
    · simp [bvec, Pi.single_apply, (middle_block_index_injective k r).eq_iff]

end GenSec

section GenSec2

theorem signature_form_sq_one (k : ℕ) : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem signature_form_conjTranspose_eq (k : ℕ) : (Hb k)ᴴ = Hb k := by
  unfold Hb
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem hermitian_form_unitary_invariant {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ * H * A = H) (x y : Fin n → ℂ) :
    herm H (A *ᵥ x) (A *ᵥ y) = herm H x y := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA]

theorem signature_form_inverse_facts {k : ℕ} (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hB : Bᴴ * Hb k * B = Hb k) :
    (Hb k * Bᴴ * Hb k) * B = 1 ∧ (Hb k * Bᴴ * Hb k)ᴴ * Hb k * (Hb k * Bᴴ * Hb k) = Hb k := by
  have h1 : (Hb k * Bᴴ * Hb k) * B = 1 := by
    calc (Hb k * Bᴴ * Hb k) * B = Hb k * (Bᴴ * Hb k * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hB, signature_form_sq_one]
  have h2 : B * (Hb k * Bᴴ * Hb k) = 1 := mul_eq_one_comm.mp h1
  refine ⟨h1, ?_⟩
  have h3 : (Hb k * Bᴴ * Hb k)ᴴ = Hb k * B * Hb k := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, signature_form_conjTranspose_eq, Matrix.mul_assoc]
  rw [h3]
  calc Hb k * B * Hb k * Hb k * (Hb k * Bᴴ * Hb k) = Hb k * (B * ((Hb k * Hb k) * (Hb k * Bᴴ * Hb k))) := by
        simp only [Matrix.mul_assoc]
    _ = Hb k := by rw [signature_form_sq_one, Matrix.one_mul, h2, Matrix.mul_one]

theorem big_cell_section_exists (k0 r : ℕ) (z z' : Vec k0 r) (hT : 0 < Tz (k0 + 1) r z) (hT' : 0 < Tz (k0 + 1) r z')
    (hf : ∃ g, Formalism.MainNotions.S.IsFrameW (k0 + 1) r z g) (hf' : ∃ g, Formalism.MainNotions.S.IsFrameW (k0 + 1) r z' g) :
    ∃ μsec, IsSection (k0 + 1) r z z' μsec := by
  obtain ⟨g, hg⟩ := hf
  obtain ⟨g', hg'⟩ := hf'
  obtain ⟨A, hA, hzA⟩ := frame_gives_unitary_block z g hg
  obtain ⟨B, hB, hzB⟩ := frame_gives_unitary_block z' g' hg'
  obtain ⟨hCB, hC⟩ := signature_form_inverse_facts B hB
  obtain ⟨hsm, hun⟩ := big_cell_section_properties k0
  set T := Tz (k0 + 1) r z with hTdef
  set T' := Tz (k0 + 1) r z' with hTdef'
  set C := Hb (k0 + 1) * Bᴴ * Hb (k0 + 1) with hCdef
  have hc0 : 0 < Real.sqrt T * Real.sqrt T' := mul_pos (Real.sqrt_pos.2 hT) (Real.sqrt_pos.2 hT')
  have hcc : (Real.sqrt T * Real.sqrt T') * (Real.sqrt T * Real.sqrt T') = T * T' := by
    calc _ = (Real.sqrt T * Real.sqrt T) * (Real.sqrt T' * Real.sqrt T') := by ring
      _ = T * T' := by rw [Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le]
  have hdom : ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
      1 < Complex.normSq (ζ * (((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ))⁻¹) := by
    intro ζ hζ
    rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal, hcc, ← div_eq_mul_inv, lt_div_iff₀ (mul_pos hT hT')]
    linarith
  refine ⟨fun ζ => A * bigCellSectionMatrix k0 (ζ * (((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ))⁻¹) * C, ?_, ?_⟩
  · intro i j
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine ContDiffOn.sum fun b _ => ContDiffOn.sum fun a _ => ?_
    refine (contDiffOn_const.mul ?_).mul contDiffOn_const
    exact (hsm a b).comp (contDiff_id.mul contDiff_const).contDiffOn (fun ζ hζ => hdom ζ hζ)
  · intro ζ hζ
    obtain ⟨hM, hv⟩ := hun _ (hdom ζ hζ)
    set M := bigCellSectionMatrix k0 (ζ * (((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ))⁻¹) with hMdef
    constructor
    · calc (A * M * C)ᴴ * Hb (k0 + 1) * (A * M * C) = Cᴴ * (Mᴴ * (Aᴴ * Hb (k0 + 1) * A) * M) * C := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Hb (k0 + 1) := by rw [hA, hM, hC]
    · rw [hzA, hzB, Matrix.mulVec_mulVec]
      have e1 : A * M * C * B = A * M := by rw [Matrix.mul_assoc, hCB, Matrix.mul_one]
      rw [e1, ← Matrix.mulVec_mulVec, hermitian_form_unitary_invariant _ A hA, Matrix.mulVec_smul]
      have e2 : ∀ (s t : ℝ) (x y : Fin (k0 + 1 + 1) → ℂ), herm (Hb (k0 + 1)) ((s : ℂ) • x) ((t : ℂ) • y) =
          ((t * s : ℝ) : ℂ) * herm (Hb (k0 + 1)) x y := by
        intro s t x y
        simp [herm, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, star_smul]
        ring
      rw [e2, hv]
      have hne : (((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hc0.ne'
      field_simp

theorem big_cell_section_of_hc (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (hT : 0 < L.T) (hT' : 0 < L.T') (h : L.HC u u') :
    ∃ μsec, IsSection (L.k0 + 1) L.r L.z L.z' μsec :=
  big_cell_section_exists L.k0 L.r L.z L.z' hT hT' (h.1.imp fun _ hg => hg.1) (h.2.1.imp fun _ hg => hg.1)

theorem big_cell_section_of_local_bessel {k0 r : ℕ} (L : LocBessel (k0 + 1) r) : ∃ μsec, IsSection (k0 + 1) r L.z L.z' μsec :=
  big_cell_section_exists k0 r L.z L.z' L.hz.2 L.hz'.2 (L.hπ.imp fun _ hg => hg.1) (L.hπ'.imp fun _ hg => hg.1)

end GenSec2

theorem hyp_of_local_bessel {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (I : Set ℝ) (hint : ∀ i, ∃ m : ℤ, L.u i - L.u' i = m)
    (hI : Formalism.MainNotions.S.IsCutS L.u L.u' I) (hρ : ∃ ρ : Fin k0 → ℝ, Interlace L.u ρ ∧ Interlace L.u' ρ) :
    ∃ μsec, HypC (UnitaryLevelOperators.levOf L μsec) L.u L.u' I := by
  obtain ⟨μ, hμ⟩ := big_cell_section_of_local_bessel L
  exact ⟨μ, ⟨L.hz.1, L.hz'.1, L.hz.2, L.hz'.2, hμ⟩, ⟨L.hπ, L.hπ', hint⟩, hI, hρ⟩

theorem exists_std_of_isCutS_of_interlace (D : Formalism.BasicNotions.D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS) (I : Set ℝ)
    (hε : ∀ i, L.ε i = epsSH D.R (Fin.cast (by rw [hk]) i)) (hc : L.c = cStd) (hI : Formalism.MainNotions.S.IsCutS L.u L.u' I)
    (hρ : ∃ ρ : Fin k0 → ℝ, Interlace L.u ρ ∧ Interlace L.u' ρ) : ∃ μsec, UnitaryLevelOperators.Std D hk L μsec I := by
  obtain ⟨μ, hμ⟩ := big_cell_section_of_local_bessel L
  exact ⟨μ, hε, hc, hμ, hI, hρ⟩

section HaarCompact

theorem left_multiplication_continuous {k r : ℕ} (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (lmulM (k := k) (r := r) s) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))

theorem haar_probability_compact_subgroup {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (h1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (iv : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hivc : Continuous iv) (hiv : ∀ a ∈ S, iv a ∈ S ∧ iv a * a = 1) (hc : IsCompact S) :
    ∃ μ : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn S μ ∧ μ Set.univ = 1 := by
  classical
  let G := {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ // g ∈ S}
  let iM : Mul G := ⟨fun a b => ⟨a.1 * b.1, hmul _ a.2 _ b.2⟩⟩
  let iO : One G := ⟨⟨1, h1⟩⟩
  let iI : Inv G := ⟨fun a => ⟨iv a.1, (hiv _ a.2).1⟩⟩
  let iG : Group G := Group.ofLeftAxioms (fun a b c => Subtype.ext (Matrix.mul_assoc _ _ _))
    (fun a => Subtype.ext (Matrix.one_mul _)) (fun a => Subtype.ext (hiv _ a.2).2)
  have : IsTopologicalGroup G :=
    { continuous_mul := Continuous.subtype_mk
        ((continuous_subtype_val.comp continuous_fst).matrix_mul (continuous_subtype_val.comp continuous_snd)) _
      continuous_inv := Continuous.subtype_mk (hivc.comp continuous_subtype_val) _ }
  have : CompactSpace G := isCompact_iff_compactSpace.mp hc
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let μG : Measure G := Measure.haarMeasure ⊤
  let f : G → Mt k r := fun a i j => a.1 i j
  have hf : Continuous f :=
    continuous_pi fun i => continuous_pi fun j => Continuous.matrix_elem continuous_subtype_val i j
  have hm : Measurable f := hf.measurable
  have hu : (μG.map f) Set.univ = 1 := by
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G))
    simpa using this
  have hp : IsProbabilityMeasure (μG.map f) := ⟨hu⟩
  refine ⟨μG.map f, ⟨inferInstance, IsProbabilityMeasure.ne_zero _, ?_, ?_⟩, hu⟩
  · have hr : MeasurableSet (Set.range f)ᶜ := (isCompact_range hf).isClosed.measurableSet.compl
    refine measure_mono_null (t := (Set.range f)ᶜ) ?_ ?_
    · rintro x hx ⟨y, rfl⟩
      exact hx y.2
    · rw [Measure.map_apply hm hr]
      have : f ⁻¹' (Set.range f)ᶜ = ∅ := by
        ext y; simp
      rw [this, measure_empty]
  · intro s hs
    have hcomp : lmulM (k := k) (r := r) s ∘ f = f ∘ (fun x : G => (⟨s, hs⟩ : G) * x) := rfl
    rw [Measure.map_map (left_multiplication_continuous s).measurable hm, hcomp,
      ← Measure.map_map hm (continuous_const_mul _).measurable, map_mul_left_eq_self]

variable (k r : ℕ)

theorem split_form_middle_row (c : Fin (k + 1)) (m : Fin (2 * r + k + 1)) :
    Hpk k r (wI k r c) m = if m = wI k r c then Hb k c c else 0 := by
  by_cases hm : m ∈ Set.range (wI k r)
  · obtain ⟨d, rfl⟩ := hm
    rw [split_form_middle_block_eq]
    by_cases hcd : d = c
    · rw [hcd, if_pos rfl]
    · rw [if_neg (fun h => hcd (middle_block_index_injective k r h))]
      unfold Hb
      rw [Matrix.diagonal_apply, if_neg (fun h => hcd h.symm)]
  · have hc := c.2
    have h1 := outside_middle_block_index k r m hm
    rw [if_neg (fun h => hm ⟨c, h.symm⟩)]
    unfold Hpk
    rw [if_neg (by simp only [wI]; omega), if_neg (by simp only [wI]; omega),
      if_neg (by
        rintro ⟨-, -, h⟩
        exact hm ⟨c, h⟩)]

theorem basis_index_trichotomy (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ a, i = esI k r a) ∨ ∃ c, i = wI k r c := by
  by_cases hi : i ∈ Set.range (wI k r)
  · obtain ⟨c, rfl⟩ := hi
    exact Or.inr (Or.inr ⟨c, rfl⟩)
  · have h2 := i.2
    rcases outside_middle_block_index k r i hi with h | h
    · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    · exact Or.inr (Or.inl ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp only [esI]; omega)⟩)

theorem signature_form_diag_sq_one (c : Fin (k + 1)) : Hb k c c * Hb k c c = 1 := by
  unfold Hb
  rw [Matrix.diagonal_apply_eq]
  split_ifs <;> norm_num

theorem split_form_matrix_sq_one : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  rcases basis_index_trichotomy k r i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨c, rfl⟩
  · simp only [hermitian_form_basis_row]
    rw [Finset.sum_eq_single (esI k r a) (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, one_mul, hermitian_form_dual_basis_row]
    simp only [eq_comm]
  · simp only [hermitian_form_dual_basis_row]
    rw [Finset.sum_eq_single (eI k r a) (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, one_mul, hermitian_form_basis_row]
    simp only [eq_comm]
  · simp only [split_form_middle_row]
    rw [Finset.sum_eq_single (wI k r c) (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, split_form_middle_row]
    by_cases hj : j = wI k r c
    · rw [if_pos hj, if_pos hj.symm, signature_form_diag_sq_one]
    · rw [if_neg hj, if_neg (fun h => hj h.symm), mul_zero]

variable {k r}

theorem one_mem_unitary_stabilizer_set (z : Fin (2 * r + k + 1) → ℂ) : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z :=
  ⟨by show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * _ * 1 = _; simp, fun a => ⟨by simp, by simp⟩, by simp⟩

theorem unitary_stabilizer_mul_mem (z : Fin (2 * r + k + 1) → ℂ) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (ha : a ∈ UWset k r z) (b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hb : b ∈ UWset k r z) :
    a * b ∈ UWset k r z := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have ha1' : aᴴ * Hpk k r * a = Hpk k r := ha1
  have hb1' : bᴴ * Hpk k r * b = Hpk k r := hb1
  refine ⟨?_, fun c => ⟨?_, ?_⟩, ?_⟩
  · show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha1', hb1']
  · rw [← Matrix.mulVec_mulVec, (hb2 c).1, (ha2 c).1]
  · rw [← Matrix.mulVec_mulVec, (hb2 c).2, (ha2 c).2]
  · rw [← Matrix.mulVec_mulVec, hb3, ha3]

theorem unitary_stabilizer_inv_mem (z : Fin (2 * r + k + 1) → ℂ) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (ha : a ∈ UWset k r z) : Hpk k r * aᴴ * Hpk k r ∈ UWset k r z ∧ (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  have ha1' : aᴴ * Hpk k r * a = Hpk k r := ha1
  have h1 : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc (Hpk k r * aᴴ * Hpk k r) * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha1', split_form_matrix_sq_one]
  have h2 : a * (Hpk k r * aᴴ * Hpk k r) = 1 := mul_eq_one_comm.mp h1
  have hfix : ∀ v : Fin (2 * r + k + 1) → ℂ, a *ᵥ v = v → (Hpk k r * aᴴ * Hpk k r) *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  refine ⟨⟨?_, fun c => ⟨hfix _ (ha2 c).1, hfix _ (ha2 c).2⟩, hfix _ ha3⟩, h1⟩
  show (Hpk k r * aᴴ * Hpk k r)ᴴ * Hpk k r * (Hpk k r * aᴴ * Hpk k r) = Hpk k r
  calc (Hpk k r * aᴴ * Hpk k r)ᴴ * Hpk k r * (Hpk k r * aᴴ * Hpk k r)
      = (Hpk k r * aᴴ * Hpk k r)ᴴ * (aᴴ * Hpk k r * a) * (Hpk k r * aᴴ * Hpk k r) := by rw [ha1']
    _ = (a * (Hpk k r * aᴴ * Hpk k r))ᴴ * Hpk k r * (a * (Hpk k r * aᴴ * Hpk k r)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2]; simp

theorem unitary_stabilizer_closed (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have hmv : ∀ v : Fin (2 * r + k + 1) → ℂ,
      IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g *ᵥ v = v} := fun v =>
    isClosed_eq (Continuous.matrix_mulVec continuous_id continuous_const) continuous_const
  have hu : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have e : UWset k r z = {g | gᴴ * Hpk k r * g = Hpk k r} ∩
      ((⋂ a : Fin r, ({g | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩ {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩
        {g | g *ᵥ z = z}) := by
    ext g
    simp only [UWset, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact hu.inter ((isClosed_iInter fun a => (hmv _).inter (hmv _)).inter (hmv _))

theorem middle_block_preserves_hermitian_form (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : g ∈ UH (Hpk k r))
    (hfix : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) :
    (g.submatrix (wI k r) (wI k r))ᴴ * Hb k * g.submatrix (wI k r) (wI k r) = Hb k := by
  have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
  have h0 := fixed_frame_zero_off_middle_block g hU hfix
  ext i j
  have e := congrFun (congrFun hU' (wI k r i)) (wI k r j)
  rw [split_form_middle_block_eq] at e
  rw [← e]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  refine Fintype.sum_of_injective (wI k r) (middle_block_index_injective k r) _ _ (fun m hm => by rw [h0 m hm j, mul_zero]) (fun b => ?_)
  congr 1
  refine Fintype.sum_of_injective (wI k r) (middle_block_index_injective k r) _ _ (fun l hl => by rw [h0 l hl i]; simp)
    (fun a => by rw [split_form_middle_block_eq])

theorem entries_norm_le_one_of_fixing_last (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : Aᴴ * Hb k * A = Hb k)
    (hcol : ∀ l, A l (Fin.last k) = if l = Fin.last k then 1 else 0) (d c : Fin (k + 1)) : ‖A d c‖ ≤ 1 := by
  by_cases hc : c = Fin.last k
  · rw [hc, hcol]
    split_ifs <;> simp
  · have hrow : ∀ m, Hb k (Fin.last k) m = if m = Fin.last k then -1 else 0 := by
      intro m
      unfold Hb
      rw [Matrix.diagonal_apply]
      by_cases hm : m = Fin.last k
      · rw [if_pos hm.symm, if_pos rfl, if_pos hm]
      · rw [if_neg (fun h => hm h.symm), if_neg hm]
    have e0 := congrFun (congrFun hA (Fin.last k)) c
    rw [conjugate_form_entry_of_fixed_column A _ _ _ hcol] at e0
    simp only [hrow] at e0
    rw [Finset.sum_eq_single (Fin.last k) (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, if_neg hc] at e0
    have hlast : A (Fin.last k) c = 0 := by simpa using e0
    have e1 := congrFun (congrFun hA c) c
    have hsum : (∑ x, (Complex.normSq (A x c) : ℂ)) = 1 := by
      have hcc : Hb k c c = 1 := by
        unfold Hb
        rw [Matrix.diagonal_apply_eq, if_neg hc]
      rw [hcc] at e1
      rw [← e1]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hin : (∑ l, star (A l c) * Hb k l x) = star (A x c) * Hb k x x := by
        rw [Finset.sum_eq_single x (fun b _ hb => by
          unfold Hb
          rw [Matrix.diagonal_apply, if_neg hb, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
      rw [hin]
      by_cases hx : x = Fin.last k
      · rw [hx, hlast]; simp
      · have hxx : Hb k x x = 1 := by
          unfold Hb
          rw [Matrix.diagonal_apply_eq, if_neg hx]
        rw [hxx, mul_one, Complex.normSq_eq_conj_mul_self]
        rfl
    have hsumR : (∑ x, Complex.normSq (A x c)) = 1 := by exact_mod_cast hsum
    have hle : Complex.normSq (A d c) ≤ 1 := by
      rw [← hsumR]
      exact Finset.single_le_sum (f := fun x => Complex.normSq (A x c)) (fun x _ => Complex.normSq_nonneg _)
        (Finset.mem_univ d)
    rw [Complex.normSq_eq_norm_sq] at hle
    nlinarith [norm_nonneg (A d c)]

theorem unitary_stabilizer_compact : IsCompact (UWset k r (bvec (wI k r (Fin.last k)))) := by
  have hsub : UWset k r (bvec (wI k r (Fin.last k))) ⊆
      Set.pi Set.univ (fun _ : Fin (2 * r + k + 1) => Set.pi Set.univ
        (fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1)) := by
    intro g hg i _ j _
    obtain ⟨hU, hfix, hz⟩ := hg
    rw [mem_closedBall_zero_iff]
    have hδ : ∀ (c : Fin (2 * r + k + 1)), g *ᵥ bvec c = bvec c → ‖g i c‖ ≤ 1 := by
      intro c hc
      rw [column_eq_basis_of_fixes_vector g c hc i]
      split_ifs <;> simp
    rcases basis_index_trichotomy k r j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨c, rfl⟩
    · exact hδ _ (hfix a).1
    · exact hδ _ (hfix a).2
    · by_cases hi : i ∈ Set.range (wI k r)
      · obtain ⟨d, rfl⟩ := hi
        exact entries_norm_le_one_of_fixing_last (g.submatrix (wI k r) (wI k r)) (middle_block_preserves_hermitian_form g hU hfix)
          (fun l => by
            rw [Matrix.submatrix_apply, column_eq_basis_of_fixes_vector g _ hz]
            simp only [(middle_block_index_injective k r).eq_iff]) d c
      · rw [fixed_frame_zero_off_middle_block g hU hfix i hi c]; simp
  exact IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1) (unitary_stabilizer_closed _) hsub

theorem unitary_stabilizer_haar_probability : ∃ μ : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (UWset k r (bvec (wI k r (Fin.last k)))) μ ∧
    μ Set.univ = 1 :=
  haar_probability_compact_subgroup _ (one_mem_unitary_stabilizer_set _) (unitary_stabilizer_mul_mem _) (fun a => Hpk k r * aᴴ * Hpk k r)
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const)
    (unitary_stabilizer_inv_mem _) unitary_stabilizer_compact

end HaarCompact

section HaarClosed

theorem haar_measure_closed_subgroup {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (h1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (iv : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hivc : Continuous iv) (hiv : ∀ a ∈ S, iv a ∈ S ∧ iv a * a = 1) (hc : IsClosed S) :
    ∃ μ : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn S μ := by
  classical
  have : LocallyCompactSpace (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  let G := {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ // g ∈ S}
  let iM : Mul G := ⟨fun a b => ⟨a.1 * b.1, hmul _ a.2 _ b.2⟩⟩
  let iO : One G := ⟨⟨1, h1⟩⟩
  let iI : Inv G := ⟨fun a => ⟨iv a.1, (hiv _ a.2).1⟩⟩
  let iG : Group G := Group.ofLeftAxioms (fun a b c => Subtype.ext (Matrix.mul_assoc _ _ _))
    (fun a => Subtype.ext (Matrix.one_mul _)) (fun a => Subtype.ext (hiv _ a.2).2)
  have : IsTopologicalGroup G :=
    { continuous_mul := Continuous.subtype_mk
        ((continuous_subtype_val.comp continuous_fst).matrix_mul (continuous_subtype_val.comp continuous_snd)) _
      continuous_inv := Continuous.subtype_mk (hivc.comp continuous_subtype_val) _ }
  have hce : Topology.IsClosedEmbedding (Subtype.val : G → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    hc.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace G := hce.locallyCompactSpace
  let _ : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let μG : Measure G := Measure.haar
  let f : G → Mt k r := fun a i j => a.1 i j
  have hfce : Topology.IsClosedEmbedding f := hce
  have hf : Continuous f := hfce.continuous
  have hm : Measurable f := hf.measurable
  have hfc : IsFiniteMeasureOnCompacts (μG.map f) :=
    ⟨fun K hK => by
      rw [Measure.map_apply hm hK.measurableSet]
      exact (hfce.isCompact_preimage hK).measure_lt_top⟩
  refine ⟨μG.map f, inferInstance, ?_, ?_, ?_⟩
  · intro h0
    have h2 : (μG.map f) Set.univ = 0 := by rw [h0]; simp
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ] at h2
    exact (isOpen_univ.measure_ne_zero μG ⟨1, trivial⟩) h2
  · have hr : MeasurableSet (Set.range f)ᶜ := hfce.isClosed_range.measurableSet.compl
    refine measure_mono_null (t := (Set.range f)ᶜ) ?_ ?_
    · rintro x hx ⟨y, rfl⟩
      exact hx y.2
    · rw [Measure.map_apply hm hr]
      have : f ⁻¹' (Set.range f)ᶜ = ∅ := by
        ext y; simp
      rw [this, measure_empty]
  · intro s hs
    have hcomp : lmulM (k := k) (r := r) s ∘ f = f ∘ (fun x : G => (⟨s, hs⟩ : G) * x) := rfl
    rw [Measure.map_map (left_multiplication_continuous s).measurable hm, hcomp,
      ← Measure.map_map hm (continuous_const_mul _).measurable, map_mul_left_eq_self]

variable {k r : ℕ}

def UnipotentEntryCondition (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) → g i j = if i = j then 1 else 0

theorem unipotent_radical_mem_iff (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ UnipotentEntryCondition k r g := by
  constructor
  · rintro ⟨hU, h1, h2⟩
    refine ⟨hU, fun i j hj hij => ?_⟩
    by_cases hjr : j.val < r
    · have e : j = eI k r ⟨j.val, hjr⟩ := Fin.ext rfl
      rw [e]
      exact h1 ⟨j.val, hjr⟩ i (by show j.val ≤ i.val; omega)
    · exact h2 i j (by omega) hj (by omega)
  · rintro ⟨hU, hP⟩
    refine ⟨hU, fun a i hai => hP i _ (by have := a.2; simp only [eI]; omega) (Or.inl hai),
      fun i j h1 h2 h3 => hP i j h2 (Or.inr h3)⟩

theorem unipotent_entry_condition_mul (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : UnipotentEntryCondition k r a)
    (hb : UnipotentEntryCondition k r b) : UnipotentEntryCondition k r (a * b) := by
  intro i j hj hij
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hb j j hj (Or.inl le_rfl), if_pos rfl, mul_one]
    exact ha i j hj hij
  · intro m _ hmj
    by_cases hm : j.val ≤ m.val ∨ r ≤ m.val
    · rw [hb m j hj hm, if_neg hmj, mul_zero]
    · rw [ha i m (by omega) (by omega), if_neg (by
        intro h
        have := congrArg Fin.val h
        omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem unipotent_entry_condition_inv (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hba : b * a = 1)
    (ha : UnipotentEntryCondition k r a) : UnipotentEntryCondition k r b := by
  have key : ∀ (n : ℕ) (i j : Fin (2 * r + k + 1)), j.val = n → j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) →
      b i j = if i = j then 1 else 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j hn hj hij
      have e := congrFun (congrFun hba i) j
      rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single j] at e
      · rw [ha j j hj (Or.inl le_rfl), if_pos rfl, mul_one] at e
        exact e
      · intro m _ hmj
        by_cases hm : j.val ≤ m.val ∨ r ≤ m.val
        · rw [ha m j hj hm, if_neg hmj, mul_zero]
        · rw [ih m.val (by omega) i m rfl (by omega) (by omega), if_neg (by
            intro h
            have := congrArg Fin.val h
            omega), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
  exact fun i j hj hij => key j.val i j rfl hj hij

theorem mul_mem_UH_Hpk_nonempty_parameter_models (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : a ∈ UH (Hpk k r))
    (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha1' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb1' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha1', hb1']

theorem unitary_group_inv_mem (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : a ∈ UH (Hpk k r)) :
    Hpk k r * aᴴ * Hpk k r ∈ UH (Hpk k r) ∧ (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
  have ha1' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc (Hpk k r * aᴴ * Hpk k r) * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha1', split_form_matrix_sq_one]
  have h2 : a * (Hpk k r * aᴴ * Hpk k r) = 1 := mul_eq_one_comm.mp h1
  refine ⟨?_, h1⟩
  show (Hpk k r * aᴴ * Hpk k r)ᴴ * Hpk k r * (Hpk k r * aᴴ * Hpk k r) = Hpk k r
  calc (Hpk k r * aᴴ * Hpk k r)ᴴ * Hpk k r * (Hpk k r * aᴴ * Hpk k r)
      = (Hpk k r * aᴴ * Hpk k r)ᴴ * (aᴴ * Hpk k r * a) * (Hpk k r * aᴴ * Hpk k r) := by rw [ha1']
    _ = (a * (Hpk k r * aᴴ * Hpk k r))ᴴ * Hpk k r * (a * (Hpk k r * aᴴ * Hpk k r)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2]; simp

theorem unipotent_radical_set_closed : IsClosed (Nset k r) := by
  have hu : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have hp : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | UnipotentEntryCondition k r g} := by
    unfold UnipotentEntryCondition
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (Continuous.matrix_elem continuous_id i j) continuous_const
  have e : Nset k r = {g | gᴴ * Hpk k r * g = Hpk k r} ∩ {g | UnipotentEntryCondition k r g} := by
    ext g
    exact unipotent_radical_mem_iff g
  rw [e]
  exact hu.inter hp

theorem unipotent_radical_haar_exists (k r : ℕ) : ∃ μ : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (Nset k r) μ :=
  haar_measure_closed_subgroup _
    ((unipotent_radical_mem_iff _).2 ⟨by show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * _ * 1 = _; simp,
      fun i j _ _ => Matrix.one_apply⟩)
    (fun a ha b hb => (unipotent_radical_mem_iff _).2 ⟨mul_mem_UH_Hpk_nonempty_parameter_models a b ((unipotent_radical_mem_iff a).1 ha).1 ((unipotent_radical_mem_iff b).1 hb).1,
      unipotent_entry_condition_mul a b ((unipotent_radical_mem_iff a).1 ha).2 ((unipotent_radical_mem_iff b).1 hb).2⟩)
    (fun a => Hpk k r * aᴴ * Hpk k r)
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const)
    (fun a ha => ⟨(unipotent_radical_mem_iff _).2 ⟨(unitary_group_inv_mem a ((unipotent_radical_mem_iff a).1 ha).1).1,
      unipotent_entry_condition_inv a _ (unitary_group_inv_mem a ((unipotent_radical_mem_iff a).1 ha).1).2 ((unipotent_radical_mem_iff a).1 ha).2⟩,
      (unitary_group_inv_mem a ((unipotent_radical_mem_iff a).1 ha).1).2⟩)
    unipotent_radical_set_closed

theorem unitary_stabilizer_haar_exists (z : Fin (2 * r + k + 1) → ℂ) : ∃ μ : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ :=
  haar_measure_closed_subgroup _ (one_mem_unitary_stabilizer_set _) (unitary_stabilizer_mul_mem _) (fun a => Hpk k r * aᴴ * Hpk k r)
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const)
    (unitary_stabilizer_inv_mem _) (unitary_stabilizer_closed _)

end HaarClosed

theorem haar_measure_ok_exists (L : Lev) : ∃ h : L.Haar, h.Ok := by
  obtain ⟨μW, hW⟩ := unitary_stabilizer_haar_exists (k := L.k0 + 1) (r := L.r) L.z
  obtain ⟨μN, hN⟩ := unipotent_radical_haar_exists (L.k0 + 1) L.r
  obtain ⟨μW', hW'⟩ := unitary_stabilizer_haar_exists (k := L.k0 + 1) (r := L.r) L.z'
  exact ⟨⟨μW, μN, μW'⟩, hW, hN, hW'⟩

theorem rank_one_level_full_bundle (r : ℕ) (C : ℝ) (N : ℕ) :
    ∃ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ) (h : L.Haar) (A : ℝ) (mm : ℕ),
      L.r = r ∧ HypC L u u' I ∧ h.Ok ∧ Big C L N A mm := by
  obtain ⟨h, hh⟩ := haar_measure_ok_exists (rankOneLevel r 0 4)
  obtain ⟨A, mm, hB⟩ := size_condition_exists C (rankOneLevel r 0 4) N
  exact ⟨_, _, _, _, h, A, mm, rfl, hyp_rank_one_level r, hh, hB⟩

end TopsChoicePartA

end Formalism.MainNotions.S.Inh
