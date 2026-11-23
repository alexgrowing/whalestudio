import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
open Matrix
namespace GlobalTheory.StdPar.UnipArch

section Lin

variable {A : Type} [CommRing A] {n r : ℕ}

theorem mem_span_cols_iff (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A) :
    y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) ↔ ∃ a : Fin r → A, (∀ l, l ∉ I → a l = 0) ∧ C *ᵥ a = y := by
  first
  | exact @_root_.GlobalTheory.ColumnSumLemma.main
  | exact _root_.GlobalTheory.ColumnSumLemma.main
  | (apply _root_.GlobalTheory.ColumnSumLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ColumnSumLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ColumnSumLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ColumnSumLemma.main ..)

variable (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
include hPt

theorem supp_mulVec (Q : Matrix (Fin r) (Fin r) A) (hQ : ∀ i l, Q i l ≠ 0 → P i l) (j : Fin r) (a : Fin r → A)
    (ha : ∀ l, ¬ P l j → a l = 0) : ∀ i, ¬ P i j → (Q *ᵥ a) i = 0 := by
  intro i hi
  show ∑ l, Q i l * a l = 0
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hq : Q i l = 0
  · rw [hq, zero_mul]
  · rw [ha l (fun h => hi (hPt i l j (hQ i l hq) h)), mul_zero]

include hPlt in
theorem supp_of_add (Q : Matrix (Fin r) (Fin r) A) (hQ : ∀ i l, Q i l ≠ 0 → P i l) (j : Fin r) (c : Fin r → A)
    (hd : ∀ i, ¬ P i j → (c + Q *ᵥ c) i = 0) : ∀ i, ¬ P i j → c i = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | _ i ih =>
  intro hi
  have h1 : (Q *ᵥ c) i = 0 := by
    show ∑ l, Q i l * c l = 0
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hq : Q i l = 0
    · rw [hq, zero_mul]
    · have hil := hQ i l hq
      rw [ih l (hPlt i l hil) (fun h => hi (hPt i l j hil h)), mul_zero]
  have := hd i hi
  rwa [Pi.add_apply, h1, add_zero] at this

include hPlt in

theorem core (C : Matrix (Fin n) (Fin r) A) (N : Matrix (Fin r) (Fin n) A) (T : Set (Fin r))
    (hN : ∀ i v, N i v ≠ 0 → i ∈ T) (hQ : ∀ i l, (N * C) i l ≠ 0 → P i l) :
    (∀ y, (1 + C * N) *ᵥ y - y ∈ Submodule.span A ((fun i => Cᵀ i) '' T)) ∧
    (∀ j, (1 + C * N) *ᵥ Cᵀ j - Cᵀ j ∈ Submodule.span A ((fun i => Cᵀ i) '' {i | P i j})) ∧
    (∀ j y, y ∈ Submodule.span A ((fun i => Cᵀ i) '' {i | P i j}) ↔
      (1 + C * N) *ᵥ y ∈ Submodule.span A ((fun i => Cᵀ i) '' {i | P i j})) := by
  have hD : ∀ y, (1 + C * N) *ᵥ y = y + C *ᵥ (N *ᵥ y) := fun y => by
    rw [add_mulVec, one_mulVec, mulVec_mulVec]
  have hcol : ∀ j, N *ᵥ Cᵀ j = fun i => (N * C) i j := fun j => by
    funext i
    simp [mulVec, dotProduct, mul_apply]
  refine ⟨fun y => ?_, fun j => ?_, fun j y => ?_⟩
  · rw [hD, add_sub_cancel_left]
    refine (mem_span_cols_iff C T _).2 ⟨N *ᵥ y, fun l hl => ?_, rfl⟩
    show ∑ v, N l v * y v = 0
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases h : N l v = 0
    · rw [h, zero_mul]
    · exact absurd (hN l v h) hl
  · rw [hD, add_sub_cancel_left, hcol]
    refine (mem_span_cols_iff C _ _).2 ⟨_, fun l hl => ?_, rfl⟩
    by_contra h
    exact hl (hQ l j h)
  · rw [mem_span_cols_iff, mem_span_cols_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a + (N * C) *ᵥ a, fun l hl => ?_, ?_⟩
      · rw [Pi.add_apply, ha l hl, supp_mulVec P hPt _ hQ j a (fun l h => ha l h) l hl, add_zero]
      · rw [hD]
        simp only [mulVec_add, mulVec_mulVec, Matrix.mul_assoc]
    · rintro ⟨b, hb, hy⟩
      have hd : N *ᵥ y + (N * C) *ᵥ (N *ᵥ y) = (N * C) *ᵥ b := by
        rw [← mulVec_mulVec, ← mulVec_add, ← hD, ← hy, mulVec_mulVec]
      have hc := supp_of_add P hPt hPlt _ hQ j (N *ᵥ y) (fun i hi => by
        rw [hd]; exact supp_mulVec P hPt _ hQ j b (fun l h => hb l h) i hi)
      refine ⟨b - N *ᵥ y, fun l hl => by rw [Pi.sub_apply, hb l hl, hc l hl, sub_zero], ?_⟩
      rw [mulVec_sub, hy, hD, add_sub_cancel_right]

end Lin

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.AutFunCompare (evW sgW)

variable (F) in

def inlA : Ainf F →ₗ[F] AF F := LinearMap.inl F (Ainf F) (Af F)

variable (F) in

def inrA : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)

variable (F E) in

def glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) : AF F ⊗[F] E :=
  (inlA F).rTensor E (∑ w, (sgW w).rTensor E (c w))

theorem map_evW_sum_sgW (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) (w : InfinitePlace F) :
    Algebra.TensorProduct.map (evW w) (AlgHom.id F E) (∑ w', (sgW w').rTensor E (c w')) = c w := by
  classical
  rw [map_sum, Finset.sum_eq_single w]
  · induction c w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show (evW w (sgW w a)) ⊗ₜ[F] x = a ⊗ₜ[F] x
      congr 1
      exact Pi.single_eq_same w a
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · intro w' _ hw'
    induction c w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show (evW w (sgW w' a)) ⊗ₜ[F] x = 0
      rw [show evW w (sgW w' a) = 0 from Pi.single_eq_of_ne (Ne.symm hw') a, TensorProduct.zero_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  · simp

theorem compInf_rTensor_inlA (z : Ainf F ⊗[F] E) (w : InfinitePlace F) :
    compInf F E w ((inlA F).rTensor E z) = Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem compInf_glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) (w : InfinitePlace F) :
    compInf F E w (glueInf F E c) = c w := by
  rw [glueInf, compInf_rTensor_inlA, map_evW_sum_sgW]

theorem sndA_rTensor_inlA (z : Ainf F ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((inlA F).rTensor E z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    show (sndA F (inlA F a)) ⊗ₜ[F] x = 0
    rw [show sndA F (inlA F a) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem sndA_glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glueInf F E c) = 0 :=
  sndA_rTensor_inlA _

@[simp] theorem glueInf_zero : glueInf F E (fun _ => 0) = 0 := by
  simp only [glueInf, map_zero, Finset.sum_const_zero]

theorem tens_ext {z z' : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w z = compInf F E w z')
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z = Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z') :
    z = z' := by
  have hz : ∀ z : AF F ⊗[F] E, z = (inlA F).rTensor E (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) +
      (inrA F).rTensor E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]
    | tmul x y =>
      show x ⊗ₜ[F] y = (inlA F (fstA F x)) ⊗ₜ[F] y + (inrA F (sndA F x)) ⊗ₜ[F] y
      rw [← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero _).symm (zero_add _).symm
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  have hc : ∀ (w : InfinitePlace F) (z : AF F ⊗[F] E), compInf F E w z =
      Algebra.TensorProduct.map (evW w) (AlgHom.id F E) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
    intro w z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul x y => rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  rw [hz z, hz z', h2, GlobalTheory.AutFunCompare.infTens_ext (fun w => (hc w z).symm.trans ((h1 w).trans (hc w z')))]

end Glue

section Main

end Main

end GlobalTheory.StdPar.UnipArch
