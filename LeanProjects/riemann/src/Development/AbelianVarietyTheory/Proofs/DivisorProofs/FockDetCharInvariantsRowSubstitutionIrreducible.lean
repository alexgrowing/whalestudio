import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalBasePtTopMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSubEqDetCharSmulOfMemInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigMatConjTransposeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors

noncomputable section
open MvPolynomial
namespace GlobalTheory.MinorFrame.RowIrr
open GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]

theorem exists_unitary_eval_ne {a d : ℕ} (h : a ≤ d) (P : Pol ι d a) (hP : P ≠ 0) :
    ∃ κ : ι → Matrix.unitaryGroup (Fin d) ℂ,
      eval (basePt ι d a) (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hP
  let f : Var ι d a → MvPolynomial (ι × Fin d × Fin d) ℂ := fun y => X (y.1, Fin.castLE h y.2.2, y.2.1)
  have key : ∀ (Q : Pol ι d a) (w : ι × Fin d × Fin d → ℂ),
      eval w (aeval f Q) = eval (fun y => eval w (f y)) Q := by
    intro Q w
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p y hp => simp only [map_mul, hp, aeval_X, eval_X]
  have hF0 : aeval f P = 0 := by
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := ι) (n := d) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
    simp only [Matrix.one_mul]
    rw [key]
    have hu' : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ := fun τ =>
      Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)
    have := hall (fun τ => ⟨u τ, hu' τ⟩)
    rw [eval_rowSub] at this
    refine (congrArg (fun F => eval F P) (funext fun y => ?_)).trans this
    simp only [f, eval_X]
    rw [Finset.sum_eq_single (Fin.castLE h y.2.2)]
    · simp [basePt]
    · intro b _ hb
      have : (b : ℕ) ≠ (y.2.2 : ℕ) := fun e => hb (Fin.ext (by simpa using e))
      simp [basePt, this]
    · simp
  refine MvPolynomial.funext fun z => ?_
  let w : ι × Fin d × Fin d → ℂ := fun x => if hr : (x.2.1 : ℕ) < a then z (x.1, x.2.2, ⟨x.2.1, hr⟩) else 0
  have := key P w
  rw [hF0, map_zero] at this
  rw [map_zero, this]
  exact congrArg (fun F => eval F P) (funext fun y => by simp [f, w])

theorem rowSub_lowScal_X {d a : ℕ} (t : ℂ) (y : Var ι d a) :
    (∑ i' : Fin d, C (lowScal d a t i' y.2.1) * (X (y.1, i', y.2.2) : Pol ι d a)) =
      C (if (y.2.1 : ℕ) < a then 1 else t) * X y := by
  obtain ⟨τ, i, j⟩ := y
  rw [Finset.sum_eq_single i]
  · simp [lowScal]
  · intro b _ hb
    simp [lowScal, Matrix.diagonal_apply_ne _ hb]
  · simp

def lowDeg {d a : ℕ} (s : Var ι d a →₀ ℕ) : ℕ := s.sum fun y e => if (y.2.1 : ℕ) < a then 0 else e

theorem rowSub_lowScal_monomial {d a : ℕ} (t : ℂ) (s : Var ι d a →₀ ℕ) (c : ℂ) :
    rowSub (fun _ => lowScal d a t) (monomial s c : Pol ι d a) = monomial s (c * t ^ lowDeg s) := by
  unfold rowSub
  rw [aeval_monomial]
  simp only [rowSub_lowScal_X, mul_pow, Finsupp.prod_mul]
  have h1 : (s.prod fun y k => (C (if (y.2.1 : ℕ) < a then 1 else t) : Pol ι d a) ^ k) = C (t ^ lowDeg s) := by
    unfold Finsupp.prod lowDeg Finsupp.sum
    rw [← Finset.prod_pow_eq_pow_sum, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    beta_reduce
    split_ifs <;> simp
  rw [h1, ← monomial_eq, algebraMap_eq, C_mul_monomial]

theorem lowDeg_le {d a : ℕ} (s : Var ι d a →₀ ℕ) : lowDeg s ≤ s.sum fun _ e => e := by
  unfold lowDeg Finsupp.sum
  exact Finset.sum_le_sum fun y _ => by beta_reduce; split_ifs <;> omega

theorem lowScal_mem_unitary {d a : ℕ} {t : ℂ} (ht : ‖t‖ = 1) : lowScal d a t ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [lowScal, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.star_apply]
  by_cases hi : (i : ℕ) < a
  · simp [hi]
  · simp only [hi, if_false, RCLike.star_def]
    rw [Complex.conj_mul', ht]; simp

theorem rowSub_lowScal_zero_mem {a d : ℕ} (S : Submodule ℂ (Pol ι d a))
    (hS : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ S, rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ S)
    (P : Pol ι d a) (hP : P ∈ S) : rowSub (fun _ => lowScal d a 0) P ∈ S := by
  set M := P.totalDegree + 1 with hMdef
  have hM : M ≠ 0 := by omega
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / M)
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM
  have hωn : ∀ k : ℕ, ‖ω ^ k‖ = 1 := fun k => by rw [norm_pow, hω.norm'_eq_one hM, one_pow]
  have heq : rowSub (fun _ => lowScal d a 0) P =
      ∑ k ∈ Finset.range M, (M : ℂ)⁻¹ • rowSub (fun _ => lowScal d a (ω ^ k)) P := by
    conv_lhs => rw [as_sum P]
    conv_rhs => rw [as_sum P]
    simp only [map_sum, rowSub_lowScal_monomial, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.sum_congr rfl (fun x _ => by rw [smul_monomial]), ← map_sum]
    congr 1
    have hb : lowDeg s < M := lt_of_le_of_lt (lowDeg_le s) (by have := le_totalDegree hs; omega)
    have hx : ∀ x : ℕ, (ω ^ x) ^ lowDeg s = (ω ^ lowDeg s) ^ x := fun x => by rw [← pow_mul, ← pow_mul, mul_comm]
    simp_rw [hx, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
    by_cases hb0 : lowDeg s = 0
    · simp only [hb0, pow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      field_simp
    · have hne : ω ^ lowDeg s ≠ 1 := hω.pow_ne_one_of_pos_of_lt hb0 hb
      rw [geom_sum_eq hne, show (ω ^ lowDeg s) ^ M = 1 by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow],
        sub_self, zero_div, zero_pow hb0]
      simp
  rw [heq]
  refine S.sum_mem fun k _ => S.smul_mem _ ?_
  exact hS (fun _ => ⟨lowScal d a (ω ^ k), lowScal_mem_unitary (hωn k)⟩) P hP

theorem rowSub_lowScal_zero_of_mem_inv {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) (P : Pol ι d a) (hP : P ∈ inv a d n) :
    rowSub (fun _ => lowScal d a 0) P = eval (basePt ι d a) P • topMinors h n := by
  refine MvPolynomial.funext fun z => ?_
  let g : ι → Matrix (Fin a) (Fin a) ℂ := fun τ => Matrix.of fun i j => z (τ, Fin.castLE h i, j)
  have hc := congrArg (eval (basePt ι d a)) (colSub_eq_detChar_smul_of_mem_inv n P hP g)
  rw [eval_colSub, smul_eq_C_mul, map_mul, eval_C] at hc
  have hv : eval z (topMinors h n) = detChar n g := by
    have hm : ∀ τ, (RingHom.mapMatrix (eval z))
        (Matrix.of fun i i' : Fin a => (X (τ, (topRows h).1 i, i') : Pol ι d a)) = g τ := fun τ => by
      ext i j; simp [g, topRows]
    simp only [topMinors, prodMinors, minorAt, map_prod, map_pow, RingHom.map_det, hm, detChar, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hpt : (fun y : Var ι d a => ∑ i' : Fin d, lowScal d a 0 i' y.2.1 * z (y.1, i', y.2.2)) =
      fun y => ∑ j' : Fin a, g y.1 j' y.2.2 * basePt ι d a (y.1, y.2.1, j') := by
    funext y
    rw [Finset.sum_eq_single y.2.1 (fun b _ hb => by simp [lowScal, Matrix.diagonal_apply_ne _ hb]) (by simp)]
    by_cases hy : (y.2.1 : ℕ) < a
    · rw [Finset.sum_eq_single ⟨y.2.1, hy⟩]
      · simp [lowScal, hy, g, basePt]
      · intro b _ hb
        have : (y.2.1 : ℕ) ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
        simp [basePt, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [lowScal, hy]
      · intro b _
        have : (y.2.1 : ℕ) ≠ (b : ℕ) := fun e => hy (e ▸ b.2)
        simp [basePt, this]
  rw [eval_rowSub, hpt, hc, smul_eq_C_mul, map_mul, eval_C, hv, mul_comm]

theorem exists_fockS_orth {σ : Type} (V N : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V] (hNV : N < V) :
    ∃ Q ∈ V, Q ≠ 0 ∧ ∀ P ∈ N, Formalism.L2.DIV.fockS P Q = 0 := by
  classical
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNV.le
  have hlt : Module.finrank ℂ N < Module.finrank ℂ V := Submodule.finrank_lt_finrank_of_lt hNV
  let b := Module.finBasis ℂ N
  let L : V →ₗ[ℂ] (Fin (Module.finrank ℂ N) → ℂ) :=
    LinearMap.pi fun i => (Formalism.L2.DIV.fockL ((b i : N) : MvPolynomial σ ℂ)).comp V.subtype
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨Q, hQ, hQ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨Q, Q.2, fun h => hQ0 (Subtype.ext h), fun P hP => ?_⟩
  have hQi : ∀ i, Formalism.L2.DIV.fockS ((b i : N) : MvPolynomial σ ℂ) Q = 0 := fun i => by
    have := congrFun (LinearMap.mem_ker.mp hQ) i
    simpa [L, Formalism.L2.DIV.fockL_apply] using this
  have hsum := b.sum_repr ⟨P, hP⟩
  have hPe : P = ∑ i, (b.repr ⟨P, hP⟩ i) • ((b i : N) : MvPolynomial σ ℂ) := by
    have := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  rw [hPe, ← Formalism.L2.DIV.fockL_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, Formalism.L2.DIV.fockL_apply, hQi i, smul_zero]

theorem inv_finiteDimensional (a d : ℕ) (n : ι → ℕ) : FiniteDimensional ℂ (inv (ι := ι) a d n) := by
  classical
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (prodMinors (ι := ι) (a := a) (d := d) (n := n)))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le (inv_le_span_prodMinors a d n)

theorem topMinors_mem {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) (S : Submodule ℂ (Pol ι d a)) (hSI : S ≤ inv a d n)
    (hS : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ S, rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ S)
    (hS0 : S ≠ ⊥) : topMinors h n ∈ S := by
  obtain ⟨P, hPS, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨κ, hκ⟩ := exists_unitary_eval_ne h P hP0
  set P' := rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P
  have h1 : rowSub (fun _ => lowScal d a 0) P' ∈ S := rowSub_lowScal_zero_mem S hS P' (hS κ P hPS)
  rw [rowSub_lowScal_zero_of_mem_inv h n P' (hSI (hS κ P hPS))] at h1
  have := S.smul_mem (eval (basePt ι d a) P')⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this

end GlobalTheory.MinorFrame.RowIrr

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.MinorFrame.RowIrr

theorem inv_irreducible : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), a ≤ d →
    ∀ N : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a), N ≤ GlobalTheory.MinorFrame.inv (ι := ι) a d n →
    (∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ N, GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ N) →
    N = ⊥ ∨ N = GlobalTheory.MinorFrame.inv (ι := ι) a d n := by
  intro ι _ a d n h N hNI hN
  by_cases hN0 : N = ⊥
  · exact Or.inl hN0
  refine Or.inr ?_
  by_contra hne
  haveI := inv_finiteDimensional (ι := ι) a d n
  obtain ⟨Q, hQI, hQ0, hQN⟩ := exists_fockS_orth (inv a d n) N (lt_of_le_of_ne hNI hne)
  let M : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a) :=
    { carrier := {R | R ∈ GlobalTheory.MinorFrame.inv a d n ∧ ∀ P ∈ N, Formalism.L2.DIV.fockS P R = 0}
      add_mem' := fun {R R'} hR hR' => ⟨(GlobalTheory.MinorFrame.inv a d n).add_mem hR.1 hR'.1, fun P hP => by
        rw [← Formalism.L2.DIV.fockL_apply, map_add, Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockL_apply, hR.2 P hP, hR'.2 P hP,
          add_zero]⟩
      zero_mem' := ⟨(GlobalTheory.MinorFrame.inv a d n).zero_mem, fun P _ => by
        rw [← Formalism.L2.DIV.fockL_apply, map_zero]⟩
      smul_mem' := fun c {R} hR => ⟨(GlobalTheory.MinorFrame.inv a d n).smul_mem c hR.1, fun P hP => by
        rw [← Formalism.L2.DIV.fockL_apply, map_smul, Formalism.L2.DIV.fockL_apply, hR.2 P hP, smul_zero]⟩ }
  have hMI : M ≤ GlobalTheory.MinorFrame.inv a d n := fun R hR => hR.1
  have hMs : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ R ∈ M,
      GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) R ∈ M := by
    intro κ R hR
    refine ⟨GlobalTheory.MinorFrame.rowSub_mem_inv _ hR.1, fun P hP => ?_⟩
    have hP' : P = GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ))
        (GlobalTheory.MinorFrame.rowSub (fun τ => ((star (κ τ) : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) P) := by
      rw [rowSub_rowSub]
      have : (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ) * ((star (κ τ) : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) =
          fun _ => 1 := by
        funext τ
        exact Unitary.mul_star_self_of_mem (κ τ).2
      rw [this, rowSub_one]
    rw [hP', GlobalTheory.MinorFrame.fockS_rowSub_unitary]
    exact hR.2 _ (hN (fun τ => star (κ τ)) P hP)
  have hM0 : M ≠ ⊥ := by
    intro hM
    apply hQ0
    have : Q ∈ M := ⟨hQI, hQN⟩
    rw [hM] at this
    exact (Submodule.mem_bot ℂ).1 this
  have h1 := topMinors_mem h n N hNI hN hN0
  have h2 := topMinors_mem h n M hMI hMs hM0
  have h3 := h2.2 _ h1
  have := GlobalTheory.MinorFrame.fockS_self_re_pos (topMinors_ne_zero (ι := ι) h n)
  rw [h3] at this
  simp at this

end GlobalTheory.MinorFrame.RowIrr
