import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalBasePtTopMinors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RowTransport

open GlobalTheory.MinorFrame MvPolynomial

section LA

variable {V V' Q : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup Q] [Module ℂ Q]

def eigSet (T G : Module.End ℂ V) (t : ℂ) : Set V := {v | ∃ k : ℤ, T v = (k : ℂ) • v ∧ G v = t ^ k • v}

theorem exists_nodes (T G : Module.End ℂ V) (t : ℂ) (v : V) (hv : v ∈ Submodule.span ℂ (eigSet T G t)) :
    ∃ s : Finset ℤ, ∀ p : Polynomial ℂ, (∀ k ∈ s, p.eval (k : ℂ) = t ^ k) → G v = Polynomial.aeval T p v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨k, h1, h2⟩ := hv
    refine ⟨{k}, fun p hp => ?_⟩
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul h1, hp k (by simp), h2]
  | zero => exact ⟨∅, fun p _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun p hp => ?_⟩
    rw [map_add, map_add, hs p fun k hk => hp k (by simp [hk]), hs' p fun k hk => hp k (by simp [hk])]
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨s, fun p hp => by rw [map_smul, map_smul, hs p hp]⟩

theorem transfer (q : V →ₗ[ℂ] Q) (q' : V' →ₗ[ℂ] Q) (T G : Module.End ℂ V) (T' G' : Module.End ℂ V') (t : ℂ)
    (h : ∀ P P', q P = q' P' → q (T P) = q' (T' P'))
    (hV : Submodule.span ℂ (eigSet T G t) = ⊤) (hV' : Submodule.span ℂ (eigSet T' G' t) = ⊤)
    (P : V) (P' : V') (hP : q P = q' P') : q (G P) = q' (G' P') := by
  obtain ⟨s, hs⟩ := exists_nodes T G t P (hV ▸ Submodule.mem_top)
  obtain ⟨s', hs'⟩ := exists_nodes T' G' t P' (hV' ▸ Submodule.mem_top)
  have hp : ∀ k ∈ s ∪ s', (Lagrange.interpolate (s ∪ s') (fun k : ℤ => (k : ℂ)) (fun k => t ^ k)).eval (k : ℂ) = t ^ k :=
    fun k hk => Lagrange.eval_interpolate_at_node (v := fun k : ℤ => (k : ℂ)) _ (Int.cast_injective.injOn) hk
  rw [hs _ fun k hk => hp k (by simp [hk]), hs' _ fun k hk => hp k (by simp [hk])]
  generalize Lagrange.interpolate (s ∪ s') (fun k : ℤ => (k : ℂ)) (fun k => t ^ k) = p
  induction p using Polynomial.induction_on with
  | C c => simp [hP]
  | add p r hp hr => simp only [map_add, LinearMap.add_apply, hp, hr]
  | monomial n c ih =>
    have e : Polynomial.C c * Polynomial.X ^ (n + 1) = Polynomial.X * (Polynomial.C c * Polynomial.X ^ n) := by ring
    rw [e, map_mul, map_mul (Polynomial.aeval T'), Polynomial.aeval_X, Polynomial.aeval_X, Module.End.mul_apply,
      Module.End.mul_apply]
    exact h _ _ ih

end LA

section Rows

variable {ι : Type} [Fintype ι] {d a : ℕ}

def rho (S : ι → Matrix (Fin d) (Fin d) ℂ) : Derivation ℂ (Pol ι d a) (Pol ι d a) :=
  mkDerivation ℂ fun y => rowSub S (X y)

omit [Fintype ι] in
theorem rowSub_X (S : ι → Matrix (Fin d) (Fin d) ℂ) (y : Var ι d a) :
    rowSub S (X y : Pol ι d a) = ∑ i', S y.1 i' y.2.1 • X (y.1, i', y.2.2) := by
  simp [rowSub, smul_eq_C_mul]

omit [Fintype ι] in
theorem rho_X (S : ι → Matrix (Fin d) (Fin d) ℂ) (y : Var ι d a) : rho S (X y) = rowSub S (X y) :=
  mkDerivation_X _ _ _

omit [Fintype ι] in
theorem rowSub_add_X (S S' : ι → Matrix (Fin d) (Fin d) ℂ) (y : Var ι d a) :
    rowSub (S + S') (X y : Pol ι d a) = rowSub S (X y) + rowSub S' (X y) := by
  simp [rowSub_X, add_smul, Finset.sum_add_distrib]

omit [Fintype ι] in
theorem rowSub_smul_X (c : ℂ) (S : ι → Matrix (Fin d) (Fin d) ℂ) (y : Var ι d a) :
    rowSub (c • S) (X y : Pol ι d a) = c • rowSub S (X y) := by
  simp [rowSub_X, Finset.smul_sum, smul_smul]

omit [Fintype ι] in
theorem rho_add (S S' : ι → Matrix (Fin d) (Fin d) ℂ) : (rho (S + S') : Derivation ℂ (Pol ι d a) _) = rho S + rho S' :=
  derivation_ext fun y => by simp [rho_X, rowSub_add_X]

omit [Fintype ι] in
theorem rho_smul (c : ℂ) (S : ι → Matrix (Fin d) (Fin d) ℂ) : (rho (c • S) : Derivation ℂ (Pol ι d a) _) = c • rho S :=
  derivation_ext fun y => by simp [rho_X, rowSub_smul_X]

theorem rowSub_mul (S A : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) : rowSub S (rowSub A P) = rowSub (S * A) P :=
  RowIrr.rowSub_rowSub S A P

theorem rowSub_one' (P : Pol ι d a) : rowSub (1 : ι → Matrix (Fin d) (Fin d) ℂ) P = P := RowIrr.rowSub_one P

theorem rho_rowSub_X (S A : ι → Matrix (Fin d) (Fin d) ℂ) (y : Var ι d a) :
    rho S (rowSub A (X y)) = rowSub (S * A) (X y) := by
  rw [← rowSub_mul, rowSub_X A, map_sum, map_sum]
  simp only [map_smul, Derivation.map_smul, rho_X]

def natSet (S : ι → Matrix (Fin d) (Fin d) ℂ) (t : ℂ) : Set (Pol ι d a) :=
  {P | ∃ k : ℕ, rho S P = (k : ℂ) • P ∧ rowSub (1 + (t - 1) • S) P = t ^ k • P}

omit [Fintype ι] in
theorem natSet_mul {S : ι → Matrix (Fin d) (Fin d) ℂ} {t : ℂ} {P R : Pol ι d a} (hP : P ∈ natSet S t)
    (hR : R ∈ natSet S t) : P * R ∈ natSet S t := by
  obtain ⟨k, h1, h2⟩ := hP
  obtain ⟨l, h3, h4⟩ := hR
  refine ⟨k + l, ?_, ?_⟩
  · rw [Derivation.leibniz, h1, h3]
    simp only [smul_eq_mul, mul_smul_comm, Nat.cast_add, add_smul, mul_comm R P]
    exact add_comm _ _
  · rw [map_mul, h2, h4, pow_add, smul_mul_smul_comm]

theorem span_natSet (S : ι → Matrix (Fin d) (Fin d) ℂ) (hS : S * S = S) (t : ℂ) :
    Submodule.span ℂ (natSet (a := a) S t) = ⊤ := by
  have hmul : ∀ R ∈ natSet (a := a) S t, ∀ P ∈ Submodule.span ℂ (natSet (a := a) S t),
      P * R ∈ Submodule.span ℂ (natSet (a := a) S t) := by
    intro R hR P hP
    induction hP using Submodule.span_induction with
    | mem v hv => exact Submodule.subset_span (natSet_mul hv hR)
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  rw [eq_top_iff]
  intro P hP
  clear hP
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine Submodule.subset_span ⟨0, ?_, ?_⟩
    · simp
    · simp
  | add p r hp hr => exact Submodule.add_mem _ hp hr
  | mul_X p y hp =>
    have e : (X y : Pol ι d a) = rowSub S (X y) + rowSub (1 - S) (X y) := by
      rw [← rowSub_add_X, add_sub_cancel, rowSub_one']
    rw [e, mul_add]
    refine Submodule.add_mem _ (hmul _ ⟨1, ?_, ?_⟩ _ hp) (hmul _ ⟨0, ?_, ?_⟩ _ hp)
    · rw [rho_rowSub_X, hS]; simp
    · rw [rowSub_mul, pow_one, ← rowSub_smul_X, add_mul, smul_mul_assoc, hS, one_mul, sub_smul, one_smul, add_sub_cancel]
    · rw [rho_rowSub_X, mul_sub, hS, mul_one, sub_self, ← rowSub_smul_X]; simp
    · rw [rowSub_mul, add_mul, smul_mul_assoc, mul_sub S, hS, mul_one, sub_self]; simp

end Rows

section Group

variable {ι : Type} [Fintype ι] {d a a' : ℕ} {Q : Type} [AddCommGroup Q] [Module ℂ Q]
  (q : Pol ι d a →ₗ[ℂ] Q) (q' : Pol ι d a' →ₗ[ℂ] Q) (n : ι → ℕ)

open Matrix

def good : Submonoid (ι → Matrix (Fin d) (Fin d) ℂ) where
  carrier := {g | ∀ P P', q P = q' P' → q' (rowSub g P') = detChar n g • q (rowSub (fun σ => (g σ)⁻¹ᵀ) P)}
  one_mem' := by
    intro P P' h
    have e : (fun σ : ι => ((1 : ι → Matrix (Fin d) (Fin d) ℂ) σ)⁻¹ᵀ) = 1 := by
      funext σ; simp
    rw [e, rowSub_one', rowSub_one', h]
    simp [detChar]
  mul_mem' := by
    intro g g' hg hg' P P' h
    have h1 := hg' P P' h
    rw [← map_smul] at h1
    have h2 := hg _ _ h1.symm
    have e : (fun σ : ι => ((g * g') σ)⁻¹ᵀ) = (fun σ => (g σ)⁻¹ᵀ) * (fun σ => (g' σ)⁻¹ᵀ) := by
      funext σ; simp [Matrix.mul_inv_rev]
    rw [e, ← rowSub_mul, ← rowSub_mul, h2, map_smul, map_smul, smul_smul]
    congr 1
    simp [detChar, mul_pow, Finset.prod_mul_distrib]

def LieRel : Prop := ∀ (τ : ι) (Z : Matrix (Fin d) (Fin d) ℂ) P P', q P = q' P' →
  q (-(rho (Pi.single τ Zᵀ) P) + ((n τ : ℂ) * Z.trace) • P) = q' (rho (Pi.single τ Z) P')

omit [Fintype ι] in
theorem single_idem (τ : ι) {S : Matrix (Fin d) (Fin d) ℂ} (hS : S * S = S) :
    (Pi.single τ S : ι → Matrix (Fin d) (Fin d) ℂ) * Pi.single τ S = Pi.single τ S := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp [hS]
  · simp [h]

omit [Fintype ι] in
theorem mulSingle_eq (τ : ι) (S : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) :
    (Pi.mulSingle τ (1 + c • S) : ι → Matrix (Fin d) (Fin d) ℂ) = 1 + c • (Pi.single τ S : ι → Matrix (Fin d) (Fin d) ℂ) := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp
  · simp [h]

variable {q q' n}

theorem idem_mem (hL : LieRel q q' n) (τ : ι) (S : Matrix (Fin d) (Fin d) ℂ) (hS : S * S = S) (htr : S.trace = 1)
    (t : ℂ) (ht : t ≠ 0) (hdet : (1 + (t - 1) • S).det = t) :
    (Pi.mulSingle τ (1 + (t - 1) • S) : ι → Matrix (Fin d) (Fin d) ℂ) ∈ good q q' n := by
  intro P P' h
  have hinv : (1 + (t - 1) • S)⁻¹ = 1 + (t⁻¹ - 1) • S := by
    apply Matrix.inv_eq_left_inv
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hS, smul_smul, add_assoc, ← add_smul]
    have : t⁻¹ - 1 + (t - 1) * (1 + (t⁻¹ - 1)) = 0 := by field_simp; ring
    simp only [smul_add, smul_smul, ← add_smul]
    have h2 : t⁻¹ - 1 + (t - 1 + (t - 1) * (t⁻¹ - 1)) = 0 := by rw [← this]; ring
    rw [h2]; simp
  have e1 : (fun σ => ((Pi.mulSingle τ (1 + (t - 1) • S) : ι → Matrix (Fin d) (Fin d) ℂ) σ)⁻¹ᵀ) =
      1 + (t⁻¹ - 1) • (Pi.single τ Sᵀ : ι → Matrix (Fin d) (Fin d) ℂ) := by
    funext σ
    by_cases h : σ = τ
    · subst h; simp [hinv]
    · simp [h]
  have e2 : detChar n (Pi.mulSingle τ (1 + (t - 1) • S) : ι → Matrix (Fin d) (Fin d) ℂ) = t ^ n τ := by
    unfold detChar
    rw [Finset.prod_eq_single τ]
    · simp [hdet]
    · intro σ _ h; simp [h]
    · simp
  rw [e1, e2, mulSingle_eq, ← map_smul]
  have hST : Sᵀ * Sᵀ = Sᵀ := by rw [← Matrix.transpose_mul, hS]
  symm
  refine transfer q q' (-(rho (Pi.single τ Sᵀ)).toLinearMap + (n τ : ℂ) • 1)
    (t ^ n τ • (rowSub (1 + (t⁻¹ - 1) • (Pi.single τ Sᵀ : ι → Matrix (Fin d) (Fin d) ℂ))).toLinearMap) (rho (Pi.single τ S)).toLinearMap
    (rowSub (1 + (t - 1) • (Pi.single τ S : ι → Matrix (Fin d) (Fin d) ℂ))).toLinearMap t ?_ ?_ ?_ P P' h
  · intro P P' h
    have := hL τ S P P' h
    rw [htr, mul_one] at this
    exact this
  · rw [eq_top_iff, ← span_natSet _ (single_idem τ hST) t⁻¹]
    refine Submodule.span_mono ?_
    rintro v ⟨k, h1, h2⟩
    refine ⟨(n τ : ℤ) - k, ?_, ?_⟩
    · change -(rho _ v) + (n τ : ℂ) • v = _
      rw [h1]; push_cast; module
    · change t ^ n τ • rowSub _ v = _
      rw [h2, smul_smul, zpow_sub₀ ht]; simp [div_eq_mul_inv]
  · rw [eq_top_iff, ← span_natSet _ (single_idem τ hS) t]
    refine Submodule.span_mono ?_
    rintro v ⟨k, h1, h2⟩
    exact ⟨k, by simpa using h1, by simpa using h2⟩

theorem diag_one_eq (k : Fin d) (t : ℂ) :
    (diagonal (Pi.mulSingle k t) : Matrix (Fin d) (Fin d) ℂ) = 1 + (t - 1) • Matrix.single k k 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    by_cases h' : i = k
    · subst h'; simp
    · simp [h', Ne.symm h']
  · simp only [diagonal_apply_ne _ h, Matrix.add_apply, one_apply_ne h, Matrix.smul_apply, zero_add]
    rw [Matrix.single_apply_of_ne, smul_zero]
    rintro ⟨rfl, rfl⟩; exact h rfl

theorem diag_one_mem (hL : LieRel q q' n) (τ : ι) (k : Fin d) (t : ℂ) (ht : t ≠ 0) :
    (Pi.mulSingle τ (1 + (t - 1) • Matrix.single k k 1) : ι → Matrix (Fin d) (Fin d) ℂ) ∈ good q q' n := by
  refine idem_mem hL τ _ (by simp) (by simp) t ht ?_
  rw [← diag_one_eq, det_diagonal, Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem mulSingle_mem (hL : LieRel q q' n) (τ : ι) (g : Matrix (Fin d) (Fin d) ℂ) (hg : g.det ≠ 0) :
    (Pi.mulSingle τ g : ι → Matrix (Fin d) (Fin d) ℂ) ∈ good q q' n := by
  let K : Submonoid (Matrix (Fin d) (Fin d) ℂ) :=
    (good q q' n).comap (MonoidHom.mulSingle (fun _ : ι => Matrix (Fin d) (Fin d) ℂ) τ)
  change g ∈ K
  refine diagonal_transvection_induction_of_det_ne_zero (fun g => g ∈ K) g hg ?_ ?_ fun A B _ _ hA hB => K.mul_mem hA hB
  · intro E hE
    rw [det_diagonal, Finset.prod_ne_zero_iff] at hE
    change E ∈ K.comap (diagonalRingHom (Fin d) ℂ).toMonoidHom
    rw [← Finset.univ_prod_mulSingle E]
    refine Submonoid.prod_mem _ fun k hk => ?_
    change (diagonal (Pi.mulSingle k (E k)) : Matrix (Fin d) (Fin d) ℂ) ∈ K
    rw [diag_one_eq]
    exact diag_one_mem hL τ k _ (hE k hk)
  · rintro ⟨i, l, hil, c⟩
    have e : (1 + ((2 : ℂ)⁻¹ - 1) • Matrix.single i i 1) *
        (1 + ((2 : ℂ) - 1) • (Matrix.single i i 1 + Matrix.single i l (2 * c))) = transvection i l c := by
      simp only [transvection, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
        Matrix.single_mul_single_same]
      have : Matrix.single i l (2 * c) = (2 : ℂ) • Matrix.single i l c := by simp
      rw [this]
      module
    change transvection i l c ∈ K
    rw [← e]
    refine K.mul_mem (diag_one_mem hL τ i _ (by norm_num)) (idem_mem hL τ _ ?_ ?_ 2 two_ne_zero ?_)
    · simp [add_mul, mul_add, Matrix.single_mul_single_of_ne, hil.symm]
    · simp [Matrix.trace_single_eq_of_ne, hil]
    · have h := congrArg det e
      rw [det_mul, det_transvection_of_ne _ _ hil, ← diag_one_eq, det_diagonal, Finset.prod_eq_single i] at h
      · simp only [Pi.mulSingle_eq_same] at h
        linear_combination 2 * h
      · intro b _ hb; simp [hb]
      · simp

theorem mem_good (hL : LieRel q q' n) (g : ι → Matrix (Fin d) (Fin d) ℂ) (hg : ∀ τ, (g τ).det ≠ 0) :
    g ∈ good q q' n := by
  rw [← Finset.noncommProd_mulSingle g]
  exact Submonoid.noncommProd_mem _ _ _ _ fun τ _ => mulSingle_mem hL τ _ (hg τ)

theorem lieRel_of_skew (h : ∀ (τ : ι) (Z : Matrix (Fin d) (Fin d) ℂ), Zᴴ = -Z → ∀ P P', q P = q' P' →
    q (-(rho (Pi.single τ Zᵀ) P) + ((n τ : ℂ) * Z.trace) • P) = q' (rho (Pi.single τ Z) P')) : LieRel q q' n := by
  intro τ Z P P' hP
  obtain ⟨A, B, hA, hB, rfl⟩ : ∃ A B : Matrix (Fin d) (Fin d) ℂ, Aᴴ = -A ∧ Bᴴ = -B ∧ Z = A + Complex.I • B := by
    refine ⟨(2 : ℂ)⁻¹ • (Z - Zᴴ), (-Complex.I / 2) • (Z + Zᴴ), ?_, ?_, ?_⟩
    · simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      have : star ((2 : ℂ)⁻¹) = 2⁻¹ := by simp
      rw [this]; module
    · simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
      have : star (-Complex.I / 2) = Complex.I / 2 := by simp
      rw [this]; module
    · rw [smul_smul]
      have : Complex.I * (-Complex.I / 2) = 2⁻¹ := by
        linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      rw [this]; module
  have h1 := h τ A hA P P' hP
  have h2 := h τ B hB P P' hP
  simp only [transpose_add, transpose_smul, Pi.single_add, Pi.single_smul', rho_add, rho_smul, Derivation.add_apply,
    Derivation.smul_apply, map_add, map_smul, map_neg, trace_add, trace_smul, smul_eq_mul] at h1 h2 ⊢
  rw [← h1, ← h2]
  module

end Group

section Fock

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

variable {D : D7} {a b : ℕ}

theorem der_sum_apply {R κ : Type} [CommRing R] [Algebra ℂ R] (s : Finset κ) (f : κ → Derivation ℂ R R) (x : R) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

theorem rho_single_apply (τ : D.what₂.Tau) (Y : Matrix (Fin b) (Fin b) ℂ) (P : PolF D b a) :
    rho (Pi.single τ Y) P = ∑ i, ∑ l, Y i l • ∑ j, X (τ, i, j) * pderiv (τ, l, j) P := by
  have : (rho (Pi.single τ Y) : Derivation ℂ (PolF D b a) (PolF D b a)) =
      ∑ i, ∑ l, Y i l • ∑ j, (X (τ, i, j) : PolF D b a) • pderiv (τ, l, j) := by
    refine derivation_ext ?_
    rintro ⟨σ, m, k⟩
    rw [rho_X, rowSub_X]
    simp only [der_sum_apply, Derivation.smul_apply, pderiv_X, smul_eq_mul, Pi.single_apply,
      Prod.mk.injEq]
    by_cases h : σ = τ
    · subst h
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single m, Finset.sum_eq_single k]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    · simp [h]
  rw [this]
  simp only [der_sum_apply, Derivation.smul_apply, smul_eq_mul]

theorem sum_diag (Y : Matrix (Fin b) (Fin b) ℂ) (c : ℂ) (P : PolF D b a) :
    ∑ i, ∑ l, Y i l • ∑ _j : Fin a, (if i = l then c • P else 0) = ((a : ℂ) * c * Y.trace) • P := by
  rw [Matrix.trace, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, diag_apply, ← Nat.cast_smul_eq_nsmul ℂ]
    module
  · intro l _ hl; simp [Ne.symm hl]
  · simp

theorem fockT_pos (τ : D.what₂.Tau) (Y : Matrix (Fin b) (Fin b) ℂ) (P : PolF D b a) :
    fockT τ (fun _ : Fin a => true) (fun _ : Fin b => true) Y P =
      rho (Pi.single τ Y) P + ((a : ℂ) * (1 / 2) * Y.trace) • P := by
  rw [rho_single_apply, ← sum_diag]
  simp only [fockT, LinearMap.sum_apply, LinearMap.smul_apply, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = l <;> simp [raiO, lowO, sgn, h]

theorem fockT_neg (τ : D.what₂.Tau) (Y : Matrix (Fin b) (Fin b) ℂ) (P : PolF D b a) :
    fockT τ (fun _ : Fin a => false) (fun _ : Fin b => true) Y P =
      -(rho (Pi.single τ Yᵀ) P) + ((a : ℂ) * (-1 / 2) * Y.trace) • P := by
  rw [rho_single_apply, ← sum_diag, Finset.sum_comm]
  simp only [fockT, LinearMap.sum_apply, LinearMap.smul_apply, ← Finset.sum_add_distrib, ← smul_add, transpose_apply,
    ← Finset.sum_neg_distrib, ← smul_neg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = l
  · subst h
    simp [raiO, lowO, sgn]
    module
  · simp [raiO, lowO, sgn, h, pderiv_X, Pi.single_apply, Ne.symm h]

theorem actT_true {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (eS : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (hA : ∀ j, A.ε τ j = true) (hB : ∀ i, B.ε τ i = true) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (P : PolF D X.rank M.rank) :
    GlobalTheory.RealQuot.actT true A B eS τ Y P =
      -(rho (Pi.single τ (B.fr τ * Y * (B.fr τ)⁻¹)ᵀ) P) +
        ((M.rank : ℂ) * (-1 / 2) * (B.fr τ * Y * (B.fr τ)⁻¹).trace) • P + ((eS τ : ℂ) * Y.trace) • P := by
  have f1 : @Eq (Fin M.rank → Bool) ((GlobalTheory.SquareComm.frSgn true A).ε τ) fun _ => false := by
    funext j; change (true ^^ A.ε τ j) = false; rw [hA]; rfl
  have f3 : B.ε τ = fun _ => true := funext hB
  rw [← fockT_neg, ← f1, ← f3]
  rfl

theorem actT_false {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (eS : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (hA : ∀ j, A.ε τ j = true) (hB : ∀ i, B.ε τ i = true) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (P : PolF D X.rank M.rank) :
    GlobalTheory.RealQuot.actT false A B eS τ Y P =
      rho (Pi.single τ (B.fr τ * Y * (B.fr τ)⁻¹)) P +
        ((M.rank : ℂ) * (1 / 2) * (B.fr τ * Y * (B.fr τ)⁻¹).trace) • P + ((eS τ : ℂ) * Y.trace) • P := by
  have f1 : @Eq (Fin M.rank → Bool) ((GlobalTheory.SquareComm.frSgn false A).ε τ) fun _ => true := by
    funext j; change (false ^^ A.ε τ j) = true; rw [hA]; rfl
  have f3 : B.ε τ = fun _ => true := funext hB
  have h := fockT_pos τ (B.fr τ * Y * (B.fr τ)⁻¹) P
  rw [← h]
  unfold GlobalTheory.RealQuot.actT
  rw [f1, f3]
  rfl

theorem exists_lie {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau) (hB : ∀ i, B.ε τ i = true)
    (Z : Matrix (Fin X.rank) (Fin X.rank) ℂ) (hZ : Zᴴ = -Z) :
    ∃ Y ∈ lieAt X τ, B.fr τ * Y * (B.fr τ)⁻¹ = Z ∧ Y.trace = Z.trace := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have hJ : Formalism.REAL.Jm (B.ε τ) = 1 := by
    simp [Formalism.REAL.Jm, hB]
  refine ⟨(B.fr τ)⁻¹ * Z * B.fr τ, ?_, ?_, ?_⟩
  · have hu' : IsUnit (B.fr τ)ᴴ.det := by rw [det_conjTranspose]; exact hu.star
    change _ * _ + _ * _ = 0
    rw [← B.fr_gram, hJ, mul_one, conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, hZ]
    simp only [mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu', Matrix.mul_nonsing_inv_cancel_left _ _ hu]
    simp
  · simp only [mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_nonsing_inv_cancel_left _ _ hu, mul_one]
  · rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ hu, one_mul]

theorem scalar_shift {Q : Type} [AddCommGroup Q] [Module ℂ Q] (x y z : Q) (m m' e e' n t : ℂ)
    (hn : n = e - e' - (m + m') / 2)
    (h : -x + (m * (-1 / 2) * t) • z + (e * t) • z = y + (m' * (1 / 2) * t) • z + (e' * t) • z) :
    -x + (n * t) • z = y := by
  subst hn
  linear_combination (norm := module) h

theorem unitary_inv_transpose {n : ℕ} (κ : Matrix.unitaryGroup (Fin n) ℂ) :
    (κ : Matrix (Fin n) (Fin n) ℂ)⁻¹ᵀ = (κ : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) := by
  rw [Matrix.inv_eq_left_inv (B := star (κ : Matrix (Fin n) (Fin n) ℂ)) κ.2.1]
  rfl

end Fock

open Matrix in

theorem row_transport : ∀ (D : D7) (M M' X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (A' : GlobalTheory.ChainFr.Fr M') (B : GlobalTheory.ChainFr.Fr X)
    (eS eS' : D.what₂.Tau → ℚ) (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : PolF D X.rank M.rank →ₗ[ℂ] Q) (q' : PolF D X.rank M'.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ j, A'.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = eS τ - eS' τ - ((M.rank : ℚ) + (M'.rank : ℚ)) / 2) →
    (∀ P P', q P = q' P' → ∀ τ, ∀ Y ∈ lieAt X τ,
      q (GlobalTheory.RealQuot.actT true A B eS τ Y P) = q' (GlobalTheory.RealQuot.actT false A' B eS' τ Y P')) →
    ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin X.rank) ℂ) (P : PolF D X.rank M.rank) (P' : PolF D X.rank M'.rank), q P = q' P' →
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ)) P') =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ)) •
          q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ).map (starRingEnd ℂ)) P) := by
  intro D M M' X A A' B eS eS' n₀ Q _ _ q q' hA hA' hB hn hL κ P P' hP
  have hrel : LieRel q q' n₀ := by
    refine lieRel_of_skew fun τ Z hZ P P' hP => ?_
    obtain ⟨Y, hY, e1, e2⟩ := exists_lie B τ (hB τ) Z hZ
    have h := hL P P' hP τ Y hY
    rw [actT_true A B eS τ (hA τ) (hB τ), actT_false A' B eS' τ (hA' τ) (hB τ), e1, e2] at h
    have hc : (n₀ τ : ℂ) = (eS τ : ℂ) - eS' τ - ((M.rank : ℂ) + M'.rank) / 2 := by
      have := congrArg (fun x : ℚ => (x : ℂ)) (hn τ)
      simpa using this
    simp only [map_add, map_neg, map_smul, ← hP] at h
    rw [map_add, map_neg, map_smul]
    exact scalar_shift _ _ _ _ _ _ _ _ _ hc h
  have hdet : ∀ τ, (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ).det ≠ 0 := fun τ =>
    (Matrix.UnitaryGroup.det_isUnit (κ τ)).ne_zero
  have h := mem_good hrel _ hdet P P' hP
  simp only [unitary_inv_transpose] at h
  exact h

end GlobalTheory.RowTransport

end
