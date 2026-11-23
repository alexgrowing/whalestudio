import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FstIsFinFFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinFSndFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorMaximalCompactMovedBases

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopDict

open Matrix

def IsEigB {n : ℕ} (s B : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → Bool) : Prop :=
  IsUnit B.det ∧ s * B = B * Matrix.diagonal (fun a => if e a then (1 : ℂ) else -1)

theorem IsEigB.change_zero {n : ℕ} {s B B' : Matrix (Fin n) (Fin n) ℂ} {e e' : Fin n → Bool} (h : IsEigB s B e)
    (h' : IsEigB s B' e') {a b : Fin n} (hab : e a ≠ e' b) : (B⁻¹ * B') a b = 0 := by
  have h3 : B⁻¹ * s = Matrix.diagonal (fun a => if e a then (1 : ℂ) else -1) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * (s * B) * B⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h.1, Matrix.mul_one]
      _ = _ := by rw [h.2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h.1, Matrix.one_mul]
  have h4 : Matrix.diagonal (fun a => if e a then (1 : ℂ) else -1) * (B⁻¹ * B') =
      (B⁻¹ * B') * Matrix.diagonal (fun a => if e' a then (1 : ℂ) else -1) := by
    rw [← Matrix.mul_assoc, ← h3, Matrix.mul_assoc, h'.2, Matrix.mul_assoc]
  have h5 := congrFun (congrFun h4 a) b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h5
  cases ha : e a <;> cases hb : e' b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at hab h5 <;> simp at h5 <;>
    first | linear_combination (1 / 2 : ℂ) * h5 | linear_combination (-1 / 2 : ℂ) * h5

theorem cplxO_unitMap_eig {m n : ℕ} {s B : Matrix (Fin n) (Fin n) ℂ} {e : Fin n → Bool} (h : IsEigB s B e)
    {s' B' : Matrix (Fin m) (Fin m) ℂ} {e' : Fin m → Bool} (h' : IsEigB s' B' e') (i : Fin m) (j : Fin n) :
    cplxO s s' (Formalism.IndefR.Datum.unitMap B B' i j) =
      ((if (e' i == e j) then 1 else -1 : ℂ) * Complex.I) • Formalism.IndefR.Datum.unitMap B B' i j := by
  obtain ⟨hu, h1⟩ := h
  obtain ⟨-, h2⟩ := h'
  have h3 : B⁻¹ * s = Matrix.diagonal (fun a => if e a then (1 : ℂ) else -1) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * (s * B) * B⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = _ := by rw [h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have e0 : Matrix.diagonal (fun a : Fin m => if e' a then (1 : ℂ) else -1) * single i j (1 : ℂ) *
      Matrix.diagonal (fun a : Fin n => if e a then (1 : ℂ) else -1) =
      (if (e' i == e j) then 1 else -1 : ℂ) • single i j (1 : ℂ) := by
    ext a b
    rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hab : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hab
      cases hi : e' i <;> cases hj : e j <;> simp
    · simp [hab]
  unfold cplxO Formalism.IndefR.Datum.unitMap
  rw [mul_comm _ Complex.I, ← smul_smul]
  congr 1
  calc _ = (s' * B') * single i j (1 : ℂ) * (B⁻¹ * s) := by simp only [Matrix.mul_assoc]
    _ = B' * (Matrix.diagonal (fun a : Fin m => if e' a then (1 : ℂ) else -1) * single i j (1 : ℂ) *
      Matrix.diagonal (fun a : Fin n => if e a then (1 : ℂ) else -1)) * B⁻¹ := by
        rw [h2, h3]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [e0, Matrix.mul_smul, Matrix.smul_mul]

def cj (e : Bool) : ℂ →+* ℂ := if e then RingHom.id ℂ else starRingEnd ℂ

theorem cj_apply (e : Bool) (w : ℂ) : cj e w = if e then w else starRingEnd ℂ w := by cases e <;> rfl

def coef {m n : ℕ} (B₁ B₂ : Matrix (Fin n) (Fin n) ℂ) (C₁ C₂ : Matrix (Fin m) (Fin m) ℂ) (e₁ : Fin n → Bool)
    (d₁ : Fin m → Bool) (v b : Fin m × Fin n) : ℂ :=
  cj (d₁ b.1 == e₁ b.2) ((C₁⁻¹ * C₂) b.1 v.1 * (B₂⁻¹ * B₁) v.2 b.2)

theorem coef_mul {m n : ℕ} {s B₁ B₂ : Matrix (Fin n) (Fin n) ℂ} {s' C₁ C₂ : Matrix (Fin m) (Fin m) ℂ} {e₁ e₂ : Fin n → Bool}
    {d₁ d₂ : Fin m → Bool} (h₁ : IsEigB s B₁ e₁) (h₂ : IsEigB s B₂ e₂) (k₁ : IsEigB s' C₁ d₁) (k₂ : IsEigB s' C₂ d₂)
    (v w : Fin m × Fin n) :
    ∑ b, coef B₁ B₂ C₁ C₂ e₁ d₁ v b * coef B₂ B₁ C₂ C₁ e₂ d₂ b w = if w = v then 1 else 0 := by
  have e : ∀ b, coef B₁ B₂ C₁ C₂ e₁ d₁ v b * coef B₂ B₁ C₂ C₁ e₂ d₂ b w =
      cj (d₂ w.1 == e₂ w.2) (((C₂⁻¹ * C₁) w.1 b.1 * (C₁⁻¹ * C₂) b.1 v.1) * ((B₂⁻¹ * B₁) v.2 b.2 * (B₁⁻¹ * B₂) b.2 w.2)) := by
    intro b
    unfold coef
    by_cases a1 : d₂ w.1 = d₁ b.1
    · by_cases a2 : e₁ b.2 = e₂ w.2
      · rw [a1, a2, ← map_mul]; congr 1; ring
      · rw [h₁.change_zero h₂ a2]; simp
    · rw [k₂.change_zero k₁ a1]; simp
  have eC : (C₂⁻¹ * C₁) * (C₁⁻¹ * C₂) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ k₁.1, Matrix.nonsing_inv_mul _ k₂.1]
  have eB : (B₂⁻¹ * B₁) * (B₁⁻¹ * B₂) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ h₁.1, Matrix.nonsing_inv_mul _ h₂.1]
  simp only [e]
  have e3 : ∑ b : Fin m × Fin n, ((C₂⁻¹ * C₁) w.1 b.1 * (C₁⁻¹ * C₂) b.1 v.1) * ((B₂⁻¹ * B₁) v.2 b.2 * (B₁⁻¹ * B₂) b.2 w.2) =
      ((C₂⁻¹ * C₁) * (C₁⁻¹ * C₂)) w.1 v.1 * ((B₂⁻¹ * B₁) * (B₁⁻¹ * B₂)) v.2 w.2 := by
    rw [Matrix.mul_apply (M := C₂⁻¹ * C₁), Matrix.mul_apply (M := B₂⁻¹ * B₁), Finset.sum_mul_sum, Fintype.sum_prod_type]
  rw [← map_sum, e3, eC, eB]
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  by_cases a1 : w1 = v1 <;> by_cases a2 : v2 = w2 <;> simp [Matrix.one_apply, a1, a2, @eq_comm _ w2 v2]

def sub {ι κ : Type} [Fintype κ] (c : ι → κ → κ → ℂ) : MvPolynomial (ι × κ) ℂ →ₐ[ℂ] MvPolynomial (ι × κ) ℂ :=
  MvPolynomial.aeval (fun v : ι × κ => ∑ b, c v.1 v.2 b • (MvPolynomial.X (v.1, b) : MvPolynomial (ι × κ) ℂ))

theorem sub_comp {ι κ : Type} [Fintype κ] [DecidableEq κ] (c c' : ι → κ → κ → ℂ)
    (h : ∀ τ v w, ∑ b, c τ v b * c' τ b w = if w = v then 1 else 0) : (sub c').comp (sub c) = AlgHom.id ℂ _ := by
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [sub, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_smul, Finset.smul_sum, smul_smul, AlgHom.id_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open GlobalTheory.FockSubst GlobalTheory.FockCompare GlobalTheory.OrientedHeis in

theorem exists_change {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS B₁ B₂ : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT C₁ C₂ : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) (hT : ∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ))
    (h₁ : ∀ ρ, ∃ e, IsEigB (sS ρ) (B₁ ρ) e) (h₂ : ∀ ρ, ∃ e, IsEigB (sS ρ) (B₂ ρ) e)
    (k₁ : ∀ ρ, ∃ e, IsEigB (sT ρ) (C₁ ρ) e) (k₂ : ∀ ρ, ∃ e, IsEigB (sT ρ) (C₂ ρ) e) :
    ∃ σ : PolF D T.rank S.rank ≃ₗ[ℂ] PolF D T.rank S.rank, ∀ f, IsThetaFunO ψ S T f → ∀ P,
      pureTensorO ψ θ S T sS sT B₂ C₂ f P = pureTensorO ψ θ S T sS sT B₁ C₁ f (σ P) := by
  classical
  choose e₁ h₁ using h₁
  choose e₂ h₂ using h₂
  choose d₁ k₁ using k₁
  choose d₂ k₂ using k₂
  let c := fun τ => coef (B₁ τ) (B₂ τ) (C₁ τ) (C₂ τ) (e₁ τ) (d₁ τ)
  let c' := fun τ => coef (B₂ τ) (B₁ τ) (C₂ τ) (C₁ τ) (e₂ τ) (d₂ τ)
  refine ⟨(AlgEquiv.ofAlgHom (sub c) (sub c') (sub_comp c' c fun τ => coef_mul (h₂ τ) (h₁ τ) (k₂ τ) (k₁ τ))
    (sub_comp c c' fun τ => coef_mul (h₁ τ) (h₂ τ) (k₁ τ) (k₂ τ))).toLinearEquiv, fun f hf P => ?_⟩
  have hA : ∀ (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f) :=
    fun _ _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f f', IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T f' → aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i (f + f') =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f +
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f' :=
    fun _ _ _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f :=
    fun _ _ _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i j f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' j f) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' j
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f) :=
    fun _ _ i j _ h => aPlus_comm (sS := sS) (sT := sT) hψ hθ i.1 _ hS hT j.1 _ h
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B₂ C₂ i g =
      ∑ b, c i.1 i.2 b • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B₁ C₁ (i.1, b) g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, c]
    have eS : B₂ ρ = B₁ ρ * ((B₁ ρ)⁻¹ * B₂ ρ) := (Matrix.mul_nonsing_inv_cancel_left _ _ (h₁ ρ).1).symm
    have eT : C₂ ρ = C₁ ρ * ((C₁ ρ)⁻¹ * C₂ ρ) := (Matrix.mul_nonsing_inv_cancel_left _ _ (k₁ ρ).1).symm
    have eI : ((B₁ ρ)⁻¹ * B₂ ρ)⁻¹ = (B₂ ρ)⁻¹ * B₁ ρ := by
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (h₁ ρ).1]
    have eU := GlobalTheory.FockSubBoth.unitMap_mul_both (B₁ ρ) ((B₁ ρ)⁻¹ * B₂ ρ) (C₁ ρ) ((C₁ ρ)⁻¹ * C₂ ρ) a j
    rw [← eS, ← eT, eI] at eU
    rw [eU, aPlus_dir_sum hψ hθ ρ _ _ hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (cplxO_unitMap_eig (h₁ ρ) (k₁ ρ) b.1 b.2), coef, cj_apply]
  unfold pureTensorO
  exact pure_subst (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (hA _ _) (Ac _ _) (Aadd _ _) (Asm _ _) (hA _ _) (Ac _ _) (Aadd _ _) (Asm _ _)
    (fun v b => c v.1 v.2 b) (fun v b => (v.1, b)) key hf P

theorem IsEigB.neg {n : ℕ} {s B : Matrix (Fin n) (Fin n) ℂ} {e : Fin n → Bool} (h : IsEigB s B e) :
    IsEigB (-s) B (fun a => !e a) := by
  refine ⟨h.1, ?_⟩
  rw [Matrix.neg_mul, h.2, ← Matrix.mul_neg, Matrix.diagonal_neg]
  congr 2
  funext a
  cases h : e a <;> simp [h]

theorem isEigB_of_onb {n p : ℕ} {G s B : Matrix (Fin n) (Fin n) ℂ} (h : IsONBasis G s B p) :
    IsEigB s B (fun a => decide (a.val < p)) := by
  simpa [IsEigB] using GlobalTheory.FockSubBoth.onb_sign h

theorem isEigB_fr {D : D7} {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : IsEigB (A.cart τ) (A.onb τ) (A.ε τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hu, ?_⟩
  rw [Fr.cart, Fr.onb, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rfl

theorem cart_frSgn_true {D : D7} {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : (frSgn true A).cart τ = -A.cart τ := by
  have e' : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
    ext a b
    by_cases h : a = b
    · subst h; cases h' : A.ε τ a <;> simp [Formalism.REAL.Jm, h']
    · simp [Formalism.REAL.Jm, h]
  show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = -((A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
  rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn_false {D : D7} {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : (frSgn false A).cart τ = A.cart τ := by
  show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor false (A.ε τ a)) * A.fr τ = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ
  simp

theorem isCartanInv_neg {D : D7} {V : HSp D} {τ : D.what₂.Tau} {s : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsCartanInv (gramAt D V τ) s) : IsCartanInv (gramAt D (GlobalTheory.Grid.neg V) τ) (-s) := by
  have e : gramAt D (GlobalTheory.Grid.neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, GlobalTheory.Grid.neg_gram]
  rw [e]
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

theorem dict_frames {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hX : X.Is ψ θ α β νH S) (FA : Fr A) (FA' : Fr A') (FW : Fr WW) (hA : X.rA.s = FA.cart) (hA' : X.rA'.s = FA'.cart)
    (hW : X.rW.s = FW.cart) :
    ∃ (σ : PolF D WW.rank A.rank ≃ₗ[ℂ] PolF D WW.rank A.rank) (σ' : PolF D WW.rank A'.rank ≃ₗ[ℂ] PolF D WW.rank A'.rank), ∀ t : T,
      IsFinF ψ θ true FA FW (X.f t) ∧ IsFinF ψ θ false FA' FW (X.f' t) ∧
      (∀ P g h, X.ker ψ θ t P h g = thetaKO (X.ω t) g h (fockF ψ θ true FA FW (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' ψ θ t P h g = thetaKO (X.ω' t) g h (fockF ψ θ false FA' FW (X.f' t) (σ' P)) := by
  have e1 : (frSgn true FA).cart = fun τ => -X.rA.s τ := funext fun τ => by rw [cart_frSgn_true, hA]
  have e2 : (frSgn false FA').cart = X.rA'.s := funext fun τ => by rw [cart_frSgn_false, hA']
  have hψ : IsStdChar D ψ (-1) := hX.isVac.1
  have hθ : IsInfFam θ := hX.isVac.2.inf
  have kW : ∀ ρ, ∃ e, IsEigB (X.rW.s ρ) (FW.onb ρ) e := fun ρ => ⟨_, hW ▸ isEigB_fr FW ρ⟩
  have kW' : ∀ ρ, ∃ e, IsEigB (X.rW.s ρ) (X.rW.B ρ) e := fun ρ => (hX.rigW.2.2 ρ).2.elim fun _ h => ⟨_, isEigB_of_onb h⟩
  obtain ⟨σ, hσ⟩ := exists_change (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) FA.onb X.rA.B X.rW.s FW.onb X.rW.B
    (fun ρ => isCartanInv_neg (hX.rigA.2.2 ρ).1) (fun ρ => (hX.rigW.2.2 ρ).1)
    (fun ρ => ⟨_, hA ▸ (isEigB_fr FA ρ).neg⟩) (fun ρ => (hX.rigA.2.2 ρ).2.elim fun _ h => ⟨_, (isEigB_of_onb h).neg⟩) kW kW'
  obtain ⟨σ', hσ'⟩ := exists_change A' WW hψ hθ X.rA'.s FA'.onb X.rA'.B X.rW.s FW.onb X.rW.B
    (fun ρ => (hX.rigA'.2.2 ρ).1) (fun ρ => (hX.rigW.2.2 ρ).1)
    (fun ρ => ⟨_, hA' ▸ isEigB_fr FA' ρ⟩) (fun ρ => (hX.rigA'.2.2 ρ).2.elim fun _ h => ⟨_, isEigB_of_onb h⟩) kW kW'
  refine ⟨σ, σ', fun t => ?_⟩
  have f1 := GlobalTheory.StageDict.fst_isFinF_frames X ψ θ α β νH S FA FW (congrFun e1) (fun τ => by rw [hW]) hX t
  have f2 := GlobalTheory.StageDict.isFinF_snd_frames X ψ θ α β νH S FA' FW (congrFun e2) (fun τ => by rw [hW]) hX t
  refine ⟨f1, f2, fun P g h => ?_, fun P g h => ?_⟩
  · unfold fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [e1, ← hW, hσ _ f1.1]
    try rfl
  · unfold fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [e2, ← hW, hσ' _ f2.1]
    try rfl

theorem top_dictionary : GlobalTheory.FunPr.Hypotheses₂ →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ (σ : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank)
      (σ' : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank), ∀ t : T,
      IsFinF W.ψ W.θ true A (frSum AV AV₁) (X.f t) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) ∧
      (∀ P g h, X.ker W.ψ W.θ t P h g = thetaKO (X.ω t) g h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' W.ψ W.θ t P h g = thetaKO (X.ω' t) g h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P)) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j X hG hX A A₁ AV AV₁ hA hA₁ hAV hAV₁
  exact dict_frames X _ _ _ _ _ _ hX.2.2.2.2.2.2.2 A A₁ (frSum AV AV₁)
    (hG.2.2.2.1.trans (funext fun τ => (hA τ).2.symm)) (hG.2.2.2.2.1.trans (funext fun τ => (hA₁ τ).2.symm))
    (hG.2.2.2.2.2 AV AV₁ hAV hAV₁)

end GlobalTheory.TopDict

end
