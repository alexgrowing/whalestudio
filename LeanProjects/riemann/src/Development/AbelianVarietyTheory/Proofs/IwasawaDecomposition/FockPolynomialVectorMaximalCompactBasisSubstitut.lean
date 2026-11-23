import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.APlusComm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubst

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex GlobalTheory.Ker.FockAlg

section Generic

variable {ι X : Type} {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {κ : Type} [Fintype κ] (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    (hA' : ∀ i f, P f → P (A' i f)) (hc' : ∀ i j f, P f → A' i (A' j f) = A' j (A' i f))
    (Aadd' : ∀ i f f', P f → P f' → A' i (f + f') = A' i f + A' i f')
    (Asm' : ∀ i (a : ℂ) f, P f → A' i (a • f) = a • A' i f)
    (c : ι → κ → ℂ) (r : ι → κ → ι) (h : ∀ i f, P f → A' i f = ∑ b, c i b • A (r i b) f)
    {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' f Q = pureTensorL A f
      (MvPolynomial.aeval (fun v : ι => ∑ b, c v b • (MvPolynomial.X (r v b) : MvPolynomial ι ℂ)) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), MvPolynomial.C_mul',
      map_smul, map_smul, pure_one, pure_one]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, pure_X_mul hadd hsm hA' hc' Aadd' Asm' hf, hp, h _ _ (pure_mem hadd hsm hA hf _), map_mul,
      MvPolynomial.aeval_X, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_assoc, map_smul, pure_X_mul hadd hsm hA hc Aadd Asm hf]

end Generic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
  (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) (t : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)

include hψ hθ hf

theorem dRho_csmul (w : ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (w • u) f =
      (w.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ u f + (w.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (I • u) f := by
  have e : w • u = (w.re : ℂ) • u + (w.im : ℂ) • (I • u) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (dRho_laws hψ hθ hf τ _).2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_dir_add (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (z + z') f =
      aPlus (heisO ψ S T) θ τ (cplxO s t) z f + aPlus (heisO ψ S T) θ τ (cplxO s t) z' f := by
  simp only [aPlus_eq, GlobalTheory.OrientedRealForm.cplxO_add, fun z => (dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem aPlus_dir_zero : aPlus (heisO ψ S T) θ τ (cplxO s t) 0 f = 0 := by
  have := aPlus_dir_add hψ hθ τ s t hf 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem aPlus_dir_sum {κ : Type} (F : Finset κ) (z : κ → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (∑ b ∈ F, z b) f = ∑ b ∈ F, aPlus (heisO ψ S T) θ τ (cplxO s t) (z b) f := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using aPlus_dir_zero hψ hθ τ s t hf
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, aPlus_dir_add hψ hθ τ s t hf, ih]

theorem aPlus_dir_smul (e : Bool) (w : ℂ) {u : Matrix (Fin T.rank) (Fin S.rank) ℂ}
    (hu : cplxO s t u = ((if e then 1 else -1 : ℂ) * I) • u) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (w • u) f =
      (if e then w else starRingEnd ℂ w) • aPlus (heisO ψ S T) θ τ (cplxO s t) u f := by
  have h1 : cplxO s t (w • u) = (w * ((if e then 1 else -1 : ℂ) * I)) • u := by
    rw [← smul_smul, ← hu]
    unfold cplxO
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  rw [aPlus_eq, aPlus_eq, h1, hu, dRho_csmul hψ hθ τ hf w, dRho_csmul hψ hθ τ hf (w * _),
    dRho_csmul hψ hθ τ hf (_ * I)]
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, w = x + y * I := ⟨w.re, w.im, (Complex.re_add_im w).symm⟩
  cases e
  · simp only [Bool.false_eq_true, if_false, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    match_scalars <;> simp <;> ring_nf <;> simp
  · simp only [if_true]
    match_scalars <;> simp <;> ring_nf <;> simp

omit hψ hθ hf

theorem unitMap_mul {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (a : Fin m)
    (j : Fin n) : unitMap B (B' * k) a j = ∑ b, k b a • unitMap B B' b j := by
  have e : k * single a j (1 : ℂ) = ∑ b, k b a • single b j (1 : ℂ) := by
    ext p q
    by_cases h : j = q
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, h]
  unfold unitMap
  rw [Matrix.mul_assoc B', e, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxO_unitMap {S' : D.what₂.Tau → SPar} (M : DSModel T S') {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin T.rank) (j : Fin n) : cplxO 1 (cart M τ) (unitMap B (onb M τ) b j) =
      ((if M.ε τ b then 1 else -1 : ℂ) * I) • unitMap B (onb M τ) b j := by
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have e : Formalism.REAL.Jm (M.ε τ) * single b j (1 : ℂ) = (if M.ε τ b then 1 else -1 : ℂ) • single b j (1 : ℂ) := by
    ext p q
    rw [Formalism.REAL.Jm, diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases h : b = p
    · rw [h]
    · simp [h]
  unfold cplxO unitMap cart onb
  rw [Matrix.mul_one, mul_comm _ I, ← smul_smul]
  congr 1
  calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * single b j (1 : ℂ)) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one, e, Matrix.mul_smul, Matrix.smul_mul]

theorem kset_zero {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) {a b : Fin n}
    (h : ε b ≠ ε a) : k b a = 0 := by
  have e := congrFun (congrFun hk.2 b) a
  rw [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at h e <;> simp at e <;>
    first | linear_combination (1 / 2 : ℂ) * e | linear_combination (-1 / 2 : ℂ) * e

theorem pureTensorO_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (k c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → IsThetaFunO ψ S T f → (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ a b, c τ b a = if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (MvPolynomial.aeval (fun v : FVar D T.rank S.rank => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P) := by
  intro D ψ θ S T S' M BS f k c hψ hθ hS hf hk hc P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hA : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f f', IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T f' → aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (f + f') =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f +
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f' :=
    fun _ _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f :=
    fun _ _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i j f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j f) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ i j _ h => aPlus_comm (sS := fun _ => 1) (sT := cart M) hψ hθ i.1 _ hS hT j.1 _ h
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (fun τ => onb M τ * k τ) i g =
      ∑ b, c i.1 b i.2.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (i.1, b, i.2.2) g := by
    rintro ⟨τ, a, j⟩ g hg
    simp only [aPlusAll]
    rw [unitMap_mul, aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aPlus_dir_smul hψ hθ τ _ _ hg _ _ (cplxO_unitMap τ M _ b j), hc]
    by_cases h : M.ε τ b = M.ε τ a
    · rw [h]
    · rw [kset_zero (hk τ) h]
      simp
  unfold pureTensorO
  exact pure_subst (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (hA _) (Ac _) (Aadd _) (Asm _) (hA _) (Ac _) (Aadd _) (Asm _)
    (fun v b => c v.1 b v.2.1) (fun v b => (v.1, b, v.2.2)) key hf P

end GlobalTheory.FockSubst
