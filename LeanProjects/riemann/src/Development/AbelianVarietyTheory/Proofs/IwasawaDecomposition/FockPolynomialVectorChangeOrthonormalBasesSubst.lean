import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.APlusComm

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockBasis

section Mat

variable {m n : ℕ}

theorem unitMap_mul (B u : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j =
      ∑ a, ∑ b, (k a i * u⁻¹ j b) • Formalism.IndefR.Datum.unitMap B B' a b := by
  have e : k * Matrix.single i j (1 : ℂ) * u⁻¹ = ∑ a, ∑ b, (k a i * u⁻¹ j b) • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.matrix_eq_sum_single (k * Matrix.single i j (1 : ℂ) * u⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc]
    · simp
  unfold Formalism.IndefR.Datum.unitMap
  rw [Matrix.mul_inv_rev]
  calc B' * k * Matrix.single i j (1 : ℂ) * (u⁻¹ * B⁻¹) = B' * (k * Matrix.single i j (1 : ℂ) * u⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e]
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

open scoped ComplexOrder in

theorem isCartanInv_one {G B : Matrix (Fin n) (Fin n) ℂ} (hB : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * 1 * B⁻¹ := by
    rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  refine ⟨Matrix.one_mul _, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_mul_same Matrix.PosDef.one ?_
  exact Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu))

end Mat

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (s : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
include hψ hθ hf

theorem aPlus_add_dir (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z + z') f =
      Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f + Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z' f := by
  have e : cplxO 1 s (z + z') = cplxO 1 s z + cplxO 1 s z' := by
    simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
  simp only [GlobalTheory.FockSubst.aPlus_eq, e, fun z => (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem dRho_smul_dir (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (c • z) f =
      (c.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ z f + (c.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (Complex.I • z) f := by
  have e : c • z = (c.re : ℂ) • z + (c.im : ℂ) • (Complex.I • z) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.1, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1,
    (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_smul_dir (e : Bool) (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (hz : cplxO 1 s z = (Complex.I * if e then 1 else -1) • z) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (c • z) f =
      (if e then c else star c) • Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f := by
  have e1 : cplxO 1 s (c • z) = c • cplxO 1 s z := by
    simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_comm c]
  simp only [GlobalTheory.FockSubst.aPlus_eq]
  rw [e1, hz, smul_smul, dRho_smul_dir hψ hθ τ hf c, dRho_smul_dir hψ hθ τ hf (c * _),
    dRho_smul_dir hψ hθ τ hf (Complex.I * _)]
  generalize ((fockScale D τ : ℝ) : ℂ)⁻¹ = r
  cases e
  · match_scalars <;> apply Complex.ext <;> simp <;> ring
  · match_scalars <;> apply Complex.ext <;> simp <;> ring

theorem aPlus_sum_dir {ι : Type} (t : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (∑ i ∈ t, z i) f =
      ∑ i ∈ t, Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z i) f := by
  induction t using Finset.induction_on with
  | empty =>
    have h := aPlus_add_dir hψ hθ τ s hf 0 0
    rw [add_zero] at h
    rw [Finset.sum_empty, Finset.sum_empty]
    exact left_eq_add.1 h
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, aPlus_add_dir hψ hθ τ s hf, ih]

theorem aPlus_unitMap_mul {ε : Fin T.rank → Bool} {B' k : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (ht : s * B' = B' * diagonal fun a => if ε a then (1 : ℂ) else -1) (hk : k ∈ Formalism.REAL.Kset ε)
    (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) {u : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) (i : Fin T.rank) (j : Fin S.rank) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j) f =
      ∑ a, ∑ b, (if ε i = true then k a i * u⁻¹ j b else k⁻¹ i a * u b j) •
        Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap B B' a b) f := by
  rw [unitMap_mul, aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [aPlus_smul_dir hψ hθ τ _ hf (ε a) _ _ (GlobalTheory.FockIndep.cplxO_unitMap ht a b)]
  refine congrArg (· • _) ?_
  have hk1 : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)
  have hu1 : u⁻¹ = uᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hu)
  have hc := congrFun (congrFun hk.2 a) i
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  rw [hk1, hu1, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, star_mul', star_star]
  by_cases h : ε a = ε i
  · rw [h]
  · have h0 : k a i = 0 := by
      cases h1 : ε a <;> cases h2 : ε i <;> simp only [h1, h2, not_true, if_true, Bool.false_eq_true, if_false] at h hc
      · linear_combination hc / 2
      · linear_combination -hc / 2
    simp [h0]

omit hψ hθ hf

section Generic

variable {ι κ μ X : Type} [Fintype κ] [Fintype μ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {g : X → ℂ} (c : ι → κ → μ → ℂ) (e : ι → κ → μ → ι)
    (hm : ∀ Q, P (pureTensorL A g Q))
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (hA : ∀ v h, P h → A' v h = ∑ a, ∑ b, c v a b • A (e v a b) h) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' g Q = pureTensorL A g
      (MvPolynomial.aeval (fun v => ∑ a, ∑ b, MvPolynomial.C (c v a b) * MvPolynomial.X (e v a b)) Q) := by
  have hC : ∀ (A : ι → (X → ℂ) → (X → ℂ)) a, pureTensorL A g (MvPolynomial.C a) = a • g := fun A a => by
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, GlobalTheory.FockIndep.pure_one]
  induction Q using MvPolynomial.induction_on with
  | C a => rw [hC, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hC]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, hX', hp, map_mul, MvPolynomial.aeval_X, hA _ _ (hm _)]
    simp only [Finset.sum_mul, map_sum, mul_assoc]
    simp only [MvPolynomial.C_mul', map_smul, smul_mul_assoc, hX]

end Generic

theorem pureTensorO_basis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (k : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∀ f, IsThetaFunO ψ S T f → ∀ P : PolF D T.rank S.rank, pureTensorO ψ θ S T (fun _ => 1) (cart M) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fsub M.ε k u P) := by
  intro D ψ θ S T Sp M BS hψ hθ hB k u hk hu f hf P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  have hfr := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hfr τ)]
    rfl
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ B B' v g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v g) :=
    fun _ _ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ B B' v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f Q) := fun B B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm (hth B B') ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hA : ∀ v g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) v g =
      ∑ a, ∑ b, (if M.ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
        else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) •
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (v.1, a, b) g := fun v g hg => by
    unfold aPlusAll
    exact aPlus_unitMap_mul hψ hθ v.1 _ hg (ht v.1) (hk v.1) _ (hu v.1) v.2.1 v.2.2
  have key := pure_subst (P := IsThetaFunO ψ S T) _ _
    (GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm (hth _ _) hf) (hX _ _) (hX _ _) hA P
  unfold pureTensorO fsub
  exact key

end GlobalTheory.FockBasis
