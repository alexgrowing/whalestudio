import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFockVacuumProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordEqOfPerConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.IoCmp

theorem pure_rename {ι ι' κ X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {A' : ι' → (X → ℂ) → (X → ℂ)} {g : X → ℂ}
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (e : κ → ι) (e' : κ → ι') (h : ∀ k, A (e k) = A' (e' k)) (Q : MvPolynomial κ ℂ) :
    pureTensorL A g (MvPolynomial.rename e Q) = pureTensorL A' g (MvPolynomial.rename e' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a : MvPolynomial ι ℂ),
      ← mul_one (MvPolynomial.C a : MvPolynomial ι' ℂ), MvPolynomial.C_mul', MvPolynomial.C_mul', map_smul, map_smul,
      GlobalTheory.FockIndep.pure_one, GlobalTheory.FockIndep.pure_one]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, map_mul (MvPolynomial.rename e), map_mul (MvPolynomial.rename e'), MvPolynomial.rename_X, MvPolynomial.rename_X, hX, hX', hp, h]

theorem aeval_scale {L Y : Type} (f : L → Y) (s : ℂ) {N : ℕ} {Q : MvPolynomial L ℂ} (hQ : Q.IsHomogeneous N) :
    MvPolynomial.aeval (fun ℓ => MvPolynomial.C s * MvPolynomial.X (f ℓ)) Q =
      MvPolynomial.C (s ^ N) * MvPolynomial.rename f Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m.degree = N := by
    have := hQ (MvPolynomial.mem_support_iff.1 hm)
    rwa [Finsupp.degree_eq_weight_one]
  rw [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hd]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Function.comp_apply, map_pow,
    Finsupp.degree_apply]
  ring

theorem isHomogeneous_of_span {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop)
    (a : T → ℕ → ℕ) {P : MvPolynomial (Letter T r n) k} (hP : P ∈ Submodule.span k (HHa r n k cc isX a)) :
    P.IsHomogeneous (∑ σ, ∑ i : Fin (r σ), a σ i) := by
  refine (Submodule.span_le (p := MvPolynomial.homogeneousSubmodule _ k _)).2 (fun Q hQ m hm => ?_) hP
  have h := hQ.2.2 m (MvPolynomial.mem_support_iff.2 hm)
  refine Eq.trans (b := m.degree) (by rw [Finsupp.degree_eq_weight_one]; rfl) ?_
  rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => h σ i

theorem lieFac_eq_pow {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (hx : 0 < xiR D)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    lieFac Dw (xiR D) a = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ ^ (∑ σ, ∑ i : Fin (Dw.mult σ), a (σ, i)) := by
  have h : 0 < 2 * Real.pi * xiR D := by positivity
  have h2 : (Real.sqrt (2 * Real.pi * xiR D))⁻¹ = Real.exp (-(Real.log (2 * Real.pi * xiR D) / 2)) := by
    rw [Real.exp_neg, ← Real.log_sqrt h.le, Real.exp_log (Real.sqrt_pos.2 h)]
  rw [h2, ← Real.exp_nat_mul, lieFac]
  congr 1
  push_cast
  ring

theorem two_div_fockScale (D : D7) (τ : D.what₂.Tau) : 2 / fockScale D τ = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ := by
  rw [fockScale, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq, div_mul_cancel_left₀ two_ne_zero]

theorem unitMap_submatrix {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (π : Fin m → Fin m)
    (c : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap B (B'.submatrix id π) c j = Formalism.IndefR.Datum.unitMap B B' (π c) j := by
  unfold Formalism.IndefR.Datum.unitMap
  congr 1
  ext a b
  by_cases h : b = j
  · subst h
    simp
  · simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ h]

theorem pureTensorO_rename {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) 1)
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (Z Z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (π : D.what₂.Tau → Fin T.rank → Fin T.rank) (hZ : ∀ τ, Z' τ = (Z τ).submatrix id (π τ)) {κ : Type} (ρ : κ → D.what₂.Tau)
    (c : κ → Fin T.rank) (b : κ → Fin S.rank) (Q : MvPolynomial κ ℂ) :
    pureTensorO ψ θ S T (fun _ => 1) s B Z f (MvPolynomial.rename (fun k => (ρ k, π (ρ k) (c k), b k)) Q) =
      pureTensorO ψ θ S T (fun _ => 1) s B Z' f (MvPolynomial.rename (fun k => (ρ k, c k, b k)) Q) := by
  have hX : ∀ B' v Q, pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f Q) := fun B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  refine pure_rename (hX Z) (hX Z') _ _ (fun k => ?_) Q
  simp only [aPlusAll, hZ, unitMap_submatrix]

end GlobalTheory.OneMapRef.IoCmp

end
