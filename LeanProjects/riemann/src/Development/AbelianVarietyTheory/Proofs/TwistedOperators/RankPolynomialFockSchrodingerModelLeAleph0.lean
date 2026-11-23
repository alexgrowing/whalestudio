import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.FockCount

open NumberField

theorem incM_map_piInf' {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) :
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) = J.map τ.1 := by
  ext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, GlobalTheory.AdelicU.compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    GlobalTheory.AdelicU.infEmb_tmul]

theorem rank_tens_le (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) :
    Module.rank ℂ (GlobalTheory.RealLift.Tens F P Q R S) ≤ Cardinal.aleph0 := by
  classical
  let b := _root_.Basis.piTensorProduct (R := ℂ)
    (fun _ : InfinitePlace F => MvPolynomial.basisMonomials (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ)
  rw [← b.mk_eq_rank'']
  exact Cardinal.mk_le_aleph0

theorem rank_pol_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d r s r' s' : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  intro F E _ _ _ _ _ σ B n d r s r' s' X W M hB hX hW _hM
  classical
  have hcm := hB.cm
  have hstd := hB.std
  have hFr : ∀ w, ∃ A : Matrix (Fin n) (Formalism.BasicNotions.TH.Ix r s) ℂ,
      GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) A ∧ X.θ w * A = A * Formalism.BasicNotions.TH.Jm r s := by
    intro w
    rw [incM_map_piInf', one_smul]
    exact GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s _ _ (hX.sig w) (hX.cartan w)
  have hFrW : ∀ w, ∃ C : Matrix (Fin d) (Formalism.BasicNotions.TH.Ix r' s') ℂ,
      GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) C ∧
        W.θ w * C = C * Formalism.BasicNotions.TH.Jm r' s' := by
    intro w
    rw [incM_map_piInf']
    exact GlobalTheory.T.cartanEigen_orthonormalFrame_exists d r' s' _ _ (hW.sig w) (hW.cartan w)
  choose A hA hAθ using hFr
  choose C hC hCθ using hFrW
  have hFramed : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C :=
    ⟨one_mul _, hA, hC⟩
  have hder := GlobalTheory.T.archHeisenbergDerivatives_exist
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder F E σ (Fin n) (Fin d) (Fin n × Fin d) r s r' s' B.ψ B.emb (incM F X.J)
    (incM F W.J) M.co 1 Complex.I A C hcm hstd hFramed
  have hrange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder) F E σ n d r s r' s' X W M B.ψ B.emb A C Φ
    hcm hstd hFramed hAθ hCθ hΦ
  rw [← hrange]
  exact (rank_range_le Φ).trans (rank_tens_le F r s r' s')

end GlobalTheory.FockCount
