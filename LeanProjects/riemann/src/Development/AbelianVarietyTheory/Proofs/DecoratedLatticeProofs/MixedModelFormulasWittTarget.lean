import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordsConjHermitianAdjointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.MixTargetProof

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {D : D7}

theorem cj_smul {X Y : Type} (e : Y → X) (c : ℂ) (φ : X → ℂ) : cj e (c • φ) = starRingEnd ℂ c • cj e φ := by
  funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem cj_dagger_inj (S T : HSp D) {a b : WO S T → ℂ} (h : cj (dagger T S) a = cj (dagger T S) b) : a = b := by
  have h' := congrArg (cj (dagger S T)) h
  rwa [cj_cj (dagger T S) (dagger S T) (dagger_dagger S T), cj_cj (dagger T S) (dagger S T) (dagger_dagger S T)] at h'

theorem conjAdjoint_cj {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem conj_psi_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : AF D.host.F) :
    starRingEnd ℂ (ψ (-q)) = ψ q := by
  rw [← Complex.inv_eq_conj (hψ.1.2.1 _), AddChar.map_neg_eq_inv, inv_inv]

theorem conj_levi_coeff' (z : Circle) (r : ℝ) :
    starRingEnd ℂ ((z : ℂ) * (r : ℂ)) = ((z⁻¹ : Circle) : ℂ) * (r : ℂ) := by
  rw [map_mul, Circle.coe_inv_eq_conj, Complex.conj_ofReal]

theorem incA_conj_neg_inv : cA D (incA D (-D.host.xi0⁻¹)) = incA D D.host.xi0⁻¹ := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg]

theorem dagger_ofAdj (S T : HSp D) (z : Mx D S.rank T.rank) :
    dagger S T (ofAdj S T z) = incA D D.host.xi0⁻¹ • z := by
  rw [dagger, ofAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, incA_conj_neg_inv, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

theorem symplOH_dagger {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  rw [symplOH, symplOH, (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T).1 x y, mul_neg]

end GlobalTheory.MixTargetProof

namespace GlobalTheory.MixTargetProof

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {D : D7}

theorem nC_inv_incAdj_sub {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    mt T (d.nC c)⁻¹ ⬝ d.incAdj S y - d.incAdj S y =
      d.incX S (-(c.1 ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)))) := by
  rw [d.nC_inv, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, ← Matrix.mul_assoc, d.nC_jY,
    Matrix.add_mul, add_sub_cancel_left, AddSubgroup.coe_neg, Matrix.mul_assoc, Matrix.neg_mul]

theorem giA_adj_central {S : HSp D} {ρ : ℕ} (c : skewA D ρ) (y : Mx D S.rank ρ) :
    giA S ⬝ adj (-(c.1 ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)))) = (incA D D.host.xi0⁻¹ • y) ⬝ c.1 := by
  have hc : adj c.1 = -c.1 := c.2
  rw [adj_neg, adj_mul, hc, adj_smul, adj_mul, adj_adj, adj_gA, incA_conj_neg_inv]
  simp only [Matrix.mul_neg, neg_neg]
  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, giA_gA_cancel, Matrix.smul_mul]

theorem quadratic_form_xi_inverse {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ}
    (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank))
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    d.qS S c (incA D D.host.xi0⁻¹ • y) = -d.qT S c y := by
  obtain ⟨μ', 𝓕', -, hX, hY, -, -⟩ := GlobalTheory.T.wittMixedCoords_conj_hermitianAdjoint D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  rw [HypDec.qS, HypDec.qT, ← hX, ← giA_adj_central c y, ← hY, nC_inv_incAdj_sub, symplOH_dagger hψ]

end GlobalTheory.MixTargetProof

namespace GlobalTheory.MixTargetProof

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

section Read

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} {d : HypDec T T₀ ρ} {χS : (AE D)ˣ →* Circle}
  {om : Rep S T} {om₀ : Rep S T₀} {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
  {μ' : Measure (Mx D S.rank ρ)} {𝓕' : Set (Mx D S.rank ρ)} {f : WO S T → ℂ}
  (hsw : ∀ (f : WO S T → ℂ) y, d.mixS S ψ μ' 𝓕' (cj (dagger T S) f) (incA D D.host.xi0⁻¹ • y) =
    cj (dagger T₀ S) (d.mixT S ψ μ 𝓕 f y))
  (FS : FormulasS d ψ χS (conjAdjoint om) (conjAdjoint om₀) μ' 𝓕' (cj (dagger T S) f))
include hsw FS

theorem read_source (g : GA D S) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (g, 1) f) y = om₀ (g, 1) (d.mixT S ψ μ 𝓕 f (mt S g⁻¹ ⬝ y)) := by
  apply cj_dagger_inj S T₀
  have h1 := FS.target g (incA D D.host.xi0⁻¹ • y)
  rw [conjAdjoint_cj, hsw, Matrix.mul_smul, hsw, conjAdjoint_cj] at h1
  exact h1

theorem read_core (h₀ : GA D T₀) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (1, d.emb0 h₀) f) y = om₀ (1, h₀) (d.mixT S ψ μ 𝓕 f y) := by
  apply cj_dagger_inj S T₀
  have h1 := FS.core h₀ (incA D D.host.xi0⁻¹ • y)
  rw [conjAdjoint_cj, hsw, hsw, conjAdjoint_cj] at h1
  exact h1

theorem read_levi (a : GL (Fin ρ) (AE D)) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (1, d.levi a) f) y =
      (((χS (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) * (halfMod S.rank a : ℂ)) •
        d.mixT S ψ μ 𝓕 f (y ⬝ a.1) := by
  apply cj_dagger_inj S T₀
  have h1 := FS.levi a (incA D D.host.xi0⁻¹ • y)
  rw [conjAdjoint_cj, hsw, Matrix.smul_mul, hsw] at h1
  rw [cj_smul, conj_levi_coeff']
  exact h1

theorem read_unip (hψ : IsStdChar D ψ (-1)) (b : Mx D ρ T₀.rank) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (1, d.nB b) f) y = heisO ψ S T₀ (ofAdj S T₀ (y ⬝ b)) (d.mixT S ψ μ 𝓕 f y) := by
  apply cj_dagger_inj S T₀
  have h1 := FS.unip b (incA D D.host.xi0⁻¹ • y)
  rw [conjAdjoint_cj, hsw, Matrix.smul_mul, hsw, ← dagger_ofAdj, (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T₀).2.2.2] at h1
  exact h1

theorem read_centre (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) (c : skewA D ρ)
    (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (1, d.nC c) f) y = ψ (d.qT S c y) • d.mixT S ψ μ 𝓕 f y := by
  apply cj_dagger_inj S T₀
  have h1 : d.mixS S ψ μ' 𝓕' (conjAdjoint om (d.nC c, 1) (cj (dagger T S) f)) (incA D D.host.xi0⁻¹ • y) =
      ψ (d.qS S c (incA D D.host.xi0⁻¹ • y)) • d.mixS S ψ μ' 𝓕' (cj (dagger T S) f) (incA D D.host.xi0⁻¹ • y) :=
    FS.centre c _
  rw [conjAdjoint_cj, hsw, hsw, quadratic_form_xi_inverse hψ d μ 𝓕 hμ] at h1
  rw [cj_smul, ← conj_psi_neg hψ, Complex.conj_conj]
  exact h1

end Read

theorem mixedTarget : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedTarget D := by
  intro D ψ S T T₀ ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ f hf
  have hψ := hom.std
  obtain ⟨μ', 𝓕', hμ', -, -, -, hsw⟩ := GlobalTheory.T.wittMixedCoords_conj_hermitianAdjoint D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  have hF : IsThetaFunO ψ T S (cj (dagger T S) f) := ((GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T).2.2.1 f).2 hf
  have FS := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ T T₀ S ρ d χT χS (conjAdjoint om) (conjAdjoint om₀)
    (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS χT om hom) (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T₀ χS χT om₀ hom₀) μ' 𝓕' hμ' _ hF
  exact ⟨read_source hsw FS, read_core hsw FS, read_levi hsw FS, read_unip hsw FS hψ, read_centre hsw FS hψ hμ⟩

end GlobalTheory.MixTargetProof

end
