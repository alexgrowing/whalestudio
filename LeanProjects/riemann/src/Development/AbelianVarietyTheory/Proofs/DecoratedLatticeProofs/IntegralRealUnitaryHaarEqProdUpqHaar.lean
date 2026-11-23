import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HaarReal
open Formalism.IndefR.Eqv

theorem continuous_psiT (D : D7) (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) *
      psiT D τ (basAF D c) := by
    intro x
    conv_lhs => rw [← (basAF D).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c := fun c =>
    (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
  have halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a) := by
    have e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) =
        fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      funext a
      simp only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e]
    exact ((isInfFam_thetaC D) τ).2.comp continuous_fst
  have hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D)
      ((basAF D).repr x c)) * psiT D τ (basAF D c) := funext hsum
  rw [hfun]
  exact continuous_finset_sum _ fun c _ => (halg.comp (hc c)).mul continuous_const

end GlobalTheory.HaarReal

namespace GlobalTheory.HaarReal

open Formalism.IndefR.Eqv Formalism.MainNotions.StandardLattice

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem fr_mul_inv (τ : D.what₂.Tau) : M.fr τ * (M.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem inv_mul_fr (τ : D.what₂.Tau) : (M.fr τ)⁻¹ * M.fr τ = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

def toJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  M.fr τ * g * (M.fr τ)⁻¹

theorem ofFr_toJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (toJ M τ g) = g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr toJ
  calc (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ
      = ((M.fr τ)⁻¹ * M.fr τ) * g * ((M.fr τ)⁻¹ * M.fr τ) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [inv_mul_fr, Matrix.one_mul, Matrix.mul_one]

theorem toJ_ofFr (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    toJ M τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ u) = u := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr toJ
  calc M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ) * (M.fr τ)⁻¹
      = (M.fr τ * (M.fr τ)⁻¹) * u * (M.fr τ * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = u := by rw [fr_mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem toJ_mul (τ : D.what₂.Tau) (g h : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    toJ M τ (g * h) = toJ M τ g * toJ M τ h := by
  unfold toJ
  calc M.fr τ * (g * h) * (M.fr τ)⁻¹ = M.fr τ * g * ((M.fr τ)⁻¹ * M.fr τ) * h * (M.fr τ)⁻¹ := by
        rw [inv_mul_fr, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = M.fr τ * g * (M.fr τ)⁻¹ * (M.fr τ * h * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]

theorem toJ_one (τ : D.what₂.Tau) : toJ M τ 1 = 1 := by
  unfold toJ; rw [Matrix.mul_one, fr_mul_inv]

theorem inUJ_toJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) : Formalism.REAL.inUJ (M.ε τ) (toJ M τ g) := by
  have hG := M.fr_gram τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, fr_mul_inv, Matrix.conjTranspose_one]
  unfold Formalism.REAL.inUJ toJ
  calc (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        rw [hG, hg, ← hG]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε τ) := by rw [h1, fr_mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem unit_ofFr (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hu : Formalism.REAL.inUJ (M.ε τ) u) :
    (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ u)ᴴ * gramAt D V τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ u = gramAt D V τ := by
  have hG := M.fr_gram τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, fr_mul_inv, Matrix.conjTranspose_one]
  unfold Formalism.REAL.inUJ at hu
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr
  rw [← hG]
  calc ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * u * M.fr τ)
      = (M.fr τ)ᴴ * uᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * u * M.fr τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * (uᴴ * Formalism.REAL.Jm (M.ε τ) * u) * M.fr τ := by
        rw [h1, fr_mul_inv, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by rw [hu]

theorem inUJ_umat {n : ℕ} {ε : Fin n → Bool} (u : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε (umat u) := u.2

def uJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    Formalism.REAL.UJ (M.ε τ) :=
  ⟨⟨toJ M τ g, toJ M τ (ginv D V τ g), by rw [← toJ_mul, mul_ginv D V τ g hg, toJ_one],
    by rw [← toJ_mul, ginv_mul D V τ g hg, toJ_one]⟩, inUJ_toJ M τ g hg⟩

theorem infMat_mul (τ : D.what₂.Tau) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram (thetaC D τ) (g * h) =
      infMat D.sp.cm.sig V.gram (thetaC D τ) g * infMat D.sp.cm.sig V.gram (thetaC D τ) h := by
  rw [infMat_thetaC, infMat_thetaC, infMat_thetaC, matA_mul, Matrix.map_mul]

def fwd (g : GinfC V) : ∀ τ, Formalism.REAL.UJ (M.ε τ) := fun τ =>
  uJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V)) (infMat_unitary' D V _ τ)

theorem unitFam_ofFr (us : ∀ τ, Formalism.REAL.UJ (M.ε τ)) :
    IsUnitFam D V fun τ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ)) :=
  fun τ => unit_ofFr M τ _ (inUJ_umat (us τ))

def bwd (us : ∀ τ, Formalism.REAL.UJ (M.ε τ)) : GinfC V :=
  ⟨famH D V (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ))) (unitFam_ofFr M us),
    famH_mem_GinfC D V _ _⟩

theorem continuous_matA : Continuous (matA D V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_famM : Continuous (famM D V) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))))

theorem continuous_fwd : Continuous (fwd M) := by
  refine continuous_pi fun τ => Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · refine (((continuous_const (y := M.fr τ)).matrix_mul (((continuous_matA).comp continuous_subtype_val).matrix_map
      (continuous_psiT D τ))).matrix_mul (continuous_const (y := (M.fr τ)⁻¹))).congr fun g => ?_
    show M.fr τ * _ * _ = toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V))
    rw [toJ, infMat_thetaC]; rfl
  · have c0 : Continuous fun g : GinfC V => (matA D V (g : GA D V)).map (psiT D τ) :=
      ((continuous_matA).comp continuous_subtype_val).matrix_map (continuous_psiT D τ)
    refine (((continuous_const (y := M.fr τ)).matrix_mul (((continuous_const (y := (gramAt D V τ)⁻¹)).matrix_mul
      c0.matrix_conjTranspose).matrix_mul (continuous_const (y := gramAt D V τ)))).matrix_mul
      (continuous_const (y := (M.fr τ)⁻¹))).congr fun g => ?_
    show M.fr τ * _ * _ = toJ M τ (ginv D V τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V)))
    rw [toJ, ginv, infMat_thetaC]

theorem continuous_bwd : Continuous (bwd M) := by
  have hu : ∀ τ, Continuous fun us : (∀ τ, Formalism.REAL.UJ (M.ε τ)) => umat (us τ) := fun τ =>
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply τ)
  have hg : Continuous fun us : (∀ τ, Formalism.REAL.UJ (M.ε τ)) => fun τ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ)) :=
    continuous_pi fun τ => (continuous_const.matrix_mul (hu τ)).matrix_mul continuous_const
  refine Continuous.subtype_mk (continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)) _
  · exact continuous_famM.comp hg
  · have hi : Continuous fun us : (∀ τ, Formalism.REAL.UJ (M.ε τ)) =>
        fun τ => ginv D V τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ))) :=
      continuous_pi fun τ => (continuous_const.matrix_mul ((continuous_apply τ).comp hg).matrix_conjTranspose).matrix_mul
        continuous_const
    exact continuous_famM.comp hi

def eqv : GinfC V ≃ₜ* (∀ τ, Formalism.REAL.UJ (M.ε τ)) where
  toFun := fwd M
  invFun := bwd M
  left_inv g := by
    apply Subtype.ext
    refine (famH_unique D V _ (unitFam_ofFr M (fwd M g)) (g : GA D V) g.2 fun τ => ?_).symm
    show _ = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (toJ M τ _)
    rw [ofFr_toJ]
  right_inv us := by
    funext τ
    refine Subtype.ext (Units.ext ?_)
    show toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (famH D V _ (unitFam_ofFr M us))) = umat (us τ)
    rw [infMat_famH, toJ_ofFr]
  map_mul' g h := by
    funext τ
    apply Subtype.ext
    apply Units.ext
    show toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) ((g : GA D V) * h)) =
      toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) g) * toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) h)
    rw [infMat_mul, toJ_mul]
  continuous_toFun := continuous_fwd M
  continuous_invFun := continuous_bwd M

theorem ofFr_eqv (g : GinfC V) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (eqv M g τ)) = infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V) :=
  ofFr_toJ M τ _

end GlobalTheory.HaarReal

namespace GlobalTheory.HaarReal

open Formalism.IndefR.Eqv Formalism.MainNotions.StandardLattice

theorem integral_prod_eq : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (mR : Measure (GinfC V)) (μ : ∀ τ, Measure (Formalism.REAL.UJ (M.ε τ))), mR.IsHaarMeasure → (∀ τ, (μ τ).IsHaarMeasure) → ∃ c : ℝ, 0 < c ∧ ∀ F : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ, (∀ τ, Integrable (fun u : Formalism.REAL.UJ (M.ε τ) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u))) (μ τ)) → Integrable (fun g : GinfC V => ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) (g : GA D V))) mR ∧ ∫ g : GinfC V, ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) (g : GA D V)) ∂mR = (c : ℂ) * ∏ τ, ∫ u : Formalism.REAL.UJ (M.ε τ), F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u)) ∂μ τ := by
  intro D V S M θ hθ mR μ hmR hμ
  obtain rfl : θ = thetaC D := eq_thetaC D hθ
  set e := eqv M
  haveI : (mR.map e).IsHaarMeasure := e.isHaarMeasure_map mR
  set c := (mR.map e).haarScalarFactor (Measure.pi μ)
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have key : mR.map e = c • Measure.pi μ := Measure.isMulLeftInvariant_eq_smul _ _
  set E : GinfC V ≃ᵐ (∀ τ, Formalism.REAL.UJ (M.ε τ)) := e.toHomeomorph.toMeasurableEquiv
  have hmap : mR.map E = c • Measure.pi μ := key
  refine ⟨c, hc, fun F hF => ?_⟩
  set f' : (∀ τ, Formalism.REAL.UJ (M.ε τ)) → ℂ := fun us => ∏ τ, F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ)))
  have hf : (fun g : GinfC V => ∏ τ, F τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V))) = f' ∘ E := by
    funext g
    simp only [f', Function.comp_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← ofFr_eqv M g τ]
    rfl
  have hpi : Integrable f' (Measure.pi μ) :=
    Integrable.fintype_prod_dep (f := fun τ (u : Formalism.REAL.UJ (M.ε τ)) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u))) hF
  rw [hf]
  refine ⟨(integrable_map_equiv E f').mp (by rw [hmap]; exact hpi.smul_measure_nnreal), ?_⟩
  show ∫ x, f' (E x) ∂mR = _
  rw [← integral_map_equiv E f', hmap, integral_smul_nnreal_measure,
    integral_fintype_prod_eq_prod (f := fun τ (u : Formalism.REAL.UJ (M.ε τ)) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u)))]
  rw [NNReal.smul_def, Complex.real_smul]

end GlobalTheory.HaarReal
