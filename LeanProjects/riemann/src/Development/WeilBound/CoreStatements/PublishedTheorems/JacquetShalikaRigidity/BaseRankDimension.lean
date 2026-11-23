import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundAdic

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace BaseRankDimension

open scoped ValuativeRel

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_pos (g : GA E k) : 0 < Dt g := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2

theorem dt_mul (g h : GA E k) : Dt (g * h) = Dt g * Dt h := by
  simp only [Dt, map_mul, Positive.val_mul]

theorem continuous_det' : Continuous (GeneralLinearGroup.det : GA E k → (Ad E)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · have : (fun g : GA E k => (((GeneralLinearGroup.det g)⁻¹ : (Ad E)ˣ) : Ad E)) =
        fun g : GA E k => ((g⁻¹ : GA E k) : Matrix (Fin k) (Fin k) (Ad E)).det := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem dt_cont : Continuous (Dt : GA E k → ℝ) :=
  continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp continuous_det')

theorem dt_rat (γ : GL (Fin k) E) : Dt (ratGL E k γ) = 1 := by
  have h : GeneralLinearGroup.det (ratGL E k γ) = GroundTheory.Global.IdeleGroup.diagonal E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  rw [Dt, h, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, Positive.val_one]

theorem dt_uu (j : ℕ) (u : GA E k) (hu : UU j u) : Dt u = 1 := by
  have h : GeneralLinearGroup.det u = 1 := by
    refine Units.ext ?_
    change (u : Matrix (Fin k) (Fin k) (Ad E)).det = 1
    rw [Matrix.det_of_isUpperTriangular (fun i c hc => hu.1 i c hc)]
    exact Finset.prod_eq_one fun i _ => hu.2.1 i
  rw [Dt, h, map_one, Positive.val_one]

theorem dt_invT (g : GA E k) : Dt (invT g) = (Dt g)⁻¹ := by
  have h : GeneralLinearGroup.det (invT g) = (GeneralLinearGroup.det g)⁻¹ := by
    rw [← map_inv]
    refine Units.ext ?_
    change ((g⁻¹ : GA E k) : Matrix (Fin k) (Fin k) (Ad E))ᵀ.det = _
    rw [Matrix.det_transpose]; rfl
  rw [Dt, Dt, h, map_inv]
  rfl

variable [IsTotallyComplex E]

theorem dt_eq (g : GA E k) : Dt g =
    (∏ w : InfinitePlace E, ‖((GeneralLinearGroup.det (jumpWindows.cInf g) : (Cinf E)ˣ) : Cinf E) w‖ ^ w.mult) *
      ∏ᶠ v : Pl E, ‖((GeneralLinearGroup.det (jumpWindows.cLoc v g) : (v.adicCompletion E)ˣ) : v.adicCompletion E)‖ := by
  rw [Dt, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [jumpWindows.cInf, GlobalTheory.CuspRep.det_map]
    congr 1
    exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm
  · refine finprod_congr fun v => ?_
    rw [jumpWindows.cLoc, GlobalTheory.CuspRep.det_map]
    rfl

theorem inf_one : (∏ w : InfinitePlace E, ‖((GeneralLinearGroup.det (1 : GL (Fin k) (Cinf E)) : (Cinf E)ˣ) : Cinf E) w‖ ^ w.mult) = 1 := by
  simp

omit [IsTotallyComplex E] in
theorem nrm_pi (l : ℤ) (w : Pl E) :
    ‖(GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ^ l‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-l) := by
  have h0 : (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ≠ 0 := fun h =>
    (GLnLocal.irreducible_uniformizer (w.adicCompletion E)).ne_zero (Subtype.ext h)
  rw [norm_zpow, ← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow w h0,
    GroundTheory.BlockD.SatakeBound.valued_uniformizer_eq w, WithZero.log_exp, ← _root_.zpow_mul, neg_one_mul]

theorem dt_fl (h3 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cInf (fl k w u : GA E k) = 1)
    (h4 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cLoc w (fl k w u : GA E k) = u)
    (h5 : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → jumpWindows.cLoc v (fl k w u : GA E k) = 1)
    (w : Pl E) (x : GL (Fin k) (w.adicCompletion E)) :
    Dt (fl k w x) = ‖((GeneralLinearGroup.det x : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ := by
  rw [dt_eq, h3, inf_one, one_mul, finprod_eq_single _ w (fun v hv => by rw [h5 w v x hv, map_one, Units.val_one, norm_one]), h4]

theorem dt_torus (h3 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cInf (fl k w u : GA E k) = 1)
    (h4 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cLoc w (fl k w u : GA E k) = u)
    (h5 : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → jumpWindows.cLoc v (fl k w u : GA E k) = 1)
    (w : Pl E) (l : Fin k → ℤ) :
    Dt (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l)) = (Ideal.absNorm w.asIdeal : ℝ) ^ (-∑ i, l i) := by
  rw [dt_fl h3 h4 h5]
  change ‖((Iwasawa.torusPow (w.adicCompletion E) k l : GL (Fin k) (w.adicCompletion E)) :
    Matrix (Fin k) (Fin k) (w.adicCompletion E)).det‖ = _
  rw [Iwasawa.coe_torusPow, Matrix.det_diagonal, norm_prod]
  simp only [nrm_pi]
  have hN : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero w
  rw [← Finset.sum_neg_distrib]
  refine Finset.induction_on (Finset.univ : Finset (Fin k)) (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hN]

theorem dt_split (h1 : ∀ y, jumpWindows.cInf (infGL E k y) = y) (h2 : ∀ (w : Pl E) y, jumpWindows.cLoc w (infGL E k y) = 1) (t : ℝ) :
    Dt (splitCentre E k t) = Real.exp (k * Module.finrank ℚ E * t) := by
  rw [dt_eq, splitCentre, h1]
  simp only [h2, map_one, Units.val_one, norm_one, finprod_one, mul_one]
  have e : ∀ w : InfinitePlace E, ‖((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin k)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ))) : (Cinf E)ˣ) : Cinf E) w‖ = Real.exp t ^ k := by
    intro w
    change ‖(Matrix.scalar (Fin k) ((expU fun _ : InfinitePlace E => (t : ℂ) : (Cinf E)ˣ) : Cinf E)).det w‖ = _
    simp [expU, Complex.norm_exp]
  simp only [e]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem dt_kappa (κ : GA E k) (hκ : jumpWindows.cInf κ = 1)
    (hint : ∀ w : Pl E, jumpWindows.cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) : Dt κ = 1 := by
  rw [dt_eq, hκ, inf_one, one_mul]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  obtain ⟨u, hu⟩ := hint v
  rw [← hu]
  set d := GeneralLinearGroup.det u with hd
  have ex : ((GeneralLinearGroup.det (GLnLocal.integralGLHom (v.adicCompletion E) k u) : (v.adicCompletion E)ˣ) :
      v.adicCompletion E) = ((d : 𝒪[v.adicCompletion E]) : v.adicCompletion E) := by
    change (Matrix.det ((RingHom.mapMatrix (𝒪[v.adicCompletion E]).subtype) (u : Matrix (Fin k) (Fin k) _))) = _
    rw [← RingHom.map_det]
    rfl
  rw [ex]
  set x : v.adicCompletion E := ((d : 𝒪[v.adicCompletion E]) : v.adicCompletion E) with hx
  have hx0 : x ≠ 0 := fun h => d.ne_zero (Subtype.ext h)
  have hv1 : Valued.v x ≤ 1 := GroundTheory.BlockD.SatakeBound.valued_le_one_of_mem (w := v) (d : 𝒪[v.adicCompletion E]).2
  have hxy : x * ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) = 1 := by
    rw [hx, ← Subring.coe_mul, Units.mul_inv]; rfl
  have hv2 : Valued.v ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) ≤ 1 :=
    GroundTheory.BlockD.SatakeBound.valued_le_one_of_mem (w := v) ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : 𝒪[v.adicCompletion E]).2
  have hv : Valued.v x = 1 := by
    refine le_antisymm hv1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) := by
          rw [← map_mul, hxy, map_one]
      _ ≤ Valued.v x * 1 := by gcongr
      _ = Valued.v x := mul_one _
  rw [← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v hx0, hv, WithZero.log_one, zpow_zero]

end BaseRankDimension

theorem determinant_basic_of_G0 : jumpWindows.G0 → D0 := by
  intro hG E _ _ _ k
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hG E k
  exact ⟨BaseRankDimension.dt_pos, BaseRankDimension.dt_mul, BaseRankDimension.dt_cont, BaseRankDimension.dt_rat, BaseRankDimension.dt_uu, BaseRankDimension.dt_invT, BaseRankDimension.dt_split h1 h2,
    fun t g => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t g, fun s t => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add s t,
    BaseRankDimension.dt_torus h3 h4 h5, fun κ hκ hint => BaseRankDimension.dt_kappa κ hκ hint⟩

end PositivityTheory.AdelicQuotientData

end
