import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

noncomputable section

open Classical in

private def psi {K : Type} [Field K] (w : InfinitePlace K) : ℝ →+* w.Completion :=
  if hw : w.IsReal then ((ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toRingHom
  else ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm : ℂ ≃+* w.Completion).toRingHom.comp
    Complex.ofRealHom

private theorem continuous_psi {K : Type} [Field K] (w : InfinitePlace K) : Continuous (psi w) := by
  unfold psi
  split_ifs with hw
  · exact (isometryEquivRealOfIsReal hw).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm.continuous.comp
      Complex.continuous_ofReal

private theorem posRealElem_eq {K : Type} [Field K] (w : InfinitePlace K) {ρ : ℝ} (hρ : 0 < ρ) :
    posRealElem w (ρ ^ w.mult) = psi w ρ := by
  unfold posRealElem psi
  split_ifs with hw
  · simp [InfinitePlace.mult, hw]
  · simp [InfinitePlace.mult, hw, Real.sqrt_sq hρ.le]

private theorem real_hom_unique {A : Type} [Field A] [TopologicalSpace A] [T2Space A] (f g : ℝ →+* A)
    (hf : Continuous f) (hg : Continuous g) : f = g := by
  have h := Rat.denseRange_cast (𝕜 := ℝ) |>.equalizer hf hg (funext fun q => by simp)
  exact RingHom.ext (congrFun h)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem posIdele_fst {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    ((posIdele ρ hρ : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w = psi w ρ := by
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  exact posRealElem_eq w hρ

private theorem inf_posIdele (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace E) :
    InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) (((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F).1) w =
      ((posIdele ρ hρ : IdeleGroup E) : NumberField.AdeleRing (𝓞 E) E).1 w := by
  have hx : ((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F).1 =
      (RingHom.pi fun v : InfinitePlace F => psi v) ρ := funext fun v => posIdele_fst ρ hρ v
  rw [hx, posIdele_fst]
  have hc : Continuous (((Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
      (InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))).comp
        (RingHom.pi fun v : InfinitePlace F => psi v)) :=
    (continuous_apply w).comp (InfinitePlace.continuous_infiniteAdeleRingMap.comp
      (continuous_pi fun v => continuous_psi v))
  exact congrArg (fun f : ℝ →+* w.Completion => f ρ) (real_hom_unique _ (psi w) hc (continuous_psi w))

private theorem fin_posIdele {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) :
    ((posIdele ρ hρ : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 = 1 :=
  IsDedekindDomain.FiniteAdeleRing.ext K fun v => posIdele_finite ρ hρ v

private theorem adeleMap_posIdele (ρ : ℝ) (hρ : 0 < ρ) :
    AdeleBaseChange.adeleMap F E ((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F) =
      ((posIdele ρ hρ : IdeleGroup E) : NumberField.AdeleRing (𝓞 E) E) := by
  rw [AdeleBaseChange.adeleMap_apply]
  refine Prod.ext (funext fun w => inf_posIdele ρ hρ w) ?_
  change AdeleBaseChange.finiteAdeleMap F E _ = _
  rw [fin_posIdele, fin_posIdele, map_one]

private theorem exponent (n : ℕ) (hn : 0 < n) (s : {r : ℝ // 0 < r}) :
    rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹ (s ^ Module.finrank F E) =
      rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s := by
  refine Subtype.ext ?_
  change ((s ^ Module.finrank F E : {r : ℝ // 0 < r}) : ℝ) ^ ((n * Module.finrank ℚ E : ℝ))⁻¹ =
    (s : ℝ) ^ ((n * Module.finrank ℚ F : ℝ))⁻¹
  have hk : Module.finrank ℚ F * Module.finrank F E = Module.finrank ℚ E := Module.finrank_mul_finrank ℚ F E
  have hk0 : (Module.finrank F E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [Positive.val_pow, ← Real.rpow_natCast, ← Real.rpow_mul s.2.le, ← hk]
  congr 1
  push_cast
  field_simp

theorem UpperTheory.centralSection_baseChange :
    CentBC := by
  intro F E _ _ _ _ _ n s
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hn : 0 < n := i.pos
  have h1 : centralSection E n (s ^ Module.finrank F E) =
      diagUnits n fun _ => posIdeleHom E (rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s) := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, exponent n hn, scalarUnits_apply]
  have h2 : centralSection F n s =
      diagUnits n fun _ => posIdeleHom F (rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s) := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply]
  rw [h1, h2, coe_diagUnits]
  change AdeleBaseChange.adeleMap F E (((diagUnits n fun _ => posIdeleHom F _ : AdelicGLn.AdelicGL F n)).val i j) = _
  rw [coe_diagUnits]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdeleHom_apply, posIdeleHom_apply]
    exact adeleMap_posIdele _ _
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]
