import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup

private theorem posIdele_inf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (s : ℝ) (hs : 0 < s)
    (w : InfinitePlace E) :
    ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  change GroundTheory.Global.posRealElem w _ = _
  unfold GroundTheory.Global.posRealElem
  rw [dif_neg hw]
  simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]

theorem UpperTheory.V.KernelIndexFullLattice.splitEq_holds :
    UpperTheory.V.KernelIndexFullLattice.SplitEq := by
  intro E _ _ _ a t
  refine Units.ext (Matrix.ext fun i j => ?_)
  have ha : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 i.pos.ne'
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have e : rpowHom ((a * Module.finrank ℚ E : ℝ))⁻¹ ⟨Real.exp (a * Module.finrank ℚ E * t), Real.exp_pos _⟩ =
      ⟨Real.exp t, Real.exp_pos t⟩ := by
    refine Subtype.ext ?_
    change Real.exp (a * Module.finrank ℚ E * t) ^ ((a * Module.finrank ℚ E : ℝ))⁻¹ = Real.exp t
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, e, posIdeleHom_apply, scalarUnits_apply,
    coe_diagUnits, splitCentre]
  set y : GL (Fin a) (Cinf E) :=
    Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)) with hy
  have h2 : ((infGL E a y).val i j).2 =
      (1 : Matrix (Fin a) (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) i j :=
    congrArg (fun g : GL (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) => g.val i j) (pFin_infGL y)
  have h1 : ∀ w, ((infGL E a y).val i j).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) :=
    fun w => congrFun (UpperTheory.V.Cm.infGL_entry y i j) w
  have hyv : y.val = Matrix.diagonal fun _ => (fun _ : InfinitePlace E => Complex.exp (t : ℂ)) := rfl
  refine Prod.ext (funext fun w => ?_) ?_
  · rw [h1, hyv]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdele_inf, Complex.ofReal_exp]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      exact map_zero _
  · rw [h2]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact IsDedekindDomain.FiniteAdeleRing.ext E fun v => (posIdele_finite _ _ v).symm
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl
