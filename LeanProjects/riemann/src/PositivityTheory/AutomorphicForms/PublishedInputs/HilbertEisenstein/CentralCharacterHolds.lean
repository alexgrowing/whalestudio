import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

namespace EisensteinCentralCharacter

variable {F : Type} [Field F] [NumberField F]

theorem thetaS_scalar_diagonal (Ψ : (Fin 2 → Ad F) → ℂ) (k : Fˣ) (h : GA F 2) :
    thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k : Ideles F) * h) = thetaS Ψ h := by
  unfold thetaS
  let e : {ξ : Fin 2 → F // ξ ≠ 0} ≃ {ξ : Fin 2 → F // ξ ≠ 0} :=
    { toFun := fun ξ => ⟨(k : F) • ξ.1, smul_ne_zero k.ne_zero ξ.2⟩
      invFun := fun ξ => ⟨((k⁻¹ : Fˣ) : F) • ξ.1, smul_ne_zero (k⁻¹).ne_zero ξ.2⟩
      left_inv := fun ξ => Subtype.ext (by simp [smul_smul])
      right_inv := fun ξ => Subtype.ext (by simp [smul_smul]) }
  have key : ∀ ξ : Fin 2 → F,
      rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k : Ideles F) * h : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) = rowA ((k : F) • ξ) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)) := by
    intro ξ
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    congr 1
    funext i
    rw [Matrix.vecMul_diagonal]
    simp [rowA, coe_diagonal, mul_comm]
  refine Eq.trans ?_ (e.tsum_eq fun ξ => Ψ (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))))
  exact tsum_congr fun ξ => by rw [key]; rfl

theorem hchar_diagonal (ω : HChar F) (k : Fˣ) : ω.1 (diagonal F k) = 1 := ω.2.2 k

theorem absD_nonneg (g : GA F 2) : 0 ≤ absD g := (IdeleGroup.ideleModule F _).2.le

theorem absD_scalar_mul (z : Ideles F) (g : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
      ((IdeleGroup.ideleModule F z : ℝ)) ^ 2 * absD g := by
  unfold absD
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_pow]
  rfl

theorem eisInt_mul_diag [IsTotallyReal F] (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) (k : Fˣ) :
    eisInt ω Ψ g t (u * diagonalToNormOne F k) = eisInt ω Ψ g t u := by
  unfold eisInt
  have h : moduleSection (w0 F) t * ((u * diagonalToNormOne F k : normOneSubgroup F) : Ideles F) =
      diagonal F k * (moduleSection (w0 F) t * (u : Ideles F)) := by
    rw [Subgroup.coe_mul, coe_diagonalToNormOne]
    ac_rfl
  rw [h, map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)),
    mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k)), thetaS_scalar_diagonal,
    map_mul ω.1, hchar_diagonal, one_mul]

theorem eisInt_scalar [IsTotallyReal F] (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (z : Ideles F) (g : GA F 2)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt ω Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) t u =
      ((ω.1 z : ℂˣ) : ℂ) * eisInt ω Ψ g (t * (normOneSplitting (w0 F) z).2)
        (u * (normOneSplitting (w0 F) z).1) := by
  set p := normOneSplitting (w0 F) z with hp
  have hz : z = (p.1 : Ideles F) * moduleSection (w0 F) p.2 := by
    rw [← normOneSplitting_symm_apply, hp, ContinuousMulEquiv.symm_apply_apply]
  have ht0 : (p.2 : ℝ) = (IdeleGroup.ideleModule F z : ℝ) := rfl
  have hmul : moduleSection (w0 F) (t * p.2) * ((u * p.1 : normOneSubgroup F) : Ideles F) =
      (moduleSection (w0 F) t * (u : Ideles F)) * z := by
    rw [hz, map_mul, Subgroup.coe_mul]
    ac_rfl
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) ((moduleSection (w0 F) t * (u : Ideles F)) * z) * g =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) := by
    rw [map_mul, mul_assoc]
  have hω : ((ω.1 ((moduleSection (w0 F) t * (u : Ideles F)) * z) : ℂˣ) : ℂ) =
      ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) * ((ω.1 z : ℂˣ) : ℂ) := by
    rw [map_mul ω.1, Units.val_mul]
  have habs : ((IdeleGroup.ideleModule F z : ℝ) ^ 2 * absD g) ^ ((1 : ℝ) / 2) =
      (IdeleGroup.ideleModule F z : ℝ) * absD g ^ ((1 : ℝ) / 2) := by
    have h0 : 0 ≤ (IdeleGroup.ideleModule F z : ℝ) := (IdeleGroup.ideleModule F z).2.le
    rw [Real.mul_rpow (by positivity) (absD_nonneg g), ← Real.rpow_natCast,
      ← Real.rpow_mul h0]
    norm_num
  have hc : (((t * p.2 : {r : ℝ // 0 < r}) : ℝ) : ℂ) =
      ((t : ℝ) : ℂ) * ((IdeleGroup.ideleModule F z : ℝ) : ℂ) := by
    rw [← ht0, ← Complex.ofReal_mul]
    rfl
  unfold eisInt
  rw [hmul, hsc, absD_scalar_mul, habs, hω, hc]
  have hωz : ((ω.1 z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hωA : ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  generalize thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)) = T
  generalize ((ω.1 z : ℂˣ) : ℂ) = a at hωz ⊢
  generalize ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) = b at hωA ⊢
  push_cast
  field_simp

theorem setIntegral_fd_mul (f : normOneSubgroup F → ℂ)
    (hf : ∀ (k : Fˣ) (u : normOneSubgroup F), f (u * diagonalToNormOne F k) = f u) (u0 : normOneSubgroup F) :
    ∫ u in normOneFundamentalDomain F, f (u * u0) ∂normOneMeasure F =
      ∫ u in normOneFundamentalDomain F, f u ∂normOneMeasure F := by
  have hE := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
  have hE' : IsFundamentalDomain (diagonalNormOne F).op
      ((fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F) (normOneMeasure F) := by
    refine hE.preimage_of_equiv (e := id)
      (measurePreserving_mul_right (normOneMeasure F) u0⁻¹).quasiMeasurePreserving Function.bijective_id ?_
    intro γ x
    show (γ • x) * u0⁻¹ = γ • (x * u0⁻¹)
    simp only [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
    exact mul_right_comm _ _ _
  have h1 : ∫ u in normOneFundamentalDomain F, f (u * u0) ∂normOneMeasure F =
      ∫ v in (fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F, f v ∂normOneMeasure F := by
    have := (measurePreserving_mul_right (normOneMeasure F) u0).setIntegral_preimage_emb
      (measurableEmbedding_mulRight u0) f ((fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F)
    rw [← this]
    congr 2
    ext x
    simp
  rw [h1]
  refine hE'.setIntegral_eq hE ?_
  intro γ x
  rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
  have hm : ((γ : (normOneSubgroup F)ᵐᵒᵖ)).unop ∈ diagonalNormOne F := Subgroup.mem_op.1 γ.2
  obtain ⟨k, hk⟩ := Subgroup.mem_subgroupOf.1 hm
  have he : ((γ : (normOneSubgroup F)ᵐᵒᵖ)).unop = diagonalToNormOne F k := Subtype.ext hk.symm
  rw [he, hf]

end EisensteinCentralCharacter

open EisensteinCentralCharacter in
theorem central_character_holds : SPois → SInt → SSmooth → SCent := by
  intro _ _ _ F _ _ _ ω c _ z g
  have h1 : ∀ t : {r : ℝ // 0 < r},
      ∫ u in normOneFundamentalDomain F, eisInt ω (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) t u
        ∂normOneMeasure F =
      ((ω.1 z : ℂˣ) : ℂ) * ∫ u in normOneFundamentalDomain F,
        eisInt ω (Phi c) g (t * (normOneSplitting (w0 F) z).2) u ∂normOneMeasure F := by
    intro t
    simp only [eisInt_scalar ω (Phi c) z g t]
    rw [integral_const_mul, setIntegral_fd_mul _ (fun k u => eisInt_mul_diag ω (Phi c) g _ u k)]
  unfold Eis
  simp only [h1]
  rw [integral_const_mul]
  exact congrArg (((ω.1 z : ℂˣ) : ℂ) * ·) (integral_mul_right_eq_self
    (fun t => ∫ u in normOneFundamentalDomain F, eisInt ω (Phi c) g t u ∂normOneMeasure F)
    (normOneSplitting (w0 F) z).2)

end UpperTheory.HilbertEisensteinWeightOne
