import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueEisenstein.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n k : ℕ} {J : Matrix (Fin n) (Fin n) E} {X : Matrix (Fin n) (Fin k) E}

omit [NumberField E] in

theorem scalesBy_mul {p q : GAd σ J} {β γ : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β)
    (e' : ScalesBy σ J X q γ) : ScalesBy σ J X (p * q) (β * γ) := by
  unfold ScalesBy at *
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Units.val_mul, Matrix.mul_assoc]

omit [NumberField E] in

theorem scalesBy_inv {p : GAd σ J} {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β) :
    ScalesBy σ J X p⁻¹ β⁻¹ := by
  unfold ScalesBy at *
  calc (matHom _ σ J p⁻¹).1 * adMat F X = (matHom _ σ J p⁻¹).1 * (adMat F X * β.1 * (β⁻¹).1) := by
        rw [Matrix.mul_assoc (adMat F X), ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * adMat F X * (β⁻¹).1 := by
        rw [← e]; simp only [Matrix.mul_assoc]
    _ = adMat F X * (β⁻¹).1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem absE_pos (u : (AF F ⊗[F] E)ˣ) : (0 : ℝ) < absE F E u := by
  have h : absE F E u * absE F E u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E u ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact_mod_cast pos_iff_ne_zero.2 this

theorem isCompact_isHt_scales : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ IsHt (levelAll σ J L a) h ∧ ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h H
  haveI := H.lat
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll H.cm J L a
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx H.cm H.herm H.witt
  have hsc : ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
    intro p β e g
    obtain ⟨q, γ, e', k, hk, rfl⟩ := H.iwa g
    rw [← mul_assoc, H.ht _ _ (scalesBy_mul e e') _ hk, H.ht _ _ e' _ hk, map_mul, map_mul, NNReal.coe_mul]
  let φ : GAd σ J → Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E) := fun p =>
    adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X)
  have h1 : adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    simp only [adMat, ← Matrix.map_mul, hyx]; simp
  have hφ : ∀ p β, ScalesBy σ J X p β → φ p = β.1 := fun p β e => by
    unfold ScalesBy at e
    show adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X) = β.1
    rw [e, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have cφ : Continuous φ := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  let P := GlobalTheory.StdPar.frameStab σ J X (⊤ : Subgroup (GL (Fin (r + 1)) (AF F ⊗[F] E)))
  have cP : IsClosed (P : Set (GAd σ J)) := GlobalTheory.StdPar.isClosed_frameStab hyx isClosed_univ
  have hP : ∀ p : P, ScalesBy σ J X p.1 p.2.choose := fun p => p.2.choose_spec.2
  let u : P → (AF F ⊗[F] E)ˣ := fun p => Matrix.GeneralLinearGroup.det p.2.choose
  have cu : Continuous u := Units.continuous_iff.2
    ⟨((cφ.comp continuous_subtype_val).matrix_det).congr fun p => by
        simp only [Function.comp, u, hφ _ _ (hP p)]; rfl,
      ((cφ.comp (continuous_subtype_val.inv)).matrix_det).congr fun p => by
        show (φ (p.1⁻¹)).det = _
        rw [hφ _ _ (scalesBy_inv (hP p)), ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]⟩
  refine ⟨hK, ⟨fun g => ?_, ?_, fun k hk => by simpa using H.ht 1 1 (by simp [ScalesBy]) k hk, fun g => ?_⟩, hsc⟩
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    rw [H.ht _ _ e _ hk]; exact absE_pos _
  · refine GlobalTheory.Doubling.continuous_of_prod cP hK
      (fun g => let ⟨p, β, e, k, hk, e'⟩ := H.iwa g; ⟨⟨p, β, trivial, e⟩, k, hk, e'⟩) ?_
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (cu.comp continuous_fst))).congr
      fun x => (H.ht _ _ (hP x.1) _ x.2.2).symm
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    refine ⟨k, hk, fun x => ?_⟩
    rw [mul_assoc, hsc _ _ e, H.ht _ _ e _ hk]

end GlobalTheory.ResidueEisenstein.HtCont

end
