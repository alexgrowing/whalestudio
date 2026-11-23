import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.TSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.LamSApply

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

theorem scalar_conj {N : ℕ} (c : ℂ) (hc : c ≠ 0) (M : Matrix (Fin N) (Fin N) ℂ) :
    ((Matrix.scalar (Fin N) c)⁻¹)ᴴ * M * (Matrix.scalar (Fin N) c)⁻¹ =
      (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) • M := by
  have hinv : (Matrix.scalar (Fin N) c)⁻¹ = (c⁻¹) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.scalar_apply, smul_mul_assoc, one_mul, ← Matrix.diagonal_smul]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, hc]
  rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one, smul_smul]
  congr 1
  rw [star_inv₀, ← mul_inv, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem mat_actL_scalar (g : Gp L N) (c : InfinitePlace L → ℂ) (hc : ∀ w, c w ≠ 0)
    (hg : ∀ w, ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (c w))
    (h : HS L N) (w : InfinitePlace L) :
    mat (actL g h) w = (((‖c w‖ ^ 2)⁻¹ : ℝ) : ℂ) • mat h w := by
  unfold actL actM
  simp only [LinearMap.coe_toContinuousLinearMap', coe_units_inv, LinearMap.coe_mk, AddHom.coe_mk,
    mat_mkHS]
  rw [hg w]
  exact scalar_conj (c w) (hc w) _

theorem actL_eq_of_scalar (g g' : Gp L N) (c c' : InfinitePlace L → ℂ) (hc : ∀ w, c w ≠ 0)
    (hc' : ∀ w, c' w ≠ 0)
    (hg : ∀ w, ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (c w))
    (hg' : ∀ w, ((g' w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (c' w))
    (hn : ∀ w, ‖c w‖ = ‖c' w‖) : actL g = actL g' := by
  ext1 h
  exact HS_ext fun w => by rw [mat_actL_scalar g c hc hg, mat_actL_scalar g' c' hc' hg', hn]

omit [NumberField L] in
theorem scal_coe (s : InfinitePlace L → ℂˣ) (w : InfinitePlace L) :
    ((scal L N s w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (s w : ℂ) := by
  simp [scal]

omit [NumberField L] in
theorem sc_coe (t : InfinitePlace L → ℝ) (w : InfinitePlace L) :
    (((sc t : Gp L N) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.scalar (Fin N) ((Real.exp (t w) : ℝ) : ℂ) := by
  simp [sc, scal]

omit [NumberField L] in
theorem emb_scalar_coe (u : (𝓞 L)ˣ) (w : InfinitePlace L) :
    ((emb L N (GeneralLinearGroup.scalar (Fin N) u) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.scalar (Fin N) (w.embedding ((u : 𝓞 L) : L)) := by
  ext i j
  simp [emb, toP, toK, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem exp_ne (x : ℝ) : ((Real.exp x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'

theorem tScal : TScal := by
  unfold TScal
  intro L _ _ N
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t t'
    funext w
    apply Units.ext
    simp only [Pi.mul_apply, Units.val_mul, sc_coe, Pi.add_apply, Real.exp_add, Complex.ofReal_mul,
      map_mul]
  · intro t x
    funext w
    apply Units.ext
    simp only [Pi.mul_apply, Units.val_mul, sc_coe]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
  · intro u
    have hx : ((u : 𝓞 L) : L) ≠ 0 := by simp
    refine actL_eq_of_scalar _ _ (fun w => w.embedding ((u : 𝓞 L) : L))
      (fun w => ((Real.exp (lg u w) : ℝ) : ℂ)) (fun w => (map_ne_zero _).2 hx) (fun w => exp_ne _)
      (emb_scalar_coe u) (fun w => sc_coe _ w) (fun w => ?_)
    rw [InfinitePlace.norm_embedding_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), lg, Real.exp_log (w.pos_iff.2 hx)]
  · intro s
    refine actL_eq_of_scalar _ _ (fun w => (s w : ℂ)) (fun w => ((Real.exp (Real.log ‖(s w : ℂ)‖) : ℝ) : ℂ))
      (fun w => (s w).ne_zero) (fun w => exp_ne _) (scal_coe s) (fun w => sc_coe _ w) (fun w => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.exp_log (norm_pos_iff.2 (s w).ne_zero)]
  · have key : ∀ (t : InfinitePlace L → ℝ) (h : HS L N) w i j,
        ((actL (sc t) h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) w i j =
          (((‖((Real.exp (t w) : ℝ) : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) *
            (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j := by
      intro t h w i j
      exact congrFun (congrFun (mat_actL_scalar (sc t) (fun w => ((Real.exp (t w) : ℝ) : ℂ))
        (fun w => exp_ne _) (fun w => sc_coe t w) h w) i) j
    rw [continuous_clm_apply]
    intro h
    apply continuous_induced_rng.2
    refine continuous_pi fun w => continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Function.comp_apply, key]
    refine (Complex.continuous_ofReal.comp ?_).mul continuous_const
    refine Continuous.inv₀ (by fun_prop) fun t => pow_ne_zero _ (norm_ne_zero_iff.2 (exp_ne _))

end PositivityTheory.KB.CentralizerFixed

end
