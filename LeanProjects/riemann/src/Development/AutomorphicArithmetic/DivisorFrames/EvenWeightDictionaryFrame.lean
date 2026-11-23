import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

private theorem cs_frame {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (s v : Fin N → ℂ) :
    ‖∑ m, s m * v m‖ ^ 2 ≤ (∑ a, ‖∑ m, A m a * v m‖ ^ 2) * GlobalTheory.ChowHt.frameNorm A s ^ 2 := by
  set y := A⁻¹.mulVec s with hy
  have hs : A.mulVec y = s := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hA), Matrix.one_mulVec]
  have e : ∑ m, s m * v m = ∑ a, (∑ m, A m a * v m) * y a := by
    rw [← hs]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e, GlobalTheory.ChowHt.frameNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), ← hy]
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2
  exact Finset.sum_congr rfl fun a _ => norm_mul _ _

theorem UpperTheory.even_weight_dictionary_frame :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ (σ : c.F →+* ℂ), (∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom) → (∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G), ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))), ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2) → ∀ (N n : ℕ) (b : Module.Basis (Fin N) c.F (cuspOn U Z G)) (g : Matrix (Fin N) (Fin n) c.F) (A : (c.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), GlobalTheory.CompHt.IsFrame (normOn U x V dict Z G) (latOn U Z G) b g A → ∀ (κ : ℂ →+* ℂ), (∀ a, ‖κ a‖ = ‖a‖) → κ.comp (goodOf c σ) = σ → ∀ (τ : ℕ) (t : ℝ), ∀ f ∈ smallL U x V dict Z G τ t, ∀ z ∈ framesOn (U (goodOf c σ)) Z, ‖rdU (U (goodOf c σ)) (f : Rul Xo c) z.1 z.2‖ ^ 2 ≤ Real.exp (2 * τ * t) * (∑ a, ‖∑ m, A σ m a * κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2)‖ ^ 2) ^ τ := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G hG σ hd hspan N n b g A hF κ hκ hκσ τ t f hf z hz
  obtain ⟨hz1, hz2⟩ := hz
  have hz : z ∈ framesOn (U (goodOf c σ)) Z := ⟨hz1, hz2⟩
  have hN : ∀ (G' : WTZ E) (f' : Rul Xo c), homN (U (goodOf c σ)) x G' f' z =
      GlobalTheory.DegTop.normFac (U (goodOf c σ)) x G' z * ‖rdU (U (goodOf c σ)) f' z.1 z.2‖ := fun G' f' =>
    GlobalTheory.DegTop.homN_eq x _ G' f' z
  have hpos := GlobalTheory.DegTop.normFac_pos x (U (goodOf c σ)) G hz1
  set F := GlobalTheory.DegTop.normFac (U (goodOf c σ)) x G z with hFdef
  set S := ∑ a, ‖∑ m, A σ m a * κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2)‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ F ^ 2 * S := by positivity
  have h1 := hf.2 _ (goodEmb_goodOf c σ) ⟨z.1, z.2, hz1⟩ hz
  have h2 := GlobalTheory.CompHS.bergOn_le_bergCusp (x := x) hd hspan ⟨z.1, z.2, hz1⟩ hz
  have h3 : GlobalTheory.CompHS.bergCusp U x V dict Z G σ z ≤ ENNReal.ofReal (F ^ 2 * S) := by
    rw [GlobalTheory.CompHS.bergCusp_le_iff hB0]
    intro f' hf'
    have e1 := hF.norm σ ⟨f', hf'⟩
    have e2 : f' = ∑ m, b.repr ⟨f', hf'⟩ m • (b m : Rul Xo c) := by
      have := congrArg Subtype.val (b.sum_repr ⟨f', hf'⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    have e3 : κ (rdU (U (goodOf c σ)) f' z.1 z.2) =
        ∑ m, σ (b.repr ⟨f', hf'⟩ m) * κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2) := by
      conv_lhs => rw [e2]
      rw [map_sum, Finset.sum_apply, Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
      congr 1
      exact congrArg (fun φ : c.F →+* ℂ => φ (b.repr ⟨f', hf'⟩ m)) hκσ
    have e4 := cs_frame (A σ) (hF.herm σ) (fun m => σ (b.repr ⟨f', hf'⟩ m))
      (fun m => κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2))
    rw [← e3, hκ, e1] at e4
    rw [hN, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left e4 (sq_nonneg _)
  have h4 := h1.trans (mul_le_mul_right (pow_le_pow_left' (h2.trans h3) τ) _)
  have h5 : homN (U (goodOf c σ)) x (τ • G) f z = F ^ τ * ‖rdU (U (goodOf c σ)) (f : Rul Xo c) z.1 z.2‖ := by
    rw [hN, GlobalTheory.DegTop.normFac_nsmul x _ hG hz1]
  have h6 : ENNReal.ofReal (homN (U (goodOf c σ)) x (τ • G) f z ^ 2) ≤
      ENNReal.ofReal (Real.exp (2 * τ * t) * (F ^ 2 * S) ^ τ) := by
    rw [ENNReal.ofReal_pow (homN_nonneg _ _ _ _ _), ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow hB0]
    exact h4
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity), h5] at h6
  refine le_of_mul_le_mul_left (a := (F ^ τ) ^ 2) ?_ (by positivity)
  calc _ = (F ^ τ * ‖rdU (U (goodOf c σ)) (f : Rul Xo c) z.1 z.2‖) ^ 2 := by ring
    _ ≤ _ := h6
    _ = _ := by ring
