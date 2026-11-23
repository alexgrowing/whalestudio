import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HermDiag

private theorem hermForm_eq_star_swap {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsHermitian)
    (z w : Fin g → ℂ) : hermForm A z w = star (hermForm A w z) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hA.apply j i]
  ring

private theorem eq_of_im_hermForm_eq_of_real_span_eq_univ {g : ℕ} {La : Type} [AddCommGroup La] (A B : Matrix (Fin g) (Fin g) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (P : La →+ (Fin g → ℂ))
    (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (h : ∀ a b, (hermForm A (P a) (P b)).im = (hermForm B (P a) (P b)).im) : A = B := by
  let L : (Fin g → ℂ) → (Fin g → ℂ) →ₗ[ℝ] ℝ := fun w =>
    { toFun := fun z => (hermForm A z w).im - (hermForm B z w).im
      map_add' := fun z z' => by
        simp only [hermForm, add_dotProduct, Complex.add_im]; ring
      map_smul' := fun t z => by
        simp only [hermForm, smul_dotProduct, Complex.smul_im, RingHom.id_apply, smul_eq_mul]; ring }
  have hL : ∀ w z, L w z = (hermForm A z w).im - (hermForm B z w).im := fun _ _ => rfl
  have zero_of : ∀ w, (∀ a, L w (P a) = 0) → ∀ z, L w z = 0 := by
    intro w hw z
    have h0 : L w = 0 := LinearMap.ext_on hP (fun y hy => by
      obtain ⟨a, rfl⟩ := hy
      simpa using hw a)
    rw [h0]; rfl
  have key1 : ∀ a z, L (P a) z = 0 := fun a => zero_of _ (fun b => by rw [hL, h b a, sub_self])
  have key2 : ∀ z w, L w z = 0 := by
    intro z w
    refine zero_of w (fun a => ?_) z
    have h1 := key1 a w
    rw [hL] at h1 ⊢
    rw [hermForm_eq_star_swap A hA (P a) w, hermForm_eq_star_swap B hB (P a) w]
    simp only [Complex.star_def, Complex.conj_im]
    linarith
  ext i j
  apply Complex.ext
  · have h1 := key2 (Pi.single i Complex.I) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith
  · have h1 := key2 (Pi.single i 1) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith

theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), GoodEmb c σ → IsUnf U → (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu hg hU ho
  obtain ⟨hr, htype, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := htype k
  have hbij : Function.Bijective (relab c σ) := by
    rw [← Finite.injective_iff_bijective]
    intro τ₁ τ₂ h12
    ext y
    have h1 : σ (Formalism.L2.Pj.embF c τ₁ y) = σ (Formalism.L2.Pj.embF c τ₂ y) :=
      congrArg (fun f : E →+* ℂ => f y) h12
    exact congrArg Subtype.val (σ.injective h1)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq
      simpa using this
    have h2 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, h1, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
  have hkey : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := by
    intro τ
    have hg' : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 := hg
    have hρ : ((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
    rcases hsq τ with h | h
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (h.trans hρ.symm)
      have h3 : relab c σ τ (H.rt : E) = H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = H.rt0
        rw [e, hg']
      rw [h3, h]
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = -IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (by
          show τ (H.rt : E) = -((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ)
          rw [h, hρ])
      have h3 : relab c σ τ (H.rt : E) = -H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = -H.rt0
        rw [e, map_neg, hg']
      rw [h3, h]
  have hpm : ∀ τ, relab c σ τ ∈ (U.X k).Ψ → Dw.mult τ = Dw.p := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_pos hτ]
  have hqm : ∀ τ, relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = Dw.q := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_neg hτ]
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hr
    (relab c σ) hbij Dw.mult hpm hqm
  set idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans f with hidx
  have hz : ∀ a j, W.Pm a j = if ((idx j).2 : ℕ) < Dw.q then
      FD.hermC (idx j).1.1 (U.X k).Gm (FD.col (FD.mat x.1 (idx j).1) (idx j).2)
        (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))
      else ((FD.mat x.1 (idx j).1)⁻¹.mulVec (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))) (idx j).2 := by
    intro a j
    rw [W.pm_eq a j]
    unfold Formalism.L2.Pj.perFr
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨hin, h1, h2⟩ | ⟨hout, h1, h2, h3⟩
    · have hi : (U.X k).p0 + ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dif_pos hin, dif_pos hi, if_neg (by omega)]
      have e1 : (f (W.e j)).1 = ⟨relab c σ (W.e j).1, hin⟩ := Subtype.ext h1
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 + ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 + ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
    · have hcj : conjEmb (relab c σ (W.e j).1) = (f (W.e j)).1.1 := by
        rw [h1]
        exact RingHom.ext fun y => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl
      have hin' : conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ := by
        rw [hcj]
        exact (f (W.e j)).1.2
      have hi : (U.X k).p0 - 1 - ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dif_neg hout, dif_pos hin', dif_pos hi, if_pos (by omega)]
      have e1 : (f (W.e j)).1 = ⟨conjEmb (relab c σ (W.e j).1), hin'⟩ := Subtype.ext hcj.symm
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 - 1 - ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 - 1 - ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have hx : ∀ τ : (U.X k).Ψ, FD.gram τ.1 (U.X k).Gm (FD.mat x.1 τ) =
      Matrix.diagonal fun a : Fin r => ((FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ) := by
    intro τ
    rw [← hp0]
    exact ho τ
  set D0 : Matrix (Fin W.g) (Fin W.g) ℂ :=
    Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) with hD0
  have hD : ∀ a b, (hermForm Wu.Hm (W.Pm a) (W.Pm b)).im = (hermForm D0 (W.Pm a) (W.Pm b)).im := by
    intro a b
    rw [Wu.c1 a b, hD0, GlobalTheory.OrthoHerm.im_diag_eq_trace Dw.q (-(U.X k).ξ0) (U.X k).Gm (U.X k).Ψ
      (U.X k).cmType idx hcc x.1 hx (W.φ k a : Fin r → E) (W.φ k b : Fin r → E) (W.Pm a) (W.Pm b)
      (hz a) (hz b), ← W.isom k a b]
    push_cast
    rfl
  have hD0h : D0.IsHermitian := by
    rw [hD0]
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext j
    simp
  obtain ⟨-, -, -, hspan, -⟩ := W.per
  have hHm : Wu.Hm = D0 := eq_of_im_hermForm_eq_of_real_span_eq_univ Wu.Hm D0 Wu.herm hD0h W.Pm hspan hD
  rw [hHm, hD0]
  congr 1
  funext j
  have hpos := Wu.pos (Pi.single j 1) (by simp)
  rw [hHm, hD0] at hpos
  have hdiag : (hermForm (Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ))
      (Pi.single j 1) (Pi.single j 1)).re = 2 * ((idx j).1.1 (-(U.X k).ξ0)).im := by
    simp [hermForm]
  rw [hdiag, map_neg, Complex.neg_im] at hpos
  have hre : ((idx j).1.1 (U.X k).ξ0).re = 0 := by
    have h1 : starRingEnd ℂ ((idx j).1.1 (U.X k).ξ0) = -((idx j).1.1 (U.X k).ξ0) := by
      rw [← NumberField.IsCMField.complexEmbedding_complexConj (φ := (idx j).1.1) (x := (U.X k).ξ0),
        ← map_neg]
      congr 1
      exact (U.X k).ξ0_im
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hnorm : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖(idx j).1.1 (U.X k).ξ0‖ := by
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨-, h1, -⟩ | ⟨-, h1, -, -⟩
    · rw [h1]
    · rw [h1, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  have hfin : ((idx j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    rw [hnorm, ← (Complex.abs_im_eq_norm).mpr hre, map_neg, Complex.neg_im,
      abs_of_neg (by linarith)]
  rw [hfin]

end GlobalTheory.HermDiag
