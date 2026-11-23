import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtGramOfImFormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivOfExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAbelianLogarithmStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix Filter Topology MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff CategoryTheory.Obj MonObj

namespace GlobalTheory.HodgeSmooth

theorem one_left {S : Scheme.{0}} (A : Over S) [GrpObj A] (y : Sp ℂ ⟶ S) :
    (1 : Over.mk y ⟶ A).left = y ≫ LieVB.unitSec A := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem mem_iff {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y) (z : Fin P.g → ℂ) :
    z ∈ d.u.Λ ↔ (d.u.ex z).left ≫ d.φ = y ≫ LieVB.unitSec P.A := by
  rw [← d.ex_zero, ← d.u.ker, ← (d.u.ker 0).2 (zero_mem _)]
  exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext
    (d.isPull.1.hom_ext h ((Over.w _).trans (Over.w _).symm))⟩

theorem form_dualGram_chg {n : ℕ} (T : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) (H : Matrix (Fin n) (Fin n) ℂ)
    (φ ψ : (Fin n → ℂ) → ℂ) :
    form (dualGram H) (fun a => fderiv ℂ φ 0 (Pi.single a 1)) (fun a => fderiv ℂ ψ 0 (Pi.single a 1)) =
      form (dualGram (chg (LinearMap.toMatrix' (T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) H))
        (fun a => fderiv ℂ (φ ∘ T) 0 (Pi.single a 1)) (fun a => fderiv ℂ (ψ ∘ T) 0 (Pi.single a 1)) := by
  have key (φ : (Fin n → ℂ) → ℂ) : (LinearMap.toMatrix' (T.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))ᵀ *ᵥ
      (fun a => fderiv ℂ (φ ∘ T) 0 (Pi.single a 1)) = fun a => fderiv ℂ φ 0 (Pi.single a 1) := by
    funext a
    have e : (Pi.single a 1 : Fin n → ℂ) = T (∑ c, T.symm (Pi.single a 1) c • Pi.single c 1) := by
      rw [← pi_eq_sum_univ', T.apply_symm_apply]
    rw [e, T.comp_right_fderiv, map_zero]
    simp [mulVec, dotProduct]
  rw [dualGram_chg (B := LinearMap.toMatrix' (T.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))), form_chg, key, key]
  rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
  congr 1
  exact LinearMap.ext fun v => T.apply_symm_apply v

theorem contDiffAt_dualForm {X : Scheme.{0}} (P : PPAS X) {m : ℕ} {B : Set (Fin m → ℂ)}
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} (d : ∀ b, P.RiemannData (y b)) (W : P.A.left.Opens)
    (f f' : Γ(P.A.left, W)) (hB : IsOpen B) (hb₀ : b₀ ∈ B) (hy : IsHolTo B y)
    (hW : ⊤ ≤ (y b₀ ≫ LieVB.unitSec P.A) ⁻¹ᵁ W) :
    ContDiffAt ℝ ∞ (fun b => form (dualGram (d b).H) ((d b).cov W f) ((d b).cov W f')) b₀ := by
  classical
  have := P.isAb.comm
  obtain ⟨g, B', e, hB', hb', he, hlift⟩ := RelExp.exists_relative_exp_of_smooth X P.A m B y b₀ P.isAb.smooth
    P.isAb.geomConnected hB hb₀ hy
  have hT := fun b hb => ExpCompare.exists_equiv_of_exp X P (y b) (d b) g (e b) (he b hb).2.1 (he b hb).2.2.1 (he b hb).2.2.2.1
    (he b hb).2.2.2.2.2 (he b hb).2.2.2.2.1
  obtain rfl : g = P.g := by
    obtain ⟨T, -⟩ := hT b₀ hb'
    simpa using T.toLinearEquiv.finrank_eq
  have : Nonempty ((Fin P.g → ℂ) ≃L[ℂ] (Fin P.g → ℂ)) := ⟨.refl _ _⟩
  choose! T hT using hT
  let ε : (Fin m → ℂ) × (Fin P.g → ℂ) → (Sp ℂ ⟶ P.A.left) := fun q => (e q.1 q.2).left
  have hol : IsHolTo (B' ×ˢ Set.univ) ε :=
    RelExp.isHolTo_of_holAt (hB'.prod isOpen_univ) fun q hq => (he q.1 hq.1).1 q.2
  have hker : ∀ b ∈ B', ∀ z, e b z = 1 ↔ T b z ∈ (d b).u.Λ := fun b hb z => by
    rw [mem_iff, ← hT b hb, ← one_left]
    exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩
  choose ζ hζ₀ hζ hζe using fun l : (d b₀).u.Λ => hlift ((T b₀).symm l)
    ((hker b₀ hb' _).2 (by simp))
  let H : (Fin m → ℂ) → Matrix (Fin P.g) (Fin P.g) ℂ := fun b =>
    chg (LinearMap.toMatrix' (T b : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))) (d b).H
  have hH : ∀ b v w, form (H b) v w = form (d b).H (T b v) (T b w) := fun b v w => by
    rw [form_chg, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    rfl
  have hsm : MContDiffAt ∞ H b₀ := GlobalTheory.contDiffAt_gram_of_im_form_const P.g m _ ζ H b₀
    (fun j => (hζ j).contDiffAt.restrict_scalars ℝ) (by
      have e₁ : (Set.range fun j => ζ j b₀) =
          (((T b₀).symm : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)).restrictScalars ℝ) '' (d b₀).u.Λ := by
        simp only [hζ₀]
        exact (Set.image_eq_range _ _).symm
      rw [e₁, Submodule.span_image, (d b₀).u.full, Submodule.map_top, LinearMap.range_eq_top]
      exact (T b₀).symm.surjective) fun j k => by
    obtain ⟨C, hC, hCo, hC₀⟩ := eventually_nhds_iff.1 ((hζ j).eventually_analyticAt.and
      ((hζ k).eventually_analyticAt.and ((hζe j).and ((hζe k).and (hB'.mem_nhds hb')))))
    simp only [hH]
    refine GlobalTheory.T.riemannForm_im_eventually_const_of_continuous_lattice X P m C y b₀ d ε T (ζ j) (ζ k) hCo hC₀
      (RelExp.isHolTo_of_holAt (hCo.prod isOpen_univ) fun q hq => (he q.1 (hC _ hq.1).2.2.2.2).1 q.2)
      (fun b hb => hT b (hC b hb).2.2.2.2)
      (fun b hb => (hC b hb).1.continuousAt.continuousWithinAt)
      (fun b hb => (hC b hb).2.1.continuousAt.continuousWithinAt) fun b hb => ?_
    exact ⟨(hker b (hC b hb).2.2.2.2 _).1 (hC b hb).2.2.1, (hker b (hC b hb).2.2.2.2 _).1 (hC b hb).2.2.2.1⟩
  have hdet : IsUnit (H b₀).det := by
    refine (posDef_chg ?_ (d b₀).posDef).det_pos.ne'.isUnit
    exact (LinearMap.isUnit_toMatrix'_iff).2 ((Module.End.isUnit_iff _).2 (T b₀).bijective)
  have hκ (f : Γ(P.A.left, W)) (a : Fin P.g) : ContDiffAt ℝ ∞
      (fun b => fderiv ℂ (fun z => valAt' (ε (b, z)) W f) 0 (Pi.single a 1)) b₀ := by
    have h₀ : ⊤ ≤ ε (b₀, 0) ⁻¹ᵁ W := by
      rwa [← one_left, ← (hker b₀ hb' 0).2 (by simp)] at hW
    have h₁ : AnalyticAt ℂ (fun q => valAt' (ε q) W f) (b₀, 0) :=
      SCV.analyticAt_of_differentiableOn (hol W f).2 ((hol W f).1.mem_nhds ⟨⟨hb', trivial⟩, h₀⟩)
    exact ((ContDiffAt.fderiv (f := fun b z => valAt' (ε (b, z)) W f) (g := fun _ => 0) (n := ω) (m := ∞)
      h₁.contDiffAt contDiffAt_const le_top).clm_apply contDiffAt_const).restrict_scalars ℝ
  have hD := (hsm.inv hdet).transpose
  refine ContDiffAt.congr_of_eventuallyEq (f := fun b => form (dualGram (H b))
    (fun a => fderiv ℂ (fun z => valAt' (ε (b, z)) W f) 0 (Pi.single a 1))
    (fun a => fderiv ℂ (fun z => valAt' (ε (b, z)) W f') 0 (Pi.single a 1))) ?_ ?_
  · simp only [form_eq_sum]
    exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun c _ => ((hκ f a).mul (hD a c)).mul
      (Complex.conjCLE.contDiff.contDiffAt.comp b₀ (hκ f' c))
  · filter_upwards [hB'.mem_nhds hb'] with b hb
    have e₁ (f : Γ(P.A.left, W)) : (fun z => valAt' (ε (b, z)) W f) = (d b).fn W f ∘ T b :=
      funext fun z => congrArg (valAt' · W f) (hT b hb z)
    rw [e₁, e₁]
    exact form_dualGram_chg (T b) _ _ _

theorem form_dualGram_smul {n : ℕ} {t : ℂ} (ht : t ≠ 0) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (v w : Fin n → ℂ) : form (dualGram (t • H)) v w = t⁻¹ * form (dualGram H) v w := by
  have e : (t • H)⁻¹ = t⁻¹ • H⁻¹ := inv_eq_right_inv (by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ ht, mul_nonsing_inv _ hH.det_pos.ne'.isUnit, one_smul])
  rw [dualGram, dualGram, e, transpose_smul, form_smul]

theorem isCInf_of_isDualRiemann : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    SmoothOfRelativeDimension D p → ∀ (P : PPAS X) (t : ℝ), 0 < t →
      ∀ h : VMetric p (LieVB.omega P.A) P.g, P.IsDualRiemann t h → h.IsCInf := by
  intro k _ X p D hp P t ht h H σ c y hy i j
  obtain ⟨U, W, hx, hle, ch⟩ := Conormal.exists_isChart (LieVB.sec_hom (MonObj.one (X := P.A))) (mem_ptsIn.1 hy)
  have hyU : y ∈ ptsIn p σ U := mem_ptsIn.2 hx
  obtain ⟨f, hf⟩ := ch.d_surjective (LieVB.sec_hom (MonObj.one (X := P.A)))
    (Twist.resM (LieVB.omega P.A) hle (c.e i))
  obtain ⟨f', hf'⟩ := ch.d_surjective (LieVB.sec_hom (MonObj.one (X := P.A)))
    (Twist.resM (LieVB.omega P.A) hle (c.e j))
  obtain ⟨C, hC⟩ := AlgChart.exists_mem_source (D := D) y
  have d (z : CxPts p σ) : P.RiemannData z.1 := (H σ z).1.some
  have ht' : ContDiff ℝ ∞ (WithLp.toLp 2 : (Fin D → ℂ) → ReciprocityTheory.L2DbarEstimates.V D) := PiLp.contDiff_toLp
  have ht'' : Differentiable ℂ (WithLp.toLp 2 : (Fin D → ℂ) → ReciprocityTheory.L2DbarEstimates.V D) :=
    (PiLp.contDiff_toLp (n := 1)).differentiable one_ne_zero
  have hc (z) (hz : z ∈ C.e.source) : WithLp.toLp 2 (fun a => ev p σ C.U (C.x a) z) = C.e z := by
    ext a; exact (C.apply_eq z hz a).symm
  let s : (Fin D → ℂ) → CxPts p σ := fun v => C.e.symm (WithLp.toLp 2 v)
  have hB : IsOpen (WithLp.toLp 2 ⁻¹' C.e.target : Set (Fin D → ℂ)) := C.e.open_target.preimage ht'.continuous
  have hol : IsHolTo (WithLp.toLp 2 ⁻¹' C.e.target : Set (Fin D → ℂ)) fun v => (s v).1 := fun V g =>
    ⟨(ChartGlue.isOpen_over C.e (isOpen_ptsIn V)).preimage ht'.continuous,
      (C.holo V g).comp ht''.differentiableOn fun _ hv => hv⟩
  refine ⟨C.U, Fin D, inferInstance, C.x, fun v => (t : ℂ)⁻¹ *
      form (dualGram (d (s v)).H) ((d (s v)).cov W f) ((d (s v)).cov W f'),
    WithLp.toLp 2 ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' ptsIn p σ U), C.source_subset hC,
    (ChartGlue.isOpen_over C.e (isOpen_ptsIn U)).preimage ht'.continuous, ?_, fun v hv => ?_, ?_⟩
  · rw [Set.mem_preimage, hc y hC]
    exact ChartGlue.mem_over C.e hC hyU
  · refine (contDiffAt_const.mul (contDiffAt_dualForm P (fun v => d (s v)) W f f' hB hv.1 hol ?_)).contDiffWithinAt
    exact le_trans hv.2 ((s v).1.preimage_mono ch.le)
  · filter_upwards [C.e.open_source.mem_nhds hC, (isOpen_ptsIn U).mem_nhds hyU] with z hz hzU
    have e : s (fun a => ev p σ C.U (C.x a) z) = z := by
      simp only [s, hc z hz, C.e.left_inv hz]
    rw [e, ← form_dualGram_smul (by exact_mod_cast ht.ne') (d z).posDef, ← (H σ z).2 (d z) U W ch.le f f' hzU,
      ← Met.form_frame _ c (ptsIn_mono hle hzU), ← Met.form_resM _ _ _ hle hzU, ← hf, ← hf']
    rfl

end GlobalTheory.HodgeSmooth
