import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
open GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernTop GlobalTheory.Points
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace GlobalTheory.ImmInj

theorem exists_holo_of_chart {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D' : ℕ}
    (i : X ⟶ Y) [IsClosedImmersion i] (w : i ≫ q = p) (σ : k →+* ℂ) (c0 : AlgChart q σ D') (y : CxPts p σ)
    (hy0 : PtsOver.map i w (spMap σ) y ∈ c0.e.source) {W : X.Opens} (f : Γ(X, W)) (hW : y ∈ ptsIn p σ W) :
    ∃ R : V D' → ℂ, DifferentiableAt ℂ R (c0.e (PtsOver.map i w (spMap σ) y)) ∧
      ∀ᶠ z in 𝓝 y, ev p σ W f z = R (c0.e (PtsOver.map i w (spMap σ) z)) := by
  have hU : IsAffineOpen (i ⁻¹ᵁ c0.U) := c0.affine.preimage i
  have hmU : PtsOver.map i w (spMap σ) y ∈ ptsIn q σ c0.U := c0.source_subset hy0
  have hyU : y ∈ ptsIn p σ (i ⁻¹ᵁ c0.U) := hmU
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := W) ⟨_, mem_ptsIn.1 hW⟩ (mem_ptsIn.1 hyU)
  have hB : y ∈ ptsIn p σ (X.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG X hhW f)
  obtain ⟨G, rfl⟩ := i.app_surjective c0.U c0.affine h
  obtain ⟨F, rfl⟩ := i.app_surjective c0.U c0.affine a
  have hd := fun a : Γ(Y, c0.U) => c0.differentiableAt_ev a hy0 hmU
  have hne (z : CxPts p σ) (hz : z ∈ ptsIn p σ (X.basicOpen (i.app c0.U G))) :
      ev q σ c0.U G (PtsOver.map i w (spMap σ) z) ≠ 0 := by
    rw [← ev_app i w]
    exact (mem_ptsIn_basicOpen (ptsIn_mono (X.basicOpen_le _) hz) _).1 hz
  refine ⟨fun v => ev q σ c0.U F (c0.e.symm v) * (ev q σ c0.U G (c0.e.symm v) ^ n)⁻¹,
    (hd F).mul (((hd G).pow n).inv (pow_ne_zero n ?_)), ?_⟩
  · simpa only [Function.comp_apply, c0.e.left_inv hy0] using hne y hB
  filter_upwards [(isOpen_ptsIn _).mem_nhds hB,
    (c0.e.open_source.preimage (PtsOver.continuous_map i w (spMap σ))).mem_nhds hy0] with z hz hz0
  have ha' : resG X hhW f * resG X (X.basicOpen_le _) (i.app c0.U G) ^ n =
    resG X (X.basicOpen_le (i.app c0.U G)) (i.app c0.U F) := ha
  have e := congrArg (evHom hz) ha'
  rw [map_mul, map_pow, ← ev_eq, ← ev_eq, ← ev_eq, ev_res _ hz, ev_res _ hz, ev_res _ hz, ev_app i w,
    ev_app i w] at e
  rw [c0.e.left_inv hz0]
  exact (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero n (hne z hz))).2 e

theorem fderiv_injective : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D D' : ℕ) (i : X ⟶ Y), IsClosedImmersion i → ∀ (w : i ≫ q = p) (σ : k →+* ℂ) (c : AlgChart p σ D) (c0 : AlgChart q σ D') (y : CxPts p σ), y ∈ c.e.source → PtsOver.map i w (spMap σ) y ∈ c0.e.source → Function.Injective (fderiv ℂ (c0.e ∘ PtsOver.map i w (spMap σ) ∘ c.e.symm) (c.e y)) := by
  intro k _ X Y p q D D' i hi w σ c c0 y hy hy0
  choose R hR hRe using fun a => exists_holo_of_chart i w σ c0 y hy0 (c.x a) (c.source_subset hy)
  set m := PtsOver.map i w (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ i := fun _ => rfl
  set Φ : V D → V D' := c0.e ∘ m ∘ c.e.symm with hΦ
  have hU : IsOpen (c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)) :=
    GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (PtsOver.continuous_map i w (spMap σ)))
  have hF : DifferentiableAt ℂ Φ (c.e y) :=
    (AlgChart.holo_map hm c c0).differentiableAt (hU.mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hy hy0))
  have hFy : Φ (c.e y) = c0.e (m y) := by
    simp only [hΦ, Function.comp_apply, c.e.left_inv hy]
  let S : V D' → V D := fun v => WithLp.toLp 2 fun a => R a v
  have hS : DifferentiableAt ℂ S (Φ (c.e y)) := by
    rw [hFy]
    exact differentiableAt_euclidean.2 hR
  have ht : Tendsto c.e.symm (𝓝 (c.e y)) (𝓝 y) := by
    have := c.e.continuousAt_symm (c.e.map_source hy)
    rwa [ContinuousAt, c.e.left_inv hy] at this
  have e : S ∘ Φ =ᶠ[𝓝 (c.e y)] id := by
    filter_upwards [ht.eventually (eventually_all.2 hRe), c.e.open_target.mem_nhds (c.e.map_source hy)] with v hv hv'
    ext a
    have h₁ := c.apply_eq _ (c.e.map_target hv') a
    rw [c.e.right_inv hv', hv a] at h₁
    exact h₁.symm
  have h₂ := e.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp _ hS hF, fderiv_id] at h₂
  exact Function.LeftInverse.injective (g := fderiv ℂ S (Φ (c.e y))) fun v => congrArg (· v) h₂

end GlobalTheory.ImmInj
