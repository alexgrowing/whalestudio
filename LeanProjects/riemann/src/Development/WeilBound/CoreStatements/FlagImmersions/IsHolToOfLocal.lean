import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.Pieces
import Development.WeilBound.CoreStatements.VolumeEquality.HolNull
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsForm
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement

noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

namespace Pts

theorem isHolTo_of_local {X : Scheme.{0}} {n : ℕ} {T : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)}
    (h : ∀ t ∈ T, ∃ B, B ⊆ T ∧ t ∈ B ∧ IsHolTo B y) : IsHolTo T y := by
  intro U f
  have key : ∀ t ∈ {b ∈ T | ⊤ ≤ y b ⁻¹ᵁ U}, {b ∈ T | ⊤ ≤ y b ⁻¹ᵁ U} ∈ 𝓝 t ∧
      DifferentiableAt ℂ (fun b => valAt' (y b) U f) t := by
    rintro t ⟨ht, hU⟩
    obtain ⟨B, hBT, htB, hB⟩ := h t ht
    have hn := (hB U f).1.mem_nhds (show t ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} from ⟨htB, hU⟩)
    exact ⟨mem_of_superset hn fun b hb => ⟨hBT hb.1, hb.2⟩, (hB U f).2.differentiableAt hn⟩
  exact ⟨isOpen_iff_mem_nhds.2 fun t ht => (key t ht).1, fun t ht => (key t ht).2.differentiableWithinAt⟩

theorem not_mem_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (w : (Σ k, ι k) → ℂ) :
    w ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  simpa using h.2 1 trivial

theorem sat_iff {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {w w' : (Σ k, ι k) → ℂ} :
    w ∈ torusSat {w'} ↔ SameOrbit w w' :=
  ⟨fun ⟨_, e, a, ha, h⟩ => ⟨a, ha, by rw [h, Set.mem_singleton_iff.1 e]; rfl⟩, fun ⟨a, ha, h⟩ => ⟨w', rfl, a, ha, h⟩⟩

theorem analyticAt_comp {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : FinHolAtlas e X}
    {B : FinHolAtlas e Y} {ψ : X → Y} (hψ : HoloMap A B ψ) {U : Set Y} {f : Y → ℂ} (hf : B.HoloOn U f)
    (k : Fin A.n) {t : Fin e → ℂ} (ht : t ∈ (A.chart k).target) (htU : ψ ((A.chart k).symm t) ∈ U) :
    AnalyticAt ℂ (fun s => f (ψ ((A.chart k).symm s))) t := by
  obtain ⟨j, hj⟩ := B.cover (ψ ((A.chart k).symm t))
  have h1 : AnalyticAt ℂ (B.chart j ∘ ψ ∘ (A.chart k).symm) t := hψ.2 k j t ⟨ht, hj⟩
  have h2 : AnalyticAt ℂ (f ∘ (B.chart j).symm) ((B.chart j ∘ ψ ∘ (A.chart k).symm) t) :=
    hf j _ ⟨(B.chart j).map_source hj, by
      show (B.chart j).symm (B.chart j (ψ ((A.chart k).symm t))) ∈ U
      rwa [(B.chart j).left_inv hj]⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (fun s => ψ ((A.chart k).symm s)) t :=
    hψ.1.continuousAt.comp ((A.chart k).continuousAt_symm ht)
  filter_upwards [hc.eventually ((B.chart j).open_source.mem_nhds hj)] with s hs
  show f ((B.chart j).symm (B.chart j (ψ ((A.chart k).symm s)))) = _
  rw [(B.chart j).left_inv hs]

end Pts

open Pts

theorem ptsFam : PtsFam := by
  intro E _ _ _ H D l Xo c Y S RM Sys Fx Or ψ hJ hψ hπψ hψπ
  have hnJ : ∀ w, w ∉ mcPts Or.Re.J := fun w => by rw [hJ]; exact not_mem_top w
  choose z hz using fun x : Sys.X =>
    SheetDecomposition.exists_pt Or.𝔐 (Or.Re.R.mem (ψ x) (ψ x) (Or.Re.R.mem_U (ψ x)))
  have hol : ∀ k, IsHolTo (Sys.A.chart k).target fun t => z ((Sys.A.chart k).symm t) := fun k => by
    refine isHolTo_of_local fun t₀ ht₀ => ?_
    let w₀ := ψ ((Sys.A.chart k).symm t₀)
    have hB : IsOpen ((Sys.A.chart k).target ∩ (Sys.A.chart k).symm ⁻¹' (ψ ⁻¹' Or.Re.R.U w₀)) :=
      (Sys.A.chart k).symm.isOpen_inter_preimage ((Or.Re.R.isOpen_U w₀).preimage hψ.1)
    refine ⟨(Sys.A.chart k).target ∩ (Sys.A.chart k).symm ⁻¹' (ψ ⁻¹' Or.Re.R.U w₀), Set.inter_subset_left,
      ⟨ht₀, Or.Re.R.mem_U w₀⟩, ?_⟩
    refine GlobalTheory.T.holomorphic_coords_of_generic_point _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie Or.𝔐.all _ _
      (fun t => Or.Re.R.lift w₀ (ψ ((Sys.A.chart k).symm t))) _ hB ?_ ?_
    · refine differentiableOn_pi.2 fun p t ht => ?_
      exact (analyticAt_comp hψ (Or.Re.R.holo w₀ p) k ht.1 ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      exact SheetDecomposition.coords_of_sat Or.𝔐 (hz _) (sat_iff.2 (Or.Re.R.compat _ _ _ ⟨ht.2, Or.Re.R.mem_U _⟩))
  refine ⟨z, fun x x' e => ?_, hz, hol, fun U hU => ?_⟩
  · have h := sat_iff.1 (SheetDecomposition.sat_of_coords Or.𝔐 (hz x') (e ▸ hz x))
    rw [← hπψ x, Or.Re.R.inj _ _ (hnJ _) h, hπψ]
  · obtain ⟨g, hg, hgU⟩ := SheetDecomposition.ChartForm.exists_form Or.𝔐.tie U hU
    obtain ⟨w, hw, hwg⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts (J := Ideal.span {g}) RM.arith
      (fun h => hg (h (Ideal.subset_span rfl)))
    have hg0 : MvPolynomial.aeval w g ≠ 0 := fun h0 => hwg ⟨hw.1, fun f hf => by
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hf
      have : MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
        rw [MvPolynomial.eval_map]
        exact h0
      rw [map_mul, map_mul, this, mul_zero]⟩
    obtain ⟨w₁, hw₁⟩ := Or.Re.R.surj w hw (hnJ w)
    have hsym : SameOrbit w (Or.Re.R.lift w₁ w₁) := by
      obtain ⟨a, ha, h⟩ := hw₁
      refine ⟨fun k => (a k)⁻¹, fun k => inv_ne_zero (ha k), funext fun p => ?_⟩
      rw [h]
      simp only [inv_mul_cancel_left₀ (ha _)]
    have hc : CoordsAt Or.𝔐.ξ RM.y (z (Or.Re.π w₁)) w :=
      SheetDecomposition.coords_of_sat Or.𝔐 (hz _) (sat_iff.2 (by rw [hψπ]; exact hsym))
    have hx₀ : centre (z (Or.Re.π w₁)) ∈ U := hgU _ _ (Or.𝔐.all _) hc hg0
    obtain ⟨k, hk⟩ := Sys.A.cover (Or.Re.π w₁)
    have hopen := (Sys.A.chart k).isOpen_inter_preimage (hol k U 0).1
    have hd := (GlobalTheory.T.section_boundary_closed_and_codense _ _ Sys.A Sys.L Sys.s Sys.nb Sys.m Sys.W Sys.sec Sys.snc).2
    obtain ⟨x, ⟨hxs, -, hxU⟩, hxo⟩ := hd.inter_open_nonempty _ hopen ⟨Or.Re.π w₁, hk, (Sys.A.chart k).map_source hk, by
      show ⊤ ≤ z ((Sys.A.chart k).symm (Sys.A.chart k _)) ⁻¹ᵁ U
      rw [(Sys.A.chart k).left_inv hk]
      exact (SheetDecomposition.top_le_iff_pt _ _ _).2 hx₀⟩
    refine ⟨x, hxo, ?_⟩
    have h2 : ⊤ ≤ z ((Sys.A.chart k).symm (Sys.A.chart k x)) ⁻¹ᵁ U := hxU
    rw [(Sys.A.chart k).left_inv hxs] at h2
    exact (SheetDecomposition.top_le_iff_pt _ _ _).1 h2

end RootFieldNumerics
