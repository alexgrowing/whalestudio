import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnectedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFreeStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat Metric

theorem isHolTo_comp {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {A : Set V'} {y : V' → (Sp ℂ ⟶ X)} (hy : IsHolTo A y) {B' : Set V} (hB' : IsOpen B')
    {φ : V → V'} (hφ : DifferentiableOn ℂ φ B') (hmap : Set.MapsTo φ B' A) : IsHolTo B' (fun b => y (φ b)) := by
  intro U f
  obtain ⟨h₁, h₂⟩ := hy U f
  have hset : {b ∈ B' | ⊤ ≤ y (φ b) ⁻¹ᵁ U} = B' ∩ φ ⁻¹' {v ∈ A | ⊤ ≤ y v ⁻¹ᵁ U} := by
    ext b
    constructor
    · rintro ⟨hb, hU⟩
      exact ⟨hb, hmap hb, hU⟩
    · rintro ⟨hb, _, hU⟩
      exact ⟨hb, hU⟩
  rw [hset]
  refine ⟨hφ.continuousOn.isOpen_inter_preimage hB' h₁, ?_⟩
  exact h₂.comp (hφ.mono Set.inter_subset_left) (fun b hb => hb.2)

section Exp

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem ex_zero_eq_one (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) : e.ex b 0 = 1 := by
  have h := e.add b hb 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem ex_pow_eq (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (z : Fin g → ℂ) (N : ℕ) :
    e.ex b z ^ N = e.ex b ((N : ℂ) • z) := by
  induction N with
  | zero => simp [ex_zero_eq_one e hb]
  | succ k ih =>
    rw [pow_succ, ih, ← e.add b hb]
    congr 1
    push_cast
    rw [add_smul, one_smul]

theorem ex_inv_smul_pow (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) {s : Fin g → ℂ} (hs : s ∈ e.per b)
    {N : ℕ} (hN : 0 < N) : e.ex b ((N : ℂ)⁻¹ • s) ^ N = 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [ex_pow_eq e hb, smul_smul, mul_inv_cancel₀ hN', one_smul]
  exact hs

theorem hol_ex_comp (e : FamExp G M B ψ) {B' : Set (Fin n → ℂ)} (hB' : IsOpen B') (hsub : B' ⊆ B)
    {s : (Fin n → ℂ) → (Fin g → ℂ)} (hs : DifferentiableOn ℂ s B') :
    IsHolTo B' (fun b => (e.ex b (s b)).left) :=
  isHolTo_comp e.hol hB' (φ := fun b => (b, s b)) (differentiableOn_id.prodMk hs) (fun _ hb => ⟨hsub hb, trivial⟩)

theorem period_of_tendsto (e : FamExp G M B ψ) (hsep : IsSeparated G.hom) (hhol : IsHolPts B ψ)
    {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B) {bs : ℕ → Fin n → ℂ} {q : ℕ → Fin g → ℂ} {p : Fin g → ℂ}
    (hb : Tendsto bs atTop (𝓝 b₀)) (hq : Tendsto q atTop (𝓝 p))
    (hper : ∀ m, q m ∈ e.per (bs m)) : p ∈ e.per b₀ := by
  by_cases hfreq : ∃ᶠ m in atTop, bs m = b₀
  · obtain ⟨Γ₀, hΓ, hdisc, -, -⟩ := GlobalTheory.T.period_lattice_discrete_free R G g n M B ψ e b₀ hb₀
    have hcl : IsClosed (Γ₀ : Set (Fin g → ℂ)) := by
      haveI := hdisc
      exact AddSubgroup.isClosed_of_discrete (H := Γ₀.toAddSubgroup)
    rw [hΓ] at hcl
    refine hcl.mem_of_frequently_of_tendsto (hfreq.mono fun m hm => ?_) hq
    rw [← hm]
    exact hper m
  · have hne : ∀ᶠ m in atTop, bs m ≠ b₀ := not_frequently.mp hfreq
    classical
    let s : (Fin n → ℂ) → (Fin g → ℂ) := fun b =>
      if h : b ≠ b₀ ∧ ∃ m, bs m = b then q (Nat.find h.2) else p
    have hs₀ : s b₀ = p := dif_neg (fun h => h.1 rfl)
    have hcont : ContinuousAt s b₀ := by
      rw [ContinuousAt, hs₀]
      intro U hU
      obtain ⟨K, hK⟩ := eventually_atTop.mp (hq hU)
      have hV : ∀ᶠ b in 𝓝 b₀, ∀ k ∈ Finset.range K, bs k ≠ b₀ → b ≠ bs k := by
        rw [Filter.eventually_all_finset]
        intro k _
        by_cases hk : bs k = b₀
        · exact Eventually.of_forall fun _ h => absurd hk h
        · filter_upwards [eventually_ne_nhds (Ne.symm hk)] with b hb' _ using hb'
      refine Filter.mem_map.mpr ?_
      filter_upwards [hV] with b hbV
      show s b ∈ U
      by_cases h : b ≠ b₀ ∧ ∃ m, bs m = b
      · have hsb : s b = q (Nat.find h.2) := dif_pos h
        rw [hsb]
        have hspec : bs (Nat.find h.2) = b := Nat.find_spec h.2
        refine hK _ ?_
        by_contra hlt
        refine hbV _ (Finset.mem_range.mpr (not_le.mp hlt)) ?_ hspec.symm
        rw [hspec]
        exact h.1
      · have hsb : s b = p := dif_neg h
        rw [hsb]
        exact mem_of_mem_nhds hU
    have hfr : ∃ᶠ b in 𝓝 b₀, b ∈ B ∧ s b ∈ e.per b := by
      refine hb.frequently (Eventually.frequently ?_)
      filter_upwards [hne, hb (hhol.1.mem_nhds hb₀)] with m hm hmB
      refine ⟨hmB, ?_⟩
      have h : bs m ≠ b₀ ∧ ∃ k, bs k = bs m := ⟨hm, m, rfl⟩
      obtain ⟨k, hk, hsk⟩ : ∃ k, bs k = bs m ∧ s (bs m) = q k := ⟨Nat.find h.2, Nat.find_spec h.2, dif_pos h⟩
      rw [hsk, ← hk]
      exact hper k
    have := GlobalTheory.T.period_set_closed R G g n M B ψ e hsep hhol b₀ hb₀ s hcont hfr
    rwa [hs₀] at this

end Exp

section Core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem limit_core {R : Type} [CommRing R] (t : SAB H (Sp R)) {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)}
    {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : FamExp t.G M B ψ) (hhol : IsHolPts B ψ)
    {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B) {bs : ℕ → Fin n → ℂ} (hbs : Tendsto bs atTop (𝓝 b₀))
    {Λ : Type} [AddCommGroup Λ] (Ef : Λ → Λ → ℤ) (P : ℕ → Λ →+ (Fin g → ℂ))
    (hlink : ∀ m, (∀ p, p ∈ e.per (bs m) ↔ ∃ x, P m x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N →
      GlobalTheory.UU.CubWeil t.cub N (e.ex (bs m) ((N : ℂ)⁻¹ • P m x)) (e.ex (bs m) ((N : ℂ)⁻¹ • P m x')) (unitOn ζ) →
      (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Ef x x' : ℤ) : ℂ) / N))
    (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ))
    (hper : ∀ x : W, Tendsto (fun m => P m x) atTop (𝓝 (per x)))
    (h4 : ∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => P m (x m)) atTop (𝓝 p) →
      ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) :
    (∀ x : W, per x ∈ e.per b₀) ∧ (∀ p ∈ e.per b₀, ∃ x : W, per x = p) ∧
      ∀ (N : ℕ) (ζ : ℂˣ) (x x' : W), 0 < N →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Ef x x' : ℤ) : ℂ) / N) →
        GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • per x)) (e.ex b₀ ((N : ℂ)⁻¹ • per x')) (unitOn ζ) := by
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hP : ∀ m x, P m x ∈ e.per (bs m) := fun m x => ((hlink m).1 _).2 ⟨x, rfl⟩
  have spread : ∀ p ∈ e.per b₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)) (y : ℕ → Λ), 0 < ε ∧ ball b₀ ε ⊆ B ∧
      DifferentiableOn ℂ s (ball b₀ ε) ∧ s b₀ = p ∧ (∀ b ∈ ball b₀ ε, s b ∈ e.per b) ∧
      (∀ m, bs m ∈ ball b₀ ε → P m (y m) = s (bs m)) ∧ Tendsto (fun m => P m (y m)) atTop (𝓝 p) := by
    intro p hp
    obtain ⟨ε, s, hε, hsub, hsd, hs₀, hsper⟩ := GlobalTheory.T.period_holomorphic_continuation R t.G g n M B ψ e hhol.1 b₀ hb₀ p hp
    have hy : ∀ m, ∃ y : Λ, bs m ∈ ball b₀ ε → P m y = s (bs m) := by
      intro m
      by_cases hm : bs m ∈ ball b₀ ε
      · obtain ⟨y, hy⟩ := ((hlink m).1 _).1 (hsper _ hm)
        exact ⟨y, fun _ => hy⟩
      · exact ⟨0, fun h => absurd h hm⟩
    choose y hy using hy
    refine ⟨ε, s, y, hε, hsub, hsd, hs₀, hsper, hy, ?_⟩
    have hc : ContinuousAt s b₀ := hsd.continuousOn.continuousAt (ball_mem_nhds b₀ hε)
    have ht : Tendsto (fun m => s (bs m)) atTop (𝓝 p) := by
      have := hc.tendsto.comp hbs
      rwa [hs₀] at this
    refine ht.congr' ?_
    filter_upwards [hbs (ball_mem_nhds b₀ hε)] with m hm
    exact (hy m hm).symm
  have hinj : ∀ x : W, per x = 0 → x = 0 := by
    intro x hx
    classical
    let y : ℕ → Λ := fun m => if Even m then (x : Λ) else 0
    have hy : Tendsto (fun m => P m (y m)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun m => P m x) atTop (𝓝 0) := by
        have := hper x
        rwa [hx] at this
      refine squeeze_zero_norm (fun m => ?_) (tendsto_zero_iff_norm_tendsto_zero.mp h0)
      by_cases hm : Even m
      · simp [y, hm]
      · simp [y, hm]
    obtain ⟨x₀, -, hev⟩ := h4 y 0 hy
    obtain ⟨K, hK⟩ := eventually_atTop.mp hev
    have h1 : (x : Λ) = x₀ := by
      have := hK (2 * K) (by omega)
      simpa [y] using this
    have h2 : (0 : Λ) = x₀ := by
      have := hK (2 * K + 1) (by omega)
      have hodd : ¬ Even (2 * K + 1) := by
        rw [Nat.not_even_iff_odd]
        exact ⟨K, rfl⟩
      simpa [y, hodd] using this
    exact Subtype.ext (h1.trans h2.symm)
  have hval : ∀ (x : W) (y : ℕ → Λ), Tendsto (fun m => P m (y m)) atTop (𝓝 (per x)) →
      ∀ᶠ m in atTop, y m = x := by
    intro x y hy
    obtain ⟨x₀, hp, hev⟩ := h4 y (per x) hy
    have h0 : x - x₀ = 0 := hinj _ (by rw [map_sub, hp, sub_self])
    have hxx : x = x₀ := sub_eq_zero.mp h0
    filter_upwards [hev] with m hm
    rw [hm, hxx]
  refine ⟨fun x => period_of_tendsto e hsep hhol hb₀ hbs (hper x) (fun m => hP m x), ?_, ?_⟩
  · intro p hp
    obtain ⟨ε, s, y, -, -, -, -, -, -, ht⟩ := spread p hp
    obtain ⟨x₀, h, -⟩ := h4 y p ht
    exact ⟨x₀, h.symm⟩
  · intro N ζ x x' hN hζ
    have hpx := period_of_tendsto e hsep hhol hb₀ hbs (hper x) (fun m => hP m x)
    have hpx' := period_of_tendsto e hsep hhol hb₀ hbs (hper x') (fun m => hP m x')
    obtain ⟨ε, s, y, hε, hsub, hsd, hs₀, hsper, hy, ht⟩ := spread _ hpx
    obtain ⟨ε', s', y', hε', hsub', hsd', hs₀', hsper', hy', ht'⟩ := spread _ hpx'
    have hδ : 0 < min ε ε' := lt_min hε hε'
    have hl : ball b₀ (min ε ε') ⊆ ball b₀ ε := ball_subset_ball (min_le_left _ _)
    have hr : ball b₀ (min ε ε') ⊆ ball b₀ ε' := ball_subset_ball (min_le_right _ _)
    let X : ∀ b, Over.mk (spMap (ψ b)) ⟶ t.G := fun b => e.ex b ((N : ℂ)⁻¹ • s b)
    let X' : ∀ b, Over.mk (spMap (ψ b)) ⟶ t.G := fun b => e.ex b ((N : ℂ)⁻¹ • s' b)
    have hX : IsHolTo (ball b₀ (min ε ε')) (fun b => (X b).left) :=
      hol_ex_comp e isOpen_ball (hl.trans hsub) (s := fun b => (N : ℂ)⁻¹ • s b) ((hsd.mono hl).const_smul ((N : ℂ)⁻¹))
    have hX' : IsHolTo (ball b₀ (min ε ε')) (fun b => (X' b).left) :=
      hol_ex_comp e isOpen_ball (hl.trans hsub) (s := fun b => (N : ℂ)⁻¹ • s' b) ((hsd'.mono hr).const_smul ((N : ℂ)⁻¹))
    have htors : ∀ b ∈ ball b₀ (min ε ε'), X b ^ N = 1 ∧ X' b ^ N = 1 ∧
        (X b).left ≫ t.G.hom = (X' b).left ≫ t.G.hom := fun b hb =>
      ⟨ex_inv_smul_pow e (hsub (hl hb)) (hsper b (hl hb)) hN,
        ex_inv_smul_pow e (hsub (hl hb)) (hsper' b (hr hb)) hN, (Over.w (X b)).trans (Over.w (X' b)).symm⟩
    have hb₀' : b₀ ∈ ball b₀ (min ε ε') := mem_ball_self hδ
    obtain ⟨u, hu, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t.cub (htors b₀ hb₀').1 (htors b₀ hb₀').2.1
    obtain ⟨ζ₁, rfl⟩ : ∃ z : ℂˣ, unitOn z = u :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.toMonoidHom u, Units.ext (by simp [unitOn])⟩
    have hconst := GlobalTheory.T.torsion_section_eq_of_connected (Sp R) t.G t.PP t.cub n N (ball b₀ (min ε ε')) (fun b => spMap (ψ b)) X X' ζ₁ b₀ hN
      isOpen_ball (convex_ball _ _).isPreconnected hb₀' hX hX' htors hu
    have hbm : ∀ᶠ m in atTop, bs m ∈ ball b₀ (min ε ε') := hbs (ball_mem_nhds b₀ hδ)
    obtain ⟨m, hm, hym, hym'⟩ := (hbm.and ((hval x y ht).and (hval x' y' ht'))).exists
    have hm1 := hconst (bs m) hm
    have e1 : s (bs m) = P m x := by rw [← hy m (hl hm), hym]
    have e2 : s' (bs m) = P m x' := by rw [← hy' m (hr hm), hym']
    have hc : GlobalTheory.UU.CubWeil t.cub N (e.ex (bs m) ((N : ℂ)⁻¹ • P m x)) (e.ex (bs m) ((N : ℂ)⁻¹ • P m x'))
        (unitOn ζ₁) := by
      rw [← e1, ← e2]
      exact hm1
    have hζ₁ : ζ₁ = ζ := Units.ext (((hlink m).2 N ζ₁ x x' hN hc).trans hζ.symm)
    rw [← hζ₁, ← hs₀, ← hs₀']
    exact hu

end Core

theorem limit_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n a : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (ρ : ℝ) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), 0 < ρ → ρ ≤ 1 → Flat.IsHolPts (Metric.ball 0 ρ) ψ → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x)) (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) → Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) → (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) → (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) → (∀ x : W, per x ∈ e.per ((ρ : ℂ) • z)) ∧ (∀ p ∈ e.per ((ρ : ℂ) • z), ∃ x : W, per x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : W), 0 < N → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N) → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x)) (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x')) (unitOn ζ) := by
  intro E _ _ _ H R _ t g n a M ψ ρ e Λ _ L hρ _ hhol hlink z hz ws W per hws hlim hper h4
  have hb₀ : (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    rw [mem_ball_zero_iff, norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    have : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    nlinarith
  exact limit_core t e hhol hb₀ (hlim.const_smul (ρ : ℂ)) (fun x y => L.E x y) (fun m => L.P (ws m))
    (fun m => hlink _ (hws m)) W per hper h4

end GlobalTheory.CompanionTheory.Ar.QuotLoc
