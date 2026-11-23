import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem onePiece {Y : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (m : Measure Y) (e : OpenPartialHomeomorph Y (Fin D → ℂ)) (r : (Fin D → ℂ) → ℝ)
    (hr : ContinuousOn r e.target)
    (hm : m.restrict e.source = ((volume.restrict e.target).withDensity fun v =>
      ENNReal.ofReal (r v)).map e.symm)
    (S : Set Y) (hS : MeasurableSet S) (hSs : S ⊆ e.source) (K : Y → ℝ)
    (hK : IntegrableOn K S m) :
    Integrable ((e '' S).indicator fun v => K (e.symm v) * max (r v) 0) ∧
      ∫ y in S, K y ∂m = ∫ v, (e '' S).indicator (fun v => K (e.symm v) * max (r v) 0) v := by
  classical
  set ν0 : Measure (Fin D → ℂ) := volume.restrict e.target with hν0
  set d : (Fin D → ℂ) → ENNReal := fun v => ENNReal.ofReal (r v) with hd
  have htm : MeasurableSet e.target := e.open_target.measurableSet
  have hsm : MeasurableSet e.source := e.open_source.measurableSet
  have hdm : AEMeasurable d ν0 :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hr.aemeasurable htm)
  have hdlt : ∀ᵐ v ∂ν0, d v < ⊤ := Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top
  have hsy0 : AEMeasurable e.symm ν0 := e.continuousOn_symm.aemeasurable htm
  have hsy : AEMeasurable e.symm (ν0.withDensity d) :=
    hsy0.mono_ac (withDensity_absolutelyContinuous _ _)
  set K' : Y → ℝ := S.indicator K with hK'
  have hK1 : Integrable K' m := (integrable_indicator_iff hS).2 hK
  have hK2 : Integrable K' ((ν0.withDensity d).map e.symm) := by
    rw [← hm]; exact hK1.restrict
  have hK3 : Integrable (K' ∘ e.symm) (ν0.withDensity d) :=
    (integrable_map_measure hK2.aestronglyMeasurable hsy).1 hK2
  have hK4 : Integrable (fun v => (d v).toReal • (K' ∘ e.symm) v) ν0 :=
    (integrable_withDensity_iff_integrable_smul₀' hdm hdlt).1 hK3
  have hfun : (e '' S).indicator (fun v => K (e.symm v) * max (r v) 0) =
      e.target.indicator (fun v => (d v).toReal • (K' ∘ e.symm) v) := by
    funext v
    by_cases hv : v ∈ e '' S
    · obtain ⟨y, hy, rfl⟩ := hv
      have hyt : e y ∈ e.target := e.map_source (hSs hy)
      have hinv : e.symm (e y) = y := e.left_inv (hSs hy)
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), Set.indicator_of_mem hyt]
      simp [hinv, hK', hy, hd, ENNReal.toReal_ofReal', mul_comm]
    · rw [Set.indicator_of_notMem hv]
      by_cases hvt : v ∈ e.target
      · have hns : e.symm v ∉ S := fun h => hv ⟨_, h, e.right_inv hvt⟩
        rw [Set.indicator_of_mem hvt]; simp [hK', hns]
      · rw [Set.indicator_of_notMem hvt]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (integrable_indicator_iff htm).2 hK4
  · rw [hfun, integral_indicator htm]
    calc ∫ y in S, K y ∂m = ∫ y, K' y ∂m := (integral_indicator hS).symm
      _ = ∫ y in e.source, K' y ∂m := by
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
          intro y hy
          exact Set.indicator_of_notMem (fun h => hy (hSs h)) _
      _ = ∫ y, K' y ∂((ν0.withDensity d).map e.symm) := by rw [hm]
      _ = ∫ v, (K' ∘ e.symm) v ∂(ν0.withDensity d) :=
          integral_map hsy hK2.aestronglyMeasurable
      _ = ∫ v, (d v).toReal • (K' ∘ e.symm) v ∂ν0 :=
          integral_withDensity_eq_integral_toReal_smul₀ hdm hdlt _

theorem exists_partition {Y ι : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [Countable ι] (U : ι → Set Y) (hU : ∀ l, IsOpen (U l)) (G : Set Y) (hG : MeasurableSet G)
    (hGs : G ⊆ ⋃ l, U l) :
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ U l) ∧
      Pairwise (Function.onFun Disjoint S) ∧ ⋃ l, S l = G := by
  classical
  haveI := Encodable.ofCountable ι
  refine ⟨fun l => (G ∩ U l) \ ⋃ (k : ι) (_ : Encodable.encode k < Encodable.encode l), U k,
    fun l => ?_, fun l y hy => hy.1.2, ?_, ?_⟩
  · exact (hG.inter (hU l).measurableSet).diff
      (isOpen_iUnion fun k => isOpen_iUnion fun _ => hU k).measurableSet
  · have key : ∀ l k : ι, Encodable.encode k < Encodable.encode l →
        Disjoint ((G ∩ U k) \ ⋃ (j : ι) (_ : Encodable.encode j < Encodable.encode k), U j)
          ((G ∩ U l) \ ⋃ (j : ι) (_ : Encodable.encode j < Encodable.encode l), U j) := by
      intro l k hlt
      refine Set.disjoint_left.2 fun y hyk hyl => hyl.2 ?_
      exact Set.mem_iUnion₂.2 ⟨k, hlt, hyk.1.2⟩
    intro l k hne
    rcases lt_trichotomy (Encodable.encode l) (Encodable.encode k) with h | h | h
    · exact key k l h
    · exact absurd (Encodable.encode_injective h) hne
    · exact (key l k h).symm
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun l y hy => hy.1.1
    · intro y hy
      have hex : ∃ n, ∃ l : ι, Encodable.encode l = n ∧ y ∈ U l := by
        obtain ⟨l, hl⟩ := Set.mem_iUnion.1 (hGs hy)
        exact ⟨_, l, rfl, hl⟩
      obtain ⟨l, hl, hyl⟩ := Nat.find_spec hex
      refine Set.mem_iUnion.2 ⟨l, ⟨hy, hyl⟩, fun hmem => ?_⟩
      obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 hmem
      exact Nat.find_min hex (hl ▸ hk) ⟨k, rfl, hyk⟩

theorem abs_eq_max_add_max (a : ℝ) : |a| = max a 0 + max (-a) 0 := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring

theorem integral_pieces : ∀ {Y ι : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Countable ι]
    (μ : ℤˣ → Measure Y) (e : ι → OpenPartialHomeomorph Y (Fin D → ℂ)) (ρ : ι → (Fin D → ℂ) → ℝ),
    (∀ l, ContinuousOn (ρ l) (e l).target) →
    (∀ l (ε : ℤˣ), (μ ε).restrict (e l).source = ((volume.restrict (e l).target).withDensity fun v =>
      ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ l v)).map (e l).symm) →
    ∀ (G : Set Y), MeasurableSet G → G ⊆ ⋃ l, (e l).source → ∀ F : Y → ℝ, (∀ ε, IntegrableOn F G (μ ε)) →
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ (e l).source) ∧ Pairwise (Function.onFun Disjoint S) ∧
      ⋃ l, S l = G ∧ ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) =
        ∫ v, ∑' l, ((e l) '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) v := by
  intro Y ι D _ _ _ _ μ e ρ hρ hμ G hG hGs F hF
  obtain ⟨S, hSm, hSs, hSd, hSu⟩ := exists_partition (fun l => (e l).source)
    (fun l => (e l).open_source) G hG hGs
  refine ⟨S, hSm, hSs, hSd, hSu, ?_⟩
  have hSG : ∀ l, S l ⊆ G := fun l => hSu ▸ Set.subset_iUnion S l
  have piece : ∀ (l : ι) (ε : ℤˣ) (K : Y → ℝ), IntegrableOn K (S l) (μ ε) →
      Integrable ((e l '' S l).indicator fun v => K ((e l).symm v) * max (((ε : ℤ) : ℝ) * ρ l v) 0) ∧
      ∫ y in S l, K y ∂μ ε =
        ∫ v, (e l '' S l).indicator (fun v => K ((e l).symm v) * max (((ε : ℤ) : ℝ) * ρ l v) 0) v :=
    fun l ε K hK => onePiece (μ ε) (e l) (fun v => ((ε : ℤ) : ℝ) * ρ l v)
      (continuousOn_const.mul (hρ l)) (hμ l ε) (S l) (hSm l) (hSs l) K hK
  set Φ : ι → (Fin D → ℂ) → ℝ := fun l =>
    (e l '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) with hΦ
  have hΦsub : ∀ l, Φ l =
      (e l '' S l).indicator (fun v => F ((e l).symm v) * max ((((1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) -
      (e l '' S l).indicator (fun v => F ((e l).symm v) * max ((((-1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) := by
    intro l
    funext v
    by_cases hv : v ∈ e l '' S l
    · simp only [hΦ, Pi.sub_apply, Set.indicator_of_mem hv]
      have h := max_zero_sub_max_neg_zero_eq_self (ρ l v)
      simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
      rw [← mul_sub, h]
    · simp [hΦ, Set.indicator_of_notMem hv]
  have hΦnorm : ∀ l v, ‖Φ l v‖ =
      (e l '' S l).indicator (fun v => ‖F ((e l).symm v)‖ * max ((((1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) v +
      (e l '' S l).indicator (fun v => ‖F ((e l).symm v)‖ * max ((((-1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) v := by
    intro l v
    by_cases hv : v ∈ e l '' S l
    · simp only [hΦ, Set.indicator_of_mem hv]
      simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
      rw [norm_mul, ← mul_add, Real.norm_eq_abs (ρ l v), abs_eq_max_add_max]
    · simp [hΦ, Set.indicator_of_notMem hv]
  have hFS : ∀ l ε, IntegrableOn F (S l) (μ ε) := fun l ε => (hF ε).mono_set (hSG l)
  have hFnS : ∀ l ε, IntegrableOn (fun y => ‖F y‖) (S l) (μ ε) := fun l ε => (hFS l ε).norm
  have hΦint : ∀ l, Integrable (Φ l) := by
    intro l
    rw [hΦsub l]
    exact (piece l 1 F (hFS l 1)).1.sub (piece l (-1) F (hFS l (-1))).1
  have hΦval : ∀ l, ∫ v, Φ l v = ∫ y in S l, F y ∂μ 1 - ∫ y in S l, F y ∂μ (-1) := by
    intro l
    rw [hΦsub l, (piece l 1 F (hFS l 1)).2, (piece l (-1) F (hFS l (-1))).2]
    exact integral_sub (piece l 1 F (hFS l 1)).1 (piece l (-1) F (hFS l (-1))).1
  have hΦnval : ∀ l, ∫ v, ‖Φ l v‖ =
      ∫ y in S l, ‖F y‖ ∂μ 1 + ∫ y in S l, ‖F y‖ ∂μ (-1) := by
    intro l
    simp only [hΦnorm l]
    rw [(piece l 1 _ (hFnS l 1)).2, (piece l (-1) _ (hFnS l (-1))).2]
    exact integral_add (piece l 1 _ (hFnS l 1)).1 (piece l (-1) _ (hFnS l (-1))).1
  have hU : ∀ ε, IntegrableOn F (⋃ l, S l) (μ ε) := fun ε => by rw [hSu]; exact hF ε
  have hsumN : ∀ ε, Summable fun l => ∫ y in S l, ‖F y‖ ∂μ ε := fun ε =>
    (hasSum_integral_iUnion hSm hSd (hU ε).norm).summable
  have h1 : HasSum (fun l => ∫ v, Φ l v) (∫ v, ∑' l, Φ l v) :=
    hasSum_integral_of_summable_integral_norm hΦint
      (by simp only [hΦnval]; exact (hsumN 1).add (hsumN (-1)))
  have h2 : HasSum (fun l => ∫ y in S l, F y ∂μ 1 - ∫ y in S l, F y ∂μ (-1))
      (∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1)) := by
    have a := hasSum_integral_iUnion hSm hSd (hU 1)
    have b := hasSum_integral_iUnion hSm hSd (hU (-1))
    rw [hSu] at a b
    exact a.sub b
  simp only [hΦval] at h1
  exact h2.unique h1

end GlobalTheory.CompanionTheory.MixZ.ArchEq
