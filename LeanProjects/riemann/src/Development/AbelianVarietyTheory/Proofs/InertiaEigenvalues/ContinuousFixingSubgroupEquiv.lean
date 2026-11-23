import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GalExtCContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCycCycChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open ReciprocityTheory.Gal Filter Topology

namespace GlobalTheory.Cyc.TwistLift

section Abstract

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]

theorem continuous_iff_coe {X : Type} [TopologicalSpace X] (f : X → ℤ_[l]) :
    Continuous f ↔ Continuous fun x => (f x : ℚ_[l]) :=
  PadicInt.isOpenEmbedding_coe.isInducing.continuous_iff

theorem contAction_charRep {R : Type} [CommRing R] [TopologicalSpace R] [ContinuousMul R]
    (ψ : G →* Rˣ) (hψ : Continuous fun g => (ψ g : R)) : ContAction (charRep ψ) :=
  (hψ.comp continuous_fst).mul continuous_snd

theorem kill_of_step (ψ : G →* ℤ_[l]ˣ) (hψ : Continuous fun g => (ψ g : ℤ_[l])) (N : ℕ)
    (H : ∀ d ∈ Z2 (charRep ψ), ∃ b : G → ℤ_[l], Continuous b ∧
      ∀ p, (l : ℤ_[l]) ^ (N + 1) ∣ (l : ℤ_[l]) ^ N * d p - d1 (charRep ψ) b p) :
    ∀ d ∈ Z2 (charRep ψ), ∃ b : G → ℤ_[l], Continuous b ∧
      ∀ p, d1 (charRep ψ) b p = (l : ℤ_[l]) ^ N * d p := by
  have hl : l.Prime := Fact.out
  have hl0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hl0' : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.ne_zero
  have step : ∀ d : Z2 (charRep ψ), ∃ (b : G → ℤ_[l]) (d' : Z2 (charRep ψ)), Continuous b ∧
      ∀ p, (l : ℤ_[l]) ^ N * d.1 p - d1 (charRep ψ) b p = (l : ℤ_[l]) ^ (N + 1) * d'.1 p := by
    intro d
    obtain ⟨b, hb, hd⟩ := H d.1 d.2
    choose d' hd' using hd
    have hz : ((l : ℤ_[l]) ^ N • d.1 - d1 (charRep ψ) b) ∈ Z2 (charRep ψ) :=
      sub_mem (Submodule.smul_mem _ _ d.2)
        (coboundaries2_le_cocycles2 _ (contAction_charRep ψ hψ) ⟨b, hb, rfl⟩)
    have he : ((l : ℤ_[l]) ^ N • d.1 - d1 (charRep ψ) b) = fun p => (l : ℤ_[l]) ^ (N + 1) * d' p :=
      funext hd'
    rw [he] at hz
    refine ⟨b, ⟨d', ?_, fun g h k => ?_⟩, hb, hd'⟩
    · rw [continuous_iff_coe]
      have h1 := ((continuous_iff_coe _).1 hz.1).div_const
        ((l : ℚ_[l]) ^ (N + 1))
      refine h1.congr fun p => ?_
      push_cast
      field_simp
    · have h2 := hz.2 g h k
      simp only [charRep_apply] at h2 ⊢
      apply mul_left_cancel₀ (pow_ne_zero (N + 1) hl0)
      linear_combination h2
  choose B T hB hT using step
  intro d hd
  let D : ℕ → Z2 (charRep ψ) := fun n => T^[n] ⟨d, hd⟩
  have hD : ∀ n, D (n + 1) = T (D n) := fun n => Function.iterate_succ_apply' _ _ _
  have hlt : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  have hbd : ∀ (n : ℕ) (x : ℤ_[l]), ‖(l : ℤ_[l]) ^ n * x‖ ≤ ‖(l : ℤ_[l])‖ ^ n := fun n x => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) x.norm_le_one
  have hsum : Summable fun n : ℕ => ‖(l : ℤ_[l])‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hlt
  refine ⟨fun g => ∑' n : ℕ, (l : ℤ_[l]) ^ n * B (D n) g,
    continuous_tsum (fun n => continuous_const.mul (hB _)) hsum (fun n g => hbd n _), ?_⟩
  rintro ⟨g, h⟩
  have hS : ∀ x, Tendsto (fun n => ∑ k ∈ Finset.range n, (l : ℤ_[l]) ^ k * B (D k) x) atTop
      (𝓝 (∑' n : ℕ, (l : ℤ_[l]) ^ n * B (D n) x)) := fun x =>
    (Summable.of_norm_bounded hsum (fun n => hbd n _)).hasSum.tendsto_sum_nat
  have h1 := (((hS h).const_mul (ψ g : ℤ_[l])).sub (hS (g * h))).add (hS g)
  have h2 : ∀ n, (ψ g : ℤ_[l]) * (∑ k ∈ Finset.range n, (l : ℤ_[l]) ^ k * B (D k) h) -
      (∑ k ∈ Finset.range n, (l : ℤ_[l]) ^ k * B (D k) (g * h)) +
      (∑ k ∈ Finset.range n, (l : ℤ_[l]) ^ k * B (D k) g) =
      (l : ℤ_[l]) ^ N * d (g, h) - (l : ℤ_[l]) ^ n * ((l : ℤ_[l]) ^ N * (D n).1 (g, h)) := by
    intro n
    induction n with
    | zero => simp [D]
    | succ n ih =>
      have h3 := hT (D n) (g, h)
      rw [← hD, d1_apply, charRep_apply] at h3
      simp only [Finset.sum_range_succ]
      linear_combination ih - (l : ℤ_[l]) ^ n * h3
  have h4 : Tendsto (fun n : ℕ => (l : ℤ_[l]) ^ n * ((l : ℤ_[l]) ^ N * (D n).1 (g, h))) atTop
      (𝓝 0) :=
    squeeze_zero_norm (fun n => hbd n _) (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt)
  have h5 := h4.const_sub ((l : ℤ_[l]) ^ N * d (g, h))
  rw [sub_zero] at h5
  simp only [h2] at h1
  rw [d1_apply, charRep_apply]
  exact tendsto_nhds_unique h1 h5

theorem exists_rep : ∃ rep : ℚ_[l] → ℚ_[l], (∀ x, ‖rep x - x‖ ≤ 1) ∧
    ∀ x y, ‖x - y‖ ≤ 1 → rep x = rep y := by
  refine ⟨fun x => Classical.epsilon fun y => ‖y - x‖ ≤ 1,
    fun x => Classical.epsilon_spec (p := fun y => ‖y - x‖ ≤ 1) ⟨x, by simp⟩, fun x y h => ?_⟩
  have : (fun z => ‖z - x‖ ≤ 1) = fun z => ‖z - y‖ ≤ 1 := by
    funext z
    exact propext ⟨fun h' => padic_norm_sub_le_trans h' h,
      fun h' => padic_norm_sub_le_trans h' (by rwa [norm_sub_rev])⟩
  simp only [this]

theorem lift_of_kill (ψ : G →* ℤ_[l]ˣ) (hψ : Continuous fun g => (ψ g : ℤ_[l])) (N : ℕ)
    (H : ∀ d ∈ Z2 (charRep ψ), ∃ b : G → ℤ_[l], Continuous b ∧
      ∀ p, d1 (charRep ψ) b p = (l : ℤ_[l]) ^ N * d p) (c : G → ℚ_[l])
    (hc : ∀ σ τ, ‖c (σ * τ) - c σ - ((ψ σ : ℤ_[l]) : ℚ_[l]) * c τ‖ ≤ 1)
    (hloc : ∀ σ, ∀ᶠ τ in 𝓝 σ, ‖c τ - c σ‖ ≤ 1) :
    ∃ z : G → ℚ_[l], Continuous z ∧ (∀ σ τ, z (σ * τ) = z σ + ((ψ σ : ℤ_[l]) : ℚ_[l]) * z τ) ∧
      ∀ σ, ‖z σ - (l : ℚ_[l]) ^ N * c σ‖ ≤ 1 := by
  obtain ⟨rep, hr1, hr2⟩ := exists_rep (l := l)
  have hadd : ∀ x y : ℚ_[l], ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x + y‖ ≤ 1 := fun x y hx hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  have hmul : ∀ (x : ℤ_[l]) (y : ℚ_[l]), ‖y‖ ≤ 1 → ‖(x : ℚ_[l]) * y‖ ≤ 1 := fun x y hy => by
    rw [norm_mul]; exact mul_le_one₀ x.2 (norm_nonneg _) hy
  set c' : G → ℚ_[l] := fun σ => rep (c σ) with hc'
  have hcont : Continuous c' := by
    rw [continuous_iff_continuousAt]
    intro σ
    refine (continuousAt_const (y := c' σ)).congr ?_
    filter_upwards [hloc σ] with τ hτ
    exact (hr2 _ _ hτ).symm
  have hψ' : Continuous fun g => ((ψ g : ℤ_[l]) : ℚ_[l]) :=
    PadicInt.isOpenEmbedding_coe.continuous.comp hψ
  have hint : ∀ p : G × G,
      ‖((ψ p.1 : ℤ_[l]) : ℚ_[l]) * c' p.2 - c' (p.1 * p.2) + c' p.1‖ ≤ 1 := by
    rintro ⟨σ, τ⟩
    have e : ((ψ σ : ℤ_[l]) : ℚ_[l]) * c' τ - c' (σ * τ) + c' σ =
        -(c (σ * τ) - c σ - ((ψ σ : ℤ_[l]) : ℚ_[l]) * c τ) +
          (((ψ σ : ℤ_[l]) : ℚ_[l]) * (c' τ - c τ) + (-(c' (σ * τ) - c (σ * τ)) + (c' σ - c σ))) := by
      ring
    dsimp only
    rw [e]
    refine hadd _ _ (by rw [norm_neg]; exact hc σ τ) (hadd _ _ (hmul _ _ (hr1 _))
      (hadd _ _ (by rw [norm_neg]; exact hr1 _) (hr1 _)))
  let d : G × G → ℤ_[l] := fun p => ⟨_, hint p⟩
  have hdv : ∀ σ τ, ((d (σ, τ) : ℤ_[l]) : ℚ_[l]) =
      ((ψ σ : ℤ_[l]) : ℚ_[l]) * c' τ - c' (σ * τ) + c' σ := fun _ _ => rfl
  have hd : d ∈ Z2 (charRep ψ) := by
    refine ⟨?_, fun g h k => ?_⟩
    · rw [continuous_iff_coe]
      exact (((hψ'.comp continuous_fst).mul (hcont.comp continuous_snd)).sub
        (hcont.comp continuous_mul)).add (hcont.comp continuous_fst)
    · apply Subtype.ext
      rw [charRep_apply]
      push_cast
      simp only [hdv, map_mul, Units.val_mul, PadicInt.coe_mul, mul_assoc]
      ring
  obtain ⟨b, hb, hbd⟩ := H d hd
  refine ⟨fun σ => (l : ℚ_[l]) ^ N * c' σ - (b σ : ℚ_[l]),
    (continuous_const.mul hcont).sub (PadicInt.isOpenEmbedding_coe.continuous.comp hb),
    fun σ τ => ?_, fun σ => ?_⟩
  · have h1 := congrArg (fun x : ℤ_[l] => (x : ℚ_[l])) (hbd (σ, τ))
    simp only [d1_apply, charRep_apply] at h1
    push_cast at h1
    rw [hdv] at h1
    linear_combination h1
  · have e : (l : ℚ_[l]) ^ N * c' σ - (b σ : ℚ_[l]) - (l : ℚ_[l]) ^ N * c σ =
        (((l : ℤ_[l]) ^ N : ℤ_[l]) : ℚ_[l]) * (c' σ - c σ) + ((-b σ : ℤ_[l]) : ℚ_[l]) := by
      push_cast; ring
    dsimp only
    rw [e]
    exact hadd _ _ (hmul _ _ (hr1 _)) (-b σ).2

noncomputable def redChar (χ : G →* ℤ_[l]ˣ) (r : ℕ) : G →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ

omit [TopologicalSpace G] [ContinuousMul G] in
theorem redChar_apply (χ : G →* ℤ_[l]ˣ) (r : ℕ) (g : G) :
    (redChar χ r g : ZMod (l ^ r)) = PadicInt.toZModPow r (χ g : ℤ_[l]) := rfl

theorem continuous_toZModPow (r : ℕ) :
    Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  have hl : l.Prime := Fact.out
  rw [continuous_iff_continuousAt]
  intro x
  refine (continuousAt_const (y := PadicInt.toZModPow r x)).congr ?_
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(r : ℤ)) := zpow_pos (by exact_mod_cast hl.pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  exact hy.symm

theorem step_of_duality (χ ψ : G →* ℤ_[l]ˣ) (N : ℕ)
    (hinj : Function.Injective
      (cup20 (redChar χ (N + 1)) (charRep (redChar ψ (N + 1))) (MonoidHom.id G)))
    (g₀ : G) (hg : ‖(χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(N : ℤ))) :
    ∀ d ∈ Z2 (charRep ψ), ∃ b : G → ℤ_[l], Continuous b ∧
      ∀ p, (l : ℤ_[l]) ^ (N + 1) ∣ (l : ℤ_[l]) ^ N * d p - d1 (charRep ψ) b p := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ (N + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  intro d hd
  set π : ℤ_[l] →+* ZMod (l ^ (N + 1)) := PadicInt.toZModPow (N + 1) with hπ
  obtain ⟨w, hw⟩ : (χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1 ∣ (l : ℤ_[l]) ^ N := by
    set a := (χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1
    have hpos : 0 < ‖(a : ℚ_[l])‖ := by
      rw [← PadicInt.norm_def, hg]; exact zpow_pos (by exact_mod_cast hl.pos) _
    have ha : (a : ℚ_[l]) ≠ 0 := norm_pos_iff.1 hpos
    refine ⟨⟨(l : ℚ_[l]) ^ N / a, ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, div_le_one hpos, ← PadicInt.norm_def, hg, Padic.norm_p_pow]
    · change (((l : ℤ_[l]) ^ N : ℤ_[l]) : ℚ_[l]) = (a : ℚ_[l]) * ((l : ℚ_[l]) ^ N / a)
      push_cast
      field_simp
  have hkill : ∀ φ : H0 ((twDual (redChar χ (N + 1)) (charRep (redChar ψ (N + 1)))).comp
      (MonoidHom.id G)), (π ((l : ℤ_[l]) ^ N)) • φ = 0 := by
    intro φ
    apply Subtype.ext
    apply TDual.ext
    intro m
    have h1 := congrArg (fun f : TDual (ZMod (l ^ (N + 1))) (ZMod (l ^ (N + 1))) => f m) (φ.2 g₀)
    have h2 : ∀ a : ZMod (l ^ (N + 1)), φ.1 (a * m) = a * φ.1 m := fun a =>
      LinearMap.map_smul (show ZMod (l ^ (N + 1)) →ₗ[ZMod (l ^ (N + 1))] ZMod (l ^ (N + 1))
        from φ.1) a m
    change π (χ g₀ : ℤ_[l]) * φ.1 (π (ψ g₀⁻¹ : ℤ_[l]) * m) = φ.1 m at h1
    rw [h2] at h1
    change π ((l : ℤ_[l]) ^ N) * φ.1 m = 0
    rw [hw, map_mul, map_sub, map_mul, map_one]
    linear_combination π w * h1
  have hz : (fun p => π (d p)) ∈ Z2 ((charRep (redChar ψ (N + 1))).comp (MonoidHom.id G)) := by
    refine ⟨(continuous_toZModPow _).comp hd.1, fun g h k => ?_⟩
    have h1 := congrArg π (hd.2 g h k)
    simp only [charRep_apply, map_sub, map_add, map_mul, map_zero] at h1
    exact h1
  have hx : (π ((l : ℤ_[l]) ^ N)) • (Submodule.Quotient.mk ⟨_, hz⟩ :
      H2 ((charRep (redChar ψ (N + 1))).comp (MonoidHom.id G))) = 0 := by
    apply hinj
    ext φ
    rw [map_smul, LinearMap.smul_apply, ← map_smul, hkill, map_zero, map_zero,
      LinearMap.zero_apply]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨c, hc, hcd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hx
  have hc' : Continuous c := hc
  refine ⟨fun g => (((c g).val : ℕ) : ℤ_[l]),
    (continuous_of_discreteTopology (f := fun a : ZMod (l ^ (N + 1)) =>
      ((a.val : ℕ) : ℤ_[l]))).comp hc', ?_⟩
  rintro ⟨g, h⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, ← hπ]
  have h1 := congrFun hcd (g, h)
  change π (ψ g : ℤ_[l]) * c h - c (g * h) + c g = π ((l : ℤ_[l]) ^ N) * π (d (g, h)) at h1
  simp only [d1_apply, charRep_apply, map_sub, map_add, map_mul π, map_natCast,
    ZMod.natCast_zmod_val]
  rw [h1, sub_self]

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem finite_Ks (K : FinExt l) (j : ℕ) : FiniteDimensional ℚ_[l] (Ks K j) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hf : {x : Om l | x ^ (l ^ j) = 1}.Finite := by
    refine (Polynomial.nthRootsFinset (l ^ j) (1 : Om l)).finite_toSet.subset fun x hx => ?_
    exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset
      (pow_pos (Fact.out : l.Prime).pos _) _).2 hx)
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ j) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

theorem isCyc_unique {χ χ' : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (h' : IsCyc χ') : χ = χ' := by
  ext g
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  by_contra hne
  obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) (not_le.1 hne)
  obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) m
  obtain ⟨a, ha, hga⟩ := h g m ζ hζ.pow_eq_one
  obtain ⟨a', ha', hga'⟩ := h' g m ζ hζ.pow_eq_one
  have h0 : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have h1 : ζ ^ ((a : ℤ) - a') = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, zpow_natCast, ← hga, ← hga', div_self]
    exact (map_ne_zero g).2 h0
  have h2 := (hζ.zpow_eq_one_iff_dvd _).1 h1
  have h3 : ‖(a : ℚ_[l]) - a'‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - a') m).2 (by exact_mod_cast h2)
    exact_mod_cast this
  rw [norm_sub_rev] at ha'
  exact absurd (padic_norm_sub_le_trans ha (padic_norm_sub_le_trans h3 ha')) (not_le.2 hm)

theorem continuous_fixingSubgroupEquiv (L : IntermediateField ℚ_[l] (Om l)) :
    Continuous L.fixingSubgroupEquiv.symm ∧ Continuous L.fixingSubgroupEquiv := by
  have h1 : Continuous L.fixingSubgroupEquiv.symm := by
    refine Continuous.subtype_mk ?_ _
    change Continuous (L.fixingSubgroup.subtype.comp L.fixingSubgroupEquiv.symm.toMonoidHom)
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one]
    intro U hU
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff _ _ _).1 hU
    obtain ⟨S, hS⟩ : E.FG := IntermediateField.essFiniteType_iff.1 inferInstance
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    refine ⟨IntermediateField.adjoin L (S : Set (Om l)),
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, ?_⟩
    intro g hg
    apply hEU
    rw [← hS, SetLike.mem_coe, mem_fixingSubgroup_adjoin_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x
      (IntermediateField.subset_adjoin _ _ hx)
  exact ⟨h1, (h1.homeoOfEquivCompactToT2 (f := L.fixingSubgroupEquiv.symm.toEquiv)).symm.continuous⟩

theorem lift_cocycle_of_duality (hT : Formalism.GaloisCohomology.LocalTateDualityK) (χ : GQ l →* ℚ_[l]ˣ)
    (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) (hs : Lev l s) (e : ℕ) (c : GQ l → ℚ_[l])
    (hc : ∀ σ ∈ Gj K s, ∀ τ ∈ Gj K s,
      ‖c (σ * τ) - c σ - ((χ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * c τ‖ ≤ 1)
    (hloc : ∀ σ ∈ Gj K s, ∀ᶠ τ in nhdsWithin σ (Gj K s), ‖c τ - c σ‖ ≤ 1) :
    ∃ z : GQ l → ℚ_[l],
      CocOn (Gj K s) (fun σ y => ((χ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z ∧
      ∀ σ ∈ Gj K s, ‖z σ - (l : ℚ_[l]) ^ (s + padicValNat l (e + 1)) * c σ‖ ≤ 1 := by
  classical
  set L := Ks K s with hL
  set N := s + padicValNat l (e + 1) with hN
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv L
  set Φ := L.fixingSubgroupEquiv with hΦ
  let χZ : Formalism.GaloisCohomology.GK l L →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l L) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (χ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hχ (isCyc_cycChar l)]; rfl
  let ψ : Formalism.GaloisCohomology.GK l L →* ℤ_[l]ˣ := χZ ^ (-(e : ℤ))
  have hψ : ∀ g, ((ψ g : ℤ_[l]) : ℚ_[l]) =
      ((χ (Φ.symm g : GQ l) ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) := fun g => by
    rw [Units.val_zpow_eq_zpow_val, ← hχZ]
    have h1 : ψ g = χZ g ^ (-(e : ℤ)) := rfl
    have h2 := map_zpow (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom) (χZ g) (-(e : ℤ))
    have h3 := congrArg Units.val h2
    rw [Units.val_zpow_eq_zpow_val] at h3
    rw [h1]
    exact h3
  have hψc : Continuous fun g => (ψ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hψ, Units.val_zpow_eq_zpow_val]
    exact (hχ.continuous.comp (continuous_subtype_val.comp hΦ1)).zpow₀ _
      fun g => Or.inl (Units.ne_zero _)
  obtain ⟨g₀, hg₀, hg₁⟩ := (gen_dense l _ χ (GlobalTheory.InertiaEigenvalues.isActC_galActC l) hχ K s hs).1
  have hg : ‖(χZ (Φ ⟨g₀, hg₀⟩) : ℤ_[l]) * (ψ (Φ ⟨g₀, hg₀⟩)⁻¹ : ℤ_[l]) - 1‖ =
      (l : ℝ) ^ (-(N : ℤ)) := by
    have h1 := LiftExp.norm_zpow_sub_one l s hs _ hg₁ ((e + 1 : ℕ) : ℤ) (by omega)
    rw [padicValInt.of_nat] at h1
    rw [PadicInt.norm_def]
    push_cast
    rw [hχZ, hψ, hN]
    push_cast at h1 ⊢
    rw [← h1]
    congr 2
    simp only [map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_inv, Units.val_inv_eq_inv_val,
      inv_zpow', neg_neg]
    rw [zpow_add_one₀ (Units.ne_zero _), mul_comm]
  have hcont : ContAction (charRep (redChar ψ (N + 1))) :=
    contAction_charRep _ ((continuous_toZModPow _).comp hψc)
  haveI : NeZero (l ^ (N + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hdual := (hT l L (finite_Ks K s) (N + 1) (ZMod (l ^ (N + 1)))
    (charRep (redChar ψ (N + 1))) (Nat.succ_pos _) hcont).2.2.2.2.1
  have hkill := kill_of_step ψ hψc N (step_of_duality χZ ψ N hdual _ hg)
  obtain ⟨z, hz1, hz2, hz3⟩ := lift_of_kill ψ hψc N hkill (fun g => c (Φ.symm g : GQ l))
    (fun σ τ => by
      rw [hψ, map_mul]
      exact hc _ (Φ.symm σ).2 _ (Φ.symm τ).2)
    (fun σ => by
      have h1 := hloc _ (Φ.symm σ).2
      have h2 : Tendsto (fun g => (Φ.symm g : GQ l)) (𝓝 σ)
          (nhdsWithin (Φ.symm σ : GQ l) (Gj K s)) :=
        tendsto_nhdsWithin_iff.2 ⟨(continuous_subtype_val.comp hΦ1).tendsto σ,
          Eventually.of_forall fun g => (Φ.symm g).2⟩
      exact h2.eventually h1)
  let z' : GQ l → ℚ_[l] := fun σ => if h : σ ∈ L.fixingSubgroup then z (Φ ⟨σ, h⟩) else 0
  have hz' : ∀ σ (h : σ ∈ Gj K s), z' σ = z (Φ ⟨σ, h⟩) := fun σ h => dif_pos h
  refine ⟨z', ⟨?_, fun _ _ => trivial, fun σ hσ τ hτ => ?_⟩, fun σ hσ => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    exact (hz1.comp hΦ2).congr fun σ => (hz' σ.1 σ.2).symm
  · rw [hz' _ (mul_mem hσ hτ), hz' _ hσ, hz' _ hτ]
    have h1 := hz2 (Φ ⟨σ, hσ⟩) (Φ ⟨τ, hτ⟩)
    rw [hψ, ← map_mul, MulEquiv.symm_apply_apply] at h1
    exact h1
  · have h1 := hz3 (Φ ⟨σ, hσ⟩)
    rw [MulEquiv.symm_apply_apply] at h1
    rw [hz' _ hσ]
    exact h1

theorem lift_cocycle : ∀ (D : Formalism.BasicNotions.D7), adm2 D → ArchimedeanSignatureMatching D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ (e r : ℕ) (c : GQ l → ℚ_[l]), (∀ σ ∈ Gj K s, ‖c σ‖ ≤ (l : ℝ) ^ r) → (∀ σ ∈ Gj K s, ∀ τ ∈ Gj K s, ‖c (σ * τ) - c σ - (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * c τ‖ ≤ 1) → (∀ σ ∈ Gj K s, ∀ᶠ τ in nhdsWithin σ (Gj K s), ‖c τ - c σ‖ ≤ 1) → ∃ z : GQ l → ℚ_[l], CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z ∧ ∀ σ ∈ Gj K s, ‖z σ - (l : ℚ_[l]) ^ (s + padicValNat l (e + 1)) * c σ‖ ≤ 1 :=
  fun D h2 _ l _ K s hs e _ c _ hc hloc =>
    lift_cocycle_of_duality h2 (D.loc l).χQ (D.loc l).χQ_cyc K s hs e c hc hloc

end GlobalTheory.Cyc.TwistLift
