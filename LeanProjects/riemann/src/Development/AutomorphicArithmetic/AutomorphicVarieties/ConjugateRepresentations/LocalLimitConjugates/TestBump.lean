import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusions
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private def Bp (W S : Set (GA E a)) : Prop :=
  ∃ f : GA E a → ℝ, (fun g => (f g : ℂ)) ∈ Sm E a ∧ (∀ᶠ k in 𝓝 1, ∀ g, f (g * finGL E a k) = f g) ∧
    (∀ g, 0 ≤ f g) ∧ (∀ g ∈ S, 0 < f g) ∧ ∀ g ∉ W, f g = 0

private theorem tens_mem (β : Lie E a → ℂ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (c : GL (Fin a) (Af E) → ℂ) (g₀ : GA E a) :
    (fun g => β (toL (GeneralLinearGroup.map (pInf E) (g₀ * g)).val) *
      c (GeneralLinearGroup.map (pFin E) (g₀ * g))) ∈ Sm E a := by
  intro g
  let L : Lie E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap
    (LinearMap.mulLeft ℝ (GeneralLinearGroup.map (pInf E) (g₀ * g)).val :
      Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))
  have h : ContDiff ℝ (⊤ : ℕ∞) fun x => β (L x) * c (GeneralLinearGroup.map (pFin E) (g₀ * g)) :=
    (hβ.comp L.contDiff).mul contDiff_const
  refine h.contDiffOn.congr fun x hx => ?_
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  rw [chart_val, ← mul_assoc, map_mul, map_mul _ (g₀ * g), pInf_infGL, pFin_infGL, mul_one]
  rfl

private theorem bp_pt {W : Set (GA E a)} {g₀ : GA E a} (hW : W ∈ 𝓝 g₀) : ∃ S ∈ 𝓝 g₀, Bp W S := by
  classical
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.GLProj.continuous_proj_incl E a
  have hc : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => g₀ * (infGL E a p.1 * finGL E a p.2) :=
    continuous_const.mul ((c3.comp continuous_fst).mul (c4.comp continuous_snd))
  have hn := hc.continuousAt (x := (1, 1)).preimage_mem_nhds (t := W) (by simpa using hW)
  obtain ⟨N, hN, V, hV, hNV⟩ := mem_nhds_prod_iff.1 hn
  obtain ⟨U, hU, hUV⟩ := GlobalTheory.CompanionTheory.DenseKFin.exists_openSubgroup_GLAf hV
  obtain ⟨β, b0, b1, b2, -, b3⟩ := GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv E a N hN
  have bs : ContDiff ℝ (⊤ : ℕ∞) fun x => (β x : ℂ) := b2.1
  have bc : Continuous β := Complex.continuous_re.comp bs.continuous
  have d1 : Continuous fun g : GA E a => β (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) :=
    bc.comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp
      (c1.comp (continuous_const.mul continuous_id)))
  have d2 : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) :=
    c2.comp (continuous_const.mul continuous_id)
  refine ⟨{g | 0 < β (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val)} ∩
    {g | GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ U}, ?_,
    fun g => β (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) *
      if GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ U then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
  · refine ((isOpen_lt continuous_const d1).inter (hU.preimage d2)).mem_nhds ⟨?_, ?_⟩
    · simp only [Set.mem_setOf_eq, inv_mul_cancel, map_one]
      exact b1
    · simp only [Set.mem_preimage, inv_mul_cancel, map_one]
      exact U.one_mem
  · have h := tens_mem _ bs (fun k => ((if k ∈ U then 1 else 0 : ℝ) : ℂ)) g₀⁻¹
    simpa only [Complex.ofReal_mul] using h
  · filter_upwards [hU.mem_nhds U.one_mem] with k hk g
    rw [← mul_assoc, map_mul, map_mul _ (g₀⁻¹ * g), pInf_finGL, pFin_finGL, mul_one]
    simp only [U.mul_mem_cancel_right hk]
  · intro g
    refine mul_nonneg (b0 _) ?_
    split_ifs <;> norm_num
  · rintro g ⟨h1, h2⟩
    exact mul_pos h1 ((if_pos h2).symm ▸ one_pos)
  · intro g hg
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    have h3 : GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ U := by
      by_contra h3
      exact h2 (if_neg h3)
    obtain ⟨y, hy, e⟩ := b3 _ h1
    obtain rfl : y = GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) := Units.ext e
    have h4 := hNV (Set.mk_mem_prod hy (hUV h3))
    simp only [Set.mem_preimage, infGL_mul_finGL, mul_inv_cancel_left] at h4
    exact hg h4

private theorem bp_cpt {W C : Set (GA E a)} (hC : IsCompact C) (hW : IsOpen W) (h : C ⊆ W) : Bp W C := by
  refine hC.induction_on (p := Bp W) ?_ ?_ ?_ ?_
  · exact ⟨0, (Sm E a).zero_mem, by simp, by simp, by simp, by simp⟩
  · rintro s t hst ⟨f, h1, h2, h3, h4, h5⟩
    exact ⟨f, h1, h2, h3, fun g hg => h4 g (hst hg), h5⟩
  · rintro s t ⟨f, h1, h2, h3, h4, h5⟩ ⟨f', k1, k2, k3, k4, k5⟩
    refine ⟨fun g => f g + f' g, ?_, ?_, fun g => add_nonneg (h3 g) (k3 g), ?_,
      fun g hg => by simp only [h5 g hg, k5 g hg, add_zero]⟩
    · simp only [Complex.ofReal_add]
      exact (Sm E a).add_mem h1 k1
    · filter_upwards [h2, k2] with k e1 e2 g
      rw [e1, e2]
    · rintro g (hg | hg)
      · exact add_pos_of_pos_of_nonneg (h4 g hg) (k3 g)
      · exact add_pos_of_nonneg_of_pos (h3 g) (k4 g hg)
  · intro x hx
    obtain ⟨S, hS, hb⟩ := bp_pt (hW.mem_nhds (h hx))
    exact ⟨S, mem_nhdsWithin_of_mem_nhds hS, hb⟩

private theorem lev_of (φ : Sm E a) (h : ∀ᶠ k in 𝓝 1, ∀ g, φ.1 (g * finGL E a k) = φ.1 g) : HasLev φ := by
  refine isOpen_iff_mem_nhds.2 fun k₀ h₀ => ?_
  have e : ∀ g, φ.1 (g * finGL E a k₀) = φ.1 g := fun g => congrFun (congrArg Subtype.val h₀) g
  have ht : Tendsto (fun k => k₀⁻¹ * k) (𝓝 k₀) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' _ _ (inv_mul_cancel _)
  filter_upwards [ht.eventually h] with k hk
  refine Subtype.ext (funext fun g => ?_)
  change φ.1 (g * finGL E a k) = φ.1 g
  rw [← e g, ← hk (g * finGL E a k₀), mul_assoc, ← map_mul, mul_inv_cancel_left]

end

theorem UpperTheory.V.Cj.H.testBump :
    UpperTheory.V.Cj.H.TestBump := by
  intro E _ _ _ a C W hC hW h
  obtain ⟨K, hK, hCK⟩ := exists_compact_superset hC
  obtain ⟨f, h1, h2, h3, h4, h5⟩ := bp_cpt hC (hW.inter isOpen_interior) (Set.subset_inter h hCK)
  refine ⟨⟨_, h1⟩, ⟨HasCompactSupport.intro hK fun g hg => ?_, lev_of _ ?_⟩, fun g => ⟨f g, h3 g, rfl⟩,
    fun g hg => Complex.ofReal_ne_zero.2 (h4 g hg).ne', fun g hg => ?_⟩
  · exact Complex.ofReal_eq_zero.2 (h5 g fun k => hg (interior_subset k.2))
  · filter_upwards [h2] with k hk g
    exact congrArg _ (hk g)
  · exact Complex.ofReal_eq_zero.2 (h5 g fun k => hg k.1)
