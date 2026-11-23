import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfInducedOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsElementHeightDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverNormsPullbackPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormShiftRationalMultipleLogStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsScaleByConstantStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoverNef

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem norms_shift {V : Cover Y} {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (t : (𝓞 F →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) :
    Norms V (L.shift t ht) f (fun σ y => a σ y - t (σ.comp (algebraMap (𝓞 F) F))) l := by
  obtain ⟨r, hr, hu, hc, hf⟩ := h
  refine ⟨r, hr, hu, fun σ z y y' i e₁ e₂ hi => ?_, hf⟩
  show a σ y - _ = _ - ((L.φ _).φ (i PUnit.unit) y' + 2 * t _) / 2
  rw [hc σ z y y' i e₁ e₂ hi]
  ring

theorem nefFib_of_norms {V : Cover Y} {L₁ L₂ : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} {c : HeightOneSpectrum (𝓞 F) → ℝ}
    (hc : (Function.support c).Finite) (h₁ : Norms V L₁ f a l) (h₂ : Norms V L₂ f a fun v e y => l v e y + c v)
    (hN : NefFib L₂) : NefFib L₁ := by
  obtain ⟨m, b, b', hb, hb', hm⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F c hc (GlobalTheory.T.norm_shift_rational_multiple_log F Y V L₁ L₂ f a l c h₁ h₂)
  have hb₀ : (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb
  have hb₀' : (algebraMap (𝓞 F) F b') ≠ 0 := by simpa using hb'
  set q : F := algebraMap (𝓞 F) F b' / algebraMap (𝓞 F) F b with hq
  have hq₀ : q ≠ 0 := div_ne_zero hb₀' hb₀
  let t : (𝓞 F →+* ℂ) → ℝ := fun τ => Real.log ‖τ b'‖ - Real.log ‖τ b‖
  have ht : ∀ τ, t ((starRingEnd ℂ).comp τ) = t τ := fun τ => by simp [t]
  have N₁ := GlobalTheory.T.norms_tensor_power F Y V L₁ f a l m h₁
  have N₂ := norms_shift (GlobalTheory.T.norms_scale_by_constant F Y V _ _ _ _ q hq₀ (GlobalTheory.T.norms_tensor_power F Y V L₂ f a _ m h₂)) t ht
  have hI := GlobalTheory.T.isometric_of_same_norms F Y V _ _ _ _ _ N₁ (N₂.congr (fun _ => rfl) (fun σ y => ?_) (fun v e y => ?_))
  · have hp := GlobalTheory.T.nefFib_pow_iff' (𝓞 F) V.X V.p V.ar.isProjOver
    refine (hp L₁ m m.pos).1 ((GlobalTheory.TrueGeo.NefFibUniq.nefFib_iff_of_isometric hI).2 ?_)
    exact (GlobalTheory.TrueGeo.NefFibUniq.nefFib_shift _ _ _).2 ((hp L₂ m m.pos).2 hN)
  · have e₁ : (σ.comp (algebraMap (𝓞 F) F)) b' = σ (algebraMap (𝓞 F) F b') := rfl
    have e₂ : (σ.comp (algebraMap (𝓞 F) F)) b = σ (algebraMap (𝓞 F) F b) := rfl
    simp only [t, e₁, e₂, hq, map_div₀, norm_div]
    rw [Real.log_div (by simpa using hb₀') (by simpa using hb₀)]
    ring
  · have := hm v
    simp only [hq, map_div₀]
    rw [Real.log_div ((AbsoluteValue.pos_iff _).2 hb₀').ne' ((AbsoluteValue.pos_iff _).2 hb₀).ne']
    linear_combination this

end GlobalTheory.CoverNef

namespace GlobalTheory.CoverNef

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem surjective_of_cover {V V' : Cover Y} (a : V'.X ⟶ V.X) (ha : a ≫ V.p = V'.p) (g : V'.G ⟶ V.G)
    (hj : V'.j ≫ a = g ≫ V.j) (hπ : g ≫ V.π = V'.π) (hg : g (genericPoint V'.G) = genericPoint V.G) :
    Function.Surjective a := by
  obtain ⟨h₀, -⟩ := GlobalTheory.T.cover_refinement_generic_degree F Y V V' a ha g hj hπ hg
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  have : IsProper V'.p := CommonModel.isProper_of_isProjOver V'.ar.isProjOver
  have : IsProper (a ≫ V.p) := by rw [ha]; infer_instance
  have : IsProper a := IsProper.of_comp a V.p
  have : IsDominant a := ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨_, h₀⟩)
    (dense_iff_closure_eq.2 ((genericPoint_spec V.X).trans Set.top_eq_univ))⟩
  exact (surjective_of_isDominant_of_isClosed_range a a.isClosedMap.isClosed_range).surj

theorem nefFib_of_norms_adl : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y), A.NefFib →
    ∀ (V : Cover Y) (L : HermLB V.p) (k : ℕ), 0 < k → Norms V L (fun x => genAt A.D x ^ k) (fun σ y => k * lnAdl A σ y)
      (fun v e y => k * A.lg v e y) → NefFib L := by
  intro _ F _ _ Y A ⟨M, L₀, k₀, cf, hI, hN⟩ V L k hk hL
  obtain ⟨V', a, g, b, ha, hb, hj, hπ, hg, hb'⟩ := GlobalTheory.Mean4O.CoverDom.exists_cover_dominating F Y V M
  have N₁ := GlobalTheory.T.norms_tensor_power F Y V' _ _ _ _ (k₀ : ℕ) (GlobalTheory.T.norms_pullback_along_cover F Y V V' a ha g hj hπ hg L _ _ _ hL)
  have N₂ := GlobalTheory.T.norms_tensor_power F Y V' _ _ _ _ k (GlobalTheory.T.cover_norms_pullback_power F (cxSt F) Y A M L₀ k₀ cf hI V' b hb hb')
  have hc : (Function.support fun v => (k : ℝ) * (k₀ : ℕ) * (A.n : ℕ) * cf v).Finite :=
    hI.1.subset (Function.support_mul_subset_right _ _)
  have hP := nefFib_of_norms hc N₁ (N₂.congr (fun x => by rw [← pow_mul, ← pow_mul, mul_comm])
    (fun σ y => by ring) (fun v e y => by ring))
    ((GlobalTheory.T.nefFib_pow_iff' (𝓞 F) V'.X V'.p V'.ar.isProjOver _ k hk).2
      (GlobalTheory.T.nefFib_pullback (𝓞 F) M.X V'.X M.p V'.p M.ar.isProjOver V'.ar.isProjOver b hb L₀ hN))
  exact GlobalTheory.T.nefFib_of_surjective_pullback (𝓞 F) V.X V'.X V.p V'.p V.ar.isProjOver V'.ar.isProjOver a ha
    (surjective_of_cover a ha g hj hπ hg) L ((GlobalTheory.T.nefFib_pow_iff' (𝓞 F) V'.X V'.p V'.ar.isProjOver _ _ k₀.pos).1 hP)

end GlobalTheory.CoverNef

end
