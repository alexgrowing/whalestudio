import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.FourierTransformTranslationInvariant

noncomputable section

set_option linter.unusedSectionVars false

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.TP.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem supp_congr' {C : Set (Sp k n)} {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Supp ξ C) {f g : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) (hg : g ∈ supportedIn (Set.univ : Set (Sp k n)))
    (e : ∀ p ∈ C, f p = g p) : ξ f = ξ g := by
  have := h (f - g) ((supportedIn Set.univ).sub_mem hf hg) fun p hp => by simp [e p hp]
  rwa [map_sub, sub_eq_zero] at this

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := PositivityTheory.RgUd.TP.Nil.hom t
  invFun := PositivityTheory.RgUd.TP.Nil.hom t⁻¹
  left_inv p := by
    simp [PositivityTheory.RgUd.TP.Nil.hom, smul_smul]
  right_inv p := by
    simp [PositivityTheory.RgUd.TP.Nil.hom, smul_smul]
  continuous_toFun := (continuous_fst.const_smul ((t : kˣ) : k)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.const_smul ((t⁻¹ : kˣ) : k)).prodMk continuous_snd

def trH (z : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun p := (p.1 + z, p.2)
  invFun p := (p.1 - z, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.add continuous_const).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub continuous_const).prodMk continuous_snd

variable (k) in
theorem fourQ : FourQ k := by
  intro hT n Z hZ
  obtain ⟨τ, hs, hnd, hnil⟩ := hT n Z hZ
  have h : Hyp τ Z := ⟨hs, hnd, hnil⟩
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SplitWeil.exists_hasConductor_one (k := k)
  have hψc : Continuous ψ := (GlobalTheory.T.addChar_conductor_integers_continuous_ne_one k ψ hψ).1
  let ν : Measure k := Measure.addHaar
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (supportedIn (Set.univ : Set (Sp k n)))
  let Φ : (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ) := LinearMap.ofIsCompl hC (phiS ψ ν h hψc) 0
  have hΦ : ∀ f (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))), Φ f = phi0 ψ ν h f := fun f hf =>
    LinearMap.ofIsCompl_left_apply hC (⟨f, hf⟩ : supportedIn (Set.univ : Set (Sp k n)))
  have h1 : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => by rw [hΦ f hf]; exact test_vector_mem_schwartz_bruhat ψ ν h hψ hf
  set K : ℂ := ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ)⁻¹ *
    ((((ν.real (𝒪[k] : Set k) ^ 2 * nabs k 1) ^ (dd Z) : ℝ)) : ℂ) with hKdef
  have hK : K ≠ 0 := by
    have h1 : 0 < ν.real (𝒪[k] : Set k) :=
      ENNReal.toReal_pos ((isOpen_int k).measure_ne_zero ν ⟨0, zero_mem _⟩) (isCompact_int k).measure_lt_top.ne
    have h2 : 0 < nabs k 1 := by
      show (0 : ℝ) < ((distribHaarChar k 1 : NNReal) : ℝ)
      exact_mod_cast distribHaarChar_pos
    have h3 : ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (distribHaarChar_pos).ne'
    refine mul_ne_zero (inv_ne_zero h3) ?_
    exact_mod_cast (pow_pos (mul_pos (pow_pos h1 2) h2) _).ne'
  let Φ' : (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ) := K⁻¹ • (Φ ∘ₗ LinearMap.funLeft ℂ ℂ (Refl τ Z))
  have hR : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), (fun q => f (Refl τ Z q)) ∈
      supportedIn (Set.univ : Set (Sp k n)) := fun f hf => by
    have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hf
      { toFun := Refl τ Z, invFun := Refl τ Z, left_inv := Refl_Refl h, right_inv := Refl_Refl h,
        continuous_toFun := (continuous_fst.sub (((continuous_Pr τ Z).comp continuous_fst).const_smul (2 : k))).prodMk
          continuous_snd
        continuous_invFun := (continuous_fst.sub (((continuous_Pr τ Z).comp continuous_fst).const_smul (2 : k))).prodMk
          continuous_snd : Sp k n ≃ₜ Sp k n }
    exact this
  have hRU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), (fun q => f (Refl τ Z q)) ∈ supportedIn (UU : Set (Sp k n)) :=
    fun f hf => ⟨(hR f ⟨hf.1, Set.subset_univ _⟩).1, fun q hq => by
      have := hf.2 (show Refl τ Z q ∈ Function.support f from hq)
      exact this⟩
  have h1' : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), Φ' f ∈ supportedIn (Set.univ : Set (Sp k n)) := by
    intro f hf
    show K⁻¹ • Φ (fun q => f (Refl τ Z q)) ∈ _
    refine Submodule.smul_mem _ _ ?_
    exact h1 _ (hR f hf)
  have hU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ f ∈ supportedIn (UU : Set (Sp k n)) := by
    intro f hf
    rw [hΦ f ⟨hf.1, Set.subset_univ _⟩]
    exact fourier_transform_preserves_compact ψ ν h hψ hf
  have hU' : ∀ f ∈ supportedIn (UU : Set (Sp k n)), Φ' f ∈ supportedIn (UU : Set (Sp k n)) := by
    intro f hf
    show K⁻¹ • Φ (fun q => f (Refl τ Z q)) ∈ _
    refine Submodule.smul_mem _ _ ?_
    exact hU _ (hRU f hf)
  have hinv : ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ∀ p, Φ (Φ' f) p = f p := by
    intro f hf p
    show Φ (K⁻¹ • Φ (fun q => f (Refl τ Z q))) p = f p
    rw [map_smul, hΦ _ (hR f hf), hΦ _ (test_vector_mem_schwartz_bruhat ψ ν h hψ (hR f hf)), Pi.smul_apply,
      fourier_transform_involution ψ ν h hψ (hR f hf), Refl_Refl h, ← hKdef, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK,
      one_mul]
  have cs : ∀ (s : kˣ) (g : Sp k n → ℂ), g ∈ supportedIn (Set.univ : Set (Sp k n)) →
      (fun q => g (PositivityTheory.RgUd.TP.Nil.hom s q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := fun s g hg => by
    have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hg (homH s)
    exact this
  let 𝓕 : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
    { toFun := fun ξ => ξ ∘ₗ Φ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨𝓕, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ f hf h0
    refine hξ _ (h1 f hf) fun p hp => ?_
    rw [hΦ f hf]
    exact fourier_transform_support ψ ν h f h0 hp
  · intro ξ hξ hi g hg f hf
    have ca : (fun q => f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
      have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hf (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g)
      exact this
    have ca' : (fun q => Φ f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
      have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem (h1 f hf) (PositivityTheory.RgUd.T.Nil.Four.Alg.actH g)
      exact this
    show ξ (Φ fun q => f (act g q)) = ξ (Φ f)
    refine (supp_congr' hξ (h1 _ ca) ca' fun p hp => ?_).trans (hi g hg _ (h1 f hf))
    rw [hΦ _ ca, hΦ f hf]
    exact fourier_transform_equivariant ψ ν h hg f hp.1
  · intro ξ hξ
    constructor
    · intro hk f hf
      exact hk _ (hU f hf)
    · intro hk f hf
      have hf' : f ∈ supportedIn (Set.univ : Set (Sp k n)) := supportedIn_mono (Set.subset_univ _) hf
      rw [← supp_congr' hξ (h1 _ (h1' f hf')) hf' fun p _ => hinv f hf' p]
      exact hk _ (hU' f hf)
  · intro ξ h0 f hf
    exact h0 _ (h1 f hf)
  · intro t ξ hξ f hf
    have hc1 := cs t _ (h1 f hf)
    have hc2 : ((((nabs k t)⁻¹ ^ dB Z : ℝ)) : ℂ) • Φ (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ q)) ∈
        supportedIn (Set.univ : Set (Sp k n)) :=
      (supportedIn Set.univ).smul_mem _ (h1 _ (cs t⁻¹ f hf))
    have e := supp_congr' hξ hc1 hc2 fun p hp => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hΦ f hf, hΦ _ (cs t⁻¹ f hf), fourier_transform_homothety ψ ν h t f hp.1, dd_eq]
    change ξ (fun q => Φ f (PositivityTheory.RgUd.TP.Nil.hom t q)) = _ * ξ (Φ fun q => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ q))
    rw [e, map_smul, smul_eq_mul]
  · intro ξ hξ z hz f hf
    have ct : (fun p : Sp k n => f (p.1 + z, p.2)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
      have := PositivityTheory.RgUd.T.Nil.Four.Alg.comp_mem hf (trH z)
      exact this
    show ξ (Φ fun p => f (p.1 + z, p.2)) = ξ (Φ f)
    refine supp_congr' hξ (h1 _ ct) (h1 f hf) fun p hp => ?_
    obtain ⟨x, v⟩ := p
    obtain ⟨⟨hxB, hxn⟩, -⟩ := hp
    rw [hΦ _ ct, hΦ f hf]
    refine fourier_transform_translation_invariant ψ ν h hZ f hz hxB ?_ v
    exact h.nil _ ⟨mul_mem_Bz Z (PositivityTheory.RgUd.T.Nil.Four.Phi2.Z_le_Bz Z hZ hz) hxB,
      Commute.isNilpotent_mul_left (hxB z hz) hxn⟩

end PositivityTheory.RgUd.TP.Nil.Four
