import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.atPlace_holds :
    CharEx → SatAE → FrobId → PeelAll → ClTw → ClAway → ContLeft → SSLeft → AtPlace := by
  intro hCE hSat hFI hPA hCT hCA hCL hSS E Ω _ _ _ _ _ _ l _ ι n hO hT U hU lam hl w₀ hw₀
  obtain ⟨t, κ, m, U₁, U₂, lam₁, lam₂, ψ₁, ψ₂, p₁, p₂, hodd, hκ, h1, h2, hne, hκ0, hψ0⟩ :=
    hT U hU lam hl w₀ hw₀
  obtain ⟨L, hL, hLinj⟩ := hCE E Ω l ι
  have ha_ne : ∀ i j, L (ψ₁ i) (p₁ i) ≠ L (ψ₂ j) (p₂ j) := fun i j h =>
    hne i j (hLinj _ _ _ _ (h1.alg i) (h2.alg j) h)
  obtain ⟨⟨r₁, hr₁⟩, hC₁⟩ := hO (n + t) hodd U₁ h1.aut lam₁ h1.wt
  obtain ⟨⟨r₂, hr₂⟩, -⟩ := hO (n + t) hodd U₂ h2.aut lam₂ h2.wt
  have hc1 : ∀ i, Continuous (L (ψ₁ i) (p₁ i)) := fun i => (hL _ _ (h1.alg i)).1
  have hc2 : ∀ j, Continuous (L (ψ₂ j) (p₂ j)) := fun j => (hL _ _ (h2.alg j)).1
  have hμc : Continuous (L κ m) := (hL _ _ hκ).1
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlw : ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hunr : ∀ χ : HChar E, ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, χ.UnrAt v :=
    fun χ => Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ).1
  have hu1 : ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ i, (ψ₁ i).UnrAt v :=
    Filter.eventually_all.2 fun i => hunr _
  have hu2 : ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ j, (ψ₂ j).UnrAt v :=
    Filter.eventually_all.2 fun j => hunr _
  have hid : ∀ g, cp r₁ g * lin (fun j => L (ψ₂ j) (p₂ j)) g
      = cp r₂ g * lin (fun i => L (ψ₁ i) (p₁ i)) g := by
    refine hFI E Ω l ι (n + t) t r₁ r₂ _ _ hr₁.1 hr₂.1 hc1 hc2 ?_
    filter_upwards [hlw, hunr κ, hu1, hu2, hr₁.2.2, hr₂.2.2, hSat E n U hU] with w hw hk hp1 hp2 hw1 hw2 hsat hs
    obtain ⟨B, hB⟩ := hsat hs
    obtain ⟨B₁, hB₁, e₁⟩ := h1.sat w hs hk hp1 B hB
    obtain ⟨B₂, hB₂, e₂⟩ := h2.sat w hs hk hp2 B hB
    refine ⟨(algSat n (normV w) B).map (· * ((κ.val w : ℂˣ) : ℂ)⁻¹),
      fun i => (((ψ₁ i).val w : ℂˣ) : ℂ), fun j => (((ψ₂ j).val w : ℂˣ) : ℂ), ?_, ?_, ?_, ?_⟩
    · rw [← e₁]; exact hw1 hs B₁ hB₁
    · rw [← e₂]; exact hw2 hs B₂ hB₂
    · exact fun i => ((hL _ _ (h1.alg i)).2 w (hp1 i)).1 hw
    · exact fun j => ((hL _ _ (h2.alg j)).2 w (hp2 j)).1 hw
  obtain ⟨s, hsc, hss, hcl⟩ := hPA E Ω l ι n (n + t) t r₂ _ hr₂.2.1 t r₁ _ hr₁.1 hr₁.2.1 hc1 ha_ne hid
  have key : ∀ w, IsSplitAt w → κ.UnrAt w → (∀ i, (ψ₁ i).UnrAt w) → ∀ B, SatU U w B →
      Cl ι (tw s (L κ m)) w (algSat n (normV w) B) (GlobalTheory.GalDef.jumpsOf ι lam) := by
    intro w hs hk hp B hB
    obtain ⟨B₁, hB₁, e₁⟩ := h1.sat w hs hk hp B hB
    have c1 := hC₁ r₁ hr₁ w hs B₁ hB₁
    rw [e₁] at c1
    have hj : GlobalTheory.GalDef.jumpsOf ι lam₁ = fun τ =>
        (fun τ => (GlobalTheory.GalDef.jumpsOf ι lam τ).map (· + m (ι.toRingHom.comp τ))) τ +
          Finset.univ.val.map fun i => (fun i τ => -p₁ i (ι.toRingHom.comp τ)) i τ := by
      funext τ
      simp only [jumpsOf_eq]
      exact h1.inf _
    rw [hj] at c1
    have c2 := hcl w _ (fun i => (((ψ₁ i).val w : ℂˣ) : ℂ)) _ (fun i τ => -p₁ i (ι.toRingHom.comp τ))
      (fun i => (hL _ _ (h1.alg i)).2 w (hp i)) c1
    have c3 := hCT E Ω l ι n s (L κ m) hsc hμc w _ ((κ.val w : ℂˣ) : ℂ) _
      (fun τ => -m (ι.toRingHom.comp τ)) ((hL _ _ hκ).2 w hk) c2
    have eS : ((algSat n (normV w) B).map (· * ((κ.val w : ℂˣ) : ℂ)⁻¹)).map (· * ((κ.val w : ℂˣ) : ℂ))
        = algSat n (normV w) B := by
      rw [Multiset.map_map]
      simp [Function.comp_def]
    have eJ : (fun τ => ((GlobalTheory.GalDef.jumpsOf ι lam τ).map (· + m (ι.toRingHom.comp τ))).map
        (· + -m (ι.toRingHom.comp τ))) = GlobalTheory.GalDef.jumpsOf ι lam := by
      funext τ
      rw [Multiset.map_map]
      simp [Function.comp_def]
    rw [eS] at c3
    simpa only [eJ] using c3
  refine ⟨tw s (L κ m), ⟨(hCL (G E Ω) (Qbar l) n 0).2.2.1 s _ hsc hμc,
    (hSS (G E Ω) (Qbar l) n 0).2.2 s _ hss, ?_⟩, fun B hB => key w₀ hw₀ hκ0 hψ0 B hB⟩
  filter_upwards [hlw, hunr κ, hu1] with w hw hk hp hs B hB
  exact (key w hs hk hp B hB).1 hw
