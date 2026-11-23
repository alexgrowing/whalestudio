import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.AllCoreOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP

open Sub

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

variable (Ω l) in

structure GoodGuard (Q : HeightOneSpectrum (𝓞 E) → Prop) : Prop where
  split : ∀ w, Q w → IsSplitAt w
  dense : ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    Dense {g : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), w ∉ S ∧ Q w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) g⁻¹}

variable (Ω) in

def CoreAtQ (Q : HeightOneSpectrum (𝓞 E) → Prop) (ι : Qbar l ≃+* ℂ) (m : ℕ) : Prop :=
  ∀ U : Submodule ℂ (UA E m → ℂ), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight m, (∀ τ, HasWeightAt U τ (lam τ)) →
    ∃ r : G E Ω →* GL (Fin m) (Qbar l), Continuous r ∧ IsSSRep r ∧
      ∀ w B, Q w → GlobalTheory.Row9.SatU U w B → ∀ c, GlobalTheory.Row9.SphG c ι r w B fun τ => infOfWeight (lam τ)

omit [IsAlgClosure E Ω] in

def WeakQ (Q : HeightOneSpectrum (𝓞 E) → Prop) (ι : Qbar l ≃+* ℂ) {a : ℕ} (U : Submodule ℂ (UA E a → ℂ))
    (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ IsSSRep r ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    Q w → ∀ B, SatU U w B → FrobEig ι r w (algSat a (normV w) B)

variable (Ω) in

def RowQ (Q : HeightOneSpectrum (𝓞 E) → Prop) (ι : Qbar l ≃+* ℂ) (a : ℕ) : Prop :=
  ∀ (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight a, (∀ τ, HasWeightAt U τ (lam τ)) →
    (∃ r : G E Ω →* GL (Fin a) (Qbar l), WeakQ Q ι U r) ∧
    ∀ r : G E Ω →* GL (Fin a) (Qbar l), WeakQ Q ι U r → ∀ w, Q w → ∀ B, SatU U w B →
      Cl ι r w (algSat a (normV w) B) (GlobalTheory.GalDef.jumpsOf ι lam)

variable {Q : HeightOneSpectrum (𝓞 E) → Prop}

theorem frobIdQ (hDI : DenseId) (hCp : CpFacts) (hQ : GoodGuard Ω l Q) (ι : Qbar l ≃+* ℂ) (d t : ℕ)
    (r r' : G E Ω →* GL (Fin d) (Qbar l)) (a a' : Fin t → G E Ω →* (Qbar l)ˣ) (hr : Continuous r) (hr' : Continuous r')
    (ha : ∀ i, Continuous (a i)) (ha' : ∀ j, Continuous (a' j))
    (hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, Q w → ∃ (S : Multiset ℂ) (c c' : Fin t → ℂ),
      FrobEig ι r w (S + Finset.univ.val.map c) ∧ FrobEig ι r' w (S + Finset.univ.val.map c') ∧
      (∀ i, FrobEig ι (rk1 (a i)) w {c i}) ∧ ∀ j, FrobEig ι (rk1 (a' j)) w {c' j}) :
    ∀ g, cp r g * lin a' g = cp r' g * lin a g := by
  have hS := Filter.eventually_cofinite.1 hev
  refine hDI (G E Ω) l d d t t r r' a a' hr hr' ha ha' _
    (hQ.dense _ hS) ?_
  rintro g ⟨w, hw, hsp, hl, A, hA, hF⟩
  obtain ⟨S₀, c, c', h1, h2, h3, h4⟩ := (not_not.1 hw) hsp
  have lin_map : ∀ (b : Fin t → G E Ω →* (Qbar l)ˣ) (e : Fin t → ℂ),
      (∀ i, FrobEig ι (rk1 (b i)) w {e i}) →
      (lin b g).map ι.toRingHom = ∏ i, (X - C (e i)) := by
    intro b e hb
    rw [lin, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h := ((hb i) A hA).2 g⁻¹ hF
    rw [inv_inv] at h
    have h' : cp (rk1 (b i)) g = X - C (b i g : Qbar l) := (hCp (G E Ω) (Qbar l) 0 0).2.1 (b i) g
    rw [← h']
    simpa using h
  have cp_map : ∀ (s : G E Ω →* GL (Fin d) (Qbar l)) (e : Fin t → ℂ),
      FrobEig ι s w (S₀ + Finset.univ.val.map e) →
      (cp s g).map ι.toRingHom = (S₀.map fun z => X - C z).prod * ∏ i, (X - C (e i)) := by
    intro s e hs
    have h := (hs A hA).2 g⁻¹ hF
    rw [inv_inv] at h
    rw [cp, h, Multiset.map_add, Multiset.prod_add, Multiset.map_map]
    rfl
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [Polynomial.map_mul, Polynomial.map_mul, cp_map r c h1, cp_map r' c' h2, lin_map a' c' h4,
    lin_map a c h3]
  ring

theorem weakIsoQ (hA : SatAE) (hQ : GoodGuard Ω l Q) (ι : Qbar l ≃+* ℂ) {a : ℕ} (U : Submodule ℂ (UA E a → ℂ)) (hU : IsAutRepU U)
    (r r' : G E Ω →* GL (Fin a) (Qbar l)) (hr : WeakQ Q ι U r) (hr' : WeakQ Q ι U r') : RepIso r r' := by
  obtain ⟨hc, hs, he⟩ := hr
  obtain ⟨hc', hs', he'⟩ := hr'
  have hev := he.and (he'.and (hA E a U hU))
  refine GlobalTheory.SplitAttUniq.repIso_of_dense r r' hc hc' hs hs' _
    (hQ.dense _ ((Filter.eventually_cofinite.1 hev))) ?_
  rintro g ⟨w, hw, hsp, hl, A, hP, hF⟩
  obtain ⟨h1, h2, h3⟩ := not_not.1 hw
  obtain ⟨B, hB⟩ := h3 (hQ.split w hsp)
  have e1 := ((h1 hsp B hB) A hP).2 g⁻¹ hF
  have e2 := ((h2 hsp B hB) A hP).2 g⁻¹ hF
  rw [inv_inv] at e1 e2
  exact Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)

theorem atPlaceQ (hCE : CharEx) (hSat : SatAE) (hDI : DenseId) (hCp : CpFacts) (hPA : PeelAll) (hCT : ClTw) (hCL : ContLeft)
    (hSS : SSLeft) (hQ : GoodGuard Ω l Q) (ι : Qbar l ≃+* ℂ) (n : ℕ) (hO : ∀ d, Odd d → RowQ Ω Q ι d) (hT : TwoUp E n)
    (U : Submodule ℂ (UA E n → ℂ)) (hU : IsAutRepU U) (lam : (E →+* ℂ) → DomWeight n) (hl : ∀ τ, HasWeightAt U τ (lam τ))
    (w₀ : HeightOneSpectrum (𝓞 E)) (hw₀ : Q w₀) : ∃ r : G E Ω →* GL (Fin n) (Qbar l), WeakQ Q ι U r ∧
      ∀ B, SatU U w₀ B → Cl ι r w₀ (algSat n (normV w₀) B) (GlobalTheory.GalDef.jumpsOf ι lam) := by
  obtain ⟨t, κ, m, U₁, U₂, lam₁, lam₂, ψ₁, ψ₂, p₁, p₂, hodd, hκ, h1, h2, hne, hκ0, hψ0⟩ :=
    hT U hU lam hl w₀ (hQ.split w₀ hw₀)
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
    refine frobIdQ hDI hCp hQ ι (n + t) t r₁ r₂ _ _ hr₁.1 hr₂.1 hc1 hc2 ?_
    filter_upwards [hlw, hunr κ, hu1, hu2, hr₁.2.2, hr₂.2.2, hSat E n U hU] with w hw hk hp1 hp2 hw1 hw2 hsat hs
    obtain ⟨B, hB⟩ := hsat (hQ.split w hs)
    obtain ⟨B₁, hB₁, e₁⟩ := h1.sat w (hQ.split w hs) hk hp1 B hB
    obtain ⟨B₂, hB₂, e₂⟩ := h2.sat w (hQ.split w hs) hk hp2 B hB
    refine ⟨(algSat n (normV w) B).map (· * ((κ.val w : ℂˣ) : ℂ)⁻¹),
      fun i => (((ψ₁ i).val w : ℂˣ) : ℂ), fun j => (((ψ₂ j).val w : ℂˣ) : ℂ), ?_, ?_, ?_, ?_⟩
    · rw [← e₁]; exact hw1 hs B₁ hB₁
    · rw [← e₂]; exact hw2 hs B₂ hB₂
    · exact fun i => ((hL _ _ (h1.alg i)).2 w (hp1 i)).1 hw
    · exact fun j => ((hL _ _ (h2.alg j)).2 w (hp2 j)).1 hw
  obtain ⟨s, hsc, hss, hcl⟩ := hPA E Ω l ι n (n + t) t r₂ _ hr₂.2.1 t r₁ _ hr₁.1 hr₁.2.1 hc1 ha_ne hid
  have key : ∀ w, Q w → κ.UnrAt w → (∀ i, (ψ₁ i).UnrAt w) → ∀ B, SatU U w B →
      Cl ι (tw s (L κ m)) w (algSat n (normV w) B) (GlobalTheory.GalDef.jumpsOf ι lam) := by
    intro w hs hk hp B hB
    obtain ⟨B₁, hB₁, e₁⟩ := h1.sat w (hQ.split w hs) hk hp B hB
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

theorem coreAtQ_iff_rowQ (hS : SatPol) (hA : SatAE) (hC : ClConj) (hQ : GoodGuard Ω l Q) (ι : Qbar l ≃+* ℂ) (m : ℕ) :
    CoreAtQ Ω Q ι m ↔ RowQ Ω Q ι m := by
  constructor
  · intro h U hU lam hl
    obtain ⟨r, hc, hs, hr⟩ := h U hU lam hl
    have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hlw : ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ v.asIdeal :=
      (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
    have hw : WeakQ Q ι U r := ⟨hc, hs, by
      filter_upwards [hlw] with w hwl hq B hB
      exact hr w B hq ⟨hQ.split w hq, hB⟩ .unr hwl⟩
    exact ⟨⟨r, hw⟩, fun r' hr' w hq B hB => hC E Ω l ι m r r' hc (weakIsoQ hA hQ ι U hU r r' hw hr') w _ _
      ((sphG_iff_cl hS ι r w B lam).1 (hr w B hq ⟨hQ.split w hq, hB⟩))⟩
  · intro h U hU lam hl
    obtain ⟨⟨r, hr⟩, h2⟩ := h U hU lam hl
    exact ⟨r, hr.1, hr.2.1, fun w B hq hB => (sphG_iff_cl hS ι r w B lam).2 (h2 r hr w hq B hB.2)⟩

def SubtractQ : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (Q : HeightOneSpectrum (𝓞 E) → Prop), GoodGuard Ω l Q → ∀ n : ℕ,
    (∀ d, Odd d → CoreAtQ Ω Q ι d) → TwoUp E n → CoreAtQ Ω Q ι n

theorem subtractQ_of (hCE : CharEx) (hSat : SatAE) (hDI : DenseId) (hCp : CpFacts) (hPA : PeelAll) (hCT : ClTw) (hCL : ContLeft)
    (hSS : SSLeft) (hS : SatPol) (hC : ClConj) : SubtractQ := by
  intro E Ω _ _ _ _ _ _ l _ ι Q hQ n hO hT
  have hO' : ∀ d, Odd d → RowQ Ω Q ι d := fun d hd => (coreAtQ_iff_rowQ hS hSat hC hQ ι d).1 (hO d hd)
  refine (coreAtQ_iff_rowQ hS hSat hC hQ ι n).2 fun U hU lam hl => ⟨?_, fun r hr w hw B hB => ?_⟩
  · obtain ⟨g, w, -, hw, -⟩ := (hQ.dense ∅ Set.finite_empty).nonempty
    obtain ⟨r, hr, -⟩ := atPlaceQ hCE hSat hDI hCp hPA hCT hCL hSS hQ ι n hO' hT U hU lam hl w hw
    exact ⟨r, hr⟩
  · obtain ⟨s, hs, hc⟩ := atPlaceQ hCE hSat hDI hCp hPA hCT hCL hSS hQ ι n hO' hT U hU lam hl w hw
    exact hC E Ω l ι n s r hs.1 (weakIsoQ hSat hQ ι U hU s r hs hr) w _ _ (hc B hB)

def AllCoreQ : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ), GlobalTheory.Row9.FieldOK l E → InertOK E → ∀ Q : HeightOneSpectrum (𝓞 E) → Prop, GoodGuard Ω l Q →
    (∀ d, Odd d → CoreAtQ Ω Q ι d) → ∀ n : ℕ, 1 ≤ n → CoreAtQ Ω Q ι n

theorem allCoreQ_of (hSub : SubtractQ) (hT : TwoUpOK) : AllCoreQ := by
  intro E Ω _ _ _ _ _ _ l _ ι hF hI Q hQ hO n hn
  rcases Nat.even_or_odd n with he | ho
  · exact hSub E Ω l ι Q hQ n hO (hT E hF.2.2.1 hF.1 hF.2.1 hI n hn he)
  · exact hO n ho

end UpperTheory.Gal.TP

end
