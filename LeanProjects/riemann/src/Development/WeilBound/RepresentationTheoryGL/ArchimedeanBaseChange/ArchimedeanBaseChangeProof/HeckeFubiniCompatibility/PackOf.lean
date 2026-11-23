import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH HeckeM heckeAct Repro)
open PositivityTheory.RgBcC.Bridge (along)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

def ValCont : Prop := ∀ (n : ℕ) [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (k : Mat n → (M.V →L[ℂ] M.V))
  (val : Inf n → ℂ) (T : ℝ) (χ : ℕ → Inf n) (χ₀ : Inf n), IsMult μ M k val T →
  (∀ s m, Tendsto (fun j => GlobalTheory.Dec.gelfVal (χ j s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χ₀ s) m))) →
  Tendsto (fun j => val (χ j)) atTop (𝓝 (val χ₀))

def Pack : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b),
  ∃ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ ∧ FiniteDimensional ℂ W₂ ∧
  ∀ (D : Dom E a b) [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
    [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
    (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure] (κ : Type) [Fintype κ]
    (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (g : ℝ → ℝ)
    (ka' : Bool → ℕ → Kers Ma) (kb' : Bool → ℕ → Kers Mb) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (M : ℕ) (f : Io Ma Mb κ → H E a b → ℂ) (c : ℂ)
    (ca cb : InfinitePlace E → Bool → ℕ → ℂ), Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
    IsBump g T → (∀ v, IsKer μa (Ma v) [] g (ka v)) → (∀ v, IsKer μb (Mb v) [] g (kb v)) →
    (∀ s m v, IsKer μa (Ma v) [(s, m)] g (ka' s m v)) → (∀ s m v, IsKer μb (Mb v) [(s, m)] g (kb' s m v)) →
    IsOpen (K₁ : Set (GL (Fin a) (Af E))) → IsOpen (K₂ : Set (GL (Fin b) (Af E))) →
    (∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, ψ x y ((u₁, u₂) * h) = ψ x y h) →
    (∀ i, Continuous (f i)) → f ≠ 0 → LeftInv f → WL2 D M f → c ≠ 0 →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update ka v (ka' s m v)) kb ψ) f = ca v s m • f) →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens ka (Function.update kb v (kb' s m v)) ψ) f = cb v s m • f) →
    ∃ (χa : InfinitePlace E → Inf a) (χb : InfinitePlace E → Inf b),
      (∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m = ca v s m / c) ∧ (∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m = cb v s m / c) ∧
      EigAll χa χb f ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) ∧
      (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ (∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) ∧
      (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
      ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ)

theorem pack_of (h1 : TensTest) (h2 : TypeOf) (h3 : SmoothOf) (h4 : GrowthOf) (h5 : GelOf) (h6 : InfEx) (h7 : AutOf) :
    Pack := by
  intro E _ _ _ a b Ma Mb
  obtain ⟨W₁, W₂, f₁, f₂, hW⟩ := h2 E a b Ma Mb
  refine ⟨W₁, W₂, f₁, f₂, ?_⟩
  intro D _ _ _ _ _ _ μa _ μb _ ν _ κ _ ka kb va vb T ψ g ka' kb' K₁ K₂ M f c ca cb hC hka hkb hψ hg k0a k0b k1a k1b
    o₁ o₂ hlev hf hf0 hL hW2 hc he hea heb
  have hR : Repr D ka kb ψ f := ⟨hf, c, hc, he⟩
  have hty := hW D μa μb κ ka kb va vb T ψ K₁ K₂ f hka hkb hψ hlev hR
  obtain ⟨s₁, s₂⟩ := h3 E a b μa μb Ma Mb κ D ka kb va vb T ψ (K₁.prod K₂) f hka hkb hψ (o₁.prod o₂)
    (fun x y u hu h => hlev x y u.1 hu.1 u.2 hu.2 h) hR
  obtain ⟨C, N, hG⟩ := h4 E a b D _ _ M f c (h1 E a b μa μb Ma Mb κ ka kb va vb T ψ hka hkb hψ).1 hf hL hW2 hc he
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hf0
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hi₀
  have ga := fun v s m => (h5 E a b D μa μb ν Ma Mb κ ka kb va vb T ψ f c (ca v s m) v g s m hC hka hkb hψ hg ⟨s₁, s₂⟩ hf hc he).1
    _ (k0a v) (k1a s m v) (hea v s m)
  have gb := fun v s m => (h5 E a b D μa μb ν Ma Mb κ ka kb va vb T ψ f c (cb v s m) v g s m hC hka hkb hψ hg ⟨s₁, s₂⟩ hf hc he).2
    _ (k0b v) (k1b s m v) (heb v s m)
  have ea : ∀ v, ∃ χ : Inf a, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = ca v s m / c := fun v => by
    obtain ⟨φ, hφ⟩ := s₁ i₀ x₀.2
    refine h6 E a {φ} v (fun s m => ca v s m / c) ⟨φ, rfl, fun e => hx₀ ?_⟩ ?_
    · have := congrFun hφ x₀.1
      rw [e] at this
      exact this.symm
    · rintro _ rfl y s m x hx
      rw [hφ]
      exact ga v s m i₀ y x₀.2 x hx
  have eb : ∀ v, ∃ χ : Inf b, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = cb v s m / c := fun v => by
    obtain ⟨φ, hφ⟩ := s₂ i₀ x₀.1
    refine h6 E b {φ} v (fun s m => cb v s m / c) ⟨φ, rfl, fun e => hx₀ ?_⟩ ?_
    · have := congrFun hφ x₀.2
      rw [e] at this
      exact this.symm
    · rintro _ rfl y s m x hx
      rw [hφ]
      exact gb v s m i₀ y x₀.1 x hx
  choose χa hχa using ea
  choose χb hχb using eb
  have hE : EigAll χa χb f :=
    ⟨fun i v y m₂ s m x hx => by rw [hχa]; exact ga v s m i y m₂ x hx,
      fun i v y m₁ s m x hx => by rw [hχb]; exact gb v s m i y m₁ x hx⟩
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h7 E a b _ f K₁ K₂ W₁ W₂ χa χb C N o₁ o₂ f₁ f₂ hL hty hG hE
  exact ⟨χa, χb, hχa, hχb, hE, hty, s₁, s₂, a₁, a₂, a₃, a₄⟩

end PositivityTheory.Rg.BcB.CG

end
