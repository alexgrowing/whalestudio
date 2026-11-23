import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
import GroundTheory.GlobalFields.GlobalReciprocity.General

noncomputable section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def stdSpc (n : ℕ) : Spc F E n where
  J := 1
  L := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)
  θ := fun _ => 1
  bas := fun _ => 1

variable (F) in

def skewSpc (δ : E) (𝔞 : Submodule (𝓞 E) E) (d : ℕ) : Spc F E d where
  J := δ • 1
  L := Submodule.pi Set.univ fun _ => 𝔞
  θ := fun _ => 1
  bas := fun _ => 1

structure IsLine (σ : E →ₐ[F] E) (δ : E) (𝔞 : Submodule (𝓞 E) E) : Prop where
  ne : δ ≠ 0
  skew : σ δ = -δ
  lat : 𝔞.IsLattice E
  dual : ∀ y, y ∈ 𝔞 ↔ ∀ x ∈ 𝔞, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * (y * (δ * σ x))))

def IsPos (δ : E) (emb : ∀ w : InfinitePlace F, EmbOver E w) : Prop :=
  ∀ w, ∃ c : ℝ, 0 < c ∧ Complex.I * (emb w).1 δ = c

def GoodField (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : Prop :=
  IsGalois ℚ E ∧ ∀ (v : Pl F) w, Formalism.UG.IsInertAt F E v w →
    (2 : 𝓞 F) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal ∧ ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal

def SpacesEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∃ (δ : E) (𝔞 : Submodule (𝓞 E) E) (emb : ∀ w : InfinitePlace F, EmbOver E w), IsLine σ δ 𝔞 ∧ IsPos δ emb ∧
      ∀ B : Base F E, B.emb = emb → B.P = ∅ →
        (∀ n, (stdSpc F E n).IsHerm σ B n 0) ∧ ∀ d, (skewSpc F δ 𝔞 d).IsSkew σ B d 0

def BaseEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (mα mβ : InfinitePlace F → ℤ),
      ∃ B : Base F E, B.emb = emb ∧ B.mα = mα ∧ B.mβ = mβ ∧ B.P = ∅ ∧ IsStd B.ψ ∧
        (Algebra.Unramified (𝓞 F) (𝓞 E) → GoodField F E → B.IsGood σ)

def SkewLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∃ (B : Base F E) (δ : E) (𝔞 : Submodule (𝓞 E) E), IsLine σ δ 𝔞 ∧ IsPos δ B.emb ∧ B.P = ∅ ∧ IsStd B.ψ ∧
      (GoodField F E → B.IsGood σ) ∧ (∀ n, (stdSpc F E n).IsHerm σ B n 0) ∧ ∀ d, (skewSpc F δ 𝔞 d).IsSkew σ B d 0

theorem skewLine_of (h₁ : SpacesEx) (h₂ : BaseEx) : SkewLine := by
  intro F E _ _ _ _ _ σ hc hu
  obtain ⟨δ, 𝔞, emb, hl, hp, h⟩ := h₁ F E σ hc hu
  obtain ⟨B, e1, -, -, e2, e3, e4⟩ := h₂ F E σ hc emb 0 0
  exact ⟨B, δ, 𝔞, hl, e1 ▸ hp, e2, e3, e4 hu, h B e1 e2⟩

open GroundTheory.Global GroundTheory.Global.IdeleGroup

def ordE (w : HeightOneSpectrum (𝓞 E)) (x : E) : ℤ := FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ x)

def ConjAut : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    IsGalois F E ∧ ∃ s : E ≃ₐ[F] E, (∀ x, s x = σ x) ∧ s ≠ 1 ∧ s * s = 1 ∧ (∀ g : E ≃ₐ[F] E, g = 1 ∨ g = s) ∧
      ∃ δ₀ : E, δ₀ ≠ 0 ∧ σ δ₀ = -δ₀

def IdeleStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ a : IdeleGroup F, ∃ (x : Fˣ) (b : IdeleGroup E),
    ∀ v, ord v a = ord v (diagonal F x) + ord v (ideleNorm F E b)

def OrdEmb : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (a : IdeleGroup F) (w : HeightOneSpectrum (𝓞 E)),
    ord w (ideleEmbedding F E a) = ord (w.under (𝓞 F)) a

def InvFun : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (m : HeightOneSpectrum (𝓞 E) → ℤ), (∀ᶠ w in Filter.cofinite, m w = 0) →
    (∀ (g : E ≃ₐ[F] E) w, m (g • w) = m w) → ∃ a : IdeleGroup F, ∀ w : HeightOneSpectrum (𝓞 E), ord (w.under (𝓞 F)) a = m w

def OrdAut : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (g : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), (∀ x : E, ordE (g • w) (g x) = ordE w x) ∧
    FractionalIdeal.count E (g • w) (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) =
      FractionalIdeal.count E w (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))

def OrdLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∃ (s : E ≃ₐ[F] E) (δ : E) (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x, s x = σ x) ∧ s * s = 1 ∧ δ ≠ 0 ∧ σ δ = -δ ∧ I ≠ 0 ∧
      ∀ w, ordE w δ + FractionalIdeal.count E w I + FractionalIdeal.count E (s • w) I =
        FractionalIdeal.count E w (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))

def MemOrd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E), I ≠ 0 →
    (∀ y : E, y ≠ 0 → (y ∈ I ↔ ∀ w, FractionalIdeal.count E w I ≤ ordE w y)) ∧
    (∀ w, ∃ x ∈ I, x ≠ 0 ∧ ordE w x = FractionalIdeal.count E w I) ∧ (I : Submodule (𝓞 E) E).IsLattice E

def MemDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (z : E), z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
    ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * z))

def LineEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∃ δ 𝔞, IsLine σ δ 𝔞

def PosEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ δ : E, δ ≠ 0 → σ δ = -δ → ∃ emb, IsPos (F := F) δ emb

def StdHerm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ B : Base F E, B.P = ∅ → ∀ n, (stdSpc F E n).IsHerm σ B n 0

def LineSkew : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (δ : E) (𝔞 : Submodule (𝓞 E) E), IsLine σ δ 𝔞 → ∀ B : Base F E, IsPos δ B.emb → B.P = ∅ →
    ∀ d, (skewSpc F δ 𝔞 d).IsSkew σ B d 0

theorem spacesEx_of (h₁ : LineEx) (h₂ : PosEx) (h₃ : StdHerm) (h₄ : LineSkew) : SpacesEx := by
  intro F E _ _ _ _ _ σ hc hu
  obtain ⟨δ, 𝔞, hl⟩ := h₁ F E σ hc hu
  obtain ⟨emb, hp⟩ := h₂ F E σ hc δ hl.ne hl.skew
  exact ⟨δ, 𝔞, emb, hl, hp, fun B e1 e2 => ⟨h₃ F E σ hc B e2, h₄ F E σ δ 𝔞 hl B (e1 ▸ hp) e2⟩⟩

end UpperTheory.Gal.TP.Skew

end
