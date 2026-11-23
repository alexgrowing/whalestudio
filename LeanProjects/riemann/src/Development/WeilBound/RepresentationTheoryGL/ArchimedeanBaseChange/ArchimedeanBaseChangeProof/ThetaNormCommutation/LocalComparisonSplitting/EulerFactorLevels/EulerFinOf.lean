import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.Fin

open PositivityTheory.Rg.BcB.G8

def Good {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) : Prop :=
  (∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) ∧
  ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧
    (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0

def DcCount : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K Γ : Subgroup G) (δ : G)
  (f : G → ℂ), IsOpen (K : Set G) → IsCompact (K : Set G) → Good θ K δ → Γ ≤ twCent θ δ →
  (∀ x : G, Finite (Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)) → Finite (Γ ⊓ cptPart (twCent θ δ) : Subgroup G) →
  (Finite (DoubleCoset.Quotient ((Γ.subgroupOf (twCent θ δ) : Subgroup (twCent θ δ)) : Set (twCent θ δ))
    ((cptPart (twCent θ δ)).subgroupOf (twCent θ δ) : Set (twCent θ δ)))) →
  (∀ x, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) →
  {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k)) ≠ 0}.Finite →
    dcSum Γ K (fun x => f (x⁻¹ * δ * θ x)) = mass θ Γ δ * twOrb θ K δ f

def MassProd : Prop := ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G') (δ : G) (δ' : G'),
  mass (θ.prodMap θ') (Γ.prod Γ') (δ, δ') = mass θ Γ δ * mass θ' Γ' δ'

def RestrTw : Prop := ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)]
  [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (θ : G →* G) (θH : ∀ i, H i →* H i)
  (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (δ : G) (f : ∀ i, H i → ℂ),
  (∀ i, Continuous (p i)) → (∀ i x, p i (θ x) = θH i (p i x)) → (∀ x y : G, (∀ i, p i x = p i y) → x = y) →
  (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) →
  (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) →
  (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) →
  (∀ i, IsCompact (KH i : Set (H i))) → (∀ i, IsOpen (KH i : Set (H i))) → (∀ i, Good (θH i) (KH i) (p i δ)) →
  (∀ i (x : H i), (rStab fun k : KH i => f i ((x * k)⁻¹ * p i δ * θH i (x * k))).index ≠ 0) →
  (∀ i, {q : DoubleCoset.Quotient (twCent (θH i) (p i δ) : Set (H i)) (KH i : Set (H i)) |
    ∃ k ∈ KH i, f i ((Quotient.out q * k)⁻¹ * p i δ * θH i (Quotient.out q * k)) ≠ 0}.Finite) →
  (∀ᶠ i in cofinite, p i δ ∈ KH i ∧ f i = (KH i : Set (H i)).indicator 1 ∧
    (∀ g : H i, g⁻¹ * p i δ * θH i g ∈ KH i → ∃ t ∈ twCent (θH i) (p i δ), t⁻¹ * g ∈ KH i) ∧
    cptPart (twCent (θH i) (p i δ)) ≤ KH i) →
  twOrb θ K δ (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, twOrb (θH i) (KH i) (p i δ) (f i)

def SplitConv : Prop := ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H) (K : Subgroup H),
  (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y))

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def UnitAE : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
  ∀ᶠ (w : {w : GlobalTheory.BCT.Pl E // w ∈ S}) in cofinite, ∀ (y : GLw a w.1 × GLw b w.1), y = (locEl a w.1 δ₁, locEl b w.1 δ₂) →
    y ∈ K2 (E := E) a b w.1 ∧ (∀ g : GLw a w.1 × GLw b w.1, g⁻¹ * y * ((thL a w.1).prodMap (thL b w.1)) g ∈ K2 (E := E) a b w.1 →
      ∃ t ∈ twCent ((thL a w.1).prodMap (thL b w.1)) y, t⁻¹ * g ∈ K2 (E := E) a b w.1) ∧
    cptPart (twCent ((thL a w.1).prodMap (thL b w.1)) y) ≤ K2 (E := E) a b w.1

def LocGood : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (w : Pl E)
  (y : GLw a w × GLw b w), (nrmL a w y.1).val.charpoly.Separable → (nrmL b w y.2).val.charpoly.Separable →
  Good ((thL a w).prodMap (thL b w)) (K2 a b w) y

def LocSupp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (w : Pl E)
  (y : GLw a w × GLw b w), (nrmL a w y.1).val.charpoly.Separable → (nrmL b w y.2).val.charpoly.Separable →
  (∀ C : Set (GLw a w × GLw b w), IsCompact C → {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set _)
    (K2 (E := E) a b w : Set (GLw a w × GLw b w)) | ∃ k ∈ K2 (E := E) a b w,
      (Quotient.out q * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (Quotient.out q * k) ∈ C}.Finite) ∧
  ∀ (K' : Subgroup (GLw a w × GLw b w)) (f : GLw a w × GLw b w → ℂ), IsOpen (K' : Set (GLw a w × GLw b w)) → K' ≤ K2 a b w →
    IsHecke K' f → ∀ x, (rStab fun k : K2 (E := E) a b w => f ((x * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * k))).index ≠ 0

def RatFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ)
  (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
  Good (thP E a b) ((Kf E a).prod (Kf E b)) (ratF E a δ₁, ratF E b δ₂) ∧
  (∀ x : Gf E a b, Finite (gam δ₁ δ₂ ⊓ ((Kf E a).prod (Kf E b)).map (MulAut.conj x).toMonoidHom : Subgroup (Gf E a b))) ∧
  Finite (gam δ₁ δ₂ ⊓ cptPart (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂)) : Subgroup (Gf E a b)) ∧
  Finite (DoubleCoset.Quotient
    ((((gam δ₁ δ₂).subgroupOf (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))) : Subgroup (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))) :
      Set (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂)))
    ((((cptPart (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))).subgroupOf (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))) :
      Subgroup (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))) : Set (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂))))

def SuppFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)),
  IsSection S → ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
    {q : DoubleCoset.Quotient (twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Set (Gf E a b))
      (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) |
      ∃ k ∈ (Kf E a).prod (Kf E b), orbFn S φ₁ φ₂ δ₁ δ₂ (Quotient.out q * k) ≠ 0}.Finite ∧
    {q : DoubleCoset.Quotient (gam δ₁ δ₂ : Set (Gf E a b)) (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) |
      ∃ k ∈ (Kf E a).prod (Kf E b), orbFn S φ₁ φ₂ δ₁ δ₂ (Quotient.out q * k) ≠ 0}.Finite

def EulerFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)),
  IsSection S → ∀ (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ), IsTestP φ₁ → IsTestP φ₂ →
  ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), polE δ₁ ∈ Ell E a → polE δ₂ ∈ Ell E b →
    twOrb (thP E a b) ((Kf E a).prod (Kf E b)) (ratF E a δ₁, ratF E b δ₂) (finFn S φ₁ φ₂) =
      ∏ᶠ w ∈ S, twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w)

def FinHalfOf : Prop := DcCount → MassProd → RatFin → SuppFin → EulerFin → KfOC → FinLevel → FinHalf

def EulerFinOf : Prop := RestrTw → SplitConv → UnitAE → LocGood → LocSupp → KfOC → EulerFin

def SuppFinOf : Prop := LocSupp → UnitAE → RatFin → LocGood → SuppFin

end PositivityTheory.Rg.BcB.G8.Fin

end
