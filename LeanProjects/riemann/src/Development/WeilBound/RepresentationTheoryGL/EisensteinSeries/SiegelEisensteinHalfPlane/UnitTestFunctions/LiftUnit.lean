import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import GroundTheory.GlobalFields.TateThesis.EulerFactors
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace PositivityTheory.RgEis.TF

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev OH (k : Type) [Field k] [NumberField k] : Subring (FiniteAdeleRing (𝓞 k) k) := integralFiniteAdeles (𝓞 k) k

def InM (M : ℕ) (x : FiniteAdeleRing (𝓞 k) k) : Prop := ∃ y ∈ OH k, x = (M : FiniteAdeleRing (𝓞 k) k) * y

def UnitVec (v : ι → InfiniteAdeleRing k) : Prop := ∀ w : InfinitePlace k, ∑ j, ‖v j w‖ ^ 2 = 1

def Prim (v : ι → FiniteAdeleRing (𝓞 k) k) : Prop :=
  (∀ j, v j ∈ OH k) ∧ ∃ c : ι → FiniteAdeleRing (𝓞 k) k, (∀ j, c j ∈ OH k) ∧ ∑ j, c j * v j = 1

def rd (φ : 𝓢(ι → mixedSpace k, ℂ)) (v : ι → InfiniteAdeleRing k) : ℂ := φ fun j => homeomorphMixedSpace k (v j)

def col (i₀ : ι) (κ : GL ι 𝔸[k]) : ι → 𝔸[k] := ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1

def zInf (φ : 𝓢(Unit → mixedSpace k, ℂ)) (ω : HeckeCharacter k) (s : ℂ) : ℂ :=
  ∫ a : (InfiniteAdeleRing k)ˣ, rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
    ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ s ∂infiniteIdeleMeasure k

def zFin (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k) (s : ℂ) : ℂ :=
  ∫ b : (FiniteAdeleRing (𝓞 k) k)ˣ, g (fun _ => (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
    ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ s ∂finiteIdeleMeasure k

def RealBump : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ : ι) (m : ℕ) (δ : ℝ), 0 < δ → ∃ (F : (ι → ℝ) → ℝ) (f : ℝ → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ F (Pi.single i₀ 1) = 1 ∧ f 1 = 1 ∧
    (∀ t, 0 ≤ t → 0 ≤ f t) ∧ (∀ t, f (-t) = (-1) ^ m * f t) ∧
    ∀ v : ι → ℝ, ∑ j, v j ^ 2 = 1 →
      (∀ t : ℝ, F (t • v) = f t * F v) ∧ (F v ≠ 0 → 1 - δ < v i₀ ^ 2) ∧ (0 < v i₀ → 0 ≤ F v)

def CplxBump : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ : ι) (δ : ℝ), 0 < δ → ∃ (F : (ι → ℂ) → ℝ) (f : ℂ → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ F (Pi.single i₀ 1) = 1 ∧
    (∀ t, ‖t‖ = 1 → f t = 1) ∧ (∀ t, 0 ≤ f t) ∧ (∀ v, 0 ≤ F v) ∧
    ∀ v : ι → ℂ, ∑ j, ‖v j‖ ^ 2 = 1 → (∀ t : ℂ, F (t • v) = f t * F v) ∧ (F v ≠ 0 → 1 - δ < ‖v i₀‖ ^ 2)

def SignChar : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ω : HeckeCharacter k), ω * ω = 1 →
    ∃ m : {w : InfinitePlace k // w.IsReal} → ℕ, ∀ a : (InfiniteAdeleRing k)ˣ,
      (ω.toIdele (ofInfinite a) : ℂ) =
        ∏ w, (if 0 < (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w then (1 : ℂ) else (-1) ^ m w)

def ArchFun : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ : ι) (ω : HeckeCharacter k), ω * ω = 1 →
    ∀ δ : ℝ, 0 < δ → ∃ (φ : 𝓢(ι → mixedSpace k, ℂ)) (φ₁ : 𝓢(Unit → mixedSpace k, ℂ)),
      rd φ (Pi.single i₀ 1) = 1 ∧
      (∀ a : (InfiniteAdeleRing k)ˣ, (∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) →
        rd φ₁ (fun _ => (a : InfiniteAdeleRing k)) = ω.toIdele (ofInfinite a)) ∧
      (∀ a : (InfiniteAdeleRing k)ˣ, ∃ r : ℝ, 0 ≤ r ∧
        rd φ₁ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) = r) ∧
      ∀ v : ι → InfiniteAdeleRing k, UnitVec v →
        (∀ t : InfiniteAdeleRing k, rd φ (t • v) = rd φ₁ (fun _ => t) * rd φ v) ∧
        (rd φ v ≠ 0 → ∀ w, 1 - δ < ‖v i₀ w‖ ^ 2) ∧
        ((∀ w, ‖v i₀ w - 1‖ < 1) → ∃ r : ℝ, 0 ≤ r ∧ rd φ v = r)

def CondM : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ω : HeckeCharacter k), ∃ M₀ : ℕ, M₀ ≠ 0 ∧
    ∀ u ∈ finiteIntegralUnits k, InM M₀ ((u : FiniteAdeleRing (𝓞 k) k) - 1) → ω.toIdele (ofFinite u) = 1

def LiftUnit : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (M : ℕ), M ≠ 0 → ∀ a ∈ OH k, ∀ b ∈ OH k, ∀ u ∈ finiteIntegralUnits k,
    InM M (a * b - (u : FiniteAdeleRing (𝓞 k) k)) → ∃ u₁ ∈ finiteIntegralUnits k, InM M (a - (u₁ : FiniteAdeleRing (𝓞 k) k))

def InMTop : Prop :=
  ∀ (k : Type) [Field k] [NumberField k],
    (∀ M : ℕ, M ≠ 0 → IsOpen {x : FiniteAdeleRing (𝓞 k) k | InM M x} ∧ IsClosed {x : FiniteAdeleRing (𝓞 k) k | InM M x}) ∧
    ∀ x : FiniteAdeleRing (𝓞 k) k, (∀ M : ℕ, M ≠ 0 → InM M x) → x = 0

def FinFun : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ω : HeckeCharacter k), ∃ M₀ : ℕ, M₀ ≠ 0 ∧ ∀ M : ℕ, M ≠ 0 → M₀ ∣ M →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ : ι),
    ∃ (g : (ι → FiniteAdeleRing (𝓞 k) k) → ℂ) (g₁ : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ),
      g ∈ GJMatrix.finiteSchwartzBruhatPi k ∧ g₁ ∈ GJMatrix.finiteSchwartzBruhatPi k ∧ g (Pi.single i₀ 1) = 1 ∧
      (∀ u ∈ finiteIntegralUnits k, g₁ (fun _ => (u : FiniteAdeleRing (𝓞 k) k)) = ω.toIdele (ofFinite u)) ∧
      (∀ t, ‖g₁ fun _ => t‖ ≤ 1 ∧ (g₁ (fun _ => t) ≠ 0 → t ∈ OH k)) ∧
      (ω = 1 → ∀ t, ∃ r : ℝ, 0 ≤ r ∧ g₁ (fun _ => t) = r) ∧
      ∀ v, Prim v → (∀ t : FiniteAdeleRing (𝓞 k) k, g (t • v) = g₁ (fun _ => t) * g v) ∧
        (g v ≠ 0 → ∀ j, j ≠ i₀ → InM M (v j)) ∧ (InM M₀ (v i₀ - 1) → g v = 0 ∨ g v = 1)

def ZSplit : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (φ : 𝓢(Unit → mixedSpace k, ℂ)) (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (ω : HeckeCharacter k) (s : ℂ), g ∈ GJMatrix.finiteSchwartzBruhatPi k →
    globalZeta (fun t => GJMatrix.schwartzBruhatTensorPi φ g fun _ => t) ω s = zInf φ ω s * zFin g ω s

def ZInf : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (φ : 𝓢(Unit → mixedSpace k, ℂ)) (ω : HeckeCharacter k),
    (∀ a : (InfiniteAdeleRing k)ˣ, ∃ r : ℝ, 0 ≤ r ∧
      rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) = r) →
    rd φ (fun _ => 1) ≠ 0 → ∀ x : ℝ, 1 < x → zInf φ ω x ≠ 0

def ZFinPos : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ), g ∈ GJMatrix.finiteSchwartzBruhatPi k →
    (∀ t, ∃ r : ℝ, 0 ≤ r ∧ g (fun _ => t) = r) → g (fun _ => 1) ≠ 0 → ∀ x : ℝ, 1 < x → zFin g 1 x ≠ 0

def ZFinLim : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k),
    g ∈ GJMatrix.finiteSchwartzBruhatPi k → (∀ t, ‖g fun _ => t‖ ≤ 1 ∧ (g (fun _ => t) ≠ 0 → t ∈ OH k)) →
    (∀ u ∈ finiteIntegralUnits k, g (fun _ => (u : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite u) : ℂ) = 1) →
    ∀ b : ℝ, ∃ x : ℝ, b < x ∧ zFin g ω x ≠ 0

def ColLaw : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ : ι),
    (∀ κ ∈ (adStd k).kGL ι, UnitVec (fun j => (col i₀ κ j).1) ∧ Prim fun j => (col i₀ κ j).2) ∧
    (Continuous fun κ : GL ι 𝔸[k] => col i₀ κ) ∧ col (k := k) i₀ 1 = Pi.single i₀ 1 ∧
    ∀ p ∈ (adStd k).kGL ι, p ∈ stab 𝔸[k] {i₀} →
      (∀ κ : GL ι 𝔸[k], col i₀ (p * κ) = (((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) • col i₀ κ) ∧
      ∃ (a : (InfiniteAdeleRing k)ˣ) (u : (FiniteAdeleRing (𝓞 k) k)ˣ), bdet {i₀} p = ofInfinite a * ofFinite u ∧
        (∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) ∧ u ∈ finiteIntegralUnits k

def Supp : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ : ι),
    IsCompact ((adStd k).kGL ι : Set (GL ι 𝔸[k])) → ∀ U ∈ 𝓝 (1 : (adStd k).kGL ι), ∀ M₀ : ℕ, M₀ ≠ 0 →
    ∃ (M : ℕ) (δ : ℝ), M ≠ 0 ∧ M₀ ∣ M ∧ 0 < δ ∧ ∀ κ : (adStd k).kGL ι,
      (∀ j, j ≠ i₀ → InM M (col i₀ κ.1 j).2) → (∀ w, 1 - δ < ‖(col i₀ κ.1 i₀).1 w‖ ^ 2) →
      ∃ p : (adStd k).kGL ι, p.1 ∈ stab 𝔸[k] {i₀} ∧ ∃ u ∈ U, κ = p * u

def SphArch : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι],
    ∃ (φ : 𝓢(ι → mixedSpace k, ℂ)) (φ₁ : 𝓢(Unit → mixedSpace k, ℂ)), φ 0 = 1 ∧ rd φ₁ (fun _ => 1) ≠ 0 ∧
      (∀ t : InfiniteAdeleRing k, ∃ r : ℝ, 0 ≤ r ∧ rd φ₁ (fun _ => t) = r) ∧
      ∀ v : ι → InfiniteAdeleRing k, UnitVec v → ∀ t : InfiniteAdeleRing k, rd φ (t • v) = rd φ₁ fun _ => t

end PositivityTheory.RgEis.TF
