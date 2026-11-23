import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.SharpRestriction.ParConsts

noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.SelectionLemmas

open Formalism.MainNotions.G

variable {p : ℕ} {O : Type} [CommRing O]

def esymmOn {ι : Type} (VV : Finset ι) (κ : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ B ∈ VV.powersetCard k, ∏ v ∈ B, κ v

def monoN (G : GAtP p) (VV B : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ) (x : G.Fn) : G.Fn :=
  ((p : G.O) ^ (∑ v ∈ VV \ B, Sv v)) •
    ((B.sort (· ≤ ·)).foldr (fun v f => (G.yv v)^[m] ∘ f) id) x

def prodIdeal (G : GAtP p) (VV : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ)
    (M : Submodule G.O G.Fn) : Submodule G.O G.Fn :=
  Submodule.span G.O (⋃ B ∈ VV.powerset, monoN G VV B m Sv '' (M : Set G.Fn))

def tau {ι : Type} (VV : Finset ι) (m D : ℕ) (t : ι → ℕ) : ℕ := ∑ v ∈ VV, m * (t v + D + 1)

def IsSaturatedIn {X : Type} [AddCommGroup X] [Module O X] (M' M : Submodule O X) : Prop :=
  M' ≤ M ∧ ∀ (a : O) (x : X), x ∈ M → a ≠ 0 → a • x ∈ M' → x ∈ M'

def adm1 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := G.TrivStab

def adm2 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := G.FinClasses

def adm3 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop :=
  ∀ (u v : Fin G.P.nV) (F : G.Fn), G.yv u (G.yv v F) = G.yv v (G.yv u F)

def admitted (D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := adm1 D G ∧ adm2 D G ∧ adm3 D G

def Conclusion1 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop :=
  ∀ (VV : Finset (Fin G.P.nV)) (t Sv : Fin G.P.nV → ℕ) (Dd cStar S m : ℕ) (κ : Fin G.P.nV → ℝ),
    1 ≤ m → (∀ v ∈ VV, Sv v ≤ S) →
    (∀ v ∈ VV, LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r
      (G.P.lam0 v) (t v) Dd (κ v) cStar) →
    let M := G.Mna
    let d : ℕ := G.dna
    let N := prodIdeal G VV m Sv M
    let τ : ℕ := tau VV m Dd t
    ((∀ β : ℕ, Formalism.G0.AllButLE (p : G.O) M N
        ⌊(d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ (τ + β * S)) ∧
      Formalism.G0.AllButLE (p : G.O) M N 0 (∑ v ∈ VV, Sv v)) ∧
    ((m : ℝ) * ∑ v ∈ VV, κ v ≤ 1 / 2 →
      let Sig : ℝ := (m : ℝ) * ∑ v ∈ VV, κ v
      let Nst := N ⊓ (Ideal.span {(p : G.O) ^ τ}) • M
      (∀ β : ℕ, (d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1) ≤
          (d : ℝ) * Sig ^ (β + 1) / ((β + 1).factorial : ℝ)) ∧
      (∃ ℓ : ℕ, Module.length G.O (↥M ⧸ Submodule.comap M.subtype Nst) = ℓ ∧
        (ℓ : ℝ) ≤ ((Module.length G.O (G.O ⧸ Ideal.span {(p : G.O)})).toNat : ℝ) *
          ((d : ℝ) * τ + 2 * S * Sig * d)) ∧
      ∀ (M' : Submodule G.O G.Fn) (hM' : IsSaturatedIn M' M),
        Nst ⊓ M' ≤ (Ideal.span {(p : G.O) ^ τ}) • M' ∧
        Function.Injective (Submodule.mapQ (Submodule.comap M'.subtype Nst) (Submodule.comap M.subtype Nst)
          (Submodule.inclusion hM'.1) (fun _ hx => hx)) ∧
        ∀ (Y : Type) [AddCommGroup Y] [Module G.O Y] (K : G.Fn →ₗ[G.O] Y) (Z : Submodule G.O Y),
          N.map K ≤ Z → (Nst ⊓ M').map K ≤ Z)

def IntegralityFromMetric (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : Formalism.BasicNotions.GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    admitted D (D.gat u w h) → Conclusion1 D (D.gat u w h)

def RationalPlaneProblemLocal (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (G : GAtP p), admitted D G → Conclusion1 D G

def FamilyGlobalDerivation {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), IntegralityFromMetric (Fm.D x i)

end Formalism.MainNotions.SelectionLemmas
