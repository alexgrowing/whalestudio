import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.CurveDevissage

theorem interNum_one_nonneg {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k V)) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : N.IsLB)
    (h : ∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra k Γ(Z, ⊤)],
      (∀ r : k, i.appTop (algebraMap k Γ(V, ⊤) r) = algebraMap k Γ(Z, ⊤) r) →
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection k (N.pull i) 1)
    (F : V.Modules) (hF : QCoh.IsFiniteQC F) : 0 ≤ interNum k F ![N] := by
  have := isNoetherian_of_isProjOver hp
  have hL : ∀ i, ((![N] : Fin 1 → LB V) i).IsLB := fun i => by fin_cases i; exact hN
  refine QCoh.devissage V (fun F => 0 ≤ interNum k F ![N])
    (fun F hF => (interNum_eq_zero_of_isZero k hF hL).ge) (fun S hS h₁ h₃ p₁ p₃ => ?_)
    (fun Z hZ _ G hG => ?_) F hF
  · rw [interNum_shortExact hS hL
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)]
    exact add_nonneg p₁ p₃
  · have := isIntegral_red hZ
    letI := algebraΓAlong k (redι Z)
    have hi := appTop_algebraMap_along k (redι Z)
    have hpZ : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
      rw [← comp_strHom hi]
      exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hM := LB.isLB_pull hN (redι Z)
    have e : (fun i => ((![N] : Fin 1 → LB V) i).pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    have e' : (fun _ : Fin 1 => N.pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    rw [interNum_pushforward_of_isClosedImmersion hi G hL, e]
    have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ 1 :=
      (redι Z).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hd
    rcases hdZ.eq_or_lt with h1 | h1
    · rw [VB.interNum_one_eq_genRank_mul k _ hpZ h1 G _ hM]
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      have := h _ (redι Z) hi h1
      rwa [topSelf_def, e'] at this
    · refine (interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom k _) G hpZ ?_
        fun i => by fin_cases i; exact hM).ge
      rw [Fintype.card_fin]
      exact (QCoh.suppDim_le G).trans_lt h1

theorem degOfRank_nonneg : ∀ (p : ℕ) [Fact p.Prime] (V : Scheme.{0}) [Algebra (ZMod p) Γ(V, ⊤)], IsProjOver (strHom (ZMod p) V) → topologicalKrullDim V ≤ 1 → ∀ N : LB V, N.IsLB → (∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) (N.pull i) 1) → 0 ≤ degOfRank (ZMod p) (toMod N) 1 := by
  intro p _ V _ hp hd N hN h
  have := Twist.isFiniteQC_twist (F := structureModule V) hN
  have h1 := interNum_one_nonneg hp hd hN (fun Z i _ _ _ _ hZ => h Z i hZ)
    (twist (structureModule V) N) this
  have h2 := interNum_twist_cons (ZMod p) (structureModule V) (P := ![]) hN isEmptyElim
  have h3 : chi (ZMod p) (twist (structureModule V) N) = chi (ZMod p) (toMod N) :=
    chi_congr _ (Twist.unitTwistIso N)
  have h4 : interNum (ZMod p) (twist (structureModule V) N) ![N] =
    chi (ZMod p) (twist (structureModule V) N) - chi (ZMod p) (structureModule V) :=
    h2.trans (congrArg₂ (· - ·) (interNum_of_isEmpty _ _ _) (interNum_of_isEmpty _ _ _))
  rw [degOfRank]
  push_cast
  linarith

end GlobalTheory.CurveDevissage
