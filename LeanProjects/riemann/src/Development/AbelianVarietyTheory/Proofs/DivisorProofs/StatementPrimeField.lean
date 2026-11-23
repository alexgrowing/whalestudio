import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberScalesPicMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSurfacePullbackLawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSurfaceFlagCoverExistsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps

namespace GlobalTheory.DegChTwo

theorem hasFlag_isVB {X : Scheme.{0}} {E : X.Modules} {l : List (LB X)} (h : HasFlag E l) :
    IsVB E l.length := by
  induction h with
  | nil h => exact isVB_zero_iff.2 h
  | cons S hS hL e h ih =>
    have h3 : IsVB S.X₃ 1 := (isVB_toMod hL).of_iso e.symm
    simpa using GlobalTheory.T.short_exact_vector_bundles_rank_add _ S _ _ hS ih h3

theorem hasFlag_isLB {X : Scheme.{0}} {E : X.Modules} {l : List (LB X)} (h : HasFlag E l) :
    ∀ L ∈ l, L.IsLB := by
  induction h with
  | nil h => simp
  | cons S hS hL e h ih =>
    intro L hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hL
    · exact ih L hm

variable {k : Type} [Field k] {T : Scheme.{0}} [Algebra k Γ(T, ⊤)] [IsIntegral T]

theorem degCh2_shortExact (hT : IsProjSurface k T) {S : ShortComplex T.Modules} (hS : S.ShortExact)
    {r₁ r₂ r₃ : ℕ} (h₁ : IsVB S.X₁ r₁) (h₂ : IsVB S.X₂ r₂) (h₃ : IsVB S.X₃ r₃) :
    degCh2 k S.X₂ = degCh2 k S.X₁ + degCh2 k S.X₃ := by
  have hD := GlobalTheory.DualExact.shortExact_dual T S r₃ hS h₃
  have c₁ := chi_shortExact (k := k) hS (hT.finiteCoh h₁).1 (hT.finiteCoh h₃).1
  have c₂ := chi_shortExact (k := k) hD (hT.finiteCoh h₃).2.1 (hT.finiteCoh h₁).2.1
  have := h₂.isFiniteQC
  have g := genRank_shortExact hS
  rw [h₁.genRank_eq, h₂.genRank_eq, h₃.genRank_eq] at g
  rw [degCh2_eq h₁, degCh2_eq h₂, degCh2_eq h₃]
  simp only at c₂
  rw [c₁, c₂, g]
  push_cast
  ring

theorem degCh2_of_isZero {E : T.Modules} (h : IsZero E) : degCh2 k E = 0 := by
  have hv : IsVB E 0 := isVB_zero_iff.2 h
  rw [degCh2_eq hv, chi_eq_zero_of_isZero k h, chi_eq_zero_of_isZero k (isVB_zero_iff.1 hv.dual)]
  simp

theorem additiveLaw (hT : IsProjSurface k T) : AdditiveLaw k T :=
  fun _ hS _ _ _ h₁ h₂ h₃ => degCh2_shortExact hT hS h₁ h₂ h₃

theorem flagLaw (hT : IsProjSurface k T) : FlagLaw k T := by
  intro E l h
  induction h with
  | nil h => simp [degCh2_of_isZero h]
  | cons S hS hL e h ih =>
    have h3 : IsVB S.X₃ 1 := (isVB_toMod hL).of_iso e.symm
    rw [List.map_cons, List.sum_cons,
      degCh2_shortExact hT hS (hasFlag_isVB h) (by simpa using GlobalTheory.T.short_exact_vector_bundles_rank_add _ S _ _ hS (hasFlag_isVB h) h3) h3, ih,
      degCh2_congr e, hT.degCh2_toMod hL]
    ring

theorem frobeniusLaw (p : ℕ) [Fact p.Prime] (T : Scheme.{0}) [Algebra (ZMod p) Γ(T, ⊤)]
    [IsIntegral T] (hT : IsProjSurface (ZMod p) T) : FrobeniusLaw (ZMod p) T p := by
  intro E r hE
  obtain ⟨T', _, _, ρ, d, l, hT', hc, hd, hfl⟩ := GlobalTheory.T.projective_surface_flag_cover_exists (ZMod p) T hT E r hE
  have hY : (p : Γ(T', ⊤)) = 0 := natCast_eq_zero T' p (ZMod p)
  have hX : (p : Γ(T, ⊤)) = 0 := natCast_eq_zero T p (ZMod p)
  have e₁ := GlobalTheory.T.projective_surface_pullback_law (ZMod p) T hT T' hT' ρ d hc hd E r hE
  have e₂ := GlobalTheory.T.projective_surface_pullback_law (ZMod p) T hT T' hT' ρ d hc hd _ r (hE.frobPull p hX)
  have φ : (Scheme.Modules.pullback ρ).obj ((frobPull p hX).obj E) ≅
      (frobPull p hY).obj ((Scheme.Modules.pullback ρ).obj E) :=
    (frobPullPullbackIso p hX ρ hY).app E
  have hfl' := GlobalTheory.T.pullback_preserves_line_bundle_flag _ _ (frob T' p hY) _ l hfl
  have f₁ := flagLaw hT' _ l hfl
  have f₂ := flagLaw hT' _ _ hfl'
  have hLB := hasFlag_isLB hfl
  have key : ((l.map fun L => L.pull (frob T' p hY)).map fun L =>
      (interNum (ZMod p) (structureModule T') ![L, L] : ℚ) / 2) =
      l.map fun L => (p : ℚ) ^ 2 * ((interNum (ZMod p) (structureModule T') ![L, L] : ℚ) / 2) := by
    rw [List.map_map]
    refine List.map_congr_left fun L hL => ?_
    have hL' := hLB L hL
    have := GlobalTheory.T.intersection_number_scales_pic_multiple (ZMod p) T' hT' L _ hL' (Semi.LB.isLB_pull hL' _) p
      (cls_pull_frob p hY hL' _)
    simp only [Function.comp_apply]
    rw [this]
    push_cast
    ring
  rw [key, List.sum_map_mul_left, ← f₁, e₁, ← degCh2_congr φ, e₂] at f₂
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.pos.ne'
  apply mul_left_cancel₀ hd0
  linear_combination f₂

theorem statementPrimeField : StatementPrimeField := fun p _ T _ _ hT =>
  ⟨additiveLaw hT, dualLaw _ T, frobeniusLaw p T hT⟩

end GlobalTheory.DegChTwo
