import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

open ReciprocityTheory.ChartRestriction.G.Chart (isTan_iff) in

theorem detGen_apply_ne_zero_of_isDiff : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetGen) (v : Fin (Module.finrank ℚ F) → X.Lie)
    (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
    (∀ j, u.IsDiff (W j) (v j).hom) → W.det ≠ 0 → δ.1 v ≠ 0 := by
  intro F _ _ 𝔠 X L u δ v W hW hdet
  obtain ⟨h1, h2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  have hsm : Smooth X.A.hom := by
    haveI := X.dim
    exact SmoothOfRelativeDimension.smooth (Module.finrank ℚ F) X.A.hom
  obtain ⟨v₀, hv₀, -⟩ := GlobalTheory.exists_lieBasis_of_holUnif X.A L _ u hsm h1 h2
  let b := Serre.Lie.basis X.rm hv₀
  have hsmul : ∀ (c : ℂ) (w : Fin (Module.finrank ℚ F) → ℂ) (x : X.Lie), u.IsDiff w x.hom →
      u.IsDiff (c • w) (c • x).hom := by
    intro c w x h
    have := GlobalTheory.UnifLieBasis.isDiff_smul u ((isTan_iff _).2 x.isTangent) h c
    convert this using 1
    rfl
  have hsum : ∀ a : Fin (Module.finrank ℚ F) → ℂ, u.IsDiff (∑ j, a j • W j) (∑ j, a j • v j).hom := by
    intro a
    rw [Serre.Lie.hom_sum, ← List.prod_ofFn]
    exact (GlobalTheory.UnifLieBasis.isDiff_list_prod u _ _ (fun j ↦ (isTan_iff _).2 (a j • v j).isTangent)
      (fun j ↦ hsmul _ _ _ (hW j))).2
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 := hsum a
    rw [ha] at h0
    have hz : u.IsDiff 0 (0 : X.Lie).hom := by
      rw [Serre.Lie.hom_zero]
      exact GlobalTheory.UnifLieBasis.isDiff_zero u
    have heq : ∑ j, a j • W j = 0 := (h1 _ (0 : X.Lie).isTangent).unique h0 hz
    rw [← Matrix.vecMul_eq_sum] at heq
    by_contra hne
    push_neg at hne
    obtain ⟨i, hi⟩ := hne
    exact hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨a, fun h ↦ hi (by rw [h]; rfl), heq⟩)
  haveI : Nonempty (Fin (Module.finrank ℚ F)) := Fin.pos_iff_nonempty.1 Module.finrank_pos
  let B := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b, Fintype.card_fin])
  have hB : (B : Fin (Module.finrank ℚ F) → X.Lie) = v := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hmem : B.det ∈ Submodule.span ℂ {δ.1} := by rw [δ.2]; exact Submodule.mem_top
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hmem
  intro h0
  have h1' := B.det_self
  rw [← ht, hB, AlternatingMap.smul_apply, h0, smul_zero] at h1'
  exact zero_ne_one h1'

end GlobalTheory.LatJet
