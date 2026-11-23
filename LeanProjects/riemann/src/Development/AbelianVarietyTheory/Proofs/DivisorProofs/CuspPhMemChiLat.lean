import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankEigenspaceLe
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LevDesc

theorem cuspPh_mem_chiLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E) (hG : Even G.2) (hW : Even W.2) (hK : KeepsCusp U (G + W)) (hKW : KeepsCusp U W), (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U (G + W)), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U (G + W) → g ∈ latW U (G + W)) → (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U W), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U W → g ∈ latW U W) → ∀ (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W), u ∈ latW U W → ∀ f : cuspW Xo c U G, f ∈ latW U G → ∀ h : S, GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h ∈ GlobalTheory.LevDesc.chiLat S U (G + W) χ := by
  intro E _ _ _ H Dw l Xo c r U S hpq hA G W hG hW hK hKW hGW hWW χ u hu f hf h
  rw [GlobalTheory.LevDesc.mem_chiLat]
  refine ⟨?_, fun g => ?_⟩
  · have hint : ∀ g : S, IsIntegral ℤ ((((χ g)⁻¹ : (c.F)ˣ) : c.F)) := fun g => by
      refine IsIntegral.of_pow (Fintype.card_pos (α := S)) ?_
      rw [← Units.val_pow_eq_pow_val, ← map_inv, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
      exact isIntegral_one
    have hmem : ∀ g : S, pull Xo c g ((f : Rul Xo c) * pull Xo c h u) ∈ cuspW Xo c U (G + W) := fun g =>
      hK _ _ (GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW _ _ u.2))
    have hlat : ∀ g : S, (⟨_, hmem g⟩ : cuspW Xo c U (G + W)) ∈ latW U (G + W) := fun g => by
      have hu' : (⟨pull Xo c h u, hKW _ _ u.2⟩ : cuspW Xo c U W) ∈ latW U W := hWW h u _ rfl hu
      have hm : (f : Rul Xo c) * pull Xo c h u ∈ cuspW Xo c U (G + W) := GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW _ _ u.2)
      exact hGW g ⟨_, hm⟩ _ rfl (GlobalTheory.AllWt.mul_mem_supLat hf hu' hm)
    have he : GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h =
        ∑ g : S, (⟨_, hint g⟩ : 𝓞 c.F) • (⟨_, hmem g⟩ : cuspW Xo c U (G + W)) := by
      apply Subtype.ext
      rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply, GlobalTheory.LevDesc.levTr_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Submodule.coe_smul_of_tower, ← algebraMap_smul (c.F)]
      rfl
    rw [he]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hlat g)
  · rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply]
    exact (GlobalTheory.LevDesc.mem_levEigen.1 (GlobalTheory.LevDesc.levTr_mem_levEigen hpq hA χ _)) g

end GlobalTheory.LevDesc
