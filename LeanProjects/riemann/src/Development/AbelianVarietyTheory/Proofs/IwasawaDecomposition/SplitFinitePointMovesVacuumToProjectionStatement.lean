import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFinitePointMovesVacuumToProjection
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitFinitePoint_moves_vacuum_to_projection : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), S.SigOK → T.SigOK → ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → GlobalTheory.Ker.IdemTwo w → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ (LT : Lt D.host.E T.rank) (L : Lt D.host.E r), IsSelfDualC T LT → SelfD X L → GlobalTheory.Ker.IsAA (latW hr L) LT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ h ∈ GfC S, SuppAt e S h → ∀ x : (AE D)ˣ, IsDetAt e S h x → ∀ Λ ∈ Vset D.host.E S.rank 1, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmtC S h) (stdL D.host.E S.rank) Λ → ∀ v : TF S.rank g, IsVac X bas w (tens (stdL D.host.E S.rank) L) v → ∀ (t : ℂ) (f : WO S T → ℂ), Zak ψ θ hr eT bas idx (frOf hr eT Z) (t • v) f → Zak ψ θ hr eT bas idx (frOf hr eT Z) ((t * (((χT x)⁻¹ : Circle) : ℂ) * ((Real.sqrt (((((Λ ⊓ stdL D.host.E S.rank).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index ^ r : ℕ) : ℝ)) : ℝ) : ℂ)) • projA X bas w (tens Λ L) v) (om (h, 1) f) := by
  first | exact @GlobalTheory.OneMapRef.SplitProj.zak_om_split | exact GlobalTheory.OneMapRef.SplitProj.zak_om_split | (intros; apply GlobalTheory.OneMapRef.SplitProj.zak_om_split <;> assumption)
