import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePairDatumRationalApproxEqTwisted
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHomStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawBetweenBasePointsMovedPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.ReadLaw

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem transport_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) (κ₀ : TC.GA B (B.R.N i)) (κ₀' : TC.GA B (B.R.N (i + 1))), finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 = κ₀.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 = κ₀'.1 → ∀ (q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)), TC.PtOf (κ₀ * A.kb i α) q.1.1 → TC.PtOf (κ₀' * A.kb (i + 1) γ) q'.1.1 → cosetIn q = cosetIn (A.p0 i α) → cosetIn q' = cosetIn (A.p0 (i + 1) γ) → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → A.xi i hi α γ z' = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) q q' (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) := by
  intro B X I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' κ₀ κ₀' hκ hκ' q q' hq hq' hc hc' z z' v hv hvh hact
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨d, hd, h1⟩ := GlobalTheory.AdForm.CongAtIdem.cong_at_idem ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (rankN (I.rec7 l Z) i hi0) (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hA.idem
  have hd0 := GlobalTheory.Mem.Df.disjoint_vGs_Q I hok l a
  have hQ := GlobalTheory.Mem.Col2.ColIn.Q_subset_SQ I a
  have hb := hA.base i hi0 α
  have hb' := hA.base (i + 1) hi γ
  obtain ⟨M₀, hM₀, h2⟩ := GlobalTheory.AdForm.TwResid.xiAt_transport_tw I l hok u a i hi (A.b0 i α) (A.b0 (i + 1) γ)
    (A.p0 i α) q (A.p0 (i + 1) γ) q' (A.kb i α) κ₀ (A.kb (i + 1) γ) κ₀'
    (hb.1.of_extTo hQ hd0) hb.2 (hb'.1.of_extTo hQ hd0) hb'.2 hq hq' hc hc'
  obtain ⟨z₂, t, ht, hth, hv2⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) A.e _ hA.idem
    (d * M₀) (Nat.mul_pos hd hM₀) v hvh
  have hm : (z' + k • z₂).map (fun r => A.e * incA (I.rec7 l Z) r) =
      z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • z₂.map (fun r => A.e * incA (I.rec7 l Z) r) := by
    have e := map_add (((AddMonoidHom.mulLeft A.e).comp (incA (I.rec7 l Z)).toAddMonoidHom).mapMatrix) z' (k • z₂)
    rw [map_nsmul] at e
    exact e
  have hcong : (z' + k • z₂).map (fun r => A.e * incA (I.rec7 l Z) r) =
      actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + (d * M₀) • (-(k • t)) := by
    rw [hact, hm, hv2, smul_neg, smul_comm (d * M₀) k t, smul_add]
    abel
  have hc2 := h1 κ.1 κ'.1 κ₀ κ₀' hκ hκ' M₀ z (z' + k • z₂) (-(k • t)) (neg_mem (nsmul_mem ht k)) hcong
  have hx := h2 _ _ hc2
  have hw : IsHalf A.e (v - (d * M₀) • t) := fun r s => by
    rw [Matrix.sub_apply, Matrix.smul_apply, mul_sub, mul_smul_comm, hvh r s, hth r s]
  have hz2 : z₂.map (fun r => A.e * incA (I.rec7 l Z) r) = v - (d * M₀) • t := eq_sub_of_add_eq hv2.symm
  have hp := hper (z' + k • z₂) z' (v - (d * M₀) • t) (sub_mem hv (nsmul_mem ht _)) hw (by rw [hm, hz2])
  exact hp.symm.trans (congrArg B.embLL hx)

theorem law_read : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  intro B X I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' hr hr' x y hx hy z z' v hv hvh hact
  obtain ⟨κ₀, hκ₀⟩ := ((hA.U i (Nat.le_of_succ_le hi) α κ.1).1 κ.2).2
  obtain ⟨κ₀', hκ₀'⟩ := ((hA.U (i + 1) hi γ κ'.1).1 κ'.2).2
  obtain ⟨q, q', hq, hq', hc, hc', hlaw⟩ := GlobalTheory.T.finiteDatum_law_between_basePoints_movedPoints I hok hpins l Z u a Ch A hA i hi α γ κ κ' hr hr' x y hx hy κ₀.1 κ₀'.1 hκ₀.symm hκ₀'.symm
  have h2 := transport_base I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' κ₀.1 κ₀'.1 hκ₀.symm hκ₀'.symm q q' hq hq' hc hc' z z' v hv hvh hact
  rw [h2]
  exact hlaw _

end GlobalTheory.AdForm.ReadLaw
