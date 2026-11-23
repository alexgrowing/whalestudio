import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem form_of_rat_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) → (∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c') → ∃ x, ((I.tw l l0 Z).fm u μ).emb (i + 1) x = φ := by
  intro B X I _hOk _hPins l Z l0 Y O Pl Bs _hQp hStd _hBas _hBsLL _hUnf _hJets u μ i hi φ hφ hv
  clear _hBsLL _hUnf _hJets _hBas _hQp _hPins _hOk Bs Pl
  have hlam : lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) = lamT (B.hcW u) (i + 1) := by
    funext τ
    show Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) (i+1)) (((i+1) * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) (i+1)) (-(((i+1 : ℕ) : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : (B.R.t + 1) / 2 = k + 1 := by omega
    have e2 : (i+1) * (B.R.t + 1) / 2 = (i+1) * (k + 1) := by
      rw [show B.R.t + 1 = (k + 1) * 2 by omega, ← mul_assoc, Nat.mul_div_cancel _ two_pos]
    unfold Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
    congr 1
    funext j
    rw [e1, e2, Nat.cast_mul, sub_eq_add_neg]
  obtain ⟨nn, h1, -, h3, h4⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  change ∀ τ r, (lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) τ).natW r = _ at h3
  change ∀ τ, (lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) τ).detShift = _ at h4
  rw [hlam] at h3 h4
  have hnat : (fun τ r => (lamT (B.hcW u) (i + 1) τ).natW r) = extNu (B.R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
    funext τ r
    refine (h3 τ r).trans ?_
    congr 1
    funext τ' r'
    exact h1 τ' r'
  haveI hLL : Infinite B.LL := Infinite.of_injective (fun n : ℕ => (n : B.LL)) (fun a b h => by
    have := congrArg B.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hVV : Formalism.L2.DIV.VV B.LL (lamT (B.hcW u) (i + 1)) = polV (I.rec7 l Z) u (i + 1) := by
    rw [GlobalTheory.PdvKm.VV_eq_WtPol, hnat]; rfl
  have key : ∀ c', ∃ z : Formalism.L2.DIV.VV B.LL (lamT (B.hcW u) (i + 1)),
      evV B.fields.emb 1 (lamT (B.hcW u) (i + 1)) B.embLL z = φ c' := by
    intro c'
    obtain ⟨v', hv'⟩ := hv c'
    obtain ⟨⟨Q, hQ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v'
    refine ⟨⟨Q, hVV ▸ hQ⟩, ?_⟩
    rw [← hv']
    clear hnat h3 h1 hlam hφ hv hv'
    show _ = evP O u μ (i + 1) ⟨Q, hQ⟩
    funext y
    rw [evV_apply]
    show _ = (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(twB (I.rec7 l Z) u μ (i + 1) τ))) *
      GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL Q) ((O u μ).frm (i + 1) y)
    have hde : ∀ τ, ((I.rec7 l Z).chTw u μ).de (i + 1) y τ = (y.1 τ).det := fun τ => by
      rw [(O u μ).frm_de (i + 1) hi y τ, hStd.frm u μ (i + 1) y]
      rfl
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.one_mul, shiftOf, twB, GL3Theta.evFr, hStd.frm u μ (i + 1) y, hde, Pi.one_apply]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact congrArg (fun e : ℤ => (y.1 τ).det ^ e) (h4 τ)
  choose z hz using key
  let o : Frames (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb)) :=
    ⟨fun _ => 1, fun τ => by simp⟩
  have hinv : ∀ c' (g : (I.stp u μ (i + 1)).Stab c'),
      (I.stp u μ (i + 1)).rho B.fields.emb (lamT (B.hcW u) (i + 1)) c'.1 g.1 (z c') = z c' := by
    intro c' g
    apply evV_injective B.fields.emb 1 (lamT (B.hcW u) (i + 1)) B.embLL o
    have e1 := Law.evV_rho (I.stp u μ (i + 1)) B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) c'.1 g.1 (z c')
    have e2 := (hφ c').2 g
    refine e1.trans ?_
    refine (congrArg ((I.stp u μ (i + 1)).tr B.fields.emb B.embLL c'.1 g.1) (hz c')).trans ?_
    exact e2.trans (hz c').symm
  refine ⟨⟨z, hinv⟩, ?_⟩
  funext c'
  exact hz c'

end GlobalTheory.Mem.Col2.TC
