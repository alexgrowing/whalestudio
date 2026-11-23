import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerRow_of_kodairaSpencerValue_hodgeFil : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (θ : Matrix (Fin n) (Fin n) K) (s : K), (∀ σ k, IsTangent (ub σ k)) → (∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → θ a b = 0) → (∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w, IsLieComb (fun a => s * ∑ b, θ a b * ψ f (hb (e.symm b))) (fun a => ub (e.symm a).1 (e.symm a).2) w → GlobalTheory.DeRham.IsKSValue h f w) → ∀ (τ : E →+* ℂ) (a₀ : Fin (Dw.mult (conjEmb τ))), (∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w) → ∃ w, IsLieComb (fun b => s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)) (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w := by
  first | exact @GlobalTheory.KSRowsFil.isKSRow_of_isKSValue | exact GlobalTheory.KSRowsFil.isKSRow_of_isKSValue | (intros; apply GlobalTheory.KSRowsFil.isKSRow_of_isKSValue <;> assumption)
