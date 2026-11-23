import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.LatticeDataIntegralSpecialisation
import Development.AutomorphicArithmetic.DivisorFrames.LatticeDataGivesCutAndDual
import Development.AutomorphicArithmetic.DivisorFrames.LatticeDataValuationOfDifference
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

theorem UpperTheory.conjugate_embeddings_cut_and_dual :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (σ σ' : 𝓞 E →+* F), (∀ o, σ' o = σ (H.bar o)) → ∃ (M : ℕ) (a : Fin M → Dw.La) (T S : Fin (Dw.p + Dw.q) → Fin M → F), CutAll Dw p σ a T (vDiff E p) ∧ CutAll Dw p σ' a S 0 ∧ ∀ k : F →+* ℂ_[p], DualL Dw (k.comp σ') a (fun j m => k (T j m)) (fun j m => k (S j m)) := by
  intro E _ _ _ H Dw _ p _ F _ _ σ σ' hσ
  obtain ⟨M, a, T, S, h⟩ := UpperTheory.lattice_data_integral_specialisation E H Dw p F σ'
  have key : ∀ k : F →+* ℂ_[p],
      (∃ δ : ℂ_[p], δ ≠ 0 ∧ Real.log ‖δ‖ = -(vDiff E p * Real.log p) ∧
        CutL Dw (k.comp σ) a (fun j m => k (T j m)) δ) ∧
      CutL Dw (k.comp σ') a (fun j m => k (S j m)) 1 ∧
      DualL Dw (k.comp σ') a (fun j m => k (T j m)) (fun j m => k (S j m)) := by
    intro k
    obtain ⟨s, T', S', hs, hT, hS, hL⟩ := h k
    have e1 : (intO ℂ_[p]).subtype.comp s = k.comp σ' := RingHom.ext fun o => hs o
    have e2 : (fun j m => (T' j m : ℂ_[p])) = fun j m => k (T j m) := funext fun j => funext fun m => hT j m
    have e3 : (fun j m => (S' j m : ℂ_[p])) = fun j m => k (S j m) := funext fun j => funext fun m => hS j m
    have hd := UpperTheory.lattice_data_gives_cut_and_dual E H Dw p s M _ a T' S' hL
    have hc := UpperTheory.lattice_data_valuation_of_difference E H Dw p s (k.comp σ) (fun o => by rw [hs, hσ]; rfl) M _ a T' S' hL
    rw [e1, e2, e3] at hd
    rw [e2] at hc
    exact ⟨hc, hd⟩
  refine ⟨M, a, T, S, fun k => (key k).1, fun k => ⟨1, one_ne_zero, by simp, (key k).2.1⟩, fun k => (key k).2.2⟩
