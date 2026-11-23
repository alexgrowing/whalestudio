import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatakeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetSupportAtSplitStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigAgree

theorem cls_eq_of_locV_eq (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i)
    (sp : SplitPlace D.host.E) (σ σ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) sp σ) (hσ' : IsLocS (P.H.av.S i Q') sp σ')
    (he : D.naut.locV i Q sp.w = D.naut.locV i Q' sp.w) :
    GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ' := by
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hσ
  have h3' := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q') sp σ' hσ'
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w] at h3
  rw [← P.H.emb i Q', ← D.nbc.embAV_loc i Q' sp.w] at h3'
  rw [he] at h3
  obtain ⟨a, ha, ε, -, hlaws⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 sp.w)
  exact hlaws.bij.1 (h3.symm.trans h3')

end GlobalTheory.EigAgree

theorem GlobalTheory.EigAgree.cast_ne_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a) (hf : f ≠ 0) :
    (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  subst h
  exact hf

theorem GlobalTheory.EigAgree.eig_agree : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) (Q Q' : D.naut.AV i), D.naut.ptV i Q = some x → D.naut.ptV i Q' = some x → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ f₁ f₂ : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f₁ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → (hj ▸ f₂ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q' → f₁ ≠ 0 → f₂ ≠ 0 → ∀ c₁ c₂ : ℂ, (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c₁ • X.fn hμ j f₁ g) → (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c₂ • X.fn hμ j f₂ g) → c₁ = c₂ := by
  intro hAF hL D P X hA h41 h7 htie i hμ j hj x Q Q' hQ hQ' Pp hG hS hPS hPQ d hd f₁ f₂ hf₁ hf₂ h0₁ h0₂ c₁ c₂ e1 e2
  have hsplit : IsSplitPl D.host Pp := GlobalTheory.OffBad.isSplitPl_of_isSplit D Pp hS
  have hloc : D.naut.locV i Q Pp = D.naut.locV i Q' Pp :=
    (((h41 i).2.1 Q Q' (by rw [hQ]; exact Option.some_ne_none x) (hQ.trans hQ'.symm)).2 Pp hPS hPQ).1 hsplit
  obtain ⟨sp, hspw, hJ⟩ := GlobalTheory.OffBad.offbad hAF hL D P X hA h41 h7 htie i Pp hG hS
  subst hspw
  obtain ⟨Ds, hD1, hD2, hD3, hDt⟩ := GlobalTheory.T.split_place_hecke_satake hAF hL D P X hA h41 h7 htie i hμ j hj sp hG hS hJ d hd
  have E1 := hDt f₁ c₁ e1
  have E2 := hDt f₂ c₂ e2
  have m1 : (P.M.loc i).real (hj ▸ f₁) ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have := P.H.av.typeV i Q ▸ hf₁
    exact this
  have m2 : (P.M.loc i).real (hj ▸ f₂) ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q') := by
    have := P.H.av.typeV i Q' ▸ hf₂
    exact this
  have t1 : (P.M.loc i).real (hj ▸ f₁) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ :=
    (P.M.loc i).real_range ▸ LinearMap.mem_range_self _ _
  have t2 : (P.M.loc i).real (hj ▸ f₂) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ :=
    (P.M.loc i).real_range ▸ LinearMap.mem_range_self _ _
  have n1 : (P.M.loc i).real (hj ▸ f₁) ≠ 0 := fun h =>
    GlobalTheory.EigAgree.cast_ne_zero hj f₁ h0₁ ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  have n2 : (P.M.loc i).real (hj ▸ f₂) ≠ 0 := fun h =>
    GlobalTheory.EigAgree.cast_ne_zero hj f₂ h0₂ ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  exact GlobalTheory.T.double_coset_support_at_split hAF hL D P i Q Q' sp hJ Ds hD1 hD2 hD3
    (fun σ σ' h h' => GlobalTheory.EigAgree.cls_eq_of_locV_eq hL D P i Q Q' sp σ σ' h h' hloc) _ m1 t1 n1 _ m2 t2 n2 c₁ c₂ E1 E2
