import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.Desc

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev Comp (σ : Submodule ℂ (UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ

def Descent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
      (∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.under (𝓞 (maximalRealSubfield E)) ∈ S) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ∃ B, (CG.mk π).HasSat w B) →
      ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧
        (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → IsUnramU σ w) ∧
        (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
        ∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)

def IsOne (D : Pre E n) (π : CuspSub E n) : Prop := D.c = 1 ∧ ∀ i, ∃ e : D.N i = n, e ▸ D.V i = π.V

def SplitLike (D : Pre E n) (π : CuspSub E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

def WeakDesc (σ : Submodule ℂ (UA E n → ℂ)) (π : CuspSub E n) : Prop :=
  IsAutRepU σ ∧ (∀ w, ¬ IsSplitAt w → IsUnramU σ w) ∧
    (∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ τ B, Comp σ w τ ∧
      GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w n) ∧ GlobalTheory.LFun.HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B

def RunDesc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    (∃ σ, WeakDesc σ π) ∨ ∃ D : Pre E n, D.Reg ∧ D.ThetaStable ∧ SplitLike D π ∧ ¬ IsOne D π

def OneEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∃ D : Pre E n, IsOne D π ∧ D.Reg ∧ D.ThetaStable

def BCOut : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∃ D : Pre E n, D.Reg ∧ D.ThetaStable ∧ ∀ w, IsSplitAt w → D.SplitAt σ w

theorem bcOut_of_N (h : PositivityTheory.Rg.BcN.BaseChangeIsobaricN) (hW : WeightEx) (hT : Rig.ThetaOfAsc) : BCOut := by
  intro E _ _ _ hE n hn σ hσ
  obtain ⟨c, N, e, V, ρ, m, P, H⟩ := h E hE n hn σ hσ
  let D : Pre E n := ⟨c, N, e, V, ρ, m, H.pos, H.discrete, H.loc, H.inf⟩
  exact ⟨D, fun τ => (hW E n σ hσ τ).imp fun lam h => H.weight τ lam h, hT E n D H.csd,
    fun w hw => ⟨P w, H.sub w, H.split w hw⟩⟩

def OneRead : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (D : Pre E n),
  IsOne D π → (∀ w B, (CG.mk π).HasSat w B ↔ D.Sat w B) ∧ (∀ w, ∃ τ, π.IsLocComp w τ) ∧
    ∀ w τ, π.IsLocComp w τ → ∀ P : SmIrr (GL (Fin n) (w.adicCompletion E)),
      (GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w)) ↔ Nonempty (P.ρ.Equiv τ.ρ))

def OneOnly : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
  (D D' : Pre E n) (e : Fin D.c ≃ Fin D'.c), D.Reg → D'.Reg → IsOne D' π → (∀ i w, D.cls i w = D'.cls (e i) w) → IsOne D π

def SatComp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n)
  (w : HeightOneSpectrum (𝓞 E)) (τ τ' : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
  GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w n) → GlobalTheory.LFun.HasSatGL w τ.ρ B → (CG.mk π).HasSat w B → π.IsLocComp w τ' →
    Nonempty (τ.ρ.Equiv τ'.ρ)

def SphUnram : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n)
  (σ : Submodule ℂ (UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
  IsAutRepU σ → IsSplitAt w → (CG.mk π).HasSat w B → π.IsLocComp w τ → Comp σ w τ → IsUnramU σ w

theorem Comp.congr {σ : Submodule ℂ (UA E n → ℂ)} {w : HeightOneSpectrum (𝓞 E)}
    {τ τ' : SmIrr (GL (Fin n) (w.adicCompletion E))} (h : Comp σ w τ) (he : Nonempty (τ.ρ.Equiv τ'.ρ)) : Comp σ w τ' := by
  obtain ⟨-, f, h0, hf, h2⟩ := h
  obtain ⟨e⟩ := he
  refine ⟨τ'.irred, f ∘ₗ e.symm.toLinearMap, fun h => h0 (LinearMap.ext fun v => ?_), fun v => hf _, fun x v => ?_⟩
  · exact (congrArg f (e.symm_apply_apply v)).symm.trans (LinearMap.congr_fun h (e v))
  · exact (congrArg f (LinearMap.congr_fun (e.symm.isIntertwining' _) v)).trans (h2 x _)

end PositivityTheory.Rg.BcB.Desc

end
