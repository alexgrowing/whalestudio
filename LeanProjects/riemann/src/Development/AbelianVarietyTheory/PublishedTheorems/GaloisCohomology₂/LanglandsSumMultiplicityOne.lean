import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

namespace GlobalTheory.Published

def LanglandsSumMultiplicityOne : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (𝔪 𝔫 : Multiset (Segment k)) (r t : ℕ) (π₁ : IrrRep (GL (Fin r) k)) (π₂ : IrrRep (GL (Fin t) k)),
    IsL 𝔪 π₁.ρ → IsL 𝔫 π₂.ρ →
      (∃ π : IrrRep (GL (Fin (r + t)) k), IsL (𝔪 + 𝔫) π.ρ) ∧
        ∀ π : IrrRep (GL (Fin (r + t)) k), IsL (𝔪 + 𝔫) π.ρ → jhMult π.ρ (prod₂ π₁.ρ π₂.ρ) = 1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  {𝔪 𝔫 : Multiset (Segment k)} {r t : ℕ} {π₁ : IrrRep (GL (Fin r) k)} {π₂ : IrrRep (GL (Fin t) k)}

theorem LanglandsSumMultiplicityOne.isSubquotient (H : LanglandsSumMultiplicityOne) (h₁ : IsL 𝔪 π₁.ρ) (h₂ : IsL 𝔫 π₂.ρ)
    {π : IrrRep (GL (Fin (r + t)) k)} (h : IsL (𝔪 + 𝔫) π.ρ) : IsSubquotient π.ρ (prod₂ π₁.ρ π₂.ρ) :=
  JHMult.jhMult_ne_zero_iff.1 (by rw [(H k 𝔪 𝔫 r t π₁ π₂ h₁ h₂).2 π h]; exact one_ne_zero)

theorem LanglandsSumMultiplicityOne.isL_prod₂ (H : LanglandsSumMultiplicityOne) (h₁ : IsL 𝔪 π₁.ρ) (h₂ : IsL 𝔫 π₂.ρ)
    (hi : (prod₂ π₁.ρ π₂.ρ).IsIrreducible) : IsL (𝔪 + 𝔫) (prod₂ π₁.ρ π₂.ρ) := by
  obtain ⟨π, h⟩ := (H k 𝔪 𝔫 r t π₁ π₂ h₁ h₂).1
  obtain ⟨φ⟩ := (H.isSubquotient h₁ h₂ h).nonempty_equiv π.irr hi
  exact h.of_equiv φ.symm

omit [CharZero k] in

example {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    ∃ (𝔪 𝔫 : Multiset (Segment k)) (π₁ π₂ : IrrRep (GL (Fin 1) k)) (π : IrrRep (GL (Fin (1 + 1)) k)),
      IsL 𝔪 π₁.ρ ∧ IsL 𝔫 π₂.ρ ∧ IsL (𝔪 + 𝔫) π.ρ ∧ π = IrrRep.det (Fin 2) _ (hχ.mul (isSmoothChar_absPow (1 / 2))) :=
  ⟨_, _, _, _, _, (single_spec (IrrGL.isCusp_ofChar χ hχ)).2.2.2,
    (single_spec ((IrrGL.isCusp_ofChar χ hχ).nu 1)).2.2.2, isL_detRep_two hχ, rfl⟩

end GlobalTheory.Published

namespace GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h}

theorem IsRec.segment (H : IsRec h rc) {Δ : Segment (w.adicCompletion E)} {x : IrrGL (w.adicCompletion E)}
    (hx : IsLSeg Δ x.rep) : rc x = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  exact (H.langlands [Δ] x hx.isL).trans (WD.lpSum_zero _)

theorem IsRec.langlandsQuotient (H : IsRec h rc) {𝔪 : Multiset (Segment (w.adicCompletion E))} {s N : ℕ}
    {δ : Fin s → IrrGL (w.adicCompletion E)} (hδ : LFactors 𝔪 δ) (hd : ∑ i, (δ i).1 = N)
    {π : IrrRep (GL (Fin N) (w.adicCompletion E))} (hπ : IsCosocle π.ρ (prodIrr δ hd)) :
    rc (cls π) = sumList (List.ofFn fun i => rc (δ i)) := by
  have h1 : IsL 𝔪 (cls π).rep := IsL.of_equiv ⟨s, δ, hd, hδ, hπ⟩ (equivRep π)
  obtain ⟨Δ, ⟨hm, -⟩, hΔ⟩ := hδ
  simp only [fun i => H.segment (hΔ i)]
  obtain ⟨a, ha, ε, -, H⟩ := H
  rw [H.langlands (List.ofFn Δ) (cls π) (by rwa [← Fin.univ_val_map, hm]), List.map_ofFn]
  rfl

theorem IsRec.prod (H : IsRec h rc) {r t : ℕ} (σ : IrrRep (GL (Fin r) (w.adicCompletion E)))
    (τ : IrrRep (GL (Fin t) (w.adicCompletion E))) (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E)))
    (φ : π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) : rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ)) :=
  let ⟨_, _, _, _, H⟩ := H; H.prod r t σ τ π ⟨φ⟩

theorem IsRec.isSpherical_iff (H : IsRec h rc) (x : IrrGL (w.adicCompletion E)) : IsSpherical x.rep ↔ (rc x).unr :=
  let ⟨_, _, _, _, H⟩ := H; H.sph x

end GlobalTheory.LocLanglands

end
