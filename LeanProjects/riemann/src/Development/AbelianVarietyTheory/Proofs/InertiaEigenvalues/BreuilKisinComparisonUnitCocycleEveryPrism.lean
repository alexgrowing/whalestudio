import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinCoproductUnitCocycleIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopesAdicTopologicalBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.StratCocycle

variable {l : ℕ} {R : Type} [CommRing R]

theorem comp_assoc {P P' P'' P''' : Obj l R} (h : Hom P'' P''') (g : Hom P' P'') (f : Hom P P') :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext' rfl

theorem comp_id {P P' : Obj l R} (f : Hom P P') : f.comp (Hom.id P) = f := Hom.ext' rfl

theorem map_comp {P P' P'' : Obj l R} {d : ℕ} (ε : Matrix (Fin d) (Fin d) P.A) (g : Hom P' P'') (f : Hom P P') :
    ε.map (g.comp f).f = (ε.map f.f).map g.f := by
  rw [Matrix.map_map]; rfl

theorem unit_of_codiag {P Q B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (h1 : ∀ Δ : Hom Q P, Δ.comp inl = Δ.comp inr → ε.map Δ.f = 1)
    (k : Hom Q B) (hk : k.comp inl = k.comp inr) : ε.map k.f = 1 := by
  obtain ⟨Δ, ⟨hΔl, hΔr⟩, -⟩ := univ P (Hom.id _) (Hom.id _)
  have hk' : k = (k.comp inl).comp Δ := by
    refine (univ B (k.comp inl) (k.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔl).trans (comp_id _))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔr).trans ((comp_id _).trans hk))
  calc ε.map k.f = ε.map ((k.comp inl).comp Δ).f := congrArg (fun k : Hom Q B => ε.map k.f) hk'
    _ = (ε.map Δ.f).map (k.comp inl).f := map_comp ε _ Δ
    _ = (1 : Matrix (Fin d) (Fin d) P.A).map (k.comp inl).f :=
        congrArg (fun M : Matrix (Fin d) (Fin d) P.A => M.map (k.comp inl).f) (h1 Δ (hΔl.trans hΔr.symm))
    _ = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem cocycle_of_triple {P Q Q₂ B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (i₁ : Hom Q Q₂) (j : Hom P Q₂)
    (univ₂ : ∀ (C : Obj l R) (f : Hom Q C) (g : Hom P C), ∃! h : Hom Q₂ C, h.comp i₁ = f ∧ h.comp j = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (hc : ∀ k₂₃ k₁₃ : Hom Q Q₂, i₁.comp inr = k₂₃.comp inl → i₁.comp inl = k₁₃.comp inl →
      k₂₃.comp inr = k₁₃.comp inr → ε.map i₁.f * ε.map k₂₃.f = ε.map k₁₃.f)
    (k₁ k₂ k₃ : Hom Q B) (h12 : k₁.comp inr = k₂.comp inl) (h13 : k₁.comp inl = k₃.comp inl)
    (h23 : k₂.comp inr = k₃.comp inr) : ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  obtain ⟨k₂₃, ⟨h₂₃l, h₂₃r⟩, -⟩ := univ Q₂ (i₁.comp inr) j
  obtain ⟨k₁₃, ⟨h₁₃l, h₁₃r⟩, -⟩ := univ Q₂ (i₁.comp inl) j
  have hc' := hc k₂₃ k₁₃ h₂₃l.symm h₁₃l.symm (h₂₃r.trans h₁₃r.symm)
  obtain ⟨m, ⟨hml, hmr⟩, -⟩ := univ₂ B k₁ (k₂.comp inr)
  have e₂ : k₂ = m.comp k₂₃ := by
    refine (univ B (k₂.comp inl) (k₂.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inr) hml).trans h12)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃r).trans hmr)
  have e₃ : k₃ = m.comp k₁₃ := by
    refine (univ B (k₃.comp inl) (k₃.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inl) hml).trans h13)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃r).trans (hmr.trans h23))
  subst e₂ e₃ hml
  rw [map_comp ε m i₁, map_comp ε m k₂₃, map_comp ε m k₁₃, ← Matrix.map_mul, hc']

theorem unit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A),
    ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) →
    ∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧
      ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl →
        k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  intro l _ K bk d ρ τ s ht En ε hrel B
  have cocB := GlobalTheory.T.breuilKisinCoproduct_unit_cocycle_identities l K bk d ρ τ s ht En ε hrel
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  refine ⟨unit_of_codiag En.inl En.inr En.univ ε
    (fun Δ h => (cocB bk.prism (Hom.id _) Unit (TopBasis.self bk.J)).1 Δ h), fun k₁ k₂ k₃ h12 h13 h23 => ?_⟩
  exact (GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk En.Q _ _ (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk En.Q En.inl)).elim fun En₂ =>
    (GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis l K bk En En₂).2.elim fun ι htb => htb.elim fun tb =>
      cocycle_of_triple En.inl En.inr En.univ En₂.inl En₂.inr En₂.univ ε
        (fun k₂₃ k₁₃ a b c => (cocB En₂.Q (En₂.inl.comp En.inl) ι tb).2 En₂.inl k₂₃ k₁₃ a b c)
        k₁ k₂ k₃ h12 h13 h23

end GlobalTheory.BSP.StratCocycle
