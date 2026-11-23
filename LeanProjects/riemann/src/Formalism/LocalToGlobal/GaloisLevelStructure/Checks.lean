import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke

open Formalism.BasicNotions ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2

theorem AVTied.eigen {D : D7} {M : MtFam D} (A : AVTied D M) (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i)
    (hx : D.naut.ptV i P = some x) (w : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (NumberField.maximalRealSubfield D.host.E)) (hw : SplitOut D.nd i w)
    (hc : IsConjPl D.host w s.w) (hu : Formalism.AUTREP.IsUnif D.host.E s.v ϖ) (k1 : 1 ≤ k) (k2 : k ≤ D.R.nV)
    (y : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (hy : y ∈ D.naut.typeV i P) :
    NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) =
      iotaOC D i ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x) • (M.loc i).real y :=
  (A.ptV i P x).1 hx w k s ϖ hw hc hu k1 k2 y hy

def MtReal.transfer {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (m : MtReal D μ j)
    (φ : D.what₂.Mt μ' j' ≃ₗ[ℂ] D.what₂.Mt μ j) : MtReal D μ' j' where
  wt := m.wt
  J := m.J
  χ := m.χ
  J_open := m.J_open
  real := m.real.comp φ.toLinearMap
  real_inj := m.real_inj.comp φ.injective
  real_range := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, m.real_range]

theorem MtReal.comap_transfer {D : D7} {μ : D.what₂.Tup} {j : ℕ} (m : MtReal D μ j)
    (φ : D.what₂.Mt μ j ≃ₗ[ℂ] D.what₂.Mt μ j) (S : Submodule ℂ (GAf D.host.E D.R.nV → m.wt.W)) :
    S.comap (MtReal.transfer m φ).real = (S.comap m.real).map φ.symm.toLinearMap := by
  ext y
  simp only [MtReal.transfer, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro h
    exact ⟨φ y, h, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    show m.real (φ (φ.symm z)) ∈ S
    rw [LinearEquiv.apply_symm_apply]
    exact hz

namespace NG

open NumberField ReciprocityTheory.Aut Formalism.AUTREP

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' W'' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup W''] [Module ℂ W'']

theorem IsoRep.refl (S : Submodule ℂ (GAf L n → W)) : IsoRep S S :=
  ⟨LinearEquiv.refl ℂ S, fun _ _ _ h => h⟩

theorem IsoRep.trans {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    {S'' : Submodule ℂ (GAf L n → W'')} (h1 : IsoRep S S') (h2 : IsoRep S' S'') : IsoRep S S'' := by
  obtain ⟨T1, e1⟩ := h1
  obtain ⟨T2, e2⟩ := h2
  exact ⟨T1.trans T2, fun h f f' e => e2 h (T1 f) (T1 f') (e1 h f f' e)⟩

theorem IsoRep.symm {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (hS : ∀ h, ∀ f ∈ S, rt L n h f ∈ S) (h1 : IsoRep S S') : IsoRep S' S := by
  obtain ⟨T, e⟩ := h1
  refine ⟨T.symm, fun h g g' hg => ?_⟩
  have key := e h (T.symm g) ⟨rt L n h (T.symm g : GAf L n → W), hS h _ (T.symm g).2⟩ rfl
  rw [LinearEquiv.apply_symm_apply, ← hg] at key
  have : T ⟨rt L n h (T.symm g : GAf L n → W), hS h _ (T.symm g).2⟩ = g' := Subtype.ext key
  rw [← this, LinearEquiv.symm_apply_apply]

theorem AlgWt.Iso.refl (a : AlgWt L n) : a.Iso a := ⟨LinearEquiv.refl ℂ a.W, fun _ _ => rfl⟩

theorem AlgWt.Iso.symm {a b : AlgWt L n} (h : a.Iso b) : b.Iso a := by
  obtain ⟨T, e⟩ := h
  refine ⟨T.symm, fun γ x => ?_⟩
  apply T.injective
  rw [LinearEquiv.apply_symm_apply, e, LinearEquiv.apply_symm_apply]

theorem AlgWt.Iso.trans {a b c : AlgWt L n} (h : a.Iso b) (h' : b.Iso c) : a.Iso c := by
  obtain ⟨T, e⟩ := h
  obtain ⟨T', e'⟩ := h'
  exact ⟨T.trans T', fun γ x => by simp [e, e']⟩

theorem AutRep.iso_equivalence : Equivalence (AutRep.Iso (L := L) (n := n)) where
  refl π := ⟨AlgWt.Iso.refl _, IsoRep.refl _⟩
  symm h := ⟨h.1.symm, h.2.symm (fun k f hf => (by rename_i x _; exact x.irrS.1.stable k f hf))⟩
  trans h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

end NG

end Formalism.L2
