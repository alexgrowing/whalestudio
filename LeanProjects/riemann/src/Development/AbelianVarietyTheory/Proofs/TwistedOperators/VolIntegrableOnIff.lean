import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBplusNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.VolIdent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vol_nu_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) : ∀ X : Node, X.InRange D.R.m → M.ν X = M'.ν X :=
  fun X hX => GlobalTheory.FunObjModel.isAt_unique (hM.vtx X hX) (hM'.vtx X hX)

theorem vol_setIntegral_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) {X : Node} (hX : X.InRange D.R.m) (f : GA D (G.V X) → ℂ)
    (hf : ∀ γ ∈ GQ (G.V X), ∀ u, f (γ * u) = f u) :
    ∫ u in M.fd X, f u ∂M.ν X = ∫ u in M'.fd X, f u ∂M'.ν X := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  have e := vol_nu_eq M M' hM hM' X hX
  have h1 := (hM.vtx X hX).haar_fund
  have h2 := (hM'.vtx X hX).haar_fund
  rw [← e] at h2 ⊢
  have := h1.1
  exact h1.2.setIntegral_eq h2.2 fun γ g => hf γ γ.2 g

theorem vol_integrableOn_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) {X : Node} (hX : X.InRange D.R.m) (f : GA D (G.V X) → ℂ)
    (hf : ∀ γ ∈ GQ (G.V X), ∀ u, f (γ * u) = f u) :
    IntegrableOn f (M.fd X) (M.ν X) ↔ IntegrableOn f (M'.fd X) (M'.ν X) := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  have e := vol_nu_eq M M' hM hM' X hX
  have h1 := (hM.vtx X hX).haar_fund
  have h2 := (hM'.vtx X hX).haar_fund
  rw [← e] at h2 ⊢
  have := h1.1
  exact h1.2.integrableOn_iff h2.2 fun γ g => hf γ γ.2 g

end GlobalTheory.VolIdent

end
