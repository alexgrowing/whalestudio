import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds

noncomputable section
open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DelEps
variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}

theorem trW_mk {h : IsPlaceOver A v} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (σ : Weil h) :
    trW (WD.mk a) σ = LinearMap.trace ℂ V (a.ρ σ) := by
  obtain ⟨e, he, -⟩ := WD.mk_eq_mk.1 (Classical.choose_spec (Classical.choose_spec (WD.mk a).exists_rep))
  unfold trW
  rw [← LinearMap.trace_conj' _ e]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply, he]

def LocExt.self (h : IsPlaceOver A v) : LocExt h := ⟨K, v, h, isLocalExt_self h⟩

theorem trW_of_induces_self {h : IsPlaceOver A v} {x y : WD h} (H : Induces x y) (σ : Weil h) : trW y σ = trW x σ := by
  obtain ⟨m, n, a, b, j, rfl, rfl, hn, hj, hs⟩ := H
  have hj' : ∀ σ u, j (a.ρ σ u) = b.ρ σ (j u) := fun σ => hj σ σ fun _ => rfl
  have hsurj : Function.Surjective j := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨⟨τ, u⟩, rfl⟩
    exact ⟨_, hj' τ u⟩
  have hmn : n = m := by simpa using hn
  subst hmn
  have hb : Function.Bijective j := ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  rw [trW_mk, trW_mk, ← LinearMap.trace_conj' (a.ρ σ) (LinearEquiv.ofBijective j hb)]
  congr 1
  refine LinearMap.ext fun x => ?_
  obtain ⟨u, rfl⟩ := (LinearEquiv.ofBijective j hb).surjective x
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  exact (hj' σ u).symm

theorem trW_indOf_self {h : IsPlaceOver A v} (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    trW (indOf (LocExt.self h) ξ hξ) σ = trW (WD.lpOfChar h ξ hξ) σ := by
  have hy : ∃ y : WD h, Induces (WD.lpOfChar (LocExt.self h).h' ξ hξ) y := ⟨_, induces_self _⟩
  have e : indOf (LocExt.self h) ξ hξ = hy.choose := dif_pos hy
  exact (congrArg (trW · σ) e).trans (trW_of_induces_self (h := h) hy.choose_spec σ)

end GlobalTheory.DelEps
end
