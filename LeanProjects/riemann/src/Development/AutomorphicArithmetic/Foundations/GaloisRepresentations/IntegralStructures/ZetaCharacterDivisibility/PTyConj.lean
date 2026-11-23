import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

private def smIrrComap {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (β : G ≃ₜ* H) (σ : SmIrr G) : SmIrr H :=
  ⟨σ.V, σ.ρ.comp β.symm.toMulEquiv.toMonoidHom, fun v => (σ.smooth v).preimage β.symm.continuous,
    (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv (ρ := σ.ρ.comp β.symm.toMulEquiv.toMonoidHom) (σ := σ.ρ)
      (fun h => β.symm h) β.symm.surjective (LinearEquiv.refl ℂ _) (fun _ _ => rfl)).2 σ.irred⟩

theorem UpperTheory.Gal.Int.Div.tyConj_of :
    LocIso → TyConj := by
  intro hL E _ _ _ l a U w hw hT
  obtain ⟨hU, β, hβ, -, hc⟩ := hL E a w hw
  obtain ⟨m, J, θ, χ, hJo, hJc, hJt, hθ, hχ, hcus, φ, hφU, hφ0, hφ⟩ := hT
  let J' : Subgroup (GL (Fin a) ((cpl w).adicCompletion E)) := J.comap β.toMulEquiv.toMonoidHom
  let r : J' →* J :=
    { toFun := fun g => ⟨β g.1, g.2⟩
      map_one' := Subtype.ext (map_one β)
      map_mul' := fun x y => Subtype.ext (map_mul β _ _) }
  refine ⟨m, J', θ.comp r, χ, ?_, ?_, ?_, ?_, hχ, ?_, φ, hφU, hφ0, ?_⟩
  · exact hJo.preimage β.continuous
  · exact β.toHomeomorph.isCompact_preimage.2 hJc
  · intro x hx k hk hxk
    have h := hJt (β x) hx k hk (by rw [← map_pow, hxk, map_one])
    exact β.injective (h.trans (map_one β).symm)
  · intro t
    obtain ⟨g, rfl⟩ := hθ t
    have hg : β.symm g.1 ∈ J' := by
      show β (β.symm g.1) ∈ J
      rw [β.apply_symm_apply]
      exact g.2
    refine ⟨⟨β.symm g.1, hg⟩, ?_⟩
    show θ (r _) = θ g
    exact congrArg θ (Subtype.ext (β.apply_symm_apply _))
  · intro σ' v hv he
    have hcu : GlobalTheory.SmGL.IsCuspidal (smIrrComap β σ').ρ := by
      refine hcus (smIrrComap β σ') v hv fun g => ?_
      have hg : β.symm g.1 ∈ J' := by
        show β (β.symm g.1) ∈ J
        rw [β.apply_symm_apply]
        exact g.2
      have h := he ⟨β.symm g.1, hg⟩
      have e : r ⟨β.symm g.1, hg⟩ = g := Subtype.ext (β.apply_symm_apply _)
      have e' : (θ.comp r) ⟨β.symm g.1, hg⟩ = θ g := congrArg θ e
      rw [e'] at h
      exact h
    have h3 := hc σ'.V (σ'.ρ.comp β.symm.toMulEquiv.toMonoidHom) hcu
    have e : (σ'.ρ.comp β.symm.toMulEquiv.toMonoidHom).comp β.toMulEquiv.toMonoidHom = σ'.ρ :=
      MonoidHom.ext fun g => congrArg σ'.ρ (β.symm_apply_apply g)
    rwa [e] at h3
  · intro x hx h
    have hx' : x ∈ locU a w := hU ▸ hx
    have hm : cLoc w x ∈ J := by
      rw [← hβ]
      exact h
    rw [hφ x hx' hm]
    have e : r ⟨cLoc (cpl w) x, h⟩ = ⟨cLoc w x, hm⟩ := Subtype.ext (hβ x)
    show _ = ((χ (θ (r ⟨cLoc (cpl w) x, h⟩)) : ℂˣ) : ℂ) • φ
    rw [e]
