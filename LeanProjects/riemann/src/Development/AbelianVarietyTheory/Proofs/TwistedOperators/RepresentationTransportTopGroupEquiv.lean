import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
namespace GlobalTheory.TransportIso

theorem irreducible_admissible_integralOp_transport : ∀ (G G' : Type) [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (Φ : G ≃ₜ* G') (ν : Measure G) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), (σ.IsIrreducible → Representation.IsIrreducible (σ.comp Φ.symm.toMulEquiv.toMonoidHom)) ∧ (IsAdmissible σ → IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W)) ∧ ∀ (f : G → ℂ) (f' : G' → ℂ), (∀ g, f' (Φ g) = f g) → ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W) f' A ↔ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ f A := by
  intro G G' _ _ _ _ _ _ _ _ Φ ν W _ _ σ
  have hs : ∀ g' : G', Φ.symm.toMulEquiv g' = Φ.symm g' := fun _ => rfl
  have hs2 : ∀ g' : G', Φ.symm.toMulEquiv.toMonoidHom g' = Φ.symm g' := fun _ => rfl
  have hcomp' : ∀ g' : G', (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' = σ (Φ.symm g') := fun _ => rfl
  have hcomp : ∀ g : G, (σ.comp Φ.symm.toMulEquiv.toMonoidHom) (Φ g) = σ g := by
    intro g; rw [hcomp', Φ.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro hσ
    let e : Subrepresentation (σ.comp Φ.symm.toMulEquiv.toMonoidHom) ≃o Subrepresentation σ :=
      { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
          have := U.apply_mem_toSubmodule (Φ g) hv
          rwa [hcomp] at this⟩
        invFun := fun U => ⟨U.toSubmodule, fun g' v hv => by
          rw [hcomp']
          exact U.apply_mem_toSubmodule _ hv⟩
        left_inv := fun U => rfl
        right_inv := fun U => rfl
        map_rel_iff' := Iff.rfl }
    exact e.isSimpleOrder
  · rintro ⟨hsm, hfd⟩
    refine ⟨?_, ?_⟩
    · intro v
      have : {g' : G' | (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v = v} = Φ.symm ⁻¹' {g | σ g v = v} := by
        ext g'; exact Iff.rfl
      rw [this]
      exact (hsm v).preimage Φ.symm.continuous
    · intro K' hK'o hK'c
      let K : Subgroup G := K'.comap Φ.toMulEquiv.toMonoidHom
      have hKo : IsOpen (K : Set G) := hK'o.preimage Φ.continuous
      have hKc : IsCompact (K : Set G) := by
        have : (K : Set G) = Φ.symm '' (K' : Set G') := by
          ext g; constructor
          · intro hg; exact ⟨Φ g, hg, by simp⟩
          · rintro ⟨g', hg', rfl⟩
            show Φ (Φ.symm g') ∈ K'
            simpa using hg'
        rw [this]; exact hK'c.image Φ.symm.continuous
      have heq : GlobalTheory.PRep.fixed (σ.comp Φ.symm.toMulEquiv.toMonoidHom) K' = GlobalTheory.PRep.fixed σ K := by
        ext v
        simp only [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig]
        constructor
        · intro hv h
          have := hv ⟨Φ h, h.2⟩
          simp at this ⊢
          convert this using 3
          exact (Φ.symm_apply_apply _).symm
        · intro hv h
          have := hv ⟨Φ.symm h, show Φ (Φ.symm h) ∈ K' by simpa using h.2⟩
          simp at this ⊢
          convert this using 3
          rfl
      rw [heq]
      exact hfd K hKo hKc
  · intro f f' hf A
    let e : G ≃ᵐ G' := Φ.toHomeomorph.toMeasurableEquiv
    have hmap : ν.map Φ = ν.map e := rfl
    have he : ∀ g, e g = Φ g := fun g => rfl
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp, hmap]
    refine forall_congr' fun v => forall_congr' fun l => ?_
    rw [integrable_map_equiv, integral_map_equiv]
    have hfun : ((fun g' => f' g' * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v)) ∘ e) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    have hfun' : (fun g => f' (e g) * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) (e g) v)) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    rw [hfun, hfun']

end GlobalTheory.TransportIso
