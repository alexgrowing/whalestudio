import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.ConjFull

open GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem conjMap_mem_mult (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    {J : Set (GA D V)} {χ χ' : GA D V → ℂ} (hχ : ∀ k ∈ J, χ' k = star (χ k)) {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    conjMap M M' c h T ∈ Mult θ M' J χ' := by
  obtain ⟨T', hT', e1⟩ := (GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc).2 J χ T hT
  have : conjMap M M' c h T = T' := by
    refine MultilinearMap.ext fun v' => funext fun g => ?_
    rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
    rfl
  rw [this]
  exact mult_congr θ M' hχ hT'

theorem heckeLin_star (R : Finset (GA D V)) (φ : GA D V → ℂ) : heckeLin V R (star φ) = star (heckeLin V R φ) := by
  funext g
  show ∑ γ ∈ R, star (φ (g * γ)) = star (∑ γ ∈ R, φ (g * γ))
  rw [star_sum]

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J J0 : Set (GA D V)) (χ χ' χ0 : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a a' : Pl D.host.E → List ℤ → ℂ)
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (hχ0 : ∀ k ∈ J0, χ0 k = star (χ0 k))
    (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) (ha : ∀ P d, a' P d = star (a P d)) :
    Module.rank ℂ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) ≤
      Module.rank ℂ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) := by
  have h := (GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc).1
  have key : ∀ T ∈ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)),
      conjMap M M' c h T ∈ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨conjMap_mem_mult θ M M' c hc h hχ h1, ?_⟩, ?_⟩
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
    · obtain ⟨h4, h5⟩ := (mem_partFull θ M J0 χ0 SF a T).1 h3
      refine (mem_partFull θ M' J0 χ0 SF a' _).2 ⟨conjMap_mem_mult θ M M' c hc h hχ0 h4, fun P d R hR v' => ?_⟩
      rw [conjMap_apply, heckeLin_star, h5 P d R hR, star_smul, ha]
  let j : (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) →+
      (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank_full : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J J0 : Set (GA D V)) (χ χ' χ0 : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ), (∀ k ∈ J, χ' k = star (χ k)) → (∀ k ∈ J0, χ0 k = star (χ0 k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF (fun P d => star (a P d)) : Submodule ℂ (MMap M')) := by
  intro D V S S' θ M M' c hc J J0 χ χ' χ0 e e' SF a hχ hχ0 he
  refine le_antisymm (rank_le θ M M' c hc J J0 χ χ' χ0 e e' SF a _ hχ hχ0 he fun _ _ => rfl) ?_
  refine rank_le θ M' M (fun τ => (c τ).symm) ?_ J J0 χ' χ χ0 e' e SF _ a ?_ hχ0 ?_ ?_
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]
  · intro P d
    simp

end GlobalTheory.ConjFull

end
