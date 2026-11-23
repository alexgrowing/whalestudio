import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

noncomputable section

namespace Formalism.L2.Herm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

structure StepLevelQ (hc : CMData F E) (S : HSpace E) (gp : Fin 2 → ℕ) (T f : ℕ)
    (Q : Finset (HeightOneSpectrum (𝓞 F))) where

  Lb : Submodule (𝓞 E) (Fin S.rank → E)
  Lb_fin : Module.Finite (𝓞 E) Lb
  Lb_span : Submodule.span E (Lb : Set (Fin S.rank → E)) = ⊤
  Lb_int : Lb ≤ dualL hc S Lb
  Lb_dual : ∀ y ∈ dualL hc S Lb, (T : E) • y ∈ Lb
  Lb_index : Lb.toAddSubgroup.relIndex (dualL hc S Lb).toAddSubgroup = T ^ (2 * f)

  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))
  Uloc_lev : ∀ v, Uloc v ≤ levelVL hc.sig S.gram v Lb
  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) →
    ((gp 1 : 𝓞 F) ∉ v.asIdeal) → ((T : 𝓞 F) ∉ v.asIdeal) → v ∉ Q → Uloc v = levelVL hc.sig S.gram v Lb
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    ∀ x, InPrinc hc S v (gp i) Lb x → x ∈ Uloc v
  UlocAlt : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x, x ∈ Uloc v ↔ InLocalDiscriminantKernel hc S v Lb x
  Uloc_Q : ∀ v ∈ Q, ∃ N : ℕ, 0 < N ∧ ∀ x, InPrinc hc S v N Lb x → x ∈ Uloc v

  U : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UAf hc S ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v

end Formalism.L2.Herm

end
