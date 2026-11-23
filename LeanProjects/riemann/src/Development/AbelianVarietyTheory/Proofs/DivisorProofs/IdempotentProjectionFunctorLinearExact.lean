import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts

noncomputable section

namespace GlobalTheory.ChainParts.PartExact

section General

variable {D : Type*} [Category D] [Abelian D] {S T : ShortComplex D} (φ : S ⟶ T) (ψ : T ⟶ S)

theorem exact_of_retract (h : φ ≫ ψ = 𝟙 S) (hT : T.Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology] at hT ⊢
  rw [IsZero.iff_id_eq_zero, ← ShortComplex.homologyMap_id, ← h, ShortComplex.homologyMap_comp,
    hT.eq_zero_of_tgt (ShortComplex.homologyMap φ), zero_comp]

theorem mono_of_retract (h : φ ≫ ψ = 𝟙 S) [Mono T.f] : Mono S.f := by
  have h1 : φ.τ₁ ≫ ψ.τ₁ = 𝟙 _ := congrArg ShortComplex.Hom.τ₁ h
  haveI : Mono φ.τ₁ := mono_of_mono_fac h1
  exact mono_of_mono_fac φ.comm₁₂.symm

theorem epi_of_retract (h : φ ≫ ψ = 𝟙 S) [Epi T.g] : Epi S.g := by
  have h1 : φ.τ₃ ≫ ψ.τ₃ = 𝟙 _ := congrArg ShortComplex.Hom.τ₃ h
  haveI : Epi ψ.τ₃ := epi_of_epi_fac h1
  exact epi_of_epi_fac ψ.comm₂₃

end General

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]
  {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ)

instance (M : AM B Λ) : Mono (partι c a M) := inferInstanceAs (Mono (kernel.ι _))

theorem map_ι {M N : AM B Λ} (f : M ⟶ N) : (partF c a).map f ≫ partι c a N = partι c a M ≫ f.hom :=
  kernel.lift_ι _ _ _

theorem ι_e (M : AM B Λ) : partι c a M ≫ eA M c a = partι c a M := by
  have h : partι c a M ≫ (𝟙 M.V - eA M c a) = 0 := kernel.condition _
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
  exact h.symm

def proj (M : AM B Λ) (h : eA M c a ≫ eA M c a = eA M c a) : M.V ⟶ (partF c a).obj M :=
  kernel.lift (𝟙 M.V - eA M c a) (eA M c a) (by rw [Preadditive.comp_sub, Category.comp_id, h, sub_self])

theorem proj_ι (M : AM B Λ) (h : eA M c a ≫ eA M c a = eA M c a) : proj c a M h ≫ partι c a M = eA M c a :=
  kernel.lift_ι _ _ _

theorem ι_proj (M : AM B Λ) (h : eA M c a ≫ eA M c a = eA M c a) : partι c a M ≫ proj c a M h = 𝟙 _ := by
  rw [← cancel_mono (partι c a M), Category.assoc, proj_ι, ι_e, Category.id_comp]

theorem proj_map {M N : AM B Λ} (f : M ⟶ N) (h : eA M c a ≫ eA M c a = eA M c a)
    (h' : eA N c a ≫ eA N c a = eA N c a) : proj c a M h ≫ (partF c a).map f = f.hom ≫ proj c a N h' := by
  rw [← cancel_mono (partι c a N), Category.assoc, Category.assoc, map_ι, proj_ι, ← Category.assoc, proj_ι, eA_comm]

theorem exists_retract (S : ShortComplex (AM B Λ)) (h₁ : eA S.X₁ c a ≫ eA S.X₁ c a = eA S.X₁ c a)
    (h₂ : eA S.X₂ c a ≫ eA S.X₂ c a = eA S.X₂ c a) (h₃ : eA S.X₃ c a ≫ eA S.X₃ c a = eA S.X₃ c a) :
    ∃ (φ : S.map (partF c a) ⟶ S.map (Action.forget B.X.Modules Λ))
      (ψ : S.map (Action.forget B.X.Modules Λ) ⟶ S.map (partF c a)), φ ≫ ψ = 𝟙 _ :=
  ⟨⟨partι c a _, partι c a _, partι c a _, (map_ι c a S.f).symm, (map_ι c a S.g).symm⟩,
    ⟨proj c a _ h₁, proj c a _ h₂, proj c a _ h₃, proj_map c a S.f h₁ h₂, proj_map c a S.g h₂ h₃⟩,
    ShortComplex.hom_ext _ _ (ι_proj c a _ h₁) (ι_proj c a _ h₂) (ι_proj c a _ h₃)⟩

theorem idem_cokernel {M N : AM B Λ} (f : M ⟶ N) (h : eA N c a ≫ eA N c a = eA N c a) :
    eA (cokernel f) c a ≫ eA (cokernel f) c a = eA (cokernel f) c a := by
  have : Epi (cokernel.π f).hom := inferInstanceAs (Epi ((Action.forget B.X.Modules Λ).map (cokernel.π f)))
  rw [← cancel_epi (cokernel.π f).hom, ← Category.assoc, ← eA_comm, Category.assoc, ← eA_comm, ← Category.assoc, h]

end GlobalTheory.ChainParts.PartExact

namespace GlobalTheory.ChainParts

open PartExact

theorem partF_exact : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ] {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) (hidem : ∀ M : AM B Λ, IsAdd M → eA M c a ≫ eA M c a = eA M c a), (∀ (M : AM B Λ) (g : Γ(B.X, ⊤)), (partF c a).map (smulA M g) = smulHom ((partF c a).obj M) g) ∧
    (∀ S : ShortComplex (AM B Λ), S.ShortExact → IsAdd S.X₁ → IsAdd S.X₂ → IsAdd S.X₃ →
      (S.map (partF c a)).ShortExact) ∧
    (∀ {M N : AM B Λ} (f : M ⟶ N), IsAdd M → IsAdd N →
      Nonempty ((partF c a).obj (cokernel f) ≅ cokernel ((partF c a).map f))) ∧
    (∀ M : AM B Λ, IsAdd M → ∃ (i : (partF c a).obj M ⟶ M.V) (q : M.V ⟶ (partF c a).obj M), i ≫ q = 𝟙 _) := by
  intro O _ _ _ B Λ _ n c a hidem
  refine ⟨fun M g => ?_, fun S hS h₁ h₂ h₃ => ?_, fun {M N} f hM hN => ?_, fun M hM => ?_⟩
  · rw [← cancel_mono (partι c a M), map_ι]
    first | exact (smulHom_comp _ _).symm | exact smulHom_comp _ _
  · obtain ⟨φ, ψ, h⟩ := exists_retract c a S (hidem _ h₁) (hidem _ h₂) (hidem _ h₃)
    have hT := hS.map_of_exact (Action.forget B.X.Modules Λ)
    haveI := hT.mono_f
    haveI := hT.epi_g
    exact { exact := exact_of_retract φ ψ h hT.exact, mono_f := mono_of_retract φ ψ h, epi_g := epi_of_retract φ ψ h }
  · let S : ShortComplex (AM B Λ) := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    obtain ⟨φ, ψ, h⟩ := exists_retract c a S (hidem _ hM) (hidem _ hN) (idem_cokernel c a f (hidem _ hN))
    have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
    have hT := hS.map (Action.forget B.X.Modules Λ)
    haveI : Epi (S.map (Action.forget B.X.Modules Λ)).g :=
      inferInstanceAs (Epi ((Action.forget B.X.Modules Λ).map (cokernel.π f)))
    haveI := epi_of_retract φ ψ h
    exact ⟨(exact_of_retract φ ψ h hT).gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)⟩
  · exact ⟨partι c a M, proj c a M (hidem M hM), ι_proj c a M _⟩

end GlobalTheory.ChainParts

end
