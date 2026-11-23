import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.HoweTransport

open GlobalTheory.Published GlobalTheory.PRep

section Sub

variable {H H' T : Type} [Group H] [Group H'] [AddCommGroup T] [Module ℂ T]

def subIso (e : H ≃* H') (ρ : Representation ℂ H' T) :
    Subrepresentation (ρ.comp e.toMonoidHom : Representation ℂ H T) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (e.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (e g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem irr_comp (e : H ≃* H') {ρ : Representation ℂ H' T} (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom : Representation ℂ H T) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact (subIso e ρ).isSimpleOrder

theorem coatom_comp (e : H ≃* H') {ρ : Representation ℂ H' T}
    (h : ∀ N N' : Subrepresentation ρ, IsCoatom N → IsCoatom N' → N = N') :
    ∀ N N' : Subrepresentation (ρ.comp e.toMonoidHom : Representation ℂ H T), IsCoatom N → IsCoatom N' → N = N' := by
  intro N N' hN hN'
  apply (subIso e ρ).injective
  exact h _ _ (((subIso e ρ).isCoatom_iff N).2 hN) (((subIso e ρ).isCoatom_iff N').2 hN')

def modIso (e : H ≃* H') (ρ : Representation ℂ H' T) :
    Submodule (MonoidAlgebra ℂ H) (Representation.asModule (ρ.comp e.toMonoidHom : Representation ℂ H T)) ≃o
      Submodule (MonoidAlgebra ℂ H') ρ.asModule :=
  (Subrepresentation.subrepresentationSubmoduleOrderIso.symm.trans (subIso e ρ)).trans
    Subrepresentation.subrepresentationSubmoduleOrderIso

theorem finLen_comp (e : H ≃* H') {ρ : Representation ℂ H' T}
    (h : IsFiniteLength (MonoidAlgebra ℂ H') ρ.asModule) :
    IsFiniteLength (MonoidAlgebra ℂ H) (Representation.asModule (ρ.comp e.toMonoidHom : Representation ℂ H T)) := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
  obtain ⟨h1, h2⟩ := h
  rw [isNoetherian_iff'] at h1 ⊢
  refine ⟨(modIso e ρ).strictMono.wellFoundedGT, ?_⟩
  haveI := h2
  exact (modIso e ρ).strictMono.wellFoundedLT

end Sub

section Top

variable {G G' V : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [AddCommGroup V] [Module ℂ V]

theorem smooth_comp (e : G' →* G) (he : Continuous e) {π : Representation ℂ G V} (h : IsSmooth π) :
    IsSmooth (π.comp e : Representation ℂ G' V) := fun v => (h v).preimage he

theorem fixed_comp (e : G' ≃* G) (π : Representation ℂ G V) (K : Subgroup G') :
    fixed (π.comp e.toMonoidHom : Representation ℂ G' V) K = fixed π (K.comap e.symm.toMonoidHom) := by
  ext v
  simp only [fixed, eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro hv k
    have := hv ⟨e.symm k, k.2⟩
    simpa using this
  · intro hv k
    have := hv ⟨e k, by simp [Subgroup.mem_comap]⟩
    simpa using this

theorem admissible_comp_eval (e : G' ≃* G) (he : Continuous e) (he' : Continuous e.symm) {π : Representation ℂ G V}
    (h : IsAdmissible π) : IsAdmissible (π.comp e.toMonoidHom : Representation ℂ G' V) := by
  refine ⟨smooth_comp e.toMonoidHom he h.1, fun K hKo hKc => ?_⟩
  rw [fixed_comp]
  refine h.2 _ ?_ ?_
  · have : ((K.comap e.symm.toMonoidHom : Subgroup G) : Set G) = e.symm ⁻¹' (K : Set G') := rfl
    rw [this]
    exact hKo.preimage he'
  · have : ((K.comap e.symm.toMonoidHom : Subgroup G) : Set G) = e '' (K : Set G') := by
      ext x
      simp only [Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, Set.mem_image, MulEquiv.coe_toMonoidHom]
      exact ⟨fun hx => ⟨e.symm x, hx, by simp⟩, fun ⟨y, hy, hyx⟩ => by rw [← hyx]; simpa using hy⟩
    rw [this]
    exact hKc.image he

end Top

end GlobalTheory.HoweLocal.HoweTransport

namespace GlobalTheory.HoweLocal.HoweTransport

open GlobalTheory.Published GlobalTheory.PRep

section HoweDuality

variable {G G' H H' Y V T : Type} [Group G] [Group G'] [Group H] [Group H'] [TopologicalSpace Y]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℂ T]

theorem left_iff (eG : G ≃* G') (eH : H ≃* H') (om : G' × H' →* Module.End ℂ (Y → ℂ))
    (π : Representation ℂ G V) (f : SB Y →ₗ[ℂ] V) :
    IsLeftHom (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) π f ↔
      IsLeftHom om (π.comp eG.symm.toMonoidHom) f := by
  constructor
  · intro h g φ φ₁ hφ
    have := h (eG.symm g) φ φ₁ (by simpa using hφ)
    simpa using this
  · intro h g φ φ₁ hφ
    have := h (eG g) φ φ₁ (by simpa using hφ)
    simpa using this

theorem pair_to (eG : G ≃* G') (eH : H ≃* H') (om : G' × H' →* Module.End ℂ (Y → ℂ))
    (π : Representation ℂ G V) (τ : Representation ℂ H T) (f : SB Y →ₗ[ℂ] V ⊗[ℂ] T)
    (h : IsPairHom (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) π τ f) :
    IsPairHom om (π.comp eG.symm.toMonoidHom) (τ.comp eH.symm.toMonoidHom) f := by
  intro g k φ φ₁ hφ
  have := h (eG.symm g) (eH.symm k) φ φ₁ (by simpa using hφ)
  simpa using this

theorem pair_from (eG : G ≃* G') (eH : H ≃* H') (om : G' × H' →* Module.End ℂ (Y → ℂ))
    (π : Representation ℂ G V) (τ : Representation ℂ H' T) (f : SB Y →ₗ[ℂ] V ⊗[ℂ] T)
    (h : IsPairHom om (π.comp eG.symm.toMonoidHom) τ f) :
    IsPairHom (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) π (τ.comp eH.toMonoidHom) f := by
  intro g k φ φ₁ hφ
  have := h (eG g) (eH k) φ φ₁ (by simpa using hφ)
  simpa using this

theorem equiv_back {V' : Type} [AddCommGroup V'] [Module ℂ V'] (eG : G ≃* G') {π : Representation ℂ G V}
    {π' : Representation ℂ G V'}
    (e : Representation.Equiv (π.comp eG.symm.toMonoidHom : Representation ℂ G' V)
      (π'.comp eG.symm.toMonoidHom : Representation ℂ G' V')) :
    Nonempty (π.Equiv π') := by
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (eG g) v
  simp only [LinearMap.comp_apply]
  change e.toIntertwiningMap (π g v) = π' g (e.toIntertwiningMap v)
  simpa using h1

end HoweDuality

end GlobalTheory.HoweLocal.HoweTransport

namespace GlobalTheory.HoweLocal.HoweTransport

open GlobalTheory.Published GlobalTheory.PRep

theorem howeDualityFor_transport : ∀ {G G' H H' Y : Type} [Group G] [Group G'] [Group H] [Group H'] [TopologicalSpace G] [TopologicalSpace G']
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace Y] (eG : G ≃* G') (eH : H ≃* H'),
    Continuous eG → Continuous eG.symm → Continuous eH → Continuous eH.symm →
    ∀ om : G' × H' →* Module.End ℂ (Y → ℂ), GlobalTheory.Published.HoweDualityFor om →
      GlobalTheory.Published.HoweDualityFor (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) := by
  intro G G' H H' Y _ _ _ _ _ _ _ _ _ eG eH hG hG' hH hH' om hom
  have hGs : Continuous eG.symm.symm := by simpa using hG
  intro V _ _ π hπ hA
  obtain ⟨⟨T, iT1, iT2, Θ, p, ⟨hP, hSur, hK⟩, hS, hF, hC⟩, h2⟩ :=
    hom V (π.comp eG.symm.toMonoidHom) (irr_comp eG.symm hπ) (admissible_comp_eval eG.symm hG' hGs hA)
  refine ⟨⟨T, iT1, iT2, Θ.comp eH.toMonoidHom, p, ⟨pair_from eG eH om π Θ p hP, hSur, fun φ => ?_⟩,
    smooth_comp eH.toMonoidHom hH hS, finLen_comp eH hF, coatom_comp eH hC⟩, ?_⟩
  · rw [hK φ]
    simp only [left_iff]
  · intro T _ _ τ hτ hτs f hf hf0
    obtain ⟨h2a, h2b⟩ := h2 T (τ.comp eH.symm.toMonoidHom) (irr_comp eH.symm hτ)
      (smooth_comp eH.symm.toMonoidHom hH' hτs) f (pair_to eG eH om π τ f hf) hf0
    refine ⟨fun f' hf' => h2a f' (pair_to eG eH om π τ f' hf'), fun V' _ _ π₂ hπ₂ hA₂ f' hf' hf'0 => ?_⟩
    obtain ⟨e⟩ := h2b V' (π₂.comp eG.symm.toMonoidHom) (irr_comp eG.symm hπ₂) (admissible_comp_eval eG.symm hG' hGs hA₂) f'
      (pair_to eG eH om π₂ τ f' hf') hf'0
    exact equiv_back eG e

end GlobalTheory.HoweLocal.HoweTransport

end
