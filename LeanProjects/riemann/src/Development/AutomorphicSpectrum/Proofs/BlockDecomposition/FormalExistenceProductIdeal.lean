import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystemStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.NonPrime

variable {X : Scheme.{0}}

lemma secs_mk {E F : X.Modules} (f : F ⟶ E) [Mono f] (V : X.Opens) :
    secs (Subobject.mk f) V = Set.range (f.app V) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).hom.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).inv.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.underlyingIso_arrow]

lemma smul_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} (a : Γ(X, V)) {x : Γ(E, V)}
    (hx : x ∈ secs S V) : a • x ∈ secs S V := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨a • t, Scheme.Modules.Hom.app_smul S.arrow a t⟩

lemma add_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} {x y : Γ(E, V)}
    (hx : x ∈ secs S V) (hy : y ∈ secs S V) : x + y ∈ secs S V := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨s + t, map_add _ s t⟩

def idealSub (J : X.IdealSheafData) (E : X.Modules) : Subobject E :=
  Subobject.mk (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))

lemma secs_idealSub (J : X.IdealSheafData) (E : X.Modules) [E.IsQuasicoherent]
    (U : X.affineOpens) :
    secs (idealSub J E) U = ((J.ideal U • ⊤ : Submodule Γ(X, U) Γ(E, U)) : Set Γ(E, U)) := by
  rw [idealSub, secs_mk, ← (GlobalTheory.surjective_and_ker_unit_subschemeι J E U).2,
    ← GlobalTheory.QCoh.range_kernel_ι_app]
  rfl

lemma isQuasicoherent_idealSub (J : X.IdealSheafData) {E : X.Modules} (hE : IsCoherent E) :
    ((idealSub J E : Subobject E) : X.Modules).IsQuasicoherent := by
  have := hE.1
  have := (isCoherent_pullback J.subschemeι hE).1
  have h₀ : ((𝟭 X.Modules).obj E).IsQuasicoherent := hE.1
  have h₁ : ((Scheme.Modules.pullback J.subschemeι ⋙ Scheme.Modules.pushforward J.subschemeι).obj
      E).IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom J.subschemeι
    ((Scheme.Modules.pullback J.subschemeι).obj E)
  have hk : (kernel ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app
      E)).IsQuasicoherent := GlobalTheory.QCoh.isQuasicoherent_kernel _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι
      ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))).symm hk

lemma propSupp_mono {A : Type} [CommRing A] [X.Over (Spec (.of A))] {E : X.Modules}
    {S S' : Subobject E} (h : S ≤ S') (hS : PropSupp A S) : PropSupp A S' := by
  obtain ⟨T, hT, hsupp⟩ := hS
  refine ⟨T, hT, ?_⟩
  have w : S.arrow ≫ cokernel.π S'.arrow = 0 := by
    rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero]
  have : Epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) :=
    epi_of_epi_fac (cokernel.π_desc S.arrow (cokernel.π S'.arrow) w)
  exact Scheme.Modules.SupportedIn.of_epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) hsupp

theorem statement_of_mul_mem : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J J₁ J₂ : X.IdealSheafData),
    (∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U) →
    Statement I J₁ → Statement I J₂ → Statement I J := by
  intro A _ _ I X _ _ _ _ J J₁ J₂ hm h₁ h₂ E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hEq : E.IsQuasicoherent := hE.1
  set K : Subobject E := idealSub J₁ E with hKdef
  have hKq : (K : X.Modules).IsQuasicoherent := isQuasicoherent_idealSub J₁ hE
  have hS1 : ClosedSys I E (fun e => S e ⊔ K) :=
    { qcoh := fun e => (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh e) hKq).1
      pow_le := fun e => (hS.pow_le e).trans le_sup_left
      succ := fun e => by
        conv_lhs => rw [hS.succ e]
        exact sup_right_comm _ _ _ }
  have hK1 : ∀ e, Killed J₁ (S e ⊔ K) := by
    intro e U a ha x
    have hax : a • x ∈ secs K U := by
      rw [hKdef, secs_idealSub]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    exact (GlobalTheory.T.subobject_le_iff_affine_sections K (S e ⊔ K)).1 le_sup_right U hax
  obtain ⟨B, hBq, hBP, hB⟩ := h₁ E hE _ hS1 hK1 (propSupp_mono le_sup_left hP)
  have hDq : ((B ⊔ K : Subobject E) : X.Modules).IsQuasicoherent :=
    (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ hBq hKq).1
  have hDP : PropSupp A (B ⊔ K) := propSupp_mono le_sup_left hBP
  have hc : ∀ e, S (e + 0) ≤ (B ⊔ K) ⊔ powSub I E (e + 1) := fun e =>
    (le_sup_left : S e ≤ S e ⊔ K).trans ((hB e).symm.le.trans (sup_le_sup_right le_sup_left _))
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP (B ⊔ K) hDq 0 hc
  have hkill : ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J₂.ideal U →
      ∀ x ∈ secs (B ⊔ K) U, a • x ∈ secs (S n) U := by
    intro n U a ha x hx
    have hle : B ⊔ K ≤ S n ⊔ K :=
      sup_le ((le_sup_left : B ≤ B ⊔ powSub I E (n + 1)).trans (hB n).le) le_sup_right
    have hx' := (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 hle U hx
    rw [(GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh n) hKq).2 U U.2] at hx'
    obtain ⟨s, hs, k, hk, rfl⟩ := hx'
    rw [smul_add]
    refine add_mem_secs _ (smul_mem_secs _ a hs) ?_
    rw [hKdef, secs_idealSub] at hk
    refine Submodule.smul_induction_on (p := fun k => a • k ∈ secs (S n) U) hk
      (fun b hb y _ => ?_) (fun y z hy hz => ?_)
    · rw [smul_smul, mul_comm]
      exact hK n U _ (hm U b a hb ha) y
    · rw [smul_add]
      exact add_mem_secs _ hy hz
  exact halg (h₂ _ (GlobalTheory.T.coherent_subobject_coherent hE _ hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J₂ _ S c' hkill) hP') hDP

end GlobalTheory.CompanionTheory.GE.NonPrime
