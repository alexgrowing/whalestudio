import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardIdealPowerShiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSectionIdealPowerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Shift

theorem exists_lift_pow_smul {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : N →ₗ[R] M) :
    ∃ k : ℕ, ∀ (n : ℕ) (y : N), f y ∈ J ^ (n + k) • (⊤ : Submodule R M) →
      ∃ i ∈ J ^ n • (⊤ : Submodule R N), f i = f y := by
  obtain ⟨k, hk⟩ := J.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k, fun n y hy => ?_⟩
  have h1 : f y ∈ J ^ (n + k) • (⊤ : Submodule R M) ⊓ LinearMap.range f := ⟨hy, y, rfl⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : J ^ n • (J ^ k • (⊤ : Submodule R M) ⊓ LinearMap.range f) ≤
      (J ^ n • (⊤ : Submodule R N)).map f := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right
  obtain ⟨i, hi, hfi⟩ := h2 h1
  exact ⟨i, hi, hfi⟩

theorem mem_secs_adjKer {X Z : Scheme.{0}} (φ : Z ⟶ X) {E : X.Modules}
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (V : X.Opens) (x : Γ(E, V))
    (hx : (adjMap φ B).app V x = 0) : x ∈ secs (adjKer φ B) V := by
  obtain ⟨k, hk⟩ := kernel_ι_app_exact (adjMap φ B) V x hx
  refine ⟨(kernelSubobjectIso (adjMap φ B)).inv.app V k, ?_⟩
  rw [← hk, ← kernelSubobject_arrow' (adjMap φ B)]
  rfl

theorem local_shift {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X)
    (hφ : IsProper φ) (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) {E : X.Modules}
    (hE : IsCoherent E) (S : ℕ → Subobject E)
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (hB : (B : Z.Modules).IsQuasicoherent)
    (hBS : ∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e)
    (hK : (adjKer φ B : X.Modules).IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V) :
    ∃ c : ℕ, ∀ e, secs (S (e + c)) V ⊆ secs (adjKer φ B ⊔ powSub I E (e + 1)) V := by
  haveI := hE.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow (isCoherent_pullback φ hE)
  have hP := GlobalTheory.T.proper_pushforward_coherent φ hφ hG
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.pushforward_ideal_power_shift I φ hφ hc hG V hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI := hP.2 V hV
  let f : Γ(E, V) →ₗ[Γ(X, V)] Γ((Scheme.Modules.pushforward φ).obj (cokernel B.arrow), V) :=
    { toFun := (adjMap φ B).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  let J : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) V) I
  have hJ : ∀ m, Ideal.map (toFunctions (A := A) V) (I ^ m) = J ^ m := fun m => Ideal.map_pow _ _ _
  obtain ⟨c₂, hc₂⟩ := exists_lift_pow_smul J f
  refine ⟨c₂ + c₁, fun e x hx => ?_⟩
  have h1 := GlobalTheory.T.cokernel_section_ideal_power I φ S B (e + (c₂ + c₁)) (hBS _) V x hx
  rw [show e + (c₂ + c₁) + 1 = (e + 1 + c₂) + c₁ by omega] at h1
  have h2 := hc₁ (e + 1 + c₂) _ h1
  rw [hJ] at h2
  obtain ⟨i, hi, hfi⟩ := hc₂ (e + 1) x h2
  have hker : x - i ∈ secs (adjKer φ B) V :=
    mem_secs_adjKer φ B V _ (by
      change f (x - i) = 0
      rw [map_sub, hfi, sub_self])
  have hpow : i ∈ secs (powSub I E (e + 1)) V := by
    rw [GlobalTheory.T.ideal_power_subobject_sections I E hE.1 (e + 1) V hV, hJ]
    exact hi
  have hsup := (GlobalTheory.T.quasicoherent_sup_sections hE.1 (adjKer φ B) (powSub I E (e + 1)) hK
    ((closedSys_pow I E).qcoh e)).2 V hV
  rw [hsup]
  exact ⟨x - i, hker, i, hpow, by abel⟩

theorem shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (B : Z.Modules).IsQuasicoherent → (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∃ c : ℕ, ∀ e, S (e + c) ≤ adjKer φ B ⊔ powSub I E (e + 1) := by
  intro A _ _ I X Z _ _ _ _ φ hφ hc E hE S hS B hB hBS
  haveI := hE.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow (isCoherent_pullback φ hE)
  have hP := GlobalTheory.T.proper_pushforward_coherent φ hφ hG
  haveI := hP.1
  have hK : (adjKer φ B : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (adjMap φ B)).symm (isQuasicoherent_kernel _)
  have hloc : ∀ V : X.affineOpens, ∃ c : ℕ,
      ∀ e, secs (S (e + c)) (V : X.Opens) ⊆ secs (adjKer φ B ⊔ powSub I E (e + 1)) (V : X.Opens) :=
    fun V => local_shift I φ hφ hc hE S B hB hBS hK V V.2
  choose c hc' using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hx, -⟩ :=
        exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩)
  have anti : Antitone S :=
    antitone_nat_of_succ_le fun n => le_of_le_of_eq le_sup_left (hS.succ n).symm
  refine ⟨t.sup c, fun e => ?_⟩
  have hsupq := (GlobalTheory.T.quasicoherent_sup_sections hE.1 (adjKer φ B) (powSub I E (e + 1)) hK
    ((closedSys_pow I E).qcoh e)).1
  refine GlobalTheory.T.subobject_le_of_affine_cover (S (e + t.sup c)) _ (hS.qcoh _) hsupq (fun i : t => (i.1.1 : X.Opens))
    (fun i => i.1.2) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hxU⟩
  · intro i
    refine subset_trans ?_ (hc' i.1 e)
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (anti (Nat.add_le_add_left (Finset.le_sup i.2) e)) i.1

end GlobalTheory.CompanionTheory.GE.Shift
