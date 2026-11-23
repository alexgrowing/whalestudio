import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrob
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts

namespace GlobalTheory.ChainPts.FrobSec

section Alg

variable {A T M N : Type} [CommRing A] [CommRing T] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module T N]

theorem span_lift [Algebra A T] [Module A N] [IsScalarTower A T N] (l : M →ₗ[A] N) (hl : IsBaseChange T l) :
    Submodule.span T (Set.range l) = ⊤ ∧ ∀ (P : Type) [AddCommGroup P] [Module T P] (τ : M →+ P),
      (∀ (a : A) (x : M), τ (a • x) = algebraMap A T a • τ x) → ∃ g : N →ₗ[T] P, ∀ x, g (l x) = τ x := by
  refine ⟨eq_top_iff.2 fun n _ => ?_, fun P _ _ τ hτ => ?_⟩
  · induction n using hl.inductionOn with
    | zero => exact zero_mem _
    | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
    | smul t n ih => exact Submodule.smul_mem _ _ (ih trivial)
    | add n₁ n₂ h₁ h₂ => exact add_mem (h₁ trivial) (h₂ trivial)
  · letI : Module A P := Module.compHom P (algebraMap A T)
    haveI : IsScalarTower A T P := .of_algebraMap_smul fun _ _ => rfl
    let τ' : M →ₗ[A] P := { toFun := τ, map_add' := τ.map_add, map_smul' := hτ }
    exact ⟨hl.lift τ', fun x => hl.lift_eq τ' x⟩

theorem univ_of [Module A N] (p q : ℕ) (ι : A →+* T) (hι : Function.Surjective ι)
    (hker : RingHom.ker ι = Ideal.span {(p : A)}) (hN : ∀ (a : A) (n : N), a • n = ι a • n) (σ : M →+ N)
    (hσ : ∀ (a : A) (x : M), σ (a • x) = ι (a ^ q) • σ x) (hsp : Submodule.span T (Set.range σ) = ⊤)
    (hU : ∀ (P : Type) [AddCommGroup P] [Module T P] (τ : M →+ P),
      (∀ (a : A) (x : M), τ (a • x) = ι (a ^ q) • τ x) → ∃ g : N →ₗ[T] P, ∀ x, g (σ x) = τ x) :
    GlobalTheory.RingChain.FrobLin.Univ A p q σ := by
  have h0 : ι p = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  refine ⟨fun y => by rw [hN, h0, zero_smul], fun a x => by rw [hσ, hN], eq_top_iff.2 fun y _ => ?_,
    fun P _ _ τ hp hτ => ?_⟩
  · have hy : y ∈ Submodule.span T (Set.range σ) := hsp ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y h => exact Submodule.subset_span h
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem (hy trivial) (hz trivial)
    | smul t y _ hy =>
      obtain ⟨a, rfl⟩ := hι t
      rw [← hN]
      exact Submodule.smul_mem _ _ (hy trivial)
  · have tors : Module.IsTorsionBySet A P (RingHom.ker ι) := by
      rw [hker, Module.isTorsionBySet_span_singleton_iff]
      exact fun y => hp y
    letI mB : Module (A ⧸ RingHom.ker ι) P := tors.module
    let e : (A ⧸ RingHom.ker ι) ≃+* T := RingHom.quotientKerEquivOfSurjective hι
    letI mT : Module T P := Module.compHom P e.symm.toRingHom
    have hm : ∀ (a : A) (y : P), ι a • y = a • y := fun a y => by
      have : e.symm (ι a) = Ideal.Quotient.mk _ a := e.symm_apply_eq.2 rfl
      change e.symm (ι a) • y = _
      rw [this]
      rfl
    obtain ⟨g, hg⟩ := hU P τ fun a x => by rw [hτ, hm]
    have hs : ∀ (a : A) (y : N), g (a • y) = a • g y := fun a y => by rw [hN, g.map_smul, hm]
    exact ⟨{ toFun := g, map_add' := g.map_add, map_smul' := hs }, hg⟩

end Alg

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] {B : GlobalTheory.Vert.Model O}
  (hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0)

abbrev frι : (fibI p B).subscheme ⟶ B.X := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out hp ≫ (fibI p B).subschemeι

theorem le_frι (V : B.X.Opens) : (fibI p B).subschemeι ⁻¹ᵁ V ≤ frι p hp ⁻¹ᵁ V := le_rfl

def sig (F : B.X.Modules) (V : B.X.Opens) : Γ(F, V) →+ Γ((frobFun p hp).obj F, V) :=
  letI := appLEModule (frι p hp) ((Scheme.Modules.pullback (frι p hp)).obj F) (le_frι p hp V)
  (pullbackSections (frι p hp) F (le_frι p hp V)).toAddMonoidHom

theorem isFrobLin_sig (F : B.X.Modules) [F.IsQuasicoherent] (U : B.X.Opens) (hU : IsAffineOpen U) :
    GlobalTheory.RingChain.IsFrobLin Γ(B.X, U) p p (sig p hp F U) := by
  intro φ hφ
  refine (GlobalTheory.RingChain.FrobLin.iff_univ φ hφ _).2 ?_ φ hφ
  have hU' : IsAffineOpen ((fibI p B).subschemeι ⁻¹ᵁ U) := hU.preimage _
  have hι := (fibI p B).subschemeι_app_surjective ⟨U, hU⟩
  have hker : RingHom.ker ((fibI p B).subschemeι.app U).hom = Ideal.span {(p : Γ(B.X, U))} := by
    rw [(fibI p B).ker_subschemeι_app ⟨U, hU⟩]
    simp [fibI, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span]
  have hg : ∀ a, ((frι p hp).appLE U _ (le_frι p hp U)).hom a = ((fibI p B).subschemeι.app U).hom (a ^ p) := by
    intro a
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, map_pow]
    exact (GlobalTheory.SS.FrobField.absFrob_appLE _ p 1 Fact.out hp _ _ _).trans (by rw [pow_one])
  obtain ⟨h₁, h₂⟩ := (letI := appLEAlgebra (frι p hp) (le_frι p hp U)
    letI := appLEModule (frι p hp) ((Scheme.Modules.pullback (frι p hp)).obj F) (le_frι p hp U)
    haveI := appLE_isScalarTower (frι p hp) ((Scheme.Modules.pullback (frι p hp)).obj F) (le_frι p hp U)
    span_lift _ (isBaseChange_pullbackSections (frι p hp) F hU' hU (le_frι p hp U)))
  letI : Module Γ((fibI p B).subscheme, (fibI p B).subschemeι ⁻¹ᵁ U) Γ((frobFun p hp).obj F, U) :=
    inferInstanceAs (Module Γ((fibI p B).subscheme, (fibI p B).subschemeι ⁻¹ᵁ U)
      Γ((Scheme.Modules.pullback (frι p hp)).obj F, (fibI p B).subschemeι ⁻¹ᵁ U))
  refine univ_of p p ((fibI p B).subschemeι.app U).hom hι hker (fun _ _ => rfl) _ (fun a x => ?_) h₁
    fun P _ _ τ hτ => h₂ P τ fun a x => (hτ a x).trans (congrArg (· • τ x) (hg a).symm)
  exact (pullbackSections_smul (frι p hp) F (le_frι p hp U) a x).trans (congrArg (· • _) (hg a))

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0), ∃ σ : ∀ (F : B.X.Modules) (V : B.X.Opens), Γ(F, V) →+ Γ((frobFun p hp).obj F, V), (∀ (F G : B.X.Modules) (u : F ⟶ G) (V : B.X.Opens) (s : Γ(F, V)), ((frobFun p hp).map u).app V (σ F V s) = σ G V (u.app V s)) ∧ (∀ (F : B.X.Modules) (V V' : B.X.Opens) (hle : V' ≤ V) (s : Γ(F, V)), resM ((frobFun p hp).obj F) hle (σ F V s) = σ F V' (resM F hle s)) ∧ ∀ (F : B.X.Modules) [F.IsQuasicoherent], ((frobFun p hp).obj F).IsQuasicoherent ∧ ∀ V : B.X.Opens, IsAffineOpen V → GlobalTheory.RingChain.IsFrobLin Γ(B.X, V) p p (σ F V) := by
  intro O _ _ _ p _ B hp
  refine ⟨sig p hp, fun F G u V s => ?_, fun F V V' hle s => ?_, fun F _ => ⟨?_, isFrobLin_sig p hp F⟩⟩
  · exact pullback_map_app_pullbackSections (frι p hp) u (le_frι p hp V) s
  · exact (res_pullbackSections (frι p hp) F (le_frι p hp V) ((fibI p B).subschemeι.preimage_mono hle) s).trans
      (pullbackSections_res (frι p hp) F (le_frι p hp V') hle s).symm
  · exact inferInstanceAs ((Scheme.Modules.pushforward (fibI p B).subschemeι).obj
      ((Scheme.Modules.pullback (frι p hp)).obj F)).IsQuasicoherent

end GlobalTheory.ChainPts.FrobSec

end
