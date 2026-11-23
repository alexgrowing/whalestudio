import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulNonsingInvCancelRightGram
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.AlgStable

theorem isStable_span {D : D7} (θ : InfFam D) (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ))
    (s : Set (Z → ℂ)) (h1 : ∀ g ∈ GfC X, ∀ Φ ∈ s, ρ g Φ ∈ Submodule.span ℂ s)
    (h2 : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ s, ∃ Φ' ∈ Submodule.span ℂ s, GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsDer θ X ρ τ Y Φ Φ') :
    GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsStable θ X ρ (Submodule.span ℂ s) := by
  refine ⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩
  · have hle : Submodule.span ℂ s ≤ (Submodule.span ℂ s).comap (ρ g) := Submodule.span_le.2 (h1 g hg)
    exact hle hΦ
  · induction hΦ using Submodule.span_induction with
    | mem x hx => exact h2 τ Y hY x hx
    | zero =>
      refine ⟨0, zero_mem _, fun z => ?_⟩
      simp only [map_zero]
      exact hasDerivAt_const _ _
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', dx⟩ := hx
      obtain ⟨y', hy', dy⟩ := hy
      refine ⟨x' + y', add_mem hx' hy', fun z => ?_⟩
      simp only [map_add]
      exact (dx z).add (dy z)
    | smul a x _ hx =>
      obtain ⟨x', hx', dx⟩ := hx
      refine ⟨a • x', Submodule.smul_mem _ a hx', fun z => ?_⟩
      simp only [map_smul]
      exact (dx z).const_mul a

theorem isVacF_om {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (A : Fr S)
    (B : Fr T) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {g : GA D S} (hg : g ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) {f : WO S T → ℂ}
    (hf : IsVacF ψ θ A B f) : IsVacF ψ θ A B (om (g, h) f) := by
  have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
    intro τ z
    rw [GlobalTheory.OrientedHeis.om_dRho hW hθ g h τ z hf.1, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (inv_mem hg), Matrix.one_mul, Matrix.mul_one]
  refine ⟨hW.om_pres _ f hf.1, fun τ z => ?_⟩
  have h0 := hf.2 τ z
  unfold annih at h0 ⊢
  rw [e, e, ← map_smul, ← map_add, h0, map_zero]

theorem algF_isStable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (Am : Fr M) (Bx : Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
      IsStable θ M (fun g => ω (g, 1)) (algF ψ θ ε Am Bx) ∧ IsStable θ X (fun h => ω (1, h)) (algF ψ θ ε Am Bx) := by
  intro D ψ θ _ hθ ε M X A B χ χ' ω hW
  have hW' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hW
  have hmem : ∀ f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B f P ∈ algF ψ θ ε A B :=
    fun f P hf => Submodule.subset_span ⟨f, P, hf, rfl⟩
  have e0 : ∀ (g : GA D (sgn ε M)) (h : GA D X), (ω.toSgn ε) (g, h) = ω (ofSgn ε M g, h) := fun _ _ => rfl
  have hfin : ∀ g ∈ GfC M, ∀ h ∈ GfC X, ∀ f P, IsFinF ψ θ ε A B f →
      ω (g, h) (fockF ψ θ ε A B f P) ∈ algF ψ θ ε A B := by
    intro g hg h hh f P hf
    have hg' : (ofSgn ε M).symm g ∈ GfC (sgn ε M) := by
      rw [GlobalTheory.SgnIdent.mem_GfC_sgn, MulEquiv.apply_symm_apply]; exact hg
    have ht := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ (sgn ε M) X χ χ' (ω.toSgn ε) hW' θ hθ _ hg' h hh
      (frSgn ε A).cart B.cart A.onb B.onb f P hf.1
    have hv := isVacF_om hθ (frSgn ε A) B hW' hg' hh hf
    rw [e0, MulEquiv.apply_symm_apply] at ht hv
    have : ω (g, h) (fockF ψ θ ε A B f P) = fockF ψ θ ε A B (ω (g, h) f) P := ht
    rw [this]
    exact hmem _ _ hv
  have hL := fun τ => GlobalTheory.LieFock.lieFockUpTo D (sgn ε M) X (frSgn ε A) B θ ψ χ χ' (ω.toSgn ε) τ hθ hW'
  refine ⟨isStable_span θ M _ _ ?_ ?_, isStable_span θ X _ _ ?_ ?_⟩
  · rintro g hg _ ⟨f, P, hf, rfl⟩
    exact hfin g hg 1 (one_mem _) f P hf
  · rintro τ Z hZ _ ⟨f, P, hf, rfl⟩
    obtain ⟨κS, κT, hκ⟩ := hL τ
    have hZ' : Z ∈ lieAt (sgn ε M) τ := by rw [GlobalTheory.SgnIdent.lieAt_sgn]; exact hZ
    have e : ∀ t : ℝ, (ω.toSgn ε) (oneP θ (sgn ε M) τ Z t, 1) = ω (oneP θ M τ Z t, 1) := by
      intro t
      rw [e0]
      unfold oneP
      rw [GlobalTheory.SgnIdent.atTau_sgn θ hθ]
    have h := (hκ f hf).1 Z hZ' P
    simp only [e] at h
    exact ⟨_, hmem f _ hf, h⟩
  · rintro h hh _ ⟨f, P, hf, rfl⟩
    exact hfin 1 (one_mem _) h hh f P hf
  · rintro τ Y hY _ ⟨f, P, hf, rfl⟩
    obtain ⟨κS, κT, hκ⟩ := hL τ
    have e1 : ∀ h : GA D X, (ω.toSgn ε) (1, h) = ω (1, h) := fun h => by rw [e0, map_one]
    have h := (hκ f hf).2 Y hY P
    simp only [e1] at h
    exact ⟨_, hmem f _ hf, h⟩

end GlobalTheory.AlgStable
