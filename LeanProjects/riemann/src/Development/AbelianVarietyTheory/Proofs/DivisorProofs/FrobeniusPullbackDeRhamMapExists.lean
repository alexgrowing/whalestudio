import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasicoherentHomFromAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.LinFrob

open GlobalTheory.Twist GlobalTheory.ConjSeq

theorem pull_frobDR (p : ℕ) [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hR : (p : R) = 0) (hR' : (p : R') = 0) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')}
    [GrpObj A'] {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ)
    (c : primDR A) :
    (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (frobDR p R hR A c) =
      frobDR p R' hR' A' ((GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull c) := by
  have k := (frobMor p R hR A (cast_left p R hR A)).comp (GlobalTheory.Published.AbelianDeRham.bcMor hφ)
  refine (GrpMor.pull_pull _ _ k (fun _ ↦ rfl) rfl c).trans
    (GrpMor.pull_pull _ _ k (fun r ↦ ?_) (GlobalTheory.VB.frob_naturality p _ φ _) c).symm
  rw [RingHom.comp_apply, frobR_apply, frobR_apply, map_pow]

theorem frobDR_smul (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A : Over (Sp R)} [GrpObj A] (r : R) (c : primDR A) :
    frobDR p R hR A (r • c) = r ^ p • frobDR p R hR A c := by
  rw [LinearMap.map_smulₛₗ, frobR_apply]

theorem exists_adjoint {X Y : Scheme.{0}} (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (i : G ⟶ (Scheme.Modules.pushforward f).obj F) :
    ∃ Ψ : (Scheme.Modules.pullback f).obj G ⟶ F, ∀ (U : X.Opens) (V : Y.Opens) (h : U ≤ f ⁻¹ᵁ V)
      (s : Γ(G, V)), Ψ.app U (GlobalTheory.QCoh.pullbackSections f G h s) =
        resM F h (show Γ(F, f ⁻¹ᵁ V) from i.app V s) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  refine ⟨(adj.homEquiv _ _).symm i, fun U V h s => ?_⟩
  have h1 : adj.unit.app G ≫ (Scheme.Modules.pushforward f).map ((adj.homEquiv _ _).symm i) = i :=
    (adj.homEquiv_unit ..).symm.trans ((adj.homEquiv _ _).apply_symm_apply i)
  refine (app_resM ((adj.homEquiv _ _).symm i) h _).trans (congrArg (resM F h) ?_)
  exact congr(($h1).app V s)

theorem exists_of_semilinear (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} (h0 : (p : Γ(T, ⊤)) = 0)
    (H : T.Modules) (f : ∀ V : T.Opens, IsAffineOpen V → Γ(H, V) → Γ(H, V))
    (hadd : ∀ V hV s t, f V hV (s + t) = f V hV s + f V hV t)
    (hsmul : ∀ V hV (r : Γ(T, V)) s, f V hV (r • s) = r ^ p • f V hV s)
    (hres : ∀ V V' hV hV' (h : V' ≤ V) s, f V' hV' (resM H h s) = resM H h (f V hV s)) :
    ∃ Ψ : (GlobalTheory.VB.frobPull p h0).obj H ⟶ H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      Ψ.app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p h0) H (le_refl V) s) = f V hV s := by
  let G : T.Modules := (Scheme.Modules.pushforward (GlobalTheory.VB.frob T p h0)).obj H
  let j : ∀ V : T.Opens, IsAffineOpen V → Γ(H, V) →ₗ[Γ(T, V)] Γ(G, V) := fun V hV =>
    { toFun := f V hV
      map_add' := hadd V hV
      map_smul' := fun r s => by
        refine (hsmul V hV r s).trans ?_
        rw [← GlobalTheory.VB.frob_app p h0 V r]
        rfl }
  obtain ⟨i, hi⟩ := GlobalTheory.hom_of_affine_compatible T H G j hres
  obtain ⟨Ψ, hΨ⟩ := exists_adjoint (GlobalTheory.VB.frob T p h0) i
  refine ⟨Ψ, fun V hV s => (hΨ V V (le_refl V) s).trans ?_⟩
  refine (resM_self (F := H) (le_refl V) _).trans ?_
  exact LinearMap.congr_fun (hi V hV) s

theorem frobDR_res (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} (h0 : (p : Γ(T, ⊤)) = 0) (A : Over T)
    [GrpObj A] (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (he : IsDRIso A H e) {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s : Γ(H, V)) :
    (e V' hV').symm (frobDR p Γ(T, V') (GlobalTheory.SS.FrobField.cast_zero h0 V') (onAff A hV')
      (e V' hV' (resM H h s))) =
    resM H h ((e V hV).symm (frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero h0 V) (onAff A hV)
      (e V hV s))) := by
  letI := resAlg h
  obtain ⟨φ, hφ, hφ'⟩ := VB.exists_transition A hV hV' h
  have a := he V V' hV hV' h φ hφ hφ'
  refine (e V' hV').symm_apply_eq.2 (Eq.trans ?_ (a _).symm)
  refine (congrArg (frobDR p Γ(T, V') (GlobalTheory.SS.FrobField.cast_zero h0 V') (onAff A hV'))
    (a s)).trans ?_
  refine (pull_frobDR p (GlobalTheory.SS.FrobField.cast_zero h0 V) _ hφ _).symm.trans ?_
  exact congrArg (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull ((e V hV).apply_symm_apply _).symm

theorem exists_linFrob : GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ Ψ : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj H ⟶ H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      e V hV ((Ψ).app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))) H
        (le_refl V) s)) =
      GlobalTheory.ConjSeq.frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V)
        (onAff A hV) (e V hV s) := by
  intro _ p _ T _ A _ g _ _ H e he
  have key : ∀ h0 : (p : Γ(T, ⊤)) = 0, ∃ Ψ : (GlobalTheory.VB.frobPull p h0).obj H ⟶ H,
      ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
        Ψ.app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p h0) H (le_refl V) s) =
          (e V hV).symm (frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero h0 V) (onAff A hV)
            (e V hV s)) := fun h0 => by
    refine exists_of_semilinear p h0 H _ (fun V hV s t => ?_) (fun V hV r s => ?_)
      fun V V' hV hV' h s => ?_
    · rw [map_add, map_add, map_add]
    · rw [(e V hV).map_smul, frobDR_smul, (e V hV).symm.map_smul]
    · exact frobDR_res p h0 A H e he hV hV' h s
  obtain ⟨Ψ, hΨ⟩ := key (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))
  exact ⟨Ψ, fun V hV s => (congrArg (e V hV) (hΨ V hV s)).trans ((e V hV).apply_symm_apply _)⟩

end GlobalTheory.LinFrob
