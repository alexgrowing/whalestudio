import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
open GlobalTheory.Twist (resM resM_resM app_resM)
open GlobalTheory.PtNorm (homPi homPi_apply homPi_res isFiniteQC_homMod)

namespace GlobalTheory.HomExact

variable {X : Scheme.{0}}

theorem homPi_homMap {E F G : X.Modules} {U V : X.Opens} {ι : Type} [Fintype ι] {e : ι → Γ(E, U)}
    (he : IsFrame e) (h : V ≤ U) (β : F ⟶ G) (ψ : Γ(homMod E F, V)) (i : ι) :
    homPi he h ((homMap (𝟙 E) β).app V ψ) i = β.app V (homPi he h ψ i) := rfl

theorem homMap_comp_zero (E : X.Modules) (S : ShortComplex X.Modules) :
    homMap (𝟙 E) S.f ≫ homMap (𝟙 E) S.g = 0 := by
  ext V ψ : 3
  refine VB.hom_ext fun W h s => ?_
  change (S.f ≫ S.g).app W (homApp ψ h s) = 0
  rw [S.zero]
  rfl

theorem shortExact_homMod {E : X.Modules} {r : ℕ} (hE : IsVB E r) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (ShortComplex.mk (homMap (𝟙 E) S.f) (homMap (𝟙 E) S.g) (homMap_comp_zero E S)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' (DualExact.exact_of_locally _ fun V x hx => ?_)
    (QCoh.mono_of_locally_app_injective _ fun V x hx => ⟨V, hx, le_rfl, fun a b hab => ?_⟩)
    (QCoh.epi_of_locally_app_surjective _ fun V x hx => ?_)
  · obtain ⟨U, e, -, hxU, hle, he⟩ := hE.exists_affine hx
    refine ⟨U, hle, hxU, fun (t : Γ(homMod E S.X₂, U))
      (ht : (homMap (𝟙 E) S.g).app U t = 0) => ?_⟩
    have H (i : Fin r) : ∃ u, S.f.app U u = homPi he le_rfl t i :=
      (QCoh.exact_app_of_exact_of_mono hS.exact U _).1 (by
        rw [← homPi_homMap, ht, map_zero]; rfl)
    choose u hu using H
    refine ⟨(homPi he le_rfl).symm u, (homPi he le_rfl).injective (funext fun i => ?_)⟩
    rw [← hu]
    refine (homPi_homMap he le_rfl S.f _ i).trans ?_
    rw [LinearEquiv.apply_symm_apply]
  · refine VB.hom_ext fun W h s => QCoh.injective_app_of_mono S.f W ?_
    exact congrArg (fun ψ : Γ(homMod E S.X₂, V) => homApp ψ h s) hab
  · obtain ⟨U, e, hU, hxU, hle, he⟩ := hE.exists_affine hx
    refine ⟨U, hxU, hle, fun (t : Γ(homMod E S.X₃, U)) => ?_⟩
    choose u hu using fun i => QCoh.surjective_app_of_epi S.g hU (homPi he le_rfl t i)
    refine ⟨(homPi he le_rfl).symm u, (homPi he le_rfl).injective (funext fun i => ?_)⟩
    rw [← hu]
    refine (homPi_homMap he le_rfl S.g _ i).trans ?_
    rw [LinearEquiv.apply_symm_apply]

theorem chi_shortExact_mk (k : Type) [Field k] [Algebra k Γ(X, ⊤)] {F G H : X.Modules}
    {f : F ⟶ G} {g : G ⟶ H} {w : f ≫ g = 0} (hS : (ShortComplex.mk f g w).ShortExact)
    (h₁ : FiniteCoh k F) (h₃ : FiniteCoh k H) : chi k G = chi k F + chi k H := by
  have := chi_shortExact (k := k) hS h₁ h₃
  exact this

theorem chi_homMod_shortExact : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E r → ∀ (S : ShortComplex T.Modules), S.ShortExact → QCoh.IsFiniteQC S.X₁ → QCoh.IsFiniteQC S.X₂ → QCoh.IsFiniteQC S.X₃ → chi k (homMod E S.X₂) = chi k (homMod E S.X₁) + chi k (homMod E S.X₃) := by
  intro k _ T _ _ hT E r hE S hS h₁ h₂ h₃
  have i₁ : QCoh.IsFiniteQC (homMod E S.X₁) := isFiniteQC_homMod hE
  have i₃ : QCoh.IsFiniteQC (homMod E S.X₃) := isFiniteQC_homMod hE
  have f₁ : FiniteCoh k (homMod E S.X₁) :=
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) _ hT.isProjOver
  have f₃ : FiniteCoh k (homMod E S.X₃) :=
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) _ hT.isProjOver
  have hx := shortExact_homMod hE S hS
  exact chi_shortExact_mk k hx f₁ f₃

end GlobalTheory.HomExact
