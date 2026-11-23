import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdealMul
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalLimit
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CohFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules) (q : ℕ)

abbrev formalα (n : ℕ) : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) q →ₗ[A]
    Sheaf.H.{u} (modulesAb F) q :=
  H.linearMap A (idealPowι I F (n + 1)) q

def formalK (n : ℕ) : Submodule A (Sheaf.H.{u} (modulesAb F) q) :=
  LinearMap.range (formalα I F q n)

lemma formalK_antitone : Antitone (formalK I F q) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨H.linearMap A (idealPowSucc I F (n + 1)) q x, ?_⟩
  change Sheaf.H.map.{u} (modulesAbMap (idealPowι I F (n + 1))) q
      (Sheaf.H.map.{u} (modulesAbMap (idealPowSucc I F (n + 1))) q x) =
    Sheaf.H.map.{u} (modulesAbMap (idealPowι I F (n + 1 + 1))) q x
  rw [← Sheaf.H.map_comp_apply, ← modulesAbMap_comp, idealPowSucc_ι]

abbrev formalβ (n : ℕ) : Sheaf.H.{u} (modulesAb F) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  H.linearMap A (quotPowπ I F n) q

abbrev formalτE (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F (n + 1))) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  H.linearMap A (quotPowMap I F n) q

lemma shortExact_abSC_quotPow (n : ℕ) : (abSC (quotPowSC I F n)).ShortExact :=
  shortExact_abSC (quotPowSC_shortExact I F n)

lemma ker_formalβ (n : ℕ) : LinearMap.ker (formalβ I F q n) = formalK I F q n := by
  ext h
  constructor
  · intro hh
    exact H.exact₂ (shortExact_abSC_quotPow I F n) h hh
  · rintro ⟨x, rfl⟩
    exact H.map_g_map_f (S := abSC (quotPowSC I F n)) x

abbrev formalδ (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F n)) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1) :=
  H.δLinear A (shortExact_abSC_quotPow I F n) q

def formalQ (n : ℕ) : Submodule A (Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) :=
  LinearMap.range (formalδ I F q n)

def formalι (n : ℕ) : (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q n) →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  (formalK I F q n).liftQ (formalβ I F q n) (ker_formalβ I F q n).ge

lemma formalι_mk (n : ℕ) (h : Sheaf.H.{u} (modulesAb F) q) :
    formalι I F q n (Submodule.Quotient.mk h) = formalβ I F q n h := rfl

lemma formalι_injective (n : ℕ) : Function.Injective (formalι I F q n) := by
  rw [← LinearMap.ker_eq_bot, formalι, Submodule.ker_liftQ, ker_formalβ, Submodule.mkQ_map_self]

def formalπ (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F n)) q →ₗ[A] formalQ I F q n :=
  (formalδ I F q n).rangeRestrict

lemma range_formalι (n : ℕ) :
    LinearMap.range (formalι I F q n) = LinearMap.ker (formalπ I F q n) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply Subtype.ext
    exact H.δ_map_g (shortExact_abSC_quotPow I F n) rfl h
  · intro hy
    have hy' : formalδ I F q n y = 0 := congrArg Subtype.val hy
    obtain ⟨h, rfl⟩ := H.exact₃ (shortExact_abSC_quotPow I F n) rfl y hy'
    exact ⟨Submodule.Quotient.mk h, rfl⟩

def abSCHom {S S' : ShortComplex X.Modules} (φ : S ⟶ S') : abSC S ⟶ abSC S' where
  τ₁ := modulesAbMap φ.τ₁
  τ₂ := modulesAbMap φ.τ₂
  τ₃ := modulesAbMap φ.τ₃
  comm₁₂ := by
    change modulesAbMap φ.τ₁ ≫ modulesAbMap S'.f = modulesAbMap S.f ≫ modulesAbMap φ.τ₂
    rw [← modulesAbMap_comp, ← modulesAbMap_comp, φ.comm₁₂]
  comm₂₃ := by
    change modulesAbMap φ.τ₂ ≫ modulesAbMap S'.g = modulesAbMap S.g ≫ modulesAbMap φ.τ₃
    rw [← modulesAbMap_comp, ← modulesAbMap_comp, φ.comm₂₃]

def quotPowSCMap (n : ℕ) : quotPowSC I F (n + 1) ⟶ quotPowSC I F n where
  τ₁ := idealPowSucc I F (n + 1)
  τ₂ := 𝟙 F
  τ₃ := quotPowMap I F n
  comm₁₂ := by
    change idealPowSucc I F (n + 1) ≫ idealPowι I F (n + 1) = idealPowι I F (n + 2) ≫ 𝟙 F
    rw [idealPowSucc_ι, Category.comp_id]
  comm₂₃ := by
    change 𝟙 F ≫ quotPowπ I F n = quotPowπ I F (n + 1) ≫ quotPowMap I F n
    rw [quotPowπ_map, Category.id_comp]

lemma formalδ_naturality (n : ℕ) (x : Sheaf.H.{u} (modulesAb (quotPow I F (n + 1))) q) :
    formalδ I F q n (formalτE I F q n x) =
      H.linearMap A (idealPowSucc I F (n + 1)) (q + 1) (formalδ I F q (n + 1) x) := by
  simp only [formalδ, formalτE, H.δLinear_apply, H.linearMap_apply]
  exact H.δ_naturality (shortExact_abSC_quotPow I F (n + 1)) (shortExact_abSC_quotPow I F n)
    (abSCHom (quotPowSCMap I F n)) q (q + 1) rfl x

end

end GroundTheory.Arith.SchemeCoh
