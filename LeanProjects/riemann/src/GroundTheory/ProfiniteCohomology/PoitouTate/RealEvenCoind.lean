import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealAbstract
import GroundTheory.ProfiniteCohomology.PoitouTate.RealCup
import GroundTheory.ProfiniteCohomology.RealPlaces.Induced
import GroundTheory.ProfiniteCohomology.RealPlaces.DevissageNatural
import GroundTheory.ProfiniteCohomology.PoincarePairs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCores
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {κ : Type} {F : κ → Type} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (U : OpenSubgroup G) (hU : FreeOnCosets ψ (U : Subgroup G))

section Shapiro

theorem tateCoindIso_tateCompactCupRes {N₁ N₂ N₃ : Rep (ULift.{0} ℤ) (U : Subgroup G)} [IsDiscreteRep N₁]
    [IsDiscreteRep N₂] [IsDiscreteRep N₃] (μ : N₁ ⊗ N₂ ⟶ N₃) {a r b : ℕ} (h : (a + 1) + r = b + 1)
    (y : tateCompactCohomologyRes φ ψ (Rep.coind (U : Subgroup G).subtype N₁) (a + 1))
    (x : cohomology (Rep.coind (U : Subgroup G).subtype N₂) r) :
    (tateCoindIso φ ψ U N₃ hU b).hom.hom (tateCompactCupRes φ ψ (coindPairing (U : Subgroup G) μ) h y x) =
      compactCupRes (mackeyFamily U φ) μ h ((tateCoindIso φ ψ U N₁ hU a).hom.hom y)
        ((shapiroMap U N₂ r).hom x) := by
  rw [tateCoindIso_hom, tateCoindIso_hom]
  change (mackeyCompactCohomologyIso U φ N₃ (b + 1)).hom.hom
      ((tateForget φ ψ _ _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) (b + 1)).hom
        (tateCompactCupRes φ ψ (coindPairing (U : Subgroup G) μ) h y x)) =
    compactCupRes (mackeyFamily U φ) μ h ((mackeyCompactCohomologyIso U φ N₁ (a + 1)).hom.hom
      ((tateForget φ ψ _ _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) (a + 1)).hom y)) ((shapiroMap U N₂ r).hom x)
  rw [tateForget_tateCompactCupRes]
  exact mackeyCompactCohomologyIso_compactCupRes U φ μ h _ x

theorem tateCompactCores_tateCoindIso_hom (A : Rep (ULift.{0} ℤ) G) [IsDiscreteRep A] (b : ℕ)
    (W : tateCompactCohomologyRes φ ψ
      (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) (b + 1)) :
    (tateCompactCores φ ψ U hU A b).hom
        ((tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).hom.hom W) =
      (tateCompactCohomologyResMap φ ψ (coindTrace (U : Subgroup G) A) (b + 1)).hom W := by
  change (tateCompactCohomologyResMap φ ψ (coindTrace (U : Subgroup G) A) (b + 1)).hom
    ((tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).inv.hom
      ((tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).hom.hom W)) = _
  rw [hom_apply_hom_apply_of_comp_eq (tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU b).hom_inv_id W]
  rfl

end Shapiro

section Coind

variable {n : ℕ} [NeZero n] {D : Rep (ULift.{0} ℤ) G} [IsDiscreteRep D] (hD : ∀ d : D, n • d = 0)

def tateCoindDualCompactMap (s : ℕ) :
    tateCompactCohomologyRes φ ψ
        (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) (s + 1) →+
      compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) (s + 1) :=
  ((compactCohomologyResMap (mackeyFamily U φ)
      (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (s + 1)).hom.comp
    (((tateCoindIso φ ψ U
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom).comp
      (tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom)).toAddMonoidHom

theorem tateCoindDualCompactMap_apply (s : ℕ)
    (y : tateCompactCohomologyRes φ ψ
      (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) (s + 1)) :
    tateCoindDualCompactMap φ ψ U hU hD s y =
      (compactCohomologyResMap (mackeyFamily U φ)
        (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (s + 1)).hom
        ((tateCoindIso φ ψ U
          (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom
          ((tateCompactCohomologyResMap φ ψ
            (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y)) :=
  rfl

theorem bijective_tateCoindDualCompactMap (s : ℕ) :
    Function.Bijective (tateCoindDualCompactMap φ ψ U hU hD s) := by
  have h1 := bijective_compactCohomologyResMap_of_comp_eq_id (mackeyFamily U φ)
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).inv (Iso.hom_inv_id _)
    (Iso.inv_hom_id _) (s + 1)
  have h2 : Function.Bijective (tateCoindIso φ ψ U
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom :=
    Function.bijective_iff_has_inverse.2 ⟨(tateCoindIso φ ψ U _ hU s).inv.hom,
      fun w => hom_apply_hom_apply_of_comp_eq (tateCoindIso φ ψ U _ hU s).hom_inv_id w,
      fun w => hom_apply_hom_apply_of_comp_eq (tateCoindIso φ ψ U _ hU s).inv_hom_id w⟩
  have h3 := bijective_tateCompactCohomologyResMap_of_comp_eq_id φ ψ
    (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D)
    (coindDualHom (U : Subgroup G) (ULift.{0} (ZMod n)) D)
    (coindDualInv_comp_coindDualHom _ _ _) (coindDualHom_comp_coindDualInv _ _ _) (s + 1)
  exact h1.comp (h2.comp h3)

abbrev tateCoresTrace (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) :
    compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) 3 →+ ZMod n :=
  t.comp (tateCompactCores φ ψ U hU D 2).hom.toAddMonoidHom

theorem tateCompactDualityMap_coind (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) {r s : ℕ}
    (h : r + (s + 1) = 3)
    (x : cohomology (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n)) r)
    (y : tateCompactCohomologyRes φ ψ
      (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) (s + 1)) :
    tateCompactDualityMap φ ψ D h t
        (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n)) x y =
      compactZmodDualityMap (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) hD
        (tateCoresTrace φ ψ U hU t) h ((shapiroMap U (zmodRep.{0} (U : Subgroup G) n) r).hom x)
        (tateCoindDualCompactMap φ ψ U hU hD s y) := by
  have hy : (tateCompactCohomologyResMap φ ψ (coindDualHom (U : Subgroup G) (ULift.{0} (ZMod n)) D)
      (s + 1)).hom ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y) = y := by
    rw [← ConcreteCategory.comp_apply, ← tateCompactCohomologyResMap_comp,
      coindDualInv_comp_coindDualHom, tateCompactCohomologyResMap_id]
    rfl
  have e1 := compactCupRes_compactCohomologyResMap (mackeyFamily U φ)
    (zmodMulPairingRight n (Rep.res (U : Subgroup G).subtype D) hD)
    (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n))
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (𝟙 _)
    (by rw [tensorHom_zmodDualIso_zmodMulPairingRight, MonoidalCategory.id_tensorHom_id,
      Category.id_comp]) ((Nat.add_comm (s + 1) r).trans h)
    ((tateCoindIso φ ψ U
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)) hU s).hom.hom
      ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y))
    ((shapiroMap U (zmodRep.{0} (U : Subgroup G) n) r).hom x)
  rw [cohomologyMap_id, ModuleCat.hom_id, LinearMap.id_apply] at e1
  have e2 := tateCoindIso_tateCompactCupRes φ ψ U hU
    (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n))
    (b := 2) ((Nat.add_comm (s + 1) r).trans h)
    ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y) x
  have e3 := tateCompactCores_tateCoindIso_hom φ ψ U hU D 2
    (tateCompactCupRes φ ψ (coindPairing (U : Subgroup G)
      (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{0} (U : Subgroup G) n)))
      ((Nat.add_comm (s + 1) r).trans h)
      ((tateCompactCohomologyResMap φ ψ
        (coindDualInv (U : Subgroup G) (ULift.{0} (ZMod n)) D) (s + 1)).hom y) x)
  rw [tateCompactDualityMap_apply, compactZmodDualityMap_apply, tateCoindDualCompactMap_apply, e1, ← e2]
  refine Eq.trans (congrArg t ?_) (congrArg t e3).symm
  conv_lhs => rw [← hy]
  rw [tateCompactCupRes_tateCompactCohomologyResMap φ ψ _
    ((coindDualHom (U : Subgroup G) (ULift.{0} (ZMod n)) D ⊗ₘ
      𝟙 (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) ≫
      dualEvalPairing D (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n)))
    _ (𝟙 _) (by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]), cohomologyMap_id,
    tensorHom_coindDualHom_dualEvalPairing, ← tateCompactCohomologyResMap_tateCompactCupRes]
  rfl

theorem bijective_tateCompactDualityMap_coind (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) {r s : ℕ}
    (h : r + (s + 1) = 3)
    (hb : Function.Bijective (compactZmodDualityMap (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D)
      hD (tateCoresTrace φ ψ U hU t) h)) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{0} (U : Subgroup G) n))) := by
  have hsh : Function.Bijective (shapiroMap U (zmodRep.{0} (U : Subgroup G) n) r) :=
    Function.bijective_iff_has_inverse.2 ⟨inv (shapiroMap U _ r), inv_shapiroMap_apply U r,
      shapiroMap_inv_apply U r⟩
  exact bijective_of_bijective_comp hb hsh (bijective_tateCoindDualCompactMap φ ψ U hU hD s)
    (tateCompactDualityMap_coind φ ψ U hU hD t h)

end Coind

section Cores

theorem surjective_tateCompactCores_three (D : Rep (ULift.{0} ℤ) G) [IsDiscreteRep D] [Finite D] {n : ℕ}
    (hD : ∀ d : D, n • d = 0)
    (hV : ∀ (M : Rep (ULift.{0} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Subsingleton (tateCompactCohomologyRes φ ψ M 4)) :
    Function.Surjective (tateCompactCores φ ψ U hU D 2).hom := by
  have hS := coindTraceShortComplex_shortExact (U : Subgroup G) D
  have : IsDiscreteRep (coindTraceShortComplex (U : Subgroup G) D).X₂ :=
    inferInstanceAs (IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype D)))
  have : IsDiscreteRep (coindTraceShortComplex (U : Subgroup G) D).X₁ :=
    isDiscreteRep_subrepresentation _ _ _
  have : IsDiscreteRep (coindTraceShortComplex (U : Subgroup G) D).X₃ := inferInstanceAs (IsDiscreteRep D)
  have : Finite (Rep.res (U : Subgroup G).subtype D) := inferInstanceAs (Finite D)
  have : Finite (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype D)) :=
    finite_coind U _
  have : Finite (coindTraceShortComplex (U : Subgroup G) D).X₁ :=
    inferInstanceAs (Finite (coindTraceKer (U : Subgroup G) D))
  have hN : ∀ m : (coindTraceShortComplex (U : Subgroup G) D).X₁, n • m = 0 := fun m =>
    Subtype.ext (Subtype.ext (funext fun x => hD _))
  have h4 := hV _ hN
  have hg : Function.Surjective
      (tateCompactCohomologyResMap φ ψ (coindTrace (U : Subgroup G) D) 3).hom := fun y =>
    (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (tateCompactRes_exact₃ φ ψ hS 3)
      (@Subsingleton.elim _ h4 _ _)
  intro y
  refine (hg y).elim fun x hx => ⟨(tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype D) hU 2).hom.hom x, ?_⟩
  exact (tateCompactCores_tateCoindIso_hom φ ψ U hU D 2 x).trans hx

end Cores

end GroundTheory.ProfCoh
