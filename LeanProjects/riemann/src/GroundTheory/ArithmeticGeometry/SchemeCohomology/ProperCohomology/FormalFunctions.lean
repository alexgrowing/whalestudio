import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalVanish
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalCompare
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

theorem exists_finite_affineCover (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated] :
    ∃ (ι : Type u) (_ : Finite ι) (𝔘 : ι → X.Opens), iSup 𝔘 = ⊤ ∧
      ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a)) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => (V : Set X))
    (fun V => V.1.isOpen) (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩)
  refine ⟨s, inferInstance, fun V => V.1.1, ?_, fun m t => IsAffineOpen.iInf fun a => (t a).1.2⟩
  apply le_antisymm le_top
  intro x _
  obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨⟨V, hV⟩, hx⟩

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules}

lemma isSeparated_of_over [IsSeparated (X ↘ Spec (.of A))] : X.IsSeparated := by
  refine ⟨?_⟩
  rw [show terminal.from X = (X ↘ Spec (.of A)) ≫ terminal.from _ from terminal.hom_ext _ _]
  infer_instance

lemma cechK_succ_le {ι : Type u} (𝔘 : ι → X.Opens) (p n : ℕ) :
    cechK I 𝔘 p (F := F) (n + 1) ≤ cechK I 𝔘 p n := by
  rintro _ ⟨z, rfl⟩
  refine ⟨cechH.linearMap 𝔘 A (idealPowSucc I F n) p z, ?_⟩
  have h := congrArg (fun f => f.hom) (show modulesAbMap (idealPowSucc I F n) ≫
      modulesAbMap (idealPowι I F n) = modulesAbMap (idealPowι I F (n + 1)) by
    rw [← modulesAbMap_comp, idealPowSucc_ι])
  change cechHMap 𝔘 (modulesAbMap (idealPowι I F n)).hom p
      (cechHMap 𝔘 (modulesAbMap (idealPowSucc I F n)).hom p z) =
    cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + 1))).hom p z
  rw [← cechHMap_comp]
  exact congrArg (fun f => cechHMap 𝔘 f p z) h

lemma towerComp_formalτQ_val (q n : ℕ) : ∀ (c : ℕ) (y : formalQ I F q (n + c)),
    ((towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c y : formalQ I F q n) :
      Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) =
      H.linearMap A (transMap I F n c) (q + 1) y
  | 0, y => by
    change (y : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) =
      H.linearMap A (𝟙 _) (q + 1) y
    rw [H.linearMap_id]
    rfl
  | c + 1, y => by
    change ((towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c
      (formalτQ I F q (n + c) y) : formalQ I F q n) : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) = _
    rw [towerComp_formalτQ_val q n c, transMap, H.linearMap_comp]
    rfl

variable [IsProper (X ↘ Spec (.of A))] (hF : IsCoherent F)

include hF in
lemma exists_formalK_le (q : ℕ) : ∃ c, ∀ n, formalK I F q (n + c) ≤
    I ^ n • (⊤ : Submodule A (Sheaf.H.{u} (modulesAb F) q)) := by
  have := hF.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have := isSeparated_of_over (A := A) (X := X)
  obtain ⟨ι, _, 𝔘, hUtop, hU⟩ := exists_finite_affineCover X
  obtain ⟨c, hc⟩ := exists_cechK_eq_pow_smul I hF 𝔘 hU q hUtop
  refine ⟨c, fun n => ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨zČ, rfl⟩ := (cechHLinearEquivH 𝔘 hUtop hU A (idealPow I F (n + c + 1)) q).surjective z
  rw [formalα, ← cechHLinearEquivH_naturality]
  have h2 := cechK_succ_le I 𝔘 q (n + c) (F := F) ⟨zČ, rfl⟩
  rw [hc n] at h2
  have hmem : cechH.linearMap 𝔘 A (idealPowι I F (n + c + 1)) q zČ ∈
      I ^ n • (⊤ : Submodule A (cechH (modulesAb F).obj 𝔘 q)) :=
    Submodule.smul_mono le_rfl le_top h2
  refine Submodule.smul_induction_on hmem (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul ha trivial
  · rw [map_add]
    exact add_mem hy hy'

include hF in
lemma exists_towerComp_formalτQ_eq_zero (q : ℕ) :
    ∃ c, ∀ n, towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c = 0 := by
  have := hF.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have := isSeparated_of_over (A := A) (X := X)
  obtain ⟨ι, _, 𝔘, hUtop, hU⟩ := exists_finite_affineCover X
  obtain ⟨c, hc⟩ := exists_transMap_eq_zero I hF 𝔘 hU (q + 1) hUtop
  refine ⟨c, fun n => LinearMap.ext fun y => Subtype.ext ?_⟩
  rw [towerComp_formalτQ_val, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  obtain ⟨x, hx⟩ := y.2
  obtain ⟨yČ, hyČ⟩ :=
    (cechHLinearEquivH 𝔘 hUtop hU A (idealPow I F (n + c + 1)) (q + 1)).surjective y.1
  have hι : cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + c + 1))).hom (q + 1) yČ = 0 := by
    apply (cechHLinearEquivH 𝔘 hUtop hU A F (q + 1)).injective
    rw [map_zero]
    change cechHLinearEquivH 𝔘 hUtop hU A F (q + 1)
      (cechH.linearMap 𝔘 A (idealPowι I F (n + c + 1)) (q + 1) yČ) = 0
    rw [cechHLinearEquivH_naturality, hyČ, ← hx]
    exact H.map_f_δ (shortExact_abSC_quotPow I F (n + c)) rfl x
  rw [← hyČ, ← cechHLinearEquivH_naturality]
  change cechHLinearEquivH 𝔘 hUtop hU A (idealPow I F (n + 1)) (q + 1)
    (cechHMap 𝔘 (modulesAbMap (transMap I F n c)).hom (q + 1) yČ) = 0
  rw [hc n yČ hι, map_zero]

include hF in

theorem formalFunctions_mem_range (q : ℕ) {x : ∀ n, Sheaf.H.{u} (modulesAb (quotPow I F n)) q}
    (hx : x ∈ towerLimit (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q)
      (formalτE I F q)) (n : ℕ) : x n ∈ LinearMap.range (formalβ I F q n) := by
  obtain ⟨c, hc⟩ := exists_towerComp_formalτQ_eq_zero I hF q
  exact mem_range_formalβ_of_mem_towerLimit hc hx n

end

end GroundTheory.Arith.SchemeCoh
