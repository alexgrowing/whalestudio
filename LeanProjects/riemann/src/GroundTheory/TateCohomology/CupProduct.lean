import Mathlib
import GroundTheory.TateCohomology.CupCochains
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits

namespace GroundTheory.GroupCoh

variable {k G : Type u} [CommRing k] [Group G]

section Cocycles

variable {A B : Rep k G} {p q n : ℕ}

theorem cocycles_ext {z z' : cocycles A n} (h : iCocycles A n z = iCocycles A n z') : z = z' :=
  (ModuleCat.mono_iff_injective _).1 inferInstance h

theorem d_iCocycles (z : cocycles A n) :
    (inhomogeneousCochains.d A n).hom (iCocycles A n z) = 0 := by
  have h := congr(($((inhomogeneousCochains A).iCycles_d n (n + 1))).hom z)
  simpa using h

theorem iCocycles_toCocycles {m : ℕ} (y : (Fin m → G) → A) :
    iCocycles A (m + 1) (toCocycles A m (m + 1) y) = (inhomogeneousCochains.d A m).hom y := by
  change (toCocycles A m (m + 1) ≫ iCocycles A (m + 1)).hom y = _
  rw [HomologicalComplex.toCycles_i]
  simp

theorem toCocycles_eq_zero {i : ℕ} (h : i + 1 ≠ n) : toCocycles A i n = 0 :=
  (inhomogeneousCochains A).toCycles_eq_zero (by simpa using h)

theorem π_eq_zero_of_eq_d {m : ℕ} (z : cocycles A (m + 1)) (y : (Fin m → G) → A)
    (hz : iCocycles A (m + 1) z = (inhomogeneousCochains.d A m).hom y) :
    π A (m + 1) z = 0 := by
  have : z = toCocycles A m (m + 1) y := cocycles_ext (by rw [hz, iCocycles_toCocycles])
  subst this
  exact congr(($((inhomogeneousCochains A).toCycles_comp_homologyπ m (m + 1))).hom y)

def descH {M : Type u} [AddCommGroup M] [Module k M] (φ : cocycles A n →ₗ[k] M)
    (hφ : ∀ (i : ℕ) (y : (Fin i → G) → A), φ (toCocycles A i n y) = 0) :
    groupCohomology A n →ₗ[k] M :=
  (((inhomogeneousCochains A).homologyIsCokernel _ n rfl).desc
    (CokernelCofork.ofπ (Z := ModuleCat.of k M) (ModuleCat.ofHom φ)
      (by ext y; exact hφ _ y))).hom

theorem descH_π {M : Type u} [AddCommGroup M] [Module k M] (φ : cocycles A n →ₗ[k] M)
    (hφ : ∀ (i : ℕ) (y : (Fin i → G) → A), φ (toCocycles A i n y) = 0) (z : cocycles A n) :
    descH φ hφ (π A n z) = φ z :=
  congr(($(((inhomogeneousCochains A).homologyIsCokernel _ n rfl).fac
    (CokernelCofork.ofπ (Z := ModuleCat.of k M) (ModuleCat.ofHom φ)
      (by ext y; exact hφ _ y)) WalkingParallelPair.one)).hom z)

theorem linearMap_ext {M : Type u} [AddCommGroup M] [Module k M]
    {φ ψ : groupCohomology A n →ₗ[k] M} (h : ∀ z : cocycles A n, φ (π A n z) = ψ (π A n z)) :
    φ = ψ :=
  LinearMap.ext fun x => groupCohomology_induction_on x h

theorem cupCochain_zero_left (h : p + q = n) (g : (Fin q → G) → B) :
    cupCochain h (0 : (Fin p → G) → A) g = 0 :=
  (cupₗ h).map_zero₂ g

theorem cupCochain_zero_right (h : p + q = n) (f : (Fin p → G) → A) :
    cupCochain h f (0 : (Fin q → G) → B) = 0 :=
  (cupₗ h f).map_zero

theorem d_cupCochain_iCocycles (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    (inhomogeneousCochains.d (A ⊗ B) n).hom (cupCochain h (iCocycles A p z) (iCocycles B q w)) =
      0 := by
  rw [d_cupCochain, d_iCocycles, d_iCocycles, cupCochain_zero_left, cupCochain_zero_right,
    smul_zero, add_zero]

def cupCocycle (h : p + q = n) (z : cocycles A p) (w : cocycles B q) : cocycles (A ⊗ B) n :=
  cocyclesMk (cupCochain h (iCocycles A p z) (iCocycles B q w)) (d_cupCochain_iCocycles h z w)

theorem iCocycles_cupCocycle (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    iCocycles (A ⊗ B) n (cupCocycle h z w) = cupCochain h (iCocycles A p z) (iCocycles B q w) :=
  iCocycles_mk _ (d_cupCochain_iCocycles h z w)

def cupCocycles (h : p + q = n) : cocycles A p →ₗ[k] cocycles B q →ₗ[k] cocycles (A ⊗ B) n :=
  LinearMap.mk₂ k (cupCocycle h)
    (fun z z' w => cocycles_ext (by
      rw [map_add, iCocycles_cupCocycle, iCocycles_cupCocycle, iCocycles_cupCocycle, map_add]
      exact (cupₗ h).map_add₂ _ _ _))
    (fun c z w => cocycles_ext (by
      rw [map_smul, iCocycles_cupCocycle, iCocycles_cupCocycle, map_smul]
      exact (cupₗ h).map_smul₂ _ _ _))
    (fun z w w' => cocycles_ext (by
      rw [map_add, iCocycles_cupCocycle, iCocycles_cupCocycle, iCocycles_cupCocycle, map_add]
      exact (cupₗ h _).map_add _ _))
    (fun c z w => cocycles_ext (by
      rw [map_smul, iCocycles_cupCocycle, iCocycles_cupCocycle, map_smul]
      exact (cupₗ h _).map_smul _ _))

theorem iCocycles_cupCocycles (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    iCocycles (A ⊗ B) n (cupCocycles h z w) = cupCochain h (iCocycles A p z) (iCocycles B q w) :=
  iCocycles_cupCocycle h z w

end Cocycles

section Cohomology

variable {A B : Rep k G} {p q n : ℕ}

theorem π_cupCocycles_toCocycles_right (h : p + q = n) (z : cocycles A p) (i : ℕ)
    (y : (Fin i → G) → B) : π (A ⊗ B) n (cupCocycles h z (toCocycles B i q y)) = 0 := by
  by_cases hi : i + 1 = q
  · subst hi
    obtain rfl : n = p + i + 1 := by omega
    refine π_eq_zero_of_eq_d _ ((-1 : k) ^ p • cupCochain rfl (iCocycles A p z) y) ?_
    rw [map_smul, d_cupCochain, d_iCocycles, cupCochain_zero_left, zero_add, smul_smul, ← pow_add,
      ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul, iCocycles_cupCocycles,
      iCocycles_toCocycles]
  · simp [toCocycles_eq_zero hi]

theorem π_cupCocycles_toCocycles_left (h : p + q = n) (i : ℕ) (y : (Fin i → G) → A)
    (w : cocycles B q) : π (A ⊗ B) n (cupCocycles h (toCocycles A i p y) w) = 0 := by
  by_cases hi : i + 1 = p
  · subst hi
    obtain rfl : n = i + q + 1 := by omega
    refine π_eq_zero_of_eq_d _ (cupCochain rfl y (iCocycles B q w)) ?_
    rw [d_cupCochain, d_iCocycles, cupCochain_zero_right, smul_zero, add_zero,
      iCocycles_cupCocycles, iCocycles_toCocycles]
  · simp [toCocycles_eq_zero hi]

def cupHLeft (h : p + q = n) (z : cocycles A p) :
    groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) n :=
  descH ((π (A ⊗ B) n).hom ∘ₗ cupCocycles h z) (π_cupCocycles_toCocycles_right h z)

theorem cupHLeft_π (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    cupHLeft h z (π B q w) = π (A ⊗ B) n (cupCocycles h z w) :=
  descH_π _ _ w

def cupH (h : p + q = n) :
    groupCohomology A p →ₗ[k] groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) n :=
  descH
    { toFun := cupHLeft h
      map_add' := fun z z' => linearMap_ext fun w => by
        rw [LinearMap.add_apply, cupHLeft_π, cupHLeft_π, cupHLeft_π, map_add,
          LinearMap.add_apply, map_add]
      map_smul' := fun c z => linearMap_ext fun w => by
        rw [LinearMap.smul_apply, cupHLeft_π, cupHLeft_π, map_smul, LinearMap.smul_apply,
          map_smul, RingHom.id_apply] }
    (fun i y => linearMap_ext fun w => by
      show cupHLeft h (toCocycles A i p y) (π B q w) = 0
      rw [cupHLeft_π, π_cupCocycles_toCocycles_left])

theorem cupH_π (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    cupH h (π A p z) (π B q w) = π (A ⊗ B) n (cupCocycles h z w) := by
  rw [cupH, descH_π]
  exact cupHLeft_π h z w

variable (A B p q) in

def cupTensor :
    groupCohomology A p ⊗[k] groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) (p + q) :=
  TensorProduct.lift (cupH rfl)

variable (A B p q) in

def cup : groupCohomology A p ⊗ groupCohomology B q ⟶ groupCohomology (A ⊗ B) (p + q) :=
  ModuleCat.ofHom (cupTensor A B p q)

theorem map_π_apply {A' : Rep k G} (φ : A ⟶ A') (z : cocycles A n) :
    map (MonoidHom.id G) φ n (π A n z) = π A' n (cocyclesMap (MonoidHom.id G) φ n z) := by
  change (π A n ≫ map (MonoidHom.id G) φ n).hom z =
    (cocyclesMap (MonoidHom.id G) φ n ≫ π A' n).hom z
  rw [π_map]

theorem iCocycles_cocyclesMap {A' : Rep k G} (φ : A ⟶ A') (z : cocycles A n) :
    iCocycles A' n (cocyclesMap (MonoidHom.id G) φ n z) =
      fun x => φ.hom (iCocycles A n z x) := by
  change (cocyclesMap (MonoidHom.id G) φ n ≫ iCocycles A' n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

theorem map_cupH {A' B' : Rep k G} (φ : A ⟶ A') (ψ : B ⟶ B') (h : p + q = n)
    (a : groupCohomology A p) (b : groupCohomology B q) :
    map (MonoidHom.id G) (φ ⊗ₘ ψ) n (cupH h a b) =
      cupH h (map (MonoidHom.id G) φ p a) (map (MonoidHom.id G) ψ q b) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  have key : cocyclesMap (A := A ⊗ B) (MonoidHom.id G) (φ ⊗ₘ ψ) n (cupCocycles h z w) =
      cupCocycles h (cocyclesMap (MonoidHom.id G) φ p z) (cocyclesMap (MonoidHom.id G) ψ q w) := by
    refine cocycles_ext ?_
    rw [iCocycles_cocyclesMap, iCocycles_cupCocycles, iCocycles_cupCocycles, iCocycles_cocyclesMap,
      iCocycles_cocyclesMap]
    funext x
    exact tensorHom_cupCochain φ ψ h _ _ x
  rw [cupH_π, map_π_apply, map_π_apply, cupH_π, ← key]
  exact map_π_apply _ _

theorem d_oneCochain :
    (inhomogeneousCochains.d (𝟙_ (Rep k G)) 0).hom (oneCochain (k := k) (G := G)) = 0 := by
  funext x
  simp [inhomogeneousCochains.d_hom_apply, oneCochain]
  rfl

variable (k G) in

def oneClass : groupCohomology (𝟙_ (Rep k G)) 0 :=
  π _ 0 (cocyclesMk oneCochain d_oneCochain)

end Cohomology

end GroundTheory.GroupCoh
