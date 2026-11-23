import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

lemma smulHom_comp_smulHom (F : X.Modules) (r s : Γ(X, ⊤)) :
    smulHom F r ≫ smulHom F s = smulHom F (r * s) := by
  ext U x
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, smulHom_app_apply, map_mul,
    mul_smul]
  rw [smul_comm]

lemma smulHom_sum (F : X.Modules) {ι : Type*} (s : Finset ι) (r : ι → Γ(X, ⊤)) :
    smulHom F (∑ i ∈ s, r i) = ∑ i ∈ s, smulHom F (r i) :=
  map_sum (smulRingHom F) r s

lemma smulHom_one (F : X.Modules) : smulHom F 1 = 𝟙 F := map_one (smulRingHom F)

def imageMapOf {P₁ P₂ G : X.Modules} (f₁ : P₁ ⟶ G) (f₂ : P₂ ⟶ G) (φ : G ⟶ G) (h : P₁ ⟶ P₂)
    (w : f₁ ≫ φ = h ≫ f₂) : kernel (cokernel.π f₁) ⟶ kernel (cokernel.π f₂) :=
  kernel.lift _ (kernel.ι _ ≫ φ) (by
    rw [Category.assoc]
    apply (cancel_epi (Abelian.factorThruImage f₁)).1
    rw [comp_zero, ← Category.assoc, ← Category.assoc]
    have hfac : Abelian.factorThruImage f₁ ≫ kernel.ι (cokernel.π f₁) = f₁ := Abelian.image.fac f₁
    rw [hfac, w, Category.assoc, cokernel.condition, comp_zero])

@[reassoc (attr := simp)]
lemma imageMapOf_ι {P₁ P₂ G : X.Modules} (f₁ : P₁ ⟶ G) (f₂ : P₂ ⟶ G) (φ : G ⟶ G) (h : P₁ ⟶ P₂)
    (w : f₁ ≫ φ = h ≫ f₂) : imageMapOf f₁ f₂ φ h w ≫ kernel.ι _ = kernel.ι _ ≫ φ :=
  kernel.lift_ι _ _ _

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [X.Over (Spec (.of A))]

attribute [local instance] algebraOfOver

section Generators

lemma exists_fin_generators (J : Ideal A) :
    ∃ (k : ℕ) (g : Fin k → A), Ideal.span (Set.range g) = J :=
  Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian J)

def idealGenNum (J : Ideal A) : ℕ := (exists_fin_generators J).choose

def idealGen (J : Ideal A) : Fin (idealGenNum J) → A := (exists_fin_generators J).choose_spec.choose

lemma span_idealGen (J : Ideal A) : Ideal.span (Set.range (idealGen J)) = J :=
  (exists_fin_generators J).choose_spec.choose_spec

lemma idealGen_mem (J : Ideal A) (i : Fin (idealGenNum J)) : idealGen J i ∈ J :=
  (span_idealGen J).le (Ideal.subset_span ⟨i, rfl⟩)

variable (F : X.Modules)

def idealSumMap (J : Ideal A) : (⨁ fun _ : Fin (idealGenNum J) => F) ⟶ F :=
  biproduct.desc fun k => smulHom F (algebraMap A Γ(X, ⊤) (idealGen J k))

lemma exists_idealSumMap_smulHom (J₁ J₂ : Ideal A) (a : A)
    (ha : ∀ i, a * idealGen J₁ i ∈ J₂) :
    ∃ h : (⨁ fun _ : Fin (idealGenNum J₁) => F) ⟶ (⨁ fun _ : Fin (idealGenNum J₂) => F),
      idealSumMap F J₁ ≫ smulHom F (algebraMap A Γ(X, ⊤) a) = h ≫ idealSumMap F J₂ := by
  have key : ∀ i, ∃ c : Fin (idealGenNum J₂) → A,
      ∑ j, c j * idealGen J₂ j = a * idealGen J₁ i := fun i => by
    have := ha i
    rw [← span_idealGen J₂] at this
    exact (Ideal.mem_span_range_iff_exists_fun).1 this
  choose c hc using key
  refine ⟨biproduct.desc fun i => biproduct.lift fun j => smulHom F (algebraMap A Γ(X, ⊤) (c i j)),
    ?_⟩
  apply biproduct.hom_ext'
  intro i
  simp only [idealSumMap, biproduct.ι_desc_assoc, biproduct.lift_desc, smulHom_comp_smulHom,
    ← map_mul, ← smulHom_sum, ← map_sum]
  rw [hc i, mul_comm]

end Generators

variable (I : Ideal A) (F : X.Modules)

abbrev idealPow (n : ℕ) : X.Modules := kernel (cokernel.π (idealSumMap F (I ^ n)))

abbrev idealPowι (n : ℕ) : idealPow I F n ⟶ F := kernel.ι _

def idealPowSucc (n : ℕ) : idealPow I F (n + 1) ⟶ idealPow I F n :=
  imageMapOf _ _ (smulHom F (algebraMap A Γ(X, ⊤) 1))
    (exists_idealSumMap_smulHom F (I ^ (n + 1)) (I ^ n) 1 fun i => by
      rw [one_mul]
      exact Ideal.pow_le_pow_right (Nat.le_succ n) (idealGen_mem _ i)).choose
    (exists_idealSumMap_smulHom F (I ^ (n + 1)) (I ^ n) 1 fun i => by
      rw [one_mul]
      exact Ideal.pow_le_pow_right (Nat.le_succ n) (idealGen_mem _ i)).choose_spec

@[reassoc (attr := simp)]
lemma idealPowSucc_ι (n : ℕ) : idealPowSucc I F n ≫ idealPowι I F n = idealPowι I F (n + 1) := by
  rw [idealPowSucc, imageMapOf_ι, map_one, smulHom_one, Category.comp_id]

def idealPowMul {k n : ℕ} (a : A) (ha : a ∈ I ^ k) : idealPow I F n ⟶ idealPow I F (n + k) :=
  imageMapOf _ _ (smulHom F (algebraMap A Γ(X, ⊤) a))
    (exists_idealSumMap_smulHom F (I ^ n) (I ^ (n + k)) a fun i => by
      have := Ideal.mul_mem_mul ha (idealGen_mem (I ^ n) i)
      rwa [← pow_add, add_comm] at this).choose
    (exists_idealSumMap_smulHom F (I ^ n) (I ^ (n + k)) a fun i => by
      have := Ideal.mul_mem_mul ha (idealGen_mem (I ^ n) i)
      rwa [← pow_add, add_comm] at this).choose_spec

@[reassoc (attr := simp)]
lemma idealPowMul_ι {k n : ℕ} (a : A) (ha : a ∈ I ^ k) :
    idealPowMul I F a ha ≫ idealPowι I F (n + k) =
      idealPowι I F n ≫ smulHom F (algebraMap A Γ(X, ⊤) a) :=
  imageMapOf_ι _ _ _ _ _

abbrev quotPow (n : ℕ) : X.Modules := cokernel (idealPowι I F (n + 1))

abbrev quotPowπ (n : ℕ) : F ⟶ quotPow I F n := cokernel.π _

def quotPowMap (n : ℕ) : quotPow I F (n + 1) ⟶ quotPow I F n :=
  cokernel.desc _ (quotPowπ I F n) (by
    rw [← idealPowSucc_ι, Category.assoc, cokernel.condition, comp_zero])

@[reassoc (attr := simp)]
lemma quotPowπ_map (n : ℕ) : quotPowπ I F (n + 1) ≫ quotPowMap I F n = quotPowπ I F n :=
  cokernel.π_desc _ _ _

def quotPowSC (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (idealPowι I F (n + 1)) (quotPowπ I F n) (cokernel.condition _)

lemma quotPowSC_shortExact (n : ℕ) : (quotPowSC I F n).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by change Mono (idealPowι I F (n + 1)); infer_instance
  epi_g := by change Epi (quotPowπ I F n); infer_instance

section Qcoh

variable [F.IsQuasicoherent]

instance (J : Ideal A) : (⨁ fun _ : Fin (idealGenNum J) => F).IsQuasicoherent :=
  isQuasicoherent_biproduct _

instance (n : ℕ) : (idealPow I F n).IsQuasicoherent := inferInstance

instance (n : ℕ) : (quotPow I F n).IsQuasicoherent := inferInstance

abbrev toFunctions (V : X.Opens) : A →+* Γ(X, V) := (restrictTop V).comp (algebraMap A Γ(X, ⊤))

theorem range_idealPowι_app {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ) :
    Set.range ((idealPowι I F n).app V) =
      ((Ideal.map (toFunctions V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) : Set Γ(F, V)) := by
  rw [range_kernel_ι_cokernel_π_app _ hV]
  set g := idealGen (I ^ n)
  let L : (Fin (idealGenNum (I ^ n)) → Γ(F, V)) →ₗ[Γ(X, V)] Γ(F, V) :=
    { toFun := fun x => ∑ k, toFunctions V (g k) • x k
      map_add' := fun x y => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by simp [Finset.smul_sum, smul_comm r] }
  have h1 : Set.range ((idealSumMap F (I ^ n)).app V) = Set.range L := by
    ext m
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨fun k => (biproduct.π (fun _ : Fin (idealGenNum (I ^ n)) => F) k).app V p, ?_⟩
      change (∑ k, toFunctions V (g k) •
        (biproduct.π (fun _ : Fin (idealGenNum (I ^ n)) => F) k).app V p) = _
      conv_rhs => rw [biproduct_app_eq_sum _ V p]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, idealSumMap,
        biproduct.ι_desc, smulHom_app_apply]
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨∑ k, (biproduct.ι (fun _ : Fin (idealGenNum (I ^ n)) => F) k).app V (x k), ?_⟩
      change _ = ∑ k, toFunctions V (g k) • x k
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, idealSumMap,
        biproduct.ι_desc, smulHom_app_apply]
      rfl
  rw [h1]
  have h2 : (LinearMap.range L) = Ideal.map (toFunctions V) (I ^ n) • ⊤ := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change ∑ k, toFunctions V (g k) • x k ∈ _
      refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      exact Ideal.mem_map_of_mem _ (idealGen_mem _ k)
    · refine Submodule.smul_le.2 fun r hr m _ => ?_
      rw [← span_idealGen (I ^ n), Ideal.map_span, ← Set.range_comp] at hr
      obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hr
      refine ⟨fun k => c k • m, ?_⟩
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_smul, Function.comp_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, mul_comm]
  rw [← h2]
  rfl

theorem surjective_quotPowπ_app {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ) :
    Function.Surjective ((quotPowπ I F n).app V) :=
  surjective_cokernel_π_app _ hV

theorem quotPowπ_app_eq_zero_iff {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ) (m : Γ(F, V)) :
    (quotPowπ I F n).app V m = 0 ↔
      m ∈ (Ideal.map (toFunctions V) (I ^ (n + 1)) • ⊤ : Submodule Γ(X, V) Γ(F, V)) := by
  rw [← mem_range_app_iff _ hV, range_idealPowι_app I F hV]
  rfl

end Qcoh

section Coherent

variable {F}

end Coherent

end

end GroundTheory.Arith.SchemeCoh
