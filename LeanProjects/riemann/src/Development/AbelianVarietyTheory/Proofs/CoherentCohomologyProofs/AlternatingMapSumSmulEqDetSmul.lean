import Mathlib

namespace GlobalTheory

open scoped BigOperators

section JetWedge

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}

noncomputable def jetWedge (ω : M [⋀^Fin D]→ₗ[A] N) : (A × M) [⋀^Fin (D + 1)]→ₗ[A] N :=
  AlternatingMap.alternatizeUncurryFin
    ((LinearMap.fst A A M).smulRight (ω.compLinearMap (LinearMap.snd A A M)))

theorem jetWedge_apply (ω : M [⋀^Fin D]→ₗ[A] N) (v : Fin (D + 1) → A × M) :
    jetWedge ω v =
      ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * (v i).1) • ω (fun k => (v (i.succAbove k)).2) := by
  rw [jetWedge, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, ← Int.cast_smul_eq_zsmul A]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  rfl

theorem jetWedge_shear (ω : M [⋀^Fin D]→ₗ[A] N) (h : A) (u : M) (v : Fin (D + 1) → A × M) :
    jetWedge ω (fun i => (h * (v i).1, h • (v i).2 + (v i).1 • u)) = h ^ (D + 1) • jetWedge ω v := by
  classical
  let φ : (A × M) →ₗ[A] (A × M) :=
    (h • LinearMap.fst A A M).prod (h • LinearMap.snd A A M + (LinearMap.fst A A M).smulRight u)
  let g : Option M → A × M := fun o => o.elim (1, 0) (fun m => (0, m))
  have hg : Submodule.span A (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, m⟩ -
    have : ((a, m) : A × M) = a • g none + g (some m) := by simp [g]
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))
      (Submodule.subset_span ⟨some m, rfl⟩)
  have key : ((jetWedge ω).compLinearMap φ).toMultilinearMap
      = (h ^ (D + 1) • jetWedge ω).toMultilinearMap := by
    refine MultilinearMap.ext_of_span_eq_top (g := fun _ => g) (fun _ => hg) fun j => ?_
    change jetWedge ω (fun i => φ (g (j i))) = h ^ (D + 1) • jetWedge ω (fun i => g (j i))
    by_cases hj : ∃ a b, a ≠ b ∧ j a = j b
    · obtain ⟨a, b, hab, hjab⟩ := hj
      rw [(jetWedge ω).map_eq_zero_of_eq _ (i := a) (j := b) (by simp only [hjab]) hab,
        (jetWedge ω).map_eq_zero_of_eq _ (i := a) (j := b) (by simp only [hjab]) hab, smul_zero]
    · push Not at hj
      rw [jetWedge_apply, jetWedge_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases hi : j i with
      | some m => simp [φ, g]
      | none =>
        have hk : ∀ k : Fin D, (g (j (i.succAbove k))).1 = 0 := by
          intro k
          cases hk : j (i.succAbove k) with
          | some m => simp [g]
          | none => exact absurd (hk.trans hi.symm) (hj _ _ (Fin.succAbove_ne i k))
        have : (fun k : Fin D => (φ (g (j (i.succAbove k)))).2)
            = fun k : Fin D => h • (g (j (i.succAbove k))).2 := by
          funext k
          simp [φ, hk k]
        rw [this, ω.map_smul_univ (fun _ => h)]
        simp only [φ, g, smul_smul]
        congr 1
        simp
        ring
  exact congrArg (fun F : MultilinearMap A (fun _ : Fin (D + 1) => A × M) N => F v) key

theorem alternating_map_sum_smul_eq_det_smul {n : ℕ} (ω : M [⋀^Fin n]→ₗ[A] N)
    (a : Matrix (Fin n) (Fin n) A) (w : Fin n → M) :
    ω (fun i => ∑ k, a i k • w k) = a.det • ω w := by
  classical
  let φ : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A w
  have key : ω.compLinearMap φ
      = ((LinearMap.toSpanSingleton A N (ω w)).compAlternatingMap Matrix.detRowAlternating) := by
    refine Module.Basis.ext_alternating (Pi.basisFun A (Fin n)) fun v hv => ?_
    have hb : Function.Bijective v := Finite.injective_iff_bijective.mp hv
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v hb
    have e1 : (fun i => (Pi.basisFun A (Fin n)) (v i)) = (Pi.basisFun A (Fin n)) ∘ σ := rfl
    rw [e1, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e2 : (Matrix.detRowAlternating : (Fin n → A) [⋀^Fin n]→ₗ[A] A) (Pi.basisFun A (Fin n))
        = 1 := by
      rw [← Matrix.det_one (n := Fin n)]
      change Matrix.det _ = _
      congr 1
      ext i j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simp only [LinearMap.compAlternatingMap_apply, e2, LinearMap.toSpanSingleton_apply, one_smul,
      AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp [φ]
  have := congrArg (fun F : (Fin n → A) [⋀^Fin n]→ₗ[A] N => F a) key
  have e3 : (fun i => ∑ k, a i k • w k) = fun i => φ (a i) := by
    funext i
    exact (Fintype.linearCombination_apply A w (a i)).symm
  rw [e3]
  exact this

theorem alternating_sub_mem_smul_top (ω : M [⋀^Fin D]→ₗ[A] N) (I : Ideal A) (v w : Fin D → M)
    (hvw : ∀ k, v k - w k ∈ I • (⊤ : Submodule A M)) :
    ω v - ω w ∈ I • (⊤ : Submodule A N) := by
  classical
  have key : ∀ s : Finset (Fin D), ω (s.piecewise v w) - ω w ∈ I • (⊤ : Submodule A N) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have h1 : s.piecewise v w = Function.update (s.piecewise v w) i (w i) := by
        rw [eq_comm, Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hi]
      have h2 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          = ω.toMultilinearMap.toLinearMap (s.piecewise v w) i (v i - w i) := by
        rw [map_sub, Finset.piecewise_insert]
        conv_lhs => rw [h1]
        simp
      have h3 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          ∈ I • (⊤ : Submodule A N) := by
        rw [h2]
        have := Submodule.mem_map_of_mem
          (f := ω.toMultilinearMap.toLinearMap (s.piecewise v w) i) (hvw i)
        rw [Submodule.map_smul''] at this
        exact Submodule.smul_mono le_rfl le_top this
      simpa using add_mem h3 ih
  simpa using key Finset.univ

end JetWedge

section JacForm

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}

noncomputable def jacForm (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)
    (f : Fin (D + 1) → A) : N :=
  ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * f i) • ω (fun k => d (f (i.succAbove k)))

variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)

theorem jacForm_eq_jetWedge (f : Fin (D + 1) → A) :
    jacForm d ω f = jetWedge ω (fun i => (f i, d (f i))) := by
  rw [jetWedge_apply, jacForm]

theorem jacForm_mul (h : A) (f : Fin (D + 1) → A) :
    jacForm d ω (fun i => h * f i) = h ^ (D + 1) • jacForm d ω f := by
  rw [jacForm_eq_jetWedge, jacForm_eq_jetWedge, ← jetWedge_shear ω h (d h)]
  simp only [Derivation.leibniz]

theorem form_d_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    ω (fun k => d (h * g k)) - h ^ D • ω (fun k => d (g k)) ∈ I • (⊤ : Submodule A N) := by
  have : h ^ D • ω (fun k => d (g k)) = ω (fun k => h • d (g k)) := by
    rw [ω.map_smul_univ (fun _ => h)]
    simp
  rw [this]
  refine alternating_sub_mem_smul_top ω I _ _ fun k => ?_
  rw [Derivation.leibniz, add_sub_cancel_left]
  exact Submodule.smul_mem_smul (hg k) Submodule.mem_top

variable [Module R N] [IsScalarTower R A N] [IsScalarTower R A M]

noncomputable def jacobianMultilinearTo : A [⋀^Fin (D + 1)]→ₗ[R] N where
  toMultilinearMap := ((jetWedge ω).toMultilinearMap.restrictScalars R).compLinearMap
    (fun _ => (LinearMap.id : A →ₗ[R] A).prod (d : A →ₗ[R] M))
  map_eq_zero_of_eq' v i j hv hij :=
    (jetWedge ω).map_eq_zero_of_eq (fun i => (v i, d (v i))) (by simp only [hv]) hij

theorem jacFormAlt_apply (f : Fin (D + 1) → A) : jacobianMultilinearTo d ω f = jacForm d ω f :=
  (jacForm_eq_jetWedge d ω f).symm

end JacForm

section RestrictScalars

variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}

def altRestrictScalars (ω : M [⋀^Fin D]→ₗ[B] N) : M [⋀^Fin D]→ₗ[A] N where
  toMultilinearMap := ω.toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' v _ _ hv hij := ω.map_eq_zero_of_eq v hv hij

@[simp] theorem altRestrictScalars_apply (ω : M [⋀^Fin D]→ₗ[B] N) (v : Fin D → M) :
    altRestrictScalars A ω v = ω v := rfl

variable {A} {L : Type*} [AddCommGroup L] [Module A L]

variable (B D) in

noncomputable def exteriorPowerMapOver (φ : L →ₗ[A] M) : (⋀[A]^D L) →ₗ[A] (⋀[B]^D M) :=
  exteriorPower.alternatingMapLinearEquiv
    ((altRestrictScalars A (exteriorPower.ιMulti B D (M := M))).compLinearMap φ)

@[simp] theorem exteriorPowerMapOver_ιMulti (φ : L →ₗ[A] M) (v : Fin D → L) :
    exteriorPowerMapOver B D φ (exteriorPower.ιMulti A D v)
      = exteriorPower.ιMulti B D (fun k => φ (v k)) := by
  simp [exteriorPowerMapOver]

noncomputable def wedgeContract (φ : Fin D → L →ₗ[A] B) : (⋀[A]^D L) →ₗ[A] B :=
  exteriorPower.alternatingMapLinearEquiv
    ((altRestrictScalars A (Matrix.detRowAlternating : (Fin D → B) [⋀^Fin D]→ₗ[B] B)).compLinearMap
      (LinearMap.pi φ))

@[simp] theorem wedgeContract_ιMulti (φ : Fin D → L →ₗ[A] B) (v : Fin D → L) :
    wedgeContract φ (exteriorPower.ιMulti A D v) = (Matrix.of fun j k => φ k (v j)).det := by
  simp only [wedgeContract, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

end RestrictScalars

section Jac

variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}

open KaehlerDifferential

noncomputable def dWedge (g : Fin D → A) : ⋀[A]^D Ω[A⁄R] :=
  exteriorPower.ιMulti A D (fun k => KaehlerDifferential.D R A (g k))

noncomputable def jac (f : Fin (D + 1) → A) : ⋀[A]^D Ω[A⁄R] :=
  ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * f i) • dWedge R (fun k => f (i.succAbove k))

theorem jac_mul (h : A) (f : Fin (D + 1) → A) :
    jac R (fun i => h * f i) = h ^ (D + 1) • jac R f :=
  jacForm_mul _ _ h f

theorem dWedge_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    dWedge R (fun k => h * g k) - h ^ D • dWedge R g ∈ I • (⊤ : Submodule A (⋀[A]^D Ω[A⁄R])) :=
  form_d_mul_sub_mem _ _ I h g hg

variable (A D) in

noncomputable def jacobianMultilinear : A [⋀^Fin (D + 1)]→ₗ[R] (⋀[A]^D Ω[A⁄R]) :=
  jacobianMultilinearTo (KaehlerDifferential.D R A) (exteriorPower.ιMulti A D)

@[simp] theorem jacAlt_apply (f : Fin (D + 1) → A) : jacobianMultilinear R A D f = jac R f :=
  jacFormAlt_apply _ _ f

variable {R}

theorem map_jac (S B : Type*) [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [IsScalarTower R S B] [SMulCommClass S A B]
    (f : Fin (D + 1) → A) :
    exteriorPowerMapOver B D (KaehlerDifferential.map R S A B) (jac R f)
      = jac S (fun i => algebraMap A B (f i)) := by
  rw [jac, jac, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, dWedge, exteriorPowerMapOver_ιMulti, ← algebraMap_smul B]
  simp [dWedge]

variable (R A D)

end Jac

end GlobalTheory
