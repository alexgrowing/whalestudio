import Mathlib

open IsLocalRing TensorProduct

namespace GlobalTheory.AdicSurj

open AdicCompletion

variable (B : Type) {A : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem mem_smul_top_iff (n : ℕ) (b : B) :
    b ∈ (J ^ n • ⊤ : Submodule A B) ↔ b ∈ (J.map (algebraMap A B)) ^ n := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]

theorem pow_le_comap (n : ℕ) :
    J ^ n ≤ ((J.map (algebraMap A B)) ^ n).comap (algebraMap A B) := by
  rw [← Ideal.map_pow]; exact Ideal.le_comap_map

noncomputable def lev (n : ℕ) :
    AdicCompletion J A →+* B ⧸ (J.map (algebraMap A B)) ^ n :=
  (Ideal.quotientMap _ (algebraMap A B) (pow_le_comap B J n)).comp (evalₐ J n).toRingHom

theorem lev_mk (n : ℕ) (s : AdicCauchySequence J A) :
    lev B J n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ (algebraMap A B (s n)) := by
  simp [lev, evalₐ_mk, Ideal.quotientMap_mk]

theorem lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (lev B J n) = lev B J m := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  have h1 := s.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simp only [RingHom.comp_apply, lev_mk]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  have h3 : s n - s m ∈ J ^ m := by rw [← neg_sub]; exact neg_mem h1
  exact Ideal.mem_comap.mp (pow_le_comap B J m h3)

noncomputable def psi : AdicCompletion J A →+* AdicCompletion (J.map (algebraMap A B)) B :=
  AdicCompletion.liftRingHom _ (lev B J) (fun hle ↦ lev_compat B J hle)

theorem evalₐ_psi (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi B J x) = lev B J n x := by
  simp [psi]

theorem psi_algebraMap (a : A) :
    psi B J (algebraMap A (AdicCompletion J A) a) =
      algebraMap A (AdicCompletion (J.map (algebraMap A B)) B) a := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_psi, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk, AdicCompletion.algebraMap_apply, evalₐ_of]

theorem map_val_mk_eq_iff (s : AdicCauchySequence J A) (n : ℕ) (c : B) :
    (map J (Algebra.linearMap A B) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev B J n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by
  rw [map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
    Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]
  rfl

theorem psi_surjective [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Surjective (psi B J) := by
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  let t' : AdicCauchySequence J B := ⟨t.val, fun {m n} hmn ↦ by
    have h := t.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [SModEq.sub_mem, mem_smul_top_iff]; exact h⟩
  obtain ⟨x, hx⟩ := map_surjective J (f := Algebra.linearMap A B) hs (AdicCompletion.mk J _ t')
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  refine ⟨AdicCompletion.mk J A s, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_psi, evalₐ_mk]
  refine (map_val_mk_eq_iff B J s n (t n)).mp ?_
  rw [hx]; rfl

theorem ker_psi [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    RingHom.ker (psi B J) =
      Ideal.map (algebraMap A (AdicCompletion J A)) (LinearMap.ker (Algebra.linearMap A B)) := by
  set q := LinearMap.ker (Algebra.linearMap A B)
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hz : map J (Algebra.linearMap A B) x = 0 := by
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
      ext n
      have := (map_val_mk_eq_iff B J s n 0).mpr
        (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])
      simpa using this
    obtain ⟨y, rfl⟩ := ((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := Algebra.linearMap A B)
      Subtype.val_injective (LinearMap.exact_subtype_ker_map _) hs) x).mp hz
    obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite J q y
    clear hx hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [ofTensorProduct_tmul, map_smul, map_of, smul_eq_mul]
      have hm : (of J A) (q.subtype m) = algebraMap A (AdicCompletion J A) (m : A) := by
        rw [AdicCompletion.algebraMap_apply]; rfl
      rw [hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, psi_algebraMap, AdicCompletion.algebraMap_apply]
    have : algebraMap A B a = 0 := LinearMap.mem_ker.mp ha
    rw [this, _root_.map_zero]

end GlobalTheory.AdicSurj

namespace GlobalTheory.AdicSurj

open AdicCompletion

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

instance isScalarTower_adic :
    IsScalarTower A B (AdicCompletion (J.map (algebraMap A B)) B) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

noncomputable def psiₐ :
    AdicCompletion J A →ₐ[A] AdicCompletion (J.map (algebraMap A B)) B :=
  { psi B J with commutes' := psi_algebraMap B J }

noncomputable def theta :
    B ⊗[A] AdicCompletion J A →ₐ[B] AdicCompletion (J.map (algebraMap A B)) B :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) (psiₐ J) fun _ _ ↦ Commute.all _ _

theorem theta_bijective [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Bijective (theta (B := B) J) := by
  let e := RingHom.quotientKerEquivOfSurjective (psi_surjective B J hs)
  have hker : RingHom.ker (psi B J) ≤
      RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := AdicCompletion J A)).toRingHom := by
    rw [ker_psi B J hs, Ideal.map_le_iff_le_comap]
    intro a ha
    have h0 : algebraMap A B a = 0 := LinearMap.mem_ker.mp ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (1 : B) ⊗ₜ[A] algebraMap A (AdicCompletion J A) a = 0
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, h0, zero_mul,
      TensorProduct.zero_tmul]
  let σ : AdicCompletion (J.map (algebraMap A B)) B →+* B ⊗[A] AdicCompletion J A :=
    (Ideal.Quotient.lift _ _ hker).comp e.symm.toRingHom
  have hσ : ∀ x, σ (psi B J x) = 1 ⊗ₜ[A] x := by
    intro x
    have : e.symm (psi B J x) = Ideal.Quotient.mk _ x := e.symm_apply_eq.mpr rfl
    simp only [σ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this,
      Ideal.Quotient.lift_mk]
    rfl
  have hleft : ∀ t, σ (theta J t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul b x =>
      obtain ⟨a, rfl⟩ := hs b
      rw [theta, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
        ← IsScalarTower.algebraMap_apply, ← psi_algebraMap B J a]
      change σ (psi B J _ * psi B J x) = _
      rw [← map_mul, hσ, ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨Function.LeftInverse.injective hleft, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := psi_surjective B J hs y
  refine ⟨1 ⊗ₜ[A] x, ?_⟩
  rw [theta, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

theorem tensor_ringEquiv [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B))
    (I : Ideal B) (hI : I = J.map (algebraMap A B)) (K : Type) [CommRing K] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] :
    Nonempty (AdicCompletion I B ⊗[B] K ≃+* AdicCompletion J A ⊗[A] K) := by
  subst hI
  let θ := AlgEquiv.ofBijective (theta (B := B) J) (theta_bijective J hs)
  exact ⟨(Algebra.TensorProduct.comm B _ K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[B] K) θ.symm).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange A B B K (AdicCompletion J A)).toRingEquiv.trans
    (Algebra.TensorProduct.comm A K (AdicCompletion J A)).toRingEquiv))⟩

end GlobalTheory.AdicSurj

theorem GlobalTheory.adicCompletion_tensor_quotient_ringEquiv :
    ∀ (R₀ R K : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [CommRing R] [IsLocalRing R]
      [Algebra R₀ R] [CommRing K] [Algebra R K] [Algebra R₀ K] [IsScalarTower R₀ R K],
      Function.Surjective (algebraMap R₀ R) →
        Nonempty (AdicCompletion (maximalIdeal R) R ⊗[R] K ≃+*
          AdicCompletion (maximalIdeal R₀) R₀ ⊗[R₀] K) := by
  intro R₀ R K _ _ _ _ _ _ _ _ _ _ hs
  have hk : RingHom.ker (algebraMap R₀ R) ≤ maximalIdeal R₀ :=
    le_maximalIdeal (RingHom.ker_ne_top _)
  have hmax : ((maximalIdeal R₀).map (algebraMap R₀ R)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (hf := hs) (H := maximalIdeal.isMaximal R₀) with h | h
    · exfalso
      have h1 : (1 : R) ∈ (maximalIdeal R₀).map (algebraMap R₀ R) := h ▸ Submodule.mem_top
      obtain ⟨a, ha, hfa⟩ := (Ideal.mem_map_iff_of_surjective _ hs).mp h1
      have h2 : 1 - a ∈ maximalIdeal R₀ := hk (by rw [RingHom.mem_ker, map_sub, hfa, map_one, sub_self])
      have h3 : (1 : R₀) ∈ maximalIdeal R₀ := by simpa using add_mem h2 ha
      exact (maximalIdeal.isMaximal R₀).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
    · exact h
  exact GlobalTheory.AdicSurj.tensor_ringEquiv (maximalIdeal R₀) hs _ (eq_maximalIdeal hmax).symm K
