import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WCoreDef

noncomputable section

namespace PI.LocMassTypW.WCoreP

open Matrix Module

theorem model_inj {K V W Z : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [AddCommGroup Z] [Module K Z]
    (a : W →ₗ[K] V) (b : V →ₗ[K] W) (s : W →ₗ[K] V) (T : Submodule K W) (ζ : Z →ₗ[K] V)
    (ha : Function.Injective a) (hbs : ∀ w, b (s w) = w)
    (hT : ∀ w, b (a w) ∈ T → b (a w) = 0)
    (hζ : Function.Injective ζ) (hζb : ∀ z, b (ζ z) = 0)
    (hζa : ∀ z w, ζ z = a w → ζ z = 0) :
    Function.Injective (LinearMap.coprod a (LinearMap.coprod (s ∘ₗ T.subtype) ζ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨w, ⟨⟨t, ht⟩, z⟩⟩ h
  simp only [LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h

  have hb := congrArg b h
  rw [map_add, map_add, hbs, hζb, add_zero, map_zero] at hb
  have hbaw : b (a w) ∈ T := by
    rw [eq_neg_of_add_eq_zero_left hb]
    exact T.neg_mem ht
  have h0 := hT w hbaw
  have ht0 : t = 0 := by
    rw [h0, zero_add] at hb
    exact hb
  subst ht0
  rw [map_zero, zero_add] at h
  have hz : ζ z = a (-w) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_right h
  have z0 : z = 0 := hζ (by rw [hζa z (-w) hz, map_zero])
  subst z0
  rw [map_zero, add_zero] at h
  have w0 : w = 0 := ha (by rw [h, map_zero])
  subst w0
  rfl

theorem exists_Z {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (a : W →ₗ[K] V) (b : V →ₗ[K] W) (s : W →ₗ[K] V)
    (ha : Function.Injective a) (hbs : ∀ w, b (s w) = w) :
    ∃ Z : Submodule K V, Z ≤ LinearMap.ker b ∧ (∀ z ∈ Z, z ∈ LinearMap.range a → z = 0) ∧
      finrank K Z + finrank K (LinearMap.ker (b ∘ₗ a)) + finrank K W = finrank K V := by
  set S := LinearMap.range a ⊓ LinearMap.ker b with hSdef
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.comap (LinearMap.ker b).subtype S)
  refine ⟨C.map (LinearMap.ker b).subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
  · intro z hz hza
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hz
    have hcS : c ∈ Submodule.comap (LinearMap.ker b).subtype S := ⟨hza, c.2⟩
    have h0 : c = 0 := (Submodule.disjoint_def.mp hC.disjoint) c hcS hc
    rw [h0, map_zero]
  · have h1 := Submodule.finrank_add_eq_of_isCompl hC
    rw [← Submodule.finrank_map_subtype_eq (LinearMap.ker b) (Submodule.comap _ S),
      Submodule.map_comap_subtype] at h1
    rw [Submodule.finrank_map_subtype_eq]
    have h2 : finrank K ↥(LinearMap.ker b ⊓ S) = finrank K (LinearMap.ker (b ∘ₗ a)) := by
      have hS : LinearMap.ker b ⊓ S = (LinearMap.ker (b ∘ₗ a)).map a := by
        rw [LinearMap.ker_comp, Submodule.map_comap_eq, hSdef, inf_comm, inf_assoc, inf_idem]
      rw [hS]
      exact (Submodule.equivMapOfInjective a ha _).finrank_eq.symm
    have h3 : finrank K (LinearMap.ker b) + finrank K W = finrank K V := by
      have h4 := LinearMap.finrank_range_add_finrank_ker b
      have hr : LinearMap.range b = ⊤ := LinearMap.range_eq_top.mpr fun w => ⟨s w, hbs w⟩
      rw [hr, finrank_top] at h4
      omega
    omega

theorem field_core {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (a0 a : W →ₗ[K] V) (b0 b : V →ₗ[K] W) (s0 s : W →ₗ[K] V)
    (ha0 : Function.Injective a0) (ha : Function.Injective a)
    (hs0 : ∀ w, b0 (s0 w) = w) (hs : ∀ w, b (s w) = w) (hc : ∀ w, b (a w) = b0 (a0 w)) :
    ∃ e : V ≃ₗ[K] V, (∀ w, e (a0 w) = a w) ∧ ∀ v, b (e v) = b0 v := by

  obtain ⟨T, hT⟩ := Submodule.exists_isCompl (LinearMap.range (b ∘ₗ a))
  obtain ⟨Z, hZb, hZa, hZd⟩ := exists_Z a b s ha hs
  obtain ⟨Z0, hZ0b, hZ0a, hZ0d⟩ := exists_Z a0 b0 s0 ha0 hs0
  have hba : b ∘ₗ a = b0 ∘ₗ a0 := LinearMap.ext hc
  have hTcond : ∀ w, b (a w) ∈ T → b (a w) = 0 := fun w h =>
    (Submodule.disjoint_def.mp hT.disjoint) _ ⟨w, rfl⟩ h
  have hT0cond : ∀ w, b0 (a0 w) ∈ T → b0 (a0 w) = 0 := fun w h => by
    rw [← hc] at h ⊢
    exact hTcond w h
  set F := LinearMap.coprod a (LinearMap.coprod (s ∘ₗ T.subtype) Z.subtype) with hF
  set F0 := LinearMap.coprod a0 (LinearMap.coprod (s0 ∘ₗ T.subtype) Z0.subtype) with hF0
  have hFi : Function.Injective F :=
    model_inj a b s T Z.subtype ha hs hTcond Subtype.val_injective
      (fun z => LinearMap.mem_ker.mp (hZb z.2)) (fun z w h => hZa z z.2 ⟨w, h.symm⟩)
  have hF0i : Function.Injective F0 :=
    model_inj a0 b0 s0 T Z0.subtype ha0 hs0 hT0cond Subtype.val_injective
      (fun z => LinearMap.mem_ker.mp (hZ0b z.2)) (fun z w h => hZ0a z z.2 ⟨w, h.symm⟩)
  have hTd : finrank K T = finrank K (LinearMap.ker (b ∘ₗ a)) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hT
    have h2 := LinearMap.finrank_range_add_finrank_ker (b ∘ₗ a)
    omega
  have hdim : finrank K (W × T × Z) = finrank K V := by
    rw [Module.finrank_prod, Module.finrank_prod, hTd]
    omega
  have hdim0 : finrank K (W × T × Z0) = finrank K V := by
    rw [Module.finrank_prod, Module.finrank_prod, hTd, hba]
    omega
  have hZZ : finrank K Z0 = finrank K Z := by
    have h1 := hZd
    have h2 := hZ0d
    rw [hba] at h1
    omega
  let EF : (W × T × Z) ≃ₗ[K] V := LinearEquiv.ofBijective F
    ⟨hFi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hFi⟩
  let EF0 : (W × T × Z0) ≃ₗ[K] V := LinearEquiv.ofBijective F0
    ⟨hF0i, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim0).mp hF0i⟩
  let φ : Z0 ≃ₗ[K] Z := LinearEquiv.ofFinrankEq Z0 Z hZZ
  let G : (W × T × Z0) ≃ₗ[K] (W × T × Z) :=
    (LinearEquiv.refl K W).prodCongr ((LinearEquiv.refl K T).prodCongr φ)
  refine ⟨EF0.symm.trans (G.trans EF), fun w => ?_, fun v => ?_⟩
  · have h1 : EF0.symm (a0 w) = (w, 0, 0) := by
      rw [LinearEquiv.symm_apply_eq]
      show a0 w = F0 (w, 0, 0)
      simp [hF0]
    simp only [LinearEquiv.trans_apply, h1]
    show F (G (w, 0, 0)) = a w
    simp [hF, G]
  · obtain ⟨⟨w, t, z0⟩, rfl⟩ := EF0.surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    show b (F (G (w, t, z0))) = b0 (F0 (w, t, z0))
    have hz : b (φ z0 : V) = 0 := LinearMap.mem_ker.mp (hZb (φ z0).2)
    have hz0 : b0 (z0 : V) = 0 := LinearMap.mem_ker.mp (hZ0b z0.2)
    simp only [hF, hF0, G, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, LinearMap.coprod_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, map_add, hs, hs0, hz, hz0, hc]

theorem field_mat {K : Type*} [Field K] {n m : ℕ} (A0 A B0 B : Matrix (Fin n) (Fin m) K)
    (L0 L M0 M : Matrix (Fin m) (Fin n) K) (hL0 : L0 * A0 = 1) (hL : L * A = 1)
    (hM0 : M0 * B0 = 1) (hM : M * B = 1) (hC : A0ᵀ * B0 = Aᵀ * B) :
    ∃ k : Matrix (Fin n) (Fin n) K, IsUnit k ∧ k * A0 = A ∧ Bᵀ * k = B0ᵀ := by
  have inj : ∀ {A' : Matrix (Fin n) (Fin m) K} {L' : Matrix (Fin m) (Fin n) K}, L' * A' = 1 →
      Function.Injective (Matrix.toLin' A') := by
    intro A' L' h x y hxy
    have h2 := congrArg (Matrix.toLin' L') hxy
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h] using h2
  have sec : ∀ {B' : Matrix (Fin n) (Fin m) K} {M' : Matrix (Fin m) (Fin n) K}, M' * B' = 1 →
      ∀ w, Matrix.toLin' B'ᵀ (Matrix.toLin' M'ᵀ w) = w := by
    intro B' M' h w
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, h]
  have hC' : Bᵀ * A = B0ᵀ * A0 := by
    have h := congrArg Matrix.transpose hC
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h
    exact h.symm
  obtain ⟨e, he1, he2⟩ := field_core (Matrix.toLin' A0) (Matrix.toLin' A) (Matrix.toLin' B0ᵀ)
    (Matrix.toLin' Bᵀ) (Matrix.toLin' M0ᵀ) (Matrix.toLin' Mᵀ) (inj hL0) (inj hL) (sec hM0) (sec hM)
    (fun w => by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hC'])
  refine ⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_, ?_⟩
  · have h : LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) *
        LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      have h2 : (e : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) =
          LinearMap.id := by
        ext x
        simp
      rw [h2, LinearMap.toMatrix'_id]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)
  · rw [← LinearMap.toMatrix'_toLin' A0, ← LinearMap.toMatrix'_comp]
    have h : (e : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ Matrix.toLin' A0 = Matrix.toLin' A :=
      LinearMap.ext he1
    rw [h, LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_toLin' Bᵀ, ← LinearMap.toMatrix'_comp]
    have h : Matrix.toLin' Bᵀ ∘ₗ (e : (Fin n → K) →ₗ[K] (Fin n → K)) = Matrix.toLin' B0ᵀ :=
      LinearMap.ext he2
    rw [h, LinearMap.toMatrix'_toLin']

def k1 {R : Type*} [CommRing R] {n m : ℕ} (A B0 B : Matrix (Fin n) (Fin m) R)
    (L0 M : Matrix (Fin m) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  A * L0 + Mᵀ * B0ᵀ - Mᵀ * Bᵀ * A * L0

theorem affine_sol {R : Type*} [CommRing R] {n m : ℕ} (A0 A B0 B : Matrix (Fin n) (Fin m) R)
    (L0 M : Matrix (Fin m) (Fin n) R) (hL0 : L0 * A0 = 1) (hM : M * B = 1)
    (hC' : B0ᵀ * A0 = Bᵀ * A) (X : Matrix (Fin n) (Fin n) R) :
    (k1 A B0 B L0 M + (1 - Mᵀ * Bᵀ) * X * (1 - A0 * L0)) * A0 = A ∧
      Bᵀ * (k1 A B0 B L0 M + (1 - Mᵀ * Bᵀ) * X * (1 - A0 * L0)) = B0ᵀ := by
  have hBM : Bᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]
  have hQ : (1 - A0 * L0) * A0 = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hL0, Matrix.mul_one, sub_self]
  have hP : Bᵀ * (1 - Mᵀ * Bᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBM, Matrix.one_mul, sub_self]
  constructor
  · rw [Matrix.add_mul, Matrix.mul_assoc ((1 - Mᵀ * Bᵀ) * X), hQ, Matrix.mul_zero, add_zero]
    simp only [k1, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, hL0, Matrix.mul_one]
    rw [hC']
    abel
  · rw [Matrix.mul_add, ← Matrix.mul_assoc Bᵀ ((1 - Mᵀ * Bᵀ) * X), ← Matrix.mul_assoc Bᵀ, hP,
      Matrix.zero_mul, Matrix.zero_mul, add_zero]
    simp only [k1, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hBM, Matrix.one_mul]
    abel

theorem proj_fix {R : Type*} [CommRing R] {n m : ℕ} (A0 B : Matrix (Fin n) (Fin m) R)
    (L0 M : Matrix (Fin m) (Fin n) R) (h : Matrix (Fin n) (Fin n) R)
    (h1 : h * A0 = 0) (h2 : Bᵀ * h = 0) :
    (1 - Mᵀ * Bᵀ) * h * (1 - A0 * L0) = h := by
  have e1 : Mᵀ * Bᵀ * h = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]
  have e2 : h * (1 - A0 * L0) = h := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.zero_mul, sub_zero]
  rw [Matrix.sub_mul, Matrix.one_mul, e1, sub_zero, e2]

end PI.LocMassTypW.WCoreP

namespace PI.LocMassTypW

open Matrix WCoreP

theorem transitiveOverLocalRings : WCore := by
  intro O _ _ n m A0 A B0 B ⟨L0, hL0⟩ ⟨L, hL⟩ ⟨M0, hM0⟩ ⟨M, hM⟩ hC
  set f := IsLocalRing.residue O with hf
  have hmap1 : ∀ {X : Matrix (Fin m) (Fin n) O} {Y : Matrix (Fin n) (Fin m) O}, X * Y = 1 →
      X.map f * Y.map f = 1 := by
    intro X Y h
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]
  have hCf : (A0.map f)ᵀ * B0.map f = (A.map f)ᵀ * B.map f := by
    rw [← Matrix.transpose_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hC]

  obtain ⟨kb, hkbu, hkbA, hkbB⟩ := field_mat (A0.map f) (A.map f) (B0.map f) (B.map f) (L0.map f) (L.map f)
    (M0.map f) (M.map f) (hmap1 hL0) (hmap1 hL) (hmap1 hM0) (hmap1 hM) hCf
  have hC' : B0ᵀ * A0 = Bᵀ * A := by
    have h := congrArg Matrix.transpose hC
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h

  obtain ⟨hk1A, hk1B⟩ := affine_sol A0 A B0 B L0 M hL0 hM hC' 0
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at hk1A hk1B
  set hbar := kb - (k1 A B0 B L0 M).map f with hhbar
  have hb1 : hbar * A0.map f = 0 := by
    rw [hhbar, Matrix.sub_mul, hkbA, ← Matrix.map_mul, hk1A, sub_self]
  have hb2 : (B.map f)ᵀ * hbar = 0 := by
    rw [hhbar, Matrix.mul_sub, hkbB, ← Matrix.transpose_map (M := B), ← Matrix.map_mul, hk1B,
      Matrix.transpose_map, sub_self]
  have hproj := proj_fix (A0.map f) (B.map f) (L0.map f) (M.map f) hbar hb1 hb2

  let X : Matrix (Fin n) (Fin n) O := fun i j => Function.surjInv IsLocalRing.residue_surjective (hbar i j)
  have hX : X.map f = hbar := by
    ext i j
    exact Function.surjInv_eq IsLocalRing.residue_surjective (hbar i j)
  obtain ⟨hkA, hkB⟩ := affine_sol A0 A B0 B L0 M hL0 hM hC' X
  set k := k1 A B0 B L0 M + (1 - Mᵀ * Bᵀ) * X * (1 - A0 * L0) with hk
  have hkmap : k.map f = kb := by
    rw [← RingHom.mapMatrix_apply, hk]
    simp only [map_add, map_mul, map_sub, map_one, RingHom.mapMatrix_apply]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map, hX, hproj, hhbar]
    abel
  refine ⟨k, ?_, hkA, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hdet : IsLocalRing.residue O k.det = kb.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hf, hkmap]
    rw [hdet]
    exact ((Matrix.isUnit_iff_isUnit_det kb).mp hkbu).ne_zero
  · have h := congrArg Matrix.transpose hkB
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h

end PI.LocMassTypW
