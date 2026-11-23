import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.IdxSmith

noncomputable section

namespace UnitaryThetaMoves

variable {C : Type*} [NormedField C] {Γ : Type*} [CommGroup Γ]

def chiRatio (χ : Γ →* Cˣ) (M M' : ℕ) (dg dg' dg₁ dg₂ : Γ) : C :=
  ((χ dg₁ ^ (M' : ℤ) * χ dg₂ ^ (-(M : ℤ))) / (χ dg ^ (M' : ℤ) * χ dg' ^ (-(M : ℤ))) : Cˣ)

def idxExp (M M' : ℕ) (a a' : ℤ) : ℤ := 2 * ((M' : ℤ) * a - (M : ℤ) * a')

theorem norm_units_zpow (x : Cˣ) (z : ℤ) : ‖((x ^ z : Cˣ) : C)‖ = ‖(x : C)‖ ^ z := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow]

theorem norm_units_ne_zero (x : Cˣ) : ‖(x : C)‖ ≠ 0 := norm_ne_zero_iff.mpr x.ne_zero

section Val

variable {V : Type*} [Fintype V]

theorem norm_chi_prod (χ : Γ →* Cˣ) (t : V → Γ) (Q : V → ℕ) (a : V → ℤ)
    (ht : ∀ v, ‖((χ (t v) : Cˣ) : C)‖ = ‖(Q v : C)‖) :
    ‖((χ (∏ v, t v ^ a v) : Cˣ) : C)‖ = ∏ v, ‖(Q v : C)‖ ^ a v := by
  first
  | (rw [map_prod, Units.coe_prod, norm_prod]
     refine Finset.prod_congr rfl fun v _ => ?_
     rw [map_zpow, norm_units_zpow, ht v])
  | (simp [map_prod, norm_prod, norm_units_zpow, ht])

theorem norm_chiRatio (χ : Γ →* Cˣ) (H : Subgroup Γ) (hχH : ∀ h ∈ H, χ h = 1)
    (M M' : ℕ) (t : V → Γ) (Q : V → ℕ) (a a' : V → ℤ) (dg dg' dg₁ dg₂ u u' : Γ)
    (hu : u ∈ H) (hu' : u' ∈ H)
    (hk : dg₁ = dg * (∏ v, t v ^ a v) * u) (hk' : dg₂ = dg' * (∏ v, t v ^ a' v) * u')
    (hQ : ∀ v, (Q v : C) ≠ 0) (ht : ∀ v, ‖((χ (t v) : Cˣ) : C)‖ = ‖(Q v : C)‖) :
    ‖chiRatio χ M M' dg dg' dg₁ dg₂‖ = ∏ v, ‖(Q v : C)‖ ^ ((M' : ℤ) * a v - (M : ℤ) * a' v) := by
  subst hk hk'
  have hu1 : χ u = 1 := hχH u hu
  have hu1' : χ u' = 1 := hχH u' hu'
  have hQn : ∀ v, ‖(Q v : C)‖ ≠ 0 := fun v => norm_ne_zero_iff.mpr (hQ v)
  have hα := norm_units_ne_zero (χ dg)
  have hβ := norm_units_ne_zero (χ dg')
  have hprod : ∏ v, ‖(Q v : C)‖ ^ ((M' : ℤ) * a v - (M : ℤ) * a' v) =
      (∏ v, ‖(Q v : C)‖ ^ a v) ^ (M' : ℤ) * (∏ v, ‖(Q v : C)‖ ^ a' v) ^ (-(M : ℤ)) := by
    first
    | rw [← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    | rw [Finset.prod_zpow, Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ (hQn v)]
    congr 1
    ring
  simp only [chiRatio, Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul, norm_units_zpow,
    map_mul, hu1, hu1', mul_one, norm_chi_prod χ t Q a ht, norm_chi_prod χ t Q a' ht]
  rw [hprod, mul_zpow, mul_zpow]
  first
  | (rw [div_eq_iff (mul_ne_zero (zpow_ne_zero _ hα) (zpow_ne_zero _ hβ))]
     ring)
  | (field_simp
     ring)

theorem norm_sqrt_idx (M M' : ℕ) (Q : V → ℕ) (a a' : V → ℤ) (hQ : ∀ v, (Q v : C) ≠ 0)
    (n : ℕ) (hn : (n : C) = ∏ v, (Q v : C) ^ idxExp M M' (a v) (a' v)) (s : C) (hs : s * s = n) :
    ‖s‖ = ∏ v, ‖(Q v : C)‖ ^ ((M' : ℤ) * a v - (M : ℤ) * a' v) := by
  have hQn : ∀ v, ‖(Q v : C)‖ ≠ 0 := fun v => norm_ne_zero_iff.mpr (hQ v)
  have hR : 0 ≤ ∏ v, ‖(Q v : C)‖ ^ ((M' : ℤ) * a v - (M : ℤ) * a' v) :=
    Finset.prod_nonneg fun v _ => zpow_nonneg (norm_nonneg _) _
  have hsq : ‖s‖ * ‖s‖ = (∏ v, ‖(Q v : C)‖ ^ ((M' : ℤ) * a v - (M : ℤ) * a' v)) *
      (∏ v, ‖(Q v : C)‖ ^ ((M' : ℤ) * a v - (M : ℤ) * a' v)) := by
    rw [← norm_mul, hs, hn, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [norm_zpow, ← zpow_add₀ (hQn v), idxExp, two_mul]
  first
  | exact (mul_self_inj (norm_nonneg _) hR).1 hsq
  | nlinarith [norm_nonneg s]

theorem norm_inv_mul_charRatio (χ : Γ →* Cˣ) (H : Subgroup Γ) (hχH : ∀ h ∈ H, χ h = 1)
    (M M' : ℕ) (t : V → Γ) (Q : V → ℕ) (a a' : V → ℤ) (dg dg' dg₁ dg₂ u u' : Γ)
    (hu : u ∈ H) (hu' : u' ∈ H)
    (hk : dg₁ = dg * (∏ v, t v ^ a v) * u) (hk' : dg₂ = dg' * (∏ v, t v ^ a' v) * u')
    (hQ : ∀ v, (Q v : C) ≠ 0) (ht : ∀ v, ‖((χ (t v) : Cˣ) : C)‖ = ‖(Q v : C)‖)
    (n : ℕ) (hn : (n : C) = ∏ v, (Q v : C) ^ idxExp M M' (a v) (a' v)) (s : C) (hs : s * s = n) :
    ‖s⁻¹ * chiRatio χ M M' dg dg' dg₁ dg₂‖ = 1 := by
  have hQn : ∀ v, ‖(Q v : C)‖ ≠ 0 := fun v => norm_ne_zero_iff.mpr (hQ v)
  rw [norm_mul, norm_inv, norm_sqrt_idx M M' Q a a' hQ n hn s hs,
    norm_chiRatio χ H hχH M M' t Q a a' dg dg' dg₁ dg₂ u u' hu hu' hk hk' hQ ht]
  exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (hQn v))

end Val

section Index

def matLat (O K : Type*) [CommRing O] [Field K] [Algebra O K] (N N' : ℕ) : AddSubgroup (Matrix (Fin N') (Fin N) K) where
  carrier := {x | ∀ i j, x i j ∈ (algebraMap O K).range}
  add_mem' := fun ha hb i j => Subring.add_mem _ (ha i j) (hb i j)
  zero_mem' := fun _ _ => Subring.zero_mem _
  neg_mem' := fun ha i j => Subring.neg_mem _ (ha i j)

def movHom (K : Type*) [Field K] {N N' : ℕ} (k : GL (Fin N) K) (k' : GL (Fin N') K) :
    Matrix (Fin N') (Fin N) K →+ Matrix (Fin N') (Fin N) K where
  toFun x := (k' : Matrix (Fin N') (Fin N') K) * x * ((k⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  map_zero' := by simp
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]

def movLat (O K : Type*) [CommRing O] [Field K] [Algebra O K] {N N' : ℕ} (k : GL (Fin N) K) (k' : GL (Fin N') K) :
    AddSubgroup (Matrix (Fin N') (Fin N) K) :=
  (matLat O K N N').map (movHom K k k')

def RelIndexFormula : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    (ϖ : O), Irreducible ϖ → ∀ (Q : ℕ), Nat.card (IsLocalRing.ResidueField O) = Q →
    ∀ (N N' : ℕ) (k : GL (Fin N) K) (k' : GL (Fin N') K) (a a' : ℤ) (w w' : Oˣ),
      (k : Matrix (Fin N) (Fin N) K).det = algebraMap O K ϖ ^ a * algebraMap O K (w : O) →
      (k' : Matrix (Fin N') (Fin N') K).det = algebraMap O K ϖ ^ a' * algebraMap O K (w' : O) →
      matLat O K N N' ≤ movLat O K k k' →
      0 ≤ (N' : ℤ) * a - (N : ℤ) * a' ∧
        (matLat O K N N').relIndex (movLat O K k k') = Q ^ ((N' : ℤ) * a - (N : ℤ) * a').toNat

theorem hn_of_idx {V : Type*} [Fintype V] (M₀ M₀' : ℕ) (Q : V → ℕ) (a a' : V → ℤ) (nv : V → ℕ)
    (hpos : ∀ v, 0 ≤ idxExp M₀ M₀' (a v) (a' v))
    (hnv : ∀ v, nv v = Q v ^ (idxExp M₀ M₀' (a v) (a' v)).toNat) :
    (((∏ v, nv v : ℕ)) : C) = ∏ v, (Q v : C) ^ idxExp M₀ M₀' (a v) (a' v) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hnv v, Nat.cast_pow, ← zpow_natCast, Int.toNat_of_nonneg (hpos v)]

theorem idxExp_eq (M₀ M₀' : ℕ) (a a' : ℤ) :
    idxExp M₀ M₀' a a' = ((2 * M₀' : ℕ) : ℤ) * a - ((2 * M₀ : ℕ) : ℤ) * a' := by
  unfold idxExp
  push_cast
  ring

end Index

section IdxProof

alias card_quot_range_toLin' := DVRLatticeIndex.card_quot_range_toLin_clean

end IdxProof

section IdxMain

open scoped Matrix

theorem zpow_eq_unit {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (ϖ : O) (hϖ : Irreducible ϖ) (m : ℤ) (U : Oˣ)
    (h : algebraMap O K ϖ ^ m = algebraMap O K (U : O)) : m = 0 := by
  have hinj := IsFractionRing.injective O K
  have key : ∀ (j : ℕ) (V : Oˣ), algebraMap O K ϖ ^ j = algebraMap O K (V : O) → j = 0 := by
    intro j V hj
    by_contra hj0
    have h1 : ϖ ^ j = (V : O) := hinj (by rw [map_pow]; exact hj)
    have h2 : IsUnit (ϖ ^ j) := by rw [h1]; exact V.isUnit
    exact hϖ.1 ((isUnit_pow_iff hj0).1 h2)
  rcases Int.eq_nat_or_neg m with ⟨j, rfl | rfl⟩
  · rw [zpow_natCast] at h
    simp [key j U h]
  · rw [zpow_neg, zpow_natCast, inv_eq_iff_eq_inv, ← map_units_inv (algebraMap O K)] at h
    simp [key j _ h]

theorem movHom_inv_apply {K : Type*} [Field K] {N N' : ℕ} (k : GL (Fin N) K) (k' : GL (Fin N') K)
    (x : Matrix (Fin N') (Fin N) K) : movHom K k⁻¹ k'⁻¹ (movHom K k k' x) = x := by
  simp only [movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_inv]
  first
  | (rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one])
  | (simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
     rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one])
  | simp [Matrix.mul_assoc]

theorem movHom_inv_injective {K : Type*} [Field K] {N N' : ℕ} (k : GL (Fin N) K) (k' : GL (Fin N') K) :
    Function.Injective (movHom K k⁻¹ k'⁻¹) := by
  intro x y hxy
  have h := congrArg (movHom K k⁻¹⁻¹ k'⁻¹⁻¹) hxy
  rwa [movHom_inv_apply, movHom_inv_apply] at h

private theorem zpow_identity_aux_lemma {K : Type*} [Field K] (x y z : K) (hx : x ≠ 0) (N N' : ℕ) (a a' : ℤ) :
    ((x ^ a' * z)⁻¹) ^ N * (x ^ a * y) ^ N' = x ^ ((N' : ℤ) * a - (N : ℤ) * a') * (y ^ N' * z⁻¹ ^ N) := by
  have h1 : x ^ ((N' : ℤ) * a) = (x ^ a) ^ N' := by rw [mul_comm, zpow_mul, zpow_natCast]
  have h2 : x ^ ((N : ℤ) * a') = (x ^ a') ^ N := by rw [mul_comm, zpow_mul, zpow_natCast]
  rw [zpow_sub₀ hx, h1, h2]
  first
  | ring
  | (field_simp
     ring)

theorem relIndexFormula : RelIndexFormula := by
  unfold RelIndexFormula
  intro O K _ _ _ _ _ _ ϖ hϖ Q hQ N N' k k' a a' w w' hdk hdk' hle
  have hmem : ∀ y : Matrix (Fin N') (Fin N) K, y ∈ matLat O K N N' ↔
      ∀ i j, y i j ∈ (algebraMap O K).range := fun y => Iff.rfl
  have hTT₀ : ∀ x, movHom K k⁻¹ k'⁻¹ (movHom K k k' x) = x := movHom_inv_apply k k'
  have hT₀T : ∀ x, movHom K k k' (movHom K k⁻¹ k'⁻¹ x) = x := by
    intro x
    simpa only [inv_inv] using movHom_inv_apply k⁻¹ k'⁻¹ x
  have hTL : ∀ y ∈ matLat O K N N', movHom K k⁻¹ k'⁻¹ y ∈ matLat O K N N' := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 (hle hy)
    rwa [hTT₀]
  have hent : ∀ (i p : Fin N') (j q : Fin N), ∃ z : O, algebraMap O K z =
      ((k'⁻¹ : GL (Fin N') K) : Matrix (Fin N') (Fin N') K) i p * (k : Matrix (Fin N) (Fin N) K) q j := by
    intro i p j q
    have hE : (Matrix.of fun (r : Fin N') (c : Fin N) => if r = p then (if c = q then (1 : K) else 0) else 0) ∈
        matLat O K N N' := by
      refine (hmem _).2 fun r c => ?_
      rw [Matrix.of_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
      · exact Subring.zero_mem _
    obtain ⟨z, hz⟩ := RingHom.mem_range.1 ((hmem _).1 (hTL _ hE) i j)
    refine ⟨z, hz.trans ?_⟩
    first
    | (simp only [movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_inv, Matrix.mul_apply, Matrix.of_apply,
        mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
        ite_true]; done)
    | (simp only [movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_inv, Matrix.mul_apply, Matrix.of_apply,
        mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
        if_true]; done)
    | (simp [movHom, Matrix.mul_apply, mul_ite, ite_mul]; done)
  choose D hD using hent
  obtain ⟨Mat, hMat⟩ : ∃ Mat : Matrix (Fin N' × Fin N) (Fin N' × Fin N) O, ∀ i j p q,
      algebraMap O K (Mat (i, j) (p, q)) =
        ((k'⁻¹ : GL (Fin N') K) : Matrix (Fin N') (Fin N') K) i p * (k : Matrix (Fin N) (Fin N) K) q j :=
    ⟨Matrix.of fun r c => D r.1 c.1 r.2 c.2, fun i j p q => hD i p j q⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin N' × Fin N → O) →+ Matrix (Fin N') (Fin N) K,
      ∀ x i j, Φ x i j = algebraMap O K (x (i, j)) :=
    ⟨{ toFun := fun x => Matrix.of fun i j => algebraMap O K (x (i, j))
       map_zero' := by ext i j; simp
       map_add' := fun x y => by ext i j; simp }, fun x i j => rfl⟩
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    funext r
    obtain ⟨i, j⟩ := r
    have h : Φ x i j = Φ y i j := by rw [hxy]
    rw [hΦ, hΦ] at h
    exact IsFractionRing.injective O K h
  have hrange : Φ.range = matLat O K N N' := by
    ext y
    rw [AddMonoidHom.mem_range, hmem]
    constructor
    · rintro ⟨x, rfl⟩ i j
      rw [hΦ]
      exact RingHom.mem_range.2 ⟨x (i, j), rfl⟩
    · intro hy
      have hy' : ∀ i j, ∃ z, algebraMap O K z = y i j := fun i j => RingHom.mem_range.1 (hy i j)
      choose f hf using hy'
      refine ⟨fun r => f r.1 r.2, ?_⟩
      ext i j
      rw [hΦ]
      exact hf i j
  have hcomm : ∀ x, Φ (Matrix.toLin' Mat x) = movHom K k⁻¹ k'⁻¹ (Φ x) := by
    intro x
    ext i j
    calc Φ (Matrix.toLin' Mat x) i j
        = ∑ m : Fin N', ∑ l : Fin N, ((k'⁻¹ : GL (Fin N') K) : Matrix (Fin N') (Fin N') K) i m *
            (k : Matrix (Fin N) (Fin N) K) l j * algebraMap O K (x (m, l)) := by
          rw [hΦ, Matrix.toLin'_apply]
          first
          | (simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, map_sum, map_mul, hMat]; done)
          | (simp only [Matrix.mulVec, Matrix.dotProduct, Fintype.sum_prod_type, map_sum, map_mul, hMat]; done)
          | (simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, map_sum, hMat]; done)
      _ = ∑ l : Fin N, (∑ m : Fin N', ((k'⁻¹ : GL (Fin N') K) : Matrix (Fin N') (Fin N') K) i m * Φ x m l) *
            (k : Matrix (Fin N) (Fin N) K) l j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hΦ]
          ring
      _ = movHom K k⁻¹ k'⁻¹ (Φ x) i j := by
          first
          | (simp only [movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_inv, Matrix.mul_apply]; done)
          | rfl
  have hsub : ((matLat O K N N').comap (movHom K k k')).comap Φ =
      (LinearMap.range (Matrix.toLin' Mat)).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
    constructor
    · intro hx
      rw [← hrange] at hx
      obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 hx
      refine ⟨y, hΦinj ?_⟩
      rw [hcomm, hy, hTT₀]
    · rintro ⟨y, rfl⟩
      rw [hcomm, hT₀T, ← hrange]
      exact AddMonoidHom.mem_range.2 ⟨y, rfl⟩
  have hidx : ((matLat O K N N').comap (movHom K k k')).relIndex (matLat O K N N') =
      (((matLat O K N N').comap (movHom K k k')).comap Φ).index := by
    first
    | (rw [AddSubgroup.index_comap, hrange])
    | (rw [← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap, ← AddMonoidHom.range_eq_map, hrange])
  have hrc : (matLat O K N N').relIndex ((matLat O K N N').map (movHom K k k')) =
      ((matLat O K N N').comap (movHom K k k')).relIndex (matLat O K N N') := by
    first
    | exact (AddSubgroup.relIndex_comap _ _).symm
    | rw [AddSubgroup.relIndex_comap]
  have hmapMat : (algebraMap O K).mapMatrix Mat = Matrix.kroneckerMap (· * ·)
      ((k'⁻¹ : GL (Fin N') K) : Matrix (Fin N') (Fin N') K) (k : Matrix (Fin N) (Fin N) K).transpose := by
    ext ⟨i, j⟩ ⟨p, q⟩
    first
    | (rw [RingHom.mapMatrix_apply, Matrix.map_apply, hMat, Matrix.kroneckerMap_apply, Matrix.transpose_apply]; done)
    | (simp [hMat, Matrix.kroneckerMap_apply]; done)
  have hdetA : ((k'⁻¹ : GL (Fin N') K) : Matrix (Fin N') (Fin N') K).det =
      ((k' : Matrix (Fin N') (Fin N') K).det)⁻¹ := by
    first
    | exact eq_inv_of_mul_eq_one_left (by rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one])
    | rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    | simp
  have hπ : algebraMap O K ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Oˣ, algebraMap O K (u₀ : O) =
      algebraMap O K (w : O) ^ N' * (algebraMap O K (w' : O))⁻¹ ^ N :=
    ⟨w ^ N' * w'⁻¹ ^ N, by simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, map_units_inv]⟩
  have hdetK : algebraMap O K Mat.det =
      algebraMap O K ϖ ^ ((N' : ℤ) * a - (N : ℤ) * a') * algebraMap O K (u₀ : O) := by
    rw [hu₀, RingHom.map_det, hmapMat, Matrix.det_kronecker, Matrix.det_transpose, hdetA, hdk, hdk']
    simp only [Fintype.card_fin]
    exact zpow_identity_aux_lemma _ _ _ hπ N N' a a'
  have hU0 : algebraMap O K (u₀ : O) ≠ 0 := (u₀.isUnit.map (algebraMap O K)).ne_zero
  have hd0 : Mat.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdetK
    exact mul_ne_zero (zpow_ne_zero _ hπ) hU0 hdetK.symm
  obtain ⟨m, v, hdv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  have hV : algebraMap O K (v : O) ≠ 0 := (v.isUnit.map (algebraMap O K)).ne_zero
  have h' : algebraMap O K (v : O) * algebraMap O K ϖ ^ m =
      algebraMap O K ϖ ^ ((N' : ℤ) * a - (N : ℤ) * a') * algebraMap O K (u₀ : O) := by
    rw [← hdetK, hdv, map_mul, map_pow]
  have hm : algebraMap O K ϖ ^ m =
      (algebraMap O K (v : O))⁻¹ * (algebraMap O K (v : O) * algebraMap O K ϖ ^ m) := by
    rw [← mul_assoc, inv_mul_cancel₀ hV, one_mul]
  have hkey : algebraMap O K ϖ ^ ((m : ℤ) - ((N' : ℤ) * a - (N : ℤ) * a')) =
      algebraMap O K ((u₀ * v⁻¹ : Oˣ) : O) := by
    rw [zpow_sub₀ hπ, zpow_natCast, Units.val_mul, map_mul, map_units_inv, div_eq_iff (zpow_ne_zero _ hπ), hm, h']
    ring
  have hm0 := zpow_eq_unit ϖ hϖ _ _ hkey
  have he : (N' : ℤ) * a - (N : ℤ) * a' = m := by linarith
  have hc := card_quot_range_toLin' ϖ hϖ Mat m v (by rw [hdv, mul_comm])
  refine ⟨by rw [he]; omega, ?_⟩
  have htoNat : ((N' : ℤ) * a - (N : ℤ) * a').toNat = m := by rw [he]; simp
  rw [htoNat, ← hQ, ← hc, show movLat O K k k' =
    (matLat O K N N').map (movHom K k k') from rfl, hrc, hidx, hsub]
  first
  | rfl
  | exact AddSubgroup.index_eq_card _

end IdxMain

section Model

variable {F M : Type*} [AddCommGroup F] [Module C F] [AddCommGroup M] [Module C M]

def eNat (χ : Γ →* Cˣ) (M₀ M₀' : ℕ) (dg dg' : Γ) (Th : M) : M :=
  (((χ dg ^ (M₀' : ℤ) * χ dg' ^ (-(M₀ : ℤ)) : Cˣ) : C)) • Th

def xiNat (χ : Γ →* Cˣ) (M₀ M₀' : ℕ) (dg₁ dg₂ : Γ) (ΞTh : F →ₗ[C] M) : F →ₗ[C] M :=
  (((χ dg₁ ^ (M₀' : ℤ) * χ dg₂ ^ (-(M₀ : ℤ)) : Cˣ) : C)) • ΞTh

def MapsToUpToSign (ΞTh : F →ₗ[C] M) (oneYP : F) (ThY : M) (s : C) : Prop :=
  ∃ ε : C, (ε = 1 ∨ ε = -1) ∧ ΞTh (s • oneYP) = ε • ThY

theorem exists_norm_eq_one_scaledMap_eq {V : Type*} [Fintype V] (χ : Γ →* Cˣ) (H : Subgroup Γ) (hχH : ∀ h ∈ H, χ h = 1)
    (M₀ M₀' : ℕ) (t : V → Γ) (Q : V → ℕ) (a a' : V → ℤ) (dg dg' dg₁ dg₂ u u' : Γ)
    (hu : u ∈ H) (hu' : u' ∈ H)
    (hk : dg₁ = dg * (∏ v, t v ^ a v) * u) (hk' : dg₂ = dg' * (∏ v, t v ^ a' v) * u')
    (hQ : ∀ v, (Q v : C) ≠ 0) (ht : ∀ v, ‖((χ (t v) : Cˣ) : C)‖ = ‖(Q v : C)‖)
    (n : ℕ) (hn : (n : C) = ∏ v, (Q v : C) ^ idxExp M₀ M₀' (a v) (a' v)) (s : C) (hs : s * s = n)
    (ΞTh : F →ₗ[C] M) (oneYP : F) (ThY : M) (hvac : MapsToUpToSign ΞTh oneYP ThY s) :
    ∃ κ : C, ‖κ‖ = 1 ∧ xiNat χ M₀ M₀' dg₁ dg₂ ΞTh oneYP = κ • eNat χ M₀ M₀' dg dg' ThY := by
  obtain ⟨ε, hε, hΞ⟩ := hvac
  have hn0 : (n : C) ≠ 0 := by
    rw [hn]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (hQ v)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hn0
    rw [← hs, zero_mul]
  have hc0 : ((χ dg ^ (M₀' : ℤ) * χ dg' ^ (-(M₀ : ℤ)) : Cˣ) : C) ≠ 0 := Units.ne_zero _
  refine ⟨ε * (s⁻¹ * chiRatio χ M₀ M₀' dg dg' dg₁ dg₂), ?_, ?_⟩
  · rw [norm_mul, norm_inv_mul_charRatio χ H hχH M₀ M₀' t Q a a' dg dg' dg₁ dg₂ u u' hu hu' hk hk' hQ ht n hn s hs,
      mul_one]
    rcases hε with rfl | rfl
    · exact norm_one
    · rw [norm_neg, norm_one]
  · have hx : ΞTh oneYP = s⁻¹ • ε • ThY := by
      rw [← hΞ, map_smul, inv_smul_smul₀ hs0]
    simp only [xiNat, eNat, chiRatio, LinearMap.smul_apply, hx, smul_smul, Units.val_div_eq_div_val]
    congr 1
    first
    | (rw [mul_assoc ε, mul_assoc s⁻¹, div_mul_cancel₀ _ hc0]
       ring)
    | (field_simp
       ring)

end Model

section Assembled

theorem exists_norm_eq_one_scaledMap_eq_of_relIndex {V : Type*} [Fintype V] (OV KV : V → Type) [∀ v, CommRing (OV v)] [∀ v, IsDomain (OV v)]
    [∀ v, IsDiscreteValuationRing (OV v)] [∀ v, Field (KV v)] [∀ v, Algebra (OV v) (KV v)]
    [∀ v, IsFractionRing (OV v) (KV v)] (ϖ : ∀ v, OV v) (hϖ : ∀ v, Irreducible (ϖ v))
    (χ : Γ →* Cˣ) (H : Subgroup Γ) (hχH : ∀ h ∈ H, χ h = 1) (M₀ M₀' : ℕ)
    (k : ∀ v, GL (Fin (2 * M₀)) (KV v)) (k' : ∀ v, GL (Fin (2 * M₀')) (KV v)) (a a' : V → ℤ)
    (wv wv' : ∀ v, (OV v)ˣ)
    (hdk : ∀ v, (k v : Matrix (Fin (2 * M₀)) (Fin (2 * M₀)) (KV v)).det =
      algebraMap (OV v) (KV v) (ϖ v) ^ a v * algebraMap (OV v) (KV v) (wv v : OV v))
    (hdk' : ∀ v, (k' v : Matrix (Fin (2 * M₀')) (Fin (2 * M₀')) (KV v)).det =
      algebraMap (OV v) (KV v) (ϖ v) ^ a' v * algebraMap (OV v) (KV v) (wv' v : OV v))
    (hle : ∀ v, matLat (OV v) (KV v) (2 * M₀) (2 * M₀') ≤ movLat (OV v) (KV v) (k v) (k' v))
    (t : V → Γ) (dg dg' dg₁ dg₂ u u' : Γ) (hu : u ∈ H) (hu' : u' ∈ H)
    (hk : dg₁ = dg * (∏ v, t v ^ a v) * u) (hk' : dg₂ = dg' * (∏ v, t v ^ a' v) * u')
    (hQ : ∀ v, ((Nat.card (IsLocalRing.ResidueField (OV v)) : ℕ) : C) ≠ 0)
    (ht : ∀ v, ‖((χ (t v) : Cˣ) : C)‖ = ‖((Nat.card (IsLocalRing.ResidueField (OV v)) : ℕ) : C)‖)
    (s : C) (hs : s * s = ((∏ v, (matLat (OV v) (KV v) (2 * M₀) (2 * M₀')).relIndex
      (movLat (OV v) (KV v) (k v) (k' v)) : ℕ) : C))
    {F M : Type*} [AddCommGroup F] [Module C F] [AddCommGroup M] [Module C M]
    (ΞTh : F →ₗ[C] M) (oneYP : F) (ThY : M) (hvac : MapsToUpToSign ΞTh oneYP ThY s) :
    ∃ κ : C, ‖κ‖ = 1 ∧ xiNat χ M₀ M₀' dg₁ dg₂ ΞTh oneYP = κ • eNat χ M₀ M₀' dg dg' ThY := by
  have hR := fun v => relIndexFormula (OV v) (KV v) (ϖ v) (hϖ v) _ rfl (2 * M₀) (2 * M₀') (k v) (k' v)
    (a v) (a' v) (wv v) (wv' v) (hdk v) (hdk' v) (hle v)
  refine exists_norm_eq_one_scaledMap_eq χ H hχH M₀ M₀' t (fun v => Nat.card (IsLocalRing.ResidueField (OV v)))
    a a' dg dg' dg₁ dg₂ u u' hu hu' hk hk' hQ ht _ ?_ s hs ΞTh oneYP ThY hvac
  refine hn_of_idx M₀ M₀' _ a a' _ (fun v => ?_) (fun v => ?_)
  · rw [idxExp_eq]
    exact (hR v).1
  · rw [idxExp_eq]
    exact (hR v).2

end Assembled

end UnitaryThetaMoves

end
