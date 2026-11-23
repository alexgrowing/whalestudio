import Mathlib

namespace GlobalTheory.LiftDeriv

theorem krullDimLE_and_isLocalRing_quotient {P : Type} [CommRing P] (Q S : Ideal P) [hQ : Q.IsMaximal]
    (n : ℕ) (h1 : Q ^ (n + 1) ≤ S) (h2 : S ≤ Q) :
    Ring.KrullDimLE 0 (P ⧸ S) ∧ IsLocalRing (P ⧸ S) := by
  have hSt : S ≠ ⊤ := fun h => hQ.ne_top (top_le_iff.1 (h ▸ h2))
  have : Nontrivial (P ⧸ S) := Ideal.Quotient.nontrivial_iff.2 hSt
  have key : ∀ M : Ideal (P ⧸ S), M.IsPrime → M = Q.map (Ideal.Quotient.mk S) := by
    intro M hM
    have hc : (M.comap (Ideal.Quotient.mk S)).IsPrime := Ideal.comap_isPrime _ _
    have h3 : Q ≤ M.comap (Ideal.Quotient.mk S) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (h1 ha)]
      exact M.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M).symm.trans
      (congrArg _ (hQ.eq_of_le hc.ne_top h3).symm)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (P ⧸ S)
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (P ⧸ S)).out 1 0 rfl rfl).mp
    ⟨M, hM.isPrime, fun M' hM' => (key M' hM').trans (key M hM.isPrime).symm⟩

theorem exists_derivation_extending : ∀ (A P R K : Type) [CommRing A] [CommRing P] [IsNoetherianRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], Function.Surjective (algebraMap P R) → Function.Surjective (algebraMap R K) → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (algebraMap A R) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (algebraMap A R) = β) → ∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i := by
  intro A P R K _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf hg hlift ℓ
  have hPK : algebraMap P K = (algebraMap R K).comp (algebraMap P R) := IsScalarTower.algebraMap_eq P R K
  have hQm : (RingHom.ker (algebraMap P K)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (by rw [hPK]; exact hg.comp hf)
  have hIQ : RingHom.ker (algebraMap P R) ≤ RingHom.ker (algebraMap P K) := fun x hx => by
    rw [RingHom.mem_ker] at hx ⊢
    rw [hPK, RingHom.comp_apply, hx, map_zero]
  generalize hI : RingHom.ker (algebraMap P R) = I at ℓ hIQ
  generalize hQ : RingHom.ker (algebraMap P K) = Q at hQm hIQ
  let J : Ideal P := Submodule.map I.subtype (LinearMap.ker ℓ)
  have hJI : J ≤ I := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hJ : ∀ (i i' : P) (hi : i ∈ I) (hi' : i' ∈ I), i' - i ∈ J → ℓ ⟨i, hi⟩ = ℓ ⟨i', hi'⟩ := by
    intro i i' hi hi' h
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 h
    have e : x = ⟨i', hi'⟩ - ⟨i, hi⟩ := Subtype.ext (by simpa using hxe)
    rw [LinearMap.mem_ker, e, map_sub, sub_eq_zero] at hx
    exact hx.symm
  have hQIJ : Q * I ≤ J := by
    refine Ideal.mul_le.2 fun q hq i hi => ?_
    refine Submodule.mem_map.2 ⟨⟨q * i, I.mul_mem_left q hi⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker]
    have e : (⟨q * i, I.mul_mem_left q hi⟩ : I) = q • ⟨i, hi⟩ := rfl
    rw [e, map_smul, Algebra.smul_def]
    have hq0 : algebraMap P K q = 0 := by rw [← RingHom.mem_ker, hQ]; exact hq
    rw [hq0, zero_mul]
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul Q (I : Submodule P P)
  have hAR : Q ^ (k + 1) ⊓ I ≤ J := by
    have h := hk (k + 1) (Nat.le_succ k)
    rw [Nat.add_sub_cancel_left, pow_one] at h
    have e : (Q ^ (k + 1) • ⊤ : Submodule P P) = Q ^ (k + 1) := by rw [smul_eq_mul, Ideal.mul_top]
    rw [e] at h
    rw [h]
    exact le_trans (Submodule.smul_mono le_rfl inf_le_right) hQIJ

  let S : Ideal P := J ⊔ Q ^ (k + 1)
  let T : Ideal P := I ⊔ Q ^ (k + 1)
  have hST : S ≤ T := sup_le_sup_right hJI _
  have hSQ : S ≤ Q := sup_le (hJI.trans hIQ) (Ideal.pow_le_self (Nat.succ_ne_zero k))
  obtain ⟨hdim, hloc⟩ := krullDimLE_and_isLocalRing_quotient Q S k le_sup_right hSQ
  haveI : IsArtinianRing (P ⧸ S) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let π : P ⧸ S →+* P ⧸ T := Ideal.Quotient.factor hST
  have hπmk : ∀ x, π (Ideal.Quotient.mk S x) = Ideal.Quotient.mk T x := fun x => rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, hπmk x⟩
  have hTT : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ S := by
    intro x hx y hy
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨i', hi', z', hz', rfl⟩ := Submodule.mem_sup.1 hy
    have e : (i + z) * (i' + z') = i * i' + (i * z' + z * (i' + z')) := by ring
    rw [e]
    refine S.add_mem (Ideal.mem_sup_left (hQIJ (Ideal.mul_mem_mul (hIQ hi) hi'))) (Ideal.mem_sup_right ?_)
    exact (Q ^ (k + 1)).add_mem (Ideal.mul_mem_left _ _ hz') (Ideal.mul_mem_right _ _ hz)
  have hsq : RingHom.ker π ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun c hc d hd => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [RingHom.mem_ker, hπmk, Ideal.Quotient.eq_zero_iff_mem] at hc hd
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hTT x hc y hd
  let β : A →+* P ⧸ S := (Ideal.Quotient.mk S).comp (algebraMap A P)
  have hIT : RingHom.ker (algebraMap P R) ≤ T := hI ▸ le_sup_left
  let e := RingHom.quotientKerEquivOfSurjective hf
  let L : P ⧸ RingHom.ker (algebraMap P R) →+* P ⧸ T :=
    Ideal.Quotient.lift (RingHom.ker (algebraMap P R)) (Ideal.Quotient.mk T)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hIT ha))
  let φ₀ : R →+* P ⧸ T := L.comp e.symm.toRingHom
  have hφ₀ : ∀ a, φ₀ (algebraMap P R a) = Ideal.Quotient.mk T a := by
    intro a
    have h1 : e.symm (algebraMap P R a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    change L (e.symm (algebraMap P R a)) = _
    rw [h1, Ideal.Quotient.lift_mk]
  have hcomp : φ₀.comp (algebraMap A R) = π.comp β := by
    ext r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A P R r, hφ₀]
    rfl
  obtain ⟨φ, hφπ, hφA⟩ := hlift (P ⧸ S) (P ⧸ T) π hπs hsq β φ₀ hcomp

  let δ : P → P ⧸ S := fun a => Ideal.Quotient.mk S a - φ (algebraMap P R a)
  have hδ : ∀ a, δ a ∈ RingHom.ker π := by
    intro a
    rw [RingHom.mem_ker]
    show π (Ideal.Quotient.mk S a - φ (algebraMap P R a)) = 0
    rw [map_sub, hπmk, ← RingHom.comp_apply, hφπ, hφ₀, sub_self]
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := by
    intro a b
    show Ideal.Quotient.mk S (a + b) - φ (algebraMap P R (a + b)) = _
    rw [map_add, map_add, map_add]
    show _ = (Ideal.Quotient.mk S a - φ (algebraMap P R a)) + (Ideal.Quotient.mk S b - φ (algebraMap P R b))
    ring
  have hδmul : ∀ a b, δ (a * b) = Ideal.Quotient.mk S a * δ b + Ideal.Quotient.mk S b * δ a := by
    intro a b
    have h0 : δ a * δ b = 0 := by
      have : δ a * δ b ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul (hδ a) (hδ b)
      rw [hsq] at this
      exact (Ideal.mem_bot.1 this)
    change (Ideal.Quotient.mk S a - φ (algebraMap P R a)) * (Ideal.Quotient.mk S b - φ (algebraMap P R b)) = 0 at h0
    show Ideal.Quotient.mk S (a * b) - φ (algebraMap P R (a * b)) =
      Ideal.Quotient.mk S a * (Ideal.Quotient.mk S b - φ (algebraMap P R b)) +
        Ideal.Quotient.mk S b * (Ideal.Quotient.mk S a - φ (algebraMap P R a))
    rw [map_mul, map_mul, map_mul]
    linear_combination -h0

  let Rl : P ⧸ S → K → Prop := fun c v => ∃ (i : P) (hi : i ∈ I), ∃ z ∈ Q ^ (k + 1),
    Ideal.Quotient.mk S (i + z) = c ∧ ℓ ⟨i, hi⟩ = v
  have huniq : ∀ c v v', Rl c v → Rl c v' → v = v' := by
    rintro c v v' ⟨i, hi, z, hz, rfl, rfl⟩ ⟨i', hi', z', hz', he, rfl⟩
    rw [Ideal.Quotient.eq] at he
    obtain ⟨j, hj, w, hw, hjw⟩ := Submodule.mem_sup.1 he
    have hmem : i' - i - j ∈ Q ^ (k + 1) ⊓ I := by
      refine ⟨?_, (I.sub_mem (I.sub_mem hi' hi) (hJI hj))⟩
      have e1 : i' - i - j = w + z - z' := by linear_combination -hjw
      rw [e1]
      exact (Q ^ (k + 1)).sub_mem ((Q ^ (k + 1)).add_mem hw hz) hz'
    have h2 : i' - i ∈ J := by
      have := J.add_mem (hAR hmem) hj
      rwa [sub_add_cancel] at this
    exact hJ i i' hi hi' h2
  have hex : ∀ c : P ⧸ S, π c = 0 → ∃ v, Rl c v := by
    intro c hc
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hπmk, Ideal.Quotient.eq_zero_iff_mem] at hc
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hc
    exact ⟨_, i, hi, z, hz, rfl, rfl⟩
  have hRadd : ∀ c c' v v', Rl c v → Rl c' v' → Rl (c + c') (v + v') := by
    rintro c c' v v' ⟨i, hi, z, hz, rfl, rfl⟩ ⟨i', hi', z', hz', rfl, rfl⟩
    refine ⟨i + i', I.add_mem hi hi', z + z', (Q ^ (k + 1)).add_mem hz hz', ?_, ?_⟩
    · rw [← map_add]; congr 1; ring
    · rw [← map_add]; rfl
  have hRsmul : ∀ c v (p : P), Rl c v → Rl (Ideal.Quotient.mk S p * c) (p • v) := by
    rintro c v p ⟨i, hi, z, hz, rfl, rfl⟩
    refine ⟨p * i, I.mul_mem_left p hi, p * z, Ideal.mul_mem_left _ p hz, ?_, ?_⟩
    · rw [← map_mul]; congr 1; ring
    · rw [← map_smul]; rfl
  have hR0 : Rl 0 0 := ⟨0, I.zero_mem, 0, (Q ^ (k + 1)).zero_mem, by simp, map_zero ℓ⟩
  have hRI : ∀ i (hi : i ∈ I), Rl (Ideal.Quotient.mk S i) (ℓ ⟨i, hi⟩) :=
    fun i hi => ⟨i, hi, 0, (Q ^ (k + 1)).zero_mem, by rw [add_zero], rfl⟩
  let D0 : P → K := fun a => Classical.choose (hex (δ a) (hδ a))
  have hD0 : ∀ a v, Rl (δ a) v → D0 a = v := fun a v h =>
    huniq _ _ _ (Classical.choose_spec (hex (δ a) (hδ a))) h
  have hspec : ∀ a, Rl (δ a) (D0 a) := fun a => Classical.choose_spec (hex (δ a) (hδ a))
  have hDadd : ∀ a b, D0 (a + b) = D0 a + D0 b := fun a b =>
    hD0 _ _ (by rw [hδadd]; exact hRadd _ _ _ _ (hspec a) (hspec b))
  have hDmul : ∀ a b, D0 (a * b) = a • D0 b + b • D0 a := fun a b =>
    hD0 _ _ (by rw [hδmul]; exact hRadd _ _ _ _ (hRsmul _ _ a (hspec b)) (hRsmul _ _ b (hspec a)))
  have hDA : ∀ r : A, D0 (algebraMap A P r) = 0 := by
    intro r
    refine hD0 _ _ ?_
    have : δ (algebraMap A P r) = 0 := by
      show Ideal.Quotient.mk S (algebraMap A P r) - φ (algebraMap P R (algebraMap A P r)) = 0
      rw [← IsScalarTower.algebraMap_apply A P R r, ← RingHom.comp_apply φ, hφA, sub_eq_zero]
      rfl
    rw [this]; exact hR0
  let Dl : P →ₗ[A] K :=
    { toFun := D0
      map_add' := hDadd
      map_smul' := fun r a => by
        rw [Algebra.smul_def, hDmul, hDA, smul_zero, add_zero, RingHom.id_apply, algebraMap_smul] }
  refine ⟨Derivation.mk' Dl hDmul, fun ⟨i, hi⟩ => ?_⟩
  show D0 i = ℓ ⟨i, hi⟩
  refine hD0 _ _ ?_
  have : δ i = Ideal.Quotient.mk S i := by
    show Ideal.Quotient.mk S i - φ (algebraMap P R i) = _
    have hi0 : algebraMap P R i = 0 := by rw [← RingHom.mem_ker, hI]; exact hi
    rw [hi0, map_zero, sub_zero]
  rw [this]; exact hRI i hi

end GlobalTheory.LiftDeriv
