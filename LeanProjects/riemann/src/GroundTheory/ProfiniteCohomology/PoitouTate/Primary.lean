import Mathlib
import GroundTheory.ProfiniteCohomology.PoincarePairs
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section Dual

variable {G : Type u} [Group G]

theorem nsmul_dualRep_eq_zero_of_nsmul {q : ℕ} {D M : Rep.{u} (ULift.{u} ℤ) G}
    (hM : ∀ m : M, q • m = 0) (f : dualRep D M) : q • f = 0 := by
  let f' : M →ₗ[ULift.{u} ℤ] D := f
  change q • f' = 0
  refine LinearMap.ext fun m => ?_
  rw [LinearMap.smul_apply, ← map_nsmul, hM, map_zero, LinearMap.zero_apply]

variable (D Dq : Rep.{u} (ULift.{u} ℤ) G) (j : Dq ⟶ D) (M : Rep.{u} (ULift.{u} ℤ) G)

def dualRepPost : dualRep Dq M ⟶ dualRep D M :=
  (Rep.ihom M).map j

theorem dualRepPost_hom_apply (f : M →ₗ[ULift.{u} ℤ] Dq) (m : M) :
    ((dualRepPost D Dq j M).hom f : M →ₗ[ULift.{u} ℤ] D) m = j.hom (f m) :=
  rfl

theorem tensorHom_dualRepPost_dualEvalPairing :
    (dualRepPost D Dq j M ⊗ₘ 𝟙 M) ≫ dualEvalPairing D M =
      (𝟙 (dualRep Dq M) ⊗ₘ 𝟙 M) ≫ (dualEvalPairing Dq M ≫ j) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bijective_dualRepPost {N q : ℕ} [NeZero N] [NeZero q] (hD : Nonempty (D ≃+ ZMod N))
    (hDq : Nonempty (Dq ≃+ ZMod q)) (hj : Function.Injective j.hom) [Finite M]
    (hM : ∀ m : M, q • m = 0) : Function.Bijective (dualRepPost D Dq j M).hom := by
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite Dq := finite_of_nonempty_addEquiv hDq
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep Dq M) := finite_dualRep
  have : Finite (dualRep Dq (dualRep Dq M)) := finite_dualRep
  refine Function.Injective.bijective_of_nat_card_le (fun f f' hff' => ?_) ?_
  · exact LinearMap.ext fun m => hj (LinearMap.congr_fun hff' m)
  · calc Nat.card (dualRep D M) ≤ Nat.card M := card_dualRep_le hD
      _ ≤ Nat.card (dualRep Dq (dualRep Dq M)) :=
          Nat.card_le_card_of_injective _ (bijective_toDualDual hDq hM).1
      _ ≤ Nat.card (dualRep Dq M) := card_dualRep_le hDq

end Dual

section SmulSubrep

variable {k G : Type u} [CommRing k] [Group G] (M : Rep.{u} k G) (c : k)

abbrev smulSubrep : Rep.{u} k G :=
  M.subrepresentation (LinearMap.range (c • LinearMap.id : M →ₗ[k] M)) (by
    rintro g _ ⟨b, rfl⟩
    exact ⟨M.ρ g b, by simp⟩)

def smulSubrepProj : M ⟶ smulSubrep M c :=
  Rep.ofHom ⟨(c • LinearMap.id : M →ₗ[k] M).rangeRestrict, fun g => LinearMap.ext fun b =>
    Subtype.ext (by simp)⟩

def smulSubrepIncl : smulSubrep M c ⟶ M :=
  M.subtype _ _

theorem smulSubrepProj_smulSubrepIncl : smulSubrepProj M c ≫ smulSubrepIncl M c = c • 𝟙 M := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun b => ?_))
  rfl

theorem exists_eq_smul_of_smulSubrep (x : smulSubrep M c) : ∃ m : M, x.1 = c • m := by
  obtain ⟨y, m, rfl⟩ := x
  exact ⟨m, rfl⟩

def smulSubrepPair (c₀ c₁ : k) : Bool → Rep.{u} k G :=
  fun j => Bool.rec (smulSubrep M c₀) (smulSubrep M c₁) j

def smulSubrepPairIncl (c₀ c₁ : k) : ∀ j, smulSubrepPair M c₀ c₁ j ⟶ M :=
  fun j => Bool.rec (smulSubrepIncl M c₀) (smulSubrepIncl M c₁) j

def smulSubrepPairProj (c₀ c₁ : k) : ∀ j, M ⟶ smulSubrepPair M c₀ c₁ j :=
  fun j => Bool.rec (smulSubrepProj M c₀) (smulSubrepProj M c₁) j

theorem sum_smulSubrepPairProj_incl (c₀ c₁ : k) (hc : c₀ + c₁ = 1) :
    ∑ j, smulSubrepPairProj M c₀ c₁ j ≫ smulSubrepPairIncl M c₀ c₁ j = 𝟙 M := by
  rw [Fintype.sum_bool]
  change smulSubrepProj M c₁ ≫ smulSubrepIncl M c₁ + smulSubrepProj M c₀ ≫ smulSubrepIncl M c₀ = 𝟙 M
  rw [smulSubrepProj_smulSubrepIncl, smulSubrepProj_smulSubrepIncl, ← add_smul, add_comm, hc, one_smul]

instance finite_smulSubrep [Finite M] : Finite (smulSubrep M c) :=
  inferInstanceAs (Finite (LinearMap.range (c • LinearMap.id : M →ₗ[k] M)))

instance isDiscreteRep_smulSubrep [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep M] :
    IsDiscreteRep (smulSubrep M c) :=
  ⟨fun x => Subgroup.isOpen_mono (H₁ := stabilizer M.ρ x.1) (fun g hg => by
    rw [mem_stabilizer] at hg ⊢
    exact Subtype.ext hg) (isOpen_stabilizer M x.1)⟩

instance isDiscreteRep_smulSubrepPair [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep M]
    (c₀ c₁ : k) (j : Bool) : IsDiscreteRep (smulSubrepPair M c₀ c₁ j) := by
  cases j
  · exact isDiscreteRep_smulSubrep M c₀
  · exact isDiscreteRep_smulSubrep M c₁

instance finite_smulSubrepPair [Finite M] (c₀ c₁ : k) (j : Bool) : Finite (smulSubrepPair M c₀ c₁ j) := by
  cases j
  · exact finite_smulSubrep M c₀
  · exact finite_smulSubrep M c₁

end SmulSubrep

section Killed

variable {G : Type u} [Group G]

theorem nsmul_smulSubrep_eq_zero {M : Rep.{u} (ULift.{u} ℤ) G} {a b : ℕ}
    (hM : ∀ m : M, (a * b) • m = 0) (β : ℤ) (x : smulSubrep M ((β * b : ℤ) : ULift.{u} ℤ)) :
    a • x = 0 := by
  obtain ⟨m, hm⟩ := exists_eq_smul_of_smulSubrep M _ x
  refine Subtype.ext ?_
  change a • x.1 = 0
  rw [hm, smul_comm, Int.cast_smul_eq_zsmul, mul_zsmul, natCast_zsmul, ← mul_nsmul, hM, zsmul_zero]

end Killed

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

section Level

variable {N q : ℕ} [NeZero N] [NeZero q] (D Dq : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
  [IsDiscreteRep Dq] (j : Dq ⟶ D) (t : compactCohomologyRes φ D 3 →+ ZMod N)
  (tq : compactCohomologyRes φ Dq 3 →+ ZMod q)
  (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]

theorem bijective_compactDualityMap_of_level
    (htj : ∀ z, zmodToQZ N (t ((compactCohomologyResMap φ j 3).hom z)) = zmodToQZ q (tq z))
    (hD : Nonempty (D ≃+ ZMod N)) (hDq : Nonempty (Dq ≃+ ZMod q)) (hj : Function.Injective j.hom)
    (hM : ∀ m : M, q • m = 0) {r s : ℕ} (h : r + s = 3)
    (hq : Function.Bijective (compactDualityMap φ Dq h tq M)) :
    Function.Bijective (compactDualityMap φ D h t M) := by
  have hJ := bijective_dualRepPost D Dq j M hD hDq hj hM
  set e := Rep.isoOfBijective (dualRepPost D Dq j M) hJ
  have hJc : Function.Bijective (compactCohomologyResMap φ (dualRepPost D Dq j M) s).hom :=
    bijective_compactCohomologyResMap_of_comp_eq_id φ e.hom e.inv e.hom_inv_id e.inv_hom_id s
  have key : ∀ x y', zmodToQZ N (compactDualityMap φ D h t M x
      ((compactCohomologyResMap φ (dualRepPost D Dq j M) s).hom y')) =
        zmodToQZ q (compactDualityMap φ Dq h tq M x y') := by
    intro x y'
    rw [compactDualityMap_apply, compactDualityMap_apply,
      compactCupRes_compactCohomologyResMap φ (dualEvalPairing D M) (dualEvalPairing Dq M ≫ j)
        (dualRepPost D Dq j M) (𝟙 M) (tensorHom_dualRepPost_dualEvalPairing D Dq j M),
      cohomologyMap_id, ModuleCat.id_apply, ← compactCohomologyResMap_compactCupRes, htj]
  have hkill : ∀ y : compactCohomologyRes φ (dualRep Dq M) s, q • y = 0 :=
    nsmul_compactCohomologyRes_eq_zero φ (nsmul_dualRep_eq_zero_of_nsmul hM) s
  refine ⟨fun x₁ x₂ hx => hq.1 (AddMonoidHom.ext fun y' => zmodToQZ_injective ?_), fun χ => ?_⟩
  · rw [← key, ← key, hx]
  · let F : compactCohomologyRes φ (dualRep Dq M) s →+ QZ :=
      ((zmodToQZ N).comp χ).comp (compactCohomologyResMap φ (dualRepPost D Dq j M) s).hom.toAddMonoidHom
    have hF : ∀ y', q • F y' = 0 := fun y' => by rw [← map_nsmul, hkill, map_zero]
    obtain ⟨x, hx⟩ := hq.2 (zmodOfQZ F hF)
    refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
    obtain ⟨y', rfl⟩ := hJc.2 y
    apply zmodToQZ_injective (n := N)
    rw [key, hx, zmodToQZ_zmodOfQZ]
    rfl

end Level

section Primary

variable {N : ℕ} [NeZero N] (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
  (t : compactCohomologyRes φ D 3 →+ ZMod N)
  (Dp : ℕ → Rep.{u} (ULift.{u} ℤ) G) [∀ p, IsDiscreteRep (Dp p)]
  (tp : ∀ p, compactCohomologyRes φ (Dp p) 3 →+ ZMod (p ^ N.factorization p))
  (jp : ∀ p, Dp p ⟶ D)

end Primary

section Primary

variable {N : ℕ} [NeZero N] (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
  (t : compactCohomologyRes φ D 3 →+ ZMod N)
  (Dp : ℕ → Rep.{u} (ULift.{u} ℤ) G) [∀ p, IsDiscreteRep (Dp p)]
  (tp : ∀ p, compactCohomologyRes φ (Dp p) 3 →+ ZMod (p ^ N.factorization p))
  (jp : ∀ p, Dp p ⟶ D)

theorem bijective_compactDualityMap_of_primePow (hD : Nonempty (D ≃+ ZMod N))
    (hDp : ∀ p ∈ N.primeFactors, Nonempty (Dp p ≃+ ZMod (p ^ N.factorization p)))
    (hjp : ∀ p ∈ N.primeFactors, Function.Injective (jp p).hom)
    (htp : ∀ p ∈ N.primeFactors, ∀ z, zmodToQZ N (t ((compactCohomologyResMap φ (jp p) 3).hom z)) =
      zmodToQZ (p ^ N.factorization p) (tp p z))
    (hφp : ∀ p ∈ N.primeFactors, ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
      (∀ m : M, p ^ N.factorization p • m = 0) → ∀ {r s : ℕ} (h : r + s = 3),
        Function.Bijective (compactDualityMap φ (Dp p) h (tp p) M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, N • m = 0) {r s : ℕ}
    (h : r + s = 3) : Function.Bijective (compactDualityMap φ D h t M) := by

  have hq : ∀ p ∈ N.primeFactors, ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
      (∀ m : M, p ^ N.factorization p • m = 0) → Function.Bijective (compactDualityMap φ D h t M) := by
    intro p hp M _ _ hMp
    have : NeZero (p ^ N.factorization p) := ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    exact bijective_compactDualityMap_of_level φ D (Dp p) (jp p) t (tp p) M (htp p hp) hD (hDp p hp)
      (hjp p hp) hMp h (hφp p hp M hMp h)
  suffices H : ∀ d, d ∣ N → ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
      (∀ m : M, d • m = 0) → Function.Bijective (compactDualityMap φ D h t M) from
    H N dvd_rfl M hM
  intro d
  induction d using Nat.recOnPrimeCoprime with
  | zero => exact fun h0 => absurd (Nat.eq_zero_of_zero_dvd h0) (NeZero.ne N)
  | prime_pow p n hp =>
    intro hpn M _ _ hMd
    rcases Nat.eq_zero_or_pos n with rfl | hn
    ·
      have hM0 : ∀ m : M, m = 0 := fun m => by simpa using hMd m
      by_cases hN1 : N = 1
      · have : Subsingleton M := ⟨fun x y => (hM0 x).trans (hM0 y).symm⟩
        have := subsingleton_cohomology_of_subsingleton M r
        subst hN1
        refine ⟨fun x y _ => Subsingleton.elim x y, fun χ => ⟨0, AddMonoidHom.ext fun y => ?_⟩⟩
        exact Subsingleton.elim _ _
      · obtain ⟨p', hp', hp'N⟩ := Nat.exists_prime_and_dvd hN1
        exact hq p' (Nat.mem_primeFactors.2 ⟨hp', hp'N, NeZero.ne N⟩) M
          (fun m => by rw [hM0 m, nsmul_zero])
    · have hpN : p ∈ N.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p hn.ne').trans hpn, NeZero.ne N⟩
      have hle : n ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization (NeZero.ne N)).1 hpn
      refine hq p hpN M fun m => ?_
      obtain ⟨c, hc⟩ := pow_dvd_pow p hle
      rw [hc, mul_comm, mul_nsmul, hMd]
  | coprime a b ha hb hab iha ihb =>
    intro habN M _ _ hMd
    obtain ⟨α, β, hαβ⟩ := Nat.isCoprime_iff_coprime.2 hab
    refine bijective_compactDualityMap_of_sum φ D h t
      (smulSubrepPair M ((α * a : ℤ) : ULift.{u} ℤ) ((β * b : ℤ) : ULift.{u} ℤ)) M
      (smulSubrepPairIncl M _ _) (smulSubrepPairProj M _ _)
      (sum_smulSubrepPairProj_incl M _ _ (by rw [← Int.cast_add, hαβ, Int.cast_one])) (fun j => ?_)
    cases j with
      | true =>
        exact iha (dvd_of_mul_right_dvd habN) (smulSubrep M ((β * b : ℤ) : ULift.{u} ℤ))
          (nsmul_smulSubrep_eq_zero (fun m => hMd m) β)
      | false =>
        exact ihb (dvd_of_mul_left_dvd habN) (smulSubrep M ((α * a : ℤ) : ULift.{u} ℤ))
          (nsmul_smulSubrep_eq_zero (fun m => by rw [mul_comm]; exact hMd m) α)

end Primary

end GroundTheory.ProfCoh
