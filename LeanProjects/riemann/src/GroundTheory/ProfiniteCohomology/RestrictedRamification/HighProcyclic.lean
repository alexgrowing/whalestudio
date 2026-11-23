import Mathlib
import GroundTheory.ProfiniteCohomology.Procyclic
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

structure IsPrimePowGenerator {G : Type*} [Group G] [TopologicalSpace G] (ℓ : ℕ) (σ : G) : Prop where

  dense : IsTopologicalGenerator σ

  exists_hom : ∀ b : ℕ, ∃ φ : G →* Multiplicative (ZMod (ℓ ^ b)),
    IsOpen (φ.ker : Set G) ∧ φ σ = Multiplicative.ofAdd 1

section Quotient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem IsTopologicalGenerator.exists_zpow_mk_eq {σ : G} (hσ : IsTopologicalGenerator σ) (U : Subgroup G)
    [U.Normal] (hU : IsOpen (U : Set G)) (y : G ⧸ U) : ∃ m : ℤ, (QuotientGroup.mk σ : G ⧸ U) ^ m = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have ho : IsOpen {x : G | g⁻¹ * x ∈ U} := hU.preimage (continuous_const.mul continuous_id)
  obtain ⟨x, hxσ, hx⟩ := hσ.exists_mem_open ho ⟨g, by simp [U.one_mem]⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxσ
  refine ⟨m, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
  have hx' : g⁻¹ * σ ^ m ∈ U := hx
  simpa using inv_mem hx'

variable [CompactSpace G]

theorem IsTopologicalGenerator.exists_hom_zmod_orderOf {σ : G} (hσ : IsTopologicalGenerator σ) (U : Subgroup G)
    [U.Normal] (hU : IsOpen (U : Set G)) :
    ∃ φ : G →* Multiplicative (ZMod (orderOf (QuotientGroup.mk σ : G ⧸ U))),
      U ≤ φ.ker ∧ φ σ = Multiplicative.ofAdd 1 := by
  have : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  set τ : G ⧸ U := QuotientGroup.mk σ with hτ
  set L := orderOf τ with hL
  let f : ℤ →+ Additive (G ⧸ U) := zmultiplesHom (Additive (G ⧸ U)) (Additive.ofMul τ)
  have hf : f (L : ℤ) = 0 := by
    change (L : ℤ) • Additive.ofMul τ = 0
    rw [natCast_zsmul, ← ofMul_pow, hL, pow_orderOf_eq_one, ofMul_one]
  let ψ : ZMod L →+ Additive (G ⧸ U) := ZMod.lift L ⟨f, hf⟩
  have hψ : ∀ m : ℤ, ψ (m : ZMod L) = Additive.ofMul (τ ^ m) := fun m => by
    change ZMod.lift L ⟨f, hf⟩ (m : ZMod L) = _
    rw [ZMod.lift_coe]
    change m • Additive.ofMul τ = _
    rw [← ofMul_zpow]
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective k
    rw [hψ, ← ofMul_one, Additive.ofMul.injective.eq_iff] at hk
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact orderOf_dvd_iff_zpow_eq_one.2 hk
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨m, hm⟩ := hσ.exists_zpow_mk_eq U hU (Additive.toMul y)
    exact ⟨m, by rw [hψ, hm]; rfl⟩
  let e : ZMod L ≃+ Additive (G ⧸ U) := AddEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  let φ : G →* Multiplicative (ZMod L) :=
    (AddMonoidHom.toMultiplicativeRight e.symm.toAddMonoidHom).comp (QuotientGroup.mk' U)
  refine ⟨φ, fun u hu => ?_, ?_⟩
  · rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (e.symm (Additive.ofMul (QuotientGroup.mk u : G ⧸ U))) = 1
    rw [(QuotientGroup.eq_one_iff u).2 hu, ofMul_one, map_zero, ofAdd_zero]
  · change Multiplicative.ofAdd (e.symm (Additive.ofMul τ)) = _
    congr 1
    rw [AddEquiv.symm_apply_eq]
    change Additive.ofMul τ = ψ 1
    have h1 := hψ 1
    rw [Int.cast_one, zpow_one] at h1
    exact h1.symm

end Quotient

section Cocycle

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Rep.{u} k G} {σ : G} [IsDiscreteRep A]

theorem IsTopologicalGenerator.exists_cocycle_of_hom (hσ : IsTopologicalGenerator σ) (L : ℕ) [NeZero L]
    (φ : G →* Multiplicative (ZMod L)) (hφo : IsOpen (φ.ker : Set G)) (hφσ : φ σ = Multiplicative.ofAdd 1)
    (a : A) (hmem : σ ^ L ∈ stabilizer A.ρ a) (hsum : ∑ i ∈ Finset.range L, A.ρ (σ ^ i) a = 0) :
    ∃ f : (Fin 1 → G) → A, IsLocallyConstant f ∧ (inhomogeneousCochains.d A 1).hom f = 0 ∧
      f (fun _ => σ) = a := by
  have hρ : ∀ (x y : ℤ) (v : A), A.ρ (σ ^ x) (A.ρ (σ ^ y) v) = A.ρ (σ ^ (x + y)) v := by
    intro x y v
    rw [zpow_add, map_mul, Module.End.mul_apply]
  have hper : ∀ q : ℤ, A.ρ (σ ^ ((L : ℤ) * q)) a = a := by
    intro q
    have : σ ^ ((L : ℤ) * q) = (σ ^ L) ^ q := by
      rw [← zpow_natCast σ L, ← zpow_mul]
    rw [this]
    exact (mem_stabilizer _ _ _).1 (zpow_mem hmem _)
  obtain ⟨c, hc⟩ : ∃ c : ℤ → A, ∀ n, c n = ∑ i ∈ Finset.range ((n : ZMod L).val), A.ρ (σ ^ i) a :=
    ⟨_, fun _ => rfl⟩
  have hc0 : c 0 = 0 := by rw [hc]; simp
  have hrec : ∀ n : ℤ, c (n + 1) = c n + A.ρ (σ ^ n) a := by
    intro n
    obtain ⟨r, hr⟩ : ∃ r, r = (n : ZMod L).val := ⟨_, rfl⟩
    have hrL : r < L := hr ▸ ZMod.val_lt _
    have hrn : A.ρ (σ ^ n) a = A.ρ (σ ^ r) a := by
      have h1 : (r : ℤ) = n % L := by rw [hr, ZMod.val_intCast]
      have h2 : n = r + L * (n / L) := by rw [h1]; exact (Int.emod_add_mul_ediv n L).symm
      conv_lhs => rw [h2]
      rw [zpow_add, map_mul, Module.End.mul_apply, hper, zpow_natCast]
    have hval : ((n + 1 : ℤ) : ZMod L).val = (r + 1) % L := by
      rw [Int.cast_add, Int.cast_one, ZMod.val_add, ZMod.val_one_eq_one_mod, ← hr, Nat.add_mod_mod]
    rw [hc, hc, hval, hrn, ← hr]
    rcases Nat.lt_or_ge (r + 1) L with h | h
    · rw [Nat.mod_eq_of_lt h, Finset.sum_range_succ]
    · have h' : r + 1 = L := le_antisymm (by omega) h
      rw [h', Nat.mod_self, Finset.range_zero, Finset.sum_empty, ← Finset.sum_range_succ, h', hsum]
  have hcoc : ∀ x y : ℤ, c (x + y) = c x + A.ρ (σ ^ x) (c y) := by
    intro x y
    induction y using Int.induction_on with
    | zero => simp [hc0]
    | succ y ih =>
      rw [← add_assoc, hrec, ih, hrec, map_add, hρ, add_assoc]
    | pred y ih =>
      have e1 := hrec (x + (-(y : ℤ) - 1))
      have e2 := hrec (-(y : ℤ) - 1)
      rw [show x + (-(y : ℤ) - 1) + 1 = x + -(y : ℤ) by ring, ih] at e1
      rw [show -(y : ℤ) - 1 + 1 = -(y : ℤ) by ring] at e2
      rw [e2, map_add, hρ] at e1
      have e3 := e1.symm
      rw [← add_assoc] at e3
      exact add_right_cancel e3
  obtain ⟨F, hF⟩ : ∃ F : G → A, ∀ g, F g =
      ∑ i ∈ Finset.range (Multiplicative.toAdd (φ g)).val, A.ρ (σ ^ i) a := ⟨_, fun _ => rfl⟩
  have hFpow : ∀ n : ℤ, F (σ ^ n) = c n := by
    intro n
    rw [hF, hc, map_zpow, hφσ, toAdd_zpow, toAdd_ofAdd, zsmul_one]
  have hFlc : IsLocallyConstant F := by
    have h1 : IsLocallyConstant φ := φ.isLocallyConstant_of_isOpen_ker hφo
    have : F = (fun z : Multiplicative (ZMod L) =>
        ∑ i ∈ Finset.range (Multiplicative.toAdd z).val, A.ρ (σ ^ i) a) ∘ φ := funext hF
    rw [this]
    exact h1.comp _
  have hflc : IsLocallyConstant fun x : Fin 1 → G => F (x 0) :=
    hFlc.comp_continuous (continuous_apply 0)
  refine ⟨fun x => F (x 0), hflc, ?_, ?_⟩
  · refine hσ.eq_of_forall_zpow_pi (isLocallyConstant_d A hflc)
      (IsLocallyConstant.const 0) fun n => ?_
    show (inhomogeneousCochains.d A 1).hom (fun x => F (x 0)) (fun i => σ ^ n i) = 0
    rw [inhomogeneousD_one_apply]
    dsimp only
    rw [← zpow_add, hFpow, hFpow, hFpow, hcoc]
    abel
  · show F σ = a
    have h1 := hFpow 1
    rw [zpow_one] at h1
    rw [h1, ← zero_add (1 : ℤ), hrec, hc0, zpow_zero, map_one, Module.End.one_apply, zero_add]

end Cocycle

section Primary

theorem mul_pow_dvd_of_dvd_of_pow_add_dvd {ℓ N L e : ℕ} (hℓ : ℓ.Prime) (hN : 0 < N) (h1 : N ∣ L)
    (h2 : ℓ ^ (e + N) ∣ L) : N * ℓ ^ e ∣ L := by
  obtain ⟨v, r, hr, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' ℓ hℓ.ne_one
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hN
  have hcop : Nat.Coprime (ℓ ^ (e + v)) r :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hr)
  have hv : v ≤ ℓ ^ v * r := by
    have h3 : v < ℓ ^ v := v.lt_pow_self hℓ.one_lt
    have h4 : ℓ ^ v ≤ ℓ ^ v * r := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hr0)
    omega
  have h3 : ℓ ^ (e + v) ∣ L := (Nat.pow_dvd_pow ℓ (by omega)).trans h2
  have h4 : r ∣ L := (Dvd.intro_left _ rfl).trans h1
  have := hcop.mul_dvd_of_dvd_of_dvd h3 h4
  calc ℓ ^ v * r * ℓ ^ e = ℓ ^ (e + v) * r := by ring
    _ ∣ L := this

end Primary

section CocyclePrimary

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {ℓ : ℕ} {σ : G}

theorem IsPrimePowGenerator.exists_cocycle (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    {A : Rep.{u} k G} [IsDiscreteRep A] (a : A) {e : ℕ} (ha : ℓ ^ e • a = 0) :
    ∃ f : (Fin 1 → G) → A, IsLocallyConstant f ∧ (inhomogeneousCochains.d A 1).hom f = 0 ∧
      f (fun _ => σ) = a := by
  obtain ⟨U₀, hU₀⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_stabilizer A a) (stabilizer A.ρ a).one_mem
  have : Finite (G ⧸ (U₀ : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ U₀.isOpen'
  set N := orderOf (QuotientGroup.mk σ : G ⧸ (U₀ : Subgroup G)) with hNdef
  have hN : 0 < N := orderOf_pos _
  have hσN : σ ^ N ∈ stabilizer A.ρ a := hU₀ ((QuotientGroup.eq_one_iff _).1 (by
    rw [QuotientGroup.mk_pow, hNdef, pow_orderOf_eq_one]))
  obtain ⟨χ, hχo, hχσ⟩ := hσ.exists_hom (e + N)
  let U : Subgroup G := (U₀ : Subgroup G) ⊓ χ.ker
  have hUo : IsOpen (U : Set G) := U₀.isOpen'.inter hχo
  have : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hUo
  set L := orderOf (QuotientGroup.mk σ : G ⧸ U) with hLdef
  obtain ⟨φ, hφU, hφσ⟩ := hσ.dense.exists_hom_zmod_orderOf U hUo
  have hLU : σ ^ L ∈ U := (QuotientGroup.eq_one_iff _).1 (by
    rw [QuotientGroup.mk_pow, hLdef, pow_orderOf_eq_one])
  have hL : 0 < L := orderOf_pos _
  have h1 : N ∣ L := orderOf_dvd_of_pow_eq_one (by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hLU.1)
  have h2 : ℓ ^ (e + N) ∣ L := by
    have hk : χ (σ ^ L) = 1 := hLU.2
    rw [map_pow, hχσ, ← ofAdd_nsmul, nsmul_one, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff] at hk
    exact (ZMod.natCast_eq_zero_iff _ _).1 hk
  obtain ⟨c, hc⟩ := mul_pow_dvd_of_dvd_of_pow_add_dvd hℓ hN h1 h2
  have hsum : ∑ i ∈ Finset.range L, A.ρ (σ ^ i) a = 0 := by
    rw [hc, mul_assoc]
    exact sum_range_mul_eq_zero ((mem_stabilizer _ _ _).1 hσN) (by rw [mul_comm, mul_smul, ha, smul_zero])
  have : NeZero L := ⟨hL.ne'⟩
  exact hσ.dense.exists_cocycle_of_hom L φ (Subgroup.isOpen_mono hφU hUo) hφσ a (hU₀ hLU.1) hsum

theorem IsPrimePowGenerator.H1Eval_surjective (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) :
    Function.Surjective (H1Eval A σ).hom := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨e, he⟩ := hA a
  obtain ⟨f, hlc, hd, hfσ⟩ := hσ.exists_cocycle hℓ a he
  let x : locallyConstantCochains A 1 := ⟨f, hlc⟩
  have hx : ((cochainsComplex A).d 1 2).hom x = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, cochainsComplex_d]
    exact Subtype.ext hd
  refine ⟨(cohomologyπ A 1).hom ((cochainsComplex A).cyclesMk x 2 (by simp) hx), ?_⟩
  rw [H1Eval_cohomology_class_apply]
  have h : cocycleFun A ((cochainsComplex A).cyclesMk x 2 (by simp) hx) = f :=
    congrArg Subtype.val ((cochainsComplex A).i_cyclesMk x 2 (by simp) hx)
  rw [h, hfσ]

omit [TotallyDisconnectedSpace G] in

theorem primary_discreteCoind_of_primary (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) (f : discreteCoind k G A) : ∃ e : ℕ, ℓ ^ e • f = 0 := by
  let f' : LocallyConstant G A := f
  have : Finite (Set.range f') := f'.range_finite.to_subtype
  choose kk hkk using fun v : Set.range f' => hA v
  obtain ⟨K, hK⟩ := (Set.finite_range kk).bddAbove
  refine ⟨K, LocallyConstant.ext fun x => ?_⟩
  show ℓ ^ K • f' x = 0
  exact pow_nsmul_eq_zero_of_le (hK ⟨⟨f' x, x, rfl⟩, rfl⟩) (hkk ⟨f' x, x, rfl⟩)

omit [TotallyDisconnectedSpace G] in

theorem primary_coindCokernel_of_primary (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) (x : coindCokernel A) : ∃ e : ℕ, ℓ ^ e • x = 0 := by
  have hepi : Epi (coindCokernelπ A) := (coindShortComplex_shortExact A).epi_g
  obtain ⟨f, rfl⟩ := (Rep.epi_iff_surjective (coindCokernelπ A)).1 hepi x
  obtain ⟨e, he⟩ := primary_discreteCoind_of_primary A hA f
  exact ⟨e, by rw [← map_nsmul, he, map_zero]⟩

theorem IsPrimePowGenerator.mem_range_sub_one_discreteCoind (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) (c : LocallyConstant G A) :
    c ∈ LinearMap.range ((discreteCoind k G A).ρ σ - 1) := by
  have hz := isZero_cohomology_discreteCoind k G A 0
  have hs : Subsingleton (cohomology (discreteCoind k G A) 1) :=
    ModuleCat.subsingleton_of_isZero hz
  obtain ⟨x, hx⟩ := hσ.H1Eval_surjective hℓ (discreteCoind k G A)
    (primary_discreteCoind_of_primary A hA) (Submodule.Quotient.mk c)
  rw [Subsingleton.elim x 0, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at hx
  exact hx

theorem IsPrimePowGenerator.isZero_cohomology_two (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) :
    IsZero (cohomology A 2) := by
  refine IsZero.of_iso ?_ (cohomologyCoindCokernelIso A 0).symm
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  apply H1Eval_injective (coindCokernel A) hσ.dense
  refine Subsingleton.elim (h := ⟨fun q q' => ?_⟩) _ _
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨q', rfl⟩ := Submodule.Quotient.mk_surjective _ q'
  rw [Submodule.Quotient.eq]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (q - q')
  rw [← hc]
  obtain ⟨d, hd⟩ := hσ.mem_range_sub_one_discreteCoind hℓ A hA c
  refine ⟨(coindCokernelπ A).hom d, ?_⟩
  rw [LinearMap.sub_apply, Module.End.one_apply, ← Rep.hom_comm_apply, ← map_sub]
  rw [← hd]
  rfl

theorem IsPrimePowGenerator.isZero_cohomology_of_primary (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ e : ℕ, ℓ ^ e • a = 0) {n : ℕ} (hn : 2 ≤ n) :
    IsZero (cohomology A n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  induction m generalizing A with
  | zero => exact hσ.isZero_cohomology_two hℓ A hA
  | succ m ih =>
    exact (ih (coindCokernel A) (primary_coindCokernel_of_primary A hA)).of_iso
      (cohomologyCoindCokernelIso A (m + 1)).symm

theorem IsPrimePowGenerator.eq_zero_of_pow_nsmul (hℓ : ℓ.Prime) (hσ : IsPrimePowGenerator ℓ σ)
    (A : Rep.{u} k G) [IsDiscreteRep A] (hA : IsAddTorsion A) {p : ℕ} (hp : 2 ≤ p)
    (x : cohomology A p) {n : ℕ} (hx : ℓ ^ n • x = 0) : x = 0 := by
  set W := primarySubmodule A ℓ
  have hW := primarySubmodule_le_comap A ℓ
  have hS := subQuotShortComplex_shortExact A W hW

  have hbij : Function.Bijective (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃).hom := by
    have : ⇑(ℓ • 𝟙 (subQuotShortComplex A W hW).X₃).hom =
        fun y : A ⧸ W => ℓ • y := funext fun y => nsmul_id_hom_apply _ ℓ y
    rw [this]
    exact bijective_nsmul_quotient_primarySubmodule A hA hℓ
  have hiso : IsIso (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃) := by
    have he : (Rep.mkIso ((ℓ • 𝟙 (subQuotShortComplex A W hW).X₃).hom.ofBijective hbij)).hom =
        ℓ • 𝟙 (subQuotShortComplex A W hW).X₃ := Rep.hom_ext rfl
    rw [← he]
    infer_instance
  have hinj : Function.Injective (cohomologyMap (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃) p).hom := by
    have hH : IsIso (cohomologyMap (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃) p) :=
      ⟨cohomologyMap (inv (ℓ • 𝟙 (subQuotShortComplex A W hW).X₃)) p, by
        rw [← cohomologyMap_comp, IsIso.hom_inv_id, cohomologyMap_id], by
        rw [← cohomologyMap_comp, IsIso.inv_hom_id, cohomologyMap_id]⟩
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  let x' : cohomology (subQuotShortComplex A W hW).X₂ p := x
  have hx' : ℓ ^ n • x' = 0 := hx
  have hg : (cohomologyMap (subQuotShortComplex A W hW).g p).hom x' = 0 := by
    have hpow : ∀ j : ℕ, ∀ y : cohomology (subQuotShortComplex A W hW).X₃ p, ℓ ^ j • y = 0 → y = 0 := by
      intro j
      induction j with
      | zero => intro y hy; simpa using hy
      | succ j ih =>
        intro y hy
        apply ih
        apply hinj
        rw [map_zero, cohomologyMap_nsmul_id_apply, ← mul_smul, ← pow_succ']
        exact hy
    exact hpow n _ (by rw [← map_nsmul, hx', map_zero])
  obtain ⟨y, hy'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS p) x' hg
  have hy : IsZero (cohomology (subQuotShortComplex A W hW).X₁ p) :=
    hσ.isZero_cohomology_of_primary hℓ _ (fun (b : (subQuotShortComplex A W hW).X₁) => by
      obtain ⟨j, hj⟩ := b.2
      exact ⟨j, Subtype.ext hj⟩) hp
  have h0 : x' = 0 := by
    rw [← hy', (ModuleCat.subsingleton_of_isZero hy).elim y 0, map_zero]
  exact h0

end CocyclePrimary

end GroundTheory.ProfCoh
