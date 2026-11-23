import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoTpow

open HomogeneousLocalization

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

theorem evV_awayMap (i : X ⟶ PSpace K N) {f g x : MvPolynomial (Fin (N + 1)) K} {n : ℕ}
    (hg : g ∈ grK K N n) (hx : x = f * g) (V : X.Opens)
    (hf : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) f) (hxV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x)
    (a : Away (grK K N) f) :
    evV i x V hxV (awayMap (grK K N) hg hx a) = evV i f V hf a := by
  have h := congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (grK K N) hg hx)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  change (i.appLE _ V hxV).hom ((Proj.awayToSection (grK K N) x).hom (awayMap (grK K N) hg hx a)) = _
  rw [h]
  change ((_ ≫ i.appLE _ V hxV).hom) _ = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem prod_pow_mem {n e p : ℕ} (y : Fin n → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (α : Fin n → ℕ) (hp : (∑ j, α j) * e = p) :
    ∏ j, y j ^ α j ∈ grK K N p := by
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ (fun j => y j ^ α j) (fun j => e * α j)
    (fun j _ => (hy j).pow (α j))
  rw [MvPolynomial.mem_homogeneousSubmodule, ← hp, mul_comm, Finset.mul_sum]
  exact h

theorem prod_mk_pow {n e c : ℕ} {g : MvPolynomial (Fin (N + 1)) K} (hg : g ∈ grK K N e)
    (y : Fin n → MvPolynomial (Fin (N + 1)) K) (h1 : ∀ j, y j ∈ grK K N (1 • e)) (α : Fin n → ℕ)
    (hc : ∑ j, α j = c) (hm : ∏ j, y j ^ α j ∈ grK K N (c • e)) :
    ∏ j, Away.mk (grK K N) hg 1 (y j) (h1 j) ^ α j = Away.mk (grK K N) hg c (∏ j, y j ^ α j) hm := by
  have hpow : ∀ k : ℕ, g ^ k ∈ Submonoid.powers g := fun k => ⟨k, rfl⟩
  let v : Localization (Submonoid.powers g) := Localization.mk 1 ⟨g, 1, pow_one g⟩
  have hv : ∀ k : ℕ, v ^ k = Localization.mk 1 ⟨g ^ k, hpow k⟩ := by
    intro k
    induction k with
    | zero => simpa using Localization.mk_one.symm
    | succ k ih =>
      rw [pow_succ, ih, Localization.mk_mul]
      simp [pow_succ]
  have key : ∀ (k : ℕ) (x) (hx : x ∈ grK K N (k • e)),
      (Away.mk (grK K N) hg k x hx).val = algebraMap _ _ x * v ^ k := by
    intro k x hx
    rw [Away.val_mk, hv, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    simp
  apply HomogeneousLocalization.val_injective
  rw [← HomogeneousLocalization.algebraMap_apply, map_prod]
  simp_rw [map_pow, HomogeneousLocalization.algebraMap_apply, key, pow_one, mul_pow,
    Finset.prod_mul_distrib, map_prod, map_pow, Finset.prod_pow_eq_pow_sum, hc]

theorem exists_shift {n : ℕ} (S : Finset (Fin n)) (v : Fin n → ℤ) (h : ∀ j, j ∉ S → 0 ≤ v j) :
    ∃ (r : ℕ) (α : Fin n → ℕ), ∀ j, (α j : ℤ) = v j + if j ∈ S then (r : ℤ) else 0 := by
  refine ⟨∑ j, (v j).natAbs, fun j => (v j + if j ∈ S then ((∑ j, (v j).natAbs : ℕ) : ℤ) else 0).toNat, fun j => ?_⟩
  refine Int.toNat_of_nonneg ?_
  by_cases hj : j ∈ S
  · have h1 : (v j).natAbs ≤ ∑ j, (v j).natAbs :=
      Finset.single_le_sum (f := fun j => (v j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [hj, if_true]
    omega
  · simpa [hj] using h j hj

theorem cross_mul {c r e₁ e₂ : ℕ} {f g a : MvPolynomial (Fin (N + 1)) K}
    (hf : f ∈ grK K N e₁) (hg : g ∈ grK K N e₂) (ha : a ∈ grK K N (r • e₁)) (ha' : a ∈ grK K N (c • e₂))
    (hF : f ^ r ∈ grK K N (c • e₂)) :
    awayMap (grK K N) hg (mul_comm g f) (Away.mk (grK K N) hf r a ha) *
      awayMap (grK K N) hf (rfl : g * f = g * f) (Away.mk (grK K N) hg c (f ^ r) hF) =
    awayMap (grK K N) hf (rfl : g * f = g * f) (Away.mk (grK K N) hg c a ha') := by
  simp only [awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  simp only [Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
  ring

theorem core {d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (V : X.Opens) (h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0))
    (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
    (hy0 : y 0 ∈ grK K N e) (h1 : ∀ j, y j ∈ grK K N (1 • e)) (r : ℕ) (α : Fin (d + 1) → ℕ)
    (hα : ∑ j, α j = r * S.card)
    (ha : ∏ j, y j ^ α j ∈ grK K N (r • (S.card * e))) :
    evV i (yS y S) V hS (Away.mk (grK K N) (yS_mem y hy S) r _ ha) *
        ∏ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) ^ (if j ∈ S then r else 0) =
      ∏ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) ^ α j := by
  have hP : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0 * yS y S) := by
    rw [Proj.basicOpen_mul]
    exact le_inf h0 hS
  have hβ : ∑ j, (if j ∈ S then r else 0) = r * S.card := by
    simp [Finset.sum_ite_mem, mul_comm]
  have ha' : ∏ j, y j ^ α j ∈ grK K N ((r * S.card) • e) :=
    prod_pow_mem y hy α (by rw [hα, smul_eq_mul])
  have hF' : ∏ j, y j ^ (if j ∈ S then r else 0) ∈ grK K N ((r * S.card) • e) :=
    prod_pow_mem y hy _ (by rw [hβ, smul_eq_mul])
  have hFeq : ∏ j, y j ^ (if j ∈ S then r else 0) = yS y S ^ r := by
    simp [yS, pow_ite, Finset.prod_ite_mem, Finset.prod_pow]
  have hF : yS y S ^ r ∈ grK K N ((r * S.card) • e) := hFeq ▸ hF'
  simp_rw [← map_pow, ← map_prod]
  rw [prod_mk_pow hy0 y h1 α hα ha', prod_mk_pow hy0 y h1 _ hβ hF']
  simp only [hFeq]
  rw [← evV_awayMap i hy0 (mul_comm (y 0) (yS y S)) V hS hP,
    ← evV_awayMap i (yS_mem y hy S) rfl V h0 hP, ← evV_awayMap i (yS_mem y hy S) rfl V h0 hP, ← map_mul,
    cross_mul (yS_mem y hy S) hy0 ha ha' hF]

theorem tpow_mem_range {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) : 0 < e →
    ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
      (ht : ∀ k, IsUnit (tV i y hy V hV k)), ∀ m ∈ expS S,
      tpow (fun k => (ht k).unit) m ∈ Set.range (evV i (yS y S) V hS) := by
  intro _ S hS ht m hm
  have h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0) :=
    hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0)
  have hy0 : y 0 ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y 0)).2 (hy 0)
  have h1 : ∀ j, y j ∈ grK K N (1 • e) := fun j => by
    simpa using (MvPolynomial.mem_homogeneousSubmodule e (y j)).2 (hy j)
  let n : Fin (d + 1) → ℤ := Fin.cons (-∑ k, m k) m
  have hn0 : n 0 = -∑ k, m k := rfl
  have hns : ∀ k : Fin d, n k.succ = m k := fun _ => rfl
  have hn : ∀ j, j ∉ S → 0 ≤ n j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · intro hj
      have := hm.2 hj
      rw [hn0]
      omega
    · intro hj
      rw [hns]
      exact hm.1 k hj
  obtain ⟨r, α, hα⟩ := exists_shift S n hn
  have hsum : ∑ j, n j = 0 := by
    rw [Fin.sum_univ_succ, hn0]
    simp only [hns]
    ring
  have hαs : ∑ j, α j = r * S.card := by
    have : ((∑ j, α j : ℕ) : ℤ) = ((r * S.card : ℕ) : ℤ) := by
      push_cast
      simp_rw [hα]
      rw [Finset.sum_add_distrib, hsum]
      simp [Finset.sum_ite_mem, mul_comm]
    exact_mod_cast this
  have ha : ∏ j, y j ^ α j ∈ grK K N (r • (S.card * e)) :=
    prod_pow_mem y hy α (by rw [hαs, smul_eq_mul, mul_assoc])
  refine ⟨Away.mk (grK K N) (yS_mem y hy S) r _ ha, ?_⟩
  have hc := core i y hy V h0 S hS hy0 h1 r α hαs ha
  let T : Fin (d + 1) → (Γ(X, V))ˣ := Fin.cons 1 (fun k => (ht k).unit)
  have hT0 : T 0 = 1 := rfl
  have hTs : ∀ k : Fin d, T k.succ = (ht k).unit := fun _ => rfl
  have hT : ∀ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) = (T j : Γ(X, V)) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · have : Away.mk (grK K N) hy0 1 (y 0) (h1 0) = 1 := by
        apply HomogeneousLocalization.val_injective
        rw [Away.val_mk, HomogeneousLocalization.val_one]
        simpa using Localization.mk_self (⟨y 0, 1, pow_one _⟩ : Submonoid.powers (y 0))
      rw [this, map_one, hT0, Units.val_one]
    · rw [hTs, IsUnit.unit_spec]
      rfl
  simp only [hT] at hc
  have hU : ∏ k, (ht k).unit ^ m k = ∏ j, T j ^ n j := by
    rw [Fin.prod_univ_succ, hT0, one_zpow, one_mul]
    simp only [hTs, hns]
  have hA : ∏ j, T j ^ α j = (∏ j, T j ^ n j) * ∏ j, T j ^ (if j ∈ S then r else 0) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add, hα]
    split_ifs <;> simp
  have hc' : evV i (yS y S) V hS (Away.mk (grK K N) (yS_mem y hy S) r _ ha) *
      ((∏ j, T j ^ (if j ∈ S then r else 0) : (Γ(X, V))ˣ) : Γ(X, V)) =
      ((∏ j, T j ^ n j : (Γ(X, V))ˣ) : Γ(X, V)) * ((∏ j, T j ^ (if j ∈ S then r else 0) : (Γ(X, V))ˣ) : Γ(X, V)) := by
    rw [← Units.val_mul, ← hA]
    simpa [Units.coe_prod] using hc
  have := (Units.mul_left_inj _).1 hc'
  rw [this, tpow, hU]

end GlobalTheory.CompanionTheory.GeoTpow
