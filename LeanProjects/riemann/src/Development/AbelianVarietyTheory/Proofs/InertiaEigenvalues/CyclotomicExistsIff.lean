import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.KernelCharacterDelta

noncomputable section
namespace GlobalTheory.PsiLemmaCompare
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.IndefiniteRowSideFullHecke

section Subst
variable {k : Type} [Field k]

theorem vv_eq : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by simp [vv]

theorem vv_ne : vv k ≠ 0 := by simp [vv]

theorem single_eq (m : ℤ) : (HahnSeries.single m 1 : k⸨X⸩) = vv k ^ m := by
  rw [vv, ← RatFunc.single_zpow]

theorem coe_ne {f : k⟦X⟧} (h : f ≠ 0) : (f : k⸨X⸩) ≠ 0 := fun e =>
  h (HahnSeries.ofPowerSeries_injective (e.trans (map_zero _).symm))

def substHom (f : k⟦X⟧) (h0 : PowerSeries.constantCoeff f = 0) (h1 : f ≠ 0) : k⸨X⸩ →+* k⸨X⸩ :=
  IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : k⟦X⟧))
    (g := (HahnSeries.ofPowerSeries ℤ k).comp
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom)
    (by
      rintro ⟨_, n, rfl⟩
      refine IsUnit.mk0 _ ?_
      simp only [map_pow]
      refine pow_ne_zero _ ?_
      simpa [PowerSeries.substAlgHom_X] using coe_ne h1)

theorem substHom_coe (f : k⟦X⟧) (h0 : PowerSeries.constantCoeff f = 0) (h1 : f ≠ 0) (a : k⟦X⟧) :
    substHom f h0 h1 (a : k⸨X⸩) = ((a.subst f : k⟦X⟧) : k⸨X⸩) := by
  have := IsLocalization.lift_eq (S := k⸨X⸩) (M := Submonoid.powers (PowerSeries.X : k⟦X⟧))
    (g := (HahnSeries.ofPowerSeries ℤ k).comp
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) : k⟦X⟧ →ₐ[k] k⟦X⟧).toRingHom)
    (by
      rintro ⟨_, n, rfl⟩
      refine IsUnit.mk0 _ ?_
      simp only [map_pow]
      refine pow_ne_zero _ ?_
      simpa [PowerSeries.substAlgHom_X] using coe_ne h1) a
  refine this.trans ?_
  simp [PowerSeries.coe_substAlgHom]

theorem substL_eq (f : k⟦X⟧) (h0 : PowerSeries.constantCoeff f = 0) (h1 : f ≠ 0) (x : k⸨X⸩) :
    FrobeniusBinomialReduction.substL f x = substHom f h0 h1 x := by
  conv_rhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart x]
  rw [map_mul, substHom_coe, single_eq, map_zpow₀, vv_eq, substHom_coe,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' h0), FrobeniusBinomialReduction.substL]

theorem hom_ext {F G : k⸨X⸩ →+* k⸨X⸩} (h : ∀ a : k⟦X⟧, F (a : k⸨X⸩) = G (a : k⸨X⸩)) : F = G :=
  IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : k⟦X⟧)) (RingHom.ext h)

theorem exists_mul_pow (x : k⸨X⸩) : ∃ (n : ℕ) (a : k⟦X⟧), x * vv k ^ n = (a : k⸨X⸩) := by
  obtain ⟨⟨a, _, n, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : k⟦X⟧)) x
  refine ⟨n, a, ?_⟩
  simpa [vv_eq] using h

end Subst

section Frob
variable (k : Type) [Field k] (l : ℕ) [hl : Fact l.Prime]

theorem phiPi_coeff_mul (x : k⸨X⸩) (q : ℤ) : (OnePlusPowerCharacters.phiPi k l x).coeff (l * q) = x.coeff q := by
  unfold OnePlusPowerCharacters.phiPi
  erw [HahnSeries.embDomainRingHom_apply]
  exact HahnSeries.embDomain_coeff (a := q)

theorem phiPi_coeff_not (x : k⸨X⸩) (n : ℤ) (h : ¬ (l : ℤ) ∣ n) : (OnePlusPowerCharacters.phiPi k l x).coeff n = 0 := by
  unfold OnePlusPowerCharacters.phiPi
  erw [HahnSeries.embDomainRingHom_apply]
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨q, rfl⟩
  exact h ⟨q, rfl⟩

theorem coeff_neg (a : k⟦X⟧) {n : ℤ} (h : n < 0) : (a : k⸨X⸩).coeff n = 0 := by
  rw [PowerSeries.coeff_coe, if_pos h]

theorem phiPi_eq (x : k⸨X⸩) : OnePlusPowerCharacters.phiPi k l x = FrobeniusBinomialReduction.frobπ k l x := by
  have hp := hl.out.ne_zero
  have h0 : PowerSeries.constantCoeff ((PowerSeries.X : k⟦X⟧) ^ l) = 0 := by simp [hp]
  have h1 : ((PowerSeries.X : k⟦X⟧) ^ l) ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  rw [FrobeniusBinomialReduction.frobπ, substL_eq _ h0 h1]
  congr 1
  refine hom_ext fun a => ?_
  rw [substHom_coe]
  ext n
  have hpos : (0 : ℤ) < l := by exact_mod_cast hl.out.pos
  by_cases hd : (l : ℤ) ∣ n
  · obtain ⟨q, rfl⟩ := hd
    rw [phiPi_coeff_mul]
    rcases lt_or_ge q 0 with hq | hq
    · rw [coeff_neg k a hq, coeff_neg k _ (mul_neg_of_pos_of_neg hpos hq)]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      rw [← Nat.cast_mul, LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries,
        PowerSeries.coeff_subst_X_pow hp, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl.out.pos]
      simp
  · rw [phiPi_coeff_not k l _ _ hd]
    rcases lt_or_ge n 0 with hq | hq
    · rw [coeff_neg k _ hq]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      rw [LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_subst_X_pow hp, if_neg]
      exact fun h => hd (Int.natCast_dvd_natCast.2 h)

def assembleX (y : Fin l → k⸨X⸩) : k⸨X⸩ := ∑ j : Fin l, vv k ^ (j : ℕ) * OnePlusPowerCharacters.phiPi k l (y j)

theorem assembleX_coeff (y : Fin l → k⸨X⸩) (q : ℤ) (j : Fin l) :
    (assembleX k l y).coeff (l * q + (j : ℕ)) = (y j).coeff q := by
  have hv : ∀ (i : ℕ) (z : k⸨X⸩) (n : ℤ), (vv k ^ i * z).coeff n = z.coeff (n - i) := by
    intro i z n
    rw [← zpow_natCast, ← single_eq]
    conv_lhs => rw [← sub_add_cancel n i]
    rw [HahnSeries.coeff_single_mul_add, one_mul]
  rw [assembleX, HahnSeries.coeff_sum, Finset.sum_eq_single j]
  · rw [hv, add_sub_cancel_right, phiPi_coeff_mul]
  · intro i _ hij
    rw [hv, phiPi_coeff_not]
    intro hd
    rw [add_sub_assoc] at hd
    have h2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - (i : ℕ) := (dvd_add_right (dvd_mul_right _ _)).1 hd
    have h3 := Int.eq_zero_of_abs_lt_dvd h2 (by
      have := i.2; have := j.2
      rw [abs_lt]; constructor <;> omega)
    exact hij (Fin.ext (by omega))
  · simp

theorem assembleX_bijective : Function.Bijective (assembleX k l) := by
  have hpos : (0 : ℤ) < l := by exact_mod_cast hl.out.pos
  constructor
  · intro y z h
    funext j
    ext q
    rw [← assembleX_coeff, h, assembleX_coeff]
  · intro x
    have hb : ∀ j : Fin l, BddBelow (Function.support fun q : ℤ => x.coeff (l * q + (j : ℕ))) := by
      intro j
      refine ⟨-|x.order| - 1, fun q hq => ?_⟩
      have h1 : x.order ≤ l * q + (j : ℕ) := HahnSeries.order_le_of_coeff_ne_zero hq
      have h2 : ((j : ℕ) : ℤ) < l := by exact_mod_cast j.2
      by_contra hc
      push Not at hc
      have h3 := neg_abs_le x.order
      have h4 := abs_nonneg x.order
      nlinarith
    refine ⟨fun j => HahnSeries.ofSuppBddBelow _ (hb j), ?_⟩
    ext n
    have hn : n = l * (n / l) + ((⟨(n % l).toNat, by
        have := Int.emod_lt_of_pos n hpos; have := Int.emod_nonneg n hpos.ne'; omega⟩ : Fin l) : ℕ) := by
      have := Int.emod_nonneg n hpos.ne'
      simp only [Int.toNat_of_nonneg this]
      exact (Int.mul_ediv_add_emod n l).symm
    rw [hn, assembleX_coeff]
    simp

theorem assemble_bijective : Function.Bijective (OnePlusPowerCharacters.assemble k l) := by
  let T : Matrix (Fin l) (Fin l) k⸨X⸩ := Matrix.of fun m j => (((j : ℕ).choose m : ℕ) : k⸨X⸩)
  have hdet : T.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · simp [T]
    · intro i j h
      simp only [T, Matrix.of_apply]
      rw [Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from h), Nat.cast_zero]
  have hT : Function.Bijective T.mulVec :=
    ⟨Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det T).2 (hdet ▸ isUnit_one)),
     Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det T).2 (hdet ▸ isUnit_one))⟩
  have e : OnePlusPowerCharacters.assemble k l = assembleX k l ∘ T.mulVec := by
    funext y
    simp only [Function.comp, OnePlusPowerCharacters.assemble, assembleX, Matrix.mulVec, dotProduct, map_sum, map_mul, T,
      Matrix.of_apply, map_natCast, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, add_comm, add_pow]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun m => vv k ^ m * (((j : ℕ).choose m : ℕ) : k⸨X⸩))]
    simp only [one_pow, mul_one]
    refine Finset.sum_subset (Finset.range_subset_range.2 j.2) fun m _ hm => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hm), Nat.cast_zero, mul_zero]
  rw [e]
  exact (assembleX_bijective k l).comp hT

end Frob

section Ring
variable {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] [CharP k l]

theorem binom_const (t : ℤ_[l]) : PowerSeries.constantCoeff (FrobeniusBinomialReduction.binomPow k l t - 1) = 0 := by
  rw [map_sub, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, FrobeniusBinomialReduction.binomPow, PowerSeries.coeff_map,
    PowerSeries.binomialSeries_coeff]
  simp

theorem binom_ne (t : ℤ_[l]) (h : FrobeniusBinomialReduction.red k l t ≠ 0) : FrobeniusBinomialReduction.binomPow k l t - 1 ≠ 0 := by
  intro e
  have := congrArg (PowerSeries.coeff 1) e
  rw [map_sub, FrobeniusBinomialReduction.binomPow, PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff] at this
  exact h (by simpa [PowerSeries.coeff_one] using this)

theorem binom_unit_ne (t : ℤ_[l]ˣ) : FrobeniusBinomialReduction.binomPow k l t - 1 ≠ 0 :=
  binom_ne _ (t.isUnit.map (FrobeniusBinomialReduction.red k l)).ne_zero

theorem gam_const : PowerSeries.constantCoeff ((1 + PowerSeries.X : k⟦X⟧) ^ (1 + l) - 1) = 0 := by simp

theorem gam_ne : (1 + PowerSeries.X : k⟦X⟧) ^ (1 + l) - 1 ≠ 0 := by
  rw [← FrobeniusBinomialReduction.binomPow_natCast k l]
  refine binom_ne _ ?_
  rw [map_natCast]
  simp

theorem gam_coe (b : k⟦X⟧) : FrobeniusBinomialReduction.gamπ k l (b : k⸨X⸩) = ((OnePlusPowerCharacters.gammaPi k l b : k⟦X⟧) : k⸨X⸩) := by
  rw [FrobeniusBinomialReduction.gamπ, substL_eq _ gam_const gam_ne, substHom_coe, OnePlusPowerCharacters.gammaPi]

theorem act_coe (t : ℤ_[l]ˣ) (b : k⟦X⟧) :
    FrobeniusBinomialReduction.actπ k l t (b : k⸨X⸩) = ((OnePlusPowerCharacters.deltaPi k l t b : k⟦X⟧) : k⸨X⸩) := by
  rw [FrobeniusBinomialReduction.actπ, substL_eq _ (binom_const _) (binom_unit_ne t), substHom_coe]
  rfl

theorem deltaInv_coe (b : k⟦X⟧) : FrobeniusBinomialReduction.DeltaInv k l (b : k⸨X⸩) ↔
    ∀ z : ℤ_[l], z ^ (l - 1) = 1 → OnePlusPowerCharacters.deltaPi k l z b = b := by
  have h1 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
  constructor
  · intro h z hz
    obtain ⟨t, rfl⟩ := IsUnit.of_pow_eq_one hz h1
    have := h t (Units.ext (by simpa using hz))
    rw [act_coe] at this
    exact HahnSeries.ofPowerSeries_injective this
  · intro h t ht
    rw [act_coe, h t (by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one])]

theorem deltaInv_mul {x y : k⸨X⸩} (hx : FrobeniusBinomialReduction.DeltaInv k l x) (hy : FrobeniusBinomialReduction.DeltaInv k l y) :
    FrobeniusBinomialReduction.DeltaInv k l (x * y) := by
  intro t ht
  have h1 := hx t ht
  have h2 := hy t ht
  rw [FrobeniusBinomialReduction.actπ, substL_eq _ (binom_const _) (binom_unit_ne t)] at h1 h2 ⊢
  rw [map_mul, h1, h2]

theorem deltaInv_zpow {x : k⸨X⸩} (hx : FrobeniusBinomialReduction.DeltaInv k l x) (m : ℤ) :
    FrobeniusBinomialReduction.DeltaInv k l (x ^ m) := by
  intro t ht
  have h1 := hx t ht
  rw [FrobeniusBinomialReduction.actπ, substL_eq _ (binom_const _) (binom_unit_ne t)] at h1 ⊢
  rw [map_zpow₀, h1]

theorem isCyclotomic_iff (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) :
    OnePlusPowerCharacters.IsCyclotomic R ι ↔ FrobeniusBinomialReduction.IsCyclotomic R ι := by
  constructor
  · rintro ⟨⟨u, hu⟩, hint, hinv, hφ, hγ⟩
    have hA : ∀ a : k⟦X⟧, FrobeniusBinomialReduction.DeltaInv k l (ι (a : k⸨X⸩)) := by
      intro a
      obtain ⟨b, hb⟩ := hint a
      rw [hb, deltaInv_coe, hinv]
      exact ⟨a, hb⟩
    have hv : FrobeniusBinomialReduction.DeltaInv k l (ι (vv k)) := by rw [vv_eq]; exact hA _
    refine ⟨?_, ?_, ⟨u, hu⟩, fun x => by rw [hφ, phiPi_eq], ?_⟩
    · ext y
      constructor
      · rintro ⟨x, rfl⟩
        rw [← LaurentSeries.single_order_mul_powerSeriesPart x, single_eq, map_mul, map_zpow₀]
        exact deltaInv_mul (deltaInv_zpow hv _) (hA _)
      · intro hy
        obtain ⟨n, c, hc⟩ := exists_mul_pow y
        obtain ⟨e, he⟩ : ∃ e, l - 1 = e + 1 := ⟨l - 2, by have := hl.out.two_le; omega⟩
        have hb : y * ι (vv k) ^ n = ((c * ((u : k⟦X⟧) * PowerSeries.X ^ e) ^ n : k⟦X⟧) : k⸨X⸩) := by
          rw [hu, he, map_mul, map_pow, map_mul, map_pow, ← hc, ← vv_eq]
          ring
        have h2 : FrobeniusBinomialReduction.DeltaInv k l (y * ι (vv k) ^ n) :=
          deltaInv_mul hy (by simpa using deltaInv_zpow hv n)
        rw [hb, deltaInv_coe, hinv] at h2
        obtain ⟨a, ha⟩ := h2
        have hne : ι (vv k) ≠ 0 := (map_ne_zero ι).2 vv_ne
        refine ⟨(a : k⸨X⸩) / vv k ^ n, ?_⟩
        rw [map_div₀, map_pow, ha, ← hb, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)]
    · ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨hint a, hA a⟩
      · rintro ⟨⟨b, rfl⟩, hb⟩
        rw [deltaInv_coe, hinv] at hb
        exact hb
    · have : (ι : k⸨X⸩ →+* k⸨X⸩).comp (R.γ : k⸨X⸩ →+* k⸨X⸩) =
          (substHom _ (gam_const (k := k) (l := l)) gam_ne).comp (ι : k⸨X⸩ →+* k⸨X⸩) := by
        refine hom_ext fun a => ?_
        obtain ⟨b, hb⟩ := hint a
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [hγ a b hb, hb, substHom_coe, OnePlusPowerCharacters.gammaPi]
      intro x
      rw [FrobeniusBinomialReduction.gamπ, substL_eq _ gam_const gam_ne]
      simpa only [RingHom.comp_apply, RingHom.coe_coe] using RingHom.congr_fun this x
  · rintro ⟨-, hA, hu, hφ, hγ⟩
    refine ⟨hu, fun a => ?_, fun b => ?_, fun x => by rw [hφ, phiPi_eq], fun a b hab => ?_⟩
    · have : ι (a : k⸨X⸩) ∈ Set.range (fun a : k⟦X⟧ => ι (a : k⸨X⸩)) := ⟨a, rfl⟩
      rw [hA] at this
      exact this.1
    · rw [← deltaInv_coe]
      change _ ↔ (b : k⸨X⸩) ∈ Set.range (fun a : k⟦X⟧ => ι (a : k⸨X⸩))
      rw [hA]
      exact ⟨fun h => ⟨⟨b, rfl⟩, h⟩, fun h => h.2⟩
    · rw [hγ, hab, gam_coe]

omit hl [CharP k l] in

theorem psiRing_iff (R : RingPG k l) (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) :
    OnePlusPowerCharacters.PsiRing R ψ ↔ FrobeniusBinomialReduction.PsiRing R ψ := by
  have e : {x : k⸨X⸩ | ∃ b : k⟦X⟧, x = (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)) := by
    ext x
    simp [eq_comm]
  unfold OnePlusPowerCharacters.PsiRing FrobeniusBinomialReduction.PsiRing
  rw [e]
  refine and_congr_right fun h => and_congr_left fun _ => ⟨fun h1 => by simpa using h1 1, fun h1 a => ?_⟩
  have := h a 1
  rwa [mul_one, h1, mul_one] at this

end Ring

section Mod
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem coe_smul (b : k⟦X⟧) (x : V) : (b : k⸨X⸩) • x = b • x := algebraMap_smul k⸨X⸩ b x

theorem image_sh_pull (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) (f Ψ : V →ₗ[k] V) (a : ℤ)
    (h3 : ψ '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)))
    (h1 : ∀ (a : k⸨X⸩) (x : V), Ψ (a • f x) = ψ a • x) (M₀ : Submodule k⟦X⟧ V) :
    Ψ '' (sh a (pull f M₀) : Set V) = (M₀ : Set V) := by
  ext m
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have key : ∀ b : k⟦X⟧, Ψ (vv k ^ a • b • y) ∈ M₀ := by
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, hm, rfl⟩ := hx
        intro b
        have : ψ (vv k ^ a * (b : k⸨X⸩)) ∈ Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)) :=
          h3 ▸ ⟨_, ⟨b, rfl⟩, rfl⟩
        obtain ⟨c, hc⟩ := this
        rw [← coe_smul, ← mul_smul, h1, ← hc, coe_smul]
        exact M₀.smul_mem c hm
      | zero => intro b; simp
      | add x y _ _ hx hy => intro b; rw [smul_add, smul_add, map_add]; exact M₀.add_mem (hx b) (hy b)
      | smul c x _ hx => intro b; rw [← mul_smul b]; exact hx _
    simpa using key 1
  · intro hm
    have : (1 : k⸨X⸩) ∈ Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)) := ⟨1, map_one _⟩
    rw [← h3] at this
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := this
    refine ⟨_, ⟨b • f m, Submodule.smul_mem _ b (Submodule.subset_span ⟨m, hm, rfl⟩), rfl⟩, ?_⟩
    change Ψ (vv k ^ a • b • f m) = m
    rw [← coe_smul, ← mul_smul, h1, hb, one_smul]

theorem psiMod_iff {l : ℕ} (R : RingPG k l) (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) (hψ : FrobeniusBinomialReduction.PsiRing R ψ)
    (f g₀ g Ψ : V →ₗ[k] V) :
    OnePlusPowerCharacters.PsiMod l ψ f g₀ g Ψ ↔
      (∀ a x, Ψ (a • f x) = ψ a • x) ∧ (∀ x, Ψ (g x) = g₀ (Ψ x)) ∧
        ∀ M₀ : Submodule k⟦X⟧ V, IsLat M₀ → CondC g₀ M₀ → FrobeniusBinomialReduction.PsiShift l g Ψ (pull f M₀) :=
  ⟨fun h => ⟨h.1, h.2.1, fun M₀ hM hc => (h.2.2 M₀ hM).2 hc⟩,
   fun h => ⟨h.1, h.2.1, fun M₀ hM =>
    ⟨fun a h1 h2 => image_sh_pull ψ f Ψ a (hψ.2.2.2 a h1 h2) h.1 M₀, h.2.2 M₀ hM⟩⟩⟩

end Mod

def LemmaPsiEtale : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l], 5 ≤ l →
  ∀ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), OnePlusPowerCharacters.IsCyclotomic R ι →
    Function.Bijective (OnePlusPowerCharacters.assemble k l) ∧
    ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, OnePlusPowerCharacters.IsPsi l ι ψ ∧ OnePlusPowerCharacters.PsiRing R ψ ∧
      ∀ (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
        [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
        [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V) (i : ZMod n),
        ∃ Ψ : V →ₗ[k] V, OnePlusPowerCharacters.PsiMod l ψ (D.φ i) (D.γ (i - 1)) (D.γ i) Ψ

end GlobalTheory.PsiLemmaCompare
