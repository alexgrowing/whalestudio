import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier

namespace GlobalTheory.DenomIdeal

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (w : ι → X.functionField)

def IsDen (V : X.Opens) (a : Γ(X, V)) : Prop :=
  ∀ h : genericPoint X ∈ V, ∀ j, ∀ y ∈ V, RegAt y (fnOf V h a * w j)

def gens (V : X.Opens) : Set Γ(X, V) :=
  {b | ∃ a, IsDen w V a ∧ ∃ j, ∀ h : genericPoint X ∈ V, fnOf V h b = fnOf V h a * w j}

def idealOn (V : X.Opens) : Ideal Γ(X, V) := Ideal.span (gens w V)

variable {w}

theorem IsDen.res {U V : X.Opens} (e : V ≤ U) {a : Γ(X, U)} (ha : IsDen w U a) :
    IsDen w V (resG X e a) := by
  intro h j y hy
  rw [fnOf_resG]
  exact ha (e h) j y (e hy)

theorem res_mem_gens {U V : X.Opens} (e : V ≤ U) {b : Γ(X, U)} (hb : b ∈ gens w U) :
    resG X e b ∈ gens w V := by
  obtain ⟨a, ha, j, hj⟩ := hb
  exact ⟨resG X e a, ha.res e, j, fun h => by rw [fnOf_resG, fnOf_resG, hj]⟩

theorem mem_map_of_mem_gens_basicOpen [Fintype ι] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    {b : Γ(X, X.basicOpen f)} (hb : b ∈ gens w (X.basicOpen f)) :
    b ∈ (idealOn w U).map (resG X (X.basicOpen_le f)) := by
  by_cases hg : genericPoint X ∈ X.basicOpen f
  swap
  · have : b = 0 := Cartier.fn_ext fun h => (hg h).elim
    rw [this]; exact zero_mem _
  have hU' : genericPoint X ∈ U := X.basicOpen_le f hg
  have := hU.isLocalization_basicOpen f
  obtain ⟨a', ha', j, hj⟩ := hb
  obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) a'
  have e' : fnOf _ hg a' * fnOf U hU' f ^ n = fnOf U hU' a := by
    have := congrArg (fnOf _ hg) e
    simp only [map_mul, map_pow] at this
    change fnOf _ hg a' * fnOf _ hg (resG X (X.basicOpen_le f) f) ^ n =
      fnOf _ hg (resG X (X.basicOpen_le f) a) at this
    rwa [fnOf_resG, fnOf_resG] at this
  have hreg : ∀ i, ∀ x ∈ X.basicOpen f, RegAt x (fnOf U hU' a * w i) := fun i x hx => by
    rw [← e', mul_right_comm]
    exact (ha' hg i x hx).mul (GlobalTheory.TrueGeo.SmallSec.regAt_pow (regAt_fnOf (X.basicOpen_le f hx) hU' f) n)
  have := fun i => GlobalTheory.InvertIdeal.exists_mul_pow hU hU' f hg (hreg i)
  choose m γ hγ using this
  set M := ∑ i, m i
  have hm : ∀ i, m i ≤ M := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have key : ∀ i, fnOf U hU' (γ i * f ^ (M - m i)) = fnOf U hU' (a * f ^ M) * w i := fun i => by
    rw [map_mul, map_mul, hγ, map_pow, map_pow, ← Nat.add_sub_cancel' (hm i), pow_add]
    simp only [Nat.add_sub_cancel_left]
    ring
  have hden : IsDen w U (a * f ^ M) := fun h i y hy => by
    rw [← key i]; exact regAt_fnOf hy _ _
  have hgen : γ j * f ^ (M - m j) ∈ gens w U := ⟨_, hden, j, fun h => key j⟩
  have hu : IsUnit (resG X (X.basicOpen_le f) f) := IsLocalization.Away.algebraMap_isUnit f
  have hb0 : resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) = b * resG X (X.basicOpen_le f) f ^ (n + M) :=
    Cartier.fn_ext fun h => by
      rw [fnOf_resG, key, map_mul (fnOf _ h), map_pow, fnOf_resG, hj, map_mul, map_pow, ← e']
      ring
  have hb : b = resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) * ((hu.unit⁻¹ : _) : Γ(X, X.basicOpen f)) ^ (n + M) := by
    rw [hb0, mul_assoc, ← mul_pow, hu.mul_val_inv, one_pow, mul_one]
  rw [hb]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hgen))

variable (w) in

def idealSheaf [Fintype ι] : X.IdealSheafData where
  ideal U := idealOn w U.1
  map_ideal_basicOpen U f := by
    show Ideal.map (resG X (X.basicOpen_le f)) (idealOn w U.1) = idealOn w (X.basicOpen f)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 fun b hb => ?_
      exact Ideal.subset_span (res_mem_gens (X.basicOpen_le f) hb)
    · exact Ideal.span_le.2 fun b hb => mem_map_of_mem_gens_basicOpen U.2 f hb

theorem idealSheaf_ideal [Fintype ι] (U : X.affineOpens) : (idealSheaf w).ideal U = idealOn w U.1 := rfl

theorem idealSheaf_ne_bot [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) : idealSheaf w ≠ ⊥ := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hηW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hW' : IsAffineOpen W := hW
  choose β γ hβ hγ using fun j => GlobalTheory.InvertIdeal.exists_denom hW' hηW hηW (regAt_genericPoint (w j))
  have hβ0 : ∀ j, fnOf W hηW (β j) ≠ 0 := fun j => ((unitAt_fnOf_iff hηW hηW (β j)).2 (hβ j)).ne_zero
  set d := ∏ j, β j
  have hd : ∀ j, fnOf W hηW d * w j = fnOf W hηW (γ j) * fnOf W hηW (∏ i ∈ Finset.univ.erase j, β i) := fun j => by
    rw [hγ, show d = β j * ∏ i ∈ Finset.univ.erase j, β i from (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm,
      map_mul]
    ring
  have hden : IsDen w W d := fun h j y hy => by
    rw [hd j]; exact (regAt_fnOf hy _ _).mul (regAt_fnOf hy _ _)
  have hgen : d ∈ gens w W := ⟨d, hden, i₀, fun h => by rw [h1, mul_one]⟩
  have hd0 : fnOf W hηW d ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => hβ0 j
  intro hbot
  have hmem : d ∈ (idealSheaf w).ideal ⟨W, hW⟩ := Ideal.subset_span hgen
  rw [hbot] at hmem
  exact hd0 (by rw [(Ideal.mem_bot).1 hmem, map_zero])

theorem notMem_support [Finite ι] [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) {y : X} {k : ι} (hk : w k ≠ 0)
    (hy : ∀ j, RegAt y (w j / w k)) : y ∉ (idealSheaf w).support := by
  obtain ⟨V, hyV, ha⟩ := GlobalTheory.InvertIdeal.exists_common_open hy
  choose a ha using ha
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
  have e : W ≤ V := hWV
  have hηW : genericPoint X ∈ W := gen_mem hyW
  have hfa : ∀ j, fnOf W hηW (resG X e (a j)) = w j / w k := fun j => by rw [fnOf_resG, ha]
  have hden : IsDen w W (resG X e (a i₀)) := fun h j x hx => by
    rw [hfa, h1, one_div, inv_mul_eq_div, ← hfa j]; exact regAt_fnOf hx _ _
  have hgen : (1 : Γ(X, W)) ∈ gens w W :=
    ⟨_, hden, k, fun h => by rw [map_one, hfa, h1, one_div, inv_mul_cancel₀ hk]⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hyW, Scheme.mem_zeroLocus_iff]
  intro H
  exact H 1 (Ideal.subset_span hgen) (by rw [Scheme.basicOpen_one]; exact hyW)

theorem fnOf_appLE {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X) {W : X.Opens} {A : Y'.Opens} (hA : A ≤ s ⁻¹ᵁ W)
    (hA' : genericPoint Y' ∈ A) (hW : genericPoint X ∈ W) (c : Γ(X, W)) :
    fnOf A hA' ((s.appLE W A hA).hom c) = GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hW c) := by
  rw [GlobalTheory.TrueGeo.SmallSec.fnMap_fnOf s hη hW (hA hA'), ← fnOf_resG hA hA']
  rfl

theorem exists_dvd_of_effCartier [Fintype ι] {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X)
    (hE : ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier ((idealSheaf w).comap s)) (y' : Y') :
    ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k) ≠ 0 ∧ ∀ j,
      RegAt y' (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k)) := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (s y')) isOpen_univ
  obtain ⟨U0, f0, sectionFrameQuotient, hf0, hI0⟩ := hE y'
  obtain ⟨t, htle, hyt⟩ := U0.2.exists_basicOpen_le (V := U0.1 ⊓ s ⁻¹ᵁ W) ⟨y', sectionFrameQuotient, hyW⟩ sectionFrameQuotient
  have hAW : Y'.basicOpen t ≤ s ⁻¹ᵁ W := fun x hx => (htle hx).2
  have hA' : genericPoint Y' ∈ Y'.basicOpen t := gen_mem hyt
  have hηW : genericPoint X ∈ W := gen_mem hyW
  set F := resG Y' (Y'.basicOpen_le t) f0 with hFdef
  have hIA : ((idealSheaf w).comap s).ideal (Y'.affineBasicOpen t) = Ideal.span {F} := by
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, hI0, Ideal.map_span, Set.image_singleton]
  have hmap : Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W) = Ideal.span {F} := by
    rw [← hIA, GlobalTheory.Principalise.comapIdealAffine _ s ⟨W, hW⟩ (Y'.affineBasicOpen t) hAW]
    rfl
  set φ := fnOf (Y'.basicOpen t) hA'
  set w' := fun j => GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) with hw'
  have hφ : ∀ c : Γ(X, W), φ ((s.appLE W (Y'.basicOpen t) hAW).hom c) =
      GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW c) := fun c => fnOf_appLE s hη hAW hA' hηW c
  have hF0 : φ F ≠ 0 := by
    have hU0 : genericPoint Y' ∈ U0.1 := Y'.basicOpen_le t hA'
    have : Nontrivial Γ(Y', U0.1) := (fnOf U0.1 hU0).domain_nontrivial
    rw [hFdef, fnOf_resG]
    intro h
    exact nonZeroDivisors.ne_zero hf0 (fnOf_injective _ hU0 (h.trans (map_zero _).symm))
  have key : ∀ x ∈ Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W),
      ∃ C : ι → Y'.functionField, φ x = ∑ j, w' j * C j ∧ ∀ i j, ∃ r : Γ(Y', Y'.basicOpen t),
        w' i * C j = φ F * φ r := by
    intro x hx
    rw [idealOn, Ideal.map_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, ⟨a, ha, j₀, hb⟩, rfl⟩ := hx
      refine ⟨Pi.single j₀ (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW a)), ?_, fun i j => ?_⟩
      · rw [hφ, hb hηW, map_mul, Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
          (by simp), Pi.single_eq_same, mul_comm]
      · by_cases hj : j = j₀
        · subst hj
          rw [Pi.single_eq_same]
          obtain ⟨bi, hbi⟩ := exists_fnOf_eq hηW fun y hy => ha hηW i y hy
          have hmem : (s.appLE W (Y'.basicOpen t) hAW).hom bi ∈ Ideal.span {F} :=
            hmap ▸ Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, ha, i, fun _ => hbi⟩)
          obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
          refine ⟨r, ?_⟩
          rw [hw', ← map_mul, mul_comm (w i), ← hbi, ← hφ, ← hr, map_mul, mul_comm]
        · rw [Pi.single_eq_of_ne hj, mul_zero]
          exact ⟨0, by rw [map_zero, mul_zero]⟩
    | zero => exact ⟨0, by simp, fun i j => ⟨0, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨C, hC, hC'⟩ := hx
      obtain ⟨D, hD, hD'⟩ := hy
      refine ⟨C + D, by rw [map_add, hC, hD, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, mul_add],
        fun i j => ?_⟩
      obtain ⟨r, hr⟩ := hC' i j
      obtain ⟨r', hr'⟩ := hD' i j
      exact ⟨r + r', by simp only [Pi.add_apply, mul_add, hr, hr', map_add]⟩
    | smul c x _ hx =>
      obtain ⟨C, hC, hC'⟩ := hx
      refine ⟨fun j => φ c * C j, ?_, fun i j => ?_⟩
      · rw [smul_eq_mul, map_mul, hC, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · obtain ⟨r, hr⟩ := hC' i j
        refine ⟨c * r, ?_⟩
        rw [map_mul, mul_left_comm, hr]
        ring
  obtain ⟨C, hC, hC'⟩ := key F (hmap ▸ Ideal.mem_span_singleton_self F)
  choose r hr using hC'
  have hreg : ∀ i j, RegAt y' (w' i * (C j / φ F)) := fun i j => by
    rw [mul_div_assoc', hr, mul_div_cancel_left₀ _ hF0]
    exact regAt_fnOf hyt _ _
  have he1 : ∑ j, (fun _ => (1 : Y'.functionField)) j * (w' j * (C j / φ F)) = 1 := by
    simp only [one_mul, mul_div_assoc']
    rw [← Finset.sum_div, ← hC, div_self hF0]
  obtain ⟨k, hk⟩ := GlobalTheory.InvertIdeal.exists_unitAt (x := y') (c := fun _ => 1)
    (g := fun j => w' j * (C j / φ F)) (fun _ => ⟨1, map_one _⟩) (fun j => hreg j j) he1
  have hk0 : w' k * (C k / φ F) ≠ 0 := hk.ne_zero
  refine ⟨k, left_ne_zero_of_mul hk0, fun j => ?_⟩
  have e : w' j / w' k = (w' j * (C k / φ F)) * (w' k * (C k / φ F))⁻¹ := by
    have h2 : C k / φ F ≠ 0 := right_ne_zero_of_mul hk0
    rw [← div_eq_mul_inv, mul_div_mul_right _ _ h2]
  change RegAt y' (w' j / w' k)
  rw [e]
  exact (hreg j k).mul hk.inv.regAt

theorem exists_idealSheaf : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  intro Y _ N w i₀ U h1 hU
  refine ⟨idealSheaf w, idealSheaf_ne_bot i₀ h1, fun y hy => ?_, fun Y' _ s hη hE y' =>
    exists_dvd_of_effCartier s (specializes_of_eq hη) hE y'⟩
  obtain ⟨k, hk, hreg⟩ := hU y hy
  exact notMem_support i₀ h1 hk hreg

end GlobalTheory.DenomIdeal
