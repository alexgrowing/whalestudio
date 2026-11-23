import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.LocM.FJ

section Directions

variable {L L' : Type} [AddCommGroup L] [AddCommGroup L'] {K : Type} [NormedField K]

def Nonneg (P : Set L) (χ : Module.Dual ℤ L) : Prop := ∀ γ ∈ P, 0 ≤ χ γ

def Isolates (P : Set L) (γ : L) (χ : Module.Dual ℤ L) : Prop :=
  γ ∈ P ∧ Nonneg P χ ∧ ∀ χ', Nonneg P χ' → χ' γ = χ γ → χ' = χ

def IsFat (P : Set L) : Prop := ∃ k : ℕ, 0 < k ∧ ∀ γ ∈ P, ∀ δ : L, ∃ C : ℕ, ∀ N : ℕ, C ≤ N → N • γ + k • δ ∈ P

def IsExpansion (P : Set L) (Val : L → LaurentSeries K → Prop) (c : Module.Dual ℤ L → K) : Prop :=
  (∀ χ, c χ ≠ 0 → Nonneg P χ) ∧
    ∀ γ ∈ P, ∀ r, Val γ r → ∀ n : ℤ, r.coeff n = ∑ᶠ (χ : Module.Dual ℤ L) (_ : χ γ = n), c χ

def coefSet (P : Set L) (Val : L → LaurentSeries K → Prop) (χ : Module.Dual ℤ L) : Set ℝ :=
  {x | ∃ γ r, Isolates P γ χ ∧ Val γ r ∧ x = ‖r.coeff (χ γ)‖}

def coefNorm (P : Set L) (Val : L → LaurentSeries K → Prop) (χ : Module.Dual ℤ L) : ℝ := sSup (coefSet P Val χ)

variable {P : Set L} {Val : L → LaurentSeries K → Prop} {χ : Module.Dual ℤ L}

theorem IsFat.bound {k : ℕ} (h : ∀ γ ∈ P, ∀ δ : L, ∃ C : ℕ, ∀ N : ℕ, C ≤ N → N • γ + k • δ ∈ P) {γ : L} (hγ : γ ∈ P)
    (δ : L) : ∃ C : ℕ, (∀ N : ℕ, C ≤ N → N • γ + k • δ ∈ P) ∧ ∀ χ, Nonneg P χ → |k * χ δ| ≤ C * χ γ := by
  obtain ⟨C₁, h₁⟩ := h γ hγ δ
  obtain ⟨C₂, h₂⟩ := h γ hγ (-δ)
  refine ⟨max C₁ C₂, fun N hN => h₁ N ((le_max_left _ _).trans hN), fun χ hχ => ?_⟩
  have a := hχ _ (h₁ _ (le_max_left C₁ C₂))
  have b := hχ _ (h₂ _ (le_max_right C₁ C₂))
  simp only [map_add, map_nsmul, map_neg, nsmul_eq_mul, mul_neg] at a b
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem IsFat.finite [Module.Finite ℤ L] (h : IsFat P) {γ : L} (hγ : γ ∈ P) (n : ℤ) :
    {χ : Module.Dual ℤ L | Nonneg P χ ∧ χ γ = n}.Finite := by
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨m, v, hv⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  choose C _ hC using fun i => IsFat.bound h hγ (v i)
  refine Set.Finite.of_finite_image (f := fun χ i => χ (v i))
    ((Set.Finite.pi' fun i => Set.finite_Icc (-(C i * n)) (C i * n)).subset ?_)
    fun χ _ χ' _ e => LinearMap.ext_on_range hv (congrFun e)
  rintro _ ⟨χ, ⟨h₁, rfl⟩, rfl⟩ i
  refine abs_le.1 (le_trans ?_ (hC i χ h₁))
  rw [abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) (by rw [Nat.abs_cast]; exact_mod_cast hk)

theorem exists_forall_ne_zero {T : Set (Module.Dual ℤ L)} (hT : T.Finite) (h : ∀ φ ∈ T, φ ≠ 0) :
    ∃ δ : L, ∀ φ ∈ T, φ δ ≠ 0 := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert φ T _ hT ih =>
    obtain ⟨δ, hδ⟩ := ih fun ψ hψ => h ψ (Set.mem_insert_of_mem _ hψ)
    obtain ⟨a, ha⟩ : ∃ a, φ a ≠ 0 := by
      by_contra! hh
      exact h φ (Set.mem_insert _ _) (LinearMap.ext hh)
    have fin : (⋃ ψ ∈ insert φ T, {n : ℤ | ψ (n • δ + a) = 0}).Finite := by
      refine (hT.insert φ).biUnion fun ψ hψ => Set.Subsingleton.finite fun n hn n' hn' => ?_
      simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul] at hn hn'
      by_cases h0 : ψ δ = 0
      · rcases hψ with rfl | hψ
        · rw [h0] at hn; exact absurd (by simpa using hn) ha
        · exact absurd h0 (hδ ψ hψ)
      · exact mul_right_cancel₀ h0 (by linarith)
    obtain ⟨n, hn⟩ := fin.exists_notMem
    exact ⟨n • δ + a, fun ψ hψ e => hn (Set.mem_biUnion hψ e)⟩

theorem IsFat.exists_isolates [Module.Finite ℤ L] (h : IsFat P) (hne : P.Nonempty) (hχ : Nonneg P χ) :
    ∃ γ, Isolates P γ χ := by
  obtain ⟨γ, hγ⟩ := hne
  have fin := h.finite hγ (χ γ)
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨δ, hδ⟩ := exists_forall_ne_zero (T := (fun χ' => χ' - χ) '' ({χ' | Nonneg P χ' ∧ χ' γ = χ γ} \ {χ}))
    ((fin.subset Set.diff_subset).image _) (by rintro _ ⟨χ', h', rfl⟩; exact sub_ne_zero.2 h'.2)
  obtain ⟨C, hC, hb⟩ := IsFat.bound h hγ δ
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (hχ γ hγ)
  refine ⟨_, hC (C * (2 * a + 1) + 1) (by nlinarith), hχ, fun χ' h' e => ?_⟩
  simp only [map_add, map_nsmul, nsmul_eq_mul] at e
  push_cast at e
  have b := abs_le.1 (hb χ hχ)
  have b' := abs_le.1 (hb χ' h')
  have n' := h' γ hγ
  have hC0 : (0 : ℤ) ≤ C := Int.natCast_nonneg _
  have ha0 : (0 : ℤ) ≤ a := Int.natCast_nonneg _
  have e₁ : χ' γ = χ γ := by
    rw [ha] at b e ⊢
    rcases lt_trichotomy (χ' γ) a with hl | hl | hl
    · nlinarith [mul_nonneg hC0 ha0, mul_nonneg (mul_nonneg hC0 ha0) (sub_nonneg.2 (Int.add_one_le_of_lt hl)),
        mul_nonneg hC0 (sub_nonneg.2 hl.le)]
    · exact hl
    · nlinarith [mul_nonneg (mul_nonneg hC0 ha0) (sub_nonneg.2 (Int.add_one_le_of_lt hl))]
  by_contra hne
  refine hδ _ ⟨χ', ⟨⟨h', e₁⟩, hne⟩, rfl⟩ ?_
  rw [e₁, add_right_inj] at e
  exact sub_eq_zero.2 (mul_left_cancel₀ (by exact_mod_cast hk.ne') e)

theorem IsExpansion.coeff_eq {c : Module.Dual ℤ L → K} (h : IsExpansion P Val c) {γ : L} (hγ : Isolates P γ χ)
    {r : LaurentSeries K} (hr : Val γ r) : r.coeff (χ γ) = c χ := by
  rw [h.2 γ hγ.1 r hr, finsum_eq_single _ χ]
  · exact finsum_eq_single (fun _ : χ γ = χ γ => c χ) rfl fun _ h => (h rfl).elim
  · intro χ' hne
    by_cases e : χ' γ = χ γ
    · simp [of_not_not fun h0 => hne (hγ.2.2 χ' (h.1 χ' h0) e)]
    · simp [e]

theorem coefNorm_eq_zero (h : ¬ Nonneg P χ) : coefNorm P Val χ = 0 := by
  rw [coefNorm, show coefSet P Val χ = ∅ from Set.eq_empty_of_forall_notMem fun _ ⟨_, _, h', _⟩ => h h'.2.1,
    Real.sSup_empty]

theorem coefSet_nonempty [Module.Finite ℤ L] (h : IsFat P) (hne : P.Nonempty) (hV : ∀ γ ∈ P, ∃ r, Val γ r)
    (hχ : Nonneg P χ) : (coefSet P Val χ).Nonempty := by
  obtain ⟨γ, hγ⟩ := h.exists_isolates hne hχ
  obtain ⟨r, hr⟩ := hV γ hγ.1
  exact ⟨_, γ, r, hγ, hr, rfl⟩

theorem IsExpansion.coefNorm_eq [Module.Finite ℤ L] {c : Module.Dual ℤ L → K} (hc : IsExpansion P Val c) (h : IsFat P)
    (hne : P.Nonempty) (hV : ∀ γ ∈ P, ∃ r, Val γ r) (χ : Module.Dual ℤ L) : coefNorm P Val χ = ‖c χ‖ := by
  by_cases hχ : Nonneg P χ
  · have : coefSet P Val χ = {‖c χ‖} := (coefSet_nonempty h hne hV hχ).subset_singleton_iff.1 (by
      rintro _ ⟨γ, r, hγ, hr, rfl⟩
      exact congrArg _ (hc.coeff_eq hγ hr))
    rw [coefNorm, this, csSup_singleton]
  · rw [coefNorm_eq_zero hχ, of_not_not fun h0 => hχ (hc.1 χ h0), norm_zero]

theorem IsExpansion.unique [Module.Finite ℤ L] {c c' : Module.Dual ℤ L → K} (hc : IsExpansion P Val c)
    (hc' : IsExpansion P Val c') (h : IsFat P) (hne : P.Nonempty) (hV : ∀ γ ∈ P, ∃ r, Val γ r) : c = c' := by
  funext χ
  by_cases hχ : Nonneg P χ
  · obtain ⟨γ, hγ⟩ := h.exists_isolates hne hχ
    obtain ⟨r, hr⟩ := hV γ hγ.1
    exact (hc.coeff_eq hγ hr).symm.trans (hc'.coeff_eq hγ hr)
  · rw [of_not_not fun h0 => hχ (hc.1 χ h0), of_not_not fun h0 => hχ (hc'.1 χ h0)]

theorem coefSet_le {B : ℝ} (h : ∀ γ ∈ P, ∀ r, Val γ r → ∀ n, ‖r.coeff n‖ ≤ B) : ∀ x ∈ coefSet P Val χ, x ≤ B := by
  rintro _ ⟨γ, r, hγ, hr, rfl⟩
  exact h γ hγ.1 r hr _

theorem coefNorm_le {B : ℝ} (hB : 0 ≤ B) (h : ∀ γ ∈ P, ∀ r, Val γ r → ∀ n, ‖r.coeff n‖ ≤ B) : coefNorm P Val χ ≤ B :=
  Real.sSup_le (coefSet_le h) hB

theorem coefNorm_equiv (ε : L ≃ₗ[ℤ] L') {P' : Set L'} {Val' : L' → LaurentSeries K → Prop} (hP : ∀ γ, ε γ ∈ P' ↔ γ ∈ P)
    (hV : ∀ γ r, Val' (ε γ) r ↔ Val γ r) (χ' : Module.Dual ℤ L') :
    coefNorm P Val (ε.dualMap χ') = coefNorm P' Val' χ' := by
  have hN : ∀ ψ : Module.Dual ℤ L', Nonneg P (ε.dualMap ψ) ↔ Nonneg P' ψ := fun ψ =>
    ⟨fun h γ hγ => by
      obtain ⟨γ, rfl⟩ := ε.surjective γ
      exact h γ ((hP γ).1 hγ), fun h γ hγ => h _ ((hP γ).2 hγ)⟩
  have hI : ∀ γ, Isolates P γ (ε.dualMap χ') ↔ Isolates P' (ε γ) χ' := fun γ =>
    and_congr (hP γ).symm (and_congr (hN _) ⟨fun h ψ hψ e => ε.dualMap.injective (h _ ((hN ψ).2 hψ) e), fun h ψ hψ e => by
      obtain ⟨ψ, rfl⟩ := ε.dualMap.surjective ψ
      rw [h ψ ((hN ψ).1 hψ) e]⟩)
  refine congrArg sSup (Set.ext fun x => ⟨?_, ?_⟩)
  · rintro ⟨γ, r, h₁, h₂, rfl⟩
    exact ⟨ε γ, r, (hI γ).1 h₁, (hV γ r).2 h₂, rfl⟩
  · rintro ⟨γ, r, h₁, h₂, rfl⟩
    obtain ⟨γ, rfl⟩ := ε.surjective γ
    exact ⟨γ, r, (hI γ).2 h₁, (hV γ r).1 h₂, rfl⟩

theorem isFat_pos : IsFat {n : ℤ | 0 < n} := ⟨1, one_pos, fun γ hγ δ => ⟨δ.natAbs + 1, fun N hN => by
  have h : (0 : ℤ) < γ := hγ
  have hN' : |δ| + 1 ≤ (N : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hN
  change (0 : ℤ) < N • γ + 1 • δ
  rw [nsmul_eq_mul, one_smul]
  nlinarith [neg_abs_le δ, abs_nonneg δ]⟩⟩

theorem isExpansion_single [DecidableEq (Module.Dual ℤ L)] {χ₀ : Module.Dual ℤ L} (h : Nonneg P χ₀) (a : K) :
    IsExpansion P (fun γ r => r = HahnSeries.single (χ₀ γ) a) (fun χ => if χ = χ₀ then a else 0) := by
  refine ⟨fun χ hχ => (of_not_not fun e => hχ (if_neg e) : χ = χ₀) ▸ h, ?_⟩
  rintro γ - _ rfl n
  rw [finsum_eq_single _ χ₀ fun χ e => by simp [e]]
  simp only [if_true]
  by_cases e : χ₀ γ = n
  · subst e
    rw [HahnSeries.coeff_single_same]
    exact (finsum_eq_single (fun _ : χ₀ γ = χ₀ γ => a) rfl fun _ h => (h rfl).elim).symm
  · rw [HahnSeries.coeff_single_of_ne (Ne.symm e)]
    simp [e]

end Directions

section Forms

variable {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

theorem exists_sq_le {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y) (hp : ∀ y, y ≠ 0 → 0 < β y y)
    (φ : Module.Dual ℤ X) : ∃ C : ℕ, ∀ y, φ y ^ 2 ≤ C * β y y := by
  have nn : ∀ y, 0 ≤ β y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hp y h).le
  have inj : Function.Injective β := (injective_iff_map_eq_zero _).2 fun y hy => by
    by_contra h
    simpa [hy] using hp y h
  have tor : Module.IsTorsion ℤ (Module.Dual ℤ X ⧸ LinearMap.range β) := by
    rw [← Module.finrank_eq_zero_iff_isTorsion]
    have h₁ := Submodule.finrank_quotient_add_finrank (LinearMap.range β)
    rw [LinearMap.finrank_range_of_inj inj, Module.finrank_linearMap_self] at h₁
    exact Nat.add_eq_right.1 h₁
  obtain ⟨⟨d, hd⟩, h⟩ := @tor (Submodule.Quotient.mk φ)
  obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).1 (show Submodule.Quotient.mk (d • φ) = 0 from h)
  have hd1 : 1 ≤ d ^ 2 := (one_le_sq_iff_one_le_abs d).2 (Int.one_le_abs (nonZeroDivisors.ne_zero hd))
  obtain ⟨C, hC⟩ := Int.eq_ofNat_of_zero_le (nn z)
  refine ⟨C, fun y => ?_⟩
  have e : β z y = d * φ y := by rw [hz]; rfl
  have cs : β z y ^ 2 ≤ β z z * β y y := by
    by_cases h0 : z = 0
    · simp [h0]
    · have := nn (β z z • y - β z y • z)
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hs y z] at this
      exact le_of_mul_le_mul_left (by nlinarith) (hp z h0)
  rw [← hC]
  rw [e, mul_pow] at cs
  nlinarith [sq_nonneg (φ y)]

theorem exists_abs_le {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y) (hp : ∀ y, y ≠ 0 → 0 < β y y)
    (δ : LinearMap.BilinForm ℤ X) : ∃ C : ℕ, ∀ y, |δ y y| ≤ C * β y y := by
  let b := Module.finBasis ℤ X
  choose C hC using fun i => exists_sq_le hs hp (b.coord i)
  choose C' hC' using fun i => exists_sq_le hs hp (δ (b i))
  refine ⟨∑ i, (C i + C' i), fun y => ?_⟩
  have e : δ y y = ∑ i, b.coord i y * δ (b i) y := by
    refine (congrArg (fun z => δ z y) (b.sum_repr y).symm).trans ?_
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
  rw [e, Nat.cast_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h₁ := hC i y
  have h₂ := hC' i y
  push_cast
  refine abs_le.2 ⟨?_, ?_⟩ <;>
    nlinarith [sq_nonneg (b.coord i y + δ (b i) y), sq_nonneg (b.coord i y - δ (b i) y), sq_nonneg (b.coord i y),
      sq_nonneg (δ (b i) y)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (N : ℕ)

def admitted (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Set (levelForms H N X) :=
  {γ | (∀ y, y ≠ 0 → 0 < (γ : LinearMap.BilinForm ℤ X) y y) ∧ ∀ y z, (2 * N : ℤ) ∣ (γ : LinearMap.BilinForm ℤ X) y z}

variable [Module (𝓞 E) X]

variable (X) in

theorem isFat_adm : IsFat (admitted H N X) := by
  refine ⟨2, two_pos, fun γ hγ δ => ?_⟩
  obtain ⟨C, hC⟩ := exists_abs_le γ.2.1 hγ.1 δ.1
  refine ⟨2 * C + 1, fun n hn => ⟨fun y hy => ?_, fun y z => ?_⟩⟩
  · have h₁ := hγ.1 y hy
    have h₂ := (abs_le.1 (hC y)).1
    have h₃ : (2 * C + 1 : ℤ) ≤ n := by exact_mod_cast hn
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    push_cast
    nlinarith
  · simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_add ((hγ.2 y z).mul_left _) (mul_dvd_mul_left _ (δ.2.2.2 y z))

variable {H N} in
omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem nonneg_admissible_iff_positiveDefinite (χ : Module.Dual ℤ (levelForms H N X)) : Nonneg (admitted H N X) χ ↔
    ∀ γ : levelForms H N X, (∀ y, y ≠ 0 → 0 < (γ : LinearMap.BilinForm ℤ X) y y) → 0 ≤ χ γ := by
  refine ⟨fun h γ hγ => ?_, fun h γ hγ => h γ hγ.1⟩
  have := h ((2 : ℤ) • γ) ⟨fun y hy => mul_pos two_pos (hγ y hy), fun y z => mul_dvd_mul_left _ (γ.2.2.2 y z)⟩
  rw [map_smul, smul_eq_mul] at this
  omega

end Forms

end GlobalTheory.LocM.FJ
