import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem

noncomputable section

open Filter Topology

namespace GlobalTheory.CMVal.Euler

variable {G : Type} [CommGroup G] (U : Subgroup G) (ω : G →* ℂ)

def cs (M : Set G) (z : G ⧸ U) : ℂ := M.indicator ω z.out

def Stable (M : Set G) : Prop := ∀ u ∈ U, ∀ y, y * u ∈ M ↔ y ∈ M

variable {U ω}

theorem cs_mk (hω : ∀ u ∈ U, ω u = 1) {M : Set G} (hM : Stable U M) (y : G) :
    cs U ω M (QuotientGroup.mk y) = M.indicator ω y := by
  classical
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U y
  unfold cs
  rw [hu, Set.indicator_apply, Set.indicator_apply, map_mul, hω u u.2, mul_one]
  simp only [hM u u.2 y]

theorem tsum_translate (hω : ∀ u ∈ U, ω u = 1) {M : Set G} (hM : Stable U M) (π : G) :
    ∑' z, cs U ω {y | π⁻¹ * y ∈ M} z = ω π * ∑' z, cs U ω M z := by
  classical
  have hM' : Stable U {y | π⁻¹ * y ∈ M} := fun u hu y => by
    simp only [Set.mem_setOf_eq, ← mul_assoc]; exact hM u hu _
  rw [← (Equiv.mulLeft (QuotientGroup.mk π : G ⧸ U)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun z => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  show cs U ω _ (QuotientGroup.mk (π * y)) = _
  rw [cs_mk hω hM', cs_mk hω hM, Set.indicator_apply, Set.indicator_apply]
  simp

theorem summable_mono {B M : Set G} (hB : Summable (cs U ω B)) (h : M ⊆ B) : Summable (cs U ω M) := by
  refine Summable.of_norm_bounded hB.norm fun z => ?_
  exact norm_indicator_le_of_subset h _ _

theorem tsum_split (hω : ∀ u ∈ U, ω u = 1) {B M M₁ M' : Set G} (hB : Summable (cs U ω B)) (h : M ⊆ B) (h₁ : M₁ ⊆ M)
    (hM' : Stable U M') (π : G) (hπ : ∀ y, π⁻¹ * y ∈ M' ↔ y ∈ M ∧ y ∉ M₁) :
    ∑' z, cs U ω M z = ∑' z, cs U ω M₁ z + ω π * ∑' z, cs U ω M' z := by
  classical
  rw [← tsum_translate hω hM', ← (summable_mono hB (h₁.trans h)).tsum_add
    (summable_mono (M := {y | π⁻¹ * y ∈ M'}) hB (fun y hy => h ((hπ y).1 hy).1))]
  refine tsum_congr fun z => ?_
  simp only [cs, Set.indicator_apply, Set.mem_setOf_eq, hπ]
  by_cases a : z.out ∈ M₁
  · simp [a, h₁ a]
  · simp [a]

theorem tsum_zero_of (hω : ∀ u ∈ U, ω u = 1) {M : Set G} (hM : Stable U M) (u : G) (hu : ω u ≠ 1)
    (h : ∀ y, u⁻¹ * y ∈ M ↔ y ∈ M) : ∑' z, cs U ω M z = 0 := by
  have h1 := tsum_translate hω hM u
  have h2 : {y | u⁻¹ * y ∈ M} = M := Set.ext h
  rw [h2] at h1
  have h3 : (ω u - 1) * ∑' z, cs U ω M z = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hu)

theorem tsum_fin (hω : ∀ u ∈ U, ω u = 1) {B M M' : Set G} (hB : Summable (cs U ω B)) (h : M' ⊆ B) (hM : Stable U M)
    {ι : Type} (R : Finset ι) (g : ι → G) (hg : ∀ r ∈ R, ω (g r) = 1)
    (h1 : ∀ y ∈ M', ∃! r, r ∈ R ∧ (g r)⁻¹ * y ∈ M) (h2 : ∀ r ∈ R, ∀ y, (g r)⁻¹ * y ∈ M → y ∈ M') :
    ∑' z, cs U ω M' z = R.card * ∑' z, cs U ω M z := by
  classical
  have h3 : ∑ r ∈ R, ∑' z, cs U ω {y | (g r)⁻¹ * y ∈ M} z = R.card * ∑' z, cs U ω M z := by
    rw [Finset.sum_congr rfl fun r hr => (tsum_translate hω hM (g r)).trans (by rw [hg r hr, one_mul])]
    simp
  rw [← h3, ← Summable.tsum_finsetSum fun r hr =>
    summable_mono (M := {y | (g r)⁻¹ * y ∈ M}) hB (fun y hy => h (h2 r hr y hy))]
  refine tsum_congr fun z => ?_
  simp only [cs, Set.indicator_apply, Set.mem_setOf_eq]
  by_cases a : z.out ∈ M'
  · obtain ⟨r, ⟨hr, hr'⟩, hu⟩ := h1 _ a
    rw [if_pos a, Finset.sum_eq_single r, if_pos hr']
    · intro b hb hne
      exact if_neg fun hh => hne (hu b ⟨hb, hh⟩)
    · exact fun hh => absurd hr hh
  · rw [if_neg a]
    exact (Finset.sum_eq_zero fun r hr => if_neg fun hh => a (h2 r hr _ hh)).symm

theorem tendsto_tsum_one (hω : ∀ u ∈ U, ω u = 1) {B : Set G} (hB : Summable (cs U ω B)) {ι : Type} (l : Filter ι)
    (M : ι → Set G) (h : ∀ s, M s ⊆ B) (h1 : ∀ y ∈ U, ∀ s, y ∈ M s) (h2 : ∀ y ∉ U, ∀ᶠ s in l, y ∉ M s) :
    Tendsto (fun s => ∑' z, cs U ω (M s) z) l (𝓝 1) := by
  classical
  have h0 : ∑' z : G ⧸ U, (if z = 1 then (1 : ℂ) else 0) = 1 := tsum_ite_eq _ _
  rw [← h0]
  refine tendsto_tsum_of_dominated_convergence hB.norm (fun z => ?_)
    (Eventually.of_forall fun s z => norm_indicator_le_of_subset (h s) _ _)
  have h4 : z.out ∈ U ↔ z = 1 := by rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
  by_cases a : z = 1
  · rw [if_pos a]
    refine tendsto_const_nhds.congr fun s => ?_
    rw [cs, Set.indicator_of_mem (h1 _ (h4.2 a) s), hω _ (h4.2 a)]
  · rw [if_neg a]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h2 _ (fun hh => a (h4.1 hh))] with s hs
    rw [cs, Set.indicator_of_notMem hs]

theorem hasSum_classes {M : Set G} (hM : Stable U M) (hs : Summable (cs U ω M)) :
    HasSum (fun z : {z : G ⧸ U // ∃ y : G, (QuotientGroup.mk y : G ⧸ U) = z ∧ y ∈ M} => ω z.1.out) (∑' z, cs U ω M z) := by
  classical
  have h1 : cs U ω M = Set.indicator {z : G ⧸ U | ∃ y : G, (QuotientGroup.mk y : G ⧸ U) = z ∧ y ∈ M} fun z => ω z.out := by
    funext z
    have : z.out ∈ M ↔ ∃ y : G, (QuotientGroup.mk y : G ⧸ U) = z ∧ y ∈ M := by
      refine ⟨fun h => ⟨_, QuotientGroup.out_eq' z, h⟩, ?_⟩
      rintro ⟨y, rfl, hy⟩
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U y
      rw [hu]; exact (hM u u.2 y).2 hy
    simp only [cs, Set.indicator_apply, Set.mem_setOf_eq, this]
  have h2 := hs.hasSum
  rw [h1] at h2
  rw [h1]
  exact hasSum_subtype_iff_indicator.2 h2

end GlobalTheory.CMVal.Euler

end

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology

namespace GlobalTheory.CMVal.Euler

variable {E : Type} [Field E] [NumberField E]

theorem modF_unit {y : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) = 1) : modF y = 1 := by
  unfold modF
  simp [h]

def omega (χ : HChar E) (S : ℂ) : (Af E)ˣ →* ℂ where
  toFun y := (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S
  map_one' := by rw [map_one, modF_unit fun w => by simp [one_coord]]; simp
  map_mul' y y' := by
    rw [map_mul, IdeleModule.modF_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (IdeleModule.modF_pos y).le (IdeleModule.modF_pos y').le, Units.val_mul]
    ring

theorem omega_apply (χ : HChar E) (S : ℂ) (y : (Af E)ˣ) : omega χ S y = (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S := rfl

theorem omega_unit (χ : HChar E) (S : ℂ) {y : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) = 1) :
    omega χ S y = finPart χ y := by
  rw [omega_apply, modF_unit h]; simp

theorem norm_omega {χ : HChar E} (h : IsUnitary χ) (S : ℂ) (y : (Af E)ˣ) : ‖omega χ S y‖ = modF y ^ S.re := by
  rw [omega_apply, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (IdeleModule.modF_pos y)]
  have : ‖(finPart χ y : ℂ)‖ = 1 := h _
  rw [this, one_mul]

theorem inv_natCast_cpow (N : ℕ) (S : ℂ) : ((((N : ℝ)⁻¹ : ℝ)) : ℂ) ^ S = (N : ℂ) ^ (-S) := by
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg]

theorem omega_unifAt (χ : HChar E) (S : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    omega χ S (unifAt w) = (val χ w : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-S) := by
  rw [omega_apply, finPart_unifAt, modF_unifAt, inv_natCast_cpow]

theorem one_sub_omega_ne {χ : HChar E} (h : IsUnitary χ) {S : ℂ} (hS : 0 < S.re) (w : HeightOneSpectrum (𝓞 E)) :
    1 - omega χ S (unifAt w) ≠ 0 := by
  intro h0
  have h1 := norm_omega h S (unifAt w)
  rw [← sub_eq_zero.1 h0, norm_one, modF_unifAt] at h1
  have h2 : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  exact (Real.rpow_lt_one (by positivity) (inv_lt_one_of_one_lt₀ h2) hS).ne' h1

def intI : Set (Af E)ˣ := {y | ∀ w, Valued.v ((y : Af E) w) ≤ 1}

def MS (m : HeightOneSpectrum (OF E) → ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) : Set (Af E)ˣ :=
  {y | (∀ v, LocIn (m v) v (y : Af E)) ∧ ∀ w ∈ T, Valued.v ((y : Af E) w) = 1}

theorem MS_subset (m : HeightOneSpectrum (OF E) → ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) : MS m T ⊆ intI :=
  fun _ hy w => (hy.1 _).val_le (over_under w)

theorem MS_anti (m : HeightOneSpectrum (OF E) → ℕ) {T T' : Finset (HeightOneSpectrum (𝓞 E))} (h : T ⊆ T') : MS m T' ⊆ MS m T :=
  fun _ hy => ⟨hy.1, fun w hw => hy.2 w (h hw)⟩

theorem mul_mem_MS {m : HeightOneSpectrum (OF E) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 E))} {u y : (Af E)ˣ}
    (hu : ∀ v, LocIn (m v) v (u : Af E)) (hu' : ∀ w, Valued.v ((u : Af E) w) = 1) (hy : y ∈ MS m T) : y * u ∈ MS m T :=
  ⟨fun v => (hy.1 v).mul (hu v), fun w hw => by rw [Units.val_mul, mul_coord, map_mul, hy.2 w hw, hu' w, one_mul]⟩

theorem val_inv_one {u : (Af E)ˣ} (hu' : ∀ w, Valued.v ((u : Af E) w) = 1) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (((u⁻¹ : (Af E)ˣ) : Af E) w) = 1 := by rw [inv_coord, map_inv₀, hu', inv_one]

theorem mul_mem_MS_iff {m : HeightOneSpectrum (OF E) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 E))} {u : (Af E)ˣ}
    (hu : ∀ v, LocIn (m v) v (u : Af E)) (hu' : ∀ w, Valued.v ((u : Af E) w) = 1) (y : (Af E)ˣ) :
    y * u ∈ MS m T ↔ y ∈ MS m T := by
  refine ⟨fun h => ?_, mul_mem_MS hu hu'⟩
  have := mul_mem_MS (u := u⁻¹) (fun v => (hu v).inv fun P _ => hu' P) (val_inv_one hu') h
  rwa [mul_inv_cancel_right] at this

theorem stable_MS {c : Ideal (OF E)} {m : HeightOneSpectrum (OF E) → ℕ} (hm : ∀ v, m v ≤ expIn c v)
    (T : Finset (HeightOneSpectrum (𝓞 E))) : Stable (hatOUnits c) (MS m T) := fun _ hu =>
  mul_mem_MS_iff (fun v => (locIn_of_mem_hatO hu.1 v).mono (hm v)) (OrderUnits.val_eq_one hu)

theorem shift_coord {π : (Af E)ˣ} (y : (Af E)ˣ) {w : HeightOneSpectrum (𝓞 E)} (h : (π : Af E) w = 1) :
    ((π⁻¹ * y : (Af E)ˣ) : Af E) w = (y : Af E) w := by
  rw [Units.val_mul, mul_coord, inv_coord, h, inv_one, one_mul]

theorem not_over {w : HeightOneSpectrum (𝓞 E)} {v v' : HeightOneSpectrum (OF E)} (h : Over w v') (hne : v' ≠ v) : ¬ Over w v :=
  fun h' => hne (((over_iff_under _ _).1 h).symm.trans ((over_iff_under _ _).1 h'))

theorem forall_locIn_shift {m m' : HeightOneSpectrum (OF E) → ℕ} {v : HeightOneSpectrum (OF E)} (hm : ∀ v' ≠ v, m' v' = m v')
    {π : (Af E)ˣ} (hπ : ∀ w, ¬ Over w v → (π : Af E) w = 1) (y : (Af E)ˣ) :
    (∀ v', LocIn (m' v') v' ((π⁻¹ * y : (Af E)ˣ) : Af E)) ↔
      LocIn (m' v) v ((π⁻¹ * y : (Af E)ˣ) : Af E) ∧ ∀ v' ≠ v, LocIn (m v') v' (y : Af E) := by
  have key : ∀ v' ≠ v, LocIn (m' v') v' ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (m v') v' (y : Af E) := fun v' hv' => by
    rw [hm v' hv']
    exact locIn_congr fun P hP => shift_coord y (hπ P (not_over hP hv'))
  refine ⟨fun h => ⟨h v, fun v' hv' => (key v' hv').1 (h v')⟩, fun h v' => ?_⟩
  by_cases hv' : v' = v
  · rw [hv']; exact h.1
  · exact (key v' hv').2 (h.2 v' hv')

theorem forall_locIn_iff (m : HeightOneSpectrum (OF E) → ℕ) (v : HeightOneSpectrum (OF E)) (y : Af E) :
    (∀ v', LocIn (m v') v' y) ↔ LocIn (m v) v y ∧ ∀ v' ≠ v, LocIn (m v') v' y := by
  refine ⟨fun h => ⟨h v, fun v' _ => h v'⟩, fun h v' => ?_⟩
  by_cases hv' : v' = v
  · rw [hv']; exact h.1
  · exact h.2 v' hv'

theorem single_off {v : HeightOneSpectrum (OF E)} {P : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (x : (P.adicCompletion E)ˣ)
    (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ Over w v) : (single P x : Af E) w = 1 :=
  suppAt_single P x w fun h => hw (h ▸ hP)

theorem val_single {P : HeightOneSpectrum (𝓞 E)} {x : (P.adicCompletion E)ˣ} (hx : Valued.v (x : P.adicCompletion E) = 1)
    (w : HeightOneSpectrum (𝓞 E)) : Valued.v ((single P x : Af E) w) = 1 := by
  by_cases h : w = P
  · subst h; rw [single_self, hx]
  · rw [suppAt_single P x w h, map_one]

open Classical in

theorem unif_shift {m : HeightOneSpectrum (OF E) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)}
    (hm : m (w.under (OF E)) = 0) (hw : w ∉ T) (y : (Af E)ˣ) :
    (unifAt w)⁻¹ * y ∈ MS m T ↔ y ∈ MS m T ∧ y ∉ MS m (insert w T) := by
  obtain ⟨h1, h2⟩ := unifAt_spec w
  have hT : (∀ w' ∈ T, Valued.v ((((unifAt w)⁻¹ * y : (Af E)ˣ) : Af E) w') = 1) ↔ ∀ w' ∈ T, Valued.v ((y : Af E) w') = 1 :=
    forall₂_congr fun w' hw' => by rw [shift_coord y (h1 w' fun h => hw (h ▸ hw'))]
  have hw1 : Valued.v ((((unifAt w)⁻¹ * y : (Af E)ˣ) : Af E) w) ≤ 1 ↔
      Valued.v ((y : Af E) w) ≤ 1 ∧ Valued.v ((y : Af E) w) ≠ 1 := by
    rw [Units.val_mul, mul_coord, inv_coord, map_mul, map_inv₀, h2,
      ← WithZero.exp_log (IdeleModule.coord_ne y w), ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, Ne,
      WithZero.exp_le_exp, WithZero.exp_le_exp, WithZero.exp_inj]
    omega
  have hL : LocIn 0 (w.under (OF E)) (((unifAt w)⁻¹ * y : (Af E)ˣ) : Af E) ↔
      LocIn 0 (w.under (OF E)) (y : Af E) ∧ Valued.v ((y : Af E) w) ≠ 1 := by
    rw [locIn_zero_iff, locIn_zero_iff]
    constructor
    · intro h
      refine ⟨fun P hP => ?_, (hw1.1 (h w (over_under w))).2⟩
      by_cases hPw : P = w
      · subst hPw; exact (hw1.1 (h P hP)).1
      · rw [← shift_coord y (h1 P hPw)]; exact h P hP
    · rintro ⟨h, h'⟩ P hP
      by_cases hPw : P = w
      · subst hPw; exact hw1.2 ⟨h P hP, h'⟩
      · rw [shift_coord y (h1 P hPw)]; exact h P hP
  simp only [MS, Set.mem_setOf_eq, Finset.forall_mem_insert]
  rw [hT, forall_locIn_shift (m := m) (v := w.under (OF E)) (fun _ _ => rfl)
    (fun w' hw' => h1 w' fun h => hw' (h ▸ over_under w)), forall_locIn_iff m (w.under (OF E)), hm, hL]
  tauto

end GlobalTheory.CMVal.Euler
