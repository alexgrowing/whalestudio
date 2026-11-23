import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero

namespace GlobalTheory.IoInj

open PowerSeries

theorem series_form {O : Type} [CommRing O] (ϖ : O) (hO : ∀ a, IsUnit a ∨ ϖ ∣ a) (a : O⟦X⟧) :
    (∃ b, a = C ϖ * b) ∨ ∃ (b : O⟦X⟧) (k : ℕ) (u : O⟦X⟧), IsUnit u ∧ a = C ϖ * b + X ^ k * u := by
  classical
  by_cases h : ∀ n, ϖ ∣ coeff n a
  · left
    choose d hd using h
    exact ⟨mk d, by ext n; simp [hd]⟩
  · right
    push_neg at h
    have h1 := Nat.find_spec h
    have h2 : ∀ n, ∃ d, n < Nat.find h → coeff n a = ϖ * d := by
      intro n
      by_cases hn : n < Nat.find h
      · obtain ⟨d, hd⟩ := not_not.mp (Nat.find_min h hn)
        exact ⟨d, fun _ => hd⟩
      · exact ⟨0, fun h' => absurd h' hn⟩
    choose d hd using h2
    refine ⟨mk fun n => if n < Nat.find h then d n else 0, Nat.find h,
      mk fun n => coeff (n + Nat.find h) a, ?_, ?_⟩
    · rw [isUnit_iff_constantCoeff]
      simpa using (hO _).resolve_right h1
    · ext n
      rw [map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk]
      by_cases hn : n < Nat.find h
      · rw [if_pos hn, if_neg (by omega), hd n hn, add_zero]
      · rw [if_neg hn, if_pos (by omega), coeff_mk, Nat.sub_add_cancel (by omega), mul_zero, zero_add]

theorem letter_form {O ι : Type} [CommRing O] [DecidableEq ι] (ϖ : O) (hO : ∀ a, IsUnit a ∨ ϖ ∣ a)
    (a : ι → O⟦X⟧) (i : ι) :
    (∃ b, Pi.single i 1 * a = (fun _ => C ϖ) * b) ∨ ∃ (b : ι → O⟦X⟧) (k : ℕ) (u : ι → O⟦X⟧), IsUnit u ∧
      Pi.single i 1 * a = (fun _ => C ϖ) * b + (fun _ => X) ^ k * u * Pi.single i 1 := by
  rcases series_form ϖ hO (a i) with ⟨b, hb⟩ | ⟨b, k, u, hu, hb⟩
  · left
    refine ⟨Pi.single i b, ?_⟩
    funext i'
    by_cases h : i' = i
    · subst h; simp [hb]
    · simp [h]
  · right
    refine ⟨Pi.single i b, k, fun _ => u, Pi.isUnit_iff.mpr fun _ => hu, ?_⟩
    funext i'
    by_cases h : i' = i
    · subst h; simp [hb]
    · simp [h]

theorem prec_pi {O ι : Type} [CommRing O] (q : ℕ)
    (h : ∀ a : ℕ → O, (∀ k k', k ≤ k' → (q : O) ^ k ∣ a k - a k') → ∃ L, ∀ k, (q : O) ^ k ∣ a k - L)
    (a : ℕ → ι → O⟦X⟧) (ha : ∀ k k', k ≤ k' → (q : ι → O⟦X⟧) ^ k ∣ a k - a k') :
    ∃ L, ∀ k, (q : ι → O⟦X⟧) ^ k ∣ a k - L := by
  have hq : ∀ k : ℕ, ((q : O⟦X⟧)) ^ k = C ((q : O) ^ k) := by intro k; simp
  have h1 : ∀ i n, ∃ L, ∀ k, (q : O) ^ k ∣ coeff n (a k i) - L := by
    intro i n
    apply h
    intro k k' hk
    obtain ⟨d, hd⟩ := ha k k' hk
    refine ⟨coeff n (d i), ?_⟩
    have := congrArg (fun x => coeff n (x i)) hd
    simpa only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, map_sub, hq, coeff_C_mul] using this
  choose L hL using h1
  choose d hd using hL
  refine ⟨fun i => mk (L i), fun k => ⟨fun i => mk fun n => d i n k, ?_⟩⟩
  funext i
  ext n
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, map_sub, hq, coeff_C_mul, coeff_mk, hd]

section Abstract

variable {A E B W ι : Type} [CommRing A] [CommRing E] [CommRing B] [CommRing W] [Fintype ι]

theorem idem_eq_zero {R : Type} [CommRing R] {e : R} (he : e * e = e) (h : e ∈ Ideal.jacobson (⊥ : Ideal R)) :
    e = 0 := by
  have hu := Ideal.mem_jacobson_bot.mp h (-1)
  apply hu.mul_right_eq_zero.mp
  linear_combination -he

theorem mem_jac_of_pow {R : Type} [CommRing R] {t u : R} (hu : IsUnit u) {n : ℕ}
    (h : u * t ^ n ∈ Ideal.jacobson (⊥ : Ideal R)) (hn : n ≠ 0) : t ∈ Ideal.jacobson (⊥ : Ideal R) := by
  rw [Ideal.jacobson, Ideal.mem_sInf] at h ⊢
  intro J hJ
  haveI := hJ.2.isPrime
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance n ((Ideal.unit_mul_mem_iff_mem J hu).mp (h hJ))

theorem abstract (j : A →+* E) (f : E →+* W) (g : A →+* B) (c : B →+* W) (hcomm : ∀ a, f (j a) = c (g a))
    (p : ℕ) (t π U : A) (n : ℕ) (hU : IsUnit U) (hp : (p : A) = U * t ^ (n + 1))
    (e : ι → A) (hee : ∀ i, e i * e i = e i) (hsum : ∑ i, e i = 1)
    (dich : ∀ a i, (∃ b, e i * a = t * b) ∨ ∃ (b : A) (k : ℕ) (u : A), IsUnit u ∧
      e i * a = t * b + π ^ k * u * e i)
    (hA : ∀ a : ℕ → A, (∀ k k', k ≤ k' → (p : A) ^ k ∣ a k - a k') → ∃ L, ∀ k, (p : A) ^ k ∣ a k - L)
    (hπ : IsUnit (j π)) (hE : IsAdicComplete (Ideal.span {(p : E)}) E)
    (hdense : ∀ x : E, ∃ (a : A) (m : ℕ), x * j (π ^ m) - j a ∈ Ideal.span {(p : E) ^ 1})
    (hsat : ∀ (a : A) (k : ℕ), j a ∈ Ideal.span {(p : E) ^ k} → ∃ b, a = (p : A) ^ k * b)
    (hWJ : (p : W) ∈ Ideal.jacobson (⊥ : Ideal W)) (hWtf : ∀ x : W, (p : W) * x = 0 → x = 0)
    (hcs : ∀ (y : B) (x : W), c y = (p : W) * x → ∃ y', c y' = x)
    (hBJ : g π ∈ Ideal.jacobson (⊥ : Ideal B)) (hne : ∀ i, f (j (e i)) ≠ 0) :
    Function.Injective f ∧ (∀ x, IsUnit (f x) → IsUnit x) ∧
      (∀ (x : E) (y : W), f x = (p : W) * y → ∃ x', x = (p : E) * x') ∧
      ∀ x : E, (∃ y, c y = f x) → ∃ a, j a = x := by
  classical
  have hpE : (p : E) = j U * j t ^ (n + 1) := by rw [← map_natCast j, hp]; simp
  have hpW : (p : W) = f (j U) * f (j t) ^ (n + 1) := by rw [← map_natCast f, hpE]; simp
  have hUE : IsUnit (j U) := hU.map j
  have hUW : IsUnit (f (j U)) := hUE.map f
  have htW : f (j t) ∈ Ideal.jacobson (⊥ : Ideal W) := mem_jac_of_pow hUW (hpW ▸ hWJ) (by omega)
  have htE : j t ∈ Ideal.jacobson (⊥ : Ideal E) := by
    refine mem_jac_of_pow hUE (n := n + 1) ?_ (by omega)
    rw [← hpE]
    exact IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self _)
  have hsep : ∀ x : E, (∀ k, (p : E) ^ k ∣ x) → x = 0 := by
    intro x hx
    apply IsHausdorff.haus hE.toIsHausdorff
    intro k
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k
  have htp : ∀ k, (p : E) ^ k ∣ j t ^ ((n + 1) * k) := by
    intro k
    rw [hpE, pow_mul]
    exact pow_dvd_pow_of_dvd (hUE.mul_left_dvd.mpr dvd_rfl) k
  have httf : ∀ x : W, f (j t) * x = 0 → x = 0 := by
    intro x hx
    apply hWtf
    rw [hpW]
    linear_combination f (j U) * f (j t) ^ n * hx
  have hne' : ∀ i, ¬ f (j t) ∣ f (j (e i)) := by
    rintro i ⟨w, hw⟩
    apply hne i
    apply idem_eq_zero
    · rw [← map_mul, ← map_mul, hee]
    · rw [hw]; exact Ideal.mul_mem_right _ _ htW
  have hd : ∀ x : E, ∃ (a : A) (m : ℕ) (z : E), x * j π ^ m = j a + j t * z := by
    intro x
    obtain ⟨a, m, h⟩ := hdense x
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp h
    refine ⟨a, m, j U * j t ^ n * z, ?_⟩
    rw [pow_one, hpE, map_pow] at hz
    linear_combination hz
  obtain ⟨πi, hπi⟩ := hπ.exists_right_inv
  have hπm : ∀ m : ℕ, j π ^ m * πi ^ m = 1 := fun m => by rw [← mul_pow, hπi, one_pow]

  have key1 : ∀ x : E, f (j t) ∣ f x → j t ∣ x := by
    intro x hx
    obtain ⟨a, m, z, h⟩ := hd x
    have ha : f (j t) ∣ f (j a) := by
      have : f (j a) = f x * f (j π) ^ m - f (j t) * f z := by
        have := congrArg f h
        simp only [map_mul, map_add, map_pow] at this
        linear_combination -this
      rw [this]
      exact dvd_sub (hx.mul_right _) (dvd_mul_right _ _)
    have h2 : ∀ i, t ∣ e i * a := by
      intro i
      rcases dich a i with h | ⟨b, k, u, hu, hb⟩
      · exact h
      · exfalso
        apply hne' i
        have h3 := congrArg (fun x => f (j x)) hb
        simp only [map_mul, map_add, map_pow] at h3
        have h4 : IsUnit (f (j π) ^ k * f (j u)) := ((hπ.map f).pow k).mul ((hu.map j).map f)
        rw [← h4.dvd_mul_left]
        have : f (j π) ^ k * f (j u) * f (j (e i)) = f (j (e i)) * f (j a) - f (j t) * f (j b) := by
          linear_combination -h3
        rw [this]
        exact dvd_sub (ha.mul_left _) (dvd_mul_right _ _)
    have h5 : t ∣ a := by
      rw [← one_mul a, ← hsum, Finset.sum_mul]
      exact Finset.dvd_sum fun i _ => h2 i
    rw [← (hπ.pow m).dvd_mul_right, h]
    exact dvd_add (map_dvd j h5) (dvd_mul_right _ _)
  have key1' : ∀ (k : ℕ) (x : E), f (j t) ^ k ∣ f x → j t ^ k ∣ x := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      rintro x ⟨y, hy⟩
      obtain ⟨x', rfl⟩ := key1 x ⟨f (j t) ^ k * y, by rw [hy]; ring⟩
      rw [pow_succ']
      refine mul_dvd_mul_left _ (ih _ ⟨y, ?_⟩)
      rw [← sub_eq_zero]
      apply httf
      rw [map_mul] at hy
      linear_combination hy

  have key2 : ∀ x : E, (∃ y, c y = f x) → ∃ (a : A) (x' : E), x = j a + j t * x' ∧ ∃ y, c y = f x' := by
    rintro x ⟨y, hy⟩
    obtain ⟨a, m, z, h⟩ := hd x
    have h2 : ∀ i, ∃ b d, e i * a = t * b + π ^ m * d := by
      intro i
      rcases dich a i with ⟨b, h⟩ | ⟨b, k, u, hu, hb⟩
      · exact ⟨b, 0, by simp [h]⟩
      · by_cases hk : m ≤ k
        · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
          exact ⟨b, π ^ r * u * e i, by rw [hb]; ring⟩
        · exfalso
          obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.mp hk)
          apply hne' i
          have h3 := congrArg (fun x => f (j x)) hb
          simp only [map_mul, map_add, map_pow] at h3
          have h4 := congrArg f h
          simp only [map_mul, map_add, map_pow] at h4
          obtain ⟨v, hv⟩ := hu.exists_right_inv
          have h5 : IsUnit (c (g π * (-(y * g π ^ r * g v)) + 1)) :=
            (Ideal.mem_jacobson_bot.mp hBJ _).map c
          simp only [map_mul, map_add, map_pow, map_neg, map_one, ← hcomm, hy] at h5
          have h6 : f (j u) * f (j v) = 1 := by rw [← map_mul, ← map_mul, hv, map_one, map_one]
          rw [← (h5.mul ((hπ.map f).pow k)).dvd_mul_left]
          refine ⟨-(f (j v)) * (f (j b) + f (j (e i)) * f z), ?_⟩
          linear_combination (-f (j v)) * h3 - f (j v) * f (j (e i)) * h4 - f (j π) ^ k * f (j (e i)) * h6
    choose b d hbd using h2
    have h5 : a = t * ∑ i, b i + π ^ m * ∑ i, d i := by
      rw [← one_mul a, ← hsum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hbd i
    have h6 : x = j (∑ i, d i) + j t * ((j (∑ i, b i) + z) * πi ^ m) := by
      rw [h5] at h
      simp only [map_mul, map_add, map_pow] at h
      linear_combination πi ^ m * h - (x - j (∑ i, d i)) * hπm m
    refine ⟨_, _, h6, ?_⟩
    apply hcs (g U * g t ^ n * (y - g (∑ i, d i)))
    have h7 := congrArg f h6
    rw [map_add, map_mul] at h7
    simp only [map_mul c, map_pow c, map_sub c, ← hcomm, hy, hpW]
    linear_combination f (j U) * f (j t) ^ n * h7
  have key2' : ∀ (k : ℕ) (x : E), (∃ y, c y = f x) → ∃ a : A, j t ^ k ∣ x - j a := by
    intro k
    induction k with
    | zero => intro x _; exact ⟨0, by simp⟩
    | succ k ih =>
      intro x hx
      obtain ⟨a, x', rfl, hx'⟩ := key2 x hx
      obtain ⟨a', w, hw⟩ := ih x' hx'
      refine ⟨a + t * a', w, ?_⟩
      rw [map_add, map_mul]
      linear_combination j t * hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    exact hsep x fun k => (htp k).trans (key1' _ x (by simp [hx]))
  · intro x hx
    by_contra hn
    obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits hn
    have htM : j t ∈ M := (Ideal.mem_sInf.mp htE) ⟨bot_le, hM⟩
    obtain ⟨a, m, z, h⟩ := hd x
    have haM : j a ∈ M := by
      have : j a = x * j π ^ m - j t * z := by linear_combination -h
      rw [this]
      exact M.sub_mem (M.mul_mem_right _ hxM) (M.mul_mem_right _ htM)
    apply hM.ne_top
    rw [Ideal.eq_top_iff_one, ← map_one j, ← hsum, map_sum]
    refine M.sum_mem fun i _ => ?_
    rcases dich a i with ⟨b, hb⟩ | ⟨b, k, u, hu, hb⟩
    · exfalso
      apply hne' i
      have h3 := congrArg (fun x => f (j x)) hb
      simp only [map_mul] at h3
      have h4 := congrArg f h
      simp only [map_mul, map_add, map_pow] at h4
      rw [← (hx.mul ((hπ.map f).pow m)).dvd_mul_left]
      refine ⟨f (j b) + f (j (e i)) * f z, ?_⟩
      linear_combination h3 + f (j (e i)) * h4
    · have h3 := congrArg j hb
      simp only [map_mul, map_add, map_pow] at h3
      rw [← Ideal.unit_mul_mem_iff_mem M ((hπ.pow k).mul (hu.map j))]
      have : j π ^ k * j u * j (e i) = j (e i) * j a - j t * j b := by linear_combination -h3
      rw [this]
      exact M.sub_mem (M.mul_mem_left _ haM) (M.mul_mem_right _ htM)
  · intro x y hy
    have := (htp 1).trans (key1' _ x ⟨f (j U) * y, by rw [hy, hpW]; ring⟩)
    rwa [pow_one] at this
  · intro x hx
    have h1 : ∀ k, ∃ a : A, (p : E) ^ k ∣ x - j a := fun k =>
      (key2' ((n + 1) * k) x hx).imp fun a ha => (htp k).trans ha
    choose a ha using h1
    obtain ⟨L, hL⟩ := hA a (by
      intro k k' hk
      apply hsat
      rw [Ideal.mem_span_singleton, map_sub]
      have : j (a k) - j (a k') = (x - j (a k')) - (x - j (a k)) := by ring
      rw [this]
      exact dvd_sub ((pow_dvd_pow _ hk).trans (ha k')) (ha k))
    refine ⟨L, (sub_eq_zero.mp (hsep _ fun k => ?_)).symm⟩
    have h2 := map_dvd j (hL k)
    rw [map_pow, map_natCast, map_sub] at h2
    have : x - j L = (x - j (a k)) + (j (a k) - j L) := by ring
    rw [this]
    exact dvd_add (ha k) h2

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem not_isUnit_εroot_sub_one {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    ¬ IsUnit (AI.εroot s - 1) := by
  induction s with
  | zero =>
    intro h
    have h1 := h.map (PreTilt.coeff (O := OC l) (p := l) 0)
    rw [map_sub, map_one, LocAinf.εroot, Function.iterate_zero_apply, AI.ε_coeff, AI.ζ_zero, map_one,
      sub_self] at h1
    exact not_isUnit_zero h1
  | succ s ih =>
    intro h
    apply ih
    have h1 := h.pow l
    rwa [sub_pow_char, one_pow, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p] at h1

theorem letφ_letE {O : Type} [CommRing O] {n : ℕ} (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) :
    letφ φ₀ (Pi.single i 1 : LetA O n) = Pi.single (i + 1) 1 := by
  funext i'
  change φ₀ ((Pi.single i 1 : LetA O n) (i' - 1)) = _
  by_cases h : i' = i + 1
  · subst h; simp
  · have h' : i' - 1 ≠ i := fun h' => h (by rw [← h']; ring)
    simp [h, h']

theorem idem_ne_zero {O E W : Type} [CommRing O] [CommRing E] [CommRing W] [Nontrivial W] {n : ℕ} [NeZero n]
    (j : LetA O n →+* E) (f : E →+* W) (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (φE : E → E) (φW : W → W) (h0 : φW 0 = 0)
    (h₁ : ∀ a, φE (j a) = j (letφ φ₀ a)) (h₂ : ∀ e, f (φE e) = φW (f e)) (i : ZMod n) :
    f (j (Pi.single i 1)) ≠ 0 := by
  intro hi
  have h1 : ∀ m : ℕ, f (j (Pi.single (i + (m : ZMod n)) 1)) = 0 := by
    intro m
    induction m with
    | zero => simpa using hi
    | succ m ih => rw [Nat.cast_succ, ← add_assoc, ← letφ_letE φ₀, ← h₁, h₂, ih, h0]
  apply one_ne_zero (α := W)
  rw [← map_one f, ← map_one j, ← Finset.univ_sum_single (1 : LetA O n), map_sum, map_sum]
  refine Finset.sum_eq_zero fun i' _ => ?_
  have := h1 (i' - i).val
  rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this

set_option maxHeartbeats 1000000 in

theorem ioE_injective_saturated_inter (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (_h : Good K s LL) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (_hI : IoW I) :
    Function.Injective I.ioE ∧ (∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x) ∧
      (∀ (x : R.EE) (y : RW LL), I.ioE x = ((l : ℕ) : RW LL) * y → ∃ x', x = ((l : ℕ) : R.EE) * x') ∧
      ∀ x : R.EE, (∃ y, inclR LL y = I.ioE x) →
        ∃ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), algebraMap _ R.EE a = x := by
  classical
  obtain ⟨_, hc, hl0, hlu, hfree, -, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨hWc, hWtf, -, hsat, hμ⟩ := GlobalTheory.HWL.TensorWitt.main l LL
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  haveI : NeZero (Module.finrank ℚ_[l] (K0 K)) := ⟨Module.finrank_pos.ne'⟩
  haveI : Nontrivial (RW LL) := Module.FaithfullyFlat.lTensor_nontrivial ℤ_[l] ↥(OL LL) (WCb l)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    rcases N with _ | n
    · exact absurd (by simpa using hN) hlu
    · exact ⟨n, rfl⟩
  obtain ⟨u, hu⟩ := hN.symm
  have hm : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hO : ∀ a : ↥(OL LL), IsUnit a ∨ ϖ ∣ a := by
    intro a
    by_cases h : IsUnit a
    · exact Or.inl h
    · right
      rw [← Ideal.mem_span_singleton, ← hm]
      exact h
  have hOp : ∀ a : ℕ → ↥(OL LL), (∀ k k', k ≤ k' → (l : ↥(OL LL)) ^ k ∣ a k - a k') →
      ∃ L, ∀ k, (l : ↥(OL LL)) ^ k ∣ a k - L := by
    intro a ha
    have hiff : ∀ (k : ℕ) (x y : ↥(OL LL)),
        x ≡ y [SMOD (IsLocalRing.maximalIdeal ↥(OL LL) ^ k • ⊤ : Submodule ↥(OL LL) ↥(OL LL))] ↔ ϖ ^ k ∣ x - y := by
      intro k x y
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := a) (by
      intro k k' hk
      rw [hiff]
      refine (pow_dvd_pow_of_dvd ?_ k).trans (ha k k' hk)
      exact ⟨ϖ ^ n * u, by rw [← hu]; ring⟩)
    refine ⟨L, fun k => ?_⟩
    have h1 := (hiff _ _ _).mp (hL ((n + 1) * k))
    have h2 : (l : ↥(OL LL)) ^ k ∣ ϖ ^ ((n + 1) * k) := by
      rw [pow_mul]
      exact pow_dvd_pow_of_dvd hN.dvd k
    have : a k - L = (a k - a ((n + 1) * k)) + (a ((n + 1) * k) - L) := by ring
    rw [this]
    exact dvd_add (ha _ _ (by nlinarith)) (h2.trans h1)
  have hp := P.PD_p K
  have hE := R.EE_complete
  have hdense := R.EE_dense
  have hEsat := R.EE_sat
  rw [hp] at hE hdense hEsat
  refine abstract (algebraMap _ R.EE) I.ioE.toRingHom I.io.toRingHom (inclR LL).toRingHom I.ioE_ext l
    (fun _ => C ϖ) letπ (fun _ => C (u : ↥(OL LL))) n
    (Pi.isUnit_iff.mpr fun _ => u.isUnit.map C) ?_ (fun i => Pi.single i 1) ?_ ?_
    (letter_form ϖ hO) (prec_pi l hOp) R.EE_π hE (fun x => hdense x 1) hEsat
    (IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self _)) hWtf hsat ?_ ?_
  · funext i
    have := congrArg (C : ↥(OL LL) →+* _) hu
    rw [map_natCast, map_mul, map_pow] at this
    simp only [Pi.natCast_apply, Pi.mul_apply, Pi.pow_apply, ← this]
    ring
  · intro i
    rw [← Pi.single_mul, mul_one]
  · exact Finset.univ_sum_single (1 : LetA ↥(OL LL) _)
  · haveI := hμ _ (not_isUnit_εroot_sub_one AI s)
    change I.io letπ ∈ _
    rw [I.io_π]
    exact IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self _)
  · exact idem_ne_zero (algebraMap _ R.EE) I.ioE.toRingHom R.φ₀ R.φE (φRW LL) (map_zero _) R.φE_ext I.ioE_φ

end GlobalTheory.IoInj
