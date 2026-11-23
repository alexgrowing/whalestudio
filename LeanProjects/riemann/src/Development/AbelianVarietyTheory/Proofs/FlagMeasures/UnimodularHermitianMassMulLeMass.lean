import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBoundsStatement
import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.MassRatioBound

lemma core_two (ms m : ℕ → ℝ) (D B Mb : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B) (hpos : ∀ n, 0 < ms n)
    (hrec : ∀ n, 2 ≤ n → ms (n + 1) = ms n * m (n + 1))
    (hlow : ∀ i, 3 ≤ i → 1 ≤ m i * D * B ^ i)
    (hcmp : ∀ i t, 3 ≤ i → 1 ≤ t → m i ≤ m (i + t) * B ^ t)
    (h2 : ms 2 ≤ Mb) (t : ℕ) (ht : 2 ≤ t) (s : ℕ) (hs : 2 ≤ s) :
    ms s * ms t ≤ ms (s + t) * (Mb * (D * D) * B ^ (s * (s + t))) := by
  have hMb : 0 < Mb := (hpos 2).trans_le h2
  have hB0 : 0 < B := by linarith
  have hD0 : 0 < D := by linarith
  have hm : ∀ n, 2 ≤ n → 0 < m (n + 1) := by
    intro n hn
    have := hpos (n + 1)
    rw [hrec n hn] at this
    exact (mul_pos_iff_of_pos_left (hpos n)).mp this
  induction s, hs using Nat.le_induction with
  | base =>
    have e : 2 + t = t + 1 + 1 := by omega
    have a1 := hlow (t + 1) (by omega)
    have a2 := hlow (t + 1 + 1) (by omega)
    have p1 := hm t ht
    have p2 := hm (t + 1) (by omega)
    have a3 : 1 ≤ (m (t + 1) * D * B ^ (t + 1)) * (m (t + 1 + 1) * D * B ^ (t + 1 + 1)) :=
      one_le_mul_of_one_le_of_one_le a1 a2
    have a4 : B ^ (t + 1) * B ^ (t + 1 + 1) ≤ B ^ (2 * (t + 1 + 1)) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hB (by omega)
    rw [e, hrec (t + 1) (by omega), hrec t ht]
    have pt := hpos t
    calc ms 2 * ms t ≤ Mb * ms t := by gcongr
      _ ≤ Mb * ms t * ((m (t + 1) * D * B ^ (t + 1)) * (m (t + 1 + 1) * D * B ^ (t + 1 + 1))) :=
        le_mul_of_one_le_right (by positivity) a3
      _ = ms t * m (t + 1) * m (t + 1 + 1) * (Mb * (D * D) * (B ^ (t + 1) * B ^ (t + 1 + 1))) := by
        ring
      _ ≤ _ := by gcongr
  | succ s hs ih =>
    have e : s + 1 + t = s + t + 1 := by omega
    have a1 := hcmp (s + 1) t (by omega) (by omega)
    have p1 := hm s hs
    have p2 := hm (s + t) (by omega)
    have p3 := hpos (s + t)
    have a4 : B ^ (s * (s + t)) * B ^ t ≤ B ^ ((s + 1) * (s + t + 1)) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hB (by nlinarith)
    rw [e] at a1
    rw [e, hrec s hs, hrec (s + t) (by omega)]
    calc ms s * m (s + 1) * ms t = (ms s * ms t) * m (s + 1) := by ring
      _ ≤ (ms (s + t) * (Mb * (D * D) * B ^ (s * (s + t)))) * (m (s + t + 1) * B ^ t) := by
        gcongr
      _ = ms (s + t) * m (s + t + 1) * (Mb * (D * D) * (B ^ (s * (s + t)) * B ^ t)) := by ring
      _ ≤ _ := by gcongr

lemma core_one (ms m : ℕ → ℝ) (D B Mb : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B) (hpos : ∀ n, 0 < ms n)
    (hrec : ∀ n, 2 ≤ n → ms (n + 1) = ms n * m (n + 1))
    (hlow : ∀ i, 3 ≤ i → 1 ≤ m i * D * B ^ i)
    (h1 : ms 1 ≤ Mb) (t : ℕ) (ht : 2 ≤ t) (e : ℕ) (he : t + 1 ≤ e) :
    ms 1 * ms t ≤ ms (t + 1) * (Mb * (D * D) * B ^ e) := by
  have hMb : 0 < Mb := (hpos 1).trans_le h1
  have hB0 : 0 < B := by linarith
  have hD0 : 0 < D := by linarith
  have p1 : 0 < m (t + 1) := by
    have := hpos (t + 1)
    rw [hrec t ht] at this
    exact (mul_pos_iff_of_pos_left (hpos t)).mp this
  have a1 := hlow (t + 1) (by omega)
  have a4 : B ^ (t + 1) ≤ B ^ e := pow_le_pow_right₀ hB he
  have a5 : D ≤ D * D := le_mul_of_one_le_right hD0.le hD
  have pt := hpos t
  rw [hrec t ht]
  calc ms 1 * ms t ≤ Mb * ms t := by gcongr
    _ ≤ Mb * ms t * (m (t + 1) * D * B ^ (t + 1)) := le_mul_of_one_le_right (by positivity) a1
    _ = ms t * m (t + 1) * (Mb * D * B ^ (t + 1)) := by ring
    _ ≤ _ := by gcongr

lemma core (ms m : ℕ → ℝ) (D B Mb : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B) (hpos : ∀ n, 0 < ms n)
    (hrec : ∀ n, 2 ≤ n → ms (n + 1) = ms n * m (n + 1))
    (hlow : ∀ i, 3 ≤ i → 1 ≤ m i * D * B ^ i)
    (hcmp : ∀ i t, 3 ≤ i → 1 ≤ t → m i ≤ m (i + t) * B ^ t)
    (h1 : ms 1 ≤ Mb) (h2 : ms 2 ≤ Mb) (k s : ℕ) (hk : 3 ≤ k) (hs : 1 ≤ s) (hsk : s < k) :
    ms s * ms (k - s) ≤ ms k * (Mb * (D * D) * B ^ (s * k)) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = s + t := ⟨k - s, by omega⟩
  rw [Nat.add_sub_cancel_left]
  by_cases hs1 : s = 1
  · subst hs1
    rw [add_comm 1 t]
    exact core_one ms m D B Mb hD hB hpos hrec hlow h1 t (by omega) _ (by omega)
  by_cases ht1 : t = 1
  · subst ht1
    rw [mul_comm (ms s)]
    exact core_one ms m D B Mb hD hB hpos hrec hlow h1 s (by omega) _ (by nlinarith)
  exact core_two ms m D B Mb hD hB hpos hrec hlow hcmp h2 t (by omega) s (by omega)

lemma low_base (v : ℝ) (hv : 1 ≤ v) (i : ℕ) (hi : 1 ≤ i) :
    2 ≤ ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i * 16 ^ i := by
  have hf : (1 : ℝ) ≤ ((Nat.factorial (i - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hp := Real.pi_pos
  have h4 := Real.pi_le_four
  have h : 2 ≤ v / Real.pi * 16 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]; linarith
  have h' : (2 : ℝ) ≤ (v / Real.pi * 16) ^ i :=
    h.trans (le_self_pow₀ (by linarith) (by omega))
  rw [mul_assoc, ← mul_pow]
  nlinarith

lemma cmp_base (v : ℝ) (hv : 1 ≤ v) (i t : ℕ) (ht : 1 ≤ t) :
    ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i * 4 ≤
      ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ (i + t) * 16 ^ t := by
  have hf : ((Nat.factorial (i - 1) : ℕ) : ℝ) ≤ ((Nat.factorial (i + t - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hp := Real.pi_pos
  have h4 := Real.pi_le_four
  have h : 4 ≤ v / Real.pi * 16 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]; linarith
  have h' : (4 : ℝ) ≤ (v / Real.pi * 16) ^ t :=
    h.trans (le_self_pow₀ (by linarith) (by omega))
  have hv0 : 0 < v := by linarith
  calc _ ≤ ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i * (v / Real.pi * 16) ^ t := by
        gcongr
    _ = _ := by rw [mul_pow, pow_add]; ring

theorem mass_mul_mass_le : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (k s : ℕ) (Mb : ℝ) (ms : ℕ → ℝ), 3 ≤ k → 1 ≤ s → s < k → (∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n) → ms 1 ≤ Mb → ms 2 ≤ Mb → 1 ≤ Mb → ms s * ms (k - s) ≤ ms k * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * k * (Formalism.HermitianLatticesTheory.fDeg K))) := by
  intro hS K _ _ _ hCM hv k s Mb ms hk hs hsk hms h1 h2 _
  have hstd : ∀ n, Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form K n)
      (Formalism.HermitianLatticesTheory.massTelescope_lat K n) = ms n := fun n =>
    hms n _ _ _ (Formalism.HermitianLatticesTheory.massTelescope_symm K n) (Formalism.HermitianLatticesTheory.massTelescope_ortho K n)
  have hL := GlobalTheory.T.lValEta_mem_Icc_two_pow_fDeg K hCM
  set v := Formalism.HermitianLatticesTheory.vInv K with hvdef
  set f := Formalism.HermitianLatticesTheory.fDeg K with hfdef
  have hX : (1 : ℝ) ≤ (2 * v) ^ f := one_le_pow₀ (by linarith)
  have hD : 1 ≤ Real.sqrt ((2 * v) ^ f) := Real.one_le_sqrt.mpr hX
  have hDD : Real.sqrt ((2 * v) ^ f) * Real.sqrt ((2 * v) ^ f) = (2 * v) ^ f :=
    Real.mul_self_sqrt (by linarith)
  have hv0 : 0 < v := by linarith
  have hp := Real.pi_pos
  have key := core ms (Formalism.HermitianLatticesTheory.massRatioRightSide K) (Real.sqrt ((2 * v) ^ f)) (16 ^ f) Mb hD
    (one_le_pow₀ (by norm_num))
    (fun n => hstd n ▸ Formalism.HermitianLatticesTheory.massTelescope_std_pos K hCM n)
    (fun n hn => by
      rw [← hstd, ← hstd]; exact Formalism.HermitianLatticesTheory.massTelescope_step K hS hCM n hn)
    ?_ ?_ h1 h2 k s hk hs hsk
  · rw [hDD, ← pow_mul, mul_comm f] at key
    exact key
  · intro i hi
    have a := pow_le_pow_left₀ (by norm_num) (low_base v hv i (by omega)) f
    have b := (hL i (by omega)).1
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [← hvdef, ← hfdef]
    set D := Real.sqrt ((2 * v) ^ f)
    have hD0 : 0 < D := by linarith
    set A := ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i
    have e : A ^ f / D * Formalism.HermitianLatticesTheory.lValEta K i * D * (16 ^ f) ^ i
        = (A * 16 ^ i) ^ f * Formalism.HermitianLatticesTheory.lValEta K i := by
      rw [mul_pow A, ← pow_mul, ← pow_mul, mul_comm f i]; field_simp
    rw [e]
    calc (1 : ℝ) = 2 ^ f * (2 ^ f)⁻¹ := by field_simp
      _ ≤ _ := by
        refine mul_le_mul a b (by positivity) (le_trans (by positivity) a)
  · intro i t hi ht
    have a := pow_le_pow_left₀ (by positivity) (cmp_base v hv i t ht) f
    have b := (hL i (by omega)).2
    have c := (hL (i + t) (by omega)).1
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [← hvdef, ← hfdef]
    set D := Real.sqrt ((2 * v) ^ f)
    have hD0 : 0 < D := by linarith
    have hA : 0 ≤ ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i := by positivity
    have hA' : 0 ≤ ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ (i + t) := by positivity
    set A := ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i
    set A' := ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ (i + t)
    have e4 : (4 : ℝ) ^ f = 2 ^ f * 2 ^ f := by rw [← mul_pow]; norm_num
    calc A ^ f / D * Formalism.HermitianLatticesTheory.lValEta K i ≤ A ^ f / D * 2 ^ f := by gcongr
      _ = (A * 4) ^ f / D * (2 ^ f)⁻¹ := by rw [mul_pow A, e4]; field_simp
      _ ≤ (A' * 16 ^ t) ^ f / D * Formalism.HermitianLatticesTheory.lValEta K (i + t) := by gcongr
      _ = _ := by rw [mul_pow A', ← pow_mul, ← pow_mul, mul_comm f t]; ring

end GlobalTheory.MassRatioBound
