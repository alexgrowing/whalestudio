import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallLocInShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsInCMFieldTwoPrimesDegreeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCosetsUnitIdelesCompletedOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitRepresentativesSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformiserSplitPlaceCmOrderNonunitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceUniformiserIdeleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorTimesSplitPrimesExponentsStatement

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology

namespace GlobalTheory.CMVal.Euler

variable {E : Type} [Field E] [NumberField E]

theorem summable_intI {c : Ideal (OF E)} (hc : c ≠ ⊥) {χ : HChar E} (hu : IsUnitary χ) {S : ℂ} (hS : 1 < S.re) :
    Summable (cs (hatOUnits c) (omega χ S) intI) := by
  classical
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_finite_cosets_unitIdeles_completedOrder E c hc
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_ideal_section_integralFiniteIdele_upToUnits E
  have hI := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow E).2 S.re hS).1
  have hP : Summable fun p : R × Ideal (𝓞 E) => (Ideal.absNorm p.2 : ℝ) ^ (-S.re) :=
    (summable_prod_of_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _).2 ⟨fun _ => hI, Summable.of_finite⟩
  let A : Set ((Af E)ˣ ⧸ hatOUnits c) := {z | z.out ∈ intI}
  choose J hJ hJ' using fun z : A => hg z.1.out z.2
  choose r hr hr' using fun z : A => hR _ (hJ' z)
  let f : A → R × Ideal (𝓞 E) := fun z => (⟨r z, hr z⟩, J z)
  have hf : Function.Injective f := by
    intro z z' h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h1' : r z = r z' := congrArg Subtype.val h1
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' z.1, ← QuotientGroup.out_eq' z'.1, QuotientGroup.eq]
    have := mul_mem (inv_mem (hr' z)) (hr' z')
    rw [← h1', ← h2] at this
    convert this using 1
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have h3 : Summable fun z : A => omega χ S z.1.out := by
    refine Summable.of_norm ((hP.comp_injective hf).congr fun z => ?_)
    rw [norm_omega hu, hJ z, Real.inv_rpow (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _)]
    rfl
  have h4 := (summable_subtype_iff_indicator (f := fun z : (Af E)ˣ ⧸ hatOUnits c => omega χ S z.out) (s := A)).1 h3
  refine h4.congr fun z => ?_
  simp only [cs, Set.indicator_apply, A, Set.mem_setOf_eq]

def FS (c : Ideal (OF E)) (χ : HChar E) (S : ℂ) (m : HeightOneSpectrum (OF E) → ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) : ℂ :=
  ∑' z, cs (hatOUnits c) (omega χ S) (MS m T) z

abbrev fib (v : HeightOneSpectrum (OF E)) : Finset (HeightOneSpectrum (𝓞 E)) :=
  Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v

section
variable {c : Ideal (OF E)} {χ : HChar E} {S : ℂ} (hω : ∀ u ∈ hatOUnits c, omega χ S u = 1)
  (hB : Summable (cs (hatOUnits c) (omega χ S) intI)) (hu : IsUnitary χ) (hS : 0 < S.re)
  {m : HeightOneSpectrum (OF E) → ℕ} (hm : ∀ v, m v ≤ expIn c v)

include hω hB hu hS hm in
open Classical in
theorem FS_union (T s : Finset (HeightOneSpectrum (𝓞 E))) (hs : ∀ w ∈ s, m (w.under (OF E)) = 0 ∧ w ∉ T ∧ UnrAt χ w) :
    FS c χ S m T = (∏ w ∈ s, eulerFactor χ S w) * FS c χ S m (s ∪ T) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert w s hw ih =>
    obtain ⟨h1, h2, h3⟩ := hs w (Finset.mem_insert_self _ _)
    have h4 := tsum_split hω hB (MS_subset m (s ∪ T)) (MS_anti m (Finset.subset_insert w _)) (stable_MS hm (s ∪ T)) (unifAt w)
      (unif_shift h1 (by simp [hw, h2]))
    have h5 : eulerFactor χ S w = (1 - omega χ S (unifAt w))⁻¹ := by rw [eulerFactor, if_pos h3, omega_unifAt]
    have h6 := one_sub_omega_ne hu hS w
    rw [ih fun w' hw' => hs w' (Finset.mem_insert_of_mem hw'), Finset.prod_insert hw, Finset.insert_union, h5]
    have h7 : FS c χ S m (insert w (s ∪ T)) = (1 - omega χ S (unifAt w)) * FS c χ S m (s ∪ T) := by
      unfold FS; linear_combination -h4
    rw [h7]; field_simp

include hω hm in
theorem FS_zero (T : Finset (HeightOneSpectrum (𝓞 E))) {v : HeightOneSpectrum (OF E)} {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (h : ¬ LevelLe χ P (m v)) : FS c χ S m T = 0 := by
  unfold Formalism.L2.Host.HChar.LevelLe at h
  push Not at h
  obtain ⟨x, hx1, hx2, hx3⟩ := h
  have hl : ∀ v', LocIn (m v') v' (single P x : Af E) := fun v' => locIn_of_sub_one fun P' hP' => by
    by_cases e : P' = P
    · subst e
      have : v' = v := by by_contra hne; exact not_over hP' hne hP
      rw [single_self, this]; exact hx2
    · rw [suppAt_single P x P' e]; simp
  refine tsum_zero_of hω (stable_MS hm T) (single P x) ?_ fun y => ?_
  · rw [omega_unit _ _ (val_single hx1), finPart_single]
    exact fun h => hx3 (Units.ext h)
  · rw [mul_comm]
    exact mul_mem_MS_iff (fun v' => (hl v').inv fun P' _ => val_single hx1 P') (val_inv_one (val_single hx1)) y

variable [IsCMField E]

include hω hB hm in
open Classical in
theorem FS_step (hF : TrivOnF χ) (T : Finset (HeightOneSpectrum (𝓞 E))) {v : HeightOneSpectrum (OF E)} (hv : Splits v) {k : ℕ}
    (hk : m v = k + 1) (hT : ∀ w ∈ T, ¬ Over w v) :
    FS c χ S m T = FS c χ S m (fib v ∪ T) +
      (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-S)) ^ 2 * FS c χ S (Function.update m v k) T := by
  obtain ⟨x, hx, hx'⟩ := GlobalTheory.T.exists_uniformiser_split_place_cm_order_nonunit E v hv
  obtain ⟨π, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_split_place_uniformiser_idele E v x hv hx
  have hm' : ∀ v', Function.update m v k v' ≤ expIn c v' := fun v' => by
    by_cases e : v' = v
    · subst e; rw [Function.update_self]; have := hm v'; omega
    · rw [Function.update_of_ne e]; exact hm v'
  have h5 : omega χ S π = (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-S)) ^ 2 := by
    rw [omega_apply, h4 χ hF, h3, sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      inv_natCast_cpow, sq, Units.val_one, one_mul]
  rw [← h5]
  refine tsum_split hω hB (MS_subset m T) (MS_anti m Finset.subset_union_right) (stable_MS hm' T) π fun y => ?_
  have hT' : (∀ w' ∈ T, Valued.v (((π⁻¹ * y : (Af E)ˣ) : Af E) w') = 1) ↔ ∀ w' ∈ T, Valued.v ((y : Af E) w') = 1 :=
    forall₂_congr fun w' hw' => by rw [shift_coord y (h2 w' (hT w' hw'))]
  simp only [MS, Set.mem_setOf_eq, Finset.forall_mem_union, mem_aboveF]
  rw [hT', forall_locIn_shift (m := m) (v := v) (fun _ e => Function.update_of_ne e _ _) h2, forall_locIn_iff m v,
    Function.update_self, hx' k π y h1, hk]
  tauto

include hω hB hm in
open Classical in
theorem FS_resid (T : Finset (HeightOneSpectrum (𝓞 E))) {v : HeightOneSpectrum (OF E)} (hv : Splits v)
    {P : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (hU : UnrAt χ P) (hk : m v = 1) (hT : ∀ w, Over w v → w ∈ T) :
    FS c χ S (Function.update m v 0) T = (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1) * FS c χ S m T := by
  obtain ⟨R, h1, h2, h3⟩ := GlobalTheory.T.exists_local_unit_representatives_split_prime E v P hv hP
  have h4 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1 = R.card := by rw [← h1]; push_cast; ring
  have key : ∀ r ∈ R, ∀ y : (Af E)ˣ, (single P r)⁻¹ * y ∈ MS m T ↔ LocIn 1 v (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) ∧
      (∀ v' ≠ v, LocIn (m v') v' (y : Af E)) ∧ ∀ w ∈ T, Valued.v ((y : Af E) w) = 1 := fun r hr y => by
    have hT' : (∀ w' ∈ T, Valued.v ((((single P r)⁻¹ * y : (Af E)ˣ) : Af E) w') = 1) ↔
        ∀ w' ∈ T, Valued.v ((y : Af E) w') = 1 :=
      forall₂_congr fun w' _ => by rw [Units.val_mul, mul_coord, map_mul, val_inv_one (val_single (h2 r hr)), one_mul]
    simp only [MS, Set.mem_setOf_eq]
    rw [hT', forall_locIn_shift (m := m) (v := v) (fun _ _ => rfl) (single_off hP r), hk, and_assoc]
  have key2 : ∀ y : (Af E)ˣ, y ∈ MS (Function.update m v 0) T ↔
      (∀ v' ≠ v, LocIn (m v') v' (y : Af E)) ∧ ∀ w ∈ T, Valued.v ((y : Af E) w) = 1 := fun y => by
    simp only [MS, Set.mem_setOf_eq]
    rw [forall_locIn_iff _ v, Function.update_self, locIn_zero_iff]
    refine ⟨fun h => ⟨fun v' e => by simpa [Function.update_of_ne e] using h.1.2 v' e, h.2⟩,
      fun h => ⟨⟨fun w hw => (h.2 w (hT w hw)).le, fun v' e => by simpa [Function.update_of_ne e] using h.1 v' e⟩, h.2⟩⟩
  rw [h4]
  refine tsum_fin hω hB (MS_subset _ T) (stable_MS hm T) R (single P) (fun r hr => ?_) (fun y hy => ?_) (fun r hr y hy => ?_)
  · rw [omega_unit _ _ (val_single (h2 r hr)), finPart_single, hU r (h2 r hr), Units.val_one]
  · have hy' := (key2 y).1 hy
    refine (existsUnique_congr fun r => and_congr_right fun hr => ?_).2 (h3 y fun w hw => hy'.2 w (hT w hw))
    rw [key r hr]; exact and_iff_left hy'
  · exact (key2 y).2 ((key r hr y).1 hy).2

end

section
variable {c : Ideal (OF E)} {χ : HChar E} {S : ℂ} (hω : ∀ u ∈ hatOUnits c, omega χ S u = 1)
  (hB : Summable (cs (hatOUnits c) (omega χ S) intI)) (hu : IsUnitary χ) (hS : 0 < S.re)
  {m : HeightOneSpectrum (OF E) → ℕ} (hm : ∀ v, m v ≤ expIn c v) [IsCMField E]

include hm in
open Classical in
theorem update_le (v : HeightOneSpectrum (OF E)) {k : ℕ} (hk : m v = k + 1) (v' : HeightOneSpectrum (OF E)) :
    Function.update m v k v' ≤ expIn c v' := by
  by_cases e : v' = v
  · subst e; rw [Function.update_self]; have := hm v'; omega
  · rw [Function.update_of_ne e]; exact hm v'

include hω hB hm in
open Classical in

theorem FS_ram (hF : TrivOnF χ) (T : Finset (HeightOneSpectrum (𝓞 E))) {v : HeightOneSpectrum (OF E)} (hv : Splits v) {k : ℕ}
    (hk : m v = k + 1) (hT : ∀ w ∈ T, ¬ Over w v) {P : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (h : ¬ LevelLe χ P k)
    (hr : ∀ w, Over w v → ¬ UnrAt χ w) :
    FS c χ S m T = (∏ w ∈ fib v, eulerFactor χ S w) * FS c χ S m (fib v ∪ T) := by
  rw [FS_step hω hB hm hF T hv hk hT, FS_zero hω (update_le hm v hk) T hP (by rwa [Function.update_self]),
    Finset.prod_eq_one fun w hw => by rw [eulerFactor, if_neg (hr w ((mem_aboveF w v).1 hw))]]
  ring

def eFactor (χ : HChar E) (S : ℂ) (q : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)) : ℂ :=
  (1 - (val χ P : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) * (1 - (val χ P : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) +
    ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) ^ 2

include hω hB hu hS hm in
open Classical in

theorem FS_unr (hF : TrivOnF χ) (T : Finset (HeightOneSpectrum (𝓞 E))) {v : HeightOneSpectrum (OF E)} (hv : Splits v)
    (hk : m v = 1) (hT : ∀ w ∈ T, ¬ Over w v) {P : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (h : UnrAt χ P)
    (hl : ∀ w, Over w v → LevelLe χ w 1) :
    FS c χ S m T = eFactor χ S v P * (∏ w ∈ fib v, eulerFactor χ S w) * FS c χ S m (fib v ∪ T) := by
  obtain ⟨P', hP', hne⟩ : ∃ P', Over P' v ∧ P ≠ P' := by
    obtain ⟨A, B, hAB, hA, hB⟩ := hv
    by_cases e : P = A
    · exact ⟨B, hB, e ▸ hAB⟩
    · exact ⟨A, hA, e⟩
  obtain ⟨s1, s2⟩ := GlobalTheory.T.splitsInCMField_two_primes_degree_one E v hv
  obtain ⟨h', hval⟩ := GlobalTheory.T.heckeChar_unramified_inverse_split_pair E χ v P P' hF hv hP hP' hne (hl P' hP') h
  have hfib : fib v = {P, P'} := by
    ext w
    rw [mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨s1 P P' hP hP' hne w, by rintro (rfl | rfl) <;> assumption⟩
  have h1 := FS_union hω hB hu hS (update_le hm v hk) T (fib v) fun w hw => by
    have hw' := (mem_aboveF w v).1 hw
    refine ⟨by rw [(over_iff_under _ _).1 hw', Function.update_self], fun e => hT w e hw', ?_⟩
    rcases s1 P P' hP hP' hne w hw' with rfl | rfl <;> assumption
  have h2 := FS_resid hω hB hm (fib v ∪ T) hv hP h hk fun w hw => Finset.mem_union_left _ ((mem_aboveF w v).2 hw)
  have e1 := one_sub_omega_ne hu hS P
  have e2 := one_sub_omega_ne hu hS P'
  rw [omega_unifAt, (s2 P hP).1] at e1
  rw [omega_unifAt, (s2 P' hP').1, hval, Units.val_inv_eq_inv_val] at e2
  rw [FS_step hω hB hm hF T hv hk hT, h1, h2]
  conv => enter [1, 2, 2, 1]; rw [hfib]
  conv => enter [2, 1, 2]; rw [hfib]
  rw [Finset.prod_pair hne, eulerFactor, eulerFactor, if_pos h, if_pos h', (s2 P hP).1, (s2 P' hP').1, hval,
    Units.val_inv_eq_inv_val, eFactor]
  generalize (1 - (val χ P : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-S)) = a at *
  generalize (1 - (val χ P : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-S)) = b at *
  field_simp

end

open Classical in

theorem hasSum_euler : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (S L : ℂ), UnramFin E → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → 1 < S.re → HasProd (eulerFactor χ S) L → open Classical in HasSum (fun z : {z : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q) // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q)) = z ∧ (y : Af E) ∈ hatO (condQ 𝔣 Q)} => (finPart χ z.1.out : ℂ) * ((modF z.1.out : ℝ) : ℂ) ^ S) (L * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), ((1 - (val χ (Pq q) : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) * (1 - (val χ (Pq q) : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) + ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) ^ 2)) := by
  intro E _ _ _ I _ φ hφ s κ 𝔣 Q χ Pq S L hE h𝔣 hQ hχ hPq hS hL
  obtain ⟨hc0, hsp, hdv, hnQ, hnQ', hfin⟩ := GlobalTheory.T.conductorTimesSplitPrimes_exponents E 𝔣 Q h𝔣 hQ
  set c := condQ 𝔣 Q with hc
  have hu := hχ.1
  have hF := hχ.2.1
  have hS0 : 0 < S.re := by linarith
  have hω : ∀ u ∈ hatOUnits c, omega χ S u = 1 := fun u hu => by
    rw [omega_unit _ _ (OrderUnits.val_eq_one hu),
      OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ u hu, Units.val_one]
  have hB := summable_intI hc0 hu hS
  have hm : ∀ v, expIn c v ≤ expIn c v := fun _ => le_rfl
  let e : HeightOneSpectrum (OF E) → ℂ := fun v => if v ∈ Q.filter (fun q => UnrAt χ (Pq q)) then eFactor χ S v (Pq v) else 1

  have hstep : ∀ v, expIn c v ≠ 0 → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ¬ Over w v) →
      FS c χ S (expIn c) T = e v * (∏ w ∈ fib v, eulerFactor χ S w) * FS c χ S (expIn c) (fib v ∪ T) := by
    intro v hv T hT
    have hs := hsp v (hdv v hv)
    by_cases hvQ : v ∈ Q
    · have hl : ∀ w, Over w v → LevelLe χ w 1 := fun w hw => (hχ.2.2.2 v w hw).1 hvQ
      by_cases hU : UnrAt χ (Pq v)
      · rw [FS_unr hω hB hu hS0 hm hF T hs (hnQ v hvQ) hT (hPq v hvQ) hU hl]
        simp [e, hvQ, hU]
      · rw [FS_ram hω hB hm hF T hs (k := 0) (hnQ v hvQ) hT (hPq v hvQ) (fun h => hU ((χ.unrAt_iff _).2 h)) fun w hw h => hU ?_]
        · simp [e, hU]
        · by_cases a : w = Pq v
          · exact a ▸ h
          · exact (GlobalTheory.T.heckeChar_unramified_inverse_split_pair E χ v w (Pq v) hF hs hw (hPq v hvQ) a (hl _ (hPq v hvQ)) h).1
    · have hl : ∀ w, Over w v → ExpAt χ w (expIn c v) := fun w hw => by
        rw [hnQ' v hvQ]; exact (hχ.2.2.2 v w hw).2 hvQ
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hv
      obtain ⟨P, -, -, hP, -⟩ := id hs
      rw [FS_ram hω hB hm hF T hs hk hT hP (fun h => by have := (hl P hP k).1 h; omega) fun w hw => (hl w hw).not_unrAt hv]
      simp [e, hvQ]

  have hV : ∀ V : Finset (HeightOneSpectrum (OF E)), (∀ v ∈ V, expIn c v ≠ 0) →
      FS c χ S (expIn c) ∅ = (∏ v ∈ V, e v) * (∏ w ∈ V.biUnion fib, eulerFactor χ S w) *
        FS c χ S (expIn c) (V.biUnion fib) := by
    intro V
    induction V using Finset.induction_on with
    | empty => simp
    | insert v V hv ih =>
      intro h
      have hT : ∀ w ∈ V.biUnion fib, ¬ Over w v := fun w hw => by
        obtain ⟨v', h1, h2⟩ := Finset.mem_biUnion.1 hw
        exact not_over ((mem_aboveF w v').1 h2) fun a => hv (a ▸ h1)
      rw [ih fun v' hv' => h v' (Finset.mem_insert_of_mem hv'), hstep v (h v (Finset.mem_insert_self _ _)) _ hT,
        Finset.biUnion_insert, Finset.prod_insert hv,
        Finset.prod_union (Finset.disjoint_right.2 fun w hw hw' => hT w hw ((mem_aboveF w v).1 hw'))]
      ring
  have he : ∏ v ∈ hfin.toFinset, e v = ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), eFactor χ S q (Pq q) := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.2]
    intro v hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hnQ v (Finset.mem_filter.1 hv).1]
    exact one_ne_zero
  have h0 := hV hfin.toFinset fun v hv => hfin.mem_toFinset.1 hv
  rw [he] at h0
  set T₀ := hfin.toFinset.biUnion fib with hT₀
  set e₀ := ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), eFactor χ S q (Pq q) with he₀

  have h1 : ∀ T, T₀ ⊆ T → FS c χ S (expIn c) ∅ = (∏ w ∈ T, eulerFactor χ S w) * e₀ * FS c χ S (expIn c) T := by
    intro T hT
    rw [h0, FS_union hω hB hu hS0 hm T₀ (T \ T₀), Finset.sdiff_union_of_subset hT, ← Finset.prod_sdiff hT]
    · ring
    intro w hw
    have hw' := (Finset.mem_sdiff.1 hw).2
    have h2 : expIn c (w.under (OF E)) = 0 := by
      by_contra a
      exact hw' (Finset.mem_biUnion.2 ⟨_, hfin.mem_toFinset.2 a, (mem_aboveF _ _).2 (over_under w)⟩)
    have h3 : w.under (OF E) ∉ Q := fun a => by rw [hnQ _ a] at h2; exact one_ne_zero h2
    refine ⟨h2, hw', (expAt_zero_iff χ w).1 ?_⟩
    rw [← h2, hnQ' _ h3]
    exact (hχ.2.2.2 _ w (over_under w)).2 h3

  have hO : ∀ z : Af E, z ∈ hatO c ↔ ∀ v, LocIn (expIn c v) v z :=
    fun z => ⟨locIn_of_mem_hatO, GlobalTheory.T.mem_completedOrder_of_local_congruence_split E c hc0 hsp z⟩
  have h2 : Tendsto (fun T => FS c χ S (expIn c) T) atTop (𝓝 1) := by
    refine tendsto_tsum_one hω hB atTop _ (MS_subset _) (fun y hy T => ⟨(hO _).1 hy.1, fun w _ => OrderUnits.val_eq_one hy w⟩)
      fun y hy => ?_
    by_cases a : ∀ w, Valued.v ((y : Af E) w) = 1
    · exact Eventually.of_forall fun T hT => hy ⟨(hO _).2 hT.1, (hO _).2 fun v => (hT.1 v).inv fun w _ => a w⟩
    · obtain ⟨w, hw⟩ := not_forall.1 a
      filter_upwards [eventually_ge_atTop {w}] with T hT hy'
      exact hw (hy'.2 w (hT (Finset.mem_singleton_self w)))
  have h3 : FS c χ S (expIn c) ∅ = L * e₀ := by
    have h4 : Tendsto (fun T => (∏ w ∈ T, eulerFactor χ S w) * e₀ * FS c χ S (expIn c) T) atTop (𝓝 (L * e₀ * 1)) :=
      (Tendsto.mul_const e₀ hL).mul h2
    rw [mul_one] at h4
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h4
    filter_upwards [eventually_ge_atTop T₀] with T hT using h1 T hT
  have h5 := hasSum_classes (stable_MS hm ∅) (summable_mono hB (MS_subset _ _))
  have h6 : MS (expIn c) ∅ = {y : (Af E)ˣ | (y : Af E) ∈ hatO c} := by
    ext y
    simp [MS, hO]
  unfold FS at h3
  rw [h3, h6] at h5
  exact h5

end GlobalTheory.CMVal.Euler
