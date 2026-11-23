import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresMono
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem nat_le_one' {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

private theorem dd_mul_eq_dd_mul_add_mul_dd {R : Type} [CommRing R] (f g : PowerSeries R) :
    dd (f * g) = dd f * g + f * dd g := by
  simp [dd]; ring

private theorem dl_mul_eq_add_of_isUnit {R : Type} [CommRing R] {f g : PowerSeries R}
    (hf : IsUnit f) (hg : IsUnit g) : dl (f * g) = dl f + dl g := by
  obtain ⟨u, rfl⟩ := hf
  obtain ⟨v, rfl⟩ := hg
  simp only [dl, ← Units.val_mul, Ring.inverse_unit]
  simp only [Units.val_mul, mul_inv_rev, dd_mul_eq_dd_mul_add_mul_dd]
  have h1 : (u : PowerSeries R) * ↑u⁻¹ = 1 := u.mul_inv
  have h2 : (v : PowerSeries R) * ↑v⁻¹ = 1 := v.mul_inv
  linear_combination (dd (u : PowerSeries R) * ↑u⁻¹) * h2 + (dd (v : PowerSeries R) * ↑v⁻¹) * h1

theorem UpperTheory.Kd.C7.pRepAdd :
    UpperTheory.Kd.C7.SRepAdd := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ
  have hB := (pBasEx l c).2 β
  have hpv : ∀ (P Q : Polynomial (R0 A)) (z : Ω), pv (P * Q) z = pv P z * pv Q z := by
    intro P Q z; simp [pv, Polynomial.eval₂_mul]
  refine ⟨?_, ?_⟩
  · rintro Z Z' D D' ⟨c₁, m₁, h₁⟩ ⟨c₂, m₂, h₂⟩
    refine ⟨max c₁ c₂, max (max m₁ m₂) 1, fun m hm => ?_⟩
    have hm₁ : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
    have hm₂ : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
    have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hc₁ : m - max c₁ c₂ ≤ m - c₁ := Nat.sub_le_sub_left (le_max_left _ _) m
    have hc₂ : m - max c₁ c₂ ≤ m - c₂ := Nat.sub_le_sub_left (le_max_right _ _) m
    obtain ⟨P, hP, hPL⟩ := h₁ m hm₁
    obtain ⟨P', hP', hPL'⟩ := h₂ m hm₂
    have hQ := pPresMono l hl Ω A hA c β ζ hζ Z Z m (m - c₁) (m - max c₁ c₂) P hc₁
      (fun s _ => by simp [Cg]) hP
    have hQ' := pPresMono l hl Ω A hA c β ζ hζ Z' Z' m (m - c₂) (m - max c₁ c₂) P' hc₂
      (fun s _ => by simp [Cg]) hP'
    unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres at hQ hQ'
    obtain ⟨hprim, hnr, hu, ho, hk⟩ := hQ
    obtain ⟨-, -, hu', -, hk'⟩ := hQ'
    refine ⟨fun i => P i * P' i, ?_, fun i => ?_⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨hprim, hnr, fun i => ?_, ho, fun s hs hcyc hsζ => ?_⟩
      · dsimp only
        rw [hpv]
        obtain ⟨a₁, a₂, a₃⟩ := hu i
        obtain ⟨b₁, b₂, b₃⟩ := hu' i
        dsimp only at a₁ a₂ a₃ b₁ b₂ b₃
        exact ⟨mul_mem a₁ b₁, mul_ne_zero a₂ b₂, by rw [mul_inv]; exact mul_mem a₃ b₃⟩
      · obtain ⟨k, hkv, hkc⟩ := hk s hs hcyc hsζ
        obtain ⟨k', hkv', hkc'⟩ := hk' s hs hcyc hsζ
        have hsH : s ∈ Hm l A m := Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩
        have halg := (pKumAlg l hl Ω A hA ζ hζ m (m - max c₁ c₂) (Nat.sub_le _ _) s hsH).1
        refine ⟨k + k', fun i => ?_, ?_⟩
        · dsimp only
          rw [hpv]
          exact (halg _ _ _ _ (hkv i) (hkv' i)).1
        · have hNz : NeZero (l ^ (m - max c₁ c₂)) :=
            ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
          have key : ∀ i, (((k + k') i).val : Qbar l) = (k i).val + (k' i).val
              - (l : Qbar l) ^ (m - max c₁ c₂)
                * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l) := by
            intro i
            rw [Pi.add_apply, ZMod.val_add, eq_sub_iff_add_eq]
            exact_mod_cast Nat.mod_add_div ((k i).val + (k' i).val) (l ^ (m - max c₁ c₂))
          unfold Cg at hkc hkc' ⊢
          dsimp only
          have hsplit : Z m s 1 + Z' m s 1 - ∑ i, β.val i * (((k + k') i).val : Qbar l)
              = (Z m s 1 - ∑ i, β.val i * ((k i).val : Qbar l))
                + (Z' m s 1 - ∑ i, β.val i * ((k' i).val : Qbar l))
                + ∑ i, β.val i * ((l : Qbar l) ^ (m - max c₁ c₂)
                  * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l)) := by
            simp only [key, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
            ring
          rw [hsplit]
          have hN : 0 ≤ ‖(l : Qbar l) ^ (m - max c₁ c₂)‖ := norm_nonneg _
          refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
            (max_le (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hkc hkc')) ?_)
          refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hN (fun i _ => ?_)
          rw [norm_mul, norm_mul]
          have h1 := ho i
          have h2 := nat_le_one' (l := l) (((k i).val + (k' i).val) / l ^ (m - max c₁ c₂))
          calc _ ≤ 1 * (‖(l : Qbar l) ^ (m - max c₁ c₂)‖ * 1) :=
                mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hN) (by positivity) zero_le_one
            _ = _ := by ring
    · have hU : IsUnit (Φ.ser (P i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P i)).2 (hu i)
      have hU' : IsUnit (Φ.ser (P' i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P' i)).2 (hu' i)
      have hs : Φ.ser (P i * P' i) = Φ.ser (P i) * Φ.ser (P' i) := by
        simp [Fr.ser, Polynomial.map_mul, Polynomial.eval₂_mul]
      have ht : Φ.tw m ((D + D') i) = Φ.tw m (D i) + Φ.tw m (D' i) := by
        simp [Fr.tw, map_add]
      have e₁ := hPL i
      have e₂ := hPL' i
      unfold LC at e₁ e₂ ⊢
      dsimp only
      rw [ht, hs, dl_mul_eq_add_of_isUnit hU hU', map_add, map_add]
      have f₁ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₁) e₁
      have f₂ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₂) e₂
      convert Ideal.add_mem _ f₁ f₂ using 1
      ring
  · intro Z hZ
    refine ⟨0, 0, fun m _ => ⟨fun _ => 1, ?_, fun i => ?_⟩⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨by simpa using (hζ m).1, by simp, fun i => by simp [pv], fun i => hB.1 i,
        fun s hs hcyc hsζ => ⟨0, fun i => ?_, ?_⟩⟩
      · unfold KumVal
        exact ⟨1, by simp [pv], by simp⟩
      · unfold Cg
        have hz := hZ m s (Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩)
        simp [hz]
    · unfold LC
      simp [Fr.tw, Fr.ser, dl, dd]
