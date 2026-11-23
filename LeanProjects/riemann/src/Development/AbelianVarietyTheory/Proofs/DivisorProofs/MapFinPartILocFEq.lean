import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.AlphaSplit

open Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.KDVal GlobalTheory.Mem.Col2.SplitChar

variable {D : D7}

def mulU {N₁ N₂ : ℕ} (N : ℕ) (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (hN : Even ((N₁ : ℤ) + N₂ - N)) : HeckeU D N where
  f := χ₁.f * χ₂.f
  n := χ₁.n + χ₂.n
  unitary x := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, χ₁.unitary, χ₂.unitary, mul_one]
  cont := by
    obtain ⟨m₁, hm₁, h₁⟩ := χ₁.cont
    obtain ⟨m₂, hm₂, h₂⟩ := χ₂.cont
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun u hu ⟨s, hs, e⟩ => ?_⟩
    rw [Nat.cast_mul] at e
    rw [MonoidHom.mul_apply, h₁ u hu ⟨m₂ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; ring⟩,
      h₂ u hu ⟨m₁ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; ring⟩, one_mul]
  aut a := by
    have h1 := χ₁.aut a
    have h2 := χ₂.aut a
    have hne : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ≠ 0 := fun τ => by
      have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
      exact div_ne_zero h (by simpa using h)
    rw [MonoidHom.mul_apply, Units.val_mul]
    simp only [Pi.add_apply, zpow_add₀ (hne _), Finset.prod_mul_distrib]
    calc _ = (((χ₁.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₁.n τ)) *
        (((χ₂.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₂.n τ)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  norm x := by rw [MonoidHom.mul_apply, χ₁.norm, χ₂.norm, one_mul]
  par τ := by
    have e : (χ₁.n + χ₂.n) τ - (N : ℤ) = (χ₁.n τ - N₁) + (χ₂.n τ - N₂) + ((N₁ : ℤ) + N₂ - N) := by
      simp only [Pi.add_apply]; ring
    rw [e]
    exact ((χ₁.par τ).add (χ₂.par τ)).add hN
  unr u hu hz := by rw [MonoidHom.mul_apply, χ₁.unr u hu hz, χ₂.unr u hu hz, one_mul]

theorem mulU_f {N₁ N₂ : ℕ} (N : ℕ) (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (hN : Even ((N₁ : ℤ) + N₂ - N)) (x : (AE D)ˣ) :
    (mulU N χ₁ χ₂ hN).f x = χ₁.f x * χ₂.f x := rfl

theorem eq_one_of_unr {χ : HChar D.host.E} (hχ : ∀ v, χ.UnrAt v) {u : (AE D)ˣ} (hu : IntU D u) :
    χ.1 (finIdl D u) = 1 := by
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu) (fun w => ?_) fun v x hx => ?_
  · exact congrFun (finIdl_fst D u) w
  · have hxu : IsUnitAt v x := by
      unfold IsUnitAt
      rw [hx]
      exact finIdl_unit hu v
    exact hχ v x hxu

end GlobalTheory.AlphaSplit

noncomputable section

namespace GlobalTheory.AlphaSplit

open Neutral.B1 Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.KDVal GlobalTheory.Mem.Col2.SplitChar

variable {D : D7}

theorem map_finPartI_locF_eq (χ : HChar D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (k : D.host.Fˣ) :
    χ.1 (finPartI D.host.E (locF (L := D.host.E) D.host.F v k)) = χ.resFin v k := by
  unfold HChar.resFin
  rw [MonoidHom.finsetProd_apply]
  unfold locF
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (GlobalTheory.Mem.KerDet.finPartI_localIdele Q _)

theorem even_log_norm (z : (AE D)ˣ) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ConjPl D.host.conj.toRingEquiv w w) : Even (WithZero.log (valAt w (finIdl D (z * sgU D z)))) := by
  have e : valAt w (finIdl D (z * sgU D z)) = vl D w (z : AE D) * vl D w (z : AE D) := by
    change vl D w ((z : AE D) * sgA D z) = _
    rw [map_mul, vl_sgA hw]
  have h0 : vl D w (z : AE D) ≠ 0 := valAt_ne_zero w (finIdl D z)
  rw [e, WithZero.log_mul h0 h0]
  exact ⟨_, rfl⟩

theorem eta_norm {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) (z : (AE D)ˣ) :
    χ.1 (finIdl D (z * sgU D z)) = 1 := by
  classical
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have ec : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
  set a := finIdl D (z * sgU D z) with ha_def
  have ha : a ∈ balanced (L := D.host.E) D.host.F := norm_balanced z
  let T : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 D.host.F)
  let m : HeightOneSpectrum (𝓞 D.host.F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Ideles D.host.E := ∏ v ∈ T, locF (L := D.host.E) D.host.F v (unif v) ^ m v
  have hm : ∀ w : HeightOneSpectrum (𝓞 D.host.E), m (w.under (𝓞 D.host.F)) = -WithZero.log (valAt w a) := fun w => by
    have hex : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := ⟨w, rfl⟩
    simp only [m]
    rw [dif_pos hex, ha w hex.choose hex.choose_spec]
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 D.host.F) → valAt w (locF (L := D.host.E) D.host.F v (unif v) ^ m v) = 1 :=
      fun v hv => by rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 D.host.F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        ordF_unif_self, ← WithZero.exp_zsmul, hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hunit : b⁻¹ * a ∈ unitIdl D.host.E := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)
  have hfac : ∀ v, χ.1 (finPartI D.host.E (locF (L := D.host.E) D.host.F v (unif v) ^ m v)) = 1 := fun v => by
    rw [map_zpow, map_zpow, map_finPartI_locF_eq, hχ.res.1 v, etaFin]
    split_ifs with h1
    · have hev : Even (m v) := by
        simp only [m]
        split_ifs with hex
        · set w := hex.choose
          have hwv : w.under (𝓞 D.host.F) = v := hex.choose_spec
          obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
          have hu' : w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) :=
            (under_eq_iff_conjPl c hcm.rank hcm.ne w w').2 (Or.inr (by rw [ec]; exact hw'))
          obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
          have m1 : w ∈ aboveF (L := D.host.E) D.host.F v := by simp [aboveF, hwv]
          have m2 : w' ∈ aboveF (L := D.host.E) D.host.F v := by simp [aboveF, hu', hwv]
          rw [hx, Finset.mem_singleton] at m1 m2
          have e : w' = w := m2.trans m1.symm
          rw [e] at hw'
          exact (even_log_norm z w hw').neg
        · exact ⟨0, by simp⟩
      rw [← zpow_mul, mul_comm, zpow_mul, hev.neg_one_zpow, one_zpow]
    · exact one_zpow _
  have hb : χ.1 (finPartI D.host.E b) = 1 := by
    simp only [b]
    rw [map_prod, map_prod]
    exact Finset.prod_eq_one fun v _ => hfac v
  have hr : χ.1 (finPartI D.host.E (b⁻¹ * a)) = 1 := by
    refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 hunit) (fun _ => rfl)
      fun v x hx => ?_
    have hx' : (x : v.adicCompletion D.host.E) = ((b⁻¹ * a : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v := hx
    have hxu : IsUnitAt v x := by
      unfold IsUnitAt
      rw [hx']
      exact hunit v
    exact hχ.unr v x hxu
  have key : a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
  have e1 : χ.1 a = χ.1 (finPartI D.host.E a) := by rw [ha_def, finPartI_finIdl]
  rw [e1, key, map_mul, map_mul, hb, hr, one_mul]

end GlobalTheory.AlphaSplit

noncomputable section

namespace GlobalTheory.AlphaSplit

variable {D : D7}

def invU {N : ℕ} (χ : HeckeU D N) : HeckeU D N where
  f := χ.f⁻¹
  n := -χ.n
  unitary x := by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, χ.unitary, inv_one]
  cont := by
    obtain ⟨m, hm, h⟩ := χ.cont
    exact ⟨m, hm, fun u hu hs => by rw [MonoidHom.inv_apply, h u hu hs, inv_one]⟩
  aut a := by
    have h1 := χ.aut a
    have hne : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ≠ 0 := fun τ => by
      have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
      exact div_ne_zero h (by simpa using h)
    have hf : ((χ.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    simp only [Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
    rw [← mul_inv, h1, inv_one]
  norm x := by rw [MonoidHom.inv_apply, χ.norm, inv_one]
  par τ := by
    have e : (-χ.n) τ - (N : ℤ) = -(χ.n τ - N) - 2 * N := by simp only [Pi.neg_apply]; ring
    rw [e]
    exact (χ.par τ).neg.sub (even_two_mul _)
  unr u hu hz := by rw [MonoidHom.inv_apply, χ.unr u hu hz, inv_one]

theorem invU_f {N : ℕ} (χ : HeckeU D N) (x : (AE D)ˣ) : (invU χ).f x = (χ.f x)⁻¹ := rfl

end GlobalTheory.AlphaSplit

noncomputable section

namespace GlobalTheory.AlphaSplit

open Neutral.B1 Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.SplitChar

variable {D : D7}

def etaU {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) : HeckeU D 1 where
  f := χ.1.comp (finIdl D)
  n := fun _ => 1
  unitary := fun _ => hχ.unitary _
  cont := ⟨1, one_pos, fun _ hu _ => eq_one_of_unr hχ.unr hu⟩
  aut := fun a => by
    have h1 := χ.2.2 a
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU, mul_comm] at h1
    have h2 := hχ.inf a
    rw [← D.eTau.prod_comp] at h2
    have h3 := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one] at h3
    rw [← h3]
    exact congrArg _ h2.symm
  norm := eta_norm hχ
  par := fun _ => by simp
  unr := fun _ hu _ => eq_one_of_unr hχ.unr hu

theorem etaU_f {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) (x : (AE D)ˣ) : (etaU hχ).f x = χ.1 (finIdl D x) := rfl

end GlobalTheory.AlphaSplit
