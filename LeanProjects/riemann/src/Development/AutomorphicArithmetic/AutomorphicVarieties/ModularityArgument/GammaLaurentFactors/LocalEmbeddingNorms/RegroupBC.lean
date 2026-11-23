import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOneSubBound

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ
open GroundTheory.Global.SemiLocal

namespace UpperTheory.V.Z.Gam

namespace BaseChangeLocalFactorRegrouping

private theorem one_period {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) :
    ∏ j ∈ Finset.range f, (1 - ζ ^ j * y) = 1 - y ^ f := by
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod h hf (rfl : y ^ f = y ^ f))
  rw [Polynomial.eval_prod] at h1
  simpa using h1.symm

private theorem periods {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) (g : ℕ) :
    ∏ j ∈ Finset.range (g * f), (1 - ζ ^ j * y) = (1 - y ^ f) ^ g := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Nat.succ_mul, Finset.prod_range_add, ih, pow_succ, ← one_period h hf y]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [pow_add, mul_comm g f, pow_mul, h.pow_eq_one, one_pow, one_mul]

private theorem fac_eq {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (g : ℕ) (B : Multiset ℂ) (x : ℂ) :
    ∏ j ∈ Finset.range (g * f), ((B.map (· * ζ ^ j)).map fun b => (1 - b * x)⁻¹).prod =
      (((B.map (· ^ f)).map fun b => (1 - b * x ^ f)⁻¹).prod) ^ g := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons a B ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [Finset.prod_mul_distrib, ih, mul_pow, Finset.prod_inv_distrib, ← mul_pow a x, inv_pow, ← periods h hf]
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

private theorem cast_pow_cpow (N f : ℕ) (z : ℂ) : (((N ^ f : ℕ)) : ℂ) ^ z = (((N : ℕ) : ℂ) ^ z) ^ f := by
  induction f with
  | zero => simp
  | succ f ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem norm_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm p.asIdeal ^ fdeg w :=
  Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.1.asIdeal p.asIdeal p.isPrime p.ne_bot

private theorem under_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) : w.1.under (𝓞 K) = p := by
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact w.2.over.symm

private theorem nonempty_over (p : HeightOneSpectrum (𝓞 K)) : Nonempty (PlacesOver L p) := by
  haveI := p.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p.asIdeal
  exact ⟨⟨⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩, hP⟩⟩

private theorem core (d : ℕ) (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (SL : Set (HeightOneSpectrum (𝓞 L)))
    (BK : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (BL : HeightOneSpectrum (𝓞 L) → Multiset ℂ)
    (e : HeightOneSpectrum (𝓞 K) → ℂ) (c₀ : ℝ) (r : ℕ) (hd : 0 < d)
    (hS : ∀ w, w ∈ SL ↔ w.under (𝓞 K) ∈ MainNotions)
    (h : ∀ p ∉ MainNotions, Multiset.card (BK p) ≤ r ∧ (∀ b ∈ BK p, ‖b‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀) ∧
      ∀ w : PlacesOver L p, IsPrimitiveRoot (e p) (fdeg w) ∧ Fintype.card (PlacesOver L p) * fdeg w = d ∧
        BL w.1 = (BK p).map (· ^ fdeg w))
    (s : ℂ) (hs : c₀ + 1 < s.re) :
    ∏ j ∈ Finset.range d, eulerL K (fun p => (BK p).map (· * e p ^ j)) MainNotions s = eulerL L BL SL s := by
  have hf : ∀ p ∉ MainNotions, ∀ w : PlacesOver L p, 0 < fdeg w := by
    intro p hp w
    have := ((h p hp).2.2 w).2.1
    rcases Nat.eq_zero_or_pos (fdeg w) with h0 | h0
    · rw [h0] at this; omega
    · exact h0
  have hL := (GlobalTheory.HenQ.Regroup.multipliable_E L SL BL c₀ r (by
    intro w hw
    have hp : w.under (𝓞 K) ∉ MainNotions := (hS w).not.mp hw
    let w' : PlacesOver L (w.under (𝓞 K)) := ⟨w, ⟨rfl⟩⟩
    obtain ⟨h1, h2, h3⟩ := h _ hp
    have hB : BL w = _ := (h3 w').2.2
    have hN : Ideal.absNorm w.asIdeal = _ := norm_eq w'
    refine ⟨by rw [hB, Multiset.card_map]; exact h1, fun b hb => ?_⟩
    rw [hB] at hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [hN, norm_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h2 a ha) _) s hs).hasProd
  have hK : ∀ j ∈ Finset.range d, Multipliable (fun p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions} =>
      (((BK p.1).map (· * e p.1 ^ j)).map fun b => (1 - b * ((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) := by
    intro j _
    refine GlobalTheory.HenQ.Regroup.multipliable_E K MainNotions (fun p => (BK p).map (· * e p ^ j)) c₀ r ?_ s hs
    intro p hp
    obtain ⟨h1, h2, h3⟩ := h _ hp
    obtain ⟨w⟩ := nonempty_over (L := L) p
    have he : ‖e p‖ = 1 := (h3 w).1.norm'_eq_one (hf p hp w).ne'
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [norm_mul, norm_pow, he, one_pow, mul_one]
    exact h2 a ha
  let E : (Σ p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions}, PlacesOver L p.1) ≃
      {w : HeightOneSpectrum (𝓞 L) // w ∉ SL} :=
    { toFun := fun x => ⟨x.2.1, by rw [hS, under_eq x.2]; exact x.1.2⟩
      invFun := fun w => ⟨⟨w.1.under (𝓞 K), (hS w.1).not.mp w.2⟩, ⟨w.1, ⟨rfl⟩⟩⟩
      left_inv := by
        rintro ⟨⟨p, hp⟩, w⟩
        have hw := under_eq w
        obtain ⟨w, hw'⟩ := w
        simp only at hw
        subst hw
        rfl
      right_inv := by intro w; rfl }
  have h2 := (E.hasProd_iff).mpr hL
  unfold eulerL
  rw [← Multipliable.tprod_finsetProd hK]
  refine (h2.sigma ?_).tprod_eq
  rintro ⟨p, hp⟩
  obtain ⟨w₀⟩ := nonempty_over (L := L) p
  obtain ⟨-, -, h3⟩ := h p hp
  have hcard : 0 < Fintype.card (PlacesOver L p) := Fintype.card_pos_iff.mpr ⟨w₀⟩
  have hff : ∀ w : PlacesOver L p, fdeg w = fdeg w₀ := fun w =>
    Nat.eq_of_mul_eq_mul_left hcard ((h3 w).2.1.trans (h3 w₀).2.1.symm)
  convert hasProd_fintype _ using 1
  · dsimp only [E, Equiv.coe_fn_mk, Function.comp_apply]
    rw [← (h3 w₀).2.1, fac_eq (h3 w₀).1 (hf p hp w₀), ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(h3 w).2.2, norm_eq w, cast_pow_cpow, hff w]

end BaseChangeLocalFactorRegrouping

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam.BaseChangeLocalFactorRegrouping in
theorem UpperTheory.V.Z.Gam.regroupBC :
    UpperTheory.V.Z.Gam.RegroupBC := by
  intro K L _ _ _ _ _ d MainNotions SL BK BL e c₀ r hd hS h
  refine ⟨c₀ + 1, fun s => ⟨fun hs => core d MainNotions SL BK BL e c₀ r hd.pos hS
    (fun p hp => ⟨(h p hp).1, fun b hb => ((h p hp).2.1 b hb).1, (h p hp).2.2⟩) s hs, fun hs => ?_⟩⟩
  unfold eulerLd
  rw [← core d MainNotions SL (fun p => (BK p).map (·⁻¹)) (fun w => (BL w).map (·⁻¹)) (fun p => (e p)⁻¹) c₀ r hd.pos hS
    ?_ (1 - s) ?_]
  · refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    funext p
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, mul_inv, inv_pow]
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := h p hp
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_, fun w => ⟨(h3 w).1.inv, (h3 w).2.1, ?_⟩⟩
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      exact (h2 a ha).2
    · simp only [(h3 w).2.2, Multiset.map_map]
      refine Multiset.map_congr rfl fun b _ => ?_
      simp only [Function.comp_apply, inv_pow]
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
