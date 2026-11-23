import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

namespace GlobalTheory.TameTwist

theorem sum_mul_eq_of_concentrated {U : Type} [CommGroup U] [Fintype U] (H : Subgroup U) (f g : U → ℂ)
    (hg : ∀ u, ∀ h ∈ H, g (u * h) = g u)
    (huniq : ∀ u v : U, (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (u * k * h) = μ * f (u * k)) →
      (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (v * k * h) = μ * f (v * k)) → u * v⁻¹ ∈ H) :
    ∃ u₀ : U, ∑ u, f u * g u = g u₀ * ∑ u, f u := by
  classical
  let Bad : U → Prop := fun u => ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (u * k * h) = μ * f (u * k)
  have hzero : ∀ u, Bad u → ∑ k : H, f (u * k) = 0 := by
    rintro u ⟨h, hh, μ, hμ, hf⟩
    have e : ∑ k : H, f (u * k) = μ * ∑ k : H, f (u * k) := by
      rw [Finset.mul_sum]
      calc ∑ k : H, f (u * k) = ∑ k : H, f (u * ((k * ⟨h, hh⟩ : H) : U)) :=
            (Fintype.sum_equiv (Equiv.mulRight (⟨h, hh⟩ : H)) _ _ (fun k => rfl)).symm
        _ = ∑ k : H, μ * f (u * k) := Finset.sum_congr rfl fun k _ => by
            rw [Subgroup.coe_mul, ← mul_assoc]
            exact hf k k.2
    have h2 : (1 - μ) * ∑ k : H, f (u * k) = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hμ))
  have main : ∀ u₀ : U, (∀ u, ¬ Bad u → g u = g u₀) → ∑ u, f u * g u = g u₀ * ∑ u, f u := by
    intro u₀ hu₀
    have key : ∀ u, ∑ k : H, f (u * k) * (g (u * k) - g u₀) = 0 := by
      intro u
      have hgk : ∀ k : H, g (u * k) = g u := fun k => hg u k k.2
      simp_rw [hgk, ← Finset.sum_mul]
      by_cases hu : Bad u
      · rw [hzero u hu, zero_mul]
      · rw [hu₀ u hu, sub_self, mul_zero]
    have e : ∀ k : H, ∑ u, f (u * k) * (g (u * k) - g u₀) = ∑ u, f u * (g u - g u₀) := fun k =>
      Fintype.sum_equiv (Equiv.mulRight (k : U)) _ _ (fun u => rfl)
    have h2 : (Fintype.card H : ℂ) * ∑ u, f u * (g u - g u₀) = 0 := by
      calc (Fintype.card H : ℂ) * ∑ u, f u * (g u - g u₀) = ∑ k : H, ∑ u, f u * (g u - g u₀) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ∑ k : H, ∑ u, f (u * k) * (g (u * k) - g u₀) := by simp_rw [e]
        _ = ∑ u, ∑ k : H, f (u * k) * (g (u * k) - g u₀) := Finset.sum_comm
        _ = 0 := by simp_rw [key, Finset.sum_const_zero]
    have h3 : ∑ u, f u * (g u - g u₀) = 0 :=
      (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    have h4 : ∑ u, f u * g u - g u₀ * ∑ u, f u = ∑ u, f u * (g u - g u₀) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [← sub_eq_zero, h4, h3]
  by_cases hex : ∃ u₀, ¬ Bad u₀
  · obtain ⟨u₀, hu₀⟩ := hex
    refine ⟨u₀, main u₀ fun u hu => ?_⟩
    have h1 : u₀ * (u₀⁻¹ * u) = u := mul_inv_cancel_left u₀ u
    have h2 : u₀⁻¹ * u ∈ H := by
      have := huniq u u₀ hu hu₀
      rwa [mul_comm] at this
    rw [← hg u₀ _ h2, h1]
  · push_neg at hex
    exact ⟨1, main 1 fun u hu => absurd (hex u) hu⟩

end GlobalTheory.TameTwist

namespace GlobalTheory.TameTwist

variable {E : Type} [Field E] [NumberField E]

theorem locK_eq_of_levelLe {ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {m : ℕ} (hξ : ξ.LevelLe w m) {a b : Eˣ}
    (ha : w.valuation E (a : E) = 1) (hb : w.valuation E (b : E) = 1)
    (hd : w.valuation E ((a : E) - b) ≤ WithZero.exp (-(m : ℤ))) : ξ.locK w a = ξ.locK w b := by
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have e : ((atFin w (a * b⁻¹) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      algebraMap E (w.adicCompletion E) ((a : E) / b) := by
    simp [atFin, div_eq_mul_inv]
  have h1 : ξ.loc w (atFin w (a * b⁻¹)) = 1 := by
    refine hξ _ ?_ ?_
    · rw [IsUnitAt, e, hval, map_div₀, ha, hb, div_one]
    · rw [e, ← map_one (algebraMap E (w.adicCompletion E)), ← map_sub, hval, div_sub_one b.ne_zero, map_div₀, hb, div_one]
      exact hd
  have h2 : ξ.locK w (a * b⁻¹) = 1 := h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at h2

open Classical in

def twInv (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (y : E) : ℂ :=
  if h : y = 0 then 0 else (((ξ.locK w (Units.mk0 y h))⁻¹ : ℂˣ) : ℂ)

theorem gaussTerm_mul (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (c : Eˣ) (y : E) :
    gaussTerm (χ * ξ) w c y = gaussTerm χ w c y * twInv ξ w y := by
  have hm : ∀ x, (χ * ξ).locK w x = χ.locK w x * ξ.locK w x := fun x => rfl
  unfold gaussTerm twInv
  split_ifs with h
  · simp
  · rw [hm, mul_inv, Units.val_mul]
    ring

theorem gaussTerm_mul_one_add (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (c : Eˣ) {r : E} (hr : r ≠ 0) {z : E} (e : Eˣ)
    (he : (e : E) = 1 + z) :
    gaussTerm χ w c (r * (1 + z)) =
      gaussTerm χ w c r * ((((χ.locK w e)⁻¹ : ℂˣ) : ℂ) * psiAt w (algebraMap E (w.adicCompletion E) (r * z / c))) := by
  have h1 : r * (1 + z) ≠ 0 := by rw [← he]; exact mul_ne_zero hr e.ne_zero
  have hu : Units.mk0 _ h1 = Units.mk0 r hr * e := by ext; simp [he]
  have hψ : r * (1 + z) / c = r / c + r * z / c := by ring
  rw [gaussTerm, gaussTerm, dif_neg h1, dif_neg hr, hu, map_mul, hψ, map_add, psiAt_add]
  simp only [mul_inv, Units.val_mul]
  ring

theorem psiAt_mul_congr {w : HeightOneSpectrum (𝓞 E)} {c : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((2 + diffExp w : ℕ) : ℤ))) {r r' z : 𝓞 E} (h : r - r' ∈ w.asIdeal)
    (hz : z ∈ w.asIdeal) :
    psiAt w (algebraMap E (w.adicCompletion E) ((r : E) * z / c)) =
      psiAt w (algebraMap E (w.adicCompletion E) ((r' : E) * z / c)) := by
  have e : (r : E) * z / c = (r' : E) * z / c + (((r - r') * z : 𝓞 E) : E) / c := by push_cast; ring
  have hm : (r - r') * z - 0 ∈ w.asIdeal ^ 2 := by rw [sub_zero, pow_two]; exact Ideal.mul_mem_mul h hz
  have hv := valuation_sub_le (E := E) hm
  rw [e, map_add, psiAt_add, psiAt_eq_one (t := algebraMap E _ ((((r - r') * z : 𝓞 E) : E) / c)), mul_one]
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  rw [hval, map_div₀, hc,
    div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
  rw [show ((0 : 𝓞 E) : E) = 0 from rfl, sub_zero] at hv
  convert hv using 2
  push_cast
  ring

end GlobalTheory.TameTwist

namespace GlobalTheory.TameTwist

variable {E : Type} [Field E] [NumberField E]

theorem mem_of_psiAt_eq_one {w : HeightOneSpectrum (𝓞 E)} {c : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((2 + diffExp w : ℕ) : ℤ))) {d : 𝓞 E}
    (h : ∀ z : 𝓞 E, z ∈ w.asIdeal → psiAt w (algebraMap E (w.adicCompletion E) ((d : E) * z / c)) = 1) :
    d ∈ w.asIdeal := by
  by_contra hd
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hd1 : w.valuation E (d : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hd
  have hπ1 : w.valuation E (π : E) = WithZero.exp (-1) := by
    rw [← hπ, ← w.valuation_of_algebraMap (K := E)]
  have hπP : π ∈ w.asIdeal := by
    rw [← w.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  set t := algebraMap E (w.adicCompletion E) ((d : E) * π / c) with ht_def
  have ht : Valued.v t = WithZero.exp ((1 + diffExp w : ℕ) : ℤ) := by
    rw [ht_def, hval, map_div₀, map_mul, hd1, hπ1, hc, one_mul, ← WithZero.exp_sub]
    congr 1
    push_cast
    ring
  have hnot : ¬ ∀ r ∈ w.adicCompletionIntegers E, psiAt w (t * r) = 1 := by
    rw [psiAt_conductor, ht, WithZero.exp_le_exp]
    push_cast
    omega
  push_neg at hnot
  obtain ⟨r, hr, hψ⟩ := hnot
  obtain ⟨r₀, hr₀⟩ := Formalism.UG.P.glint_exists_approx w ⟨r, hr⟩
  apply hψ
  have hr₀' : Valued.v (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀) ≤ WithZero.exp (-1) := by
    have h1 : Valued.v (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀) < 1 := hr₀
    generalize Valued.v (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀) = x at h1 ⊢
    by_cases hx : x = 0
    · rw [hx]; exact zero_le'
    rw [← WithZero.exp_log hx] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]; omega
  have e : t * r = algebraMap E (w.adicCompletion E) ((d : E) * ((π * r₀ : 𝓞 E) : E) / c) +
      t * (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀) := by
    rw [ht_def, IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E) r₀,
      show (d : E) * ((π * r₀ : 𝓞 E) : E) / c = ((d : E) * π / c) * algebraMap (𝓞 E) E r₀ by
        rw [show algebraMap (𝓞 E) E r₀ = (r₀ : E) from rfl]; push_cast; ring, map_mul]
    ring
  rw [e, psiAt_add, h _ (Ideal.mul_mem_right _ _ hπP), one_mul]
  apply psiAt_eq_one
  rw [map_mul, ht]
  calc WithZero.exp ((1 + diffExp w : ℕ) : ℤ) * Valued.v (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀)
      ≤ WithZero.exp ((1 + diffExp w : ℕ) : ℤ) * WithZero.exp (-1) := by gcongr
    _ = WithZero.exp (diffExp w : ℤ) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring

end GlobalTheory.TameTwist

namespace GlobalTheory.TameTwist

variable {E : Type} [Field E] [NumberField E]

theorem gaussSumAt_mul_tame {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.LevelLe w 2) (hξ : ξ.TameAt w) {c : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((2 + diffExp w : ℕ) : ℤ))) :
    ∃ x₀ : Eˣ, gaussSumAt (χ * ξ) w 2 c = (((ξ.locK w x₀)⁻¹ : ℂˣ) : ℂ) * gaussSumAt χ w 2 c := by
  classical
  have := w.isMaximal
  have := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal ^ 2)ˣ
  let rep : 𝓞 E ⧸ w.asIdeal ^ 2 → 𝓞 E := fun x => Quotient.out x
  let φ : 𝓞 E ⧸ w.asIdeal ^ 2 →+* 𝓞 E ⧸ w.asIdeal := Ideal.Quotient.factor (Ideal.pow_le_self two_ne_zero)
  let H : Subgroup (𝓞 E ⧸ w.asIdeal ^ 2)ˣ := (Units.map φ.toMonoidHom).ker
  have hrep2 : ∀ x, Ideal.Quotient.mk (w.asIdeal ^ 2) (rep x) = x := fun x => Ideal.Quotient.mk_out x
  have hrep : ∀ x, Ideal.Quotient.mk w.asIdeal (rep x) = φ x := fun x => by
    conv_rhs => rw [← hrep2 x]
    rfl
  have hnm : ∀ u : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, rep u ∉ w.asIdeal := fun u => out_notMem w two_ne_zero u
  have hv1 : ∀ u : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, w.valuation E (rep u : E) = 1 := fun u =>
    (w.valuation_eq_one_iff_notMem (K := E)).2 (hnm u)
  have hne : ∀ u : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, (rep u : E) ≠ 0 := fun u h => by
    have := hv1 u
    rw [h, map_zero] at this
    exact zero_ne_one this

  have hmemH : ∀ u v : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, u * v⁻¹ ∈ H ↔ rep u - rep v ∈ w.asIdeal := by
    intro u v
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, ← Ideal.Quotient.eq, hrep, hrep, Units.ext_iff]
    rfl
  have hH' : ∀ u k : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, k ∈ H → rep (u * k : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ) - rep u ∈ w.asIdeal := by
    intro u k hk
    rw [← hmemH, mul_comm u k, mul_inv_cancel_right]
    exact hk
  let f : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ → ℂ := fun u => gaussTerm χ w c (rep u)
  let g : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ → ℂ := fun u => twInv ξ w (rep u)
  have hg : ∀ u, ∀ k ∈ H, g (u * k) = g u := by
    intro u k hk
    show twInv ξ w (rep ↑(u * k)) = twInv ξ w (rep ↑u)
    rw [twInv, twInv, dif_neg (hne (u * k)), dif_neg (hne u)]
    have hd := valuation_sub_le (E := E) (w := w) (a := 1) (y := rep ↑(u * k)) (y' := rep ↑u)
      (by rw [pow_one]; exact hH' u k hk)
    have hξ1 : ξ.LevelLe w 1 := hξ
    have hd' : w.valuation E (((Units.mk0 _ (hne (u * k)) : Eˣ) : E) - ((Units.mk0 _ (hne u) : Eˣ) : E)) ≤
        WithZero.exp (-((1 : ℕ) : ℤ)) := by
      rw [Units.val_mk0, Units.val_mk0]; exact hd
    have ha : w.valuation E ((Units.mk0 _ (hne (u * k)) : Eˣ) : E) = 1 := by rw [Units.val_mk0]; exact hv1 (u * k)
    have hb : w.valuation E ((Units.mk0 _ (hne u) : Eˣ) : E) = 1 := by rw [Units.val_mk0]; exact hv1 u
    rw [locK_eq_of_levelLe hξ1 ha hb hd']

  have hmult : ∀ (u' h : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ) (z : 𝓞 E) (e : Eˣ), (h : 𝓞 E ⧸ w.asIdeal ^ 2) = Ideal.Quotient.mk _ (1 + z) →
      (e : E) = 1 + z → z ∈ w.asIdeal →
      f (u' * h) = f u' * ((((χ.locK w e)⁻¹ : ℂˣ) : ℂ) * psiAt w (algebraMap E (w.adicCompletion E) ((rep u' : E) * z / c))) := by
    intro u' h z e hh he hz
    have h1 : (1 + z) ∉ w.asIdeal := fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
      simpa using w.asIdeal.sub_mem h1 hz))
    have h2 : rep u' * (1 + z) ∉ w.asIdeal := fun h2 => (w.isPrime.mem_or_mem h2).elim (hnm u') h1
    have h3 : rep (u' * h : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ) - rep u' * (1 + z) ∈ w.asIdeal ^ 2 := by
      rw [← Ideal.Quotient.eq, hrep2, map_mul, hrep2, ← hh, Units.val_mul]
    simp only [f]
    rw [gaussTerm_congr hχ hc (hnm _) h2 h3,
      show ((rep u' * (1 + z) : 𝓞 E) : E) = (rep u' : E) * (1 + (z : E)) by push_cast; ring]
    exact gaussTerm_mul_one_add χ w c (hne u') e (by rw [he])

  have huniq : ∀ u v : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ,
      (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (u * k * h) = μ * f (u * k)) →
      (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (v * k * h) = μ * f (v * k)) → u * v⁻¹ ∈ H := by
    intro u v hu hv
    rw [hmemH]
    refine mem_of_psiAt_eq_one hc fun z hz => ?_
    have h1 : (1 + z) ∉ w.asIdeal := fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
      simpa using w.asIdeal.sub_mem h1 hz))
    have he0 : ((1 + z : 𝓞 E) : E) ≠ 0 := fun h0 => h1 (by
      have : (1 + z : 𝓞 E) = 0 := Subtype.ext h0
      rw [this]; exact w.asIdeal.zero_mem)
    let e : Eˣ := Units.mk0 _ he0
    have he : (e : E) = 1 + (z : E) := by simp [e]
    obtain ⟨h, hh⟩ := Ideal.Quotient.isUnit_mk_pow_of_notMem w.asIdeal (n := 2) h1
    have hhH : h ∈ H := by
      rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one]
      show φ h = 1
      rw [hh]
      show Ideal.Quotient.mk w.asIdeal (1 + z) = 1
      rw [map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.2 hz, add_zero]

    have key : ∀ u : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ,
        (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (u * k * h) = μ * f (u * k)) →
        psiAt w (algebraMap E (w.adicCompletion E) ((rep u : E) * z / c)) = ((χ.locK w e : ℂˣ) : ℂ) := by
      intro u hu
      by_contra hne'
      refine hu ⟨h, hhH, (((χ.locK w e)⁻¹ : ℂˣ) : ℂ) * psiAt w (algebraMap E (w.adicCompletion E) ((rep u : E) * z / c)),
        ?_, fun k hk => ?_⟩
      · intro h1
        apply hne'
        rw [Units.val_inv_eq_inv_val, inv_mul_eq_one₀ (χ.locK w e).ne_zero] at h1
        exact h1.symm
      · rw [hmult (u * k) h z e hh he hz, psiAt_mul_congr hc (hH' u k hk) hz, mul_comm]
    have ev := key v hv
    have eu := key u hu
    have e2 : ((rep u : E) * z / c) = (rep v : E) * z / c + (((rep u - rep v : 𝓞 E) : E) * z / c) := by
      push_cast; ring
    rw [e2, map_add, psiAt_add, ev] at eu
    have := (χ.locK w e).ne_zero
    exact (mul_eq_left₀ this).1 eu
  obtain ⟨u₀, hu₀⟩ := sum_mul_eq_of_concentrated H f g hg huniq
  refine ⟨Units.mk0 _ (hne u₀), ?_⟩
  rw [gaussSumAt, gaussSumAt, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp_rw [gaussTerm_mul]
  have hg0 : g u₀ = (((ξ.locK w (Units.mk0 _ (hne u₀)))⁻¹ : ℂˣ) : ℂ) := by
    simp only [g, twInv, dif_neg (hne u₀)]
  rw [← hg0]
  exact hu₀

end GlobalTheory.TameTwist

namespace GlobalTheory.TameTwist

theorem locEps_mul_tame : ∀ (E : Type) [Field E] [NumberField E] (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) (s : ℂ),
    q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → (q : 𝓞 E) ∉ w.asIdeal ^ 2 → ExpAt χ w 2 → ξ.TameAt w →
      ExpAt (χ * ξ) w 2 ∧ ∃ y : Eˣ, locEps (χ * ξ) w 2 s = ((ξ.locK w y : ℂˣ) : ℂ) * locEps χ w 2 s := by
  intro E _ _ χ ξ w q s _ _ _ hχ hξ
  have mono : ∀ {θ : HChar E} {m m' : ℕ}, m ≤ m' → θ.LevelLe w m → θ.LevelLe w m' := fun hm h x hx hd =>
    h x hx (hd.trans (WithZero.exp_le_exp.2 (by omega)))
  have hξ1 : ξ.LevelLe w 1 := hξ
  have hmul : ∀ {θ θ' : HChar E} {m : ℕ}, θ.LevelLe w m → θ'.LevelLe w m → (θ * θ').LevelLe w m :=
    fun h h' x hx hd => by rw [Formalism.L2.Host.HChar.loc_mul, h x hx hd, h' x hx hd, one_mul]
  have hχ2 : χ.LevelLe w 2 := (hχ 2).2 le_rfl
  refine ⟨fun m => ⟨fun h => ?_, fun hm => hmul ((hχ m).2 hm) (mono (by omega) hξ1)⟩, ?_⟩
  · by_contra hm
    have h1 : (χ * ξ).LevelLe w 1 := mono (by omega) h
    have h2 : χ.LevelLe w 1 := by
      have h3 : (χ * ξ * ξ⁻¹).LevelLe w 1 :=
        hmul h1 (fun x hx hd => by rw [Formalism.L2.Host.HChar.loc_inv, hξ1 x hx hd, inv_one])
      rwa [mul_inv_cancel_right] at h3
    exact absurd ((hχ 1).1 h2) (by omega)
  · obtain ⟨x₀, hx₀⟩ := gaussSumAt_mul_tame hχ2 hξ (valuation_unif_pow w (2 + diffExp w))
    refine ⟨unif w ^ (2 + diffExp w) * x₀⁻¹, ?_⟩
    rw [locEps, locEps, if_neg two_ne_zero, if_neg two_ne_zero, hx₀]
    have hm : ∀ x, (χ * ξ).locK w x = χ.locK w x * ξ.locK w x := fun x => rfl
    rw [hm, map_mul, map_inv]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring

end GlobalTheory.TameTwist
