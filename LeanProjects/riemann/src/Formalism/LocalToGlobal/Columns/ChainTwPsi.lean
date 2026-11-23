import Formalism.LocalToGlobal.Columns.ChainTwOk

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwPsi

variable {X : Fields} {P : HeightOneSpectrum (𝓞 X.E)}

theorem twDvd_of_intAt (hq : (qOf P).Prime) : ∀ (D : ℕ) (b : ℤ), IntAt P ((b : X.E) / (qOf P : X.E) ^ D) → ((qOf P : ℤ) ^ D) ∣ b
  | 0, b, _ => by simp
  | D + 1, b, h => by
      have hq0 : (qOf P : X.E) ≠ 0 := by exact_mod_cast hq.ne_zero
      have h1 : IntAt P ((b : X.E) / (qOf P : X.E) ^ D) := by
        have e : (b : X.E) / (qOf P : X.E) ^ D = (qOf P : X.E) * ((b : X.E) / (qOf P : X.E) ^ (D + 1)) := by
          field_simp
          ring
        rw [e]
        exact (ciIntAt_q (P := P) (q := qOf P)).mul h
      obtain ⟨b', rfl⟩ := twDvd_of_intAt hq D b h1
      have h2 : IntAt P ((b' : X.E) / (qOf P : X.E)) := by
        have e : (b' : X.E) / (qOf P : X.E) = (((qOf P : ℤ) ^ D * b' : ℤ) : X.E) / (qOf P : X.E) ^ (D + 1) := by
          push_cast
          field_simp
          ring
        rw [e]
        exact h
      have h3 : redP P (b' : X.E) = 0 := by
        have e : (b' : X.E) = (qOf P : X.E) * ((b' : X.E) / (qOf P : X.E)) := by field_simp
        rw [e, reduction_mul (ciIntAt_q (P := P) (q := qOf P)) h2, redP_natCast_eq_zero (ciQ_mem P), zero_mul]
      rw [redP_intCast] at h3
      have h4 := (owedC_intCast_eq_iff (A := 𝓞 X.E ⧸ P.asIdeal) hq (ciCard P) b' 0).1 (by rw [h3, Int.cast_zero])
      rw [sub_zero] at h4
      obtain ⟨c, rfl⟩ := h4
      exact ⟨c, by ring⟩

theorem twRes_exists (hq : (qOf P).Prime) (hu : ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2) :
    ∀ (D : ℕ) (y : X.E), IntAt P y → ∃ b : ℤ, IntAt P ((y - b) / (qOf P : X.E) ^ D)
  | 0, y, hy => ⟨0, by simpa using hy⟩
  | D + 1, y, hy => by
      have hq0 : (qOf P : X.E) ≠ 0 := by exact_mod_cast hq.ne_zero
      obtain ⟨b0, hb0⟩ := owedC_exists_int (A := 𝓞 X.E ⧸ P.asIdeal) hq (ciCard P) (redP P y)
      have hz : IntAt P ((y - b0) / (qOf P : X.E)) :=
        ciIntAt_div (ciQ_mem P) hu (ciIntAt_sub hy (ciIntAt_intCast b0))
          (by rw [redP_sub hy (ciIntAt_intCast b0), redP_intCast, hb0, sub_self])
      obtain ⟨b1, hb1⟩ := twRes_exists hq hu D _ hz
      refine ⟨b0 + (qOf P : ℤ) * b1, ?_⟩
      have e : (y - ((b0 + (qOf P : ℤ) * b1 : ℤ) : X.E)) / (qOf P : X.E) ^ (D + 1) =
          ((y - b0) / (qOf P : X.E) - b1) / (qOf P : X.E) ^ D := by
        push_cast
        field_simp
        ring
      rw [e]
      exact hb1

variable {σ₀ : X.K →+* ℂ} {xi0 : X.E} {D : ℕ}

theorem twZeta_pow (hz : σ₀ (twZeta σ₀ (qOf P ^ D)) = Complex.exp (2 * Real.pi * Complex.I / ((qOf P ^ D : ℕ) : ℂ)))
    (hq : (qOf P).Prime) (b : ℤ) : σ₀ (twZeta σ₀ (qOf P ^ D) ^ b) = Complex.exp (2 * Real.pi * Complex.I * b / ((qOf P ^ D : ℕ) : ℂ)) := by
  rw [map_zpow₀, hz, ← Complex.exp_int_mul]
  congr 1
  ring

theorem twZeta_ne (hz : σ₀ (twZeta σ₀ (qOf P ^ D)) = Complex.exp (2 * Real.pi * Complex.I / ((qOf P ^ D : ℕ) : ℂ))) :
    twZeta σ₀ (qOf P ^ D) ≠ 0 := by
  intro h
  rw [h, map_zero] at hz
  exact Complex.exp_ne_zero _ hz.symm

theorem twZeta_zpow_congr (hz : σ₀ (twZeta σ₀ (qOf P ^ D)) = Complex.exp (2 * Real.pi * Complex.I / ((qOf P ^ D : ℕ) : ℂ)))
    (hq : (qOf P).Prime) {b b' : ℤ} (h : ((qOf P : ℤ) ^ D) ∣ b - b') :
    twZeta σ₀ (qOf P ^ D) ^ b = twZeta σ₀ (qOf P ^ D) ^ b' := by
  apply σ₀.injective
  rw [twZeta_pow hz hq, twZeta_pow hz hq]
  obtain ⟨k, hk⟩ := h
  have hN : ((qOf P ^ D : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hq.ne_zero
  have e : 2 * Real.pi * Complex.I * (b : ℂ) / ((qOf P ^ D : ℕ) : ℂ) =
      2 * Real.pi * Complex.I * (b' : ℂ) / ((qOf P ^ D : ℕ) : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    have hb : (b : ℂ) = (b' : ℂ) + ((qOf P ^ D : ℕ) : ℂ) * k := by
      have := congrArg (fun z : ℤ => (z : ℂ)) hk
      push_cast at this ⊢
      linear_combination this
    rw [hb]
    field_simp
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

open Classical in

theorem twPsiQ_eq (hz : σ₀ (twZeta σ₀ (qOf P ^ D)) = Complex.exp (2 * Real.pi * Complex.I / ((qOf P ^ D : ℕ) : ℂ)))
    (hq : (qOf P).Prime) {a : X.E} (ha : IntAt P ((qOf P : X.E) ^ D * a)) {b : ℤ}
    (hb : IntAt P (xi0 * a - (b : X.E) / (qOf P : X.E) ^ D)) :
    twPsiQ σ₀ xi0 P D a = twZeta σ₀ (qOf P ^ D) ^ b := by
  have hex : ∃ b : ℤ, IntAt P ((qOf P : X.E) ^ D * a) ∧ IntAt P (xi0 * a - (b : X.E) / (qOf P : X.E) ^ D) := ⟨b, ha, hb⟩
  unfold twPsiQ
  rw [dif_pos hex]
  have hc := hex.choose_spec.2
  apply twZeta_zpow_congr hz hq
  apply twDvd_of_intAt hq D
  have e : ((hex.choose - b : ℤ) : X.E) / (qOf P : X.E) ^ D =
      (xi0 * a - (b : X.E) / (qOf P : X.E) ^ D) - (xi0 * a - (hex.choose : X.E) / (qOf P : X.E) ^ D) := by
    push_cast
    ring
  rw [e]
  exact ciIntAt_sub hb hc

theorem twPsiQ_exists (hq : (qOf P).Prime) (hu : ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2) (hxi : IntAt P xi0) {a : X.E}
    (ha : IntAt P ((qOf P : X.E) ^ D * a)) : ∃ b : ℤ, IntAt P (xi0 * a - (b : X.E) / (qOf P : X.E) ^ D) := by
  have hq0 : (qOf P : X.E) ≠ 0 := by exact_mod_cast hq.ne_zero
  obtain ⟨b, hb⟩ := twRes_exists hq hu D _ (hxi.mul ha)
  refine ⟨b, ?_⟩
  have e : xi0 * a - (b : X.E) / (qOf P : X.E) ^ D = (xi0 * ((qOf P : X.E) ^ D * a) - b) / (qOf P : X.E) ^ D := by
    field_simp
  rw [e]
  exact hb

end TwPsi

section TwCstQOf

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {G : ChGlob X R.m}

theorem twCstQ_of (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0) : TwCstQ (Pr := Pr) sel mu G := by
  have h2 := R.two_le_m
  have hzz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      G.σ₀ (twZeta G.σ₀ (qOf P.1 ^ (2 * R.m))) = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)) :=
    fun P hP => Classical.epsilon_spec (hz P hP)
  have hqD : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ x : X.E, IntAt P.1 x → IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * x) :=
    fun P _ x hx => by
      have e : (qOf P.1 : X.E) ^ (2 * R.m) = algebraMap (𝓞 X.E) X.E ((qOf P.1 : 𝓞 X.E) ^ (2 * R.m)) := by simp
      rw [e]
      exact (IntAt.coe P.1 _).mul hx
  refine ⟨fun P hP x y hx hy => ?_, fun P hP x hx => ?_, fun P hP => ?_, fun P hP => Classical.epsilon_spec (hs P hP),
    fun P hP a b ha hab => ?_, hxi⟩
  · obtain ⟨hq, hu⟩ := hd P hP
    obtain ⟨bx, hbx⟩ := twPsiQ_exists hq hu (hxi P hP).1 hx
    obtain ⟨by', hby⟩ := twPsiQ_exists hq hu (hxi P hP).1 hy
    have hxy : IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * (x + y)) := by rw [mul_add]; exact hx.add hy
    have hbxy : IntAt P.1 (G.xi0 * (x + y) - ((bx + by' : ℤ) : X.E) / (qOf P.1 : X.E) ^ (2 * R.m)) := by
      have e : G.xi0 * (x + y) - ((bx + by' : ℤ) : X.E) / (qOf P.1 : X.E) ^ (2 * R.m) =
          (G.xi0 * x - (bx : X.E) / (qOf P.1 : X.E) ^ (2 * R.m)) + (G.xi0 * y - (by' : X.E) / (qOf P.1 : X.E) ^ (2 * R.m)) := by
        push_cast
        ring
      rw [e]
      exact hbx.add hby
    rw [twPsiQ_eq (hzz P hP) hq hxy hbxy, twPsiQ_eq (hzz P hP) hq hx hbx, twPsiQ_eq (hzz P hP) hq hy hby,
      zpow_add₀ (twZeta_ne (hzz P hP))]
  · obtain ⟨hq, -⟩ := hd P hP
    have h0 : IntAt P.1 (G.xi0 * x - ((0 : ℤ) : X.E) / (qOf P.1 : X.E) ^ (2 * R.m)) := by
      simpa using (hxi P hP).1.mul hx
    rw [twPsiQ_eq (hzz P hP) hq (hqD P hP x hx) h0, zpow_zero]
  · obtain ⟨hq, hu⟩ := hd P hP
    have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast hq.ne_zero
    have ha : IntAt P.1 ((qOf P.1 : X.E) ^ (2 * R.m) * (qOf P.1 : X.E)⁻¹) := by
      have e : (qOf P.1 : X.E) ^ (2 * R.m) * (qOf P.1 : X.E)⁻¹ = algebraMap (𝓞 X.E) X.E ((qOf P.1 : 𝓞 X.E) ^ (2 * R.m - 1)) := by
        rw [map_pow, map_natCast, ← pow_sub_one_mul (by omega : 2 * R.m ≠ 0)]
        field_simp
      rw [e]
      exact IntAt.coe P.1 _
    obtain ⟨b, hb⟩ := twPsiQ_exists hq hu (hxi P hP).1 ha
    rw [twPsiQ_eq (hzz P hP) hq ha hb]
    intro h1
    have h2 := congrArg G.σ₀ h1
    rw [twZeta_pow (hzz P hP) hq, map_one, Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    have hN : ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hq.ne_zero
    have hbn : (b : ℂ) = (n : ℂ) * ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ) := by
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      field_simp at hn
      linear_combination hn
    have hbn' : b = n * ((qOf P.1 ^ (2 * R.m) : ℕ) : ℤ) := by exact_mod_cast hbn
    have hdiv : IntAt P.1 (G.xi0 / (qOf P.1 : X.E)) := by
      have e : G.xi0 / (qOf P.1 : X.E) = (G.xi0 * (qOf P.1 : X.E)⁻¹ - (b : X.E) / (qOf P.1 : X.E) ^ (2 * R.m)) + (n : X.E) := by
        rw [hbn']
        push_cast
        field_simp
        ring
      rw [e]
      exact hb.add (ciIntAt_intCast n)
    apply (hxi P hP).2
    have e : G.xi0 = (qOf P.1 : X.E) * (G.xi0 / (qOf P.1 : X.E)) := by field_simp
    rw [e, reduction_mul (ciIntAt_q (P := P.1) (q := qOf P.1)) hdiv, redP_natCast_eq_zero (ciQ_mem P.1), zero_mul]
  · obtain ⟨hq, -⟩ := hd P hP
    rw [twPsiQ_eq (hzz P hP) hq ha hab, twZeta_pow (hzz P hP) hq]
    push_cast
    rfl

end TwCstQOf

section TwFin

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem twLamQ_mem {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (v : Sp X.E (R.N j + cOf R j)) :
    v ∈ lamYat (Pr := Pr) (R := R) j P ↔ ∀ l, IntAt P (v l) := by
  have e : lamYat (Pr := Pr) (R := R) j P = LocE.lamY P (qOf P) (R.N j) (cOf R j) 0 := by
    unfold lamYat
    rw [if_neg hP]
  rw [e]
  unfold LocE.lamY
  rw [ciMem_sclLat]
  have h0 : ∀ l : ℕ, LocE.scE (R.N j) 0 l = 0 := fun l => by
    unfold LocE.scE
    split_ifs <;> rfl
  simp only [h0, zpow_zero, inv_one, one_mul]

theorem twStd_mem {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (v : Sp E n) :
    v ∈ stdAt E n P ↔ ∀ l, IntAt P (v l) := ciMem_stdAt P v

theorem twParL_mem {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q kj n c : ℕ} (v : Sp E (n + c)) :
    v ∈ LocE.parL P q kj n c ↔ ∀ l : Fin (n + c), IntAt P (((q : E) ^ (if kj ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * v l) := by
  unfold LocE.parL
  rw [ciMem_sclLat]

def twE {E : Type} [Field E] {N : ℕ} (s : Fin N) : Sp E N := fun l => if s = l then 1 else 0

theorem twE_int {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} (s : Fin N) (l : Fin N) :
    IntAt P (twE (E := E) s l) := by
  unfold twE
  split_ifs
  · exact ⟨1, 1, one_notMem P, by simp⟩
  · exact ⟨0, 1, one_notMem P, by simp⟩

theorem twApply_coord {E : Type} [Field E] {N M : ℕ} (f : Sp E N →ₗ[E] Sp E M) (v : Sp E N) (l : Fin M) :
    f v l = ∑ s, v s * f (twE s) l := by
  rw [LinearMap.pi_apply_eq_sum_univ f v, Finset.sum_apply]
  rfl

theorem twIntAt_sum {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} (f : Fin N → E)
    (h : ∀ s, IntAt P (f s)) : IntAt P (∑ s, f s) :=
  Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) ⟨0, 1, one_notMem P, by simp⟩ (fun s _ => h s)

theorem twJ_of_close (sharp : Bool) {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (hq0 : (qOf P : X.E) ≠ 0)
    (h h' : AutY X R j) (hb : ∀ v, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (h⁻¹ v l))
    (hb' : ∀ v, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (h'⁻¹ v l))
    (he : ∀ v, (∀ l, IntAt P (v l)) → ∀ l, IntAt P ((qOf P : X.E)⁻¹ * (h' v l - h v l))) :
    h⁻¹ * h' ∈ Jat (Pr := Pr) (R := R) sharp j P := by
  rw [twJat_Q sharp j hP]

  set q : X.E := (qOf P : X.E) with hqdef
  let w : Sp X.E (R.N j + cOf R j) → Sp X.E (R.N j + cOf R j) := fun v => q⁻¹ • (h' v - h v)
  have hw : ∀ v, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (w v l) := fun v hv l => by
    show IntAt P ((q⁻¹ • (h' v - h v)) l)
    simpa [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] using he v hv l
  have hκ : ∀ v, (h⁻¹ * h') v = v + q • h⁻¹ (w v) := fun v => by
    show h⁻¹ (h' v) = _
    have : h' v = h v + q • w v := by
      show h' v = h v + q • (q⁻¹ • (h' v - h v))
      rw [smul_smul, mul_inv_cancel₀ hq0, one_smul, add_sub_cancel]
    rw [this, map_add, map_smul]
    simp
  have hκi : ∀ v, (h⁻¹ * h')⁻¹ v = v - q • h'⁻¹ (w v) := fun v => by
    show (h'⁻¹ * h) v = _
    show h'⁻¹ (h v) = _
    have : h v = h' v - q • w v := by
      show h v = h' v - q • (q⁻¹ • (h' v - h v))
      rw [smul_smul, mul_inv_cancel₀ hq0, one_smul, sub_sub_cancel]
    rw [this, map_sub, map_smul]
    simp
  have hqI : IntAt P q := ciIntAt_q

  have stdF : ∀ v, (∀ l, IntAt P (v l)) → ∀ l, IntAt P ((h⁻¹ * h') v l) := fun v hv l => by
    rw [hκ]
    exact (hv l).add (hqI.mul (hb _ (hw v hv) l))
  have stdB : ∀ v, (∀ l, IntAt P (v l)) → ∀ l, IntAt P ((h⁻¹ * h')⁻¹ v l) := fun v hv l => by
    rw [hκi]
    exact ciIntAt_sub (hv l) (hqI.mul (hb' _ (hw v hv) l))
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [twStd_mem, twStd_mem]
    constructor
    · intro h1
      have := stdB _ h1
      simpa using this
    · exact stdF v
  ·
    have sub_std : ∀ u : Sp X.E (R.N j + cOf R j), u ∈ LocE.parL P (qOf P) (R.k + j) (R.N j) (cOf R j) → ∀ l, IntAt P (u l) := by
      intro u hu l
      have h1 := (twParL_mem u).1 hu l
      split_ifs at h1
      · have e : u l = q * ((q ^ (1 : ℤ))⁻¹ * u l) := by rw [zpow_one]; field_simp
        rw [e]
        exact hqI.mul h1
      · simpa using h1
    have q_par : ∀ u : Sp X.E (R.N j + cOf R j), (∀ l, IntAt P (u l)) → ∀ l : Fin (R.N j + cOf R j),
        IntAt P (((qOf P : X.E) ^ (if R.k + j ≤ l.1 ∧ l.1 < R.N j then (1 : ℤ) else 0))⁻¹ * (q * u l)) := by
      intro u hu l
      split_ifs
      · have e : (((qOf P : X.E) ^ (1 : ℤ))⁻¹ * (q * u l)) = u l := by rw [zpow_one, ← hqdef]; field_simp
        rw [e]
        exact hu l
      · simpa using hqI.mul (hu l)
    have parF : ∀ v, v ∈ LocE.parL P (qOf P) (R.k + j) (R.N j) (cOf R j) →
        (h⁻¹ * h') v ∈ LocE.parL P (qOf P) (R.k + j) (R.N j) (cOf R j) := fun v hv => by
      rw [hκ]
      refine Submodule.add_mem _ hv ?_
      rw [twParL_mem]
      intro l
      have := q_par (h⁻¹ (w v)) (hb _ (hw v (sub_std v hv))) l
      simpa [Pi.smul_apply, smul_eq_mul] using this
    have parB : ∀ v, v ∈ LocE.parL P (qOf P) (R.k + j) (R.N j) (cOf R j) →
        (h⁻¹ * h')⁻¹ v ∈ LocE.parL P (qOf P) (R.k + j) (R.N j) (cOf R j) := fun v hv => by
      rw [hκi]
      refine Submodule.sub_mem _ hv ?_
      rw [twParL_mem]
      intro l
      have := q_par (h'⁻¹ (w v)) (hb' _ (hw v (sub_std v hv))) l
      simpa [Pi.smul_apply, smul_eq_mul] using this
    constructor
    · intro h1
      have := parB _ h1
      simpa using this
    · exact parF v

theorem twApply_coordE {E : Type} [Field E] {N : ℕ} (f : Sp E N ≃ₗ[E] Sp E N) (v : Sp E N) (l : Fin N) :
    f v l = ∑ s, v s * f (twE s) l :=
  twApply_coord f.toLinearMap v l

theorem twAlg {E : Type} [Field E] {q y y' : E} {j : ℕ} {b b' k : ℤ} (hq : q ≠ 0) (hk : (b' : E) - b = q ^ (j + 1) * k) :
    q⁻¹ * (y' - y) = (q ^ j * y' - b') / q ^ (j + 1) - (q ^ j * y - b) / q ^ (j + 1) + k := by
  have hb : (b' : E) = b + q ^ (j + 1) * k := by linear_combination hk
  rw [hb]
  field_simp
  ring

open Classical in

def twDig (P : HeightOneSpectrum (𝓞 X.E)) (N : ℕ) (y : X.E) : ℤ :=
  if h : ∃ b : ℤ, IntAt P ((y - b) / (qOf P : X.E) ^ N) then h.choose else 0

theorem twDig_spec {P : HeightOneSpectrum (𝓞 X.E)} (hq : (qOf P).Prime) (hu : ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2) (N : ℕ)
    {y : X.E} (hy : IntAt P y) : IntAt P ((y - twDig P N y) / (qOf P : X.E) ^ N) := by
  have hex := twRes_exists hq hu N y hy
  unfold twDig
  rw [dif_pos hex]
  exact hex.choose_spec

theorem twFin_bdd (sharp : Bool) {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (hd : TwDegOne X P) :
    {D : Quotient (twSetoid (Pr := Pr) (R := R) sharp j P) | ∃ h, Quotient.mk _ h = D ∧ TwBdd (Pr := Pr) j P h}.Finite := by
  obtain ⟨hq, hu⟩ := hd
  have hq0 : (qOf P : X.E) ≠ 0 := by exact_mod_cast hq.ne_zero
  have : NeZero (qOf P ^ (j + 1)) := ⟨pow_ne_zero _ hq.ne_zero⟩
  let rep : Quotient (twSetoid (Pr := Pr) (R := R) sharp j P) → AutY X R j := fun D =>
    @Classical.epsilon _ ⟨1⟩ (fun h => Quotient.mk _ h = D ∧ TwBdd (Pr := Pr) j P h)
  let Φ : AutY X R j → (Fin (R.N j + cOf R j) → Fin (R.N j + cOf R j) → ZMod (qOf P ^ (j + 1))) := fun h l s =>
    ((twDig P (j + 1) ((qOf P : X.E) ^ j * h (twE s) l) : ℤ) : ZMod (qOf P ^ (j + 1)))
  refine Set.Finite.of_finite_image (f := fun D => Φ (rep D)) (Set.toFinite _) ?_
  intro D hD D' hD' heq
  have s1 : Quotient.mk _ (rep D) = D ∧ TwBdd (Pr := Pr) j P (rep D) := Classical.epsilon_spec hD
  have s2 : Quotient.mk _ (rep D') = D' ∧ TwBdd (Pr := Pr) j P (rep D') := Classical.epsilon_spec hD'
  rw [← s1.1, ← s2.1]
  apply Quotient.sound

  have hbI : ∀ h : AutY X R j, TwBdd (Pr := Pr) j P h → ∀ v, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (h⁻¹ v l) := fun h hb v hv => by
    have := (hb v ((twLamQ_mem hP v).2 hv)).1
    exact (twLamQ_mem hP _).1 this
  have hqI : ∀ h : AutY X R j, TwBdd (Pr := Pr) j P h → ∀ s l, IntAt P ((qOf P : X.E) ^ j * h (twE s) l) := fun h hb s l => by
    have := (hb (twE s) ((twLamQ_mem hP _).2 (fun l => twE_int s l))).2
    have h2 := (twLamQ_mem hP _).1 this l
    simpa [Pi.smul_apply, smul_eq_mul] using h2
  have hcl : ∀ s l, IntAt P ((qOf P : X.E)⁻¹ * (rep D' (twE s) l - rep D (twE s) l)) := fun s l => by
    have hy := hqI _ s1.2 s l
    have hy' := hqI _ s2.2 s l
    have d1 := twDig_spec hq hu (j + 1) hy
    have d2 := twDig_spec hq hu (j + 1) hy'
    have hE := congrFun (congrFun heq l) s
    have hdv := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hE
    obtain ⟨k, hk⟩ := hdv
    have hk' : ((twDig P (j + 1) ((qOf P : X.E) ^ j * rep D' (twE s) l) : ℤ) : X.E) -
        ((twDig P (j + 1) ((qOf P : X.E) ^ j * rep D (twE s) l) : ℤ) : X.E) = (qOf P : X.E) ^ (j + 1) * k := by
      have := congrArg (fun z : ℤ => (z : X.E)) hk
      push_cast at this
      exact this
    have e := twAlg (y := rep D (twE s) l) (y' := rep D' (twE s) l) hq0 hk'
    rw [e]
    exact (ciIntAt_sub d2 d1).add (ciIntAt_intCast k)
  have he : ∀ v, (∀ l, IntAt P (v l)) → ∀ l, IntAt P ((qOf P : X.E)⁻¹ * (rep D' v l - rep D v l)) := fun v hv l => by
    rw [twApply_coordE (rep D') v l, twApply_coordE (rep D) v l, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply twIntAt_sum
    intro s
    have e : (qOf P : X.E)⁻¹ * (v s * rep D' (twE s) l - v s * rep D (twE s) l) =
        v s * ((qOf P : X.E)⁻¹ * (rep D' (twE s) l - rep D (twE s) l)) := by ring
    rw [e]
    exact (hv s).mul (hcl s l)
  refine ⟨1, (Loc.R1 X.E (R.N j) (cOf R j)).one_mem, (rep D)⁻¹ * rep D',
    twJ_of_close sharp hP hq0 (rep D) (rep D') (hbI _ s1.2) (hbI _ s2.2) he, by simp⟩

end TwFin

section TwFin2

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem finiteness_bounded_holds (sharp : Bool) : TwFinQ X Pr R sharp := fun _ _ hP hd => twFin_bdd sharp hP hd

end TwFin2

end Formalism.L2.Col
