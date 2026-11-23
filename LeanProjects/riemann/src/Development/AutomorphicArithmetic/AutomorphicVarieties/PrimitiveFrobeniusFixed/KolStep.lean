import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.DerBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmProd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω]

private def Pr (A : ValuationSubring Ω) (u : Ω) : Prop := A.valuation (u - 1) < 1

private theorem pr_val {A : ValuationSubring Ω} {u : Ω} (h : Pr A u) : A.valuation u = 1 := by
  have := Valuation.map_one_add_of_lt A.valuation h
  rwa [add_sub_cancel] at this

private theorem pr_one (A : ValuationSubring Ω) : Pr A 1 := by simp [Pr]

private theorem pr_mul {A : ValuationSubring Ω} {u v : Ω} (hu : Pr A u) (hv : Pr A v) : Pr A (u * v) := by
  have e : u * v - 1 = u * (v - 1) + (u - 1) := by ring
  unfold Pr
  rw [e]
  refine Valuation.map_add_lt _ ?_ hu
  rw [map_mul, pr_val hu, one_mul]
  exact hv

private theorem pr_of_sub {A : ValuationSubring Ω} {u v : Ω} (hv : A.valuation v = 1) (h : A.valuation (u - v) < 1) :
    Pr A (u / v) := by
  have h0 : v ≠ 0 := fun h0 => by simp [h0] at hv
  have e : u / v - 1 = (u - v) / v := by field_simp
  unfold Pr
  rw [e, map_div₀, hv, div_one]
  exact h

private theorem pr_div {A : ValuationSubring Ω} {u v : Ω} (hu : Pr A u) (hv : Pr A v) : Pr A (u / v) := by
  refine pr_of_sub (pr_val hv) ?_
  have := Valuation.map_sub_lt A.valuation hu hv
  rwa [sub_sub_sub_cancel_right] at this

private theorem pr_pow {A : ValuationSubring Ω} {u : Ω} (hu : Pr A u) (k : ℕ) : Pr A (u ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact pr_one A
  | succ k ih => rw [pow_succ]; exact pr_mul ih hu

variable [Algebra ℚ Ω]

private theorem der_div (τ : ℕ → G ℚ Ω) (L : List ℕ) (u v : Ω) : der τ L (u / v) = der τ L u / der τ L v := by
  induction L with
  | nil => rfl
  | cons q L ih => simp only [der, ih, der1, map_div₀, div_pow, Finset.prod_div_distrib]

private theorem der_pow (τ : ℕ → G ℚ Ω) (L : List ℕ) (u : Ω) (k : ℕ) : der τ L (u ^ k) = der τ L u ^ k := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    simp only [der, ih, der1, map_pow, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, ← pow_mul, mul_comm]

private theorem der_prod (τ : ℕ → G ℚ Ω) (L : List ℕ) (S : Finset ℕ) (f : ℕ → Ω) :
    der τ L (∏ i ∈ S, f i) = ∏ i ∈ S, der τ L (f i) := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    simp only [der, ih, der1, map_prod, ← Finset.prod_pow]
    exact Finset.prod_comm

private theorem fix_mul {m q : ℕ} (h : q.Coprime m) {g : G ℚ Ω} (hm : g ∈ fixMu ℚ Ω m) (hq : g ∈ fixMu ℚ Ω q)
    (h0 : m * q ≠ 0) : g ∈ fixMu ℚ Ω (m * q) := by
  intro x hx
  have hx0 : x ≠ 0 := fun hh => by simp [hh, h0] at hx
  have h1 : (g x / x) ^ q = 1 := by
    rw [div_pow, ← map_pow, hm (x ^ q) (by rw [← pow_mul, mul_comm, hx]), div_self (pow_ne_zero _ hx0)]
  have h2 : (g x / x) ^ m = 1 := by
    rw [div_pow, ← map_pow, hq (x ^ m) (by rw [← pow_mul, hx]), div_self (pow_ne_zero _ hx0)]
  have h3 : (g x / x) ^ Nat.gcd q m = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [h, pow_one] at h3
  exact (div_eq_one_iff_eq hx0).1 h3

private theorem gen_pow {q : ℕ} (hq : q.Prime) {τ : G ℚ Ω} (h : GenAt q τ) : τ ^ (q - 1) ∈ fixMu ℚ Ω q := by
  obtain ⟨b, -, hb⟩ := h
  intro x hx
  have h1 : ∀ j : ℕ, (τ ^ j) x = x ^ (b : ZMod q).val ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hb x hx, ← pow_mul, pow_succ']
  have h2 : (b : ZMod q).val ^ (q - 1) ≡ 1 [MOD q] := by
    rw [← Nat.totient_prime hq]
    exact Nat.ModEq.pow_totient (ZMod.val_coe_unit_coprime b)
  show (τ ^ (q - 1)) x = x
  rw [h1, pow_eq_pow_mod _ hx, h2, ← pow_eq_pow_mod _ hx, pow_one]

variable [IsAlgClosure ℚ Ω]

private theorem over_smul (A : ValuationSubring Ω) (g : G ℚ Ω) (n : ℕ) : Over (g⁻¹ • A) n ↔ Over A n := by
  have := ((placeBasic Ω).2.2.2.2.2.2.2.2.2 (g⁻¹ • A) g).2.2.2.1 (n : Ω)
  rw [smul_inv_smul, map_natCast] at this
  exact this.symm

private theorem pr_gal {q : ℕ} {u : Ω} (h : ∀ A : ValuationSubring Ω, Over A q → Pr A u) (g : G ℚ Ω)
    (A : ValuationSubring Ω) (hA : Over A q) : Pr A (g u) := by
  have := ((placeBasic Ω).2.2.2.2.2.2.2.2.2 (g⁻¹ • A) g).2.2.2.1 (u - 1)
  rw [smul_inv_smul, map_sub, map_one] at this
  exact this.2 (h _ ((over_smul A g q).2 hA))

private theorem unit_gal {r : ℕ} {u : Ω} (h : ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) (g : G ℚ Ω)
    (A : ValuationSubring Ω) (hA : ¬ Over A r) : A.valuation (g u) = 1 := by
  have := ((placeBasic Ω).2.2.2.2.2.2.2.2.2 (g⁻¹ • A) g).2.2.2.2 u
  rw [smul_inv_smul] at this
  exact this.2 (h _ fun hh => hA ((over_smul A g r).1 hh))

private theorem pr_der {q : ℕ} (τ : ℕ → G ℚ Ω) (L : List ℕ) {u : Ω} (h : ∀ A : ValuationSubring Ω, Over A q → Pr A u) :
    ∀ A : ValuationSubring Ω, Over A q → Pr A (der τ L u) := by
  induction L with
  | nil => exact h
  | cons p L ih =>
    intro A hA
    rw [der, der1]
    exact Finset.prod_induction _ (Pr A) (fun _ _ => pr_mul) (pr_one A) fun i _ => pr_pow (pr_gal ih _ A hA) i

private theorem unit_opP {r M : ℕ} (hM : M ≠ 0) {Y : Ω} (h : ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (Y ^ M) = 1)
    (δ : G ℚ Ω) (a : ℕ) (A : ValuationSubring Ω) (hA : ¬ Over A r) : A.valuation (opP δ a Y) = 1 := by
  have h1 : ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation Y = 1 := fun A hA => by
    have := h A hA
    rw [map_pow] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hM).1 this
  rw [opP, map_div₀, map_pow, unit_gal h1 δ A hA, h1 A hA, one_pow, div_one]

end SlopeTestRemainingChoices

theorem UpperTheory.V.ML.kolStep :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l M F r a : ℕ) [NeZero M], F ≠ 0 → M ∣ F → r.Prime → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ →
    ∀ (x : ℕ → Ω) (s : ℕ → ℕ → ℕ), Sys l F r x s → ∀ (τ : ℕ → G ℚ Ω) (q : ℕ) (L : List ℕ), AdmL l F r (q :: L) → (∀ p ∈ q :: L, IsTau p (τ p)) →
    ∀ κ κ' : G ℚ Ω → ZMod M, IsKol M F L.prod ζ δ a (der τ L (x L.prod)) κ → IsKol M F (q :: L).prod ζ δ a (der τ (q :: L) (x (q :: L).prod)) κ' →
    ∀ A : ValuationSubring Ω, Over A q → ∀ t ∈ Ine (F := ℚ) A, (∀ w : Ω, w ^ q = 1 → t w = τ q w) → ∀ φ : G ℚ Ω, IsFrob (F := ℚ) A q φ →
    κ' t = -((s L.prod q : ZMod M) * κ φ) := by
  intro Ω _ _ _ l M F r a _ hF hMF hr ζ hζ δ hδ x s hs τ q L hL hτ κ κ' hκ hκ' A hA t ht htq φ hφ
  obtain ⟨-, -, -, pcop, pine, proot, pfrob, -⟩ := placeBasic Ω
  have hM : M ≠ 0 := NeZero.ne M
  obtain ⟨hadm', hn', -, -⟩ := isCrys_isDR_prod l F r (q :: L) hL
  have hL0 : AdmL l F r L := ⟨(List.nodup_cons.1 hL.1).2, fun p hp => hL.2 p (List.mem_cons_of_mem _ hp)⟩
  obtain ⟨hadm, hn, hcop, -⟩ := isCrys_isDR_prod l F r L hL0
  replace hcop := hcop q hL
  obtain ⟨hq, hqF, hqr, -⟩ := hL.2 q List.mem_cons_self
  have hτq := hτ q List.mem_cons_self
  rw [List.prod_cons] at hadm' hn' hκ'
  rw [der] at hκ'
  generalize L.prod = n at *
  have hcF : q.Coprime F := by
    have := hqF.gcd_eq
    rwa [Nat.gcd_one_left] at this
  have hcFn : q.Coprime (F * n) := hcF.mul_right hcop
  have hAr : ∀ B : ValuationSubring Ω, Over B q → ¬ Over B r := fun B hB =>
    pcop B q r ((Nat.coprime_primes hq hr).2 hqr) hB
  have hAFn : ¬ Over A (F * n) := pcop A q _ hcFn hA
  have hAM : ¬ Over A M := pcop A q _ (hcF.coprime_dvd_right hMF) hA
  have hFn : F * n ≠ 0 := mul_ne_zero hF hn
  have hN : F * (q * n) ≠ 0 := mul_ne_zero hF hn'
  have eN : F * (q * n) = F * n * q := by ring
  have hφP : Pows (F * n) q φ := pfrob A q _ φ hφ hAFn
  have hφF : φ ∈ fixMu ℚ Ω F := fun w hw => by
    rw [pfrob A q F φ hφ (pcop A q _ hcF hA) w hw, pow_eq_pow_mod _ hw, hqF, ← pow_eq_pow_mod _ hw, pow_one]
  have htFn : t ∈ fixMu ℚ Ω (F * n) := pine A _ hAFn ht
  have htF : t ∈ fixMu ℚ Ω F := fixMu_le ℚ Ω (dvd_mul_right F n) htFn
  have hτFn : τ q ∈ fixMu ℚ Ω (F * n) := hτq.1 _ hcFn.symm
  have htτ : (τ q)⁻¹ * t ∈ fixMu ℚ Ω (F * (q * n)) := by
    rw [eN]
    refine fix_mul hcFn (mul_mem (inv_mem hτFn) htFn) (fun w hw => ?_) (eN ▸ hN)
    rw [AlgEquiv.mul_apply, htq w hw]
    exact (τ q).symm_apply_apply w
  have hτN : τ q ^ (q - 1) ∈ fixMu ℚ Ω (F * (q * n)) := by
    rw [eN]
    exact fix_mul hcFn (pow_mem hτFn _) (gen_pow hq hτq.2) (eN ▸ hN)
  obtain ⟨y0, yfix, ycomm, yunit, -⟩ := derBasic Ω (F * n) r hFn τ L (x n) (hs.ne n hadm) (hs.fix n hadm)
  obtain ⟨w0, wfix, wcomm, wunit, -⟩ := derBasic Ω (F * (q * n)) r hN τ L (x (q * n)) (hs.ne _ hadm') (hs.fix _ hadm')
  replace yunit := yunit (hs.unit n hadm)
  replace wunit := wunit (hs.unit _ hadm')
  obtain ⟨u0, ufix, -, uunit, -, -, -, -, hstep⟩ :=
    derBasic Ω (F * (q * n)) r hN τ [q] (der τ L (x (q * n))) w0 wfix
  replace uunit := uunit wunit
  replace hstep := hstep q hq.one_le (wfix _ hτN)
  have hnrm : nrm q (τ q) (der τ L (x (q * n))) = (der τ L (x n) / φ⁻¹ (der τ L (x n))) ^ s n q := by
    have h1 := congrArg (der τ L) (hs.norm n q hq hadm' (τ q) hτFn hτq.2 φ hφP)
    rw [der_pow, der_div, ← ycomm, nrm, der_prod] at h1
    rw [← h1, nrm]
    exact Finset.prod_congr rfl fun i _ => wcomm _
  have hcong : ∀ B : ValuationSubring Ω, Over B q →
      Pr B (der τ L (x (q * n)) / φ⁻¹ (der τ L (x n)) ^ s n q) := by
    rw [ycomm, ← der_pow, ← der_div]
    refine pr_der τ L fun B hB => pr_of_sub ?_ (hs.cong n q hq hadm' φ hφP B hB)
    rw [map_pow, unit_gal (hs.unit n hadm) _ B (hAr B hB), one_pow]
  have hhom := (kolHom Ω M F n a hFn hMF ζ hζ δ hδ _ y0 yfix κ hκ).1
  have hthird := (kolHom Ω M F (q * n) a hN hMF ζ hζ δ hδ _ u0 ufix κ' hκ').2.2
  have hab := (galBasic Ω (F * n) hFn).2.2.2.2.2.1 _ yfix δ φ⁻¹
  simp only [der] at u0 ufix uunit hthird
  generalize der τ L (x (q * n)) = w at *
  generalize der τ L (x n) = y' at *
  generalize s n q = c at *
  obtain ⟨Y, hY, -⟩ := hκ'
  obtain ⟨Y', hY', hκ⟩ := hκ
  obtain ⟨z', -, hz', hκz⟩ := hκ φ⁻¹ (inv_mem hφF)
  obtain ⟨k, hk⟩ : M ∣ q - 1 := hMF.trans ((Nat.modEq_iff_dvd' hq.one_le).1 hqF.symm)
  have fy0 : φ⁻¹ y' ≠ 0 := (map_ne_zero _).2 y0
  have hty : t (der1 q (τ q) w) = τ q (der1 q (τ q) w) := by
    have := congrArg (τ q) (ufix _ htτ)
    rwa [← AlgEquiv.mul_apply, mul_inv_cancel_left] at this
  have hz : (w ^ k * z' ^ c) ^ M = t (der1 q (τ q) w) / der1 q (τ q) w := by
    rw [hty, hstep, hnrm, mul_pow, ← pow_mul, ← pow_mul, mul_comm k, ← hk, mul_comm c, pow_mul, hz', div_pow, div_pow]
    field_simp
  have hκt := hthird Y hY t htF _ hz
  have hPY : A.valuation (opP δ a Y) = 1 := unit_opP hM (hY ▸ uunit) δ a A (hAr A hA)
  have hPY' : ∀ B : ValuationSubring Ω, ¬ Over B r → B.valuation (opP δ a Y') = 1 := unit_opP hM (hY' ▸ yunit) δ a
  have hu : A.valuation (φ⁻¹ (opP δ a Y')) = 1 := unit_gal hPY' _ A (hAr A hA)
  have f1 : Pr A (t (opP δ a Y) / opP δ a Y) := pr_of_sub hPY (ht.2 _ hPY.le)
  have f2 : Pr A (opP δ a Y' / φ⁻¹ (opP δ a Y') ^ q) := by
    refine pr_of_sub (by rw [map_pow, hu, one_pow]) ?_
    have := hφ.2 _ hu.le
    rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this
  have f3 : Pr A (opP δ a (w / φ⁻¹ y' ^ c)) := pr_div (pr_gal hcong δ A hA) (pr_pow (hcong A hA) a)
  have huM : φ⁻¹ (opP δ a Y') ^ M = δ (φ⁻¹ y') / φ⁻¹ y' ^ a := by
    rw [← map_pow, opP, div_pow, ← map_pow, ← pow_mul, mul_comm a, pow_mul, hY', map_div₀, map_pow, hab]
  have z0 : z' ≠ 0 := fun h => by
    rw [h, zero_pow hM] at hz'
    exact div_ne_zero fy0 y0 hz'.symm
  have U0 : φ⁻¹ (opP δ a Y') ≠ 0 := fun h => by simp [h] at hu
  have P0 : opP δ a Y' ≠ 0 := (map_ne_zero _).1 U0
  have hUq : φ⁻¹ (opP δ a Y') ^ q = φ⁻¹ (opP δ a Y') * (δ (φ⁻¹ y') / φ⁻¹ y' ^ a) ^ k := by
    rw [← huM, ← pow_mul, ← hk, ← pow_succ', Nat.sub_add_cancel hq.one_le]
  have key : ζ ^ (κ' t).val / (ζ ^ (κ φ⁻¹).val) ^ c =
      t (opP δ a Y) / opP δ a Y * (opP δ a Y' / φ⁻¹ (opP δ a Y') ^ q) ^ c / opP δ a (w / φ⁻¹ y' ^ c) ^ k := by
    rw [hκt, hκz, hUq]
    generalize t (opP δ a Y) / opP δ a Y = T
    generalize φ⁻¹ (opP δ a Y') = U at *
    generalize opP δ a Y' = V at *
    generalize φ⁻¹ y' = v at *
    have d1 : δ w ≠ 0 := (map_ne_zero _).2 w0
    have d2 : δ z' ≠ 0 := (map_ne_zero _).2 z0
    have d3 : δ v ≠ 0 := (map_ne_zero _).2 fy0
    simp only [opP, map_mul, map_pow, map_div₀, div_pow, mul_pow, ← pow_mul]
    field_simp
    ring
  have hpr := pr_div (pr_mul f1 (pr_pow f2 c)) (pr_pow f3 k)
  rw [← key] at hpr
  have hζp : ∀ j : ℕ, (ζ ^ j) ^ M = 1 := fun j => by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h1 := proot A M _ hAM (by rw [div_pow, ← pow_mul ζ _ c, hζp, hζp, div_one]) hpr
  rw [← pow_mul, div_eq_one_iff_eq (pow_ne_zero _ (hζ.ne_zero hM)), pow_eq_pow_mod (_ * _) hζ.pow_eq_one] at h1
  have h2 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (Nat.pos_of_ne_zero hM)) h1
  have h3 := congrArg (Nat.cast : ℕ → ZMod M) h2
  rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h3
  have h4 := hhom 1 (one_mem _) 1 (one_mem _)
  have h5 := hhom φ hφF φ⁻¹ (inv_mem hφF)
  rw [mul_one] at h4
  rw [mul_inv_cancel] at h5
  rw [h3]
  linear_combination (c : ZMod M) * (-h4 - h5)
