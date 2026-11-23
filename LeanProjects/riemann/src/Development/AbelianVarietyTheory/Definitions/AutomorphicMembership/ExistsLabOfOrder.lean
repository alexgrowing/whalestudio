import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.CyclotomicNorms Polynomial Module

namespace GlobalTheory.WeilDeligne.LabModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable {g : ℕ} [Fact g.Prime]

private theorem exists_rep_tameEig_eq {h : IsPlaceOver A w} (x : WD h) :
    ∃ (n : ℕ) (b : WDRep h (Fin n → ℂ)), ∀ δ : G E Ω, WD.tameEig x δ = WD.tameEig (WD.mk b) δ := by
  induction x using Quotient.inductionOn with
  | h a =>
    refine ⟨a.1, a.2, fun δ => ?_⟩
    show (WD.inePol (WD.lpTame ⟦a⟧) δ).roots = (WD.inePol (WD.lpTame (WD.mk a.2)) δ).roots
    rw [WD.lpTame_mk]
    rfl

theorem lab_mul_wild {h : IsPlaceOver A w} {τ : Fbar g →* ℂ} {γ u : G E Ω}
    (H : TeichmullerInertiaLabelCondition A w τ γ) (hu : u ∈ Wild E A) (x : WD h) :
    WD.lab τ (γ * u) x = WD.lab τ γ x := by
  have hγ : γ ∈ Ine (F := E) A := H.2.1
  have hu' : u ∈ Ine (F := E) A := Wild_le_Ine hu
  have H' : TeichmullerInertiaLabelCondition A w τ (γ * u) := ⟨H.1, mul_mem hγ hu', H.2.2⟩
  rw [WD.lab_eq_iff H']
  refine ⟨WD.lab_monic _ _ _, ?_⟩
  rw [WD.map_rootsBar_lab H]
  obtain ⟨n, b, hb⟩ := exists_rep_tameEig_eq x
  have hγW : γ ∈ Weil h := Ine_le_Weil h hγ
  have huW : u ∈ Weil h := Ine_le_Weil h hu'
  rw [hb, hb, WD.tameEig_mk b hγW, WD.tameEig_mk b (mul_mem hγW huW)]
  have e : (⟨γ * u, mul_mem hγW huW⟩ : Weil h) = ⟨γ, hγW⟩ * ⟨u, huW⟩ := rfl
  rw [e, map_mul, b.tamePart_ρ_of_wild (σ := ⟨u, huW⟩) hu, mul_one]

private theorem tameEig_eq_tameEig_mk_of_rep {h : IsPlaceOver A w} (x : WD h) :
    ∃ (n : ℕ) (b : WDRep h (Fin n → ℂ)), ∀ δ : G E Ω, WD.tameEig x δ = WD.tameEig (WD.mk b) δ := by
  induction x using Quotient.inductionOn with
  | h a =>
    refine ⟨a.1, a.2, fun δ => ?_⟩
    show (WD.inePol (WD.lpTame ⟦a⟧) δ).roots = (WD.inePol (WD.lpTame (WD.mk a.2)) δ).roots
    rw [WD.lpTame_mk]
    rfl

private theorem roots_charpoly_pow_eq_map_pow' {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (r : ℕ) :
    (f ^ r).charpoly.roots = f.charpoly.roots.map (· ^ r) := by
  set B := Module.finBasis ℂ V
  have hm : ∀ k : ℕ, LinearMap.toMatrix B B (f ^ k) = (LinearMap.toMatrix B B f) ^ k := by
    intro k
    induction k with
    | zero => simp [LinearMap.toMatrix_one]
    | succ k ih => rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih]
  rw [← LinearMap.charpoly_toMatrix (f ^ r) B, ← LinearMap.charpoly_toMatrix f B, hm]
  exact GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ _ r _

theorem lab_pow {h : IsPlaceOver A w} {τ : Fbar g →* ℂ} {γ : G E Ω}
    (H : TeichmullerInertiaLabelCondition A w τ γ) (x : WD h) : WD.lab τ (γ ^ g) x = WD.lab τ γ x := by
  have hγ : γ ∈ Ine (F := E) A := H.2.1
  have H' : TeichmullerInertiaLabelCondition A w τ (γ ^ g) := ⟨H.1, pow_mem hγ g, H.2.2⟩
  rw [WD.lab_eq_iff H']
  refine ⟨WD.lab_monic _ _ _, ?_⟩
  rw [WD.map_rootsBar_lab H]
  have hmap := WD.tameEig_map_pow x hγ
  rw [H.1] at hmap
  obtain ⟨n, b, hb⟩ := tameEig_eq_tameEig_mk_of_rep x
  simp only [hb] at hmap ⊢
  have hγW : γ ∈ Weil h := Ine_le_Weil h hγ
  rw [WD.tameEig_mk b (pow_mem hγW g)]
  have e : (⟨γ ^ g, pow_mem hγW g⟩ : Weil h) = ⟨γ, hγW⟩ ^ g := by ext; simp
  rw [e, map_pow, roots_charpoly_pow_eq_map_pow', ← WD.tameEig_mk b hγW]
  exact hmap.symm

private theorem exists_wild_sqrtChar_ne_one_of_normV_two (h : IsPlaceOver A w) (hw : normV w = 2) {ϖ : 𝓞 E}
    (h1 : ϖ ∈ w.asIdeal) (h2 : ϖ ∉ w.asIdeal ^ 2) {x : Ω} (hx : x ^ 2 = algebraMap E Ω (ϖ : E)) :
    ∃ σ : Weil h, (σ : G E Ω) ∈ Wild E A ∧ sqrtChar h hx σ ≠ 1 := by
  by_contra hne
  push_neg at hne
  obtain ⟨γ', hγ'⟩ := GlobalTheory.MemTame.exists_tameGenAt E Ω w A h
  obtain ⟨σ0, hσ0I, hσ0x⟩ :=
    GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne E Ω A w h 2 Nat.prime_two ϖ h1 h2 x hx
  have hγ1 : sqrtChar h hx (ineIncl h ⟨γ', hγ'.1⟩) ≠ 1 := by
    intro hc
    have := IsSmooth.eq_one_of_tameGenAt (isSmooth_sqrtChar h hx) hγ' hc hne ⟨σ0, hσ0I⟩
    rw [sqrtChar_eq_one_iff, coe_ineIncl] at this
    exact hσ0x this
  have hrel := tame_relation (A := A) hγ'.1 (isFrob_frob (h := h))
  have key := hne ((ineIncl h ⟨γ', hγ'.1⟩ ^ normV w)⁻¹ *
    (frob h * ineIncl h ⟨γ', hγ'.1⟩ * (frob h)⁻¹)) (by simpa using hrel)
  rw [map_mul, map_inv, map_pow, map_mul, map_mul, map_inv, hw,
    mul_right_comm (sqrtChar h hx (frob h)), mul_inv_cancel, one_mul, pow_two, mul_inv_rev,
    mul_assoc, inv_mul_cancel, mul_one, inv_eq_one] at key
  exact hγ1 key

theorem lab_sqrtChar_two {h : IsPlaceOver A w} {τ : Fbar 2 →* ℂ} {γ : G E Ω}
    (H : TeichmullerInertiaLabelCondition A w τ γ) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {x : Ω} (hx : x ^ 2 = algebraMap E Ω (ϖ : E)) :
    ¬ WD.tame (WD.lpOfChar h _ (isSmooth_sqrtChar h hx)) ∧
      WD.lab τ γ (WD.lpOfChar h _ (isSmooth_sqrtChar h hx)) = 1 := by
  have hd : WD.lpDim (WD.lpOfChar h _ (isSmooth_sqrtChar h hx)) = 1 := by
    unfold WD.lpOfChar WD.lpDim WD.mk WD.std
    simp
  obtain ⟨σ, hσW, hσ⟩ := exists_wild_sqrtChar_ne_one_of_normV_two h H.1 h1 h2 hx
  refine ⟨?_, WD.lab_lpOfChar_of_wild τ γ (isSmooth_sqrtChar h hx) hσW hσ⟩
  unfold WD.lpOfChar
  rw [WD.tame_mk]
  unfold WDRep.Tame WDRep.ofChars
  intro ht
  have e := congrFun (LinearMap.congr_fun (ht σ hσW) (fun _ => (1 : ℂ))) default
  simp [diagEnd_apply] at e
  exact hσ e

theorem eq_one_of_cong (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hc : l.Coprime g)
    {u : Ω} (hu : u ^ l = 1) (h1 : A.valuation (u - 1) < 1) : u = 1 := by
  have hg : g.Prime := Fact.out
  by_contra hne
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [Nat.Coprime, Nat.gcd_zero_left] at hc
    exact hg.ne_one hc
  have hv : A.valuation u ≤ 1 := by
    have := A.valuation.map_add (u - 1) 1
    rw [sub_add_cancel, map_one] at this
    exact this.trans (max_le h1.le le_rfl)
  have hs : ∑ i ∈ Finset.range l, u ^ i = 0 := by
    have e := geom_sum_mul u l
    rw [hu, sub_self] at e
    exact (mul_eq_zero.mp e).resolve_right (sub_ne_zero.mpr hne)
  have hlv : A.valuation (l : Ω) < 1 := by
    have e : (l : Ω) = -∑ i ∈ Finset.range l, (u ^ i - 1) := by
      rw [Finset.sum_sub_distrib, hs]
      simp
    rw [e, Valuation.map_neg]
    exact Valuation.map_sum_lt _ one_ne_zero fun i _ => by
      simpa using GlobalTheory.WeilDeligne.cong_pow hv (by simp) h1 i
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hw]
    have : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by
      rw [show Nat.card (𝓞 E ⧸ w.asIdeal) = normV w from rfl, hw]
      exact hg.ne_zero)
    rw [show normV w = Nat.card (𝓞 E ⧸ w.asIdeal) from rfl, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have hlw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    intro hl
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hc).map (Int.castRingHom (𝓞 E))
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      rw [← hab]
      simp only [eq_intCast, Int.cast_natCast]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hl) (w.asIdeal.mul_mem_left b hgw)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := GlobalTheory.InertiaMovesRoot.val_eq_one_of_notMem h hlw
  have e : algebraMap E Ω ((((l : ℕ) : 𝓞 E)) : E) = (l : Ω) := by simp
  rw [e] at this
  exact (ne_of_lt hlv) this

theorem weil_fix (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hl : l ∣ g - 1)
    (σ : Weil h) {ζ : Ω} (hζ : ζ ^ l = 1) : (σ : G E Ω) ζ = ζ := by
  have hg : g.Prime := Fact.out
  have hg2 := hg.two_le
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hl
    omega
  have hlg : l.Coprime g := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg).2 fun hd => ?_)
    have := Nat.le_of_dvd (by omega) (hd.trans hl)
    omega
  have key : ∀ (y : Ω), y ^ l = 1 → ∀ k : ℕ, y ^ (g ^ k) = y := by
    intro y hy k
    have hpos : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
    have hd : l ∣ g ^ k - 1 := by
      have := ((Nat.modEq_iff_dvd' (by omega : 1 ≤ g)).mpr hl).pow k
      rw [one_pow] at this
      exact (Nat.modEq_iff_dvd' hpos).mp this
    obtain ⟨m, hm⟩ := hd
    have : g ^ k = l * m + 1 := by omega
    rw [this, pow_succ, pow_mul, hy, one_pow, one_mul]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0] at hζ
    exact zero_ne_one hζ
  have hσζ : ((σ : G E Ω) ζ) ^ l = 1 := by rw [← map_pow, hζ, map_one]
  have hv1 : A.valuation ζ = 1 := by
    have e : A.valuation ζ ^ l = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hlt | heq | hgt
    · exfalso
      have : A.valuation ζ ^ l < 1 := by
        exact pow_lt_one' hlt hl0
      exact (ne_of_lt this) e
    · exact heq
    · exfalso
      have : 1 < A.valuation ζ ^ l := by
        exact one_lt_pow' hgt hl0
      exact (ne_of_gt this) e
  obtain ⟨a, b, hab⟩ := (mem_Weil h).mp σ.2
  have hc := hab.2 ζ hv1.le
  rw [hw, key _ hσζ, key _ hζ] at hc
  have hσ0 : (σ : G E Ω) ζ ≠ 0 := (_root_.map_ne_zero _).2 hζ0
  have hq : (σ : G E Ω) ζ / ζ = 1 := by
    refine eq_one_of_cong h hw hlg (by rw [div_pow, hσζ, hζ, div_one]) ?_
    rw [show (σ : G E Ω) ζ / ζ - 1 = ((σ : G E Ω) ζ - ζ) / ζ by field_simp, map_div₀, hv1, div_one]
    exact hc
  exact (div_eq_one_iff_eq hζ0).mp hq

def kummer (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hl : l ∣ g - 1) (ι : Ω →+* ℂ)
    {x : Ω} (h0 : x ≠ 0) {a : E} (hx : x ^ l = algebraMap E Ω a) : Weil h →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun σ => ι ((σ : G E Ω) x / x)
      map_one' := by simp [div_self h0]
      map_mul' := fun σ σ' => by
        have h1 : ((σ' : G E Ω) x / x) ^ l = 1 := by
          rw [div_pow, ← map_pow, hx, AlgEquiv.commutes, ← hx, div_self (pow_ne_zero _ h0)]
        have h2 := weil_fix h hw hl σ h1
        have h3 : (σ : G E Ω) x ≠ 0 := (_root_.map_ne_zero _).2 h0
        rw [← map_mul, ← h2, map_div₀ (σ : G E Ω)]
        congr 1
        show (σ : G E Ω) ((σ' : G E Ω) x) / x = _
        field_simp }

theorem kummer_apply (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hl : l ∣ g - 1)
    (ι : Ω →+* ℂ) {x : Ω} (h0 : x ≠ 0) {a : E} (hx : x ^ l = algebraMap E Ω a) (σ : Weil h) :
    (kummer h hw hl ι h0 hx σ : ℂ) = ι ((σ : G E Ω) x / x) := rfl

theorem kummer_eq_one_iff (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hl : l ∣ g - 1)
    (ι : Ω →+* ℂ) {x : Ω} (h0 : x ≠ 0) {a : E} (hx : x ^ l = algebraMap E Ω a) (σ : Weil h) :
    kummer h hw hl ι h0 hx σ = 1 ↔ (σ : G E Ω) x = x := by
  rw [← Units.val_eq_one, kummer_apply, ← map_one ι, ι.injective.eq_iff, div_eq_one_iff_eq h0]

theorem isSmooth_kummer (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hl : l ∣ g - 1)
    (ι : Ω →+* ℂ) {x : Ω} (h0 : x ≠ 0) {a : E} (hx : x ^ l = algebraMap E Ω a) :
    IsSmooth (kummer h hw hl ι h0 hx) := by
  have hxalg : IsIntegral E x := Algebra.IsIntegral.isIntegral x
  have : FiniteDimensional E (IntermediateField.adjoin E {x}) := IntermediateField.adjoin.finiteDimensional hxalg
  have hle : ((IntermediateField.adjoin E {x})).fixingSubgroup ≤ MulAction.stabilizer (G E Ω) x := fun σ hσ =>
    MulAction.mem_stabilizer_iff.mpr ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ x
      (IntermediateField.subset_adjoin E {x} rfl))
  have hopen : IsOpen (MulAction.stabilizer (G E Ω) x : Set (G E Ω)) :=
    Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen _)
  unfold IsSmooth
  have e : {σ : Ine (F := E) A | kummer h hw hl ι h0 hx (ineIncl h σ) = 1} =
      Subtype.val ⁻¹' (MulAction.stabilizer (G E Ω) x : Set (G E Ω)) := by
    ext σ
    simp [kummer_eq_one_iff, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  rw [e]
  exact hopen.preimage continuous_subtype_val

theorem exists_lab_of_order {h : IsPlaceOver A w} {τ : Fbar g →* ℂ} {γ : G E Ω}
    (H : TeichmullerInertiaLabelCondition A w τ γ) (hγ : TameGenAt A γ) {l : ℕ} (hp : l.Prime) (hl : l ∣ g - 1) :
    ∃ (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (hχ' : IsSmooth χ⁻¹) (c : ZMod g), orderOf c = l ∧
      WD.lab τ γ (WD.lpOfChar h χ hχ) = X - C c ∧
      WD.lab τ γ (WD.lpOfChar h χ⁻¹ hχ') = X - C c⁻¹ := by
  have hg : g.Prime := Fact.out
  have hg2 := hg.two_le
  have hw : normV w = g := H.1
  have hlg : l.Coprime g := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg).2 fun hd => ?_)
    have := Nat.le_of_dvd (by omega) (hd.trans hl)
    omega
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 := by
    obtain ⟨ϖ, hϖ1, hϖ2⟩ :=
      SetLike.exists_of_lt (Ideal.pow_succ_lt_pow w.ne_bot 1)
    exact ⟨ϖ, by simpa using hϖ1, by simpa using hϖ2⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) hp.pos
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro e
    apply h2
    have : ϖ = 0 := by exact_mod_cast e
    rw [this]
    exact Ideal.zero_mem _
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero, eq_comm, map_eq_zero] at hx
    exact hϖ0 hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  letI : Algebra E ℂ := φ.toAlgebra
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let ι : Ω →+* ℂ := (IsAlgClosed.lift : Ω →ₐ[E] ℂ).toRingHom
  have hχ : IsSmooth (kummer h hw hl ι hx0 hx) := isSmooth_kummer h hw hl ι hx0 hx
  have hχ' : IsSmooth (kummer h hw hl ι hx0 hx)⁻¹ := by
    unfold IsSmooth at hχ ⊢
    simpa using hχ
  have hσx : ∀ σ : Weil h, ((σ : G E Ω) x) ^ l = x ^ l := fun σ => by
    rw [← map_pow, hx, AlgEquiv.commutes]
  have htame : ∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → kummer h hw hl ι hx0 hx σ = 1 := by
    intro σ hσ
    rw [kummer_eq_one_iff]
    have hq : (σ : G E Ω) x / x = 1 := by
      refine eq_one_of_cong h hw hlg (by rw [div_pow, hσx σ, div_self (pow_ne_zero _ hx0)]) ?_
      exact (mem_Wild.mp hσ) x hx0
    exact (div_eq_one_iff_eq hx0).mp hq
  have htame' : ∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → (kummer h hw hl ι hx0 hx)⁻¹ σ = 1 :=
    fun σ hσ => by rw [MonoidHom.inv_apply, htame σ hσ, inv_one]
  have hγW : γ ∈ Weil h := Ine_le_Weil h H.2.1
  have hγx : kummer h hw hl ι hx0 hx ⟨γ, hγW⟩ ≠ 1 := by
    intro hc
    obtain ⟨σ0, hσ0I, hσ0x⟩ :=
      GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne E Ω A w h l hp ϖ h1 h2 x hx
    have := IsSmooth.eq_one_of_tameGenAt hχ hγ hc htame ⟨σ0, hσ0I⟩
    rw [kummer_eq_one_iff, coe_ineIncl] at this
    exact hσ0x this
  have htχ : WD.tame (WD.lpOfChar h _ hχ) := by
    unfold WD.lpOfChar
    rw [WD.tame_mk]
    unfold WDRep.Tame WDRep.ofChars
    intro σ hσ
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [diagEnd_apply, htame σ hσ]
  have hd : WD.lpDim (WD.lpOfChar h _ hχ) = 1 := by
    unfold WD.lpOfChar WD.lpDim WD.mk WD.std
    simp
  have hdeg : (WD.lab τ γ (WD.lpOfChar h _ hχ)).natDegree = 1 := by
    rw [(WD.natDegree_lab_eq_iff H _).mpr htχ, hd]
  obtain ⟨c, hf⟩ : ∃ c : ZMod g, WD.lab τ γ (WD.lpOfChar h _ hχ) = X - C c :=
    ⟨-(WD.lab τ γ (WD.lpOfChar h _ hχ)).coeff 0, by
      conv_lhs => rw [(WD.lab_monic τ γ _).eq_X_add_C hdeg]
      simp [sub_eq_add_neg]⟩
  have hc := (WD.lab_lpOfChar_eq_iff H hχ htame c).mp hf
  have hζ : ((kummer h hw hl ι hx0 hx ⟨γ, hγW⟩ : ℂˣ) : ℂ) ^ l = 1 := by
    rw [kummer_apply, ← map_pow, div_pow, hσx, div_self (pow_ne_zero _ hx0), map_one]
  have hτinj := IsTeich.injective H.2.2
  have halg := (algebraMap (ZMod g) (Fbar g)).injective
  have hcl : c ^ l = 1 := by
    apply halg
    apply hτinj
    rw [map_pow, map_pow, hc, hζ, map_one, map_one]
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [map_one, map_one] at hc
    exact hγx (Units.val_eq_one.mp hc.symm)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcl
    exact zero_ne_one hcl
  have : Fact l.Prime := ⟨hp⟩
  have hinv : τ (algebraMap (ZMod g) (Fbar g) c⁻¹) =
      (((kummer h hw hl ι hx0 hx)⁻¹ ⟨γ, hγW⟩ : ℂˣ) : ℂ) := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, ← hc, map_inv₀]
    have ha : algebraMap (ZMod g) (Fbar g) c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ ha, map_one])
  exact ⟨_, hχ, hχ', c, orderOf_eq_prime hcl hc1, hf,
    (WD.lab_lpOfChar_eq_iff H hχ' htame' c⁻¹).mpr hinv⟩

theorem exists_rat_seven [Fact (Nat.Prime 7)] (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K] :
    ∃ (v : HeightOneSpectrum (𝓞 ℚ)) (B : ValuationSubring K) (hB : IsPlaceOver B v)
      (τ : Fbar 7 →* ℂ) (γ : G ℚ K) (χ : Weil hB →* ℂˣ) (hχ : IsSmooth χ) (hχ' : IsSmooth χ⁻¹),
      TameGenAt B γ ∧ WD.lab τ γ (WD.lpOfChar hB χ hχ) ≠ WD.lab τ γ (WD.lpOfChar hB χ⁻¹ hχ') ∧
      WD.lab τ γ (WD.lpSum (WD.lpOfChar hB χ hχ) (WD.lpOfChar hB χ⁻¹ hχ')) = X ^ 2 + X + 1 := by
  obtain ⟨v, hv⟩ := exists_normV_eq 7 Fact.out
  obtain ⟨B, hB⟩ := exists_isPlaceOver K v
  obtain ⟨τ, γ, hγ, H⟩ := exists_tameInertiaSetting hB hv
  obtain ⟨χ, hχ, hχ', c, hc, e1, e2⟩ :=
    exists_lab_of_order H hγ (l := 3) Nat.prime_three (by norm_num)
  have h3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hc
    norm_num at hc
  have hq : c ^ 2 + c + 1 = 0 := by
    have : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
  have hi : c⁻¹ = c ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← pow_succ']
    exact h3
  refine ⟨v, B, hB, τ, γ, χ, hχ, hχ', hγ, ?_, ?_⟩
  · rw [e1, e2, hi]
    intro e
    have e' : c = c ^ 2 := C_injective (sub_right_injective e)
    have : c * (c - 1) = 0 := by linear_combination -e'
    rcases mul_eq_zero.mp this with h0 | h0
    · rw [h0] at h3
      norm_num at h3
    · exact hc1 (sub_eq_zero.mp h0)
  · rw [WD.lab_lpSum, e1, e2, hi]
    have f1 : c + c ^ 2 = -1 := by linear_combination hq
    have f2 : c * c ^ 2 = 1 := by rw [← pow_succ']; exact h3
    calc (X - C c) * (X - C (c ^ 2)) = X ^ 2 - C (c + c ^ 2) * X + C (c * c ^ 2) := by
          simp only [C_add, C_mul]
          ring
      _ = X ^ 2 + X + 1 := by
          rw [f1, f2]
          simp only [map_neg, map_one]
          ring

theorem exists_rat_two (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K] :
    ∃ (v : HeightOneSpectrum (𝓞 ℚ)) (B : ValuationSubring K) (hB : IsPlaceOver B v)
      (τ : Fbar 2 →* ℂ) (γ : G ℚ K) (L : WD hB), TameGenAt B γ ∧ TeichmullerInertiaLabelCondition B v τ γ ∧
      L.lpDim = 1 ∧ ¬ L.tame ∧ WD.lab τ γ L = 1 := by
  obtain ⟨v, hv⟩ := exists_normV_eq 2 Nat.prime_two
  obtain ⟨B, hB⟩ := exists_isPlaceOver K v
  obtain ⟨τ, γ, hγ, H⟩ := exists_tameInertiaSetting hB hv
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ : 𝓞 ℚ, ϖ ∈ v.asIdeal ∧ ϖ ∉ v.asIdeal ^ 2 := by
    obtain ⟨ϖ, hϖ1, hϖ2⟩ :=
      SetLike.exists_of_lt (Ideal.pow_succ_lt_pow v.ne_bot 1)
    exact ⟨ϖ, by simpa using hϖ1, by simpa using hϖ2⟩
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ K (ϖ : ℚ)) two_pos
  have hd : WD.lpDim (WD.lpOfChar hB _ (isSmooth_sqrtChar hB hx)) = 1 := by
    unfold WD.lpOfChar WD.lpDim WD.mk WD.std
    simp
  obtain ⟨ht, hl⟩ := lab_sqrtChar_two H h1 h2 hx
  exact ⟨v, B, hB, τ, γ, _, hγ, H, hd, ht, hl⟩

end GlobalTheory.WeilDeligne.LabModel
