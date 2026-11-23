import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
import ReciprocityTheory.DualLattices.VIntCastLtOneOfDvd
import ReciprocityTheory.DualLattices.PowMemCarrier

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ri

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

def wsum (χ : MulChar F R) (g : F → C) : F → C :=
  fun x => ∑ a : F, algebraMap R C (χ⁻¹ a) * g (a * x)

omit [DecidableEq F] in
lemma wsum_mem {M : Submodule R (F → C)} (hM : FStable F M) (χ : MulChar F R) {g : F → C}
    (hg : g ∈ M) : wsum χ g ∈ M := by
  have : wsum χ g = ∑ a : F, χ⁻¹ a • fun x => g (a • x) := by
    funext x; simp [wsum, Finset.sum_apply, Algebra.smul_def]
  rw [this]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hM a g hg)

omit [DecidableEq F] in
lemma wsum_eq (χ : MulChar F R) (g : F → C) (h0 : wsum χ g 0 = 0) (x : F) :
    wsum χ g x = algebraMap R C (χ x) * wsum χ g 1 := by
  by_cases hx : x = 0
  · subst hx
    simp [MulChar.map_nonunit χ not_isUnit_zero, h0]
  · unfold wsum
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight₀ x hx) _ _ (fun a => ?_)
    have hu : χ x * χ⁻¹ x = 1 := by
      rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hx, map_one]
    simp only [Equiv.mulRight₀_apply]
    rw [map_mul χ⁻¹, map_mul (algebraMap R C) (χ⁻¹ a)]
    calc algebraMap R C (χ⁻¹ a) * g (a * x)
        = algebraMap R C (χ x * χ⁻¹ x) * (algebraMap R C (χ⁻¹ a) * g (a * x)) := by
          rw [hu, map_one, one_mul]
      _ = _ := by rw [map_mul]; ring

omit [DecidableEq F] in
lemma wsum_zero_of_ne (hv : v.Integers R) {χ : MulChar F R} (hχ : χ ≠ 1) (g : F → C) :
    wsum χ g 0 = 0 := by
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  have hs : ∑ a : F, χ⁻¹ a = 0 := MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hχ)
  simp only [wsum, mul_zero]
  rw [← Finset.sum_mul, ← map_sum, hs, map_zero, zero_mul]

lemma sum_inv_mul (χ : MulChar F R) :
    ∑ a : F, algebraMap R C (χ⁻¹ a) * algebraMap R C (χ a) = (Fintype.card F : C) - 1 := by
  have key : ∀ a : F, algebraMap R C (χ⁻¹ a) * algebraMap R C (χ a) = 1 - if a = 0 then 1 else 0 := by
    intro a
    split_ifs with h
    · subst h
      simp [MulChar.map_nonunit χ not_isUnit_zero]
    · rw [← map_mul, MulChar.inv_apply', ← map_mul, inv_mul_cancel₀ h, map_one, map_one, sub_zero]
  simp_rw [key]
  simp [Finset.sum_sub_distrib]

omit [DecidableEq F] in
lemma v_card_sub_one (p : ℕ) [hp : Fact p.Prime] (hv : v.Integers R) (hpv : v (p : C) < 1)
    [CharP F p] : v ((Fintype.card F : C) - 1) = 1 := by
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hlt : v ((Fintype.card F : C)) < 1 := by
    rw [hn, Nat.cast_pow, map_pow]
    exact pow_lt_one₀ (by simp) hpv n.pos.ne'
  have h1 : v (-1 : C) = 1 := by rw [Valuation.map_neg, map_one]
  have hadd := v.map_add_eq_of_lt_right (x := (Fintype.card F : C)) (y := -1) (by rwa [h1])
  rw [sub_eq_add_neg, hadd, h1]

omit [DecidableEq F] [Fintype F] in
lemma mem_xIdeal (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C r * algebraMap R C (χ a)) ∈ M := by
  simp only [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  have hf : r • (fun a : F => algebraMap R C (χ a)) = fun a => algebraMap R C r * algebraMap R C (χ a) := by
    funext a
    simp [Algebra.smul_def]
  rw [hf]

lemma wsum_one (AA : HopfOrder (C := C) R F) (hM : FStable F AA.carrier) (χ : MulChar F R)
    {g : F → C} (hg : g ∈ AA.carrier) (h0 : wsum χ g 0 = 0) :
    ∃ r ∈ xIdeal AA.carrier χ, algebraMap R C r = wsum χ g 1 := by
  have hm := wsum_mem hM χ hg
  obtain ⟨r, hr⟩ := AA.le_int hm 1
  refine ⟨r, (mem_xIdeal _ _ _).2 ?_, hr⟩
  convert hm using 1
  funext a
  rw [wsum_eq χ g h0 a, hr, mul_comm]

lemma push_sum (b : F) (u φ : F → C) :
    ∑ y, (∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a) * φ y = ∑ a, u a * φ (b * a) := by
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ (fun a => b * a) (fun a => u a * φ (b * a))]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

end

theorem r_dual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ ψ : AddChar F C, ψ ≠ 1 → ∀ AD : HopfOrder (C := C) R F, AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a : F => ψ (h * a)) → FStable F AD.carrier ∧ ∀ χ : MulChar F R, χ ≠ 1 → ∀ c cD : R, xIdeal AA.carrier χ = Ideal.span {c} → xIdeal AD.carrier χ = Ideal.span {cD} → v (algebraMap R C c) * v (algebraMap R C cD) = v (∑ a, algebraMap R C (χ⁻¹ a) * ψ a) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hM ψ hψ AD hAD
  refine ⟨?_, ?_⟩
  · intro b g hg
    rw [hAD] at hg ⊢
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
    refine Submodule.mem_map.mpr ⟨fun y => ∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a, ?_, ?_⟩
    · intro f' hf'
      obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = ∑ a, u a * f' (b • a) := hu _ (hM b f' hf')
      refine ⟨r, ?_⟩
      show _ = ∑ y, (∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a) * f' y
      rw [hr, push_sum]
      rfl
    · funext h
      show ∑ y, (∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a) * ψ (h * y) = ∑ a, u a * ψ ((b • h) * a)
      rw [push_sum b u (fun y => ψ (h * y))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_eq_mul]
      ring_nf
  · intro χ hχ c cD hc hcD
    set G : C := ∑ a, algebraMap R C (χ⁻¹ a) * ψ a with hG
    have hW : ∀ h : F, ∑ a, algebraMap R C (χ⁻¹ a) * ψ (a * h) = algebraMap R C (χ h) * G := by
      intro h
      have e := wsum_eq χ (fun a => ψ a) (wsum_zero_of_ne hv hχ _) h
      simpa [wsum, G] using e
    have hFt : ∀ t : C, fourier (R := R) (fun h a : F => ψ (h * a)) (fun a => t * algebraMap R C (χ⁻¹ a)) = fun h => t * G * algebraMap R C (χ h) := by
      intro t
      funext h
      show ∑ a, t * algebraMap R C (χ⁻¹ a) * ψ (h * a) = _
      calc ∑ a, t * algebraMap R C (χ⁻¹ a) * ψ (h * a) = t * ∑ a, algebraMap R C (χ⁻¹ a) * ψ (a * h) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [mul_comm h a]
            ring
        _ = _ := by rw [hW h]; ring
    have hq : v ((Fintype.card F : C) - 1) = 1 := v_card_sub_one p hv hpv
    have hcm : (fun a => algebraMap R C c * algebraMap R C (χ a)) ∈ AA.carrier :=
      (mem_xIdeal _ _ _).mp (by rw [hc]; exact Ideal.mem_span_singleton_self c)
    have hDm : (fun a => algebraMap R C cD * algebraMap R C (χ a)) ∈ AD.carrier :=
      (mem_xIdeal _ _ _).mp (by rw [hcD]; exact Ideal.mem_span_singleton_self cD)
    have key : ∀ t : C, (∃ s : R, algebraMap R C s = t * algebraMap R C c) →
        v t * v G ≤ v (algebraMap R C cD) := by
      intro t ⟨s, hs⟩
      have hu : (fun a => t * algebraMap R C (χ⁻¹ a)) ∈ dualLat AA.carrier := by
        intro g hg
        obtain ⟨r, hr, hr1⟩ := wsum_one AA hM χ hg (wsum_zero_of_ne hv hχ g)
        rw [hc] at hr
        obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        refine ⟨k * s, ?_⟩
        have e : ∑ a, t * algebraMap R C (χ⁻¹ a) * g a = t * wsum χ g 1 := by
          simp only [wsum, mul_one, Finset.mul_sum, mul_assoc]
        show _ = ∑ a, t * algebraMap R C (χ⁻¹ a) * g a
        rw [e, ← hr1, map_mul, map_mul, hs]
        ring
      have hm : (fun h => t * G * algebraMap R C (χ h)) ∈ AD.carrier := by
        rw [hAD, ← hFt]
        exact Submodule.mem_map_of_mem hu
      obtain ⟨s', hs'⟩ : ∃ s' : R, algebraMap R C s' = t * G * algebraMap R C (χ 1) := AD.le_int hm 1
      rw [map_one, map_one, mul_one] at hs'
      have hx : s' ∈ xIdeal AD.carrier χ := by
        rw [mem_xIdeal, hs']
        exact hm
      rw [hcD] at hx
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [← map_mul, ← hs', map_mul, map_mul]
      calc v (algebraMap R C k) * v (algebraMap R C cD) ≤ 1 * v (algebraMap R C cD) := by
            gcongr
            exact hv.map_le_one k
        _ = _ := one_mul _
    rw [hAD] at hDm
    obtain ⟨u, hu, hFu⟩ := Submodule.mem_map.mp hDm
    obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = ∑ a, u a * (algebraMap R C c * algebraMap R C (χ a)) := hu _ hcm
    have hinv : ∑ h, algebraMap R C (χ⁻¹ h) * fourier (R := R) (fun h a : F => ψ (h * a)) u h =
        G * ∑ a, u a * algebraMap R C (χ a) := by
      have e1 : ∀ h, fourier (R := R) (fun h a : F => ψ (h * a)) u h = ∑ a, u a * ψ (h * a) := fun h => rfl
      simp_rw [e1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      calc ∑ h, algebraMap R C (χ⁻¹ h) * (u a * ψ (h * a)) = u a * ∑ h, algebraMap R C (χ⁻¹ h) * ψ (h * a) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun h _ => ?_
            ring
        _ = _ := by rw [hW a]; ring
    have hL : ∑ h, algebraMap R C (χ⁻¹ h) * fourier (R := R) (fun h a : F => ψ (h * a)) u h =
        algebraMap R C cD * ((Fintype.card F : C) - 1) := by
      rw [hFu, ← sum_inv_mul (C := C) χ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    have e2 : ∑ a, u a * (algebraMap R C c * algebraMap R C (χ a)) = algebraMap R C c * ∑ a, u a * algebraMap R C (χ a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [e2] at hr
    have hmain : G * algebraMap R C r = algebraMap R C c * algebraMap R C cD * ((Fintype.card F : C) - 1) := by
      linear_combination G * hr - algebraMap R C c * hinv + algebraMap R C c * hL
    have hup : v (algebraMap R C c) * v (algebraMap R C cD) ≤ v G := by
      have h2 := congrArg v hmain
      rw [map_mul, map_mul, map_mul, hq, mul_one] at h2
      rw [← h2]
      calc v G * v (algebraMap R C r) ≤ v G * 1 := by
            gcongr
            exact hv.map_le_one r
        _ = v G := mul_one _
    refine le_antisymm hup ?_
    by_cases hc0 : algebraMap R C c = 0
    · have hG0 : G = 0 := by
        by_contra hG0
        have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
        have h3 := key ((p : C) * G)⁻¹ ⟨0, by rw [hc0, mul_zero, map_zero]⟩
        have e3 : ((p : C) * G)⁻¹ * G = (p : C)⁻¹ := by field_simp
        rw [← map_mul, e3, map_inv₀] at h3
        have h4 := h3.trans (hv.map_le_one cD)
        have hvp : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).mpr hp0
        rw [inv_le_one₀ (pos_iff_ne_zero.mpr hvp)] at h4
        exact absurd hpv (not_lt.mpr h4)
      rw [hG0, hc0]
      simp
    · have h3 := key (algebraMap R C c)⁻¹ ⟨1, by rw [map_one, inv_mul_cancel₀ hc0]⟩
      rw [map_inv₀] at h3
      have hvc : 0 < v (algebraMap R C c) := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hc0)
      rwa [inv_mul_le_iff₀ hvc] at h3

theorem r_decomp : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c m}) → augIdeal AA.carrier = Submodule.span R ((fun m (a : F) => algebraMap R C (c m * (σ ^ m) a)) '' (Finset.Icc 1 (p ^ f - 1) : Set ℕ)) ∧ AA.carrier = Submodule.span R {(1 : F → C)} ⊔ augIdeal AA.carrier ∧ HasColen R v AA.carrier (∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c m))) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hM σ hσ c hc
  obtain ⟨hord, -, -, -, hsep⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hpv F f hcard σ hσ
  set n := p ^ f - 1 with hn
  have hcardn : Fintype.card F = n + 1 := by
    rw [hcard, hn, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)]
  have hn1 : 1 ≤ n := by
    have := Fintype.one_lt_card (α := F)
    omega
  have hσn : σ ^ n = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one σ
  have hpow : ∀ m, m ≠ 0 → ∀ z : F, (σ ^ m) z = σ z ^ m := fun m hm z => MulChar.pow_apply' σ hm z
  have hIcc : ∀ g : ℕ → C, ∑ m ∈ Finset.Icc 1 n, g m = ∑ i ∈ Finset.range n, g (i + 1) := by
    intro g
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, add_comm 1]
  have horth : ∀ z : F, ∑ m ∈ Finset.Icc 1 n, algebraMap R C ((σ ^ m) z) = if z = 1 then (n : C) else 0 := by
    intro z
    by_cases hz1 : z = 1
    · subst hz1
      simp
    rw [if_neg hz1]
    by_cases hz0 : z = 0
    · subst hz0
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [MulChar.map_nonunit _ not_isUnit_zero, map_zero]
    have hsz := hsep z 1 hz1
    have hζ1 : algebraMap R C (σ z) ≠ 1 := by
      intro h
      rw [map_sub, h, map_one, map_one, sub_self, map_zero] at hsz
      exact zero_ne_one hsz
    have hζn : algebraMap R C (σ z) ^ n = 1 := by
      rw [← map_pow, ← hpow n (by omega), hσn, MulChar.one_apply (Ne.isUnit hz0), map_one]
    rw [hIcc]
    have e : ∀ i, algebraMap R C ((σ ^ (i + 1)) z) = algebraMap R C (σ z) * algebraMap R C (σ z) ^ i := by
      intro i
      rw [hpow _ (Nat.succ_ne_zero i), map_pow, pow_succ, mul_comm]
    simp_rw [e, ← Finset.mul_sum, geom_sum_eq hζ1, hζn, sub_self, zero_div, mul_zero]
  have hb : ∀ m, (fun a : F => algebraMap R C (c m * (σ ^ m) a)) ∈ AA.carrier := by
    intro m
    have := (mem_xIdeal AA.carrier (σ ^ m) (c m)).mp (by rw [hc m]; exact Ideal.mem_span_singleton_self _)
    simpa only [map_mul] using this
  have hn0 : (n : C) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨qi, hqi⟩ : ∃ qi : R, algebraMap R C qi = (n : C)⁻¹ := by
    have h5 := v_card_sub_one (R := R) (F := F) p hv hpv
    rw [hcardn, Nat.cast_succ, add_sub_cancel_right] at h5
    exact hv.exists_of_le_one (by rw [map_inv₀, h5, inv_one])
  have hI : augIdeal AA.carrier = Submodule.span R ((fun m (a : F) => algebraMap R C (c m * (σ ^ m) a)) '' (Finset.Icc 1 (p ^ f - 1) : Set ℕ)) := by
    apply le_antisymm
    · intro g hg
      simp only [augIdeal, Submodule.mem_inf, LinearMap.mem_ker] at hg
      have hgA := hg.1
      have hg0 : g 0 = 0 := hg.2
      have hk : ∀ m, ∃ k : R, wsum (σ ^ m) g 1 = algebraMap R C (k * c m) := by
        intro m
        obtain ⟨r, hr, hr1⟩ := wsum_one AA hM (σ ^ m) hgA (by simp [wsum, hg0])
        rw [hc m] at hr
        obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        exact ⟨k, hr1.symm⟩
      choose k hk using hk
      have e4 : ∀ a : F, ∑ m ∈ Finset.Icc 1 n, algebraMap R C ((σ ^ m)⁻¹ a) = if a = 1 then (n : C) else 0 := by
        intro a
        simp_rw [MulChar.inv_apply']
        rw [horth a⁻¹]
        simp [inv_eq_one]
      have hg_eq : g = ∑ m ∈ Finset.Icc 1 n, (qi * k m) • (fun a : F => algebraMap R C (c m * (σ ^ m) a)) := by
        funext x
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hqi]
        have hw : ∀ m ∈ Finset.Icc 1 n, wsum (σ ^ m) g x = algebraMap R C ((σ ^ m) x) * (algebraMap R C (k m) * algebraMap R C (c m)) := by
          intro m _
          rw [wsum_eq (σ ^ m) g (by simp [wsum, hg0]) x, hk m, map_mul]
        have hsum : ∑ m ∈ Finset.Icc 1 n, wsum (σ ^ m) g x = (n : C) * g x := by
          simp only [wsum]
          calc ∑ m ∈ Finset.Icc 1 n, ∑ a, algebraMap R C ((σ ^ m)⁻¹ a) * g (a * x)
              = ∑ a, (∑ m ∈ Finset.Icc 1 n, algebraMap R C ((σ ^ m)⁻¹ a)) * g (a * x) := by
                rw [Finset.sum_comm]
                simp_rw [Finset.sum_mul]
            _ = _ := by
                simp_rw [e4]
                simp [ite_mul]
        rw [Finset.sum_congr rfl hw] at hsum
        calc g x = (n : C)⁻¹ * ((n : C) * g x) := by field_simp
          _ = _ := by
            rw [← hsum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
      rw [hg_eq]
      exact Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, Finset.mem_coe.mpr hm, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      simp only [augIdeal, SetLike.mem_coe, Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨hb m, ?_⟩
      show algebraMap R C (c m * (σ ^ m) 0) = 0
      rw [MulChar.map_nonunit _ not_isUnit_zero, mul_zero, map_zero]
  have hII : AA.carrier = Submodule.span R {(1 : F → C)} ⊔ augIdeal AA.carrier := by
    apply le_antisymm
    · intro g hg
      obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = g 0 := AA.le_int hg 0
      rw [← add_sub_cancel (r • (1 : F → C)) g]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) ?_
      simp only [augIdeal, Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨AA.carrier.sub_mem hg (AA.carrier.smul_mem r AA.one_mem), ?_⟩
      show (g - r • (1 : F → C)) 0 = 0
      simp [Algebra.smul_def, ← hr]
    · refine sup_le ?_ (fun g hg => by simp only [augIdeal, Submodule.mem_inf] at hg; exact hg.1)
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact AA.one_mem
  refine ⟨hI, hII, ?_⟩
  let e := Fintype.equivFinOfCardEq hcardn
  have hre : ∀ g : ℕ → C, ∑ j : F, g (e j : ℕ) = g 0 + ∑ m ∈ Finset.Icc 1 n, g m := by
    intro g
    rw [e.sum_comp (fun k : Fin (n + 1) => g k), Fin.sum_univ_eq_sum_range g (n + 1), Finset.sum_range_succ', hIcc, add_comm]
  have hreP : ∀ g : ℕ → NNReal, ∏ j : F, g (e j : ℕ) = g 0 * ∏ m ∈ Finset.Icc 1 n, g m := by
    intro g
    rw [e.prod_comp (fun k : Fin (n + 1) => g k), Fin.prod_univ_eq_prod_range g (n + 1), Finset.prod_range_succ',
      ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, mul_comm]
    simp only [Nat.add_sub_cancel, add_comm 1]
  let TR : Matrix F F R := Matrix.of fun x j => if (e j : ℕ) = 0 then 1 else (σ ^ (e j : ℕ)) x
  let UR : Matrix F F R := Matrix.of fun j y => if (e j : ℕ) = 0 then (if y = 0 then 1 else 0)
    else if y = 0 then (if (e j : ℕ) = n then -1 else 0) else qi * (σ ^ (e j : ℕ))⁻¹ y
  let d : F → C := fun j => if (e j : ℕ) = 0 then 1 else algebraMap R C (c (e j))
  let T := TR.map (algebraMap R C)
  let U := UR.map (algebraMap R C)
  have hTU : T * U = 1 := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [T, U, Matrix.map_apply, Matrix.of_apply, TR, UR]
    have h6 := hre (fun k => algebraMap R C (if k = 0 then 1 else (σ ^ k) x) *
      algebraMap R C (if k = 0 then (if y = 0 then 1 else 0) else if y = 0 then (if k = n then -1 else 0) else qi * (σ ^ k)⁻¹ y))
    simp only at h6
    rw [h6]
    rw [Finset.sum_congr rfl (g := fun m => algebraMap R C ((σ ^ m) x) * algebraMap R C (if y = 0 then (if m = n then -1 else 0) else qi * (σ ^ m)⁻¹ y))
      (fun m hm => by rw [if_neg (by simp at hm; omega), if_neg (by simp at hm; omega)])]
    by_cases hy : y = 0
    · subst hy
      simp only [if_true, map_one, one_mul, apply_ite (algebraMap R C), map_neg, map_zero, mul_ite, mul_neg, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' (Finset.Icc 1 n) n, if_pos (Finset.mem_Icc.mpr ⟨hn1, le_rfl⟩), hσn]
      by_cases hx : x = 0
      · subst hx
        rw [MulChar.map_nonunit (1 : MulChar F R) (not_isUnit_zero (M₀ := F)), map_zero, neg_zero, add_zero,
          Matrix.one_apply_eq]
      · rw [MulChar.one_apply (Ne.isUnit hx), map_one, Matrix.one_apply_ne hx]
        ring
    · simp only [if_neg hy, if_true, map_zero, mul_zero, zero_add, map_mul, hqi]
      have e5 : ∀ m, algebraMap R C ((σ ^ m) x) * ((n : C)⁻¹ * algebraMap R C ((σ ^ m)⁻¹ y)) =
          (n : C)⁻¹ * algebraMap R C ((σ ^ m) (x * y⁻¹)) := by
        intro m
        rw [MulChar.inv_apply', map_mul (σ ^ m) x, map_mul]
        ring
      simp_rw [e5]
      rw [← Finset.mul_sum, horth, Matrix.one_apply]
      by_cases hxy : x = y
      · subst hxy
        rw [mul_inv_cancel₀ hy, if_pos rfl, if_pos rfl, inv_mul_cancel₀ hn0]
      · rw [if_neg (by rwa [mul_inv_eq_one₀ hy]), if_neg hxy, mul_zero]
  have hdetTU : T.det * U.det = 1 := by rw [← Matrix.det_mul, hTU, Matrix.det_one]
  have hTdet : T.det = algebraMap R C TR.det := (RingHom.map_det _ _).symm
  have hUdet : U.det = algebraMap R C UR.det := (RingHom.map_det _ _).symm
  have hvT : v T.det = 1 := by
    have h1 := congrArg v hdetTU
    rw [map_mul, map_one, hUdet] at h1
    have hT1 : v T.det ≤ 1 := by
      rw [hTdet]
      exact hv.map_le_one _
    have hU1 := hv.map_le_one UR.det
    refine le_antisymm hT1 ?_
    calc (1 : NNReal) = v T.det * v (algebraMap R C UR.det) := h1.symm
      _ ≤ v T.det * 1 := by gcongr
      _ = v T.det := mul_one _
  have hcol : ∀ j, (fun x => (T * Matrix.diagonal d) x j) =
      fun x => if (e j : ℕ) = 0 then 1 else algebraMap R C (c (e j) * (σ ^ (e j : ℕ)) x) := by
    intro j
    funext x
    rw [Matrix.mul_diagonal]
    simp only [T, d, TR, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [map_mul, mul_comm]
  refine ⟨T * Matrix.diagonal d, ?_, ?_⟩
  · apply le_antisymm
    · rw [hII, hI, sup_le_iff]
      constructor
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        apply Submodule.subset_span
        refine ⟨e.symm ⟨0, by omega⟩, (hcol _).trans ?_⟩
        funext x
        simp
      · rw [Submodule.span_le]
        rintro _ ⟨m, hm, rfl⟩
        have hm' : 1 ≤ m ∧ m ≤ n := by simpa using hm
        apply Submodule.subset_span
        refine ⟨e.symm ⟨m, by omega⟩, (hcol _).trans ?_⟩
        funext x
        simp only [Equiv.apply_symm_apply]
        split_ifs with h0
        · exact absurd (h0 : m = 0) (by omega)
        · rfl
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show (fun x => (T * Matrix.diagonal d) x j) ∈ AA.carrier
      rw [hcol j]
      by_cases hj : (e j : ℕ) = 0
      · simp only [hj, if_true]
        exact AA.one_mem
      · simp only [hj, if_false]
        exact hb _
  · rw [Matrix.det_mul, Matrix.det_diagonal, map_mul, hvT, one_mul, map_prod]
    have h7 := hreP (fun k => v (if k = 0 then 1 else algebraMap R C (c k)))
    simp only at h7
    rw [show (∏ j, v (d j)) = ∏ j, v (if (e j : ℕ) = 0 then 1 else algebraMap R C (c (e j))) from rfl, h7]
    simp only [↓reduceIte, if_true, map_one, one_mul]
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [if_neg (by simp at hm; omega)]

end PositivityTheory.HtPt.Ri
