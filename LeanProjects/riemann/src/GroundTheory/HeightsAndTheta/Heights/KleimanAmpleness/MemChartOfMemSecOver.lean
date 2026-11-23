import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneMemSecOverZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockComp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

namespace ModelChangeGen

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

def fracRing (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] : Subring Ω where
  carrier := {u | ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    simp only [MulMemClass.coe_mul]
    rw [div_mul_div_comm]
  one_mem' := ⟨1, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have h0 : ∀ d : A, d ∉ p → (d : Ω) ≠ 0 := fun d hd h =>
      hd (by rw [show d = 0 from Subtype.ext h]; exact p.zero_mem)
    refine ⟨a * b' + b * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    simp only [AddMemClass.coe_add, MulMemClass.coe_mul]
    rw [div_add_div _ _ (h0 b hb) (h0 b' hb')]
  zero_mem' := ⟨0, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by simp only [NegMemClass.coe_neg]; ring⟩

theorem mem_locIn (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] (a : A) :
    (a : Ω) ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨a, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩

theorem inv_mem_locIn (A : Subalgebra F Ω) (p : Ideal A) (a : A) (ha : a ∉ p) :
    (a : Ω)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨1, a, ha, by simp⟩

theorem inv_not_mem_locIn (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] (a : A) (ha : a ∈ p)
    (ha0 : (a : Ω) ≠ 0) : (a : Ω)⁻¹ ∉ IndefiniteRowSideFullHecke.Kleiman2.locIn A p := by
  intro hmem
  have hle : IndefiniteRowSideFullHecke.Kleiman2.locIn A p ≤ fracRing A p := Subring.closure_le.mpr fun u hu => hu
  obtain ⟨a', b, hb, hab⟩ := hle hmem
  have hb0 : (b : Ω) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact p.zero_mem)
  have hba : b = a * a' := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    field_simp at hab
    linear_combination hab
  exact hb (hba ▸ p.mul_mem_right a' ha)

theorem mem_chart_of_mem_secOver {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω} {δ : K → ℤ}
    {s : Ω} (hs : s ∈ secOver F y δ) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    s * ∏ k, y ⟨k, c k⟩ ^ (-δ k) ∈ chartRingOver F y c := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply] at hs
  exact hs c hc

theorem prod_twist {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (β : K → ℤ) (k₀ : K) (m : ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (∏ k, y ⟨k, c k⟩ ^ (-β k)) * (y ⟨k₀, c k₀⟩ ^ m)⁻¹ := by
  have h1 : ∀ k, y ⟨k, c k⟩ ^ (-(β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      y ⟨k, c k⟩ ^ (-β k) * y ⟨k, c k⟩ ^ (-((m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
    intro k
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [Finset.prod_congr rfl (fun k _ => h1 k), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single k₀]
  · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, zpow_neg]
  · intro k _ hk
    simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
  · intro h
    exact absurd (Finset.mem_univ k₀) h

theorem exists_not_mem {A : Subalgebra F Ω} (p : Ideal A) [hp : p.IsPrime] {n : ℕ} (t : Fin n → Ω)
    (ht : ∀ j, t j ∈ A) (u : Fin n → Ω) (hu : ∀ j, u j ∈ A) (hsum : ∑ j, u j * t j = 1) :
    ∃ j, (⟨t j, ht j⟩ : A) ∉ p := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hmem : (∑ j, (⟨u j, hu j⟩ : A) * ⟨t j, ht j⟩) ∈ p :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hcon j)
  have h1 : (∑ j, (⟨u j, hu j⟩ : A) * ⟨t j, ht j⟩) = 1 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, OneMemClass.coe_one]
    exact hsum
  exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (h1 ▸ hmem))

theorem gen_of_gen {N : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {y : (Σ k, ι k) → Ω} {k₀ : K} {e : ι k₀ ≃ Fin (N + 1)}
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type}
    {y' : (Σ k, ι' k) → Ω} {k₀' : K'} {e' : ι' k₀' ≃ Fin (N + 1)}
    (hpts : IndefiniteRowSideFullHecke.Kleiman2.modelPts F y' ⊆ IndefiniteRowSideFullHecke.Kleiman2.modelPts F y)
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm)
    {β : K → ℤ} {β' : K' → ℤ} (m : ℕ)
    (hs : secOver F y' (β' + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀') ≤
      secOver F y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (hgen' : IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y' (β' + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀'))
    {n : ℕ} {h : Fin n → Ω} (hh : ∀ j, h j ∈ secOver F y β) (hh' : ∀ j, h j ∈ secOver F y' β')
    (hg : GeneratesOver F y β h) : GeneratesOver F y' β' h := by
  intro c' hc'
  set g' := ∏ k, y' ⟨k, c' k⟩ ^ (-β' k) with hg'def
  have ht : ∀ j, h j * g' ∈ chartRingOver F y' c' := fun j => mem_chart_of_mem_secOver (hh' j) c' hc'
  let t : Fin n → chartRingOver F y' c' := fun j => ⟨h j * g', ht j⟩
  by_cases htop : Ideal.span (Set.range t) = ⊤
  · obtain ⟨u, hu⟩ := (Ideal.mem_span_range_iff_exists_fun).mp ((Ideal.eq_top_iff_one _).mp htop)
    refine ⟨fun j => u j, fun j => (u j).2, ?_⟩
    have := congrArg Subtype.val hu
    simpa [t] using this
  exfalso
  obtain ⟨p', hp'max, hle⟩ := Ideal.exists_le_maximal _ htop
  have hp' : p'.IsPrime := hp'max.isPrime
  obtain ⟨c, hc, p, hp, hzeq⟩ := hpts ⟨c', hc', p', hp', rfl⟩

  obtain ⟨r, sv, hsv, hsgen⟩ := hgen'
  obtain ⟨v, hv, hvsum⟩ := hsgen c' hc'
  simp only [prod_twist y' c' hc' β' k₀' m] at hvsum
  have hsv' : ∀ l, sv l * (g' * (y' ⟨k₀', c' k₀'⟩ ^ m)⁻¹) ∈ chartRingOver F y' c' := fun l => by
    have := mem_chart_of_mem_secOver (hsv l) c' hc'
    rwa [prod_twist y' c' hc' β' k₀' m] at this
  obtain ⟨l, hl⟩ := exists_not_mem p' _ hsv' v hv hvsum

  set g := ∏ k, y ⟨k, c k⟩ ^ (-β k) with hgdef
  obtain ⟨u, hu, husum⟩ := hg c hc
  obtain ⟨j, hj⟩ := exists_not_mem p _ (fun j => mem_chart_of_mem_secOver (hh j) c hc) u hu husum
  have hw : sv l * (g * (y ⟨k₀, c k₀⟩ ^ m)⁻¹) ∈ chartRingOver F y c := by
    have := mem_chart_of_mem_secOver (hs (hsv l)) c hc
    rwa [prod_twist y c hc β k₀ m] at this

  have hxa : y ⟨k₀, c k₀⟩ = y' ⟨k₀', e'.symm (e (c k₀))⟩ := by
    have := congrFun hx (e (c k₀))
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using this
  have hratio : y ⟨k₀, c k₀⟩ / y' ⟨k₀', c' k₀'⟩ ∈ chartRingOver F y' c' := by
    rw [hxa]
    exact Algebra.subset_adjoin ⟨⟨k₀', e'.symm (e (c k₀))⟩, rfl⟩

  have hne : ∀ {A : Subalgebra F Ω} {q : Ideal A} (a : A), a ∉ q → (a : Ω) ≠ 0 := fun a ha h0 =>
    ha (by rw [show a = 0 from Subtype.ext h0]; exact Submodule.zero_mem _)
  have hjne := hne _ hj
  have hlne := hne _ hl
  have hg'ne : g' ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc' k)
  have hgne : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hxa0 : y ⟨k₀, c k₀⟩ ≠ 0 := hc k₀
  have hxb0 : y' ⟨k₀', c' k₀'⟩ ≠ 0 := hc' k₀'
  have hhj : h j ≠ 0 := fun h0 => hjne (by simp [h0])
  have hsl : sv l ≠ 0 := fun h0 => hlne (by simp [h0])

  have hmemp : t j ∈ p' := hle (Ideal.subset_span ⟨j, rfl⟩)
  have hkey : (h j * g')⁻¹ =
      (h j * g)⁻¹ * (sv l * (g * (y ⟨k₀, c k₀⟩ ^ m)⁻¹)) *
        (sv l * (g' * (y' ⟨k₀', c' k₀'⟩ ^ m)⁻¹))⁻¹ * (y ⟨k₀, c k₀⟩ / y' ⟨k₀', c' k₀'⟩) ^ m := by
    rw [div_pow]
    field_simp
  apply inv_not_mem_locIn _ p' (t j) hmemp (mul_ne_zero hhj hg'ne)
  change (h j * g')⁻¹ ∈ _
  rw [hkey]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) (pow_mem ?_ m)
  · rw [hzeq]; exact inv_mem_locIn _ p _ hj
  · rw [hzeq]; exact mem_locIn _ p ⟨_, hw⟩
  · exact inv_mem_locIn _ p' _ hl
  · exact mem_locIn _ p' ⟨_, hratio⟩

end ModelChangeGen

open ModelChangeGen in

theorem ModelChangeGen.proof (hT : ModelTwistGenerated.Statement) : ModelChangeGen.Statement := by
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hy hy' hx β β' hs n h hh
  have hpts := modelPts_eq_of_base F y k₀ e y' k₀' e' hy hy' hx
  have h0 : secOver F y β = secOver F y' β' := by simpa using hs 0
  have hh' : ∀ j, h j ∈ secOver F y' β' := fun j => h0 ▸ hh j
  obtain ⟨c₀, hc₀⟩ := hT F K ι Ω y k₀ inferInstance hy β
  obtain ⟨c₀', hc₀'⟩ := hT F K' ι' Ω y' k₀' inferInstance hy' β'
  have hm := hc₀ (c₀.toNat : ℕ) (Int.self_le_toNat c₀)
  have hm' := hc₀' (c₀'.toNat : ℕ) (Int.self_le_toNat c₀')
  constructor
  · exact gen_of_gen (e := e) (e' := e') hpts.ge hx c₀'.toNat (hs _).ge hm' hh hh'
  · exact gen_of_gen (e := e') (e' := e) hpts.le hx.symm c₀.toNat (hs _).le hm hh' hh

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
