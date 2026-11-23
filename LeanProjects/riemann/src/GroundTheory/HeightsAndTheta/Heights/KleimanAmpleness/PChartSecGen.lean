import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

noncomputable section

section Loc

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem exists_common_denom_locIn (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] {ι' : Type*}
    [Fintype ι'] (ζ : ι' → Ω) (hζ : ∀ j, ζ j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) :
    ∃ b : A, b ∉ p ∧ ∀ j, (b : Ω) * ζ j ∈ A := by
  classical
  have h : ∀ j, ∃ b : A, b ∉ p ∧ (b : Ω) * ζ j ∈ A := fun j => locIn_le_fracSubring A p (hζ j)
  choose b hb hbζ using h
  refine ⟨∏ j, b j, fun hmem => ?_, fun j => ?_⟩
  · obtain ⟨j, _, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp hmem
    exact hb j hj
  · have key : ((∏ j', b j' : A) : Ω) * ζ j =
        ((∏ j' ∈ Finset.univ.erase j, b j' : A) : Ω) * ((b j : Ω) * ζ j) := by
      rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ j)]
      push_cast
      ring
    rw [key]
    exact A.mul_mem (Subtype.prop _) (hbζ j)

theorem sum_ne_one_of_mem_locIn (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] {n : ℕ}
    (ζ : Fin n → Ω) (hζ : ∀ j, ζ j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) (g : Fin n → A) (hg : ∀ j, g j ∈ p) :
    ∑ j, ζ j * (g j : Ω) ≠ 1 := by
  intro hsum
  obtain ⟨b, hb, hbζ⟩ := exists_common_denom_locIn A p ζ hζ
  apply hb
  have hkey : (b : Ω) = ∑ j, (b : Ω) * ζ j * g j := by
    calc (b : Ω) = b * ∑ j, ζ j * g j := by rw [hsum, mul_one]
      _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
  have key : b = ∑ j, (⟨_, hbζ j⟩ : A) * g j := by
    apply Subtype.ext
    push_cast
    exact hkey
  rw [key]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hg j)

theorem exists_mul_mem_span_of_locIn (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] {n : ℕ}
    (ζ η : Fin n → Ω) (hζ : ∀ j, ζ j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) :
    ∃ b : A, b ∉ p ∧ (b : Ω) * ∑ j, ζ j * η j ∈ Submodule.span A (Set.range η) := by
  obtain ⟨b, hb, hbζ⟩ := exists_common_denom_locIn A p ζ hζ
  refine ⟨b, hb, ?_⟩
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have key : (b : Ω) * (ζ j * η j) = (⟨_, hbζ j⟩ : A) • η j := by
    rw [Subalgebra.smul_def, smul_eq_mul]
    ring
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem mem_of_forall_maximal_mul_mem (A : Subalgebra S Ω) (M : Submodule A Ω) (t : Ω)
    (h : ∀ P : Ideal A, P.IsMaximal → ∃ b : A, b ∉ P ∧ (b : Ω) * t ∈ M) : t ∈ M := by
  let J : Ideal A := M.comap (LinearMap.toSpanSingleton A Ω t)
  have hJ : ∀ b : A, b ∈ J ↔ (b : Ω) * t ∈ M := by
    intro b
    change b • t ∈ M ↔ _
    rw [Subalgebra.smul_def, smul_eq_mul]
  have htop : J = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨b, hb, hbt⟩ := h P hP
    exact hb (hJP ((hJ b).mpr hbt))
  have h1 := (hJ 1).mp (htop ▸ Submodule.mem_top)
  simpa using h1

end Loc

section Charts

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem homog_div_mem_chartRing (x : Fin (N + 1) → Ω) {g : Kleiman.Poly S N} {m : ℕ}
    (hg : g.IsHomogeneous m) (i : Fin (N + 1)) :
    aeval x g / x i ^ m ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i := by
  rw [← Kleiman.aeval_div_of_isHomogeneous hg i, ReciprocityTheory.ChartRestriction.G.Geo.chartRing,
    Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem xProd_div_pow_mem (I : Kleiman.Chart x) (i : Fin (N + 1)) :
    Kleiman.xProd I / x i ^ I.1.card ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i := by
  have key : Kleiman.xProd I / x i ^ I.1.card = ∏ j ∈ I.1, x j / x i := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Kleiman.xProd]
  rw [key]
  exact prod_mem fun j _ => ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x i j

theorem pow_div_xProd_mem (I : Kleiman.Chart x) (a : Fin (N + 1)) :
    x a ^ I.1.card / Kleiman.xProd I ∈ Kleiman.chartRing S x I := by
  have key : x a ^ I.1.card / Kleiman.xProd I = ∏ j ∈ I.1, x a / x j := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Kleiman.xProd]
  rw [key]
  refine prod_mem fun j hj => ⟨X a, X j, 1, Kleiman.X_mem_monos hj, isHomogeneous_X S a,
    isHomogeneous_X S j, by simp⟩

theorem chartRing_le_powMulMem_xProd (I : Kleiman.Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    Kleiman.chartRing S x I ≤ powMulMem (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i)
      (Kleiman.xProd I / x i ^ I.1.card) (xProd_div_pow_mem I i) := by
  rintro _ ⟨f, s, d, hs, hf, hsd, rfl⟩
  obtain ⟨r, d₁, d', s', hsd₁, hs', hdd, hss⟩ := exists_mul_eq_prod_pow hs
  have hs0 : aeval x s ≠ 0 := Kleiman.eval_ne_zero_of_mem_monos I hs
  have hd : d = d₁ := hsd.inj_right hsd₁ (fun h => hs0 (by rw [h, map_zero]))
  subst hd
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
  refine ⟨r, ?_⟩
  have h1 : aeval x s * aeval x s' = Kleiman.xProd I ^ r := by
    have := congrArg (aeval x) hss
    simpa [map_mul, map_pow, map_prod, Kleiman.xProd] using this
  have key : (Kleiman.xProd I / x i ^ I.1.card) ^ r * (aeval x f / aeval x s) =
      aeval x (f * s') / x i ^ (d + d') := by
    rw [hdd, map_mul, div_pow, ← h1, ← pow_mul, mul_comm I.1.card r]
    field_simp
  rw [key]
  exact homog_div_mem_chartRing x (hf.mul hs') i

end Charts

section Model

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]
  {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}

theorem mem_span_of_generatesOver_chartSec (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) {n : ℕ}
    (η : Fin n → Ω) (hgen : GeneratesOver S y β η) (I : Kleiman.Chart (baseVec y k₀ e)) (t : Ω)
    (ht : t ∈ chartSecOver S y k₀ e β I) :
    t ∈ Submodule.span (Kleiman.chartRing S (baseVec y k₀ e) I) (Set.range η) := by
  obtain ⟨m, hm⟩ := ht
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : baseVec y k₀ e i ≠ 0 := (Kleiman.mem_support (baseVec y k₀ e)).mp (I.2.2 hi)
  have hxI : Kleiman.xProd I ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => (Kleiman.mem_support (baseVec y k₀ e)).mp (I.2.2 hj)
  have hA := chartRingOver_oneBlock_base (S := S) (y := y) (e := e) i
  have hAB : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm i) ≤
      Kleiman.chartRing S (baseVec y k₀ e) I := by
    rw [hA, TranslateEq.chartRing.equiv S (baseVec y k₀ e) hxi]
    exact Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hi)
  have he : Kleiman.xProd I / baseVec y k₀ e i ^ I.1.card ∈
      chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm i) := by
    rw [hA]; exact xProd_div_pow_mem I i
  have hB : Kleiman.chartRing S (baseVec y k₀ e) I ≤ powMulMem _ _ he := by
    intro r hr
    obtain ⟨M, hM⟩ := chartRing_le_powMulMem_xProd (S := S) I hi hr
    exact ⟨M, by rw [hA]; exact hM⟩
  apply mem_of_forall_maximal_mul_mem
  intro P hP
  have hPp : P.IsPrime := hP.isPrime
  have heP : (⟨_, hAB he⟩ : Kleiman.chartRing S (baseVec y k₀ e) I) ∉ P := by
    intro h
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have hinv := pow_div_xProd_mem (S := S) I i
    have h1 : (1 : Kleiman.chartRing S (baseVec y k₀ e) I) = ⟨_, hinv⟩ * ⟨_, hAB he⟩ := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, OneMemClass.coe_one]
      field_simp
    rw [h1]
    exact P.mul_mem_left _ h
  have hloc := locIn_eq_of_le_powMulMem hAB he hB P hPp heP
  obtain ⟨d, hd, q, hq, hz⟩ := model_pt_of_prime (e := e) hy hxi (P.comap (Subalgebra.inclusion hAB))
    (Ideal.comap_isPrime _ _)
  have := hq
  have hzeq : IndefiniteRowSideFullHecke.Kleiman2.locIn (Kleiman.chartRing S (baseVec y k₀ e) I) P =
      IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y d) q := hloc.trans hz
  obtain ⟨u, hu, hsum⟩ := hgen d hd
  have hv : y ⟨k₀, d k₀⟩ ≠ 0 := hd k₀

  have hsec := (mem_secOver_iff_charts y _ _).mp hm d hd
  change Kleiman.xProd I ^ m * t * genInv y (β + ((m * I.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d ∈ _
    at hsec
  rw [genInv_add_baseDeg β _ hd] at hsec
  have hvI : y ⟨k₀, d k₀⟩ ^ I.1.card / Kleiman.xProd I ∈ Kleiman.chartRing S (baseVec y k₀ e) I := by
    have := pow_div_xProd_mem (S := S) I (e (d k₀))
    simpa [baseVec_apply, IndefiniteRowSideFullHecke.Kleiman2.blockVec] using this
  have htw : t * genInv y β d ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y d) q := by
    have key : t * genInv y β d = Kleiman.xProd I ^ m * t *
        (genInv y β d * y ⟨k₀, d k₀⟩ ^ (-((m * I.1.card : ℕ) : ℤ))) *
        (y ⟨k₀, d k₀⟩ ^ I.1.card / Kleiman.xProd I) ^ m := by
      rw [zpow_neg, zpow_natCast, div_pow, ← pow_mul, mul_comm I.1.card m]
      field_simp
    rw [key]
    refine mul_mem (subset_locIn _ q hsec) ?_
    rw [← hzeq]
    exact pow_mem (subset_locIn _ P hvI) m
  have hζ : ∀ j, t * genInv y β d * u j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (Kleiman.chartRing S (baseVec y k₀ e) I) P := by
    intro j
    rw [hzeq]
    exact mul_mem htw (subset_locIn _ q (hu j))
  obtain ⟨b, hb, hbt⟩ := exists_mul_mem_span_of_locIn _ P _ η hζ
  refine ⟨b, hb, ?_⟩
  have key : ∑ j, t * genInv y β d * u j * η j = t := by
    calc ∑ j, t * genInv y β d * u j * η j = t * ∑ j, u j * (η j * genInv y β d) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = t := by rw [show genInv y β d = ∏ k, y ⟨k, d k⟩ ^ (-β k) from rfl, hsum, mul_one]
  rwa [key] at hbt

theorem generatesOver_of_span_chartSec (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) {n : ℕ}
    (η : Fin n → Ω) (hη : ∀ j, η j ∈ secOver S y β)
    (hspan : ∀ I : Kleiman.Chart (baseVec y k₀ e),
      (Submodule.span (Kleiman.chartRing S (baseVec y k₀ e) I) (Set.range η) : Set Ω) =
        chartSecOver S y k₀ e β I) :
    GeneratesOver S y β η := by
  classical
  intro c hc
  have hg : ∀ j, η j * genInv y β c ∈ chartRingOver S y c := fun j =>
    (mem_secOver_iff_charts y β (η j)).mp (hη j) c hc
  let g : Fin n → chartRingOver S y c := fun j => ⟨_, hg j⟩
  suffices hL : Ideal.span (Set.range g) = ⊤ by
    obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hL)
    refine ⟨fun j => u j, fun j => (u j).2, ?_⟩
    have h1 := congrArg Subtype.val hu
    push_cast at h1
    exact h1
  by_contra hne
  obtain ⟨q, hq, hLq⟩ := Ideal.exists_le_maximal _ hne
  have hqp : q.IsPrime := hq.isPrime
  have hgq : ∀ j, g j ∈ q := fun j => hLq (Ideal.subset_span ⟨j, rfl⟩)
  have hzmem : IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) q ∈
      IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) := by
    rw [← hy.2]
    exact ⟨c, hc, q, hqp, rfl⟩
  obtain ⟨c'', hc'', p', hp', hz⟩ := hzmem
  obtain ⟨a, rfl⟩ : ∃ a, c'' = fun _ => a := ⟨c'' (), funext fun u => by cases u; rfl⟩
  obtain ⟨i, rfl⟩ : ∃ i, a = e.symm i := ⟨e a, (e.symm_apply_apply a).symm⟩
  have hxi : baseVec y k₀ e i ≠ 0 := hc'' ()
  have hyi : y ⟨k₀, e.symm i⟩ ≠ 0 := hxi
  have hA : (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm i)) = ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i := chartRingOver_oneBlock_base (S := S) (y := y) (e := e) i

  obtain ⟨f, hfp, hfA⟩ : ∃ f : (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm i)), f ∉ p' ∧ ∀ s : Σ k, ι k, (f : Ω) * (y s / y ⟨s.1, c s.1⟩) ∈ (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm i)) := by
    refine exists_common_denom_locIn (hp := hp') (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm i)) p' (fun s : Σ k, ι k => y s / y ⟨s.1, c s.1⟩) fun s => ?_
    rw [← hz]
    exact subset_locIn _ q (div_mem_chartRingOver c s.1 s.2)
  have hcR : chartRingOver S y c ≤ powMulMem (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm i)) (f : Ω) f.2 := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    exact ⟨1, by rw [pow_one]; exact hfA s⟩

  have hr : ∀ d : ∀ k, ι k, y ⟨k₀, e.symm i⟩ / y ⟨k₀, d k₀⟩ ∈ chartRingOver S y d := fun d =>
    div_mem_chartRingOver d k₀ (e.symm i)
  have hRB : ∀ d : ∀ k, ι k, (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm i)) ≤ powMulMem (chartRingOver S y d) _ (hr d) := by
    intro d
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨⟨⟩, a⟩, rfl⟩
    refine ⟨1, ?_⟩
    have key : (y ⟨k₀, e.symm i⟩ / y ⟨k₀, d k₀⟩) ^ 1 *
        (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) ⟨(), a⟩ /
          IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) ⟨(), e.symm i⟩) =
        y ⟨k₀, a⟩ / y ⟨k₀, d k₀⟩ := by
      change (y ⟨k₀, e.symm i⟩ / y ⟨k₀, d k₀⟩) ^ 1 * (y ⟨k₀, a⟩ / y ⟨k₀, e.symm i⟩) = _
      field_simp
    rw [key]
    exact div_mem_chartRingOver d k₀ a
  have hΦ : ∀ d : ∀ k, ι k, genInv y β d * (genInv y β c)⁻¹ ∈
      powMulMem (powMulMem (chartRingOver S y d) _ (hr d)) (f : Ω) (hRB d f.2) := by
    intro d
    have key : genInv y β d * (genInv y β c)⁻¹ = ∏ k, (y ⟨k, c k⟩ / y ⟨k, d k⟩) ^ β k := by
      unfold genInv
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [div_zpow, zpow_neg, zpow_neg, inv_inv, div_eq_mul_inv, mul_comm]
    rw [key]
    refine prod_mem fun k _ => zpow_mem_of_inv_mem _ ?_ ?_ (β k)
    · exact le_powMulMem _ _ (le_powMulMem _ _ (div_mem_chartRingOver d k (c k)))
    · rw [inv_div]
      exact powMulMem_mono (hRB d) f.2 (hcR (div_mem_chartRingOver c k (d k)))
  choose Nf hNf using hΦ
  have hN : ∀ d : ∀ k, ι k, ∃ n', (y ⟨k₀, e.symm i⟩ / y ⟨k₀, d k₀⟩) ^ n' *
      ((f : Ω) ^ (Finset.univ.sup Nf) * (genInv y β d * (genInv y β c)⁻¹)) ∈ chartRingOver S y d := by
    intro d
    exact pow_mul_mem_of_le _ (hRB d f.2) (Finset.le_sup (Finset.mem_univ d)) (hNf d)
  choose nf hnf using hN
  set Nt := Finset.univ.sup Nf
  set nt := Finset.univ.sup nf

  have hsec : (f : Ω) ^ Nt * (genInv y β c)⁻¹ ∈ chartSecOver S y k₀ e β (Kleiman.singleChart hxi) := by
    refine ⟨nt, (mem_secOver_iff_charts y _ _).mpr fun d hd => ?_⟩
    change _ * genInv y _ d ∈ _
    rw [genInv_add_baseDeg β _ hd]
    have hxP : Kleiman.xProd (Kleiman.singleChart hxi) = y ⟨k₀, e.symm i⟩ := by
      simp [Kleiman.xProd, Kleiman.singleChart, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    have hcard : (Kleiman.singleChart hxi).1.card = 1 := by simp [Kleiman.singleChart]
    rw [hxP, hcard]
    have key : y ⟨k₀, e.symm i⟩ ^ nt * ((f : Ω) ^ Nt * (genInv y β c)⁻¹) *
        (genInv y β d * y ⟨k₀, d k₀⟩ ^ (-((nt * 1 : ℕ) : ℤ))) =
        (y ⟨k₀, e.symm i⟩ / y ⟨k₀, d k₀⟩) ^ nt *
          ((f : Ω) ^ Nt * (genInv y β d * (genInv y β c)⁻¹)) := by
      rw [mul_one, zpow_neg, zpow_natCast, div_pow]
      have := hd k₀
      field_simp
    rw [key]
    exact pow_mul_mem_of_le _ (hr d) (Finset.le_sup (Finset.mem_univ d)) (hnf d)
  rw [← hspan] at hsec
  obtain ⟨a', ha'⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hsec

  have hf0 : (f : Ω) ≠ 0 := by
    intro h0
    exact hfp (by rw [show f = 0 from Subtype.ext h0]; exact p'.zero_mem)
  have hgc0 : genInv y β c ≠ 0 := genInv_ne_zero β hc
  have hAI : Kleiman.chartRing S (baseVec y k₀ e) (Kleiman.singleChart hxi) = (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => e.symm i)) := by
    rw [hA, TranslateEq.chartRing.equiv S (baseVec y k₀ e) hxi]
  have hζ : ∀ j, ((a' j : Ω) * ((f : Ω) ^ Nt)⁻¹) ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) q := by
    intro j
    rw [hz]
    refine Subring.subset_closure ⟨⟨a' j, hAI ▸ (a' j).2⟩, f ^ Nt, fun h => hfp (hp'.mem_of_pow_mem _ h), ?_⟩
    simp [div_eq_mul_inv]
  apply sum_ne_one_of_mem_locIn _ q _ hζ g hgq
  have hsum : ∑ j, (a' j : Ω) * η j = (f : Ω) ^ Nt * (genInv y β c)⁻¹ := by
    rw [← ha']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul]
  calc ∑ j, (a' j : Ω) * ((f : Ω) ^ Nt)⁻¹ * ((g j : chartRingOver S y c) : Ω)
      = ((f : Ω) ^ Nt)⁻¹ * genInv y β c * ∑ j, (a' j : Ω) * η j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        show (a' j : Ω) * _ * (η j * genInv y β c) = _
        ring
    _ = 1 := by
        rw [hsum]
        field_simp

end Model

theorem ChartSecGen.full : ChartSecGen.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ N e hy β n η hη
  constructor
  · intro hgen I
    obtain ⟨Q, hQ⟩ := BundleOfDeg.full S K ι Ω y k₀ N e hy β
    have hQI : (Q.sub I : Set Ω) = chartSecOver S y k₀ e β I := Set.ext fun t => by
      rw [SetLike.mem_coe, mem_sub_iff_gam]
      refine exists_congr fun m => ?_
      rw [Kleiman.SubSystem.gam, hQ]
    apply Set.Subset.antisymm
    · rw [← hQI]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rw [hQI]
      exact mem_chartSecOver_of_mem S y k₀ e β I (hη j)
    · intro t ht
      exact mem_span_of_generatesOver_chartSec hy β η hgen I t ht
  · exact generatesOver_of_span_chartSec hy β η hη

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
