import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraicIndependentResidueOfIsUnit

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

theorem exists_rename_notMem {K : Type} [Field K] {σ : Type} (p : Ideal (MvPolynomial σ K))
    (hp : p.IsPrime ∧ p.height = 1) :
    ∃ e0 : σ, ∀ q : MvPolynomial {e // e ≠ e0} K, q ≠ 0 → rename Subtype.val q ∉ p := by
  classical
  haveI : UniqueFactorizationMonoid (MvPolynomial σ K) := MvPolynomial.uniqueFactorizationMonoid σ
  obtain ⟨hprime, hh⟩ := hp
  have hne : p ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hh
    exact zero_ne_one hh
  obtain ⟨g, hgp, hgprime⟩ := hprime.exists_mem_prime_of_ne_bot hne
  have hg0 : g ≠ 0 := hgprime.ne_zero
  haveI hPprime : (Ideal.span {g}).IsPrime := (Ideal.span_singleton_prime hg0).mpr hgprime
  have hPle : Ideal.span {g} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hgp
  have hPeq : Ideal.span {g} = p := by
    by_contra hneq
    have hlt : Ideal.span {g} < p := lt_of_le_of_ne hPle hneq
    haveI : p.FiniteHeight := ⟨Or.inr (by rw [hh]; exact ENat.one_ne_top)⟩
    have h1 : (Ideal.span {g}).height < p.height := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    rw [hh] at h1
    have hPh : (Ideal.span {g}).height = 0 := ENat.lt_one_iff_eq_zero.mp h1
    haveI : (Ideal.span {g}).FiniteHeight := ⟨Or.inr (by rw [hPh]; exact ENat.zero_ne_top)⟩
    have hbot : (⊥ : Ideal (MvPolynomial σ K)) < Ideal.span {g} := by
      rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hg0
    have h2 : (⊥ : Ideal (MvPolynomial σ K)).height < (Ideal.span {g}).height :=
      Ideal.height_strict_mono_of_isPrime_of_isPrime hbot
    rw [hPh] at h2
    exact absurd h2 not_lt_zero'
  have hvars : g.vars.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have htd : g.totalDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      unfold MvPolynomial.totalDegree
      apply Finset.sup_le
      intro d hd
      have hd0 : d = 0 := by
        ext i
        by_contra hi
        have hiv : i ∈ g.vars := (MvPolynomial.mem_vars i).mpr ⟨d, hd, Finsupp.mem_support_iff.mpr hi⟩
        rw [hemp] at hiv
        simp at hiv
      simp [hd0]
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at htd
    have ha : MvPolynomial.coeff 0 g ≠ 0 := by
      intro ha0
      apply hg0
      rw [htd, ha0, map_zero]
    apply hgprime.not_unit
    rw [htd]
    exact (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
  obtain ⟨e0, he0⟩ := hvars
  refine ⟨e0, fun q hq hmem => ?_⟩
  rw [← hPeq, Ideal.mem_span_singleton] at hmem
  obtain ⟨h, hh2⟩ := hmem
  have hr0 : rename Subtype.val q ≠ 0 := by
    intro h0
    apply hq
    exact MvPolynomial.rename_injective _ Subtype.val_injective (by rw [h0, map_zero])
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hh2
    exact hr0 hh2
  have hdeg : MvPolynomial.degreeOf e0 (rename Subtype.val q) ≠ 0 := by
    rw [hh2, MvPolynomial.degreeOf_mul_eq hg0 hh0]
    have h3 := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mp he0
    omega
  have hin : e0 ∈ (rename Subtype.val q).vars := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hdeg
  obtain ⟨i, -, hi⟩ := MvPolynomial.mem_vars_rename _ _ hin
  exact i.2 hi

theorem card_subtype_ne' {σ : Type} [Fintype σ] [DecidableEq σ] (e0 : σ) :
    Fintype.card {e // e ≠ e0} = Fintype.card σ - 1 := by
  first
  | rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  | simp [Fintype.card_subtype_compl]

theorem card_baseOrOffColumn {D N : ℕ} (j0 : Fin (N + 1)) :
    Fintype.card {e : TVar D N // e.1 = 0 ∨ e.2 ≠ j0} = (D + 1) * (N + 1) - D := by
  have hc := Fintype.card_subtype_compl (fun e : TVar D N => ¬ (e.1 = 0 ∨ e.2 ≠ j0))
  have e1 : {e : TVar D N // ¬ ¬ (e.1 = 0 ∨ e.2 ≠ j0)} ≃ {e : TVar D N // e.1 = 0 ∨ e.2 ≠ j0} :=
    Equiv.subtypeEquivRight (fun _ => not_not)
  have e2 : {e : TVar D N // ¬ (e.1 = 0 ∨ e.2 ≠ j0)} ≃ {i : Fin (D + 1) // i ≠ 0} :=
    { toFun := fun x => ⟨x.1.1, fun h => x.2 (Or.inl h)⟩
      invFun := fun i => ⟨(i.1, j0), fun h => h.elim i.2 (fun h' => h' rfl)⟩
      left_inv := fun x => by
        obtain ⟨⟨a, b⟩, hx⟩ := x
        have hb : b = j0 := by
          by_contra hne
          exact hx (Or.inr hne)
        subst hb
        rfl
      right_inv := fun i => rfl }
  rw [Fintype.card_congr e1, Fintype.card_congr e2] at hc
  have h3 : Fintype.card {i : Fin (D + 1) // i ≠ 0} = D := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    omega
  rw [hc, h3, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem val_algebraMap_eq_zero (c : ι) (p : Ideal (KTp K d.D d.N))
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p) (a : K)
    (ha : a ≠ 0) : w (algebraMap K (OmS (Ω c) d.D d.N) a) = 0 := by
  have h1 := (hw.2 (MvPolynomial.C a)).1
  have h2 := (hw.2 (MvPolynomial.C a⁻¹)).1
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes] at h1 h2
  have h3 : w (algebraMap K (OmS (Ω c) d.D d.N) a) + w (algebraMap K (OmS (Ω c) d.D d.N) a⁻¹) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg h1 h2).mp h3).1

theorem w_eq_scalarRatio_smul (hd : d.AxH 𝒜) (c : ι) (j : Fin (d.N + 1)) :
    d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hmem := hd.w_mem
  have hne : (⟨d.w (d.jc c) c, hmem _ c⟩ : 𝒜 c d.wL) ≠ 0 := fun h => hd.w_base c (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp (hd.finrank_one c d.wL) ⟨d.w j c, hmem j c⟩
  have hex : ∃ a : Ω c, d.w j c = a • d.w (d.jc c) c := by
    refine ⟨a, ?_⟩
    have h2 := congrArg Subtype.val ha
    simpa using h2.symm
  unfold ratio
  rw [dif_pos hex]
  exact hex.choose_spec

theorem exists_integral_base (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) :
    ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ∈ vRing v) ∧
      ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) ≠ 0 ∧
      ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
        ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
  have uniq : ∀ (f g : A c) (a : Ω c), g ≠ 0 → f = a • g → ratio (Ω := Ω c) f g = a := by
    intro f g a hg hfa
    have hex : ∃ b : Ω c, f = b • g := ⟨a, hfa⟩
    unfold ratio
    rw [dif_pos hex]
    by_contra hne
    apply hg
    have h0 : (hex.choose - a) • g = 0 := by rw [sub_smul, ← hex.choose_spec, ← hfa, sub_self]
    have h1 := congrArg (fun y => (hex.choose - a)⁻¹ • y) h0
    simp only [smul_zero] at h1
    rwa [inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h1
  obtain ⟨q, hqdef⟩ : ∃ q : Fin (d.N + 1) → Ω c, ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = q j :=
    ⟨_, fun _ => rfl⟩
  have hx : ∀ j, d.w j c = q j • d.w (d.jc c) c := fun j => by
    rw [← hqdef]
    exact d.w_eq_scalarRatio_smul hd c j
  have hq1 : q (d.jc c) = 1 := by
    rw [← hqdef]
    exact uniq _ _ 1 (hd.w_base c) (one_smul _ _).symm
  have key : ∀ a b : WithTop ℤ, b ≠ ⊤ → b ≤ a + b → 0 ≤ a := by
    intro a b hb h
    induction a using WithTop.recTopCoe with
    | top => exact le_top
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top => exact absurd rfl hb
      | coe b =>
        have h1 : (b : WithTop ℤ) ≤ ((a + b : ℤ) : WithTop ℤ) := by exact_mod_cast h
        have h2 : b ≤ a + b := WithTop.coe_le_coe.mp h1
        exact_mod_cast (show (0 : ℤ) ≤ a by omega)
  have smul_ne : ∀ (a : Ω c) (g : A c), a ≠ 0 → g ≠ 0 → a • g ≠ 0 := by
    intro a g ha hg h
    apply hg
    have h1 := congrArg (fun y => a⁻¹ • y) h
    simp only [smul_zero] at h1
    rwa [inv_smul_smul₀ ha] at h1
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ (fun j => v (q j)) ⟨d.jc c, Finset.mem_univ _⟩
  have hvle : v (q j0) ≤ 0 := by
    have h1 := hj0 (d.jc c) (Finset.mem_univ _)
    rwa [hq1, AddValuation.map_one] at h1
  have hq0 : q j0 ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hvle
    first
    | exact absurd hvle (by simp)
    | exact WithTop.zero_ne_top (top_le_iff.mp hvle)
  have hw0 : d.w j0 c ≠ 0 := by
    rw [hx j0]
    exact smul_ne _ _ hq0 (hd.w_base c)
  have hrat : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) = q j / q j0 := by
    intro j
    apply uniq _ _ _ hw0
    rw [hx j, hx j0, smul_smul, div_mul_cancel₀ _ hq0]
  refine ⟨j0, hw0, fun j => ?_, by rw [hqdef]; exact hq0, fun j => by rw [hrat j, hqdef, hqdef]⟩
  rw [mem_valuationRing, hrat j]
  have hmul : v (q j) = v (q j / q j0) + v (q j0) := by
    rw [← AddValuation.map_mul, div_mul_cancel₀ _ hq0]
  have hle := hj0 j (Finset.mem_univ _)
  rw [hmul] at hle
  have hnt : v (q j0) ≠ ⊤ := by
    intro h
    rw [AddValuation.top_iff] at h
    exact hq0 h
  exact key _ _ hnt hle

theorem genericHomAt_relation (hd : d.AxH 𝒜) (c : ι) (j0 : Fin (d.N + 1)) (hw0 : d.w j0 c ≠ 0)
    (hq : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))
    (i : Fin (d.D + 1)) (hi : i ≠ 0) :
    d.sH c (X (i, j0)) = -∑ j ∈ Finset.univ.erase j0, d.sH c (X (i, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) := by
  have uniq : ∀ (f g : A c) (a : Ω c), g ≠ 0 → f = a • g → ratio (Ω := Ω c) f g = a := by
    intro f g a hg hfa
    have hex : ∃ b : Ω c, f = b • g := ⟨a, hfa⟩
    unfold ratio
    rw [dif_pos hex]
    by_contra hne
    apply hg
    have h0 : (hex.choose - a) • g = 0 := by rw [sub_smul, ← hex.choose_spec, ← hfa, sub_self]
    have h1 := congrArg (fun y => (hex.choose - a)⁻¹ • y) h0
    simp only [smul_zero] at h1
    rwa [inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h1
  classical
  obtain ⟨q, hqdef⟩ : ∃ q : Fin (d.N + 1) → Ω c, ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = q j :=
    ⟨_, fun _ => rfl⟩
  have hx : ∀ j, d.w j c = q j • d.w (d.jc c) c := fun j => by
    rw [← hqdef]
    exact d.w_eq_scalarRatio_smul hd c j
  have hq1 : q (d.jc c) = 1 := by
    rw [← hqdef]
    exact uniq _ _ 1 (hd.w_base c) (one_smul _ _).symm
  have hq0 : q j0 ≠ 0 := by
    intro h0
    apply hw0
    rw [hx j0, h0, zero_smul]
  have hxq : ∀ k, d.x c k = q ((d.jc c).succAbove k) := fun k => hqdef _
  obtain ⟨T, hTdef⟩ : ∃ T : Fin (d.N + 1) → OmS (Ω c) d.D d.N, ∀ j, d.sH c (X (i, j)) = T j :=
    ⟨_, fun _ => rfl⟩
  have hTX : ∀ j, T j = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c)
        (-∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (Sum.inr (i, k))) j) := by
    intro j
    rw [← hTdef]
    simp only [Data.sH, sHom, MvPolynomial.aeval_X, sImg, if_neg hi]
  have hCr : ∀ a : Ω c, algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (MvPolynomial.C a) =
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    intro a
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N),
      MvPolynomial.algebraMap_eq]
  have hTjc : T (d.jc c) = -∑ k, T ((d.jc c).succAbove k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (d.x c k) := by
    rw [hTX, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
    simp only [map_neg, map_sum, map_mul, hCr]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hTX, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  have hsum : ∑ j, T j * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j) = 0 := by
    rw [Fin.sum_univ_succAbove _ (d.jc c), hq1, map_one, mul_one, hTjc]
    simp only [hxq]
    exact neg_add_cancel _
  simp only [hq, hqdef, hTdef, map_div₀]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)] at hsum
  have hr0 : algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j0) ≠ 0 := (map_ne_zero _).mpr hq0
  have hS : ∑ j ∈ Finset.univ.erase j0, T j * (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j) /
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j0)) =
      (∑ j ∈ Finset.univ.erase j0, T j * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j)) /
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (q j0) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hS, ← neg_div, eq_div_iff hr0]
  linear_combination hsum

end Data

end ReciprocityTheory.ChartRestriction.G.T0
