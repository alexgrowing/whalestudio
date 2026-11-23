import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FormTies
open scoped Classical

namespace GlobalTheory.MoreColumns

open GlobalTheory.DatumInverseCharacter

theorem sum_append {A F : Type} [Fintype A] [CommRing F] {n m : ℕ} (f : (Fin n → A) → F) (χ : Fin (n + m) → A → F) :
    ∑ x : Fin (n + m) → A, f (fun b => x (Fin.castAdd m b)) * ∏ b, χ b (x b) =
      (∑ y : Fin n → A, f y * ∏ b, χ (Fin.castAdd m b) (y b)) * ∏ b : Fin m, ∑ a, χ (Fin.natAdd n b) a := by
  rw [← (Fin.appendEquiv n m).sum_comp, Fintype.sum_prod_type, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.prod_univ_add]
  simp [mul_assoc]

theorem zpow_sum {F ι : Type} [Field F] {z : F} (hz : z ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    z ^ (∑ i ∈ s, a i) = ∏ i ∈ s, z ^ a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hz, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem char_sum (D : Datum H) {N : ℕ} (hN : 0 < N) {I : Ideal (𝓞 E)}
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {F : Type} [Field F] {z : F} (hz : IsPrimitiveRoot z N)
    [Fintype (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La))] (v : D.La) :
    ∑ x : D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La), z ^ D.EF (qRep x) (cHalf H I • v) =
      if v ∈ (I • ⊤ : Submodule (𝓞 E) D.La) then
        (Nat.card (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) : F) else 0 := by
  obtain ⟨hc, hc1⟩ := HalfPairing.cHalf_spec I hI
  have hz0 : z ≠ 0 := hz.ne_zero hN.ne'
  have hmk : ∀ u : D.La, z ^ D.EF (qRep (Submodule.Quotient.mk u :
      D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La))) (cHalf H I • v) =
      z ^ D.EF u (cHalf H I • v) := by
    intro u
    refine zpow_congr hN hz.pow_eq_one ?_
    rw [← LinearMap.sub_apply, ← map_sub]
    exact dvd_left D hp hc v ((Submodule.Quotient.eq _).1 (qRep_spec _))
  let χ : AddChar (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) F :=
    { toFun := fun x => z ^ D.EF (qRep x) (cHalf H I • v)
      map_zero_eq_one' := by
        have := hmk 0
        rw [map_zero, LinearMap.zero_apply, zpow_zero] at this
        exact this
      map_add_eq_mul' := fun x y => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [← Submodule.Quotient.mk_add, hmk, hmk, hmk, map_add, LinearMap.add_apply, zpow_add₀ hz0] }
  have hiff : χ = 0 ↔ v ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := by
    constructor
    · intro h
      have h1 : ∀ y, (N : ℤ) ∣ D.EF (cHalf H I • v) y := fun y => by
        have h2 : χ (Submodule.Quotient.mk y) = 1 := by rw [h]; rfl
        have h3 : z ^ D.EF y (cHalf H I • v) = 1 := (hmk y).symm.trans h2
        rw [HalfPairing.ef_swap, dvd_neg]
        exact (hz.zpow_eq_one_iff_dvd _).1 h3
      have hNI : (N : 𝓞 E) ∈ I := by
        have : Ideal.span {(N : 𝓞 E)} ≤ I := hp ▸ (Ideal.mul_le_inf.trans inf_le_left)
        exact this (Ideal.subset_span rfl)
      have h4 := mem_of_modN D hNI (modN_of_dvd D hN h1)
      have : v = cHalf H I • v - (cHalf H I - 1) • v := by rw [sub_smul, one_smul, sub_sub_cancel]
      rw [this]
      exact sub_mem h4 (Submodule.smul_mem_smul hc1 trivial)
    · intro h
      ext x
      exact (hz.zpow_eq_one_iff_dvd _).2 (dvd_right D hp hc _ h)
  have := AddChar.sum_eq_ite χ
  rw [Nat.card_eq_fintype_card]
  simp only [← hiff]
  convert this using 2
  rfl

theorem coeff_more_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n m : ℕ) (d : DeltaDat Xo c n) (φ' : (Fin (n + m) → LevQ Dw d.l₂) → c.F), d.IsLev → Dw.p + Dw.q ≤ n → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (ph : (Fin n → LaJ Xo c d) → c.F) (x₀ : Fin n → LaJ Xo c d) (ph' : (Fin (n + m) → LaJ Xo c d) → c.F) (x₀' : Fin (n + m) → LaJ Xo c d), d.PhiPin ph ψ x₀ → (withCoeff d φ').PhiPin ph' ψ x₀' → ∃ ζ : c.F, IsOfFinOrder ζ ∧ ∀ q : Fin (n + m) → LevQ Dw d.l₂, φ' q = ζ * d.φδ (fun b => q (Fin.castAdd m b)) * (if ∀ b : Fin m, levRep (q (Fin.natAdd n b)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (LaI Xo c d) : c.F) ^ m else 0) := by
  intro E _ _ _ H Dw l Xo c n m d φ' hd hn ψ ph x₀ ph' x₀' hpin hpin'
  obtain ⟨-, huniq, adj, -, hadj⟩ := HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨-, hM, -, hMb, hI, -⟩ := hd
  obtain ⟨ha, hb, hc, hone, hspan, hφ⟩ := hpin
  obtain ⟨ha', hb', hc', hone', hspan', hφ'⟩ := hpin'
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hMb
  have hI0 : d.I ≠ ⊥ := by
    intro h
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hIJ
    exact hpd.ne' (by exact_mod_cast hIJ)
  have hJ0 : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hIJ
    exact hpd.ne' (by exact_mod_cast hIJ)
  haveI : Finite (𝓞 E ⧸ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hJ0
  haveI : Finite (𝓞 E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨e⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) _ Dw.rank
  obtain ⟨e'⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I _ Dw.rank
  haveI : Finite (LaJ Xo c d) := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (LaI Xo c d) := Finite.of_equiv _ e'.toEquiv.symm
  haveI : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) :=
    Finite.of_injective (fun k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d => (k : LaI Xo c d → LaI Xo c d))
      DFunLike.coe_injective
  have hcard : Nat.card (LaJ Xo c d) = Nat.card (LaI Xo c d) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv, Nat.card_fun, Nat.card_fun,
      Nat.card_congr (Ideal.quotientEquiv d.I _ (H.bar : 𝓞 E ≃+* 𝓞 E) rfl).toEquiv]
  have himg : ∀ {k : ℕ} (hk : Dw.p + Dw.q ≤ k) (x : Fin k → LaJ Xo c d),
      x '' {b | b.val < Dw.p + Dw.q} = Set.range (fun b : Fin (Dw.p + Dw.q) => x (Fin.castLE hk b)) := by
    intro k hk x
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hk b, b.2, rfl⟩
  have hn' : Dw.p + Dw.q ≤ n + m := hn.trans (Nat.le_add_right _ _)
  have hs₀ := (congrArg (Submodule.span (𝓞 E)) (himg hn x₀)).symm.trans hspan
  have hspan₁ : Submodule.span (𝓞 E) (x₀' '' {b | b.val < Dw.p + Dw.q}) = ⊤ := hspan'
  have hb₁ : ∀ x, ph' x ≠ 0 → Submodule.span (𝓞 E) (x '' {b | b.val < Dw.p + Dw.q}) = ⊤ := hb'
  have hs₀' := (congrArg (Submodule.span (𝓞 E)) (himg hn' x₀')).symm.trans hspan₁
  obtain ⟨g, hg, -⟩ := huniq _ _ hs₀ hs₀'
  have hy₀ : ph (fun b => x₀' (Fin.castAdd m b)) = (((ψ (adj g))⁻¹ : c.Fˣ) : c.F) := by
    have h1 := hc (adj g) g ((hadj _ _).2 rfl) x₀
    rw [hone, mul_one] at h1
    rw [← h1]
    exact ha _ _ fun b hb => (hg ⟨b.1, hb⟩).symm
  have hph : ∀ x : Fin (n + m) → LaJ Xo c d,
      ph' x = ((ψ (adj g) : c.Fˣ) : c.F) * ph (fun b => x (Fin.castAdd m b)) := by
    intro x
    by_cases hx : Submodule.span (𝓞 E) (Set.range (fun b : Fin (Dw.p + Dw.q) => x (Fin.castLE hn' b))) = ⊤
    · obtain ⟨g', hg', -⟩ := huniq _ _ hs₀' hx
      have h1 : ph' (fun b => g' (x₀' b)) = (((ψ (adj g'))⁻¹ : c.Fˣ) : c.F) * ph' x₀' :=
        hc' (adj g') g' ((hadj _ _).2 rfl) x₀'
      have h2 := hc (adj g') g' ((hadj _ _).2 rfl) (fun b => x₀' (Fin.castAdd m b))
      have h3 : ph' x = ph' (fun b => g' (x₀' b)) := ha' _ _ fun b hb => (hg' ⟨b.1, hb⟩).symm
      have h4 : ph (fun b => x (Fin.castAdd m b)) = ph (fun b => g' (x₀' (Fin.castAdd m b))) :=
        ha _ _ fun b hb => (hg' ⟨b.1, hb⟩).symm
      rw [h3, h4, h1, h2, hy₀, hone', mul_one, mul_left_comm, Units.mul_inv, mul_one]
    · have h1 : ph' x = 0 := by
        by_contra h
        exact hx ((congrArg (Submodule.span (𝓞 E)) (himg hn' x)).symm.trans (hb₁ x h))
      have h2 : ph (fun b => x (Fin.castAdd m b)) = 0 := by
        by_contra h
        exact hx ((congrArg (Submodule.span (𝓞 E)) (himg hn _)).symm.trans (hb _ h))
      rw [h1, h2, mul_zero]
  refine ⟨((ψ (adj g) : c.Fˣ) : c.F),
    (Units.coeHom c.F).isOfFinOrder (ψ.isOfFinOrder (isOfFinOrder_of_finite _)), fun q => ?_⟩
  set z : d.c₂.F := (⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd) with hzdef
  have hz : IsPrimitiveRoot z d.pd := by
    have h1 : d.pd ∣ d.l₂.M' := (hM ▸ Dvd.intro_left _ rfl : d.pd ∣ d.l₂.M).trans (Nat.dvd_lcm_left _ _)
    have h2 : 0 < d.l₂.M' := Nat.lcm_pos hM₂ d.l₂.A_pos
    have h0 : IsPrimitiveRoot (zeta d.l₂.M') d.l₂.M' := Complex.isPrimitiveRoot_exp _ h2.ne'
    have h3 : IsPrimitiveRoot (⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) d.l₂.M' :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap d.c₂.F ℂ) h0 (algebraMap d.c₂.F ℂ).injective
    exact h3.pow h2 (Nat.div_mul_cancel h1).symm
  have hz0 : z ≠ 0 := hz.ne_zero hpd.ne'
  haveI := Fintype.ofFinite (LaJ Xo c d)
  have h1 : d.eF (φ' q) = ∑ᶠ x : Fin (n + m) → LaJ Xo c d, d.eF (ph' x) *
      z ^ (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b))) := hφ' q
  apply d.eF.injective
  rw [h1, map_mul, map_mul, hφ, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [zpow_sum hz0, hph, map_mul, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_append (fun y => d.eF (ph y)) (fun b a => z ^ Dw.EF (qRep a) (cHalf H d.I • levRep (q b)))]
  congr 1
  simp only [char_sum Dw hpd hIJ hI hz]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, forall_true_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  split_ifs
  · rw [map_pow, map_natCast, ← hcard]
  · rw [map_zero]

end GlobalTheory.MoreColumns
