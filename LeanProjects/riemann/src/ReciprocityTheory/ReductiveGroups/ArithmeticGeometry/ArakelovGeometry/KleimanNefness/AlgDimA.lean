import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimSt
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.CommutativeAlgebra.WeakRegularity.RingKrullDimQuotientAddOneLeOfLt
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.DimFormulaOfSurjective

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal

open ReciprocityTheory.CA

theorem lt_of_add_one_le_fin (x y : WithBot ℕ∞) (n : ℕ) (hx : x ≠ ⊥) (hxn : x ≤ n)
    (h : x + 1 ≤ y) : x < y := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl hx
  | coe a =>
  induction y using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe b =>
  norm_cast at h hxn ⊢
  induction a using ENat.recTopCoe with
  | top => exact absurd hxn (by simp)
  | coe a =>
  induction b using ENat.recTopCoe with
  | top => exact WithTop.coe_lt_top a
  | coe b =>
  norm_cast at h ⊢

theorem ringKrullDim_quotient_ne_bot {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ringKrullDim (R ⧸ I) ≠ ⊥ := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial

theorem dimLt' : DimLtStatement := by
  intro F _ σ _ V W hV hW hVW
  have h1 := ReciprocityTheory.CA.Link.ringKrullDim_quotient_add_one_le_of_lt hVW
  have h2 : ringKrullDim (MvPolynomial σ F ⧸ W) ≤ (Fintype.card σ : ℕ) := by
    refine (ringKrullDim_quotient_le W).trans (le_of_eq ?_)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, zero_add]
  exact lt_of_add_one_le_fin _ _ _ (ringKrullDim_quotient_ne_bot W hW.ne_top) h2 h1

theorem isCM_atPrime_of_le {S : Type*} [CommRing S] (𝔐 W : Ideal S) [𝔐.IsPrime] [W.IsPrime]
    (h : IsCM (Localization.AtPrime 𝔐)) (hle : W ≤ 𝔐) : IsCM (Localization.AtPrime W) := by
  have hdisj : Disjoint (𝔐.primeCompl : Set S) (W : Set S) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hle hxp)
  let p := W.map (algebraMap S (Localization.AtPrime 𝔐))
  have : p.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔐.primeCompl _ W inferInstance hdisj
  have hc : p.comap (algebraMap S (Localization.AtPrime 𝔐)) = W :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔐.primeCompl _ (I := W) inferInstance hdisj
  have h2 := h.localization_atPrime p
  have : IsLocalization W.primeCompl (Localization.AtPrime p) := by
    have h0 : IsLocalization (p.comap (algebraMap S (Localization.AtPrime 𝔐))).primeCompl
        (Localization.AtPrime p) := inferInstance
    convert h0 using 2
    rw [hc]
  let e := IsLocalization.algEquiv W.primeCompl (Localization.AtPrime W) (Localization.AtPrime p)
  exact h2.of_ringEquiv e.symm.toRingEquiv

theorem dimPIT_fin (F : Type) [Field F] (N : ℕ) (V W : Ideal (MvPolynomial (Fin N) F))
    (s : MvPolynomial (Fin N) F) (hV : V.IsPrime) (hs : s ∉ V)
    (hW : W ∈ (V ⊔ Ideal.span {s}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin N) F ⧸ W) + 1 =
      ringKrullDim (MvPolynomial (Fin N) F ⧸ V) := by
  have hWp : W.IsPrime := hW.1.1
  have hVW : V ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨𝔐, h𝔐, hW𝔐⟩ := Ideal.exists_le_maximal W hWp.ne_top
  have hCM := (height_maximal_mvPolynomial_field F N 𝔐).1
  have hCMW := isCM_atPrime_of_le 𝔐 W hCM hW𝔐
  have hrel := height_eq_add_of_isCM_localization W V hCMW hVW
  let f := Ideal.Quotient.mk V
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ W := by rw [Ideal.mk_ker]; exact hVW
  have hP : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hcomapJ : (Ideal.span {f s}).comap f = V ⊔ Ideal.span {s} := by
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ hf,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]
  have hmin : W.map f ∈ (Ideal.span {f s}).minimalPrimes := by
    have h0 := hW
    rw [← hcomapJ, Ideal.comap_minimalPrimes_eq_of_surjective hf] at h0
    obtain ⟨Q, hQ, hQW⟩ := h0
    rw [← hQW, Ideal.map_comap_of_surjective _ hf]
    exact hQ
  have : (Ideal.span {f s}).IsPrincipal := ⟨⟨f s, rfl⟩⟩
  have hle1 : (W.map f).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : W.map f ≠ ⊥ := by
    intro h0
    have h3 : f s ∈ W.map f := Ideal.mem_map_of_mem f hsW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h3
    exact hs h3
  have hge1 : 1 ≤ (W.map f).height := by
    rw [Order.one_le_iff_ne_zero]
    exact fun h0 => hne (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  have h1 : (W.map f).height = 1 := le_antisymm hle1 hge1
  have eV := height_add_ringKrullDim_quotient_mvPolynomial_field F N V
  have eW := height_add_ringKrullDim_quotient_mvPolynomial_field F N W
  rw [hrel, h1] at eW
  have := dimFormula_arith V.height 1 _ _ N (ringKrullDim_quotient_ne_bot W hWp.ne_top)
    (ringKrullDim_quotient_ne_bot V hV.ne_top) eW eV
  rw [add_comm]
  exact_mod_cast this

theorem dimPIT' : DimPITStatement := by
  intro F _ σ _ V W s hV hs hW
  let e : MvPolynomial σ F ≃+* MvPolynomial (Fin (Fintype.card σ)) F :=
    (MvPolynomial.renameEquiv F (Fintype.equivFin σ)).toRingEquiv
  let g : MvPolynomial (Fin (Fintype.card σ)) F →+* MvPolynomial σ F := e.symm
  let eh : MvPolynomial σ F →+* MvPolynomial (Fin (Fintype.card σ)) F := e
  have hcm : ∀ I : Ideal (MvPolynomial σ F), I.comap g = I.map eh := fun I => Ideal.comap_symm e
  have hV' : (V.map eh).IsPrime := by
    have h0 : (V.comap g).IsPrime := Ideal.comap_isPrime g V
    rwa [hcm] at h0
  have hs' : eh s ∉ V.map eh := by
    rw [← hcm, Ideal.mem_comap]
    simpa [g, eh] using hs
  have key := Ideal.comap_minimalPrimes_eq_of_surjective (f := g) e.symm.surjective
    (V ⊔ Ideal.span {s})
  have hmem : W.comap g ∈ ((V ⊔ Ideal.span {s}).comap g).minimalPrimes := key ▸ ⟨W, hW, rfl⟩
  rw [hcm, hcm, Ideal.map_sup, Ideal.map_span, Set.image_singleton] at hmem
  have := dimPIT_fin F _ _ _ _ hV' hs' hmem
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv W _ e rfl),
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V _ e rfl)]
  exact this

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
