import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelGoodPointGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCodimOneUniformiser
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionUnramifiedGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotientMinimalPrimeAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ringKrullDim_quotient_minimalPrime_add_one_of_fintype {σ : Type} [Fintype σ]
    {V W : Ideal (MvPolynomial σ ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial σ ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial σ ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial σ ℂ ⧸ V) := by
  have hPW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk V)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk V)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V) := Ideal.mem_map_of_mem _ hfW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have : IsDomain (MvPolynomial σ ℂ ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ V) (Ideal.Quotient.mkₐ_surjective ℂ V)
  have : IsNoetherianRing (MvPolynomial σ ℂ ⧸ V) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial σ ℂ ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h ↦ by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ ℂ ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial σ ℂ ⧸ V)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial σ ℂ ⧸ V)
    (fun M N hM hN ↦ (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

theorem NormalModelGoodPointGeneric.proof (h₁ : NormalCodimOneCompleteIntersection.Statement)
    (h₂ : NormalCodimOneUniformiser.Statement) (h₃ : JacobianRankOffHypersurface.Statement)
    (h₄ : ProjectionUnramifiedGeneric.Statement) : NormalModelGoodPointGeneric.Statement := by
  classical
  intro n d J u M hJ hdim hu
  have hP : M.ideal.IsPrime := M.isPrime
  set ut : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl (linForm u) with hut
  have hutP : ut ∉ M.ideal := by
    intro h
    apply hu
    rw [← M.comap_eq]
    exact h
  have hdimP : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (d + 1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have hev : ∀ x : Fin n ⊕ Fin M.m → ℂ, eval x ut = linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords x) := fun x ↦ by
    simp [hut, linForm, linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords, map_sum]
  set L : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) := M.ideal ⊔ Ideal.span {ut} with hL
  have hfinM : L.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ L
  set T := hfinM.toFinset with hT
  have hmemT : ∀ W, W ∈ T ↔ W ∈ L.minimalPrimes := fun W ↦ hfinM.mem_toFinset

  have hdimW : ∀ W ∈ L.minimalPrimes, ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ W) = (d : ℕ) := by
    intro W hW
    have key := ringKrullDim_quotient_minimalPrime_add_one_of_fintype hutP hW (fun h ↦ by
      rw [hdimP] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
    rw [hdimP] at key
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key

  have hgood : ∀ W ∈ L.minimalPrimes, ∃ β : MvPolynomial (Fin n ⊕ Fin M.m) ℂ, β ∉ W ∧
      ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn W, eval w β ≠ 0 → NormalModelDivisorGoodPoint M u d w := by
    intro W hW
    have hWp : W.IsPrime := hW.1.1
    have hPW : M.ideal ≤ W := le_sup_left.trans hW.1.2
    have hutW : ut ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnm : ∀ x y, x ∉ W → y ∉ W → x * y ∉ W := fun x y hx hy hm ↦ (hWp.mem_or_mem hm).elim hx hy
    obtain ⟨c, f, h, hc, hfP, hhW, hgen⟩ :=
      h₁ _ M.ideal W d hP hWp hPW M.isIntegrallyClosed hdimP (hdimW W hW)
    obtain ⟨g, a, b, t, k, hgW, hk, haW, hbW, htW, hrel, hgenW⟩ :=
      h₂ _ M.ideal W d ut hP hWp hPW M.isIntegrallyClosed hdimP (hdimW W hW) hutW hutP
    set q : Fin (c + 1) → MvPolynomial (Fin n ⊕ Fin M.m) ℂ := Fin.cons g f with hq
    have hqW : ∀ j, q j ∈ W := fun j ↦ Fin.cases (by simpa [hq] using hgW)
      (fun j ↦ by simpa [hq] using hPW (hfP j)) j
    have hspan : Ideal.span (Set.range f) ≤ Ideal.span (Set.range q) :=
      Ideal.span_mono (Set.range_subset_iff.2 fun j ↦ ⟨j.succ, by simp [hq]⟩)
    have hgq : g ∈ Ideal.span (Set.range q) := Ideal.subset_span ⟨0, by simp [hq]⟩
    have hgenq : ∀ p ∈ W, ∃ i : ℕ, (h * t) ^ i * p ∈ Ideal.span (Set.range q) := by
      intro p hp
      obtain ⟨i₁, hi₁⟩ := hgenW p hp
      obtain ⟨r, hr, s, hs, hrs⟩ := Submodule.mem_sup.1 hi₁
      obtain ⟨i₂, hi₂⟩ := hgen r hr
      refine ⟨i₁ + i₂, ?_⟩
      have e : (h * t) ^ (i₁ + i₂) * p = h ^ i₁ * t ^ i₂ * (h ^ i₂ * r) + h ^ (i₁ + i₂) * t ^ i₂ * s := by
        linear_combination (-(h ^ (i₁ + i₂) * t ^ i₂)) * hrs
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hspan hi₂))
        (Ideal.mul_mem_left _ _ ((Ideal.span_singleton_le_iff_mem _).2 hgq hs))
    have hint : ∀ i : Fin M.m, ∃ F : Polynomial (MvPolynomial (Fin n) ℂ), F.Monic ∧
        F.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
          (X (Sum.inr i)) ∈ W := fun i ↦ by
      obtain ⟨F, hF, hmem⟩ := M.integral i
      exact ⟨F, hF, hPW hmem⟩
    obtain ⟨μ₁, hμ₁W, hμ₁⟩ := h₃ _ W d (c + 1) q (h * t) hWp (hdimW W hW) hqW (hnm _ _ hhW htW) hgenq
    obtain ⟨μ₂, hμ₂W, hμ₂⟩ := h₄ (Fin n) (Fin M.m) W (c + 1) q (h * t) hWp hint hqW (hnm _ _ hhW htW) hgenq
    refine ⟨h * t * a * b * μ₁ * μ₂,
      hnm _ _ (hnm _ _ (hnm _ _ (hnm _ _ (hnm _ _ hhW htW) haW) hbW) hμ₁W) hμ₂W, fun w hw hβ ↦ ?_⟩
    have hwP : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := fun p hp ↦ hw p (hPW hp)
    simp only [map_mul, ne_eq, mul_eq_zero, not_or] at hβ
    obtain ⟨⟨⟨⟨⟨hwh, hwt⟩, hwa⟩, hwb⟩, hwμ₁⟩, hwμ₂⟩ := hβ
    have hc' : c + (d + 1) = n + M.m := by simpa using hc
    have hfam : (Fin.cons (fun s ↦ eval w (pderiv s g)) (fun j s ↦ eval w (pderiv s (f j))) :
        Fin (c + 1) → Fin n ⊕ Fin M.m → ℂ) = fun j s ↦ eval w (pderiv s (q j)) := by
      funext j s
      refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [hq]
    refine ⟨hwP, c, f, h, g, a, b, k, hc', hfP, hwh, hgen, hw g hgW, ?_, hk, hwa, hwb, hrel, ?_⟩
    · rw [hfam, linearIndependent_iff_card_eq_finrank_span]
      have := hμ₁ w hw hwμ₁
      simp only [Fintype.card_sum, Fintype.card_fin] at this ⊢
      show c + 1 = Module.finrank ℂ (Submodule.span ℂ (Set.range fun j s ↦ eval w (pderiv s (q j))))
      omega
    · intro v hv hgv hfv
      refine hμ₂ w hw hwμ₂ v hv fun j ↦ Fin.cases ?_ (fun j ↦ ?_) j
      · simpa [hq] using hgv
      · simpa [hq] using hfv j
  choose! β hβW hβ using hgood

  have hcomp : ∀ x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords x) = 0 →
      ∃ W ∈ L.minimalPrimes, x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn W := by
    intro x hxJ hxu
    have hxL : L ≤ RingHom.ker (eval x) := sup_le (fun p hp ↦ RingHom.mem_ker.mpr (hxJ p hp))
      (Ideal.span_le.mpr (by simpa [hev] using hxu))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hW, hWx⟩ := Ideal.exists_minimalPrimes_le hxL
    exact ⟨W, hW, fun p hp ↦ RingHom.mem_ker.mp (hWx hp)⟩

  have hsep : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → ∃ g ∈ V, g ∉ W := by
    intro W hW V hV hne
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (hW.2 hV.1 hcon) hcon)
  choose! gg hggV hggW using hsep
  set e : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) → MvPolynomial (Fin n ⊕ Fin M.m) ℂ :=
    fun W ↦ ∏ V ∈ T.erase W, gg W V with he
  have heW : ∀ W ∈ L.minimalPrimes, e W ∉ W := by
    intro W hW hmem
    have : W.IsPrime := hW.1.1
    obtain ⟨V, hV, hgV⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hggW W hW V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) (Finset.ne_of_mem_erase hV).symm hgV
  have heV : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → e W ∈ V := by
    intro W hW V hV hne
    have : V.IsPrime := hV.1.1
    exact Ideal.IsPrime.prod_mem_iff.mpr
      ⟨V, Finset.mem_erase.mpr ⟨hne.symm, (hmemT V).mpr hV⟩, hggV W hW V hV hne⟩
  set F : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := ∑ W ∈ T, β W * e W with hF
  have hsplit : ∀ W ∈ T, F = β W * e W + ∑ V ∈ T.erase W, β V * e V := fun W hW ↦
    (Finset.add_sum_erase T _ hW).symm
  have hrest : ∀ W ∈ L.minimalPrimes, ∑ V ∈ T.erase W, β V * e V ∈ W := by
    intro W hW
    refine Ideal.sum_mem _ fun V hV ↦ Ideal.mul_mem_left _ _ ?_
    exact heV V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) W hW (Finset.ne_of_mem_erase hV)
  have hFW : ∀ W ∈ L.minimalPrimes, F ∉ W := by
    intro W hW hmem
    rw [hsplit W ((hmemT W).mpr hW), Ideal.add_mem_iff_left _ (hrest W hW)] at hmem
    rcases hW.1.1.mem_or_mem hmem with h | h
    · exact hβW W hW h
    · exact heW W hW h
  refine ⟨L ⊔ Ideal.span {F}, le_sup_left, ringKrullDim_quotient_sup_span_lt hFW hdimW, ?_⟩
  intro w hwJ hwu hwB
  obtain ⟨W, hW, hwW⟩ := hcomp w hwJ hwu
  have hFw : eval w F ≠ 0 := by
    intro h0
    refine hwB fun p hp ↦ ?_
    have hle : L ⊔ Ideal.span {F} ≤ RingHom.ker (eval w) := by
      refine sup_le (fun p hp ↦ RingHom.mem_ker.mpr (hwW p (hW.1.2 hp))) (Ideal.span_le.mpr (by simpa using h0))
    exact RingHom.mem_ker.mp (hle hp)
  rw [hsplit W ((hmemT W).mpr hW), map_add, hwW _ (hrest W hW), add_zero, map_mul] at hFw
  exact hβ W hW w hwW (left_ne_zero_of_mul hFw)

end

end GroundTheory.Heights₂.Heights
