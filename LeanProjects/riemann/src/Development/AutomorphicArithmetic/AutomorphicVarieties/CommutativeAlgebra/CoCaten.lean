import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.ExistsIsRegularOfListEqMaximalIdeal
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.RingKrullDimLocalizationQuotientEqHeight

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem cm_of_regular (A : Type) [CommRing A] [IsRegularLocalRing A] : ReciprocityTheory.CA.IsCM A := by
  obtain ⟨xs, h1, h2, h3⟩ :=
    PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal A
  exact ⟨inferInstance, xs.length, h2.symm, xs, rfl, fun r hr => h1 ▸ Ideal.subset_span hr, h3⟩

private theorem dim_quot (A : Type) [CommRing A] [IsRegularLocalRing A] (P : Ideal A) [P.IsPrime]
    (p : Ideal (A ⧸ P)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim ((A ⧸ P) ⧸ p) = ringKrullDim (A ⧸ P) := by
  have h := cm_of_regular A
  set Q := p.comap (Ideal.Quotient.mk P) with hQ
  have hPQ : P ≤ Q := fun x hx => by
    rw [hQ, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact p.zero_mem
  have hp : Q.map (Ideal.Quotient.mk P) = p :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective p
  have e1 := h.height_add_ringKrullDim_quotient P
  have e2 := h.height_add_ringKrullDim_quotient Q
  have e3 := h.height_eq_height_add_height_map_quotient P Q hPQ
  have e4 : ringKrullDim ((A ⧸ P) ⧸ p) = ringKrullDim (A ⧸ Q) := by
    rw [← ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ), hp]
  rw [hp] at e3
  rw [e4]
  rw [e3, ← e1, WithBot.coe_add, add_assoc] at e2
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (P.height_ne_top (Ideal.IsPrime.ne_top ‹_›))
  rw [← hn] at e2
  exact ENat.WithBot.natCast_add_cancel.1 e2

theorem UpperTheory.V.Alg.co_caten :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] [IsDomain R] (p : Ideal R) [p.IsPrime], (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  intro O _ _ _ _ R _ _ hR _ p _
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  obtain ⟨s, hs⟩ : (maximalIdeal R).FG := IsNoetherian.noetherian _
  haveI := co_mvps O O s
  obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O R s (Algebra.ofId O R) (fun i => i.1)
    (fun i => hs ▸ Ideal.subset_span i.2)
  have hsurj : Function.Surjective F := by
    refine co_surj O _ R F (le_sup_of_le_left ?_)
    rw [← hs, Ideal.span_le]
    intro y hy
    have := hF ⟨y, hy⟩
    simp only at this
    rw [← this]
    exact Ideal.mem_map_of_mem _ (GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  haveI : IsRegularLocalRing (MvPowerSeries s O) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O s
  haveI : (RingHom.ker F).IsPrime := RingHom.ker_isPrime _
  let e : (MvPowerSeries s O ⧸ RingHom.ker F) ≃+* R := RingHom.quotientKerEquivOfSurjective hsurj
  have h := dim_quot (MvPowerSeries s O) (RingHom.ker F) (p.comap e)
  rw [RingEquiv.height_comap, ringKrullDim_eq_of_ringEquiv e,
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv (p.comap e) p e
      (Ideal.map_comap_of_surjective _ e.surjective p).symm)] at h
  exact h
