import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharacterEqLadicHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfPowEqOneOfValLt

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwInputs.isChars_of_sideB : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ i b (ρ : GlobalTheory.Triple.Reading D.ntw i b), GlobalTheory.Triple.IsChars cf art ρ := by
  intro _hCh hGAR D cf Rw low Pq S hL eig θ Bs hT hG _hCS hV _hroots art ha i b ρ
  have hchi := GlobalTheory.TwChiGal.firstTwistCharacter_eq_ladic_heckeCharacter D cf Bs.chiD Bs.chi Bs.eta_eq Bs.ringSpec_normalisedCharacter_eq Bs.del_eq hV art ha i b ρ
  refine ⟨hchi, fun j k hk v => ?_⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hN, u, ϖ, π, hu, hϖ1, hϖ2, hπ, hval, hord⟩ := GlobalTheory.TameGenRep.exists_rep D hG k v
  have hAw : IsPlaceOver (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) := D.nd.plOm.2 _
  have hu0 : (u : D.host.E) ≠ 0 := fun h => hu (by
    rw [show u = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hTR : NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u :=
    ⟨_, hAw, D.ntypes.tg_mem k v, ϖ, π, hϖ1, hϖ2, hπ, by simpa using hval⟩
  obtain ⟨c, hc, hcv⟩ := hT k v j u hu0 hTR
  have hxu : IsUnitAt (D.naut.plGw k v) (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : (D.naut.plGw k v).adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    (D.naut.plGw k v) _ hAw ϖ hϖ1 hϖ2 π hπ (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [atFin])
  obtain ⟨n, hn⟩ := hchi j
  have hl := GlobalTheory.Triple.Model.notMem_l (X := D.ntw) hk v
  have e1 := hn.loc (Or.inl hl) hσart.symm
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe cf) (l := D.ntw.l i)
  have hdel : (cf.delAt (D.ntw.l i)).UnrAt (D.naut.plGw k v) :=
    h5.unr _ (GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) h1 (h3 k).symm (D.naut.plGw_over k v))
  rw [GlobalTheory.Triple.blockChar, GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hxu, GlobalTheory.Triple.muBase, HChar.loc_mul,
    hdel _ hxu, mul_one] at e1
  have hg2 := (D.host.g_prime k).two_le
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hm : ((normV (D.naut.plGw k v) - 1 : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    rw [hN]
    intro h
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := (D.naut.plGw k v).asIdeal.sub_mem hgw h
    rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel] at this
  have hI : ∀ τ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      GlobalTheory.GalChar.inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b) τ ^ (normV (D.naut.plGw k v) - 1) = 1 := by
    intro τ hτ
    rw [hN, GlobalTheory.GalChar.inQ, MonoidHom.comp_apply, ← map_pow, D.ntw.twistCharacterFamily_tame i (j.1 + 1) b k _ hgw hl _ hAw τ hτ, map_one]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by rw [hN]; omega)] at hπ
    apply hϖ2
    have h0 : (ϖ : D.host.E) = 0 := (map_eq_zero_iff _ (algebraMap D.host.E D.nd.Om).injective).1 hπ.symm
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _
  have hsub : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (σ π / π - D.ntypes.tg k v π / π) < 1 := by
    have e : σ π / π - D.ntypes.tg k v π / π = (σ π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) -
      (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) := by ring
    rw [e]
    exact Valuation.map_sub_lt _ hσval hval
  have e2 := GlobalTheory.TameCharDet.eq_of_tameChar D.host.E D.nd.Om (D.naut.plGw k v) _ hAw _ (D.ntypes.tg_gen k v) _
    (GlobalTheory.GalChar.inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b)) (hn.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg) _ (by omega) hm hI π _
    hπ0 hπ hord σ hσI hsub
  refine ⟨c, hc, ?_⟩
  rw [GlobalTheory.Triple.Reading.toC_apply, ← GlobalTheory.GalChar.inQ_val, ← e2, GlobalTheory.GalChar.inQ_val, e1]
  exact hcv

end
