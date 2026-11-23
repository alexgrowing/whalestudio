import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalHomLatticeOfKeepsCompletedLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVacFix

open GlobalTheory.Hk3 GlobalTheory.WeilParts GlobalTheory.IdemSupport

variable {D : D7}

theorem infPart_eq_one {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) {x : AE D}
    (hx : f * (x - 1) = x - 1) : infPart D x = 1 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := of_isPrimeIdem hΦ h
  have h1 := congrArg (infPart D) hx
  rw [RingHom.map_mul, (place_comp hΦ hε).1, zero_mul, RingHom.map_sub, RingHom.map_one, eq_comm, sub_eq_zero] at h1
  exact h1

theorem exists_nonSplit {P : Pl D.host.E} (hP : Formalism.DivisionValues.conjPl P = P) :
    ∃ v ε, NonSplitAt D v ε ∧ ∀ e f, IsPrimeIdem P e f →
      e = algebraMap (AF D.host.F) (AE D) ε ∧ f = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hc : P = cP P := by
    refine (isConjPl_iff P P).1 fun c hc => ⟨cO D c, ?_, rfl⟩
    have h1 : cO D c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  obtain ⟨ε, hε⟩ := exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hε
  have hd : IsDelta Φ P (algebraMap (AF D.host.F) (AE D) ε) :=
    ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => (eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc.symm)⟩
  refine ⟨_, ε, ⟨hε, ?_⟩, fun e f h => ?_⟩
  · rintro ⟨e, ⟨e1, e2, -⟩, e3⟩
    have key : ∀ a : AE D, a * a = a → algebraMap (AF D.host.F) (AE D) ε * a = a → Φ a P ≠ 0 → IsDelta Φ P a :=
      fun a a1 a2 a3 => ⟨by rw [← a2, RingHom.map_mul, h0, zero_mul],
        mul_left_cancel₀ a3 (by rw [← ev_mul, a1, mul_one]),
        fun Q hQ => by rw [← a2, ev_mul, hd.2.2 Q hQ, zero_mul]⟩
    have e1' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, e1]
    have hz : Φ e P * Φ (cA D e) P = 0 := by rw [← ev_mul, e2, ev_zero]
    have hs : Φ e P + Φ (cA D e) P = 1 := by rw [← ev_add, e3, hd.2.1]
    by_cases h : Φ e P = 0
    · have a := key (cA D e) e1' (by rw [← e3]; linear_combination e1' + e2)
        (by rw [h, zero_add] at hs; rw [hs]; exact one_ne_zero)
      have b := delta_conj hΦ a
      rw [cA_cA, ← hc] at b
      exact zero_ne_one (h.symm.trans b.2.1)
    · have a := key e e1 (by rw [← e3]; linear_combination e1 + e2) h
      have b := delta_conj hΦ a
      rw [← hc] at b
      rw [a.2.1, b.2.1, one_mul] at hz
      exact one_ne_zero hz
  · obtain ⟨k1, ε', k2, k3⟩ := of_isPrimeIdem hΦ h
    exact ⟨delta_unique hΦ k1 hd, by rw [k3, placeIdem_unique k2 hε]⟩

theorem isHalf_of_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun w => w = v) : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  intro i j
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = α := FiniteAdeleRing.ext _ fun w => by
      change evalV D.host.F w (β * α) = evalV D.host.F w α
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hP w hw, mul_zero]
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (mul_zero _) hβα
  | zero => exact mul_zero _
  | add x x' _ _ h h' => rw [Matrix.add_apply, mul_add, h, h']
  | neg x _ h => rw [Matrix.neg_apply, mul_neg, h]

theorem vacFix_of_unrPl (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E) (hW : IsWeilDatumO ψ S T χS χT om)
    (uS : UnrPl P χS) (uT : UnrPl P χT) : VacFix ψ om P := by
  by_cases hP : Formalism.DivisionValues.conjPl P = P
  swap
  · exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace ψ S T χS χT om P hW hP uS uT).1
  obtain ⟨v, ε, hv, hu⟩ := exists_nonSplit hP
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨e, e', he⟩ := exists_isPrimeIdem hΦ P
  obtain ⟨rfl, rfl⟩ := hu e e' he
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  rintro f hf k ⟨hk, a, a', ha, sk⟩ k' ⟨hk', b, b', hb, sk'⟩
  rw [(hu a a' ha).2] at sk
  rw [(hu b b' hb).2] at sk'
  exact GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
    χS χT om ⟨η, e1, e4, e3, e2⟩ hW v ε hv (uS _ _ he) (uT _ _ he) k k' sk sk'
    (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
      (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) v ε hv.1 k k'
      (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hk.2.1) (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hk'.2.1))
    f hf.1 fun u hu => hf.2 _ _ he u
      (by
        rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hu
        exact GlobalTheory.PlaceModel.latO_le_top _ hu)
      (Or.inl (isHalf_of_mem hv.1 hu))

theorem unr_and_vacFix : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → ∀ f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.UnrPl P μ' ∧ GlobalTheory.Hk3.UnrPl P (μ' * η'⁻¹) ∧ GlobalTheory.Hk3.VacFix R.ψ ω P := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hc i σ μ' η' H ω hW f₀ f B _ P hP
  have h0 := (GlobalTheory.T.splittingCharacters_unramified_offLevels R F hc.lev A.μ0 P hP).2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have h1 : UnrPl P μ' := fun e f h x a b c => by
    refine (H.mu_cond x ⟨infPart_eq_one h a, b, c⟩).2 ?_
    have h2 : R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = 1 := h0 e f h x a b c
    rwa [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hc.lev.xi_base ▸ hc.lev.xi A.μ0) x, mul_one] at h2
  have h2 : UnrPl P (μ' * η'⁻¹) := fun e f h x a b c => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1 e f h x a b c, H.eta_unr x (infPart_eq_one h a) b c, inv_one, mul_one]
  exact ⟨h1, h2, vacFix_of_unrPl _ _ _ _ _ ω P hW h1 h2⟩

end GlobalTheory.ConjVacFix

end
