import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacFixInert

open GlobalTheory.IdemSupport

variable {D : D7}

theorem parity_step {r t j : ℕ} (hr : Odd r) (ht : Odd t) :
    r + j * t ≠ r + (j + 1) * t ∧ (Even (r + j * t) ∨ Even (r + (j + 1) * t)) := by
  refine ⟨by rw [add_mul, one_mul]; have := ht.pos; omega, ?_⟩
  have hr' : ¬ Even r := Nat.not_even_iff_odd.2 hr
  have ht' : ¬ Even t := Nat.not_even_iff_odd.2 ht
  rcases Nat.even_or_odd j with hj | hj
  · right; simp [Nat.even_add, Nat.even_mul, Nat.even_add_one, hr', ht', hj]
  · left; simp [Nat.even_add, Nat.even_mul, hr', ht', Nat.not_even_iff_odd.2 hj]

theorem r_odd : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem rank_Yc' {j : ℕ} (hj : j ≤ D.R.m) : (Yc D j).rank = D.R.r + j * D.R.t := by
  rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]; rfl

theorem unrPl_mul_inv' {P : Pl D.host.E} {χ η : (AE D)ˣ →* Circle} (h : UnrPl P χ) (h' : UnrPl P η) :
    UnrPl P (χ * η⁻¹) := fun e f he x h1 h2 h3 => by
  show χ x * (η x)⁻¹ = 1
  rw [h e f he x h1 h2 h3, h' e f he x h1 h2 h3, inv_one, mul_one]

theorem unrPl_step' {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ} (h : UnrPl P (μ j))
    (h' : UnrPl P η) : UnrPl P (Lift.chrStep μ η j).1 ∧ UnrPl P (Lift.chrStep μ η j).2 := by
  unfold Lift.chrStep
  split_ifs
  · exact ⟨unrPl_mul_inv' h h', h⟩
  · exact ⟨h, unrPl_mul_inv' h h'⟩

theorem inert_data {P : Pl D.host.E} (hP : Formalism.DivisionValues.conjPl P = P) :
    ∃ ε, IsPlaceIdem D (P.under (𝓞 D.host.F)) ε ∧
      (¬ ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ P = cP P ∧
      ∀ e f, IsPrimeIdem P e f → e = algebraMap (AF D.host.F) (AE D) ε ∧ f = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hc : P = cP P := by
    refine (isConjPl_iff P P).1 fun c hc => ⟨cO D c, ?_, rfl⟩
    have h1 : cO D c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  obtain ⟨ε, hε⟩ := exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hε
  have hd : IsDelta Φ P (algebraMap (AF D.host.F) (AE D) ε) :=
    ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => (eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc.symm)⟩
  refine ⟨ε, hε, ?_, hc, fun e f h => ?_⟩
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

theorem split_mul_eq_zero {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (hns : ¬ ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) :
    ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  rintro e ⟨he1, he2, v', ε', hε', hs⟩
  by_cases hv : v' = v
  · subst hv
    rw [placeIdem_unique hε' hε] at hs
    exact (hns ⟨e, ⟨he1, he2, v', ε, hε, hs⟩, hs⟩).elim
  · have h1 : e = e * algebraMap (AF D.host.F) (AE D) ε' := by rw [← hs, mul_add, he1, he2, add_zero]
    rw [h1, mul_assoc, place_orth hΦ hε' hε hv, mul_zero]

theorem two_not_mem {P : Pl D.host.E} (hc : P = cP P) : (2 : 𝓞 D.host.F) ∉ (P.under (𝓞 D.host.F)).asIdeal := by
  intro h2
  have h : ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have := Ideal.mem_comap.1 h2
    rw [map_ofNat] at this
    rw [Nat.cast_ofNat]
    exact this
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap]
  have : Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.sgO D x = cO D x := by
    apply RingOfIntegers.ext
    rw [cO_coe]
    show D.host.conj (x : D.host.E) = _
    exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm
  rw [this, ← mem_cP, ← hc]

theorem unrAtV_of {P : Pl D.host.E} {ε : AF D.host.F} {χ : (AE D)ˣ →* Circle} {e f : AE D} (he : IsPrimeIdem P e f)
    (hf : f = algebraMap (AF D.host.F) (AE D) ε) (h : UnrPl P χ) : Formalism.IndefR.WeilFull.UnrAtV ε χ := by
  intro x hx a b
  refine h e f he x ?_ a b
  rw [hf]
  linear_combination (-1 : AE D) * hx

theorem isHalf_of_mem' {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
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

theorem vacFix_of_inert (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E)
    (hI : Formalism.IndefR.WeilFull.SphInertAtO ψ S T χS χT om) (hrk : S.rank ≠ T.rank) (hev : Even S.rank ∨ Even T.rank)
    (hP : Formalism.DivisionValues.conjPl P = P) (uS : UnrPl P χS) (uT : UnrPl P χT) : VacFix ψ om P := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨ε, hε, hns, hc, hpi⟩ := inert_data hP
  obtain ⟨e0, f0, h0⟩ := exists_isPrimeIdem hΦ P
  have eS : GlobalTheory.PlaceModel.latFrame S = GlobalTheory.LevSplit.L0sub S := SetLike.coe_injective (GlobalTheory.PlaceModel.coe_latFrame S)
  have eT : GlobalTheory.PlaceModel.latFrame T = GlobalTheory.LevSplit.L0sub T := SetLike.coe_injective (GlobalTheory.PlaceModel.coe_latFrame T)
  have hsS : IsSelfDualC S (GlobalTheory.LevSplit.L0sub S) := eS ▸ GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hsT : IsSelfDualC T (GlobalTheory.LevSplit.L0sub T) := eT ▸ GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨βS, hβS⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ _ hsS.1
  obtain ⟨βT, hβT⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ _ hsT.1
  rintro f hf k ⟨hk, a, a', ha, sk⟩ k' ⟨hk', b, b', hb, sk'⟩
  rw [(hpi a a' ha).2] at sk
  rw [(hpi b b' hb).2] at sk'
  have key : ∀ u ∈ latO S T (GlobalTheory.LevSplit.L0sub S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.LevSplit.L0sub T : Set (Fin T.rank → D.host.E)) (fun w => w = P.under (𝓞 D.host.F)),
      heisO ψ S T u f = f := fun u hu =>
    hf.2 e0 f0 h0 u (GlobalTheory.PlaceModel.latO_le_top _ hu) (Or.inl (by rw [(hpi e0 f0 h0).1]; exact isHalf_of_mem' hε hu))
  refine hI hrk hev _ _ hsS hsT βS βT hβS hβT _ ε hε (two_not_mem hc) (split_mul_eq_zero hε hns)
    (unrAtV_of h0 (hpi e0 f0 h0).2 uS) (unrAtV_of h0 (hpi e0 f0 h0).2 uT) k k' sk sk' ?_ ?_ f hf.1
    ⟨fun u hu => key _ (AddSubgroup.nsmul_mem _ hu 2), fun e _ u hu _ => key u hu⟩
  · exact (GlobalTheory.LevSplit.mem_St_iff βS _ hβS _).2 ((GlobalTheory.LevSplit.ksph_iff S k).1 hk).2
  · exact (GlobalTheory.LevSplit.mem_St_iff βT _ hβT _).2 ((GlobalTheory.LevSplit.ksph_iff T k').1 hk').2

end GlobalTheory.VacFixInert

namespace GlobalTheory.VacFixInert

theorem fixAll_inert : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ t P, Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P →
    FixAll R.toRealDat t P := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC t P hG hP
  have hU := GlobalTheory.T.splittingCharacters_unramified_offLevels R.toRealDat F.lv2 hC.base.lev t P hG
  have hη := hU.1
  have hμ := hU.2
  have hr : Odd D.R.r := r_odd
  have ht : Odd D.R.t := D.R.t_odd
  have hm2 := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · have hW := hC.fullY t k hk
    have u := unrPl_step' (hμ (k + 1) (by omega) hk.le) hη
    have hp := parity_step (j := k) hr ht
    refine vacFix_of_inert _ _ P hW.inert ?_ ?_ hP u.1 u.2
    · rw [rank_Yc' (by omega), rank_Yc' (by omega)]; exact hp.1
    · rw [rank_Yc' (by omega), rank_Yc' (by omega)]; exact hp.2
  · have hW := hC.fullX t
    have u := unrPl_step' (hμ D.R.m (by omega) le_rfl) hη
    have hp := parity_step (j := D.R.m - 1) hr ht
    have hm : D.R.m - 1 + 1 = D.R.m := by omega
    rw [hm] at hp
    have hX : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
    refine vacFix_of_inert _ _ P hW.inert ?_ ?_ hP u.1 u.2
    · rw [rank_Yc' (by omega), hX]; exact hp.1
    · rw [rank_Yc' (by omega), hX]; exact hp.2
  · have hW := hC.fullP i t
    have u1 : UnrPl P (R.toLevCh.mu t ((i : ℕ) + 1)) := hμ ((i : ℕ) + 1) (by omega) i.2
    have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have hWr : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
    refine vacFix_of_inert _ _ P hW.inert ?_ ?_ hP u1 (unrPl_mul_inv' u1 hη)
    · rw [hV, hWr]; have := ht.pos; omega
    · left; rw [hV]; exact hr.add_odd ht

end GlobalTheory.VacFixInert
