import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaPrimeIsAuxiliarySplitSquarefreeLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaSpanHasType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelVectorMovedByRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallField
import Formalism.LocalRingCardinality.ConjSqrtMinusD

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerPhase

variable {D : D7}

theorem jacobi_of_card {PP : Formalism.L2.DIV.Pl D.host.E} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hc : Nat.card (kP PP) = q)
    (hm : (p : 𝓞 D.host.E) ∈ PP.asIdeal) (hd : ((D.host.d : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    jacobiSym (-(D.host.d : ℤ)) p = 1 := by
  classical
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hq.ne_zero)
  letI : Fintype (kP PP) := Fintype.ofFinite _
  have hc' : Fintype.card (kP PP) = q := by rw [← hc, Nat.card_eq_fintype_card]
  have z : ∀ n : ℕ, ((n : ℕ) : kP PP) = 0 ↔ (n : 𝓞 D.host.E) ∈ PP.asIdeal := fun n => by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem
  let e : ZMod q ≃+* kP PP := ZMod.ringEquivOfPrime (kP PP) hq hc'
  have hpq : p = q := by
    have h1 : ((p : ℕ) : ZMod q) = 0 := e.injective (by rw [map_natCast, map_zero]; exact (z p).2 hm)
    exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 ((ZMod.natCast_eq_zero_iff _ _).1 h1)).symm
  subst hpq
  haveI : Fact p.Prime := ⟨hp⟩
  have hs := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hi : IsIntegral ℤ D.host.sqrtMinusD := IsIntegral.of_pow two_pos (by
    rw [hs]
    exact (isIntegral_natCast _).neg)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 D.host.E, b ^ 2 = -((D.host.d : ℕ) : 𝓞 D.host.E) :=
    ⟨⟨D.host.sqrtMinusD, hi⟩, RingOfIntegers.coe_injective ((map_pow _ _ _).trans (hs.trans (by rw [map_neg, map_natCast])))⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff]
  · refine ⟨e.symm (Ideal.Quotient.mk PP.asIdeal b), e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply, ← map_mul, ← pow_two, hb]
    simp
  · intro h0
    refine hd ((z _).1 ?_)
    have := congrArg e h0
    simpa using this

theorem exists_auxiliary_squarefree_level_twistPlaces {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hpl : Lev.IsTwistPlaces D.host.g Q)
    (hoff : ∀ PP ∈ Q, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {p : ℕ}
    (hp : p = D.host.pde ∨ p = D.host.pde') (hQ : ∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ∃ pd : ℕ, IsAuxiliarySplitSquarefreeLevel D (D.host.g 0 * D.host.g 1) pd ∧ pd ∣ D.host.pde * D.host.pde' ∧
      ∀ PP ∈ Q, (pd : 𝓞 D.host.E) ∈ PP.asIdeal := by
  rcases Q.eq_empty_or_nonempty with rfl | ⟨PP, hPP⟩
  · exact ⟨1, auxiliarySplitSquarefreeLevel_one _, one_dvd _, fun _ h => absurd h (Finset.notMem_empty _)⟩
  have h1 : p.Prime ∧ p % 15 = 1 ∧ p ∈ D.host.levelPrimes ∧ (∀ k, p ≠ D.host.g k) ∧ p ∣ D.host.pde * D.host.pde' := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1, D.host.pde_level.1, fun k => (D.host.pde_ne_g k).1, dvd_mul_right _ _⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2, D.host.pde_level.2, fun k => (D.host.pde_ne_g k).2, dvd_mul_left _ _⟩
  obtain ⟨hpr, h15, hl, hg, hdv⟩ := h1
  obtain ⟨q, hq, hc, -⟩ := (hpl PP hPP).1
  have hj := jacobi_of_card hpr hq hc (hQ PP hPP) fun h =>
    hoff PP hPP (GlobalTheory.HalfCompare.mem_of_dvd h ((dvd_mul_left _ _).mul_right _))
  have hpq : p ≠ D.host.q := fun e =>
    hoff PP hPP (GlobalTheory.HalfCompare.mem_of_dvd (hQ PP hPP) (e ▸ ((dvd_mul_left _ _).mul_right _).mul_right _))
  refine ⟨p, ⟨hpr.odd_of_ne_two (by omega), hpr.prime.squarefree, fun p' hp' hd => ?_,
      Nat.Coprime.mul_right ((Nat.coprime_primes hpr (D.host.g_prime 0)).2 (hg 0))
        ((Nat.coprime_primes hpr (D.host.g_prime 1)).2 (hg 1)),
      (GlobalTheory.SeriesTie.PlacesGood.coprime_of_level hpr (fun h => hoff PP hPP (GlobalTheory.HalfCompare.mem_of_dvd (hQ PP hPP)
        ((((Nat.dvd_of_mem_primeFactors h).mul_right _).mul_right _).mul_right _))) hpq hl).symm⟩, hdv, hQ⟩
  rw [(Nat.prime_dvd_prime_iff_eq hp' hpr).1 hd]
  exact hj

abbrev bigF (D : D7) : IntermediateField ℚ ℂ := D.what₂.embLL.toRatAlgHom.fieldRange

instance bigF_fin (D : D7) : FiniteDimensional ℚ (bigF D) :=
  (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toLinearEquiv.finiteDimensional

instance bigF_normal (D : D7) : Normal ℚ (bigF D) :=
  (IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom)).to_normal

theorem small_le_bigF (D : D7) : (Formalism.L2.Host.embLL0 D).fieldRange ≤ (bigF D).toSubfield := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(x : D.what₂.LL), rfl⟩

section Datum

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {j : Fin D.R.m}

theorem isLevDatum_kerDat (hL : R.toLevCh.Is A.μ0) {ξ χ ξR Q ω φ} (hK : KerDat R j ξ χ ξR Q ω φ) {N : ℕ}
    (hN : ∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hcop : Nat.Coprime N (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK)) {k : Subfield ℂ}
    (hk : ∀ PP ∈ Q, ∀ x, ((ξR PP x : ℂˣ) : ℂ) ∈ k) :
    IsLevDatum R.ψ (Vc D j) (Wc D j) (R.ΛV j) (R.ΛW j) N k (R.vacP j) φ := by
  classical
  obtain ⟨-, e, he, hth⟩ := hK.vec
  obtain ⟨cV, hbV⟩ := hL.βV j
  obtain ⟨cW, hbW⟩ := hL.βW j
  have hsV := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbV
  have hsW := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbW
  have hfV := hbV.1
  have hfW := hbW.1
  have hP2 : ∀ PP ∈ R.Pg ∪ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => GlobalTheory.CoverHalf.not_mem_of_coprime PP.isPrime.ne_top hcop (hN PP (Finset.mem_union.1 hPP))
  refine ⟨(R.Pg ∪ Q).image Formalism.L2.DIV.conjPl, cA D e, _, GlobalTheory.RefDatumLev.isIdemSum_conjPl he, ?_, ?_, ?_, ?_, hth⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    show Formalism.L2.DIV.starOHom ((N : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal
    rw [map_natCast]
    exact hN P0 (Finset.mem_union.1 hP0)
  · intro t ht
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (R.βV j) (R.βW j) t)
    · exact ⟨GlobalTheory.T.idempotent_sum_self_dual_frames_bound D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 t hc.1 hc.2, hc.1⟩
    · exact absurd (if_neg hc) ht
  · intro u hu hue t
    have hN' := GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 u hu hue
    have hfr : frMapAdj (Vc D j) (Wc D j) (R.βV j) (R.βW j) (t + N • u) =
        frMapAdj (Vc D j) (Wc D j) (R.βV j) (R.βW j) t + N • frMapAdj (Vc D j) (Wc D j) (R.βV j) (R.βW j) u := by
      rw [GlobalTheory.RefDatumLev.frMapAdj_add', GlobalTheory.RefDatumLev.frMapAdj_nsmul']
    have hKu : IsHalf (cA D e) (N • u) := fun a b => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]
    have hhalf' : IsHalf (cA D e) (t + N • u) ↔ IsHalf (cA D e) t := by
      constructor
      · intro h a b
        have := h a b
        rw [Matrix.add_apply, mul_add, hKu a b] at this
        exact add_right_cancel this
      · intro h a b
        rw [Matrix.add_apply, mul_add, h a b, hKu a b]
    show (if _ then _ else _) = (if _ then _ else _)
    rw [hfr]
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (R.βV j) (R.βW j) t)
    · rw [if_pos ⟨hhalf'.2 hc.1, (GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff hN' _).2 hc.2⟩, if_pos hc]
      refine congrArg₂ (· * ·) (GlobalTheory.RefDatumLev.omegaK_congr _ fun PP hPP =>
        GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 hN' _ (hN PP (Or.inl hPP))) ?_
      have h : ∀ PP ∈ Q, redM PP (frMapAdj (Vc D j) (Wc D j) (R.βV j) (R.βW j) t +
          N • frMapAdj (Vc D j) (Wc D j) (R.βV j) (R.βW j) u) = redM PP (frMapAdj (Vc D j) (Wc D j) (R.βV j) (R.βW j) t) :=
        fun PP hPP => GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 hN' _ (hN PP (Or.inr hPP))
      unfold omegaQ
      split_ifs with h1 h2 h2
      · refine Finset.prod_congr rfl fun PP _ => ?_
        congr 3
        apply Units.ext
        simp only [IsUnit.unit_spec]
        rw [h PP.1 PP.2]
      · exact absurd (fun PP hP => by beta_reduce; rw [← h PP hP]; exact h1 PP hP) h2
      · exact absurd (fun PP hP => by beta_reduce; rw [h PP hP]; exact h2 PP hP) h1
      · rfl
    · rw [if_neg, if_neg hc]
      intro h'
      exact hc ⟨hhalf'.1 h'.1, (GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff hN' _).1 h'.2⟩
  · intro t
    show (if _ then _ else _) ∈ _
    split_ifs
    · refine mul_mem (GlobalTheory.RefDatumLev.omegaK_mem _ _ _) ?_
      unfold omegaQ
      split_ifs
      · exact prod_mem fun PP _ => zpow_mem (hk PP.1 PP.2 _) _
      · exact zero_mem _
    · exact Subfield.zero_mem _

theorem res_mem {ξ : Formalism.L2.Host.HChar D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} {c : (kP PP)ˣ →* ℂˣ} (h : IsRes ξ PP c)
    {k : Subfield ℂ} (hk : ∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ k) (x : (kP PP)ˣ) : ((c x : ℂˣ) : ℂ) ∈ k := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x : kP PP)
  have ha0 : (a : D.host.E) ≠ 0 := fun h0 => x.ne_zero (by
    rw [← ha, show a = 0 from RingOfIntegers.ext h0, map_zero])
  rw [h a (Units.mk0 _ ha0) x rfl ha.symm]
  exact hk _

end Datum

section Cover

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)

include YS in

theorem exists_goodCover_bigF (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (ha : AlgTie T) (hs : SmallHas D Rl.C) {pd : ℕ}
    (haux : IsAuxiliarySplitSquarefreeLevel D (D.host.g 0 * D.host.g 1) pd) (hd : pd ∣ D.host.pde * D.host.pde') (j : Fin D.R.m) (n : ℕ) :
    ∃ C : GlobalTheory.CoverRead.Cover T ((j : ℕ) + 1) T.σ₀, C.d.pd = pd ∧ C.σ₂.fieldRange = (bigF D).toSubfield ∧
      GoodCover T Rl.toRealDat j C n := by
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  rw [← hMg] at haux
  obtain ⟨I, hK, hprod, hsup⟩ := GlobalTheory.HalfCharacter.exists_half_of_auxiliary_split_level D T hT _ haux
  have hLL := small_le_bigF D
  have h0 := (D.host.g_prime 0).ne_zero
  have h1 := (D.host.g_prime 1).ne_zero
  have h2 := D.host.pde_prime.ne_zero
  have h3 := D.host.pde'_prime.ne_zero
  have hN : T.Q.l.M * pd ≠ 0 := mul_ne_zero (by rw [hMg]; positivity) haux.1.pos.ne'
  have hray' : RayIn D (T.Q.l.M * pd) (bigF D).toSubfield := by
    refine BaseRat.RayIn_mono hLL (GlobalTheory.CoverSmall.rayIn_of_dvd hRF D hN (by positivity) ?_ hs.ray)
    rw [hMg, mul_assoc _ D.host.pde]
    exact Nat.mul_dvd_mul_left _ hd
  have hLv : (Formalism.L2.Host.embLL0 D).fieldRange ≤ ((bigF D).val : bigF D →+* ℂ).fieldRange := fun z hz => ⟨⟨z, hLL hz⟩, rfl⟩
  obtain ⟨C, hpd, -, hfr, hG⟩ := GlobalTheory.CoverGalois.exists_goodCover_galois D T Rl.toRealDat hT j (inR j) n _ I haux hK hprod hsup
    (bigF D) ((GlobalTheory.CoverSmall.core_le_small T Rl cG S YS hT ha j).trans fun z hz => hLL hz) (BaseRat.zeta_mem_of_rayIn hN hray')
    ⟨BaseRat.valuesIn_of_le (hs.val.mu0 j) hLv, BaseRat.valuesIn_of_le hs.val.eta hLv⟩ hray'
  exact ⟨C, hpd, hfr, hG⟩

end Cover

set_option linter.unusedVariables false in

theorem exists_adForm_eq_phase_smul : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A)
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (t : D.ntw.Tw) (j : Fin D.R.m)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RatHyp T Rl F κ v₀ O t j hV →
  ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
  ∀ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) →
  ∀ ph : ℂ, IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph →
  ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) χ ξR ω φ,
    KerDat Rl.toRealDat j (Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver Rl.toRealDat (Rl.mu v) (ownAt D v)) ω φ →
  ∀ h ∈ GfC (Vc D j), ∀ P ∈ nabAtr (labLL D) (lamV D j) (Bridge.hLat (Vc D j) (fin (Vc D j) h)),
    ∃ x, adForm Rl.toRealDat j x (fun τ => u τ) = ph • singleSeries Rl.toRealDat j ω φ h (c0L j P) u := by
  intro _ _ hRF D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O t j hV H gramR c0R c0L _ u hu ph hph v χ ξR ω φ hK h hh P _
  classical
  obtain ⟨fw⟩ := H.fw
  have hT := H.laws
  have hcore := H.core
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  have hhalf := (H.pins.2.tuple ()).half
  have hpb : T.pb = Rl.C.P.pb := GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat hT.toLawsM hcore.lev hhalf

  obtain ⟨pd, haux, hdv, hQ⟩ := exists_auxiliary_squarefree_level_twistPlaces (p := ownAt D v) hK.pl hK.off (by
    unfold ownAt
    split_ifs
    exacts [Or.inr rfl, Or.inl rfl]) fun PP hPP => (Finset.mem_filter.1 hPP).2
  obtain ⟨C, rfl, hfr, hC⟩ := exists_goodCover_bigF YS hRF hT H.tieIn.alg H.small haux hdv j (κ j).n
  have hLL : (Formalism.L2.Host.embLL0 D).fieldRange ≤ C.σ₂.fieldRange := hfr ▸ small_le_bigF D

  have hv0 : (Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).ValuesIn 0 (Formalism.L2.Host.embLL0 D) := by
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [H.small.val.del', H.small.val.del]
  have hval : ∀ x, (((Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ bigF D :=
    GlobalTheory.Mem.ValFin.mem_of_orderDvd D.host.E _ (bigF D) hK.fin (GlobalTheory.Mem.Fld.valueField_le_iff.2
      (BaseRat.valuesIn_of_le hv0 fun z hz => ⟨⟨z, small_le_bigF D hz⟩, rfl⟩))
  have htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ := by
    refine ⟨hK.chr, hK.fin, hK.triv, hK.tame, fun w hw => ?_, BaseRat.valuesIn_of_le hv0 hLL⟩
    by_contra hn
    rcases (hK.ram w).1 hn with h1 | ⟨w', h1, h2⟩
    · exact hw (hQ w h1)
    · obtain ⟨c', h3, h4⟩ := h2 _ (hQ w' h1)
      refine hw ?_
      rwa [show c' = (C.d.pd : 𝓞 D.host.E) from RingOfIntegers.ext (by rw [h4]; simp)] at h3

  have hdat : IsLevDatum Rl.ψ (Vc D j) (Wc D j) (Rl.ΛV j) (Rl.ΛW j) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (Rl.vacP j) φ := by
    refine isLevDatum_kerDat hcore.lev hK ?_ ?_ fun PP hPP x => res_mem (hK.res PP hPP) (fun y => hfr ▸ hval y) x
    · rintro PP (hP | hP)
      · have h2 : T.Q.l.Mb ≤ PP.asIdeal := by
          rw [hhalf.1]
          exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
        exact GlobalTheory.HalfCompare.mem_of_dvd (h2 (GlobalTheory.RefDatumLev.natM_mem_Mb T)) (dvd_mul_right _ _)
      · exact GlobalTheory.HalfCompare.mem_of_dvd (hQ PP hP) (dvd_mul_left _ _)
    · refine Nat.Coprime.mul_left ?_ haux.2.2.2.2
      rw [hMg]
      exact Nat.Coprime.mul_left (GlobalTheory.CoverHalf.g_coprime D 0) (GlobalTheory.CoverHalf.g_coprime D 1)
  have hR : IsRat T j hV C (κ j) (ph • singleSeries Rl.toRealDat j ω φ h (c0L j P) u) :=
    ((hph C hC hLL h hh φ hdat (c0L j P) (Submodule.subset_span ⟨P, fun m => hfr ▸ ⟨_, rfl⟩, rfl⟩)).2 _ _ htw).2 _ hK.weil

  have hfix := (GlobalTheory.KerMove.kerDat_move D Γ Pl0 T0 A3.A _ Rl.toRealDat F hcore j _ χ ξR _ ω φ hK fun x => hval x).2
  obtain ⟨cV, hcV⟩ := hcore.lev.βV j
  obtain ⟨cW, hcW⟩ := hcore.lev.βW j
  have hφ : IsThetaFunO Rl.ψ (Vc D j) (Wc D j) φ :=
    (GlobalTheory.VecTheta.vecThetaSD D).2 _ _ _ _ _ _ (Rl.ΛV j) (Rl.ΛW j) _ _ _ _ _ _ _
      (GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hcore.lev.βV j)))
      (GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hcore.lev.βW j))) hcV.1 hcW.1 hK.vec
  have hTy := GlobalTheory.BaseKernelType.singleSeries_hasType hcore.models.inf hK.weil hφ hfix h (c0L j P) u
  obtain ⟨n, z, x, hz, e⟩ := BaseRat.exists_sum_evW YS H.tieIn H.size hcore.lev hpb
    (BaseRat.readsAs_one YS fw (fw.evaluates_of_lUnif H.unif) hV) hC hR fun k hk g => by
      have h1 := hTy k ⟨hk.1, hk.2.1, Subgroup.mem_bot.2 hk.2.2⟩ g
      rw [GlobalTheory.CuspMult.EqCut.levChi_flag1 rfl rfl, one_mul] at h1
      exact congrArg (ph * ·) h1

  choose c hc using fun k => (show z k ∈ (bigF D).toSubfield from hfr ▸ hz k)
  refine ⟨(YS.fi j).e (∑ k, c k • Subtype.val (x k)), ?_⟩
  rw [e, one_smul, show (fun τ => (u τ : (Rl.MW j (sg0 D A3.A)).sm τ)) = v₀ j _ from funext hu]
  change evW YS v₀ j (∑ k, c k • Subtype.val (x k)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [evW_smul, ← hc k]; rfl

end GlobalTheory.KerPhase
