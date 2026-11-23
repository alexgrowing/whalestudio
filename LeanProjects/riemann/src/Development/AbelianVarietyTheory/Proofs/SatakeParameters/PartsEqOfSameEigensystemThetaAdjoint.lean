import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.SepLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem endV_ext (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (f g : Module.End ℂ (R.HV i t).H)
    (h : ∀ x, f (R.jV i t x) = g (R.jV i t x)) : f = g := by
  have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.L i t).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HV i t
  have hk := kForm_semi (R.jV i t) (R.HV i t).e (R.B.L i t).pres.extL (fun x => hM.jV i t x) hinj (hrange.trans hB.2.symm)
    (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hB.1
  exact LinearMap.ext_on_range hk.2 (fun k => h _)

theorem hkF_eq_sum (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : Bridge.Gf V → W) : hkF V P c F = c.sum fun d z => z • hkF V P (Finsupp.single d 1) F := by
  have e : ∀ d, hkF V P (Finsupp.single d 1) F = fun h => ∑ γ ∈ rep V P d, F (h * (finHom V).rangeRestrict γ) := by
    intro d
    funext h
    simp [hkF]
  simp only [e]
  funext g
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
  rfl

theorem hkF_nonlab (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (hd : ¬ IsLab V P d) (F : Bridge.Gf V → W) : hkF V P (Finsupp.single d 1) F = 0 := by
  funext g
  simp [hkF, rep, hd]

set_option maxHeartbeats 1000000 in

theorem opsV_sum (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) (hh : IsOpsV R i t h) (P : Pl D.host.E) (hP : Good R t P)
    (c : List ℤ →₀ ℂ) (x : (R.HV i t).H) : h P c x = c.sum fun d z => z • h P (Finsupp.single d 1) x := by
  have hinj : Function.Injective (R.HV i t).e := (hM.HV i t).1
  apply hinj
  refine (hh P hP c x).trans ((hkF_eq_sum _ _ _ _).trans ?_)
  refine Eq.trans ?_ (map_finsuppSum (R.HV i t).e c _).symm
  refine Finsupp.sum_congr fun d _ => ?_
  exact (congrArg (c d • ·) (hh P hP _ x)).symm.trans (map_smul _ _ _).symm

set_option maxHeartbeats 1000000 in

theorem opsV_nonlab (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) (hh : IsOpsV R i t h) (P : Pl D.host.E) (hP : Good R t P)
    (d : List ℤ) (hd : ¬ IsLab (Vc D i) P d) : h P (Finsupp.single d 1) = 0 := by
  have hinj : Function.Injective (R.HV i t).e := (hM.HV i t).1
  refine LinearMap.ext fun x => hinj ?_
  exact (hh P hP _ x).trans ((hkF_nonlab _ _ _ hd _).trans (map_zero _).symm)

theorem q_ne_zero (R : RealDat D A Ks) (hF : R.IsFam) (P : Pl0) : A.q P ≠ 0 := by
  obtain ⟨_, _, _, hT⟩ := hF.tie
  rw [hT.q P]
  intro h0
  apply (R.pl P).ne_bot
  rw [← Ideal.absNorm_eq_zero_iff, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact h0

theorem blockProd_map_ne_zero (i : Fin D.R.m) (t : T) (P : A.ok t) :
    ((A.fam.L i t).blockProd P).map D.what₂.embLL ≠ 0 := by
  intro h
  have h0 := congrArg (fun p => Polynomial.coeff p 0) h
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h0
  rw [Polynomial.coeff_zero_eq_eval_zero] at h0
  simp [BlockDat.blockProd, FamIn.fam, liftDat, Formalism.L2.Col.blockPoly, Polynomial.eval_prod] at h0

theorem evC_single (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  simp [evC, hd]

theorem isLab_splitLab (V : HSp D) (P : Pl D.host.E) (hP : conjPl P ≠ P) (k : ℕ) (hk : k ≤ V.rank) :
    IsLab V P (splitLab V.rank k) := by
  refine (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing V P _).2 ⟨?_, ?_, fun h => absurd h hP⟩
  · simp [splitLab]
    omega
  · unfold splitLab
    refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
    · exact List.pairwise_replicate.2 (Or.inr le_rfl)
    · exact List.pairwise_replicate.2 (Or.inr le_rfl)
    · intro a ha b hb
      rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
      norm_num

theorem evC_splitC (V : HSp D) (P : Pl D.host.E) (hP : conjPl P ≠ P) (a : List ℤ → ℂ) (z : ℕ → ℂ) :
    evC V P a (splitC V.rank z) = ∑ j ∈ Finset.range (V.rank + 1), z j * a (splitLab V.rank j) := by
  unfold evC splitC
  rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> ring)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finsupp.sum_single_index (by simp), if_pos (isLab_splitLab V P hP j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))]

theorem heckePoly_cancel (nV nW q : ℕ) (κ : ℂ) (B : ℂ[X]) (z : ℕ → ℕ → ℂ) (a a' : ℕ → ℂ) (hq : q ≠ 0) (hκ : κ ≠ 0)
    (hB : B ≠ 0)
    (hpoly : ∀ b : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nV q (fun k => ∑ j ∈ Finset.range (nW + 1), z k j * b j) =
      (Formalism.L2.Col.heckePolyOf nW q b).comp (C κ * X) * B)
    (heq : ∀ k, k ≤ nV → ∑ j ∈ Finset.range (nW + 1), z k j * a j = ∑ j ∈ Finset.range (nW + 1), z k j * a' j) :
    ∀ j, j ≤ nW → a j = a' j := by
  intro j hj
  have h1 : Formalism.L2.Col.heckePolyOf nV q (fun k => ∑ i ∈ Finset.range (nW + 1), z k i * a i) =
      Formalism.L2.Col.heckePolyOf nV q (fun k => ∑ i ∈ Finset.range (nW + 1), z k i * a' i) := by
    unfold Formalism.L2.Col.heckePolyOf
    refine Finset.sum_congr rfl fun k hk => ?_
    dsimp only
    rw [heq k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
  rw [hpoly, hpoly] at h1
  have h2 := congrArg (fun p => Polynomial.coeff p j) (mul_right_cancel₀ hB h1)
  simp only [Polynomial.comp_C_mul_X_coeff] at h2
  have h3 := mul_right_cancel₀ (pow_ne_zero j hκ) h2
  have hc : ∀ b : ℕ → ℂ, (Formalism.L2.Col.heckePolyOf nW q b).coeff j = (-1) ^ j * (q : ℂ) ^ (j * (j - 1) / 2) * b j := by
    intro b
    unfold Formalism.L2.Col.heckePolyOf
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Nat.lt_succ_iff.2 hj]
  rw [hc, hc] at h3
  have hne : (-1 : ℂ) ^ j * (q : ℂ) ^ (j * (j - 1) / 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
  exact mul_left_cancel₀ hne h3

set_option maxHeartbeats 8000000 in

theorem parts_eq_of_labW : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ c c', ∀ w ∈ R.Wc' j c, ∀ w' ∈ R.Wc' j c', LinearMap.adjoint (R.thG j A3.A.μ0) w ≠ 0 → LinearMap.adjoint (R.thG j A3.A.μ0) w' ≠ 0 → labW j pl cW c = labW j pl cW c' → R.Wc' j c = R.Wc' j c' := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hInt hCW hEx hSch _ hAbs j pl cV cW hLD c c' w hw w' hw' hy hy' hlab
  obtain ⟨hCoreF, hSF, hOkI, hOnto, -, hWc, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hCW
  have hCore := hCoreF hEx
  have hw2 : w ∈ Wcc R.toRealDat R.SF j c := (hWc j c) ▸ hw
  have hw2' : w' ∈ Wcc R.toRealDat R.SF j c' := (hWc j c') ▸ hw'
  rw [hWc, hWc]
  obtain ⟨-, hOps⟩ := GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models
  obtain ⟨hV, hVops, -⟩ := hOps j A3.A.μ0
  have hM := hCore.models
  obtain ⟨y, hydef⟩ : ∃ y, y = LinearMap.adjoint (R.thG j A3.A.μ0) w := ⟨_, rfl⟩
  obtain ⟨y', hy'def⟩ : ∃ y', y' = LinearMap.adjoint (R.thG j A3.A.μ0) w' := ⟨_, rfl⟩
  rw [← hydef] at hy
  rw [← hy'def] at hy'

  have hsys : ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cV0 cW0, MatchW R.toRealDat j A3.A.μ0 P cV0 cW0 →
      hV P cV0 y = evC (Wc D j) P (c P) cW0 • y ∧ hV P cV0 y' = evC (Wc D j) P (c' P) cW0 • y' := by
    intro P hP cV0 cW0 hm
    have h := (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 hCore hSch hAbs R.SF hSF j A3.A.μ0 P hP cV0 cW0 hm hV hVops).2
    rw [hydef, hy'def]
    exact ⟨h c w hw2, h c' w' hw2'⟩

  have hfam : ∀ i, hV (pl i) (cV i) y = labW j pl cW c i • y ∧ hV (pl i) (cV i) y' = labW j pl cW c i • y' := by
    intro i
    have hg := hLD.good i
    have hm := hLD.mat i
    have h12 := hsys (pl i) hg (cV i) (cW i) hm
    have hl : labW j pl cW c' i = labW j pl cW c i := (congrFun hlab i).symm
    exact ⟨h12.1, h12.2.trans (congrArg (fun μ : ℂ => μ • y') hl)⟩
  have hcancel : ∀ μ ν : ℂ, μ • y = ν • y → μ = ν := fun μ ν h => smul_left_injective ℂ hy h
  have hcancel' : ∀ μ ν : ℂ, μ • y' = ν • y' → μ = ν := fun μ ν h => smul_left_injective ℂ hy' h
  have hne : ∀ {u : (R.HW j (sg0 D A3.A)).H} {cc}, u ∈ Wcc R.toRealDat R.SF j cc → LinearMap.adjoint (R.thG j A3.A.μ0) u ≠ 0 →
      Wcc R.toRealDat R.SF j cc ≠ ⊥ := by
    intro u cc hu hu0 hbot
    rw [hbot, Submodule.mem_bot] at hu
    exact hu0 (by rw [hu, map_zero])
  refine GlobalTheory.T.weight_cocharacter_eq_of_good_places R.toRealDat F.lv2 hCore R.SF hSF j c c' (hne hw2 (hydef ▸ hy)) (hne hw2' (hy'def ▸ hy')) ?_ ?_
  ·
    intro P hP hconj k hk
    obtain ⟨P0, hP0, rfl⟩ := (hOnto P hP).2 hconj
    obtain ⟨z, hz, hpoly⟩ := GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime R.toRealDat F.lv2 hCore hSch j A3.A.μ0 ⟨P0, hP0⟩
    have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).2 j A3.A.μ0 hV hVops
      ⟨P0, hP0⟩
    have heq : ∀ k', k' ≤ (Vc D j).rank →
        ∑ i ∈ Finset.range ((Wc D j).rank + 1), z k' i * c (R.pl P0) (splitLab (Wc D j).rank i) =
          ∑ i ∈ Finset.range ((Wc D j).rank + 1), z k' i * c' (R.pl P0) (splitLab (Wc D j).rank i) := by
      intro k' hk'
      have hm := hz k' hk'
      have h12 := hsys (R.pl P0) hP _ _ hm
      let i0 : (A3.liftI j A3.A.μ0).OpIx := Sum.inl (⟨P0, hP0⟩, k')
      have hop : hV (pl i0) (cV i0) = hV (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k') 1) := by
        apply endV_ext R.toRealDat hM j A3.A.μ0
        intro x
        have e1 := hLD.op hV hVops i0 x
        have e2 := hsplit k' hk' x
        exact e1.symm.trans e2
      have hf := hfam i0
      have a1 := hcancel _ _ ((h12.1.symm.trans (LinearMap.congr_fun hop y).symm).trans hf.1)
      have a2 := hcancel' _ _ ((h12.2.symm.trans (LinearMap.congr_fun hop y').symm).trans hf.2)
      have b1 := evC_splitC (Wc D j) (R.pl P0) hconj (c (R.pl P0)) (z k')
      have b2 := evC_splitC (Wc D j) (R.pl P0) hconj (c' (R.pl P0)) (z k')
      exact b1.symm.trans (a1.trans (a2.symm.trans b2))
    have hq : A3.A.q P0 ≠ 0 := q_ne_zero R.toRealDat hCore.fam P0
    have hκ : D.what₂.embLL (A3.A.etaVal P0 : D.what₂.LL) * (A3.A.q P0 : ℂ) ^ ((D.R.t + 1) / 2) ≠ 0 :=
      mul_ne_zero ((_root_.map_ne_zero _).2 (Units.ne_zero _)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
    exact heckePoly_cancel (Vc D j).rank (Wc D j).rank (A3.A.q P0) _ _ z (fun i => c (R.pl P0) (splitLab (Wc D j).rank i))
      (fun i => c' (R.pl P0) (splitLab (Wc D j).rank i)) hq hκ (blockProd_map_ne_zero j A3.A.μ0 ⟨P0, hP0⟩) hpoly heq k hk
  ·
    intro P d hP hconj hd
    obtain ⟨Q, hQ, rfl⟩ := (hOnto P hP).1 hconj
    have hFix := GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hCW A3.A.μ0 (R.plI Q) hP hconj
    have hTwo := GlobalTheory.T.twoSidedHeckePartner_inertPrime hHowe R.toRealDat F.lv2 hInt hCore hSch A3.A.μ0 (R.plI Q) hP hconj hFix
    obtain ⟨cV', hm⟩ := (hTwo.2 j).2 (Finsupp.single d 1)
    have h12 := hsys (R.plI Q) hP cV' _ hm
    have htie := (hCW.inert.hL j A3.A.μ0).some
    have hIL := GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models j A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
      (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2)
      (fun k hk => ⟨(hOkI _ k.1 k.1.2).1, (hOkI _ k.1 k.1.2).2,
        ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents _ _).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1⟩) htie

    have hlabop : ∀ e, ∃ μ : ℂ, hV (R.plI Q) (Finsupp.single e 1) y = μ • y ∧
        hV (R.plI Q) (Finsupp.single e 1) y' = μ • y' := by
      intro e
      by_cases he : GlobalTheory.Hk3.IsLab (Vc D j) (R.plI Q) e
      · obtain ⟨hlen, hpw, hdual⟩ := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) (R.plI Q) e).1 he
        obtain ⟨s, hs2, hspw, hspos, rfl⟩ := (GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank e).1 ⟨hlen, hpw, hdual hconj⟩
        have hok : Formalism.L2.Col.InertTypeOk (Vc D j).rank s := ⟨hspw, hspos, hs2⟩
        have hop1 := (hIL (⟨Q, hQ⟩, s) hok).2.2.2 hV hVops
        let i0 : (A3.liftI j A3.A.μ0).OpIx := Sum.inr (⟨Q, hQ⟩, s)
        have hop : hV (pl i0) (cV i0) = hV (R.plI Q) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1) := by
          apply endV_ext R.toRealDat hM j A3.A.μ0
          intro x
          have e1 := hLD.op hV hVops i0 x
          have e2 := hop1 x
          exact e1.symm.trans e2
        have hf := hfam i0
        exact ⟨_, (LinearMap.congr_fun hop y).symm.trans hf.1, (LinearMap.congr_fun hop y').symm.trans hf.2⟩
      · refine ⟨0, ?_, ?_⟩
        · rw [opsV_nonlab R.toRealDat hM j A3.A.μ0 hV hVops _ hP e he, zero_smul]
          rfl
        · rw [opsV_nonlab R.toRealDat hM j A3.A.μ0 hV hVops _ hP e he, zero_smul]
          rfl
    choose μ hμ using hlabop
    have hs1 : hV (R.plI Q) cV' y = (cV'.sum fun e a => a * μ e) • y := by
      rw [opsV_sum R.toRealDat hM j A3.A.μ0 hV hVops _ hP cV' y]
      simp only [Finsupp.sum, (hμ _).1, smul_smul, Finset.sum_smul]
    have hs2 : hV (R.plI Q) cV' y' = (cV'.sum fun e a => a * μ e) • y' := by
      rw [opsV_sum R.toRealDat hM j A3.A.μ0 hV hVops _ hP cV' y']
      simp only [Finsupp.sum, (hμ _).2, smul_smul, Finset.sum_smul]
    have f1 := hcancel _ _ (h12.1.symm.trans hs1)
    have f2 := hcancel' _ _ (h12.2.symm.trans hs2)
    rw [evC_single _ _ _ _ hd] at f1 f2
    exact f1.trans f2.symm
end GlobalTheory.Hk3.SepLift
