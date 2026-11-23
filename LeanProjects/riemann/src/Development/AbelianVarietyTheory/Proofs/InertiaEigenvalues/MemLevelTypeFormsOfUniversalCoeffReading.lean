import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevel
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF Vc Wc)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType

variable {D : D7} {S T : HSp D}

section Series

open Classical in

theorem omegaG_levT_mul_inv {n r : ℕ} (G : TypeDat D r) (hr : r ≤ n) (K : ∀ PP : Pl D.host.E, GL (Fin r) (kP PP))
    (a : G0 G.Pg r) (ha : ∀ PP : ↥G.Pg, a PP = K PP.1) (hH : a ∈ G.P.H)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaG G.levT G.muC (fun PP => y PP * ((K PP)⁻¹).val) = ((((G.P.chi ⟨a, hH⟩)⁻¹ *
      ∏ PP : ↥G.Pg, G.muC PP.1 (GeneralLinearGroup.det (a PP)) : ℂˣ)) : ℂ) * omegaG G.levT G.muC y := by
  have eK : ∀ (PP : Pl D.host.E) (u : Matrix (Fin n) (Fin r) (kP PP)) (k : Matrix (Fin r) (Fin r) (kP PP)),
      u * k = ((1 : GL (Fin n) (kP PP))).val * u * k := fun PP u k => by rw [Units.val_one, Matrix.one_mul]
  have low : ∀ (PP : Pl D.host.E) (u : Matrix (Fin n) (Fin r) (kP PP)), LowZero r (u * ((K PP)⁻¹).val) ↔ LowZero r u := fun PP u => by
    rw [eK PP]; exact GlobalTheory.AdjDatumMove.lowZero_mul_iff (one_mem _) _ u
  have top : ∀ PP : ↥G.Pg, LowZero r (y PP.1) → topL r (y PP.1 * ((K PP.1)⁻¹).val) = topL r (y PP.1) * ((a PP)⁻¹).val :=
    fun PP hu => by
      rw [eK PP.1, GlobalTheory.AdjDatumMove.topL_mul hr (one_mem _) _ hu, show upperLeftBlock hr (1 : GL (Fin n) (kP PP.1)) = 1 from blockDiagonalExtendByOnePrimeField_one _ _,
        Units.val_one, Matrix.one_mul, ha]
  by_cases hy : (∀ PP ∈ G.Pg, LowZero r (y PP)) ∧ ∃ g : G0 G.Pg r, (∀ PP : ↥G.Pg, (g PP).val = topL r (y PP.1)) ∧ g ∈ G.P.H
  · obtain ⟨h0, g, hg, hgH⟩ := hy
    rw [omegaG_levT_of G h0 g hg hgH,
      omegaG_levT_of G (fun PP hP => (low PP _).2 (h0 PP hP)) (g * a⁻¹)
        (fun PP => by rw [top PP (h0 PP.1 PP.2), ← hg PP]; rfl) (mul_mem hgH (inv_mem hH))]
    have e : (⟨g * a⁻¹, mul_mem hgH (inv_mem hH)⟩ : G.P.H) = ⟨g, hgH⟩ * (⟨a, hH⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.coe_prod]
    have e2 : ∀ PP : ↥G.Pg, (((G.muC PP.1 (GeneralLinearGroup.det ((g * a⁻¹) PP)) : ℂˣ)) : ℂ)⁻¹ =
        (((G.muC PP.1 (GeneralLinearGroup.det (a PP)) : ℂˣ)) : ℂ) *
          (((G.muC PP.1 (GeneralLinearGroup.det (g PP)) : ℂˣ)) : ℂ)⁻¹ := fun PP => by
      rw [Pi.mul_apply, Pi.inv_apply, map_mul, map_mul, map_inv, map_inv, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val,
        inv_inv, mul_comm]
    rw [Finset.prod_congr rfl fun PP _ => e2 PP, Finset.prod_mul_distrib]
    ring
  · rw [omegaG_levT_zero G hy, mul_zero]
    refine omegaG_levT_zero G fun h => hy ?_
    obtain ⟨h0, g, hg, hgH⟩ := h
    have h0' : ∀ PP ∈ G.Pg, LowZero r (y PP) := fun PP hP => (low PP _).1 (h0 PP hP)
    refine ⟨h0', g * a, fun PP => ?_, mul_mem hgH hH⟩
    have := (hg PP).trans (top PP (h0' PP.1 PP.2))
    show (g PP * a PP).val = _
    rw [Units.val_mul, this, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

variable {B : Base S T}

structure Lifts (B : Base S T) (a : G0 B.G.Pg T.rank) (κ : GA D T) : Prop where
  fin : κ ∈ GfC T
  st : Lev.finE T κ ∈ St B.F.βT
  red : ∀ PP : ↥B.G.Pg, a PP = redFn B.F.βT PP.1 (Lev.finE T κ)

theorem lifts_of_isLiftG0 {a : G0 B.G.Pg T.rank} {κ : GA D T} (h : Lev.IsLevelLift T B.F.βT B.G.levT a κ) : Lifts B a κ :=
  ⟨h.1, parLev_St h.2.1, fun PP => (congrFun h.2.2 PP).symm.trans (GlobalTheory.AdjDatumMove.restrictedBlock_self_apply _)⟩

open Classical in

theorem om_type (hB : B.Good) (hS : S.SigOK) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) {ω : PairRep S T} (hω : B.IsWeil 1 ω)
    {a : G0 B.G.Pg T.rank} (hH : a ∈ B.G.P.H) {κ : GA D T} (hκ : Lifts B a κ)
    {φ φ' : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ} (s : ↥Q → ℂˣ)
    (hφ : ∀ (PP : ↥Q) y, φ PP ((redFn B.F.βT PP.1 (Lev.finE T κ)).val * y) = (s PP : ℂ) * φ' PP y) :
    ω (1, κ) (B.vecAt Q φ') = ((B.G.P.chi ⟨a, hH⟩ * (∏ PP, s PP)⁻¹ : ℂˣ) : ℂ) • B.vecAt Q φ := by
  have hν : (Twist.triv Circle Q : Twist D Circle).Good := Twist.triv_good ((dualTypePlaces_isSplitNonconjugate_of_admissible hQ).mono
    (fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP)))
  set bδ : ℂˣ := ∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) with hbδ
  set bg : ℂˣ := ∏ PP : ↥B.G.Pg, B.G.muC PP.1 (GeneralLinearGroup.det (a PP)) with hbg
  have hD : ∀ x, B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ') x =
      (((((B.G.P.chi ⟨a, hH⟩)⁻¹ * bg) * (bδ * ∏ PP, s PP))⁻¹ : ℂˣ) : ℂ) *
        B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ) (actO S T 1 κ x) := fun x => by
    rw [datumFn_act B.F B.G (B.de.Q ∪ Q) (one_mem_St S _) hκ.st (a := (((B.G.P.chi ⟨a, hH⟩)⁻¹ * bg : ℂˣ) : ℂ))
      (b := ((bδ * ∏ PP, s PP : ℂˣ) : ℂ)) (ω' := B.locFn Q φ')
      (fun y => by
        simp only [finE_one, Units.val_one, Matrix.one_mul]
        exact omegaG_levT_mul_inv B.G B.hr _ a hκ.red hH y)
      (fun y => by
        simp only [finE_one, inv_one, Units.val_one, Matrix.mul_one]
        unfold Base.locFn
        rw [Finset.prod_congr rfl fun PP _ => flat_mul B.hr _ _ (y PP), Finset.prod_congr rfl fun PP _ => hφ PP (y PP.1),
          Finset.prod_mul_distrib, Finset.prod_mul_distrib, hbδ]
        simp only [Units.val_mul, Units.coe_prod]
        ring) x, ← Units.val_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  refine (om_vec_move hB hS hν hQ hω (one_mem _) hκ.fin (one_mem_St S _) hκ.st hD).trans ?_
  rw [← Units.val_mul]
  congr 2
  have hv : vacC B (Twist.triv Circle Q) 1 κ = bg * bδ := by
    unfold vacC
    simp only [map_one, redFn_one, inv_one, one_mul]
    rw [show allP B (Twist.triv Circle Q : Twist D Circle).Q = allP B Q from rfl, prod_allP hQ, hbδ, hbg]
    have h3 : ∏ PP ∈ Q, resP B (Twist.triv Circle Q) PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) = 1 :=
      Finset.prod_eq_one fun PP hP => by
        rw [resP_q (ν := Twist.triv Circle Q) hQ hP]
        simp [Twist.resC, Twist.triv]
    rw [h3, mul_one, ← Finset.prod_coe_sort B.G.Pg]
    congr 1
    · exact Finset.prod_congr rfl fun PP _ => by rw [resP_g (ν := Twist.triv Circle Q) hQ PP.2, hκ.red]
    · exact Finset.prod_congr rfl fun PP hP => by rw [resP_d (ν := Twist.triv Circle Q) hQ hP]
  rw [hv]
  generalize B.G.P.chi ⟨a, hH⟩ = c
  generalize ∏ PP, s PP = t
  simp only [mul_inv, inv_inv]
  calc bg * bδ * (c * bg⁻¹ * (bδ⁻¹ * t⁻¹)) = (bg * bg⁻¹) * (bδ * bδ⁻¹) * (c * t⁻¹) := by ac_rfl
    _ = c * t⁻¹ := by rw [mul_inv_cancel, mul_inv_cancel, one_mul, one_mul]

theorem om_fock (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) {ω : PairRep S T} (hω : B.IsWeil 1 ω)
    {κ : GA D T} (hκ : κ ∈ GfC T) (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (P : PolF D T.rank S.rank) :
    ω (1, κ) (B.F.fock (B.vecAt Q φ) P) = B.F.fock (ω (1, κ) (B.vecAt Q φ)) P := by
  have hth : IsThetaFunO B.F.ψ S T (B.vecAt Q φ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf (Base.isThetaAt_vecAt hB hQ φ) hB.frame.vac.2.theta
  rw [Frame.fock, (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hB.frame.vac.2.inf (fun _ => 1) (fun _ => 1)
    (fun τ => (B.F.BS τ).val) (fun τ => (B.F.BS τ).val) B.F.sT B.F.sT B.F.BT B.F.BT 1 κ
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hκ])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hκ]) _ hth P).2]
  rfl

theorem series_type (hB : B.Good) (hS : S.SigOK) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) {ω : PairRep S T} (hω : B.IsWeil 1 ω)
    {a : G0 B.G.Pg T.rank} (hH : a ∈ B.G.P.H) {κ : GA D T} (hκ : Lifts B a κ)
    {φ φ' : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ} (s : ↥Q → ℂˣ)
    (hφ : ∀ (PP : ↥Q) y, φ PP ((redFn B.F.βT PP.1 (Lev.finE T κ)).val * y) = (s PP : ℂ) * φ' PP y)
    (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    series B.F ω (B.vecAt Q φ') h P (g * κ) =
      ((B.G.P.chi ⟨a, hH⟩ * (∏ PP, s PP)⁻¹ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  have e2 : ((h, g * κ) : GA D S × GA D T) = (h, g) * (1, κ) := by simp
  rw [series_apply, series_apply, e2, map_mul, Module.End.mul_apply, om_fock hB hQ hω hκ.fin, om_type hB hS hQ hω hH hκ s hφ,
    Frame.fock, GlobalTheory.FiniteFock.pureTensorO_smul, LinearMap.map_smul]
  rfl

theorem theta_type (hB : B.Good) (hS : S.SigOK) {ω : PairRep S T} (hω : B.IsWeil 1 ω)
    {a : G0 B.G.Pg T.rank} (hH : a ∈ B.G.P.H) {κ : GA D T} (hκ : Lifts B a κ)
    (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    B.theta ω h P (g * κ) = ((B.G.P.chi ⟨a, hH⟩ : ℂˣ) : ℂ) * B.theta ω h P g := by
  have := series_type hB hS (Base.admissible_empty_of_good hB) hω hH hκ (φ := fun _ _ => 1) (φ' := fun _ _ => 1) (fun _ => 1)
    (fun _ _ => by simp) h P g
  rwa [Finset.prod_const_one, inv_one, mul_one] at this

theorem gen_type (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {ω : PairRep S T}
    (hω : B.IsWeil 1 ω) {a : G0 B.G.Pg T.rank} (hH : a ∈ B.G.P.H) {κ : GA D T} (hκ : Lifts B a κ)
    (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    B.gen ω ψ h P (g * κ) = ((B.G.P.chi ⟨a, hH⟩ : ℂˣ) : ℂ) * B.gen ω ψ h P g := by
  set d : ∀ PP : Pl D.host.E, (kP PP)ˣ := fun PP => GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ)) with hd
  have hv := series_type hB hS hQ hω hH hκ (φ := fun PP => flat (ψ.resC PP.1)) (φ' := fun PP => flat (ψ.resC PP.1))
    (fun PP => ψ.resC PP.1 (d PP.1)) (fun PP y => flat_mul B.hr _ _ y) h P g
  have hdet : detChar T ψ.chi κ = ∏ PP ∈ ψ.Q, ψ.res PP (d PP) := GlobalTheory.T.unitaryDetCharacter_eq_prod_residue_goodBaseFrame B hB ψ hψ hκ.fin hκ.st
  have e1 : ((detChar T ψ.chi κ : Circle) : ℂ) * (((∏ PP : ↥ψ.Q, ψ.resC PP.1 (d PP.1))⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [hdet, Finset.prod_coe_sort ψ.Q (fun PP => ψ.resC PP (d PP))]
    have : ((∏ PP ∈ ψ.Q, ψ.res PP (d PP) : Circle) : ℂ) = ((∏ PP ∈ ψ.Q, ψ.resC PP (d PP) : ℂˣ) : ℂ) := by
      simp only [Twist.resC, MonoidHom.comp_apply, Units.coe_prod]
      exact map_prod Circle.coeHom _ _
    rw [this, Units.mul_inv]
  simp only [Base.gen, LinearMap.comp_apply, twistBy_apply, Base.vecFlat]
  rw [hv, detChar_mul hψ.real, Circle.coe_mul, Units.val_mul]
  linear_combination (((detChar T ψ.chi g : Circle) : ℂ) * ((B.G.P.chi ⟨a, hH⟩ : ℂˣ) : ℂ) *
    series B.F ω (B.vecAt ψ.Q fun PP => flat (ψ.resC PP.1)) h P g) * e1

theorem xiCoef_type {C : Type} [AddCommGroup C] [Fintype C] (hB : B.Good) (hS : S.SigOK) {u : UnivTwist D C}
    {Q : Finset (Pl D.host.E)} (hu : u.Good Q) (hQ : B.admitted Q)
    {Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ} (hΦ : Base.IsAdmFam u Q Φ)
    {ω : PairRep S T} (hω : B.IsWeil 1 ω) {a : G0 B.G.Pg T.rank} (hH : a ∈ B.G.P.H) {κ : GA D T} (hκ : Lifts B a κ)
    (h : GA D S) (P : PolF D T.rank S.rank) (c : ↥Q → C) (g : GA D T) :
    B.xiCoef ω u Q Φ h P c (g * κ) = ((B.G.P.chi ⟨a, hH⟩ : ℂˣ) : ℂ) * B.xiCoef ω u Q Φ h P c g := by
  set dκ : ↥Q → C := fun PP => Multiplicative.toAdd (u.kap PP.1 (GeneralLinearGroup.det (redFn B.F.βT PP.1 (Lev.finE T κ))))
    with hdκ
  have hmul : Multiplicative.toAdd (detChar T (u.delQ Q) (g * κ)) = Multiplicative.toAdd (detChar T (u.delQ Q) g) + dκ := by
    rw [detChar_mul hu.delQ_real, toAdd_mul, delQ_det_of_red hB hu hκ.fin hκ.st]
  set b := c - Multiplicative.toAdd (detChar T (u.delQ Q) g) - dκ with hb
  have hv := series_type hB hS hQ hω hH hκ (φ := fun PP y => ((Φ PP.1 ((b + dκ) PP) y : ℚ) : ℂ))
    (φ' := fun PP y => ((Φ PP.1 (b PP) y : ℚ) : ℂ)) (fun _ => 1) (fun PP y => by
      have e := (hΦ PP.1 PP.2).equiv (redFn B.F.βT PP.1 (Lev.finE T κ)) (b PP)
        ((redFn B.F.βT PP.1 (Lev.finE T κ)).val * y)
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at e
      simp only [Pi.add_apply, Units.val_one, one_mul, hdκ]
      rw [← e]) h P g
  rw [Finset.prod_const_one, inv_one, mul_one] at hv
  rw [Base.xiCoef_apply, Base.xiCoef_apply, hmul,
    show c - (Multiplicative.toAdd (detChar T (u.delQ Q) g) + dκ) = b by rw [hb]; abel,
    show c - Multiplicative.toAdd (detChar T (u.delQ Q) g) = b + dκ by rw [hb]; abel]
  exact hv

theorem not_isConjPl_of_splitSet {R : Finset (Pl D.host.E)} (hR : SplitSet R) {P P' : Pl D.host.E} (hP : P ∈ R) (hP' : P' ∈ R) :
    ¬ Lev.IsConjPl P P' := fun hc => by
  have h1 : IsIdemAt (cA D (idemAt P)) P' :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 P _ _ (hR.isIdemAt hP) hc
  have h2 := hR.mul_conj hP' hP
  rw [← idemAt_eq h1, (hR.isIdemAt hP').1.1] at h2
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P'.ne_bot
  refine ((hR.isIdemAt hP').2 x hx0).1 hx ?_
  rw [h2, zero_mul, map_zero]
  exact zero_mem _

end Series

section Algebra

variable {R K A V ι : Type} [CommRing R] [Field K] [Algebra R K] [CommRing A] [Algebra R A] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

theorem mem_baseChange_iInf_ker [Finite ι] (φ : ι → V →ₗ[K] V) {x : A ⊗[R] V}
    (h : ∀ i, LinearMap.lTensor A ((φ i).restrictScalars R) x = 0) :
    x ∈ ((⨅ i, LinearMap.ker (φ i)).restrictScalars R).baseChange A := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨l, hl⟩ := (LinearMap.range (LinearMap.pi φ)).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  obtain ⟨r, hr⟩ := (LinearMap.pi φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  let s : ι → V →ₗ[K] V := fun i => r ∘ₗ l ∘ₗ LinearMap.single K (fun _ : ι => V) i
  have key : ∀ v : V, v - ∑ i, s i (φ i v) ∈ ⨅ i, LinearMap.ker (φ i) := fun v => by
    have e1 : ∑ i, s i (φ i v) = r ((LinearMap.pi φ).rangeRestrict v) := by
      have : l (LinearMap.pi φ v) = (LinearMap.pi φ).rangeRestrict v := LinearMap.congr_fun hl ((LinearMap.pi φ).rangeRestrict v)
      rw [← this, ← Finset.univ_sum_single (LinearMap.pi φ v), map_sum, map_sum]
      rfl
    have e2 : LinearMap.pi φ (r ((LinearMap.pi φ).rangeRestrict v)) = LinearMap.pi φ v :=
      congrArg Subtype.val (LinearMap.congr_fun hr ((LinearMap.pi φ).rangeRestrict v))
    rw [← LinearMap.ker_pi, LinearMap.mem_ker, map_sub, e1, e2, sub_self]
  have all : ∀ y : A ⊗[R] V, y - ∑ i, LinearMap.lTensor A ((s i).restrictScalars R)
      (LinearMap.lTensor A ((φ i).restrictScalars R) y) ∈ ((⨅ i, LinearMap.ker (φ i)).restrictScalars R).baseChange A := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz =>
      have := add_mem hy hz
      simp only [map_add, Finset.sum_add_distrib]
      convert this using 1
      abel
    | tmul a v =>
      simp only [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply]
      rw [← TensorProduct.tmul_sum, ← TensorProduct.tmul_sub]
      exact Submodule.tmul_mem_baseChange_of_mem a (key v)
  simpa [h] using all x

variable {Δ : Type}

def coefAt (δ : Δ) : V ⊗[R] AddMonoidAlgebra R Δ →ₗ[R] V :=
  (TensorProduct.rid R V).toLinearMap ∘ₗ LinearMap.lTensor V
    { toFun := fun z : AddMonoidAlgebra R Δ => z.coeff δ
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }

open Classical in
theorem coefAt_tmul_single (δ δ' : Δ) (v : V) :
    coefAt δ (v ⊗ₜ[R] AddMonoidAlgebra.single δ' (1 : R)) = if δ' = δ then v else 0 := by
  change (AddMonoidAlgebra.single δ' (1 : R)).coeff δ • v = _
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem coefAt_sum (Xi : Δ →₀ V) (δ : Δ) :
    coefAt δ (Xi.sum fun δ' f => f ⊗ₜ[R] AddMonoidAlgebra.single δ' (1 : R)) = Xi δ := by
  classical
  rw [Finsupp.sum, map_sum, Finset.sum_congr rfl fun δ' _ => coefAt_tmul_single δ δ' (Xi δ'), Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

theorem exists_eq_sum (z : V ⊗[R] AddMonoidAlgebra R Δ) :
    ∃ Xi : Δ →₀ V, z = Xi.sum fun δ f => f ⊗ₜ[R] AddMonoidAlgebra.single δ (1 : R) := by
  classical
  have hadd : ∀ X Y : Δ →₀ V, ((X + Y).sum fun δ f => f ⊗ₜ[R] AddMonoidAlgebra.single δ (1 : R)) =
      (X.sum fun δ f => f ⊗ₜ[R] AddMonoidAlgebra.single δ (1 : R)) + Y.sum fun δ f => f ⊗ₜ[R] AddMonoidAlgebra.single δ (1 : R) :=
    fun X Y => Finsupp.sum_add_index' (fun _ => TensorProduct.zero_tmul _ _) fun _ _ _ => TensorProduct.add_tmul _ _ _
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Finsupp.sum_zero_index.symm⟩
  | add y z hy hz =>
    obtain ⟨X, rfl⟩ := hy
    obtain ⟨Y, rfl⟩ := hz
    exact ⟨X + Y, (hadd X Y).symm⟩
  | tmul v w =>
    induction w using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, by rw [TensorProduct.tmul_zero, Finsupp.sum_zero_index]⟩
    | add w w' hw hw' =>
      obtain ⟨X, hX⟩ := hw
      obtain ⟨Y, hY⟩ := hw'
      exact ⟨X + Y, by rw [TensorProduct.tmul_add, hX, hY, hadd]⟩
    | single δ c =>
      refine ⟨Finsupp.single δ (c • v), ?_⟩
      rw [Finsupp.sum_single_index (by exact TensorProduct.zero_tmul _ _), TensorProduct.smul_tmul, AddMonoidAlgebra.smul_single,
        smul_eq_mul, mul_one]

end Algebra

section Record

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK UnrG Fm0 ExpDat)

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X} {hρ : ρ.Good}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ Y i j b}

theorem injective_rd (Z : CellTie hρ Y rd) : Function.Injective rd := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  obtain ⟨d⟩ := Z.nonempty_dat
  have hQ : InRange X i ∅ := ⟨by simp, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩
  have key : ∀ x, rd x = rd (Y.th i _ b d) → coefAt 0 (Y.thU i _ b ∅ 0 d) = x := fun x hx => by
    haveI : IsEmpty ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i ∅ 0)) := ⟨fun P => Finset.notMem_empty _ (admissibleConjugatePairPlaces_subset i ∅ 0 (mem_half.1 P.2).1)⟩
    rw [Z.thU_eq ∅ 0 d hQ (fun _ => x) fun a => by rw [hx, Z.th_eq, ρ.xi_of_empty i j b Y (by simp)], grpSum,
      Finset.sum_eq_single 0 (fun a _ h => absurd (funext fun P => isEmptyElim P) h)
        (fun h => absurd (@Finset.mem_univ _ (_) _) h), map_zero, coefAt_tmul_single, if_pos rfl]
  have h1 := key (Y.th i _ b d + f) (by rw [map_add, hf, add_zero])
  rw [key _ rfl] at h1
  exact left_eq_add.1 h1

include hρ in

theorem exists_lift (g : G0g N) :
    ∃ κ, Lev.IsLevelLift (Wc D j) (ρ.B i j b).F.βT (ρ.B i j b).G.levT (ρ.eG i j b g) κ := by
  obtain ⟨R, h1, -, hR⟩ := (hρ.base i j b).places.split
  exact GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty _ _ (ρ.B i j b).G.levT _ _ (hρ.latT i j b) rfl
    (fun P hP P' hP' => not_isConjPl_of_splitSet hR (h1 hP) (h1 hP')) _

variable (ρ i j b) in

def HasType (F : GA D (Wc D j) → ℂ) : Prop :=
  ∀ a (hH : a ∈ (ρ.B i j b).G.P.H) κ, Lifts (ρ.B i j b) a κ → ∀ g, F (g * κ) = (((ρ.B i j b).G.P.chi ⟨a, hH⟩ : ℂˣ) : ℂ) * F g

include hρ in
theorem hasType_theta (h P) : HasType ρ i j b (ρ.theta i j b h P) := fun _ hH _ hκ g =>
  theta_type (hρ.base i j b) (D.sp.V_sig _) (hρ.weil_base i j b) hH hκ h P g

include hρ in
theorem hasType_gens {k Q ψ} (hψ : TwOK i k Q ψ) {h P F} (hF : F ∈ ρ.gens i j b k Q ψ h P) : HasType ρ i j b F := by
  obtain ⟨hQ, -, rfl⟩ := hF
  obtain ⟨h1, h2, -⟩ := GlobalTheory.TwistGood.tw_good D N X ρ hρ i j b k Q ψ hψ
  exact fun _ hH _ hκ g => gen_type (hρ.base i j b) (D.sp.V_sig _) h1 h2 (hρ.weil_base i j b) hH hκ _ P g

include hρ in
theorem hasType_xi {Q} (hQ : Disjoint Q (X.S0 i)) (M h P a) : HasType ρ i j b (ρ.xi i j b Y Q M h P a) := fun _ hH _ hκ g =>
  xiCoef_type (hρ.base i j b) (D.sp.V_sig _) (GlobalTheory.UnivGood.univOf_good D N X ρ hρ Y i Q M)
    (GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D N X ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h) (hQ.mono_left (admissibleConjugatePairPlaces_subset i Q M)))
    (Base.isAdmFam_univFam _ _ _) (hρ.weil_base i j b) hH hκ h P a g

theorem mem_levelTypeForms_of_hasLevelType (Z : CellTie hρ Y rd) (hA : ActRead rd) {f : Y.Fm i ((j : ℕ) + 1) b} (hf : HasType ρ i j b (rd f)) :
    f ∈ Fm0 Y i ((j : ℕ) + 1) b := by
  refine (Submodule.mem_iInf _).2 fun u => LinearMap.mem_ker.2 (sub_eq_zero.2 (injective_rd Z (funext fun g => ?_)))
  obtain ⟨κ, hκ⟩ := exists_lift (hρ := hρ) (i := i) (j := j) (b := b) u.1
  have hu := (Z.U_eq u.1).2 u.2
  change rd (Y.actG i _ b u f) g = rd (((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • f) g
  rw [hA _ κ hκ, hf _ hu κ (lifts_of_isLiftG0 hκ), Z.psiU_eq u hu, map_smulₛₗ]
  rfl

theorem mem_baseChange_of_hasType (Z : CellTie hρ Y rd) (hA : ActRead rd) {k : ℕ}
    {x : X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b} (hx : HasType ρ i j b (rdK rd hρ k x)) :
    x ∈ ((Fm0 Y i ((j : ℕ) + 1) b).restrictScalars (X.O i)).baseChange (X.Ok i k) := by
  haveI : Finite (G0g N) := Finite.of_equiv _ (ρ.eG i j b).symm.toEquiv
  refine mem_baseChange_iInf_ker _ fun u => Z.injective_rdK k (funext fun g => ?_)
  obtain ⟨κ, hκ⟩ := exists_lift (hρ := hρ) (i := i) (j := j) (b := b) u.1
  have hu := (Z.U_eq u.1).2 u.2
  have key : ∀ y : X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b, rdK rd hρ k (LinearMap.lTensor (X.Ok i k)
      (((Y.actG i _ b u).toLinearMap - ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) •
        LinearMap.id).restrictScalars (X.O i)) y) g =
      rdK rd hρ k y (g * κ) - ρ.e i b (Y.psiU i b u : (FractionRing (X.O i))ˣ) * rdK rd hρ k y g := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, Pi.add_apply, hy, hz]; ring
    | tmul a f =>
      rw [LinearMap.lTensor_tmul, rdK_tmul, rdK_tmul]
      change ρ.eOk i b k a * rd (Y.actG i _ b u f - ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • f) g =
        ρ.eOk i b k a * rd f (g * κ) - _ * (ρ.eOk i b k a * rd f g)
      rw [map_sub, map_smulₛₗ, Pi.sub_apply, hA _ κ hκ, Pi.smul_apply, smul_eq_mul]
      ring
  rw [key, hx _ hu κ (lifts_of_isLiftG0 hκ), Z.psiU_eq u hu, sub_self, map_zero]
  rfl

variable (Z : CellTie hρ Y rd) (hA : ActRead rd)
include Z hA

theorem thetaSeriesDatum_mem_levelTypeForms (d : Y.Dat i ((j : ℕ) + 1) b) : Y.th i _ b d ∈ Fm0 Y i ((j : ℕ) + 1) b :=
  mem_levelTypeForms_of_hasLevelType Z hA (by rw [Z.th_eq]; exact hasType_theta (hρ := hρ) _ _)

theorem thPsi_subset {k Q ψ} (hψ : TwOK i k Q ψ) (d : Y.Dat i ((j : ℕ) + 1) b) :
    Y.thPsi i _ b k Q ψ d ⊆ ((((Fm0 Y i ((j : ℕ) + 1) b).restrictScalars (X.O i)).baseChange (X.Ok i k) :
      Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b)) :=
  fun x hx => mem_baseChange_of_hasType Z hA (hasType_gens (hρ := hρ) hψ ((Z.thPsi_iff k Q ψ hψ d x).1 hx))

theorem mem_levelTypeForms_of_universalCoeff_reading {Q} (hQ : Disjoint Q (X.S0 i)) {M h P a} {x : Y.Fm i ((j : ℕ) + 1) b}
    (hx : rd x = ρ.xi i j b Y Q M h P a) : x ∈ Fm0 Y i ((j : ℕ) + 1) b :=
  mem_levelTypeForms_of_hasLevelType Z hA (by rw [hx]; exact hasType_xi (hρ := hρ) hQ M h P a)

theorem coefAt_thU_mem (Q M) (d : Y.Dat i ((j : ℕ) + 1) b) (δ) : coefAt δ (Y.thU i _ b Q M d) ∈ Fm0 Y i ((j : ℕ) + 1) b := by
  classical
  by_cases h : InRange X i Q ∧ ∀ a, ρ.xi i j b Y Q M (Z.cls d) (Z.coef d) a ∈ Set.range rd
  · obtain ⟨hQ, h⟩ := h
    choose x hx using h
    rw [Z.thU_eq Q M d hQ x hx, grpSum, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [coefAt_tmul_single]
    split_ifs
    · exact mem_levelTypeForms_of_universalCoeff_reading Z hA hQ.2.2 (hx a)
    · exact zero_mem _
  · rw [Z.thU_off Q M d h, map_zero]
    exact zero_mem _

omit Z hA

variable (Y) in

def UnivTyped : Prop := ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b Q M (d : Y.Dat i j b),
  (∃ Xi : DelQM D.host (X.l i) Q M →₀ Y.Fm i j b,
    Y.thU i j b Q M d = Xi.sum (fun δ f => f ⊗ₜ[X.O i] AddMonoidAlgebra.single δ (1 : X.O i))) ∧
  ∀ Xi : DelQM D.host (X.l i) Q M →₀ Y.Fm i j b,
    Y.thU i j b Q M d = Xi.sum (fun δ f => f ⊗ₜ[X.O i] AddMonoidAlgebra.single δ (1 : X.O i)) → ∀ δ, Xi δ ∈ Fm0 Y i j b

variable {rds : Rds Y ρ} (W : Comparison₂ hρ rds) (hW : ∀ i j b, ActRead (rds i j b))
include W hW

theorem typeKept_of_tie (E : ExpDat Y) : GlobalTheory.TwAll.TypeKept E := by
  intro i _ j hj b k Q ψ hψ _ a _
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact thPsi_subset (W i ⟨n, h2⟩ b) (hW i ⟨n, h2⟩ b) hψ a

theorem univTyped_of_tie : UnivTyped Y := by
  intro i j hj b Q M d
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  refine ⟨exists_eq_sum _, fun Xi e δ => ?_⟩
  rw [← coefAt_sum (R := X.O i) Xi δ, ← e]
  exact coefAt_thU_mem (W i ⟨n, h2⟩ b) (hW i ⟨n, h2⟩ b) Q M d δ

theorem th_typed_of_tie (i : X.Tw) {j : ℕ} (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) (d : Y.Dat i j b) :
    Y.th i j b d ∈ Fm0 Y i j b := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact thetaSeriesDatum_mem_levelTypeForms (W i ⟨n, h2⟩ b) (hW i ⟨n, h2⟩ b) d

def allData : ExpDat Y where
  Dat0 _ j _ := {_d | j ∈ Finset.Icc 1 D.R.m}
  theta_base_equivariant i _ b d hd u :=
    sub_eq_zero.1 (LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (th_typed_of_tie W hW i hd b d) u))

end Record

section Export

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (Fm0 ExpDat)

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T₀ : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T₀ D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {Sr : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG Sr}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem type_of_exportTie (Z : ExportTie YS v₀) (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) :
    (∀ E : ExpDat D.nexp, GlobalTheory.TwAll.TypeKept E) ∧ UnivTyped D.nexp ∧
    (∀ i (j : Fin D.R.m) b Q M h P a x, Disjoint Q (D.ntw.S0 i) → Z.rd i j b x = Z.ρ.xi i j b D.nexp Q M h P a →
      x ∈ Fm0 D.nexp i ((j : ℕ) + 1) b) ∧
    ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b (d : D.nexp.Dat i j b), D.nexp.th i j b d ∈ Fm0 D.nexp i j b := by
  have hA : ∀ i j b, ActRead (Z.rd i j b) := fun i j b =>
    actRead_realRd D Γ Pl0 I0 T₀ A3 Ks Rl cG Sr YS v₀ Z.ρ Z.good i j b _ Z.pin hU hW
  exact ⟨typeKept_of_tie Z.tie hA, univTyped_of_tie Z.tie hA,
    fun i j b _ _ _ _ _ _ hQ hx => mem_levelTypeForms_of_universalCoeff_reading (Z.tie i j b) (hA i j b) hQ hx,
    fun i _ hj b d => th_typed_of_tie Z.tie hA i hj b d⟩

end Export

section Target

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie

theorem typeKept_of_fullTie : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    (∀ i j b, ActRead (rd i j b)) → ∀ E : Formalism.MainNotions.IntegralHeckeForms.XD D, GlobalTheory.TwAll.TypeKept E :=
  fun _ _ _ _ Z hA E => typeKept_of_tie Z.tie hA E

end Target

end GlobalTheory.ExportType

end
