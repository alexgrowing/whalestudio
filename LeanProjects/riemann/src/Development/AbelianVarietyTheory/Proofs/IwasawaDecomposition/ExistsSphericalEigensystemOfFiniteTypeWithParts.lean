import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalEigenvaluesIndependentOfStandardFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypePartLeEigensystemPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartLeEigensystemPartPrincipalLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

open GlobalTheory.Hk3 (Core Good IsSF SchurAll EEc Wcc IsLab SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.Mem.R3.LabEig

def IsSphScalars {D : D7} {V : HSp D} {n : ℕ} (Q : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (c : Pl D.host.E → List ℤ → ℂ) : Prop :=
  ∀ P d, IsLab V P d → ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x) →
    principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V P d) x = c P d • x

theorem exists_isSphScalars {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E)
    (Q : principalLevelFrame.RowPsi V n) (hQ : StdPsi hF Q) (π : Formalism.L2.NG.FinTyp D.host.E n) : ∃ c, IsSphScalars Q π c := by
  have h : ∀ P d, ∃ a : ℂ, IsLab V P d → ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x) →
      principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V P d) x = a • x := by
    intro P d
    by_cases hd : IsLab V P d
    · obtain ⟨a, ha⟩ := GlobalTheory.SphScalar.spherical_scalar hF Q hQ π P d _ (GlobalTheory.Hk3.OpsRows.sphOp_rep hd)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose c hc using h
  exact ⟨c, hc⟩

theorem isotE_sub : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, IsSphScalars (PW i0) π c → ∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 π, ∃ x ∈ EEc R SF c, R.HE.e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS SF hSF n hF PY PW hPY hPW π i0 c hEig b U hU
  obtain ⟨h, hOps, hNorm, -, -, hIn⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
  obtain ⟨-, hg, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  obtain ⟨nY, hβY⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hi := hC.models.HE.1
  have hUi := Submodule.mem_inf.1 hU
  have hUE : U ∈ R.EEat (R.levR F b) := hUi.1
  have hUT : U ∈ R.EEat R.triv := GlobalTheory.GoodRowsLevel.eeat_le_triv R _ hUE
  obtain ⟨x, rfl⟩ : U ∈ LinearMap.range R.HE.e := by rw [hC.models.HE.2.1]; exact hUT
  have key : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = star (c P d) • x := by
    intro P hP d hd
    have levY := GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβY P
      (by rw [Nat.cast_pow]; exact fun hm => (hg _ P hP).1 (P.isPrime.mem_of_pow_mem nY hm))
      (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
    have hB := GlobalTheory.Hk3.OpsRows.sphOp_rep hd
    have hdW : IsLab (Wc D i0) P d := ((GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i0 P d hP).2).2 hd
    have hB' := GlobalTheory.Hk3.OpsRows.sphOp_rep hdW
    have ha := hEig P d hdW
    obtain ⟨htr1, htr2⟩ := GlobalTheory.FrameTransport.sph_eigen_frame_indep hF PY (PW i0) hPY (hPW i0) P d
    have hvec : ∀ y ∈ (principalLevelFrame.FinTyp.conjT π).S, (∀ κ, PY.ψ κ ∈ hyp (Yc D 0) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
        principalLevelFrame.Hecke₃ PY (GlobalTheory.Hk3.rep (Yc D 0) P d) y = star (c P d) • y := by
      intro y hy hfy
      have hy' : (fun g => star (y g)) ∈ π.S := hy
      have hfy' : ∀ κ, PY.ψ κ ∈ hyp (Yc D 0) P →
          Formalism.L2.NG.rt D.host.E n κ (fun g => star (y g)) = fun g => star (y g) := by
        intro κ hκ
        rw [← principalLevelFrame.conj_rt, hfy κ hκ]
      have e := htr2 _ _ hB hB' _ hfy'
      rw [ha _ hy' (fun κ hκ => hfy' κ ((htr1 κ).2 hκ)), GlobalTheory.TypePart.heckeOperator_conj] at e
      funext g
      have e2 := congrArg star (congrFun e g)
      simp only [Pi.smul_apply, smul_eq_mul, star_star, star_mul'] at e2
      rw [Pi.smul_apply, smul_eq_mul, e2, mul_comm]
    have hfixU : ∀ k ∈ hyp (Yc D 0) P, postOn (R.MY 0) (principalLevelFrame.rtA k) (R.HE.e x) = R.HE.e x := by
      intro k hk
      ext1 v
      rw [postOn_apply]
      funext g
      have := GlobalTheory.Hk3.OpsRows.mult_lev (goodPart_le _ _ _ _ _ hUT) v k (levY.1 k hk).1 g
      rw [(levY.1 k hk).2, one_mul] at this
      exact this
    have hU2 := GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF PY hPY R.θ (R.MY 0) (principalLevelFrame.FinTyp.conjT π) P d _ _ hB hvec _ hUi.2 hfixU
    apply hi
    rw [hOps P hP, map_smul, GlobalTheory.Hk3.OpsRows.hk_single]
    exact hU2
  refine ⟨x, hIn c x fun P d hP hd => ?_, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    simp
  have hdd : IsLab (Yc D 0) P (dualLab d) := by
    have l1 := GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i0 P d hP
    exact l1.1.1 (l1.2.2 hd)
  have h1 := key P hP d hd
  have e := GlobalTheory.TypePart.star_eq_of_adj hNorm hP d hx0 h1 (key P hP _ hdd)
  have e' : star (c P d) = c P (dualLab d) := by
    rw [star_star] at e
    rw [e, star_star]
  rw [h1, e']

theorem isotL_sub : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, IsSphScalars (PW i0) π c → ∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (R.eWf i (sg0 D A)) π, ∃ x ∈ Wcc R SF i c, (R.HW i _).e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF n hF PW hPW π i0 c hEig i U hU
  have hLev := hC.lev
  have hN : ∀ (cc : ℕ) (P : Pl D.host.E), (((1 ^ cc : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro cc P h
    rw [one_pow, Nat.cast_one] at h
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have LO := fun (j : Fin D.R.m) (Lv : LevelP R.Pg D.R.r ℂ) (P : Pl D.host.E) (hG : Good R A.μ0 P) =>
    GlobalTheory.LevOp.level_operators (Wc D j) (R.βW j) (R.ΛW j) _ (R.datWp j Lv) (hLev.βW j).choose_spec P
      (hN _ P) (fun PP h => hG PP (h.imp id (fun h' => absurd h' (Finset.notMem_empty _))))
  have hGood := fun P => (GlobalTheory.GoodPrimes.good_primes R F hLev).2.2.1 SF hSF P
  have hU' := hU
  simp only [principalLevelFrame.isotL, Mult.goodPart, Submodule.mem_inf, LinearMap.mem_ker] at hU'
  obtain ⟨⟨hUM, hUe⟩, hUiso⟩ := hU'
  have hle : ∀ k ∈ levS (Wc D i) (R.βW i) (R.datWp i R.triv),
      k ∈ levS (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) ∧
        levChi (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) k =
          levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k := by
    intro k hk
    obtain ⟨h1, h2⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) (R.levL F false (sg0 D A)) k hk
    obtain ⟨_, h3⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) R.triv k hk
    exact ⟨h1, h2.trans h3.symm⟩
  have hU0 : U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) :=
    GlobalTheory.HeckeParts.mult_mono hle hUM
  have hrange := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, hx⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hrange]; exact hU0
  refine ⟨x, ?_, hx⟩
  rw [GlobalTheory.Hk3.Wcc, Submodule.mem_comap, hx]
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hU0, LinearMap.mem_ker.2 hUe⟩, Submodule.mem_inf.2 ⟨hU0, ?_⟩⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  obtain ⟨_, _, _, _, hoff, -⟩ := id hB
  have hG : Good R A.μ0 P := (hGood P).1 hoff
  have hSph : SphOp (Wc D i) P d B := (((LO i R.triv P hG).2.1 SF d B).1 hB).2
  have hd0 : IsLab (Wc D i0) P d :=
    (GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i0 P d hG).2.2
      ((GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i P d hG).2.1 ⟨B, hSph⟩)
  have hB0 := GlobalTheory.Hk3.OpsRows.sphOp_rep hd0
  have ha := hEig P d hd0
  obtain ⟨hiff, htr⟩ := GlobalTheory.FrameTransport.sph_eigen_frame_indep hF (PW i) (PW i0) (hPW i) (hPW i0) P d
  have hvec : ∀ y ∈ π.S, (∀ κ, (PW i).ψ κ ∈ hyp (Wc D i) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
      principalLevelFrame.Hecke₃ (PW i) B y = c P d • y := by
    intro y hy hfy
    rw [htr B _ hSph hB0 y hfy, ha y hy (fun κ hκ => hfy κ ((hiff κ).2 hκ))]
  have hUfix : ∀ k ∈ hyp (Wc D i) P, postOn (R.MW i (sg0 D A)) (principalLevelFrame.rtA k) U = U := by
    intro k hk
    obtain ⟨h1, h2⟩ := (LO i (R.levL F false (sg0 D A)) P hG).1 k hk
    have hl := principalLevelFrame.mult_lev hUM
    apply MultilinearMap.ext
    intro v
    funext g
    rw [Mult.postOn_apply]
    show U v (g * k) = U v g
    rw [hl v k h1 g, h2, one_mul]
  exact GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF (PW i) (hPW i) R.θ (R.MW i (sg0 D A)) π P d B (c P d) hSph hvec U hUiso hUfix

theorem eig_parts : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ c, (∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.EEc c, R.HE.e x = U) ∧ (∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.Wc' i c, (R.HW i (sg0 D A3.A)).e x = U) := by
  intro hW hDS hHC hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hPins hHolds hHost σ
  obtain ⟨hC3, hSF, -, -, hEE, hWc, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hPins.char
  have hCore := hC3 hHolds.aux.ex
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R.toRealDat
  have hPY : StdPsi Y.hF Y.PY := Y.stdPsi.1
  have hPW : ∀ i, StdPsi Y.hF (Y.PW i) := Y.stdPsi.2
  obtain ⟨c, hc⟩ := exists_isSphScalars Y.hF (Y.PW ⟨0, Y.hm⟩) (hPW _) (principalLevelFrame.rowRepR R.θ (Y.eFT σ))
  refine ⟨c, fun b U hU => ?_, fun i U hU => ?_⟩
  · obtain ⟨x, hx, hxU⟩ := isotE_sub R.toRealDat F.lv2 hCore hS R.SF hSF Y.hF Y.PY Y.PW hPY hPW _ ⟨0, Y.hm⟩ c hc b U hU
    exact ⟨x, by rw [hEE]; exact hx, hxU⟩
  · obtain ⟨x, hx, hxU⟩ := isotL_sub R.toRealDat F.lv2 hCore R.SF hSF Y.hF Y.PW hPW _ ⟨0, Y.hm⟩ c hc i U hU
    exact ⟨x, by rw [hWc]; exact hx, hxU⟩

end GlobalTheory.Mem.R3.LabEig

end
