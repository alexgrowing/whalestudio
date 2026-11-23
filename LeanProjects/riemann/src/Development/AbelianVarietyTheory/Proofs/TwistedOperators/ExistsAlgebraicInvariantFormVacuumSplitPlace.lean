import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitAlgForm

open GlobalTheory.SplitScalar GlobalTheory.LevelSeries.IdemSumForm GlobalTheory.AlgWave

theorem psi_ne_zero {G : Type} [AddGroup G] (ψ : AddChar G ℂ) (x : G) : ψ x ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem fin_smul {D : D7} {m n : ℕ} (a : AE D) {x : Mx D m n} (hx : x.map (infPart D) = 0) :
    (a • x).map (infPart D) = 0 := by
  ext i j
  have : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show infPart D (a * x i j) = 0
  rw [RingHom.map_mul, this, mul_zero]

theorem fin_add {D : D7} {m n : ℕ} {x y : Mx D m n} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  rw [Matrix.map_add _ (map_add (infPart D)), hx, hy, add_zero]

set_option maxHeartbeats 1000000 in

theorem exists_alg_form : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e → ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) →
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      ℓ v = 1 ∧ ∀ p, IsAlgebraic ℚ (ℓ (heisO ψ S T (w p) v)) := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT e he n w hw
  classical
  have hψ : IsStdChar D ψ (-1) := hv.1
  obtain ⟨hd, -, hsg⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  set Λ : AddSubgroup (WO S T) := latO S T (ΛS : Set (Fin S.rank → D.host.E))
    (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛdef
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ := fun a ha =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
  have hΛfin : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => latO_fin hu
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hvth : IsThetaFunO ψ S T v := hv.2.theta
  have hlat : IsLatVac (heisO ψ S T) Λ v := hv.2.lat
  have hsign : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u v = ε • v := fun u hu => by
    obtain ⟨ε, hε, h⟩ := hsg v hlat u hu
    exact ⟨ε, hε, h v hlat⟩
  have hεQ : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ε ∈ Qb ∧ ε ≠ 0 := by
    rintro ε (rfl | rfl)
    · exact ⟨one_mem _, one_ne_zero⟩
    · exact ⟨neg_mem (one_mem _), neg_ne_zero.2 one_ne_zero⟩
  have hpsi : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplO S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psi_mem hψ hS hT hx hy
  have hpsiH : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplOH S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psiH_mem hψ hS hT hx hy

  have hcS : IsSplitIdem D (cA D e) := isSplitIdem_conj he
  have he1 : e * e = e := he.1
  have hec : e * (cA D e) = 0 := he.2.1
  have hce : (cA D e) * e = 0 := by rw [mul_comm]; exact hec
  have hc1 : (cA D e) * (cA D e) = (cA D e) := by rw [← RingHom.map_mul, he1]
  have hcc : cA D (cA D e) = e := GlobalTheory.DualPairCheck.cA_cA e
  have hq1 : (1 - (e + (cA D e))) * (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by linear_combination he1 + hc1 + 2 * hec
  have hcq : cA D (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by
    rw [map_sub, map_one, map_add, hcc, add_comm (cA D e) e]
  have hcq0 : (cA D e) * (1 - (e + (cA D e))) = 0 := by linear_combination -hc1 - hce
  have hqc0 : cA D (1 - (e + (cA D e))) * (cA D e) = 0 := by rw [hcq, mul_comm]; exact hcq0
  have hdec : ∀ x : WO S T, (cA D e) • x + (e • x + (1 - (e + (cA D e))) • x) = x := fun x => by
    rw [← add_smul, ← add_smul, ← add_assoc, add_comm (cA D e) e, add_sub_cancel, one_smul]

  have caseB : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → (1 - (e + (cA D e))) • x ∈ Λ → ℓ (heisO ψ S T x v) ∈ Qb := by
    intro ℓ hinv h1 x hx hx'
    obtain ⟨ε, hε, hεv⟩ := hsign _ hx'
    have hxe : IsHalf e (e • x) := (isHalf_iff _ _).2 (by rw [smul_smul, he1])
    have hxc : IsHalf (cA D e) ((cA D e) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hc1])
    have hxq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    have horth : symplO S T (e • x) ((1 - (e + (cA D e))) • x) = 0 := symplO_eq_zero S T hcq0 hxe hxq
    have e1 : heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v = ε • heisO ψ S T (e • x) v := by
      rw [heisO_add_of_orth ψ S T horth, hεv, heisO_smul]
    have e2 : heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v) =
        ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) • heisO ψ S T x v := by
      rw [heisO_heisO, hdec x]
    have e3 : ℓ (heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v)) =
        ε * ℓ (heisO ψ S T (e • x) v) := by
      rw [hinv _ hxc _ (hth _ _ hvth), e1, map_smul, smul_eq_mul]
    rw [e2, map_smul, smul_eq_mul] at e3
    have hx0 := psi_ne_zero ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x))
    have hpq : ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) ∈ Qb :=
      hpsiH _ _ (fin_smul _ hx) (fin_add (fin_smul _ hx) (fin_smul _ hx))
    have e4 : ℓ (heisO ψ S T x v) = (ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)))⁻¹ *
        (ε * ℓ (heisO ψ S T (e • x) v)) := by
      rw [← e3, inv_mul_cancel_left₀ hx0]
    rw [e4]
    refine mul_mem (inv_mem hpq) (mul_mem (hεQ ε hε).1 ?_)
    by_cases hxΛ : e • x ∈ Λ
    · rw [hlat.2 e he _ hxΛ hxe, h1]; exact one_mem _
    · obtain ⟨l, hl, hlc, hne⟩ := dual_half he1 (fun u hu => half_fin he hu) hd (fun u hu => hΛ (cA D e) hc1 u hu) hxe hxΛ
      have h0 : ℓ (heisO ψ S T (e • x) v) = 0 := by
        have k1 := hinv l hlc _ (hth (e • x) v hvth)
        rw [heisO_comm, hlat.2 (cA D e) hcS l hl hlc, map_smul, smul_eq_mul] at k1
        have : (ψ (symplO S T l (e • x)) - 1) * ℓ (heisO ψ S T (e • x) v) = 0 := by
          rw [sub_mul, k1, one_mul, sub_self]
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
      rw [h0]; exact zero_mem _

  have step : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → ∃ ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ' (heisO ψ S T u f) = ℓ' f) ∧ ℓ' v = 1 ∧
        ℓ' (heisO ψ S T x v) ∈ Qb ∧ ∀ y : WO S T, y.map (infPart D) = 0 →
          ∃ a ∈ Qb, ℓ' (heisO ψ S T y v) = a * ℓ (heisO ψ S T y v) := by
    intro ℓ hinv h1 x hx
    by_cases hB : (1 - (e + (cA D e))) • x ∈ Λ
    · exact ⟨ℓ, hinv, h1, caseB ℓ hinv h1 x hx hB, fun y _ => ⟨1, one_mem _, (one_mul _).symm⟩⟩
    have hex : ¬ ∀ u ∈ Λ, ψ (symplO S T ((1 - (e + (cA D e))) • x) u) = 1 := fun h => hB ((hd _ (fin_smul _ hx)).2 h)
    push_neg at hex
    obtain ⟨u', hu', hne'⟩ := hex
    have huΛ : (1 - (e + (cA D e))) • u' ∈ Λ := hΛ _ hq1 u' hu'
    have huq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • u') := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    rw [symplO_smul, hcq] at hne'
    have hne := psi_skew_ne hne'
    obtain ⟨ε, hε, hεv⟩ := hsign _ huΛ
    obtain ⟨hεQ', hε0⟩ := hεQ ε hε
    have hzQ : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ∈ Qb := hpsi _ _ (hΛfin _ huΛ) hx
    have hk : ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ≠ 0 := by
      rw [← mul_one_sub]
      exact mul_ne_zero hε0 (sub_ne_zero.2 (Ne.symm hne))
    have hcomm : ∀ w₁ : WO S T, heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T w₁ v) =
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') w₁) * ε) • heisO ψ S T w₁ v := fun w₁ => by
      rw [heisO_comm, hεv, heisO_smul, smul_smul]
    refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ •
      (ℓ ∘ₗ (heisL ψ S T ((1 - (e + (cA D e))) • u') - (ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)) • LinearMap.id)),
      fun y hy f hf => ?_, ?_, ?_, fun y hy => ?_⟩
    all_goals simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sub_apply, heisL_apply,
      LinearMap.id_apply, map_sub, map_smul, smul_eq_mul]
    · have hc' : heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T y f) =
          heisO ψ S T y (heisO ψ S T ((1 - (e + (cA D e))) • u') f) := by
        rw [heisO_comm, symplO_eq_zero S T hqc0 huq hy, AddChar.map_zero_eq_one, one_smul]
      rw [hc', hinv y hy _ (hth _ _ hf), hinv y hy f hf]
    · rw [hεv, map_smul, smul_eq_mul, h1, mul_one, mul_one, inv_mul_cancel₀ hk]
    · rw [hcomm, map_smul, smul_eq_mul]
      have : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ε * ℓ (heisO ψ S T x v) -
          ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ℓ (heisO ψ S T x v) = 0 := by ring
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ *
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') y) * ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)),
        mul_mem (inv_mem (sub_mem hεQ' (mul_mem hεQ' hzQ)))
          (sub_mem (mul_mem (hpsi _ _ (hΛfin _ huΛ) hy) hεQ') (mul_mem hεQ' hzQ)), ?_⟩
      rw [hcomm, map_smul, smul_eq_mul]
      ring

  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hv.2.norm.1
    have := hv.2.norm.2 p hp
    simp [nrm2] at this
  obtain ⟨ℓ₀, hℓ₀, hinv₀⟩ := invariant_form (e := (cA D e)) (Λ := Λ) hc1 (by rw [hcc]; exact hec)
    (fun u hu => half_fin hcS hu) hd (fun u hu => by rw [hcc]; exact hΛ e he1 u hu) hv0
    (fun l hl hh => hlat.2 (cA D e) hcS l hl hh) (fun l hl hh => hlat.2 e he l hl (by rwa [hcc] at hh))
  have main : ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ℓ v = 1 ∧
      ∀ p, ℓ (heisO ψ S T (w p) v) ∈ Qb := by
    intro n
    induction n with
    | zero =>
      intro w _
      refine ⟨(ℓ₀ v)⁻¹ • ℓ₀, fun u hu f hf => ?_, ?_, fun p => p.elim0⟩
      · rw [LinearMap.smul_apply, LinearMap.smul_apply, hinv₀ u hu f hf]
      · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hℓ₀]
    | succ n ih =>
      intro w hw
      obtain ⟨ℓ, hinv, h1, halg⟩ := ih (fun p => w p.castSucc) fun p => hw _
      obtain ⟨ℓ', hinv', h1', hlast, hfac⟩ := step ℓ hinv h1 (w (Fin.last n)) (hw _)
      refine ⟨ℓ', hinv', h1', fun p => ?_⟩
      induction p using Fin.lastCases with
      | last => exact hlast
      | cast q =>
        obtain ⟨a, ha, h⟩ := hfac _ (hw q.castSucc)
        rw [h]
        exact mul_mem ha (halg q)
  obtain ⟨ℓ, hinv, h1, halg⟩ := main n w hw
  exact ⟨ℓ, fun u hu f hf => hinv u hu f hf, h1, fun p => mem_algebraicClosure_iff.1 (halg p)⟩

end GlobalTheory.SplitAlgForm

end
