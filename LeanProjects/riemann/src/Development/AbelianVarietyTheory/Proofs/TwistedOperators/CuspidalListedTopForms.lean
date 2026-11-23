import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem isTypeAt_of_finSum (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) {S : SPar}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)} {lam : Fin V.rank → ℝ} {ε : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hE : IsEnum S lam ε) (hD : Formalism.MainNotions.S.IsDS ε lam σ) (hP : IsUnit P) (hJ : Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ)
    (φ : GA D V → ℂ)
    (h : ∀ x, ∃ (n : ℕ) (L : Fin n → (H →L[ℂ] ℂ)) (v : Fin n → H),
      (∀ i, SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) (v i)) ∧
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), φ (x * atTau θ V τ g) = ∑ i, L i (σ (P * g * P⁻¹) (v i))) :
    IsTypeAt θ V τ S φ := by
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  obtain ⟨n, L, v, hv, hφ⟩ := h x
  let vv : ℕ → H := fun i => if hi : i < n then v ⟨i, hi⟩ else 0
  let ll : ℕ → (H →ₗ[ℂ] ℂ) := fun i => if hi : i < n then ((L ⟨i, hi⟩ : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) else 0
  let CC : ℕ → ℝ := fun i => if hi : i < n then ‖L ⟨i, hi⟩‖ else 0
  have hb : ∀ i w, ‖ll i w‖ ≤ CC i * ‖w‖ := fun i w => by
    by_cases hi : i < n
    · simp only [ll, CC, dif_pos hi]
      exact (L ⟨i, hi⟩).le_opNorm w
    · simp [ll, CC, dif_neg hi]
  refine ⟨vv, fun i => ?_, ll, fun i => ⟨[[]], CC i, by simp, fun w _ => by simpa using hb i w⟩,
    ⟨[[]], CC, by simp, fun i w _ => by simpa using hb i w, fun S' _ => ?_, fun _ => 1, continuous_const,
      fun g hg w _ => ?_⟩, fun g hg => ?_⟩
  · by_cases hi : i < n
    · simp only [vv, dif_pos hi]
      exact hv _
    · simp only [vv, dif_neg hi]
      intro k Xs _
      simpa using contDiff_const
  · refine summable_of_ne_finset_zero (s := Finset.range n) fun i hi => ?_
    have : ¬ i < n := by simpa using hi
    simp [CC, dif_neg this]
  · simp [hD.2.2.1.2.1 _ (GlobalTheory.TypeAtCompare.conj_mem hP hJ hg) w]
  · rw [hφ g hg]
    convert hasSum_sum_of_ne_finset_zero (s := Finset.range n)
      (f := fun i => ll i (σ (P * g * P⁻¹) (vv i))) (fun i hi => by
        have : ¬ i < n := by simpa using hi
        simp [ll, dif_neg this]) using 1
    · rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [ll, vv, i.2]
    · infer_instance

def conjFun {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (c : H' ≃ₗᵢ⋆[ℂ] H) (ℓ : H →L[ℂ] ℂ) : H' →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun w => star (ℓ (c w))
      map_add' := fun a b => by simp
      map_smul' := fun a w => by
        simp only [LinearIsometryEquiv.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply]
        rw [star_mul', Complex.star_def, Complex.conj_conj] }
    ‖ℓ‖ (fun w => by simpa using ℓ.le_opNorm (c w))

theorem conjFun_apply {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (c : H' ≃ₗᵢ⋆[ℂ] H) (ℓ : H →L[ℂ] ℂ) (w : H') : conjFun c ℓ w = star (ℓ (c w)) := rfl

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem conj_finSum {V : HSp D} {S S' : D.what₂.Tau → SPar} {θ : InfFam D} (M : DSModel V S) (M' : DSModel V S')
    (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)] (c : M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c (M'.rep τ g w) = M.rep τ g (c w))
    (hsm : ∀ w : M'.H τ, w ∈ M'.sm τ ↔ c w ∈ M.sm τ)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (x : GA D V) (z : SmT M) :
    ∃ (n : ℕ) (L : Fin n → (M'.H τ →L[ℂ] ℂ)) (v : Fin n → M'.H τ),
      (∀ i, SmoothVec (lieAt V τ) (fun g => M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹)) (v i)) ∧
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), star (PiTensorProduct.lift T z (x * atTau θ V τ g)) =
        ∑ i, L i (M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹) (v i)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    obtain ⟨ℓ, -, hℓ⟩ := GlobalTheory.DefiniteEnd.exists_sobCont M τ T f x
    have hw : c.symm (f τ) ∈ M'.sm τ := (hsm _).2 (by simp)
    have hsv : SmoothVec (lieAt V τ) (fun g => M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹)) (c.symm (f τ)) := by
      rw [GlobalTheory.SmVec.sm_eq M' τ] at hw
      exact hw
    refine ⟨1, fun _ => star r • conjFun c (LinearMap.toContinuousLinearMap ℓ), fun _ => c.symm (f τ), fun _ => hsv,
      fun g hg => ?_⟩
    have e1 := congrFun (hT.equiv τ g hg f ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩ rfl) x
    have e3 : T f (x * atTau θ V τ g) = ℓ (M.rep τ g (f τ)) := by
      rw [hℓ ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩]
      exact e1.symm
    have e2 : M.rep τ g (f τ) = c (M'.rep τ g (c.symm (f τ))) := by
      rw [hc g hg, LinearIsometryEquiv.apply_symm_apply]
    rw [Fin.sum_univ_one, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, ContinuousLinearMap.smul_apply, conjFun_apply,
      smul_eq_mul, smul_eq_mul, star_mul', e3, LinearMap.coe_toContinuousLinearMap', e2]
    rfl
  | add a b ha hb =>
    obtain ⟨n₁, L₁, v₁, hv₁, h₁⟩ := ha
    obtain ⟨n₂, L₂, v₂, hv₂, h₂⟩ := hb
    refine ⟨n₁ + n₂, Fin.append L₁ L₂, Fin.append v₁ v₂, fun i => ?_, fun g hg => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hv₁ i
      · simpa using hv₂ i
    · rw [Fin.sum_univ_add, map_add, Pi.add_apply, star_add, h₁ g hg, h₂ g hg]
      simp

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem isAutFunSm_lift {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (z : SmT M) :
    IsAutFunSm θ V (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact GlobalTheory.Mem.AutSpace.isAutFunSm_smul r (hT.aut f)
  | add a b ha hb =>
    rw [map_add]
    exact GlobalTheory.Mem.AutSpace.isAutFunSm_add ha hb

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem formX_props (R : RealDat D A Ks) (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX) (hH : R.models_HX)
    (d : ChainVec R) (t : T) (y : (R.HX t).H) :
    IsAutFunSm R.θ D.sp.X' (d.formX t y) ∧ IsCuspFun D.sp.X' (d.formX t y) ∧
      ∀ τ, IsTypeAt R.θ D.sp.X' τ ((Ptw D).Dpar D.R.m τ) fun g => star (d.formX t y g) := by
  have hx := (hH t).2.1.le (LinearMap.mem_range_self (R.HX t).e y)
  have hT := GlobalTheory.DefiniteEnd.isMultMap_toMap hθ D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX hc hpr hx
  have e : d.formX t y =
      PiTensorProduct.lift (PiTensorProduct.lift.symm (R.cX.toMap R.prX ((R.HX t).e y))) d.v := by
    rw [LinearEquiv.apply_symm_apply]; rfl
  rw [e]
  refine ⟨isAutFunSm_lift hT _, GlobalTheory.DefiniteEnd.isCuspFun_of_definite D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) _,
    fun τ => ?_⟩
  haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX τ
  obtain ⟨M', c, hc'⟩ := @GlobalTheory.ConjDS.exists_conjModel D D.sp.X' (parB (Ptw D) D.R.m) R.MX
  have hsm := (GlobalTheory.ConjMult.conj_mult R.θ R.MX M' c hc').1 τ
  have hE := M'.enum τ
  simp only [parB, dualPar_dualPar] at hE
  exact isTypeAt_of_finSum R.θ D.sp.X' τ hE (M'.ds τ) (M'.fr_unit τ) (M'.fr_gram τ) _
    fun x => conj_finSum R.MX M' τ (c τ) (hc' τ) hsm hT x d.v

theorem props_cast (θ : InfFam D) (S : D.what₂.Tau → SPar) {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)}
    (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩) (φ : GA D D.sp.X' → ℂ) (h1 : IsAutFunSm θ D.sp.X' φ) (h2 : IsCuspFun D.sp.X' φ)
    (h3 : ∀ τ, IsTypeAt θ D.sp.X' τ (S τ) fun g => star (φ g)) :
    IsAutFunSm θ X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      IsCuspFun X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      ∀ τ, IsTypeAt θ X.sp τ (S τ) fun g => star (φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) := by
  subst h
  exact ⟨h1, h2, h3⟩

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

theorem formTop_isCuspListed : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), GlobalTheory.FlipRun.IsCuspListed ch.W.θ (.grid 0 D.R.m) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hm := hS.core.models
  obtain ⟨h1, h2, h3⟩ := formX_props R hm.inf hm.cX hm.prX hm.HX ch.cv t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  obtain ⟨k1, k2, k3⟩ := props_cast R.θ (fun τ => Node.par D ch.sc.cGap (.grid 0 D.R.m) τ) (columnBlock R.toLevCh D.R.m)
    (colY_m R.toLevCh) (ch.cv.formX t y) h1 h2 (fun τ => by
      rw [show Node.par D ch.sc.cGap (.grid 0 D.R.m) τ = (Ptw D).Dpar D.R.m τ from parV_zero D _ le_rfl τ]
      exact h3 τ)
  rw [hθ]
  exact ⟨k1, k2, k3⟩

end GlobalTheory.EndCusp
