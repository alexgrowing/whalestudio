import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.InfinityTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtEqInfMat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFamilyLowLieActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightVectorTransferStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockActionsIsHolomorphicProductKRepFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMinorProductTranslateJointLowestWeightStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameFunctionActionHolomorphicExtremalLowestStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceLeSpanUnitaryOrbitExtremalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProofStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeightsStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JointHarm

theorem isThetaFunO_of_isThetaAt {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (h₀ : IsThetaFunO ψ S T f₀) :
    IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    LinearMap.pi fun w => l ∘ₗ GlobalTheory.SplitScalar.heisL ψ S T w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

theorem compAt_mt_one' {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) :
    compAt θ τ (Formalism.L2.Theta.mt V 1) = 1 :=
  (GlobalTheory.WeilDeriv.compAt_mt_eq_infMat θ τ V 1).trans (GlobalTheory.PointAtPlaceHom.infMat_one V _)

section Mat

variable {m : ℕ} {ε : Fin m → Bool}

theorem mem_KC_of_K {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) : k ∈ GlobalTheory.Dec.KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

theorem one_mem_K : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem invT_mem_KC {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ GlobalTheory.Dec.KC ε) : (g⁻¹)ᵀ ∈ GlobalTheory.Dec.KC ε := by
  obtain ⟨_inst⟩ := hg.1.nonempty_invertible
  refine ⟨(Matrix.isUnit_transpose _).2 (Matrix.isUnit_nonsing_inv_iff.2 hg.1), ?_⟩
  have hc : g⁻¹ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g⁻¹ := by
    calc g⁻¹ * Formalism.REAL.Jm ε = g⁻¹ * (Formalism.REAL.Jm ε * g) * g⁻¹ := by
          rw [mul_assoc, mul_assoc, Matrix.mul_inv_of_invertible, mul_one]
      _ = Formalism.REAL.Jm ε * g⁻¹ := by
          rw [← hg.2, ← mul_assoc, Matrix.inv_mul_of_invertible, one_mul]
  have hJ : (Formalism.REAL.Jm ε)ᵀ = Formalism.REAL.Jm ε := Matrix.diagonal_transpose _
  have := congrArg Matrix.transpose hc
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ] at this
  exact this.symm

theorem invT_conj {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    ((k.map star)⁻¹)ᵀ = k := by
  have h : kᵀ * k.map star = 1 := by
    have := congrArg Matrix.transpose (Unitary.star_mul_self_of_mem hk)
    rw [Matrix.transpose_mul, Matrix.transpose_one] at this
    exact this
  rw [Matrix.inv_eq_left_inv h, Matrix.transpose_transpose]

theorem mem_K_allPos {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    u ∈ Formalism.REAL.Kset (allPos m) :=
  ⟨hu, by simp [Formalism.REAL.Jm, allPos]⟩

theorem K_mul {k k' : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (hk' : k' ∈ Formalism.REAL.Kset ε) :
    k * k' ∈ Formalism.REAL.Kset ε :=
  ⟨Submonoid.mul_mem _ hk.1 hk'.1, by rw [Matrix.mul_assoc, hk'.2, ← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]⟩

end Mat

theorem mulSingle_mem_KC {ι : Type} {m : ℕ} {ε : ι → Fin m → Bool} {τ : ι} {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : g ∈ GlobalTheory.Dec.KC (ε τ)) (ρ : ι) :
    (Pi.mulSingle τ g : ι → Matrix (Fin m) (Fin m) ℂ) ρ ∈ GlobalTheory.Dec.KC (ε ρ) := by
  by_cases h : ρ = τ
  · subst h; rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h]; exact mem_KC_of_K one_mem_K

theorem commute_factU_factK {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    {u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (hu : ∀ τ, IsUnit (u τ))
    {g : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ} (hg : ∀ τ, g τ ∈ GlobalTheory.Dec.KC (ε τ)) :
    Commute (factU ε x₁ x₂ x₃ u) (factK n ε x₁ x₂ x₃ g) := by
  have hm := (GlobalTheory.T.fockPolynomialAction_one_mul_adjoint D m n ε x₁ x₂ x₃).2.1
  have h1 : ∀ τ, (1 : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) τ ∈ GlobalTheory.Dec.KC (ε τ) := fun _ => mem_KC_of_K one_mem_K
  have h2 : ∀ τ, IsUnit ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ) := fun _ => isUnit_one
  have a := hm 1 (fun τ => ((g τ)⁻¹)ᵀ) u 1 h1 (fun τ => invT_mem_KC (hg τ)) hu h2
  have b := hm (fun τ => ((g τ)⁻¹)ᵀ) 1 1 u (fun τ => invT_mem_KC (hg τ)) h1 h2 hu
  rw [one_mul, mul_one] at a
  rw [one_mul, mul_one] at b
  exact a.symm.trans b

theorem IsBotFam.map_of_commute {ι : Type} {n : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P] {ε : ι → Fin n → Bool}
    {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P} {μ : ι → Fin n → ℝ} {x : P} (h : IsBotFam ε ϖ μ x)
    {A : Module.End ℂ P} (hA : ∀ g, (∀ τ, g τ ∈ GlobalTheory.Dec.KC (ε τ)) → Commute A (ϖ g)) : IsBotFam ε ϖ μ (A x) := by
  intro τ
  refine ⟨fun g hg hl => ?_, fun θ => ?_⟩
  · have := LinearMap.congr_fun (hA _ (mulSingle_mem_KC hg)).eq x
    simp only [Module.End.mul_apply] at this
    show ϖ _ (A x) = A x
    rw [← this]
    exact congrArg A ((h τ).1 g hg hl)
  · have hg : (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ GlobalTheory.Dec.KC (ε τ) := by
      refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
      rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
      exact fun a => (Complex.exp_ne_zero _).isUnit
    have := LinearMap.congr_fun (hA _ (mulSingle_mem_KC hg)).eq x
    simp only [Module.End.mul_apply] at this
    show ϖ _ (A x) = _
    rw [← this, ← map_smul]
    exact congrArg A ((h τ).2 θ)

def botSub {ι : Type} {n : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P] (ε : ι → Fin n → Bool)
    (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (μ : ι → Fin n → ℝ) : Submodule ℂ P where
  carrier := {x | IsBotFam ε ϖ μ x}
  zero_mem' := fun τ => ⟨fun g _ _ => map_zero _, fun θ => by simp⟩
  add_mem' := fun {a b} ha hb τ => ⟨fun g hg hl => by rw [map_add, (ha τ).1 g hg hl, (hb τ).1 g hg hl],
    fun θ => by rw [map_add, (ha τ).2 θ, (hb τ).2 θ, smul_add]⟩
  smul_mem' := fun c a ha τ => ⟨fun g hg hl => by rw [map_smul, (ha τ).1 g hg hl],
    fun θ => by rw [map_smul, (ha τ).2 θ, smul_comm]⟩

theorem exists_io_poly (D : D7) (V W : HSp D) (θ : InfFam D) (Sp : D.what₂.Tau → SPar) (M : DSModel W Sp)
    (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W)
    (hθ : IsInfFam θ) (hc : c.Is) (h0 : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam))
    (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hBS : ∀ τ, IsUnit (BS τ))
    (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hr : W.rank ≤ V.rank)
    (hpq : ∀ τ, p τ + q τ = W.rank) (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ))
    (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a)
    (hK : ∀ τ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ))
    (hU : ∀ τ j, wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j = -(lam τ).w j) :
    ∃ io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      (∀ u ∈ GinfC V, (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) →
        ∀ x w, fact M.ε x₁ x₂ x₃ 1 (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (io x w) =
          io x (c.ρ u w)) ∧
      (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
        ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → ∀ w,
          fact M.ε x₁ x₂ x₃ (Pi.mulSingle τ k) 1 (io (PiTensorProduct.tprod ℂ v) w) =
            io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w) ∧
      ∃ (v : ∀ ρ, lowT M ρ) (w : c.W), (∀ ρ, ‖((v ρ : M.sm ρ) : M.H ρ)‖ = 1) ∧ ‖w‖ = 1 ∧
        io (PiTensorProduct.tprod ℂ v) w = delta p q ap am := by
  obtain ⟨hhK, hhU⟩ := GlobalTheory.T.fockActions_isHolomorphicProductKRepFamily D W.rank V.rank M.ε x₁ x₂ x₃
  obtain ⟨κ, Δ', hκ, hΔ, hbK, hbU⟩ := GlobalTheory.T.exists_minorProduct_translate_jointLowestWeight D W.rank V.rank M.ε p q ap am x₁ x₂ x₃ hr hpq hε hap ham
  obtain ⟨m, hm1, hm2, hm3⟩ := GlobalTheory.T.holomorphic_family_low_lie_action D W Sp M _ _ _ hhK
  obtain ⟨hv1, hv2, hv3, hv4⟩ := GlobalTheory.T.frameFunctionAction_holomorphic_extremal_lowest D.what₂.Tau V.rank lam
  have eK : (fun τ a => -(wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ)) =
      fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) := by
    funext τ a; rw [Pi.neg_apply, hK]
  have eU : (fun τ (j : Fin V.rank) => (wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j : ℝ)) =
      fun τ j => -((lam τ).w j : ℝ) := by
    funext τ j; rw [hU]; push_cast; rfl
  rw [eK] at hbK
  rw [eU] at hbU
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.lowest_weight_vector_transfer _ _ _ _ _ _ _ _ _ _ _ _ hhU hv1 hbU hv2 hv3
  obtain ⟨j, hj1, hj2⟩ := GlobalTheory.T.exists_polynomialModel_coefficientSpace_realPoints D V θ c lam c0 hθ hc h0 BS hBS
  have key : ∀ F ∈ VV ℂ lam,
      ψ F ∈ botSub M.ε (factK V.rank M.ε x₁ x₂ x₃) (fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) ∧
      ∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (allPos V.rank)) →
        ψ (vact lam u F) = factU M.ε x₁ x₂ x₃ u (ψ F) := by
    intro F hF
    have hF' := GlobalTheory.T.coefficientSpace_le_span_unitary_orbit_extremal D.what₂.Tau V.rank lam hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem F h =>
      obtain ⟨u, hu, rfl⟩ := h
      refine ⟨?_, fun u' hu' => ?_⟩
      · rw [hψ u hu]
        exact hbK.map_of_commute fun g hg => commute_factU_factK _ _ _ _ (fun τ => (mem_KC_of_K (hu τ)).1) hg
      · rw [← Module.End.mul_apply, ← hv1.2.2.1 u' u (fun τ => mem_KC_of_K (hu' τ)) (fun τ => mem_KC_of_K (hu τ)),
          hψ (u' * u) (fun τ => K_mul (hu' τ) (hu τ)), hψ u hu,
          hhU.2.2.1 u' u (fun τ => mem_KC_of_K (hu' τ)) (fun τ => mem_KC_of_K (hu τ)), Module.End.mul_apply]
    | zero => exact ⟨by rw [map_zero]; exact zero_mem _, fun u _ => by simp only [map_zero]⟩
    | add a b _ _ ha hb =>
      exact ⟨by rw [map_add]; exact add_mem ha.1 hb.1, fun u hu => by simp only [map_add, ha.2 u hu, hb.2 u hu]⟩
    | smul s a _ ha =>
      exact ⟨by rw [map_smul]; exact Submodule.smul_mem _ _ ha.1, fun u hu => by simp only [map_smul, ha.2 u hu]⟩
  have hjm : ∀ w, j w ∈ VV ℂ lam := fun w => hj1 ▸ LinearMap.mem_range_self j w
  obtain ⟨v0, hv0, hmv⟩ := hm2 κ hκ
  obtain ⟨w0, hw0⟩ : (ten fun τ => extremal ℂ V.rank (lam τ)) ∈ LinearMap.range j := hj1 ▸ hv4
  have hw0' : w0 ≠ 0 := by
    rintro rfl
    exact hv3 (by rw [← hw0, map_zero])
  have hψ0 : ψ (j w0) = Δ' := by
    have := hψ 1 fun _ => one_mem_K
    rwa [hv1.2.1, hhU.2.1, Module.End.one_apply, Module.End.one_apply, ← hw0] at this
  let N : D.what₂.Tau → ℂ := fun ρ => (‖((v0 ρ : M.sm ρ) : M.H ρ)‖ : ℂ)
  have hN : ∀ ρ, ‖((v0 ρ : M.sm ρ) : M.H ρ)‖ ≠ 0 := fun ρ h =>
    hv0 ρ (Subtype.ext (Subtype.ext (norm_eq_zero.1 h)))
  have hN' : ∀ ρ, N ρ ≠ 0 := fun ρ => Complex.ofReal_ne_zero.2 (hN ρ)
  have hw1 : ‖w0‖ ≠ 0 := norm_ne_zero_iff.2 hw0'
  have hw2 : (‖w0‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw1
  obtain ⟨io, hio⟩ : ∃ io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      ∀ x w, io x w = ((∏ ρ, N ρ) * (‖w0‖ : ℂ)) • m x (ψ (j w)) :=
    ⟨((∏ ρ, N ρ) * (‖w0‖ : ℂ)) • LinearMap.compl₂ m (ψ ∘ₗ j), fun _ _ => rfl⟩
  refine ⟨io, fun u hu hun x w => ?_, fun τ k hk v u hu w => ?_,
    fun ρ => (N ρ)⁻¹ • v0 ρ, (‖w0‖ : ℂ)⁻¹ • w0, fun ρ => ?_, ?_, ?_⟩
  · rw [hio, hio, map_smul]
    refine congrArg (HSMul.hSMul _) ?_
    have hcm := hm1 (factU M.ε x₁ x₂ x₃ fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ)
      (fun k hk => commute_factU_factK _ _ _ _ (fun τ => (mem_KC_of_K (mem_K_allPos (hun τ))).1)
        fun τ => mem_KC_of_K (hk τ)) x
    rw [hj2 u hu, (key _ (hjm w)).2 _ fun τ => mem_K_allPos (hun τ)]
    exact LinearMap.congr_fun hcm.eq _
  · rw [hio, hio, map_smul]
    refine congrArg (HSMul.hSMul _) ?_
    rw [hm3 _ (key _ (hjm w)).1 τ k hk v u hu]
    have : (fun ρ => (((Pi.mulSingle τ (k.map star) : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) ρ)⁻¹)ᵀ) =
        Pi.mulSingle τ k := by
      funext ρ
      by_cases h : ρ = τ
      · subst h; rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, invT_conj hk.1]
      · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, inv_one, Matrix.transpose_one]
    rw [factK, this]
  · show ‖(N ρ)⁻¹ • ((v0 ρ : M.sm ρ) : M.H ρ)‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (hN ρ)]
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hw1]
  · rw [MultilinearMap.map_smul_univ]
    rw [map_smul, map_smul, LinearMap.smul_apply, hio, smul_smul, smul_smul, hψ0, hmv _ hbK, factK]
    have : (fun τ => (((κ τ).map star)⁻¹)ᵀ) = κ := funext fun τ => invT_conj (hκ τ).1
    rw [this, hΔ, Finset.prod_inv_distrib]
    have hP : (∏ ρ, N ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hN' ρ
    convert one_smul ℂ _ using 2
    field_simp

end GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

theorem onb_eq_one {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : Bᴴ * G * B = 1 := by
  obtain ⟨e, he, h1, -⟩ := h
  rw [h1, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases he a with h | h
  · simp [h.1]
  · exact absurd a.2 (not_lt.2 h.2)

theorem conj_mem_UH {D : D7} {W : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel W Sp) (τ : D.what₂.Tau)
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) :
    (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
  obtain ⟨_inst⟩ := (M.fr_unit τ).nonempty_invertible
  have h1 : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := by
    have : kᴴ * k = 1 := Unitary.star_mul_self_of_mem hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, this, Matrix.one_mul]
  have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_inv_of_invertible, Matrix.conjTranspose_one]
  show ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D W τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D W τ
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) * M.fr τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h2, Matrix.mul_inv_of_invertible, Matrix.mul_one, Matrix.mul_one, h1]

theorem exists_ioP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta ∧ ∃ io, ({ R with ioP := io } : RealDat D A Ks).thP_ioP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hF hM hω hv
  have hθ : IsInfFam R.θ := hM.inf
  have hth : ∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := fun i t => by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hv i t
    exact isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  refine ⟨fun i t P => ?_, ?_⟩
  · exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ (hω i t) hθ (fun _ => 1) (fun _ => 1) (R.BV i) _
      (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) _ 1 1
      (fun τ => by rw [Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_mt_one', Matrix.mul_one, Matrix.one_mul]) (fun _ => rfl) (fun _ => rfl) _ (hth i t) P).1
  suffices h : ∀ i, ∃ y : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
      ∀ t, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t) (R.ptP i t) (RealDat.Delta i) y from
    Classical.skolem.1 h
  intro i
  obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => onb_eq_one (hM.BV i τ)
  have hBu : ∀ τ, IsUnit (R.BV i τ) := fun τ => (IsUnit.of_mul_eq_one_right _ (hBS τ))
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hM.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank := fun τ =>
    (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).rank.1.trans hrk.symm
  obtain ⟨io, h1, h2, h3⟩ := exists_io_poly D (Vc D i) (Wc D i) R.θ _ (R.MW i (sg0 D A)) (R.cV i) _ (c0L i) hθ
    (hM.cV i) (hT.mapL i) (R.BV i) hBu _ _ _ _ x₁ x₂ x₃ (hrk.le.trans (r_le_V i)) hpq (hM.order i)
    (fun τ => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).aPlus_antitone) (fun τ => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).aM_anti) (fun τ => (hx τ).2.2.2.1)
    (fun τ => (hx τ).2.2.2.2)
  refine ⟨io, fun t => ?_⟩
  have hact := GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) _ (R.MW i (sg0 D A)) (R.BV i) (hω i t) hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hM.order i) _ _ (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T R.toLevCh A.μ0 hL i t τ).chiV)
    (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T R.toLevCh A.μ0 hL i t τ).chiW) x₁ x₂ x₃ (fun τ => (hx τ).1) (fun τ => (hx τ).2.1)
    (fun τ => (hx τ).2.2.1) _ (hth i t)
    (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hv i t) (hth i t))
  have hfr : ∀ τ, (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ))
  refine ⟨fun u hu x w => ?_, fun τ k hk v u hu w => ?_, h3⟩
  · have e : (fun τ => (R.MW i (sg0 D A)).fr τ * compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) *
        ((R.MW i (sg0 D A)).fr τ)⁻¹) = 1 := by
      funext τ; rw [compAt_mt_one', Matrix.mul_one, hfr]; rfl
    obtain ⟨a, b⟩ := hact u hu 1 (one_mem _) fun τ => by rw [congrFun e τ]; exact one_mem_K
    rw [← h1 u hu a x w]
    have := b (io x w)
    rw [e] at this
    exact this
  · have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (conj_mem_UH (R.MW i (sg0 D A)) τ hk)
    have e : (fun ρ => (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
        (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹) = Pi.mulSingle τ k := by
      funext ρ
      rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
      by_cases h : ρ = τ
      · subst h
        rw [hs.2.1, Pi.mulSingle_eq_same]
        calc _ = ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) * k *
            ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
          _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
      · rw [hs.2.2 ρ h, Pi.mulSingle_eq_of_ne h, Matrix.mul_one, hfr]
    have e' : (fun ρ => (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ) = 1 := by
      funext ρ
      rw [compAt_mt_one', Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ))]; rfl
    obtain ⟨-, b⟩ := hact 1 (one_mem _) _ hs.1 fun ρ => by
      rw [congrFun e ρ]
      by_cases h : ρ = τ
      · subst h; rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_K
    rw [← h2 τ k hk v u hu w]
    have := b (io (PiTensorProduct.tprod ℂ v) w)
    rw [e, e'] at this
    exact this

end GlobalTheory.JointHarm

end
