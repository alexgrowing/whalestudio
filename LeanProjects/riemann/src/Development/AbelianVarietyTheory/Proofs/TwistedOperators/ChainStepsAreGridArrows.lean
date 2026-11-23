import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultTEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

variable {D : D7}

section Transfer

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem actO_eq_of_real {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) {x : WO S T}
    (hx : x.map (infPart D) = 0) : actO S T g h x = x := by
  have e1 : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = 1 := congrArg Units.val (show finHom S g⁻¹ = 1 from inv_mem hg)
  have e2 : (Formalism.L2.Theta.mt T h).map (finPart D) = 1 := congrArg Units.val (show finHom T h = 1 from hh)
  have e3 : (actO S T g h x).map (infPart D) = x.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]
  have e4 : (actO S T g h x).map (finPart D) = x.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.mul_one, Matrix.one_mul]
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun e3 i) j) (congrFun (congrFun e4 i) j)

theorem isItW_of_mem_span {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T} (hω : IsWeilDatumO ψ S T χS χT ω) (hθ : IsInfFam θ)
    {P P' : D.what₂.Tau → SPar} {M : DSModel S P} {M' : DSModel T P'}
    {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀))
    {It : PolF D T.rank S.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (h : IsItW θ M M' ω (pureTensorO ψ θ S T sS sT BS BT f) It) :
    IsItW θ M M' ω (pureTensorO ψ θ S T sS sT BS BT f₀) It := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  let L : Module.End ℂ (WO S T → ℂ) := ∑ a ∈ c.support, c a • GlobalTheory.SplitScalar.heisL ψ S T a.1
  have hL : ∀ F, L F = ∑ a ∈ c.support, c a • heisO ψ S T a.1 F := fun F => by
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, GlobalTheory.SplitScalar.heisL_apply]
  have hd : ∀ τ z F, IsThetaFunO ψ S T F → L (dRho (heisO ψ S T) θ τ z F) = dRho (heisO ψ S T) θ τ z (L F) :=
    fun τ z F hF => by
      rw [hL, hL, GlobalTheory.FockTranslate.dRho_sum hω.std.1.1 hθ hF τ z c.support (fun a => a.1) c fun a _ => a.2]
  have hpt : ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f₀ Q) ∧
      L (pureTensorO ψ θ S T sS sT BS BT f₀ Q) = pureTensorO ψ θ S T sS sT BS BT (L f₀) Q := fun Q => by
    refine GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
      (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _ _ L (fun k F hF => ?_) f₀ h₀ Q
    obtain ⟨τ, i, j⟩ := k
    refine ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub (GlobalTheory.OrientedHeis.theta_dRho hθ hω.std τ _ hF)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hω.std τ _ hF))), ?_⟩
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul, hd _ _ _ hF, hd _ _ _ hF]
  have hom : ∀ g ∈ GinfC S, ∀ k ∈ GinfC T, ∀ Q, ω (g, k) (pureTensorO ψ θ S T sS sT BS BT (L f₀) Q) =
      L (ω (g, k) (pureTensorO ψ θ S T sS sT BS BT f₀ Q)) := fun g hg k hk Q => by
    rw [← (hpt Q).2, hL, hL, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hω.om_heis _ _ _ _ (hpt Q).1, actO_eq_of_real hg hk a.2]
  have hder : ∀ (F : ℝ → WO S T → ℂ) (F' : WO S T → ℂ), (∀ z, HasDerivAt (fun t => F t z) (F' z) 0) →
      ∀ z, HasDerivAt (fun t => L (F t) z) (L F' z) 0 := fun F F' hF z => by
    simp only [hL, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]
    exact HasDerivAt.fun_sum fun a _ => ((hF _).const_mul _).const_mul _
  have e : (c.sum fun i a => a • heisO ψ S T i.1 f₀) = L f₀ := (hL f₀).symm
  rw [e] at h
  refine ⟨h.ne, h.bdd, fun τ g hg φ φ' H => h.eqK τ g hg φ φ' ?_, fun τ X hX φ φ' H => h.eqg τ X hX φ φ' fun z => ?_,
    fun τ g hg φ φ' v v' H => h.invK τ g hg φ φ' v v' ?_, fun τ X hX φ φ' v v' H => h.invg τ X hX φ φ' v v' fun z => ?_⟩
  · rw [hom _ (GlobalTheory.FinTranslate.atTau_mem θ S τ g) _ (one_mem _), ← H, (hpt φ').2]
  · simp only [fun t => hom _ (GlobalTheory.FinTranslate.oneP_mem θ S τ X t) _ (one_mem _) φ, ← (hpt φ').2]
    exact hder _ _ H z
  · rw [hom _ (one_mem _) _ (GlobalTheory.FinTranslate.atTau_mem θ T τ g), ← H, (hpt φ').2]
  · simp only [fun t => hom _ (one_mem _) _ (GlobalTheory.FinTranslate.oneP_mem θ T τ X t) φ, ← (hpt φ').2]
    exact hder _ _ H z

theorem stepVec_mem_span
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {L : LevDat D.host.E ℂ S.rank}
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT L χ Q ξ f₀ f) :
    f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) := by
  classical
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := h
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO dS.1 dT.1 βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  rw [hall Tm hTm]
  exact (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hinf hTm hSB).1

theorem finVec_of_mem_span
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}
    (hv : IsVacO ψ θ S T sS sT ΛS ΛT f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀)) :
    IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  exact ⟨GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hv.1.1 f₀ hv.2.theta _ c.support (fun a => a.1) c fun a _ => a.2,
    fun τ => GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hv.1.1 hv.2.inf f₀ hv.2.theta τ _ (hv.2.fock τ) _ c.support
      (fun a => a.1) c fun a _ => a.2⟩

end Transfer

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem chrStep_eq_muAt (R : RealDat D A Ks) (t : T) (j : ℕ) : Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) =
    (GridPre.muAt R t (j + 1) (rkV D 0 j), GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

end GlobalTheory.Grid

end
