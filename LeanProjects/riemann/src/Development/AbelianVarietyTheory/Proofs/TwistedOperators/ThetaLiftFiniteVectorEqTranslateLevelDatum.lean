import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLevelDatumSumOfTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceModelIndicatorThetaFockLatticeVacuumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelFiniteVectorNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianThetaLevelGroupStabilizesSelfDualLatticStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StronglyMeasurableIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in

theorem thP_vec_eq_translate : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (hn : T.rank ≤ S.rank) (B : C.Bas), C.IsB B → ∀ ΛT : Lt D.host.E T.rank, IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ f₀ f, IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f → ∃ (Lv : SW.Level C.X) (M : ℕ) (f' : WO S T → ℂ) (k₀ : GA D S), IdemTwo Lv.w ∧ 0 < M ∧ (M : 𝓞 D.host.E) ∈ Lv.𝔪 ∧ C.IsBase Lv B f' ∧ k₀ ∈ GfC S ∧ f = om (k₀, 1) (C.uVec Lv hn f') ∧ C.IsTh (C.uVec Lv hn f') ∧ C.IsFock B (C.uVec Lv hn f') ∧ C.uVec Lv hn f' ≠ 0 ∧ ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  intro D S T C om hom hn B hB ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg hodd f₀ f hf
  have hf0 : f ≠ 0 := GlobalTheory.T.theta_kernel_finite_vector_ne_zero D S T C hn B hB ΛT hsd βS βT hβS hβT Pg Q ξ f₀ f hf
  have hfc := hf
  obtain ⟨hvac, e, he, hθ⟩ := hf
  obtain ⟨Lv, k₀, Λ', L, hw2, hmP, hJ, hk₀, hmov, hfin, hA, hB', hC, hD, hE, hF⟩ :=
    GlobalTheory.T.thetaLift_level_datum_sum_of_translates D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg hodd e he
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hfT : f = Tm (thPDatum S T βS βT Pg Q ξ e) := hall Tm hTm
  obtain ⟨hSB, hTh, hFock, hLat⟩ := GlobalTheory.T.placeModel_indicator_theta_fock_latticeVacuum D S T C B hB ΛT hsd (Pg ∪ Q) e he f₀ hvac Tm hTm L hA hB' hC
  have hLat'' := hLat _ hD
  haveI := Fintype.ofFinite (LvCls C Lv)
  set f'' := Tm (indL L) with hf''
  have hee : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hhalf : ∀ w : WO S T, IsHalf (cA D e) (partAt (cA D e) w) := fun w i j => by
    simp only [partAt, Matrix.map_apply]
    rw [← mul_assoc, hee]
  set t : LvCls C Lv → WO S T := fun c =>
    partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) with ht
  have hfsum : f = ∑ c : LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) •
      heisO C.ψ S T (t c) f'' := by
    rw [hfT]
    have hΦ : thPDatum S T βS βT Pg Q ξ e = ∑ c : LvCls C Lv,
        Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) • fun x => indL L (x + t c) := by
      funext x
      rw [hF x, finsum_eq_sum_of_fintype, Finset.sum_apply]
      rfl
    rw [hΦ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, hTm.trans _ hSB _ (hhalf _)]
  set f' := om (k₀⁻¹, 1) f'' with hf'
  have hinv : ∀ g : GA D S, ∀ x, om (g, 1) (om (g⁻¹, 1) x) = x := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one]
    exact congrArg (fun E : Module.End ℂ (WO S T → ℂ) => E x) om.map_one
  have hinv' : ∀ g : GA D S, ∀ x, om (g⁻¹, 1) (om (g, 1) x) = x := fun g x => by
    simpa using hinv g⁻¹ x
  have hom1 : om (k₀, 1) f' = f'' := hinv k₀ f''
  have hTh' : C.IsTh f' := hom.om_pres _ _ hTh
  have hu : om (k₀, 1) (C.uVec Lv hn f') = f := by
    rw [hfsum, Ctx.uVec, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul]
    congr 1
    rw [Ctx.rho, hom.om_heis _ _ _ _ hTh', hom1]
    obtain ⟨v, hv, hv1, hv2⟩ := hE _ (c.out).2
    have h2 : heisO C.ψ S T (2 • v) f'' = f'' := hLat''.1 v hv
    have h3 := GlobalTheory.FinTranslate.heisO_heisO S T C.ψ (t c) (2 • v) f''
    rw [h2, show C.ψ (symplOH S T (t c) (2 • v)) = 1 from hv2, one_smul] at h3
    calc heisO C.ψ S T (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) f''
        = heisO C.ψ S T (t c + 2 • v) f'' := congrArg (fun w => heisO C.ψ S T w f'') hv1
      _ = heisO C.ψ S T (t c) f'' := h3.symm
  have hmt1 : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => by simp [Formalism.L2.Theta.mt]
  have hmvB : C.mvB 1 B = B := by
    funext τ
    simp [Ctx.mvB, hmt1, compAt]
  have hfmt1 : fmt T 1 = 1 := by simp [fmt, hmt1]
  have hmov1 : IsMov (fmt T 1) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) := by
    rw [hfmt1]
    intro u
    exact ⟨fun h => ⟨u, h, (Matrix.one_mulVec u).symm⟩, fun ⟨u₀, h, e⟩ => by rw [e, Matrix.one_mulVec]; exact h⟩
  have hne' : f' ≠ 0 := by
    intro h0
    apply hf0
    have : f'' = 0 := by rw [← hom1, h0, map_zero]
    rw [hfsum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [this]
    have : heisO C.ψ S T (t c) (0 : WO S T → ℂ) = 0 := by
      funext w
      simp [heisO]
    rw [this, smul_zero]
  have hFock' : C.IsFock B f' := by
    have := (((GlobalTheory.Ker.WeakMove.om_move D S T C om hom k₀⁻¹ 1 f'' hTh).2 B hB).1 hFock)
    rwa [hmvB] at this
  have hlat' : IsLatVac (heisO C.ψ S T) (hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ))) f' :=
    (GlobalTheory.TensLatMove.hatA_move D S T C k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hmov hmov1).2
      om hom f'' hTh hLat''
  have hbase : C.IsBase Lv B f' := ⟨hTh', hne', hFock', hlat'⟩
  have hu1 : C.IsTh (C.uVec Lv hn f') := GlobalTheory.Ker.KernelCompare.isTh_uVec C Lv hn hTh'
  have hfth : C.IsTh f := hu ▸ hom.om_pres _ _ hu1
  have hfF : C.IsFock B f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_thPVec C.ψ C.θ S T _ _ _ _ βS βT Pg Q ξ f₀ f hfc hfth τ
  have hu2 : C.IsFock B (C.uVec Lv hn f') := by
    have h := (((GlobalTheory.Ker.WeakMove.om_move D S T C om hom k₀⁻¹ 1 f hfth).2 B hB).1 hfF)
    rw [hmvB, ← hu, hinv'] at h
    exact h
  have hu3 : C.uVec Lv hn f' ≠ 0 := fun h0 => hf0 (by rw [← hu, h0, map_zero])
  refine ⟨Lv, Ideal.absNorm Lv.𝔪, f', k₀, hw2, ?_, Ideal.absNorm_mem Lv.𝔪, hbase, hk₀, hu.symm, hu1, hu2, hu3,
    GlobalTheory.T.hermitianThetaLevelGroup_stabilizes_selfDualLatticeFrame D S T C Lv ΛT hsd hAA βT hβT Pg hmP hJ⟩
  exact Nat.pos_of_ne_zero fun h => Lv.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

end GlobalTheory.LiftLevel

end
