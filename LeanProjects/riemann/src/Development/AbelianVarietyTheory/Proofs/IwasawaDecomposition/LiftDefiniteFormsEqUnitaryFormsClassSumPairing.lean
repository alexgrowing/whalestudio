import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLiftsStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.LiftForms

theorem exists_embed {K N W : Type} [Field K] [AddCommGroup N] [Module ℂ N] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {σ : K →+* ℂ} {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (li : LinearIndependent ℂ (fun k => j (Pi.single k 1)))
    (sp : Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤) (a : (Fin n → K) → N)
    (hadd : ∀ x y, a (x + y) = a x + a y) (hsmul : ∀ (c : K) x, a (c • x) = σ c • a x)
    (C : Submodule ℂ N) (ip : N → N → ℂ) (hC : PeterssonHilbertSpace.IsHermPos C ip) (hsp : Submodule.span ℂ (Set.range a) = C)
    (hip : ∀ x x', ⟪j x, j x'⟫_ℂ = ip (a x) (a x')) :
    ∃ J : W →ₗ[ℂ] N, Function.Injective J ∧ LinearMap.range J = C ∧ (∀ x x', ⟪x, x'⟫_ℂ = ip (J x) (J x')) ∧
      ∀ x, J (j x) = a x := by
  classical
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk li sp.ge
  have hb : ∀ k, b k = j (Pi.single k 1) := fun k => Module.Basis.mk_apply li sp.ge k
  let J : W →ₗ[ℂ] N := b.constr ℂ fun k => a (Pi.single k 1)
  let a' : (Fin n → K) →ₛₗ[σ] N := { toFun := a, map_add' := hadd, map_smul' := hsmul }
  have hJ : ∀ x, J (j x) = a x := by
    have h : (J : W →ₛₗ[RingHom.id ℂ] N).comp j = a' := by
      refine (Pi.basisFun K (Fin n)).ext fun k => ?_
      rw [Pi.basisFun_apply, LinearMap.comp_apply, ← hb]
      exact b.constr_basis ℂ _ k
    intro x
    exact LinearMap.congr_fun h x
  have htop : ∀ u : W, u ∈ Submodule.span ℂ (Set.range j) := by
    intro u
    have hu : u ∈ Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) := sp ▸ Submodule.mem_top
    exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩) hu
  have hr : LinearMap.range J = C := by
    have h1 : Submodule.span ℂ (Set.range j) = ⊤ := eq_top_iff.2 fun u _ => htop u
    rw [LinearMap.range_eq_map, ← h1, Submodule.map_span, ← Set.range_comp, ← hsp]
    congr 2
    exact funext hJ
  have hm : ∀ u, J u ∈ C := fun u => hr ▸ LinearMap.mem_range_self J u
  have hz : ∀ v, ip 0 (J v) = 0 := by
    intro v
    have := hC.smul 0 0 ⟨_, hm v⟩
    simpa using this
  have left : ∀ v, (∀ x, ⟪j x, v⟫_ℂ = ip (J (j x)) (J v)) → ∀ u, ⟪u, v⟫_ℂ = ip (J u) (J v) := by
    intro v hv u
    induction htop u using Submodule.span_induction with
    | mem _ h => obtain ⟨x, rfl⟩ := h; exact hv x
    | zero => rw [inner_zero_left, map_zero, hz]
    | add p q _ _ hp hq =>
      rw [inner_add_left, map_add, hp, hq]
      exact (hC.add ⟨_, hm p⟩ ⟨_, hm q⟩ ⟨_, hm v⟩).symm
    | smul s p _ hp =>
      rw [inner_smul_left, map_smul, hp]
      exact (hC.smul s ⟨_, hm p⟩ ⟨_, hm v⟩).symm
  have hall : ∀ u v, ⟪u, v⟫_ℂ = ip (J u) (J v) := by
    intro u v
    refine left v (fun x => ?_) u
    have h1 : ⟪v, j x⟫_ℂ = ip (J v) (J (j x)) := left (j x) (fun x' => by rw [hJ, hJ, hip]) v
    rw [← inner_conj_symm, h1]
    exact hC.herm ⟨_, hm v⟩ ⟨_, hm (j x)⟩
  refine ⟨J, ?_, hr, hall, hJ⟩
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h := hall u u
  rw [show ip (J u) (J u) = ip 0 (J u) by rw [hu], hz] at h
  exact inner_self_eq_zero.1 h

set_option maxHeartbeats 2000000 in

theorem lift_forms_embed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 i t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W), LinearIndependent ℂ (fun k => j (Pi.single k 1)) → Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤ → (∀ x x', ⟪j x, j x'⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t) x x')) → ∃ J : W →ₗ[ℂ] (GA D ((y.L F.lv2).V i) → (y.L F.lv2).TauV i), Function.Injective J ∧ LinearMap.range J = (y.L F.lv2).Amt (y.tup t) i ∧ (∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipA (y.tup t) i (J x) (J x')) ∧ ∀ x, J (j x) = R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hP hH y i t W _ _ j li sp hip
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  have hok : A3.A.fam.Ok 1 := hH.ok.ok2
  have h := (GlobalTheory.T.classSums_eq_pairings_topChain_lifts D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hB hP.keep.prX hok (y.tup t)).2.2 i
  have hA := GlobalTheory.HilbertLevels.hermA R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj (y.tup t) i
  have key : ∀ t', t' = t → (Submodule.span ℂ (Set.range fun x => R.toRealDat.extV i t' (R.toRealDat.jV i t' (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t' x))) = (y.L F.lv2).Amt (y.tup t) i ∧ ∀ x x', (y.L F.lv2).ipA (y.tup t) i (R.toRealDat.extV i t' (R.toRealDat.jV i t' (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t' x))) (R.toRealDat.extV i t' (R.toRealDat.jV i t' (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t' x'))) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t') x x')) →
      (Submodule.span ℂ (Set.range fun x => R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x))) = (y.L F.lv2).Amt (y.tup t) i ∧ ∀ x x', (y.L F.lv2).ipA (y.tup t) i (R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x))) (R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x'))) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t) x x')) := by
    rintro _ rfl h'
    exact h'
  obtain ⟨h1, h2⟩ := key (y.tupT (y.tup t)) (y.tupT_tup t) h
  refine exists_embed j li sp
    (fun x => R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x))) ?_ ?_ _ _ hA h1 ?_
  · intro x x'
    simp only [DatApi.liftForm_add]
    exact (congrArg _ (map_add (R.toRealDat.jV i t) _ _)).trans (map_add (R.toRealDat.extV i t) _ _)
  · intro c x
    simp only [DatApi.liftForm_smul]
    exact (congrArg _ (map_smulₛₗ (R.toRealDat.jV i t) _ _)).trans (map_smul (R.toRealDat.extV i t) _ _)
  · intro x x'
    exact (hip x x').trans (h2 x x').symm

end GlobalTheory.Mem.R3.Rw.LiftForms
