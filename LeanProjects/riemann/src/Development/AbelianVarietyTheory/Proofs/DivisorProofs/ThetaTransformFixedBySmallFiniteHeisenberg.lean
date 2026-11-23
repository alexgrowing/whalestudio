import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantCompactSupportInvariantOpenAddSubStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupAddCharDotProductTrivialOnCompactStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLevel

theorem uniform_locConst {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [NonarchimedeanAddGroup X] (g : X → ℂ) (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z :=
  GlobalTheory.T.exists_openAddSubgroup_invariant_of_locallyConstant g hg hc

theorem char_dot_compact {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (χ : AddChar K ℂ) (hχ : Continuous χ) (κ : Type) [Fintype κ] (C : Set (κ → K))
    (hC : IsCompact C) : ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 :=
  GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact χ hχ κ C hC

end GlobalTheory.ThetaLevel

namespace GlobalTheory.ThetaLevel

open Matrix

section Heis

variable {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]

theorem schr_add (a b : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ (a + b) φ x =
      ψ (-(⅟(2 : R) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2))) * GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ b φ) x := by
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x a.1 b.1]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (a.1 ⬝ᵥ b.2) * (invOf_two_add_invOf_two : ⅟(2 : R) + ⅟(2 : R) = 1)

end Heis

theorem symp_eq_symplO (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (x y : Formalism.IndefR.Datum.WO S T) :
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
      Formalism.IndefR.Datum.symplO S T x y := by
  have hB' : ∀ a b, ξ * incM D.host.F JB a b = incA (D := D) D.host.xi0 * incA (D := D) (S.gram⁻¹ a b) := by
    intro a b
    have h := congrFun (congrFun hB a) b
    rw [Matrix.smul_apply, smul_eq_mul] at h
    rw [h]
    show incA (D := D) (D.host.xi0 * S.gram⁻¹ a b) = _
    rw [map_mul]
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.symplO Formalism.IndefR.Datum.hO
  congr 1
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  subst hA
  have hT : incM D.host.F T.gramᵀ i k = incA (D := D) (T.gram k i) := rfl
  rw [hT]
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (y k l) = Formalism.L2.Theta.cA D (y k l) := rfl
  rw [hc]
  linear_combination (x i j * incA (D := D) (T.gram k i) * Formalism.L2.Theta.cA D (y k l)) * hB' j l

end GlobalTheory.ThetaLevel

namespace GlobalTheory.ThetaLevel

open Matrix

def infIncl (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := pairA F x 0
  map_add' _ _ := Prod.ext rfl (add_zero 0).symm
  map_smul' c _ := Prod.ext rfl (smul_zero c).symm

set_option maxHeartbeats 2000000 in

theorem infIdem_smul (D : D7) (z : AE D) :
    pairA D.host.F 1 0 • z = TensorProduct.map (infIncl D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (one_mul _) (zero_mul _)
  | add z z' hz hz' =>
    rw [smul_add (pairA D.host.F 1 0) z z', hz, hz', map_add (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) z z',
      map_add]

theorem finIdem_smul (D : D7) (z : AE D) (hz : infPart D z = 0) : pairA D.host.F 0 1 • z = z := by
  have h1 : pairA D.host.F 0 1 + pairA D.host.F 1 0 = 1 := Prod.ext (zero_add 1) (add_zero 1)
  have h2 := infIdem_smul D z
  rw [show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 from hz, map_zero] at h2
  calc pairA D.host.F 0 1 • z = pairA D.host.F 0 1 • z + pairA D.host.F 1 0 • z := by rw [h2, add_zero]
    _ = z := by rw [← add_smul, h1, one_smul]

theorem e_eq_fin (D : D7) (S T : HSp D) {B : Formalism.IndefR.Datum.WO S T → Formalism.IndefR.Datum.WO S T → AF D.host.F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (u : Formalism.IndefR.Datum.WO S T)
    (hu : u.map (infPart D) = 0) :
    co.e u = ((fun i => pairA D.host.F 0 ((co.e u).1 i).2), (fun i => pairA D.host.F 0 ((co.e u).2 i).2)) := by
  have hu' : pairA D.host.F 0 1 • u = u := by
    ext a b
    exact finIdem_smul D (u a b) (congrFun (congrFun hu a) b)
  have h2 := congrArg co.e hu'
  rw [LinearEquiv.map_smul] at h2
  conv_lhs => rw [← h2]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact Prod.ext (zero_mul _) (one_mul _)
  · exact Prod.ext (zero_mul _) (one_mul _)

theorem schr_fin_fix (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ K : OpenAddSubgroup (κ → Af F), ∀ a ∈ K, ∀ b ∈ K,
      GlobalTheory.WeilM.schr ψ ((fun i => pairA F 0 (a i)), (fun i => pairA F 0 (b i))) Φ = Φ := by
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → Af F) := GlobalTheory.HeisSchA.nonarch_pi
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨H1, hH1⟩ := uniform_locConst g hg.1 hg.2
    obtain ⟨H2, hH2⟩ := char_dot_compact (GlobalTheory.HeisSchA.finChar ψ)
      (hψ.comp (continuous_const.prodMk continuous_id)) κ (tsupport g) hg.2
    let c : Af F := (⅟(2 : AF F)).2
    let m : (κ → Af F) →+ (κ → Af F) := DistribMulAction.toAddMonoidHom _ c
    have hm : Continuous m := continuous_const_smul c
    refine ⟨H1 ⊓ H2 ⊓ H2.comap m hm, fun a ha b hb => funext fun x => ?_⟩
    obtain ⟨⟨ha1, -⟩, ha3⟩ := ha
    obtain ⟨⟨-, hb2⟩, -⟩ := hb
    let z : κ → Af F := fun i => (x i).2
    have hpa1 : GlobalTheory.WeilM.pureA F f g (x + fun i => pairA F 0 (a i)) =
        f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g (z + a) := by
      simp only [GlobalTheory.WeilM.pureA]
      congr 2
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + 0) = _
      rw [add_zero]
    have hpa0 : GlobalTheory.WeilM.pureA F f g x = f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g z := rfl
    have harg : x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) * ((fun i => pairA F 0 (a i)) ⬝ᵥ (fun i => pairA F 0 (b i)))
        = pairA F 0 (z ⬝ᵥ b + (c • a) ⬝ᵥ b) := by
      have e1 : GlobalTheory.HeisSchA.p1 (F := F) (x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) *
          ((fun i => pairA F 0 (a i)) ⬝ᵥ (fun i => pairA F 0 (b i)))) = 0 := by
        rw [map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
        have e0 : (fun i => GlobalTheory.HeisSchA.p1 (F := F) (pairA F 0 (b i))) = 0 := funext fun i => rfl
        simp only [Function.comp_def, e0, dotProduct_zero, mul_zero, add_zero]
      have e2 : GlobalTheory.HeisSchA.p2 (F := F) (x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) *
          ((fun i => pairA F 0 (a i)) ⬝ᵥ (fun i => pairA F 0 (b i)))) = z ⬝ᵥ b + (c • a) ⬝ᵥ b := by
        rw [map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct, smul_dotProduct, smul_eq_mul]
        rfl
      exact Prod.ext e1 e2
    show ψ (x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) * ((fun i => pairA F 0 (a i)) ⬝ᵥ
      (fun i => pairA F 0 (b i)))) * GlobalTheory.WeilM.pureA F f g (x + fun i => pairA F 0 (a i)) = GlobalTheory.WeilM.pureA F f g x
    rw [harg, hpa1, hpa0, hH1 z a ha1]
    by_cases hz : g z = 0
    · rw [hz, mul_zero, mul_zero]
    · have h3 : GlobalTheory.HeisSchA.finChar ψ (z ⬝ᵥ b + (c • a) ⬝ᵥ b) = 1 := hH2 z (subset_tsupport _ hz) _ ha3 b hb2
      rw [show ψ (pairA F 0 (z ⬝ᵥ b + (c • a) ⬝ᵥ b)) = 1 from h3, one_mul]
  | zero => exact ⟨⊤, fun a _ b _ => funext fun x => mul_zero _⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨K1, hK1⟩ := h1
    obtain ⟨K2, hK2⟩ := h2
    refine ⟨K1 ⊓ K2, fun a ha b hb => funext fun x => ?_⟩
    have e1 := congrFun (hK1 a ha.1 b hb.1) x
    have e2 := congrFun (hK2 a ha.2 b hb.2) x
    simp only [GlobalTheory.WeilM.schr] at e1 e2 ⊢
    rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
  | smul r Φ₁ _ h1 =>
    obtain ⟨K1, hK1⟩ := h1
    refine ⟨K1, fun a ha b hb => funext fun x => ?_⟩
    have e1 := congrFun (hK1 a ha b hb) x
    simp only [GlobalTheory.WeilM.schr] at e1 ⊢
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]

end GlobalTheory.ThetaLevel

namespace GlobalTheory.ThetaLevel

open Matrix

set_option maxHeartbeats 1000000 in

theorem thetaTr_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∃ U : AddSubgroup (Formalism.IndefR.Datum.WO S T), IsOpen (U : Set (Formalism.IndefR.Datum.WO S T)) ∧
          ∀ u ∈ U, u.map (infPart D) = 0 → Formalism.IndefR.Datum.heisO ψ S T u (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF D.host.F) (Formalism.IndefR.Datum.WO S T) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → AE D))
  obtain ⟨K, hK⟩ := schr_fin_fix D.host.F ψ hψ.1.1 Φ hΦ
  have hcont : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  let f1 : Formalism.IndefR.Datum.WO S T →+ (κ → Af D.host.F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).1 i).2) (fun u v => by funext i; rw [map_add]; rfl)
  let f2 : Formalism.IndefR.Datum.WO S T →+ (κ → Af D.host.F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).2 i).2) (fun u v => by funext i; rw [map_add]; rfl)
  have hf1 : Continuous f1 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hcont))
  have hf2 : Continuous f2 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hcont))
  let U : OpenAddSubgroup (Formalism.IndefR.Datum.WO S T) := K.comap f1 hf1 ⊓ K.comap f2 hf2
  refine ⟨(U : AddSubgroup _), U.isOpen, fun u hu hinf => funext fun w => ?_⟩
  have hfix : GlobalTheory.WeilM.schr ψ (co.e u) Φ = Φ := by
    rw [e_eq_fin D S T co u hinf]
    exact hK _ hu.1 _ hu.2
  show ψ (Formalism.IndefR.Datum.symplOH S T w u) * GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (co.e (w + u)) Φ) =
    GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (co.e w) Φ)
  rw [map_add]
  have h1 : GlobalTheory.WeilM.schr ψ (co.e w + co.e u) Φ = fun x =>
      ψ (-(⅟(2 : AF D.host.F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2))) *
        GlobalTheory.WeilM.schr ψ (co.e w) (GlobalTheory.WeilM.schr ψ (co.e u) Φ) x :=
    funext (schr_add ψ _ _ Φ)
  rw [h1, hfix]
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have h2 : Formalism.IndefR.Datum.symplOH S T w u =
      ⅟(2 : AF D.host.F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2) := by
    rw [← co.form, symp_eq_symplO D S T JA JB ξ hA hB, Formalism.IndefR.Datum.symplOH]
    congr 1
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [h2, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThetaLevel
