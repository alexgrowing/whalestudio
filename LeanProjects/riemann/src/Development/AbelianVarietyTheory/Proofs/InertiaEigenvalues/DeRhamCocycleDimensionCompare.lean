import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundary

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoOrth

open GlobalTheory.BKOrth

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem pairT_filV_right (P : V →ₗ[LL] V' →ₗ[LL] LL) (a : ℤ) (v : V) (z : V' ⊗[Qp] BdR)
    (hz : z ∈ FilV PD (LL := LL) (V := V') a) :
    pairT BdR P (v ⊗ₜ[Qp] (1 : BdR)) z ∈ FilV PD (LL := LL) (V := LL) a := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add]; exact add_mem hy hy'
  | tmul v' f =>
    rw [AlgebraTensorModule.map_tmul, pairT_tmul, one_mul]
    exact ⟨P v v' ⊗ₜ[Qp] f, rfl⟩

theorem actVB_one (ρ : Representation LL G V) (x : V ⊗[Qp] B) : actVB PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp [actVB_tmul]

end Gen

theorem cocycle_inv {G : Type} [Group G] {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]
    (ρ : Representation LL G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) :
    ρ g (c g⁻¹) = - c g := by
  have h1 : c 1 = 0 := by simpa using hc 1 1
  have := hc g g⁻¹
  rw [mul_inv_cancel, h1] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem goodO_Zl (l : ℕ) [Fact l.Prime] : GoodO (Qp := ℚ_[l]) ℚ_[l] ℤ_[l] := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  exact (PadicInt.isOpenEmbedding_coe (p := l)).isOpen_range

set_option maxHeartbeats 1600000 in

theorem orth_of_cont (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V']
    [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V']
    [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V')
    (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]) (hρ' : ∀ y, Continuous fun g => ρ' g y)
    (hdR : IsDR (P.PD K) ρ') (hD : IsDual1 (P.PD K) ρ ρ' m)
    (hχ : Continuous fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]))
    (c : ↥(GK K) → V) (hc : c ∈ geometricCocycles (P.PD K) ρ) (a : ↥(GK K) → V')
    (ha : a ∈ crystallineCocycles (P.PD K) ρ') : CobL (P.PD K) (cupL ρ' m c a) := by
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨hcz, b, hb⟩ := hc
  obtain ⟨haz, β, hβφ, hβ⟩ := ha
  obtain ⟨-, d, hd, hd'⟩ :=
    GlobalTheory.CobCrisLift.coboundary_lift l P AI hT K ℚ_[l] ℤ_[l] (goodO_Zl l)
      { V := V', ρ := ρ', cont := hρ' } hdR a β hβ
  have hfixd : ∀ g, actVdR (P.PD K) ρ' g d = d := fun g => by
    have := (Submodule.mem_iInf _).1 hd g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  obtain ⟨hsurj, hker⟩ := GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI hT K ℚ_[l] ℚ_[l]
  obtain ⟨we, w0, hw0, hweφ, hweι⟩ := hsurj 0 (pairT P.R.BdR m b d)
  have hweφ' : φVB (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) we = we := (sub_eq_zero.1 hweφ).symm
  let F : ↥(GK K) → ℚ_[l] ⊗[ℚ_[l]] P.R.B := fun h =>
    (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h we - we) -
      pairT P.R.B m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' h β)
  have hFφ : ∀ h, φVB (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) = F h := fun h => by
    have e1 : φVB (P.PD K) (LL := ℚ_[l]) (V := V) (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        c h ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
      simp [φVB]
    simp only [F, map_sub, pairT_φVB, e1, GlobalTheory.CobCrisLift.φVB_act, hβφ, hweφ']
  have hFι : ∀ h, ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) ∈
      FilV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) 0 := fun h => by
    have e1 : ιV (P.PD K) (LL := ℚ_[l]) (V := V) (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
      simp [ιV]
    have e2 : pairT P.R.BdR m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) (actVdR (P.PD K) ρ' h d) =
        actVdR (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h (pairT P.R.BdR m b d) -
          pairT P.R.BdR m b d := by
      rw [hb h, map_sub, LinearMap.sub_apply, ← pairT_actVdR (P.PD K) ρ ρ' m hD.1 h b d, hfixd h]
    have hι1 : ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) we = pairT P.R.BdR m b d + w0 :=
      sub_eq_iff_eq_add.1 hweι
    have s1 : ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) =
        (actVdR (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h w0 - w0) -
          pairT P.R.BdR m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR))
            (actVdR (P.PD K) ρ' h (ιV (P.PD K) (LL := ℚ_[l]) (V := V') β - d)) := by
      simp only [F, map_sub, pairT_ιV, e1, GlobalTheory.CobCrisLift.ιV_act, hι1, map_add, e2]
      abel
    rw [s1]
    exact sub_mem (sub_mem (actVdR_filV (P.PD K) _ 0 h w0 hw0) hw0)
      (pairT_filV_right (P.PD K) m 0 (c h) _ (actVdR_filV (P.PD K) ρ' 0 h _ hd'))
  have hF : ∀ h, ∃ x : ℚ_[l], F h = x ⊗ₜ[ℚ_[l]] (1 : P.R.B) := fun h => hker (F h) (hFφ h) (hFι h)
  choose f hf using hF
  let bas := Module.finBasis ℚ_[l] V
  let γ : Fin (finrank ℚ_[l] V) → ↥(GK K) → ℚ_[l] := fun i g => bas.coord i (c g)
  have hγ : ∀ i, Continuous (γ i) := fun i =>
    (IsModuleTopology.continuous_of_linearMap (bas.coord i)).comp hcz.1
  let k : ↥(GK K) → ℚ_[l] := fun h => charRep (cycLL (P.PD K) ℚ_[l]) h (f h⁻¹)
  have hsum : ∀ g, k g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      ∑ i, γ i g • pairT P.R.B m (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β +
        (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (-we) - -we) := by
    intro g
    have ec : c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = ∑ i, γ i g • (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
      conv_lhs => rw [← bas.sum_repr (c g)]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul']
      rfl
    have ek : k g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F g⁻¹) := by
      rw [hf g⁻¹, actVB_tmul, map_one]
    have e3 : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g
        (pairT P.R.B m (c g⁻¹ ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g⁻¹ β)) =
        -pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β := by
      rw [← pairT_actVB (P.PD K) ρ ρ' m hD.1 g, ← actVB_mul, mul_inv_cancel, actVB_one, actVB_tmul,
        map_one, cocycle_inv ρ c hcz.2 g, neg_tmul, map_neg, LinearMap.neg_apply]
    have e4 : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g
        (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g⁻¹ we) = we := by
      rw [← actVB_mul, mul_inv_cancel, actVB_one]
    rw [ek]
    simp only [F, map_sub, e3, e4, map_neg, ec, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply]
    abel
  have hk : Continuous k :=
    GlobalTheory.FundCont.contCore_tied l P AI hT K ℚ_[l] ℤ_[l] (goodO_Zl l)
      (charGRep (Qp := ℚ_[l]) (O := ℤ_[l]) (cycLL (P.PD K) ℚ_[l]) hχ) _
      (fun i => pairT P.R.B m (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β) γ hγ (-we) k hsum
  have hfk : f = fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * k g⁻¹ := by
    funext g
    simp only [k, charRep_apply, inv_inv]
    rw [← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul]
  have hcont : Continuous f := by
    rw [hfk]
    exact hχ.mul (hk.comp continuous_inv)
  refine ⟨f, hcont, ?_⟩
  funext ⟨g, h⟩
  have hcup : cupL ρ' m c a (g, h) = m (c g) (ρ' g (a h)) := rfl
  rw [hcup]
  apply tmul_one_injective (P.PD K) (LL := ℚ_[l])
  beta_reduce
  have hd1 : ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) ℚ_[l])) f (g, h) =
      charRep (cycLL (P.PD K) ℚ_[l]) g (f h) - f (g * h) + f g := rfl
  have hact : (charRep (cycLL (P.PD K) ℚ_[l]) g (f h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
    rw [actVB_tmul, map_one]
  have hch : actVB (P.PD K) ρ g (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [actVB_tmul, map_one]
  have hcoc : c (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) + ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [hcz.2 g h, add_tmul]
  have hrhs : (m (c g) (ρ' g (a h))) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B))
          (actVB (P.PD K) ρ' g (actVB (P.PD K) ρ' h β)) -
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g β) := by
    have e : (m (c g) (ρ' g (a h))) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g (a h ⊗ₜ[ℚ_[l]] (1 : P.R.B))) := by
      rw [actVB_tmul, map_one, pairT_tmul, mul_one]
    rw [e, hβ h, map_sub, map_sub]
  have main : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F h) - F (g * h) + F g =
      pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B))
          (actVB (P.PD K) ρ' g (actVB (P.PD K) ρ' h β)) -
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g β) := by
    simp only [F, map_sub, actVB_mul, hcoc, map_add, LinearMap.add_apply,
      ← pairT_actVB (P.PD K) ρ ρ' m hD.1 g, hch]
    abel
  calc (ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) ℚ_[l])) f (g, h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
      = actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) -
          f (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) + f g ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
        rw [hd1, tmul_one_sub_add, hact]
    _ = actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F h) - F (g * h) + F g := by
        rw [hf h, hf (g * h), hf g]
    _ = _ := main
    _ = _ := hrhs.symm

theorem hyodo_orth : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → ∀ c ∈ geometricCocycles (P.PD K) ρ, ∀ a ∈ crystallineCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m c a) := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hρ hρ' hdR hD c hc a ha
  by_cases hV : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hV
    obtain ⟨v', hv'⟩ : ∃ v', m v v' ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (hD.2.1 v h)
    have hm : Continuous fun p : V × V' => m p.1 p.2 :=
      IsModuleTopology.continuous_bilinear_of_finite_left m
    have hχ : Continuous fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) := by
      have e : (fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])) =
          fun g => m (ρ g v) (ρ' g v') * (m v v')⁻¹ := by
        funext g
        rw [hD.1, mul_assoc, mul_inv_cancel₀ hv', mul_one]
      rw [e]
      exact (hm.comp ((hρ v).prodMk (hρ' v'))).mul continuous_const
    exact orth_of_cont l P AI hT K V ρ V' ρ' m hρ' hdR hD hχ c hc a ha
  · push_neg at hV
    refine ⟨0, continuous_const, funext fun x => ?_⟩
    simp [cupL, hV (c x.1), ReciprocityTheory.Def.d1]

end GlobalTheory.HyodoOrth
