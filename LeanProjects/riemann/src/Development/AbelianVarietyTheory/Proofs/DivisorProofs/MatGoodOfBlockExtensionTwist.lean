import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraFurther

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace.FullRankSum

theorem joint_inj {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L] [IsFractionRing O L] {a b c : ℕ}
    (B : Mx O a c) (C : Mx O b c) (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) (x : Fin c → L)
    (hB : (B.map (algebraMap O L)).mulVec x = 0) (hC : (C.map (algebraMap O L)).mulVec x = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6; revert O L h_2 h_3 h_4 h_5 h_6 a b c B C h x hB hC; exact @_root_.GlobalTheory.MulVecZeroDenominator.target)
  | exact @_root_.GlobalTheory.MulVecZeroDenominator.target
  | exact _root_.GlobalTheory.MulVecZeroDenominator.target
  | (apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulVecZeroDenominator.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulVecZeroDenominator.target ..)

theorem exists_equiv {L : Type} [Field L] {n : ℕ} (B : Mx L n (n + 1)) (C : Mx L 1 (n + 1))
    (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) :
    ∃ e : (Fin (n + 1) → L) ≃ₗ[L] (Fin n → L) × (Fin 1 → L), ∀ v, e v = (B.mulVec v, C.mulVec v) := by
  let φ : (Fin (n + 1) → L) →ₗ[L] (Fin n → L) × (Fin 1 → L) := (Matrix.toLin' B).prod (Matrix.toLin' C)
  have hi : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact h v (congrArg Prod.fst hv) (congrArg Prod.snd hv)
  exact ⟨φ.linearEquivOfInjective hi (by simp), fun v => rfl⟩

variable {l : ℕ} [Fact l.Prime] {K LL : FinExt l}

theorem tw_mulVec {a b : ℕ} {r : ↥(GK K) →* GL (Fin b) ↥(OL LL)} {r' : ↥(GK K) →* GL (Fin a) ↥(OL LL)}
    {A : Mx ↥(OL LL) a b} (hA : Tw r r' A) (g : ↥(GK K)) (y : Fin b → ↥LL.1) :
    (A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec (repOf r g y) =
      repOf r' g ((A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec y) := by
  rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
    hA g]

theorem matGood_sum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (ρ : ↥(GK K) →* GL (Fin 1) ↥(OL LL)) (r₂ : ↥(GK K) →* GL (Fin (n + 1)) ↥(OL LL)) (U U' : ZMod f → Multiset ℤ) (B : Mx ↥(OL LL) n (n + 1)) (C : Mx ↥(OL LL) 1 (n + 1)), MatGood P emb r U → MatGood P emb ρ U' → Tw r₂ r B → Tw r₂ ρ C → (∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) → MatGood P emb r₂ (fun i => U i + U' i) := by
  intro l _ P AI T K LL f n emb r ρ r₂ U U' B C hr hρ hB hC hinj
  obtain ⟨_, -, -, -, -, -, hF⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨e, he⟩ := exists_equiv (B.map (algebraMap ↥(OL LL) ↥LL.1)) (C.map (algebraMap ↥(OL LL) ↥LL.1))
    (joint_inj B C hinj)
  have hq : ∀ g v, e (repOf r₂ g v) = (repOf r g (e v).1, repOf ρ g (e v).2) := fun g v => by
    rw [he, he, tw_mulVec hB, tw_mulVec hC]
  obtain ⟨-, hc, hm⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T K LL _ (repOf r₂) _ (repOf r) _ (repOf ρ) e hq
  refine ⟨fun a b => ?_, hc.2 ⟨hr.2.1, hρ.2.1⟩, fun i τ hτ a => ?_⟩
  · have c1 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inl _ _ _) := LinearMap.continuous_on_pi _
    have c2 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inr _ _ _) := LinearMap.continuous_on_pi _
    have d1 : Continuous fun g => repOf r g (e (Pi.single b 1)).1 := (latOf r hr.1).cont _
    have d2 : Continuous fun g => repOf ρ g (e (Pi.single b 1)).2 := (latOf ρ hρ.1).cont _
    have d := (continuous_apply a).comp ((c1.comp d1).add (c2.comp d2))
    refine d.congr fun g => ?_
    have : repOf r₂ g (Pi.single b 1) = e.symm (repOf r g (e (Pi.single b 1)).1, 0) +
        e.symm (0, repOf ρ g (e (Pi.single b 1)).2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, ← hq, e.symm_apply_apply]
    have h2 := congrFun this a
    rw [repOf_apply, Matrix.mulVec_single_one] at h2
    exact h2.symm
  · rw [hm, hr.2.2 i τ hτ a, hρ.2.2 i τ hτ a, Multiset.count_add]
    push_cast
    rfl

end GlobalTheory.WachPlace.FullRankSum

end
