import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawTrivialityOnDenseFibresProductAbelianStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open AdjointOfPairing in

theorem lbIso_cubeLB_of_pairing_adjoint : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫ a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L) := by
  intro hl k _ _ _ P a a' ha ha' H
  have := P.isAb.comm
  have out : ∀ r : P.A ⟶ P.A ⊗ P.A, (∃ t : LB.Gen (LB.LinComb P.L (fun i => r.left ≫ Out.rosatiφ P.A a a' i)
      Out.rosatiε), t.IsGen) → ∃ t : ((LB.LinComb P.L (Out.rosatiφ P.A a a') Out.rosatiε).pull r.left).Gen,
        t.IsGen := fun r ⟨t, ht⟩ => gen_chartPull (chartPullOut P.L _ _ _ _ fun _ => rfl) t ht
  obtain ⟨t, ht⟩ := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian hl.globalFns k P.A P.A (LB.LinComb P.L (Out.rosatiφ P.A a a') Out.rosatiε) P.L
    P.isAb P.isAb P.isLB P.ample
    (DVR.linComb_isLB P.L P.isLB _ _)
    (out _ (exists_gen_of_formEq_zero P.isLB fun U _ h => by
      rw [prod_ros, MonObj.one_comp, _root_.one_mul, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel))
    ((TorsionDense.dense_torsion P hl.irred hl.kerPow).mono (Set.biUnion_subset_biUnion_left
      fun x hx => hx.elim fun n hx => out _ (exists_gen_fibre hl P a a' n (Nat.cast_ne_zero.2 hx.1.ne') x hx.2
        fun y c hy => H n x y c hx.1 hx.2 hy)))
    (out _ (exists_gen_of_formEq_zero P.isLB fun U _ h => by
      rw [prod_ros, MonObj.one_comp, _root_.mul_one, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel))
  obtain ⟨u, hu, -⟩ := exists_gen P.isLB
    (φ' := Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A, snd P.A P.A ≫ a'] I.down).left)
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A ≫ a, snd P.A P.A] I.down).left))
    (ε' := Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => -(-1) ^ (2 - I.down.card)))
    (fun V _ h => by
      have p := prod_ros a a' (fst P.A P.A) (snd P.A P.A) h
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (DVR.prod_neg _ _ p).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2)))
        (K' := ULift.{0} (Finset (Fin 2))) (U := V) _ (NormRos.prod_square (fst P.A P.A) (snd P.A P.A ≫ a') h)
        (DVR.prod_neg _ _ (NormRos.prod_square (fst P.A P.A ≫ a) (snd P.A P.A) h))).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
  exact lbIso_of_gen u hu

end GlobalTheory
