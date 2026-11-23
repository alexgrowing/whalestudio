import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelIdealEqKernelRelativeFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFrobeniusKernelIdealOfZeroDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulPStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobRigKer

variable {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

variable (O A) in

def evalZeroTwo : A ⊗[O] A →ₗ[O] O :=
  (TensorProduct.lid O O).toLinearMap ∘ₗ TensorProduct.map (counit (R := O)) (counit (R := O))

@[simp] theorem evalZeroTwo_tmul (a b : A) :
    evalZeroTwo O A (a ⊗ₜ b) = counit (R := O) a * counit (R := O) b := by
  simp [evalZeroTwo]

theorem evalZeroTwo_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    evalZeroTwo O B (pullbackTwo f c) = evalZeroTwo O A c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo, evalZeroTwo_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem evalZeroTwo_comul (b : A) : evalZeroTwo O A (comul b) = counit (R := O) b := by
  have key : TensorProduct.map (counit (R := O)) (counit (R := O)) (comul (R := O) b) =
      LinearMap.lTensor O (counit (R := O)) (LinearMap.rTensor A (counit (R := O)) (comul b)) := by
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
  show TensorProduct.lid O O (TensorProduct.map (counit (R := O)) (counit (R := O)) (comul b)) = _
  rw [key, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul, TensorProduct.lid_tmul, one_smul]

theorem evalZeroTwo_cobOne (b : A) : evalZeroTwo O A (cobOne O A b) = - counit (R := O) b := by
  rw [cobOne_apply, map_sub, map_sub, evalZeroTwo_comul, evalZeroTwo_tmul, evalZeroTwo_tmul,
    Bialgebra.counit_one]
  ring

theorem mk_kerIdeal_apply (f : A →ₐc[O] B) (a : A) :
    Ideal.Quotient.mkₐ O (kerIdeal f) (f a) = counit (R := O) a • 1 := by
  have hmem : a - algebraMap O A (counit (R := O) a) ∈ augIdeal O A := by
    simp [RingHom.mem_ker]
  have himg := Ideal.mem_map_of_mem (f : A →ₐ[O] B) hmem
  have e : (f : A →ₐ[O] B) (algebraMap O A (counit (R := O) a)) = algebraMap O B (counit (R := O) a) :=
    AlgHom.commutes _ _
  rw [map_sub, e] at himg
  rw [Algebra.smul_def, mul_one, ← AlgHom.commutes (Ideal.Quotient.mkₐ O (kerIdeal f)),
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
  exact himg

theorem map_mk_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (pullbackTwo f c) = evalZeroTwo O A c • 1 := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [pullbackTwo, TensorProduct.map_tmul, BialgHom.coe_toLinearMap,
      Algebra.TensorProduct.map_tmul, mk_kerIdeal_apply, evalZeroTwo_tmul,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    rw [mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, add_smul]

theorem map_mk_cobOne_eq_zero (f : A →ₐc[O] B) {c : A ⊗[O] A} {b : B}
    (hb : counit (R := O) b = 0) (hc : cobOne O B b = pullbackTwo f c) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (cobOne O B b) = 0 := by
  rw [hc, map_mk_pullTwo, ← evalZeroTwo_pullTwo f c, ← hc, evalZeroTwo_cobOne, hb, neg_zero,
    zero_smul]

def oneFun {p : ℕ} (G : PDivGroup p O) : G.funs := ⟨fun _ => 1, fun _ => map_one _⟩

theorem funsMap_oneFun {p : ℕ} {G H : PDivGroup p O} (f : G ⟶ H) :
    funsMap f (oneFun H) = oneFun G :=
  Subtype.ext (funext fun n => map_one (f.app n))

theorem dUnit_one : dUnit O (1 : A) = 0 := by
  simp [dUnit]

end GlobalTheory.PDiv.FrobRigKer

namespace GlobalTheory.PDivGroup

open GlobalTheory.PDiv.FrobRigKer

theorem ker_rigExtMap_relFrob_le_range_rigOfOmega (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) :
    LinearMap.ker (rigExtMap (relFrob h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 h
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨⟨c, w⟩, rfl⟩ : ∃ z, (frobTwist h G).rigMk z = x := Submodule.mkQ_surjective _ x
  rw [rigExtMap_mk] at hx
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
  have hB1 : G.cob B = cocyclesMap (relFrob h G) c := congrArg Prod.fst hB
  have hB2 : G.dFun B = G.omegaMap _ (relFrob h G) w := congrArg Prod.snd hB
  set t : K := counit (R := K) (B.1 1) with ht
  set B₁ : G.funs := B - t • oneFun G with hB₁
  set c₁ : (frobTwist h G).cocycles := c - t • (frobTwist h G).cob (oneFun (frobTwist h G))
    with hc₁def
  have hc₁ : G.cob B₁ = cocyclesMap (relFrob h G) c₁ := by
    simp only [hB₁, hc₁def, map_sub, map_smul, hB1, cocyclesMap_cob, funsMap_oneFun]
  have hb0 : counit (R := K) (B₁.1 1) = 0 := by
    show counit (R := K) (B.1 1 - t • (1 : G.A 1)) = 0
    rw [map_sub, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one, ht, sub_self]
  have hbd : dUnit K (B₁.1 1) = 0 := by
    have e1 : G.dFun B = 0 := by rw [hB2, omegaMap_relFrob, LinearMap.zero_apply]
    have e2 : G.dFun (oneFun G) = 0 := Subtype.ext (funext fun n => dUnit_one)
    have e : G.dFun B₁ = 0 := by rw [hB₁, map_sub, map_smul, e1, e2, smul_zero, sub_zero]
    exact congrArg (fun z : G.omega => z.1 1) e
  have hcob : cobOne K (G.A 1) (B₁.1 1) = pullbackTwo ((relFrob h G).app 1) (c₁.1 1) :=
    congrArg (fun z : G.cocycles => z.1 1) hc₁
  have hker := GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G 1
  have hmem : B₁.1 1 ∈ frobKerIdeal p K (G.A 1) := by
    refine GlobalTheory.T.mem_frobeniusKernelIdeal_of_zero_differential p K (G.A 1) _ hb0 hbd ?_
    rw [hker]
    exact map_mk_cobOne_eq_zero ((relFrob h G).app 1) hb0 hcob
  rw [hker] at hmem
  have hV : (verschiebung h G).app 1 (B₁.1 1) = 0 :=
    GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) _ hmem
  have hcomp : cocyclesMap (verschiebung h G) (cocyclesMap (relFrob h G) c₁) =
      cocyclesMap (verschiebung h G ≫ relFrob h G) c₁ :=
    Subtype.ext (funext fun n => (pullTwo_comp _ _ _).symm)
  obtain ⟨B', hB'⟩ : c₁ ∈ LinearMap.range (frobTwist h G).cob := by
    refine GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP (frobTwist h G) c₁ (funsMap (verschiebung h G) B₁) ?_ hV
    rw [← cocyclesMap_cob, hc₁, hcomp, verschiebung_comp_relFrob]
  set B₀ : (frobTwist h G).funs := B' + t • oneFun (frobTwist h G) with hB₀
  have hc0 : (frobTwist h G).cob B₀ = c := by
    rw [hB₀, map_add, map_smul, hB', hc₁def, sub_add_cancel]
  refine ⟨w - (frobTwist h G).dFun B₀, ?_⟩
  show Submodule.Quotient.mk ((0 : (frobTwist h G).cocycles), w - (frobTwist h G).dFun B₀) =
    Submodule.Quotient.mk (c, w)
  refine ((Submodule.Quotient.eq
    (LinearMap.range ((frobTwist h G).cob.prod (frobTwist h G).dFun))).2
    (LinearMap.mem_range.2 ⟨B₀, Prod.ext ?_ ?_⟩)).symm
  · show (frobTwist h G).cob B₀ = c - 0
    rw [sub_zero]
    exact hc0
  · show (frobTwist h G).dFun B₀ = w - (w - (frobTwist h G).dFun B₀)
    exact (sub_sub_cancel w _).symm

end GlobalTheory.PDivGroup
