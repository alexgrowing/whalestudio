import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulSymplecticPairingCharacterTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatMulInvIdealLatticeMemIntegralStatement

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.MovedTrChar
open GlobalTheory.BotClassDict (finQ finStd)
open scoped TensorProduct

def secF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

def secI (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem decomp {D : D7} (a : AE D) : a = secI D (infPart D a) + secF D (finPart D a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, LinearMap.map_zero, LinearMap.map_zero, add_zero]
  | add a b ha hb =>
    rw [RingHom.map_add, RingHom.map_add, LinearMap.map_add, LinearMap.map_add]
    conv_lhs => rw [ha, hb]
    abel
  | tmul c e =>
    have hc : c = LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F) (fstA D.host.F c) +
        LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) (sndA D.host.F c) := by
      refine Prod.ext ?_ ?_
      · exact (add_zero _).symm
      · exact (zero_add _).symm
    conv_lhs => rw [hc]
    erw [TensorProduct.add_tmul]
    rfl

theorem infPart_secF {D : D7} (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (secF D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [LinearMap.map_add, RingHom.map_add, ha, hb, add_zero]
  | tmul c e =>
    show fstA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) ⊗ₜ[D.host.F] e = 0
    have : fstA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) = 0 := rfl
    rw [this, TensorProduct.zero_tmul]

theorem finPart_secF {D : D7} (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (secF D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [LinearMap.map_add, RingHom.map_add, ha, hb]
  | tmul c e =>
    show sndA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) ⊗ₜ[D.host.F] e = c ⊗ₜ[D.host.F] e
    have : sndA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) = c := rfl
    rw [this]

theorem finQ_eq {D : D7} (a : AE D) : finQ D a = (GlobalTheory.BotFormula.toAfE D).symm (finPart D a) := rfl

theorem recon_ex {D : D7} (q : Formalism.MainNotions.StandardLatticesGL3.AE D) : ∃ a : AE D, infPart D a = 0 ∧ finQ D a = q :=
  ⟨secF D (GlobalTheory.BotFormula.toAfE D q), infPart_secF _, by rw [finQ_eq, finPart_secF, RingEquiv.symm_apply_apply]⟩

theorem recon_uniq {D : D7} (a b : AE D) (h1 : infPart D a = infPart D b) (h2 : finQ D a = finQ D b) : a = b := by
  have h3 : finPart D a = finPart D b := by
    rw [finQ_eq, finQ_eq] at h2
    exact (GlobalTheory.BotFormula.toAfE D).symm.injective h2
  rw [decomp a, decomp b, h1, h3]

end GlobalTheory.MovedTrChar

namespace GlobalTheory.MovedTrChar
open GlobalTheory.BotClassDict (finQ finStd)
open scoped TensorProduct

theorem finPt_parts {D : D7} (S T : HSp D) (r : D.host.E) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    infPart D (finPt (S := S) (T := T) rfl rfl r z i j) = 0 ∧
      finQ D (finPt (S := S) (T := T) rfl rfl r z i j) = -(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * Formalism.MainNotions.StandardLatticesGL3.inc D (z i j)) := by
  have e0 : finPt (S := S) (T := T) rfl rfl r z i j = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * z i j)) := rfl
  rw [e0]
  constructor
  · show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (-(r⁻¹ * z i j)) = 0
    rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl]
    erw [TensorProduct.zero_tmul]
  · have e1 : finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * z i j))) = finPart D (incA D (-(r⁻¹ * z i j))) := rfl
    rw [finQ_eq, e1, ← finQ_eq]
    erw [GlobalTheory.BotClassDict.finQ_inclR]
    rw [RingHom.map_neg, RingHom.map_mul]

theorem uComp {D : D7} (S T : HSp D) (hGS : HSpace.gram S = 1) (hGT : HSpace.gram T = 1)
    (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T)
    (hg : IsFinPt S g x) (hh : IsFinPt T h y) (w : WO S T) (hw : ∀ i j, infPart D (w i j) = 0) (i : Fin T.rank) (j : Fin S.rank) :
    infPart D (actO S T g h w i j) = 0 ∧
      finQ D (actO S T g h w i j) =
        (((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * w.map (finQ D) *
          (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j := by
  have hy : finStd T hGT h = y := GlobalTheory.BotClassDict.finStd_of_isFinPt T hGT hh
  have hx : finStd S hGS g⁻¹ = x⁻¹ := by rw [map_inv, GlobalTheory.BotClassDict.finStd_of_isFinPt S hGS hg]
  have eh : (Formalism.L2.Theta.mt T h).map (finQ D) = ((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
    ext k l
    rw [Matrix.map_apply, ← hy, GlobalTheory.BotClassDict.finStd_apply]
    rfl
  have eg : (Formalism.L2.Theta.mt S g⁻¹).map (finQ D) =
      (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
    ext k l
    rw [Matrix.map_apply]
    have := GlobalTheory.BotClassDict.finStd_apply S hGS g⁻¹ k l
    rw [hx] at this
    exact this.symm
  have key : ∀ {R : Type} [Ring R] (f : AE D →+* R), (actO S T g h w).map f =
      (Formalism.L2.Theta.mt T h).map f * w.map f * (Formalism.L2.Theta.mt S g⁻¹).map f := by
    intro R _ f
    simp only [actO, Matrix.map_mul]
  constructor
  · have hw0 : w.map (infPart D) = 0 := by ext k l; exact hw k l
    have := congrFun (congrFun (key (infPart D)) i) j
    rw [Matrix.map_apply, hw0, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this
  · have := congrFun (congrFun (key (finQ D)) i) j
    rw [Matrix.map_apply, eh, eg] at this
    exact this

end GlobalTheory.MovedTrChar

namespace GlobalTheory.MovedTrChar
open GlobalTheory.BotClassDict (finQ finStd)

theorem symplOH_neg_self {D : D7} (S T : HSp D) (u : WO S T) : symplOH S T (-u) u = 0 := by
  have h0 := Formalism.IndefR.Fin.symplOH_add_left S T u (-u) u
  rw [add_neg_cancel, GlobalTheory.FinTranslate.symplOH_self, zero_add, GlobalTheory.FinTranslate.symplOH_zero_left] at h0
  exact h0.symm

theorem ent_smul {D : D7} {m n : ℕ} (Y : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (Z : Matrix (Fin m) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D))
    (X : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (c : Formalism.MainNotions.StandardLatticesGL3.AE D) (i : Fin m) (j : Fin n) :
    (Y * (c • Z) * X) i j = c * (Y * Z * X) i j := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

set_option maxHeartbeats 1000000 in

theorem psi_sympl_moved_eq_one : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    ψ (symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
  intro D ψ θ S T a d hS hT cc δ r hset x y g h hg hh z
  subst hS; subst hT
  obtain ⟨A0, hA0⟩ : ∃ A0, A0 = actO S T g h (finPt rfl rfl r z) := ⟨_, rfl⟩
  obtain ⟨N, hN, hC⟩ := GlobalTheory.T.exists_nsmul_symplecticPairing_character_trivial ψ hset.std.1.1 hset.std.1.2.1 S T A0
  obtain ⟨M, hM, hMint⟩ := GlobalTheory.T.exists_pos_nat_mul_inv_idealLattice_mem_integral cc r
  refine ⟨N * M, by positivity, fun z' hz' => ?_⟩
  choose t ht hte using hz'
  obtain ⟨u, hu⟩ : ∃ u : WO S T, u = A0 - finPt rfl rfl r z' := ⟨_, rfl⟩
  choose v hv1 hv2 using fun i j => recon_ex (D := D) ((M : Formalism.MainNotions.StandardLatticesGL3.AE D) * (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * t i j))
  have hNv : ∀ i j, (N • Matrix.of v : WO S T) i j = (N : AE D) * v i j := fun i j => by
    rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
  have hmap : (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) = (-(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹)) • z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) := by
    ext i j; rw [Matrix.map_apply, (finPt_parts S T r z i j).2, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, neg_mul]
  have huv : u = N • (Matrix.of v) := by
    ext i j
    have e1 := (uComp S T hset.gS hset.gT x y g h hg hh _ (fun i j => (finPt_parts S T r z i j).1) i j)
    have e2 := finPt_parts S T r z' i j
    apply recon_uniq
    · rw [hNv, map_mul, hv1, mul_zero, hu, Matrix.sub_apply, map_sub, hA0, e1.1, e2.1, sub_zero]
    · rw [hNv, map_mul, hv2]
      rw [hu, Matrix.sub_apply, map_sub]
      rw [hA0, e1.2, e2.2]
      rw [hmap]
      rw [ent_smul]
      rw [map_natCast]
      have h3 := hte i j
      rw [Matrix.sub_apply, Matrix.map_apply] at h3
      push_cast at h3 ⊢
      linear_combination (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹) * h3
  have hself : symplOH S T (-u) u = 0 := symplOH_neg_self S T u
  have hsum : finPt rfl rfl r z' + u = A0 := by rw [hu]; abel
  have geq : actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z' = u := by subst hA0; exact hu.symm
  have h1 := Formalism.IndefR.Fin.symplOH_add_left S T (finPt rfl rfl r z') u u
  rw [hsum, GlobalTheory.FinTranslate.symplOH_self, add_zero] at h1
  rw [geq, ← h1, huv]
  exact hC _ (fun i j => hv1 i j) (fun i j => by rw [Matrix.of_apply, hv2]; exact hMint _ (ht i j))

end GlobalTheory.MovedTrChar
