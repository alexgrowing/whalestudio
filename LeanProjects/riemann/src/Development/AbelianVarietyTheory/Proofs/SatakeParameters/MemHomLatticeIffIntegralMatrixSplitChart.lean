import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitHomLattice

open GlobalTheory.LatticeStable GlobalTheory.SplitScalar

variable {D : D7}

theorem ideal_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

theorem finPart_mul_incA (w : AE D) (x : D.host.E) :
    finPart D (w * incA D x) = finPart D w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) := by
  rw [RingHom.map_mul]; rfl

theorem mul_int_mem {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) (o : 𝓞 D.host.E) :
    w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) ∈ intAE D := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o', rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β, hβ, o' * o, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem mul_lat_mem (V : HSp D) {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D)
    {y : Fin V.rank → D.host.E} (hy : y ∈ L0c D V) :
    (fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] y i)) ∈ LamHat V := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β, hβ, fun i => (o : D.host.E) * y i, ?_, ?_⟩
    · have h : ∑ i, y i • V.frame i ∈ V.L0 := hy
      have h2 := V.L0.smul_mem o h
      show ∑ i, ((o : D.host.E) * y i) • V.frame i ∈ V.L0
      rw [Finset.smul_sum] at h2
      simp only [mul_smul]
      convert h2 using 2 with i
      exact algebraMap_smul D.host.E o _
    · funext i
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => simp only [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => simp only [add_mul]; exact add_mem hx hy
  | neg x _ hx => simp only [neg_mul]; exact neg_mem hx

theorem finPart_liftFin (x : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (liftFin D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | tmul a m => rfl
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]

theorem finPart_cA (x : AE D) : finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | tmul a m => rfl
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]

def rk (S T : HSp D) (a : D.host.E) (s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E) : WO S T :=
  Matrix.of fun i j => liftFin D (((1 : Af D.host.F) ⊗ₜ[D.host.F] a) * t i *
    ∑ k, sigR (Af D.host.F) D.sp.cm.sig (s k) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] S.gram k j))

def rkHom (S T : HSp D) (a : D.host.E) : (Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+
    (Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ WO S T :=
  AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun t => rk S T a s t) fun t t' => by
      ext i j
      simp only [rk, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, LinearMap.map_add, add_mul, mul_add])
    (fun s s' => AddMonoidHom.ext fun t => by
      ext i j
      simp only [rk, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, LinearMap.map_add, RingHom.map_add, add_mul,
        mul_add, Finset.sum_add_distrib, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply])

theorem rk_mem (S T : HSp D) {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hs : s ∈ LamHat S)
    {t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E} (ht : t ∈ LamHat T) :
    rk S T a s t ∈ latO S T (L0c D S) (L0c D T) fun _ => True := by
  change rkHom S T a s t ∈ _
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun _ h => absurd trivial h, a, ha, x, hx, y, hy, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · ext i j
        change liftFin D (_ * _ * ∑ k, (α ⊗ₜ[D.host.F] star (x k)) * _) = _
        rw [Matrix.of_apply, ← liftFin_tmul]
        congr 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [← TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

section Chart

variable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem pi_idem (he : IsSplitIdem D e) (hπ : Chart e v π) : π e = 1 := by
  have h : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1, sub_self])
  rw [RingHom.map_sub, RingHom.map_one] at h
  exact (sub_eq_zero.1 h).symm

theorem idem_int {e : AE D} (he : IsSplitIdem D e) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])

theorem pi_eq_of_finPart (he : IsSplitIdem D e) (hπ : Chart e v π) {a b : AE D} (h : finPart D a = finPart D b) :
    π a = π b := by
  rw [← sub_eq_zero, ← RingHom.map_sub, hπ.2.1]
  exact adele_ext (by rw [RingHom.map_mul, infPart_splitIdem he, zero_mul, RingHom.map_zero])
    (by rw [RingHom.map_mul, RingHom.map_sub, h, sub_self, mul_zero, RingHom.map_zero])

theorem pi_rk (he : IsSplitIdem D e) (hπ : Chart e v π) (S T : HSp D) (a : D.host.E) (s : Fin S.rank → AE D)
    (t : Fin T.rank → AE D) (i : Fin T.rank) (j : Fin S.rank) :
    π (rk S T a (fun k => finPart D (cA D e * s k)) (fun k => finPart D (e * t k)) i j) =
      π (incA D a) * π (t i) * ∑ k, π (cA D (s k)) * π (incA D (S.gram k j)) := by
  have h : π (rk S T a (fun k => finPart D (cA D e * s k)) (fun k => finPart D (e * t k)) i j) =
      π (incA D a * (e * t i) * ∑ k, cA D (cA D e * s k) * incA D (S.gram k j)) := by
    refine pi_eq_of_finPart he hπ ?_
    rw [rk, Matrix.of_apply, finPart_liftFin]
    simp only [← finPart_cA]
    rw [RingHom.map_mul (finPart D) (_ * _), RingHom.map_mul (finPart D) (incA D a), map_sum (finPart D)]
    simp only [finPart_mul_incA]
    rfl
  rw [h]
  simp only [RingHom.map_mul, map_sum π, GlobalTheory.DualPairCheck.cA_cA, pi_idem he hπ, one_mul]

theorem exists_generator (he : IsSplitIdem D e) (hπ : Chart e v π) :
    ∃ a₀ ∈ D.host.AA, π (incA D a₀) ≠ 0 ∧ ∀ a ∈ D.host.AA, IsInt (Ov D v) ((π (incA D a₀))⁻¹ * π (incA D a)) := by
  have hfg : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (ideal_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    exact ideal_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 hs.symm)
  obtain ⟨a₀, ha₀, hmax⟩ := s.exists_max_image (fun a => Valued.v (π (incA D a))) hne
  have hle : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E),
      Valued.v (π (incA D a)) ≤ Valued.v (π (incA D a₀)) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hmax a ha
    | zero => simp only [map_zero, zero_le]
    | add x y _ _ hx hy => rw [RingHom.map_add, RingHom.map_add]; exact Valuation.map_add_le _ hx hy
    | smul o x _ hx =>
      have ho : Valued.v (π (incA D (o : D.host.E))) ≤ 1 :=
        isInt_Ov.1 ((hπ.2.2.2 _).1 (by rw [finPart_mul_incA]; exact mul_int_mem (idem_int he) o))
      rw [show o • x = (o : D.host.E) * x from rfl, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul]
      exact (mul_le_of_le_one_left' ho).trans hx
  have h0 : π (incA D a₀) ≠ 0 := by
    intro h
    apply ideal_ne_zero D
    rw [FractionalIdeal.eq_zero_iff]
    intro a ha
    have := hle a ha
    rw [h, map_zero, le_zero_iff, map_eq_zero] at this
    exact (map_eq_zero (π.comp (incA D))).1 this
  refine ⟨a₀, ?_, h0, fun a ha => isInt_Ov.2 ?_⟩
  · show a₀ ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    rw [← hs]; exact Submodule.subset_span ha₀
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]
    exact hle a ha

end Chart

theorem mem_latO_iff_intM : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (S T : HSp D) (βS : GL (Fin S.rank) (Fv D.host.F v)) (βT : GL (Fin T.rank) (Fv D.host.F v)), Frame S e π βS → Frame T e π βT → ∃ c : Fv D.host.F v, c ≠ 0 ∧ ∀ u : WO S T, IsHalf e u → (u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔ IntM (Ov D v) (c • ((βT⁻¹).1 * Matrix.map u π * βS.1))) := by
  intro D e v π he hπ S T βS βT hS hT
  obtain ⟨a₀, ha₀, h0, hgen⟩ := exists_generator he hπ
  refine ⟨(π (incA D a₀))⁻¹, inv_ne_zero h0, fun u hu => ⟨fun h => ?_, fun h => ?_⟩⟩
  · clear hu
    induction h using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      intro i j
      have h1 := (hT fun k => incA D (t k)).1 (by
        simp only [finPart_mul_incA]; exact mul_lat_mem T (idem_int he) ht) i
      have h2 := (GlobalTheory.SplitDualLat.conj_mem_lamHat_iff e v π he hπ S βS hS fun k => incA D (s k)).1 (by
        simp only [finPart_mul_incA]; exact mul_lat_mem S (idem_int (isSplitIdem_conj he)) hs) j
      have h3 := hgen a ha
      have h4 : IsInt (Ov D v) (evalV D.host.F v α) := isInt_Ov.2 (hα v)
      have h5 := mul_mem (mul_mem (mul_mem (isInt_iff.1 h4) (isInt_iff.1 h3)) (isInt_iff.1 h1)) (isInt_iff.1 h2)
      have hm : ∀ m : D.host.E, π (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = evalV D.host.F v α * π (incA D m) := by
        intro m
        have : (pairA D.host.F 0 α ⊗ₜ[D.host.F] m : AE D) =
            algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D m := by
          change _ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] m)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this, RingHom.map_mul, hπ.2.2.1]
        rfl
      rw [isInt_iff]
      convert h5 using 1
      rw [← Matrix.vecMul_vecMul]
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, hm,
        Matrix.mulVec, Matrix.vecMul, dotProduct, RingHom.map_mul, map_sum, GlobalTheory.DualPairCheck.cA_incA]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
      ring
    | zero =>
      rw [Matrix.map_zero _ π.map_zero, Matrix.mul_zero, Matrix.zero_mul, smul_zero]
      exact fun i j => ⟨0, map_zero _⟩
    | add x y _ _ hx hy =>
      rw [Matrix.map_add _ π.map_add, Matrix.mul_add, Matrix.add_mul, smul_add]
      exact hx.add hy
    | neg x _ hx =>
      rw [Matrix.map_neg _ π.map_neg, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
      exact fun i j => isInt_iff.2 (neg_mem (isInt_iff.1 (hx i j)))
  · set G : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := S.gram.map fun a => π (incA D a) with hG
    have hGu : IsUnit G.det := by
      have := (GlobalTheory.LatVac.gram_det_isUnit S).map (π.comp (incA D))
      rwa [RingHom.map_det] at this
    choose σ hσ using hπ.1
    set Y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := (π (incA D a₀))⁻¹ • (Matrix.map u π * βS.1) with hY
    set Z : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := (βS⁻¹).1 * G⁻¹ with hZ
    have hZ1 : Z * (G * βS.1) = 1 := by
      rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hGu, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    have hs : ∀ j, (fun k => finPart D (cA D e * cA D (σ (Z j k)))) ∈ LamHat S := by
      intro j
      refine (GlobalTheory.SplitDualLat.conj_mem_lamHat_iff e v π he hπ S βS hS fun k => cA D (σ (Z j k))).2 fun l => ?_
      simp only [GlobalTheory.DualPairCheck.cA_cA, hσ]
      have : ((fun k => Z j k) ᵥ* (G * βS.1)) l = (Z * (G * βS.1)) j l := rfl
      rw [this, hZ1]
      exact intM_one j l
    have ht : ∀ j, (fun k => finPart D (e * σ (Y k j))) ∈ LamHat T := by
      intro j
      refine (hT fun k => σ (Y k j)).2 fun i => ?_
      simp only [hσ]
      have : ((βT⁻¹).1 *ᵥ fun k => Y k j) i = ((βT⁻¹).1 * Y) i j := rfl
      rw [this, hY, Matrix.mul_smul, ← Matrix.mul_assoc]
      exact h i j
    have hU := smul_mem_latO D S T _ _ _ e (idem_int he) _
      (sum_mem fun j (_ : j ∈ Finset.univ) => rk_mem S T ha₀ (hs j) (ht j))
    convert hU using 1
    ext i l
    rw [Matrix.smul_apply, smul_eq_mul, ← hu i l, ← sub_eq_zero, ← mul_sub, ← hπ.2.1, RingHom.map_sub, sub_eq_zero,
      Matrix.sum_apply, map_sum]
    have hsum : ∀ j, π (rk S T a₀ (fun k => finPart D (cA D e * cA D (σ (Z j k))))
        (fun k => finPart D (e * σ (Y k j))) i l) = π (incA D a₀) * (Y i j * (Z * G) j l) := by
      intro j
      rw [pi_rk he hπ S T a₀ (fun k => cA D (σ (Z j k))) (fun k => σ (Y k j)) i l, mul_assoc]
      simp only [GlobalTheory.DualPairCheck.cA_cA, hσ]
      rfl
    simp only [hsum]
    rw [← Finset.mul_sum, ← Matrix.mul_apply, hZ, Matrix.nonsing_inv_mul_cancel_right _ _ hGu, hY, Matrix.smul_mul,
      Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul,
      mul_inv_cancel_left₀ h0, Matrix.map_apply]

end GlobalTheory.SplitHomLattice

end
