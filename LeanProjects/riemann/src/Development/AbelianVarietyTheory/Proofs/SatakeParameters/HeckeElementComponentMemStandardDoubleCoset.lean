import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitHecke.HeckeComp

variable {D : D7}

theorem mul_mem_intAE {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem smul_mem_latHat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (L : Set (Fin n → E)) (hL : ∀ u : 𝓞 E, ∀ w ∈ L, (u : E) • w ∈ L) {x : Af F ⊗[F] E} {y : Fin n → Af F ⊗[F] E}
    (hx : x ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (hy : y ∈ latHat F E L) : x • y ∈ latHat F E L := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, w, hw, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, (u : E) • w, hL u w hw, ?_⟩
      · rw [map_mul]; exact mul_mem (ha v) (hb v)
      · funext i
        rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_smul]; exact neg_mem h

theorem smul_mem_LamHat (V : HSp D) {x : Af D.host.F ⊗[D.host.F] D.host.E}
    {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ LamHat V) :
    x • y ∈ LamHat V := by
  refine smul_mem_latHat _ (fun u w hw => ?_) hx hy
  have h1 : ∑ i, ((u : D.host.E) • w) i • V.frame i = (u : D.host.E) • ∑ i, w i • V.frame i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_assoc]
  change ∑ i, ((u : D.host.E) • w) i • V.frame i ∈ V.L0
  rw [h1]
  have h2 := V.L0.smul_mem u hw
  rw [← algebraMap_smul D.host.E u] at h2
  exact h2

theorem det_unit {A O K : Type} [CommRing A] [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (π : A →+* K) {n : ℕ} (β : GL (Fin n) K)
    (M : Matrix (Fin n) (Fin n) A) {e u u' w : A} (p : O) (k : ℕ) (he1 : π e = 1) (hp : algebraMap O K p = π w)
    (hu : IsInt O (π u)) (hu' : IsInt O (π u')) (huu : e * u * u' = e) (hdet : e * M.det = e * w ^ k * u) :
    ∃ t : Oˣ, ((β⁻¹).1 * M.map π * β.1).det = algebraMap O K (p ^ k * t) := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hu'
  have hab : a * b = 1 := by
    apply hinj
    have h := congrArg π huu
    rw [map_mul, map_mul, he1, one_mul] at h
    rw [map_mul, ha, hb, h, map_one]
  refine ⟨Units.mkOfMulEqOne a b hab, ?_⟩
  have h := congrArg π hdet
  rw [map_mul, map_mul, map_mul, he1, one_mul, one_mul, map_pow, RingHom.map_det] at h
  rw [det_mul, det_mul, mul_right_comm, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one,
    one_mul, Units.val_mkOfMulEqOne, map_mul, map_pow, hp, ha]
  exact h

theorem fin_mul_mem {e u : AE D} (he : finPart D e ∈ intAE D) (hu : finPart D u ∈ intAE D) :
    finPart D (e * u) ∈ intAE D := by
  have h : finPart D (e * u) = finPart D e * finPart D u := RingHom.map_mul _ e u
  rw [h]
  exact mul_mem_intAE he hu

theorem intM_of_stable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hπ : Function.Surjective π) (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)) (hβ : Frame V e π β)
    (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ LamHat V →
      (fun i => finPart D (e * (M *ᵥ y) i)) ∈ LamHat V) :
    IntM (Ov D v) ((β⁻¹).1 * M.map π * β.1) := by
  intro i j
  choose y hy using fun k => hπ (β.1 k j)
  have h0 : (fun k => π (y k)) = β.1 *ᵥ Pi.single j 1 := by
    funext k
    rw [hy, mulVec_single_one]
    rfl
  have h1 : (fun i => finPart D (e * y i)) ∈ LamHat V := by
    refine (hβ y).2 fun l => ?_
    rw [h0, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, mulVec_single_one]
    exact intM_one l j
  have h2 := (hβ _).1 (hM y h1) i
  have h3 : (fun k => π ((M *ᵥ y) k)) = M.map π *ᵥ (fun k => π (y k)) := by
    funext k
    exact RingHom.map_mulVec π M y k
  rw [h3, h0, mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at h2
  exact h2

theorem fin_mulVec {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (e : A)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) :
    (fun i => φ (e * (M *ᵥ y) i)) = M.map φ *ᵥ (fun i => φ (e * y i)) := by
  funext i
  have h : (fun i => φ (e * y i)) = φ ∘ (e • y) := rfl
  rw [h, ← RingHom.map_mulVec, mulVec_smul]
  rfl

theorem clause_in {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} {e : A} (he : e * e = e)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) :
    (fun i => φ e * (M.map φ *ᵥ (fun i => φ (e * y i))) i) = fun i => φ (e * (M *ᵥ y) i) := by
  funext i
  rw [← fin_mulVec, ← map_mul, ← mul_assoc, he]

theorem clause_out {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} {e : A} (he : e * e = e) (w : A)
    (M N : Matrix (Fin n) (Fin n) A) (hNM : N * M = 1) (y : Fin n → A) (z : Fin n → B)
    (h : (fun a => φ e * (φ w * φ (e * y a))) = fun a => φ e * (M.map φ *ᵥ z) a) :
    (fun i => φ (e * ((w • N) *ᵥ y) i)) = φ e • z := by
  have h1 : (fun i => φ (e * (w • y) i)) = φ e • (M.map φ *ᵥ z) := by
    funext a
    have h2 : φ e * (φ w * φ (e * y a)) = φ (e * (w • y) a) := by
      rw [← map_mul, ← map_mul, Pi.smul_apply, smul_eq_mul]
      congr 1
      linear_combination (w * y a) * he
    rw [← h2]
    exact congrFun h a
  rw [smul_mulVec, ← mulVec_smul, fin_mulVec, h1, mulVec_smul, mulVec_mulVec, ← Matrix.map_mul, hNM,
    Matrix.map_one _ (map_zero φ) (map_one φ), one_mulVec]

set_option maxHeartbeats 1000000 in

theorem hk_of_isHeckeElt : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ (ϖ : D.host.E) (p : Ov D v) (k : ℕ) (α : GA D V), algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D ϖ) → IsHeckeElt V e ϖ k α → Hk (Ov D v) p k (rho V π β α) := by
  intro D e v π he hc V β hβ ϖ p k α hp hα
  obtain ⟨-, -, hin, hout, u, u', hu, hu', huu, hdet⟩ := hα
  obtain ⟨hs, hker, -, hint⟩ := hc
  have hee : e * e = e := he.1
  have hei : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have he1 : π e = 1 := by
    have h := (hker (1 - e)).2 (by rw [mul_sub, mul_one, hee, sub_self])
    rw [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at h
    exact h.symm
  have hinv : Formalism.L2.Theta.mt V α⁻¹ * Formalism.L2.Theta.mt V α = 1 := by
    change (matHom V α⁻¹).1 * (matHom V α).1 = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [rho_val]
    refine intM_of_stable hs V β hβ _ fun y hy => ?_
    rw [← clause_in (finPart D) hee]
    exact hin _ hy
  · have h1 : algebraMap (Ov D v) (Fv D.host.F v) p • ((rho V π β α)⁻¹).1 =
        (β⁻¹).1 * (incA D ϖ • Formalism.L2.Theta.mt V α⁻¹).map π * β.1 := by
      have h2 : (incA D ϖ • Formalism.L2.Theta.mt V α⁻¹).map π =
          π (incA D ϖ) • (Formalism.L2.Theta.mt V α⁻¹).map π := by
        exact Matrix.ext fun i j => RingHom.map_mul π _ _
      rw [← map_inv, rho_val, h2, hp, Matrix.mul_smul, Matrix.smul_mul]
    rw [h1]
    refine intM_of_stable hs V β hβ _ fun y hy => ?_
    obtain ⟨z, hz, h⟩ := hout _ hy
    rw [clause_out (finPart D) hee (incA D ϖ) _ _ hinv y z h]
    exact smul_mem_LamHat V hei hz
  · rw [rho_val]
    have hinj : Function.Injective (algebraMap (Ov D v) (Fv D.host.F v)) := Subtype.val_injective
    have h1 := (hint u).1 (fin_mul_mem hei hu)
    have h2 := (hint u').1 (fin_mul_mem hei hu')
    exact det_unit hinj π β (Formalism.L2.Theta.mt V α) p k he1 hp h1 h2 huu hdet

end GlobalTheory.SplitHecke.HeckeComp

end
