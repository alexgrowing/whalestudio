import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUltrametricDistFinExt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK
open scoped Formalism.Per

namespace GlobalTheory.BKReal

section Glue

variable {O B R : Type} [CommRing O] [CommRing B] [CommRing R] [Algebra O B] [Algebra O R]
  {a : ℕ} [NeZero a] (c : (ZMod a → O) →ₐ[O] R) (f : B →ₐ[O] R)

def idem (τ : ZMod a) : R := c (Pi.single τ 1)

theorem idem_mul_self (τ : ZMod a) : idem c τ * idem c τ = idem c τ := by
  rw [idem, ← map_mul, ← Pi.single_mul, one_mul]

theorem idem_mul_of_ne {τ σ : ZMod a} (h : τ ≠ σ) : idem c τ * idem c σ = 0 := by
  rw [idem, idem, ← map_mul, ← map_zero c]
  congr 1
  ext ρ
  by_cases h1 : ρ = τ
  · simp [h1, h]
  · simp [h1]

theorem sum_idem : ∑ τ, idem c τ = 1 := by
  simp only [idem]
  rw [← map_sum, Finset.univ_sum_single (fun _ : ZMod a => (1 : O))]
  exact map_one c

theorem idem_mul_sum (x : ZMod a → R) (τ : ZMod a) : idem c τ * ∑ σ, idem c σ * x σ = idem c τ * x τ := by
  rw [Finset.mul_sum, Finset.sum_eq_single τ (fun σ _ h => by
    rw [← mul_assoc, idem_mul_of_ne c h.symm, zero_mul]) (by simp), ← mul_assoc, idem_mul_self]

theorem eq_sum_idem (x : ZMod a → O) : c x = ∑ τ, idem c τ * algebraMap O R (x τ) := by
  conv_lhs => rw [← Finset.univ_sum_single x, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_comm, ← Algebra.smul_def, idem, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

def glue : (ZMod a → B) →ₐ[O] R where
  toFun x := ∑ τ, idem c τ * f (x τ)
  map_one' := by simp [sum_idem]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_mul' x y := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_right_comm, idem_mul_sum, Pi.mul_apply, map_mul]
    ring
  commutes' o := by
    simp only [Pi.algebraMap_apply, AlgHom.commutes]
    rw [← Finset.sum_mul, sum_idem, one_mul]

theorem glue_apply (x : ZMod a → B) : glue c f x = ∑ τ, idem c τ * f (x τ) := rfl

theorem glue_const (b : B) : glue c f (fun _ => b) = f b := by
  rw [glue_apply, ← Finset.sum_mul, sum_idem, one_mul]

theorem idem_mul_glue (x : ZMod a → B) (τ : ZMod a) : idem c τ * glue c f x = idem c τ * f (x τ) :=
  idem_mul_sum c _ τ

variable {c f} in

theorem map_glue {B' R' : Type} [CommRing B'] [CommRing R'] [Algebra O B'] [Algebra O R']
    {c' : (ZMod a → O) →ₐ[O] R'} {f' : B' →ₐ[O] R'} (s : R →+* R') (k : ZMod a)
    (hs : ∀ τ, s (idem c τ) = idem c' (τ + k)) {x : ZMod a → B} {y : ZMod a → B'}
    (h : ∀ τ, s (f (x (τ - k))) = f' (y τ)) : s (glue c f x) = glue c' f' y := by
  rw [glue_apply, glue_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight k) _ _ fun τ => ?_
  rw [map_mul, hs, Equiv.coe_addRight, ← h, add_sub_cancel_right]

theorem tensor_hom_ext {Z W J : Type} [CommRing Z] [CommRing W] [Algebra Z O] [Algebra Z W] {v : J → W}
    (hv : Submodule.span Z (Set.range v) = ⊤) (f g : O ⊗[Z] W →ₐ[O] R)
    (h : ∀ i, f (1 ⊗ₜ v i) = g (1 ⊗ₜ v i)) : f = g := by
  have h1 : ∀ w, f (1 ⊗ₜ w) = g (1 ⊗ₜ w) := fun w => by
    have hw : w ∈ Submodule.span Z (Set.range v) := hv ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
    | zero => simp
    | add x y _ _ hx hy => simp only [tmul_add, map_add, hx, hy]
    | smul c x _ hx => rw [tmul_smul, ← algebraMap_smul O c, map_smul, map_smul, hx]
  ext1 x
  induction x with
  | zero => simp
  | tmul o w =>
    have : o ⊗ₜ[Z] w = o • ((1 : O) ⊗ₜ[Z] w) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, h1]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bijective_lift {Z W J I : Type} [CommRing Z] [CommRing W] [Algebra Z O] [Algebra Z W] [Fintype I]
    (emb : I → W →ₐ[Z] O) {v : J → W} (hv : Submodule.span Z (Set.range v) = ⊤) (t : W)
    (ht : ∀ j, v j = 0 ∨ ∃ k : ℕ, v j = t ^ k) (hu : ∀ i j, i ≠ j → IsUnit (emb i t - emb j t))
    (f : Polynomial Z) (hfm : f.Monic) (hfd : f.natDegree ≤ Fintype.card I) (h0 : Polynomial.aeval t f = 0)
    (hroot : ∀ i, Polynomial.aeval (emb i t) f = 0) :
    Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId O (I → O)) (AlgHom.pi emb)
      fun _ _ => Commute.all _ _) := by
  rcases subsingleton_or_nontrivial O with hO | hO
  · have := Module.subsingleton O (O ⊗[Z] W)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  set Φ := Algebra.TensorProduct.lift (Algebra.ofId O (I → O)) (AlgHom.pi emb) fun _ _ => Commute.all _ _
  obtain ⟨s, hs⟩ := GlobalTheory.UnramIdem.exists_lift (R := O ⊗[Z] W) hu (f.map (algebraMap Z O)) (hfm.map _)
    (by rwa [hfm.natDegree_map]) (fun τ => by rw [Polynomial.eval_map_algebraMap, hroot]) (1 ⊗ₜ t) (by
      rw [Polynomial.aeval_map_algebraMap]
      exact (Polynomial.aeval_algHom_apply (Algebra.TensorProduct.includeRight : W →ₐ[Z] O ⊗[Z] W) t f).trans
        (by rw [h0, map_zero]))
  have h2 : Φ (1 ⊗ₜ t) = fun τ => emb τ t := funext fun τ => by simp [Φ]
  have h3 : Φ.comp s = AlgHom.id _ _ :=
    GlobalTheory.UnramIdem.hom_ext hu _ _ (by rw [AlgHom.comp_apply, hs, h2]; rfl)
  have h4 : s.comp Φ = AlgHom.id _ _ := by
    refine tensor_hom_ext hv _ _ fun x => ?_
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    rcases ht x with h | ⟨k, h⟩
    · rw [h, tmul_zero, map_zero, map_zero]
    · have h5 : (1 : O) ⊗ₜ[Z] (t ^ k) = ((1 : O) ⊗ₜ[Z] t) ^ k := by
        rw [Algebra.TensorProduct.tmul_pow, one_pow]
      rw [h, h5, map_pow, map_pow, h2, hs]
  exact ⟨Function.LeftInverse.injective (g := s) (AlgHom.congr_fun h4),
    Function.RightInverse.surjective (g := s) (AlgHom.congr_fun h3)⟩

end Glue

variable {l : ℕ} [hl : Fact l.Prime]

section Sigma

variable (a : ℕ) [NeZero a]

variable (l) in

def sigmaNeg (τ : ZMod a) : Wq l a ≃ₐ[ℤ_[l]] Wq l a := sigma l a ^ (-τ).val

theorem sigmaNeg_zero : sigmaNeg l a 0 = 1 := by simp [sigmaNeg]

theorem sigmaNeg_mul (τ : ZMod a) : sigmaNeg l a τ * sigma l a = sigmaNeg l a (τ - 1) := by
  rw [sigmaNeg, sigmaNeg, ← pow_succ]
  refine pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 ?_) (sigma_pow_eq_one l a)
  simp only [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
  ring

theorem mul_sigmaNeg (τ : ZMod a) : sigma l a * sigmaNeg l a τ = sigmaNeg l a (τ - 1) := by
  rw [← sigmaNeg_mul, sigmaNeg, ← pow_succ, ← pow_succ']

theorem exists_monic (t : Wq l a) : ∃ f : Polynomial ℤ_[l], f.Monic ∧ f.natDegree = a ∧
    ∀ τ, Polynomial.aeval (sigmaNeg l a τ t) f = 0 := by
  let P : Polynomial (Wq l a) := ∏ τ : ZMod a, (Polynomial.X - Polynomial.C (sigmaNeg l a τ t))
  have hPm : P.Monic := Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _
  have hPσ : P.map (sigma l a : Wq l a →+* Wq l a) = P := by
    rw [Polynomial.map_prod]
    refine Fintype.prod_equiv (Equiv.subRight 1) _ _ fun τ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Equiv.subRight_apply, ← mul_sigmaNeg]
    rfl
  have hPl : P ∈ Polynomial.lifts (algebraMap ℤ_[l] (Wq l a)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨y, hy⟩ := GlobalTheory.ArtinSchreierWitt.fixed_frob l (Fq l a) (P.coeff n)
      ((Polynomial.coeff_map _ n).symm.trans (congrArg (Polynomial.coeff · n) hPσ))
    exact ⟨y, hy.symm⟩
  obtain ⟨f, hf, hfd, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hPl hPm
  have hroot : ∀ τ, Polynomial.aeval (sigmaNeg l a τ t) f = 0 := fun τ => by
    rw [← Polynomial.eval_map_algebraMap, hf, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by simp)
  refine ⟨f, hfm, ?_, hroot⟩
  rw [hfd, Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _]
  simp

theorem exists_gen_isUnit_sub : ∃ z : Fq l a, (∀ x : Fq l a, x ≠ 0 → ∃ k : ℕ, x = z ^ k) ∧
    ∀ τ σ : ZMod a, τ ≠ σ →
      IsUnit (sigmaNeg l a τ (WittVector.teichmuller l z) - sigmaNeg l a σ (WittVector.teichmuller l z)) := by
  obtain ⟨z, ω, hω, hz, h⟩ := exists_gen l a
  refine ⟨z, h, fun τ σ hne => WittVector.isUnit_of_coeff_zero_ne_zero _ fun he => ?_⟩
  rw [← WittVector.constantCoeff_apply, map_sub, sub_eq_zero, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, sigmaNeg, sigmaNeg, coeff_sigma_pow, coeff_sigma_pow,
    WittVector.teichmuller_coeff_zero] at he
  have h2 : ω ^ l ^ (-τ).val = ω ^ l ^ (-σ).val := (algebraMap (Om l) ℂ_[l]).injective (by
    have h5 := congrArg (fun y : Fq l a => (((Fq.val l a y).untilt : OC l) : ℂ_[l])) he
    simp only [map_pow, SubmonoidClass.coe_pow, GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz] at h5 ⊢
    exact h5)
  have hvv : (-τ).val ≠ (-σ).val := fun h => hne (neg_injective (ZMod.val_injective _ h))
  have hlt : ∀ i < a, l ^ i < l ^ a - 1 := fun i hi => by
    have ha : 2 ≤ a := by have := ZMod.val_lt (-τ); have := ZMod.val_lt (-σ); omega
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    have h3 : l ^ i ≤ l ^ (b + 1) := Nat.pow_le_pow_right hl.out.pos (by omega)
    have h4 : 1 < l ^ (b + 1) := Nat.one_lt_pow (by omega) hl.out.one_lt
    have h5 : l ^ (b + 1) * 2 ≤ l ^ (b + 2) := Nat.mul_le_mul_left _ hl.out.two_le
    omega
  exact hvv (Nat.pow_right_injective hl.out.two_le
    (hω.pow_inj (hlt _ (ZMod.val_lt _)) (hlt _ (ZMod.val_lt _)) h2))

end Sigma

section Coeff

variable {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O)

def emb (τ : ZMod a) : Wq l a →ₐ[ℤ_[l]] O := t.comp (sigmaNeg l a τ).toAlgHom

theorem emb_zero (w : Wq l a) : emb t 0 w = t w := congrArg t (AlgEquiv.congr_fun (sigmaNeg_zero a) w)

theorem emb_sigma (τ : ZMod a) (w : Wq l a) : emb t τ (sigma l a w) = emb t (τ - 1) w :=
  congrArg t (AlgEquiv.congr_fun (sigmaNeg_mul a τ) w)

def splitHom : O ⊗[ℤ_[l]] Wq l a →ₐ[O] (ZMod a → O) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (AlgHom.pi (emb t)) fun _ _ => Commute.all _ _

theorem splitHom_tmul (o : O) (w : Wq l a) (τ : ZMod a) : splitHom t (o ⊗ₜ w) τ = o * emb t τ w := rfl

theorem splitHom_bijective : Function.Bijective (splitHom t) := by
  obtain ⟨z, h, hu⟩ := exists_gen_isUnit_sub (l := l) a
  obtain ⟨f, hfm, hfd, hroot⟩ := exists_monic a (WittVector.teichmuller l z)
  have h2 := hroot 0
  rw [sigmaNeg_zero, AlgEquiv.one_apply] at h2
  refine bijective_lift (emb t) (span_teich l a) _ (fun x => ?_)
    (fun τ σ hne => by
      have := (hu τ σ hne).map t
      rw [map_sub] at this
      exact this) f hfm (by rw [hfd, ZMod.card]) h2
    fun τ => (Polynomial.aeval_algHom_apply t (sigmaNeg l a τ _) f).trans (by rw [hroot, map_zero])
  rcases eq_or_ne x 0 with rfl | h0
  · exact Or.inl (WittVector.teichmuller_zero l)
  · exact Or.inr ((h x h0).imp fun k hk => by rw [hk, map_pow])

def splitEquiv : O ⊗[ℤ_[l]] Wq l a ≃ₐ[O] (ZMod a → O) := AlgEquiv.ofBijective _ (splitHom_bijective t)

def galA (g : GQ l) : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := Per.σA g
  commutes' := fun r =>
    WittVector.map_injective (algebraMap (OCb l) (Cb l)) (IsFractionRing.injective (OCb l) (Cb l))
      ((galW_inclW g _).symm.trans (((congrArg (galW l g) ((inclWA l).commutes r)).trans
        ((galW l g).commutes r)).trans ((inclWA l).commutes r).symm))

variable (l O) in

abbrev OA : Type := O ⊗[ℤ_[l]] Ainf l

variable (l O) in

abbrev OW : Type := O ⊗[ℤ_[l]] WCb l

variable (l O) in

def inclO : OA l O →ₐ[O] OW l O := Algebra.TensorProduct.map (AlgHom.id _ _) (inclWA l)

variable (l O) in

def frobOW : OW l O →ₐ[O] OW l O := Algebra.TensorProduct.map (AlgHom.id _ _) (frobW l)

variable (l O) in

def frobOA : OA l O →ₐ[O] OA l O :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (GlobalTheory.Cyc.IoMap.frobA l)

variable (O) in

def galOA (g : GQ l) : OA l O →ₐ[O] OA l O := Algebra.TensorProduct.map (AlgHom.id _ _) (galA g)

variable (O) in

def galOW (g : GQ l) : OW l O →ₐ[O] OW l O :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (galW l g).toAlgHom

theorem frobOA_tmul (o : O) (w : Ainf l) :
    frobOA l O (o ⊗ₜ w) = o ⊗ₜ WittVector.frobenius w :=
  congrArg (fun y : Ainf l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.Cyc.IoMap.frobA_apply l w)

theorem galOA_tmul (g : GQ l) (o : O) (w : Ainf l) : galOA O g (o ⊗ₜ w) = o ⊗ₜ Per.σA g w := rfl

theorem galOW_tmul (g : GQ l) (o : O) (w : WCb l) : galOW O g (o ⊗ₜ w) = o ⊗ₜ galW l g w := rfl

theorem inclO_tmul (o : O) (w : Ainf l) : inclO l O (o ⊗ₜ w) = o ⊗ₜ inclW l w := rfl

theorem frobOW_tmul (o : O) (w : WCb l) : frobOW l O (o ⊗ₜ w) = o ⊗ₜ frobW l w := rfl

theorem galOW_one (x : OW l O) : galOW O 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => rw [galOW_tmul, map_one, AlgEquiv.one_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galOW_mul (g h : GQ l) (x : OW l O) : galOW O (g * h) x = galOW O g (galOW O h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => rw [galOW_tmul, galOW_tmul, galOW_tmul, map_mul, AlgEquiv.mul_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem frobOW_inclO (x : OA l O) : frobOW l O (inclO l O x) = inclO l O (frobOA l O x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => rw [frobOA_tmul, inclO_tmul, inclO_tmul, frobOW_tmul, frobW_inclW]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galOW_inclO (g : GQ l) (x : OA l O) : galOW O g (inclO l O x) = inclO l O (galOA O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => rw [galOA_tmul, inclO_tmul, inclO_tmul, galOW_tmul, galW_inclW]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galOW_frobOW (g : GQ l) (x : OW l O) : galOW O g (frobOW l O x) = frobOW l O (galOW O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    rw [frobOW_tmul, galOW_tmul, galOW_tmul, frobOW_tmul]
    exact congrArg (fun y : WCb l => o ⊗ₜ[ℤ_[l]] y)
      (WittVector.ext fun n => map_pow (autCb l (galTilt l g)) (w.coeff n) l)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem inclO_injective [Module.Free ℤ_[l] O] : Function.Injective (inclO l O) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := O) (inclWA l).toLinearMap inclW_injective

def constA : (ZMod a → O) →ₐ[O] OA l O :=
  (Algebra.TensorProduct.map (AlgHom.id _ _) (wA l a)).comp (splitEquiv t).symm.toAlgHom

def constW : (ZMod a → O) →ₐ[O] OW l O := (inclO l O).comp (constA t)

theorem constA_splitHom (x : O ⊗[ℤ_[l]] Wq l a) :
    constA t (splitHom t x) = Algebra.TensorProduct.map (AlgHom.id O _) (wA l a) x :=
  congrArg (Algebra.TensorProduct.map (AlgHom.id O _) (wA l a)) ((splitEquiv t).symm_apply_apply x)

theorem constA_emb (w : Wq l a) : constA t (fun τ => emb t τ w) = 1 ⊗ₜ wA l a w := by
  have : (fun τ => emb t τ w) = splitHom t (1 ⊗ₜ w) := funext fun τ => by
    rw [splitHom_tmul, one_mul]
  rw [this, constA_splitHom]
  rfl

theorem frobOA_constA (x : ZMod a → O) :
    frobOA l O (constA t x) = constA t fun τ => x (τ - 1) := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective t).2 x
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact (map_zero (constA t)).symm
  | tmul o w =>
    have : (fun τ => splitHom t (o ⊗ₜ w) (τ - 1)) = splitHom t (o ⊗ₜ sigma l a w) :=
      funext fun τ => by rw [splitHom_tmul, splitHom_tmul, emb_sigma]
    rw [this, constA_splitHom, constA_splitHom]
    exact (frobOA_tmul o _).trans (congrArg (fun y : Ainf l => o ⊗ₜ[ℤ_[l]] y) (wA_sigma l a w).symm)
  | add y y' h h' =>
    rw [map_add, map_add, map_add, h, h', ← map_add]
    rfl

theorem frobOA_idem (τ : ZMod a) : frobOA l O (idem (constA t) τ) = idem (constA t) (τ + 1) := by
  rw [idem, frobOA_constA, idem]
  congr 1
  ext1 σ
  simp only [Pi.single_apply, sub_eq_iff_eq_add]

theorem inclO_idem (τ : ZMod a) : inclO l O (idem (constA t) τ) = idem (constW t) τ := rfl

theorem frobOW_idem (τ : ZMod a) : frobOW l O (idem (constW t) τ) = idem (constW t) (τ + 1) := by
  rw [← inclO_idem, frobOW_inclO, frobOA_idem, inclO_idem]

theorem galOA_constA {g : GQ l} (hg : ∀ x ∈ Kunr l a, g x = x) (x : ZMod a → O) :
    galOA O g (constA t x) = constA t x := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective t).2 x
  rw [constA_splitHom]
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Ainf l => o ⊗ₜ[ℤ_[l]] y) (gal_wA l a hg w)
  | add y y' h h' => simp only [map_add, h, h']

variable (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

variable {K} (l) in

def frobAc (f : ZMod a → A O K) : ZMod a → A O K :=
  fun τ => ⟨frob _ l (f (τ - 1)), frob_mem_A l (f (τ - 1)).2⟩

omit [NeZero a] [Algebra ℤ_[l] O] in

theorem coe_frobAc (f : ZMod a → A O K) (τ : ZMod a) :
    (frobAc l f τ : K⟦X⟧) = frobTot _ a l (fun σ => (f σ : K⟦X⟧)) τ := rfl

def toAc : (Wq l a)⟦X⟧ →+* (ZMod a → A O K) :=
  RingHom.pi fun τ => (equivA O K).toRingEquiv.toRingHom.comp
    (PowerSeries.map (emb t τ).toRingHom)

theorem coeff_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) (n : ℕ) :
    coeff n (toAc t K x τ : K⟦X⟧) = algebraMap O K (emb t τ (coeff n x)) := rfl

theorem exists_eq_sum_toAc {J : Type} [Fintype J] (o : Module.Basis J ℤ_[l] O) (f : ZMod a → A O K) :
    ∃ x : J → (Wq l a)⟦X⟧, f = ∑ j, o j • toAc t K (x j) := by
  choose y hy using fun n => (splitHom_bijective t).2
    fun τ => coeff n ((equivA O K).symm (f τ))
  refine ⟨fun j => mk fun n => GlobalTheory.Decompl.crd o j (y n), funext fun τ => ?_⟩
  refine (equivA O K).symm.injective (PowerSeries.ext fun n => ?_)
  rw [← congrFun (hy n) τ, ← GlobalTheory.Decompl.sum_crd o (y n)]
  simp only [map_sum, Finset.sum_apply, Pi.smul_apply, map_smul, splitHom_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show toAc t K (mk fun n => GlobalTheory.Decompl.crd o j (y n)) τ =
    equivA O K (PowerSeries.map (emb t τ).toRingHom _) from rfl, AlgEquiv.symm_apply_apply,
    coeff_map, coeff_mk, smul_eq_mul]
  rfl

namespace PiSys

variable {e : ℕ} (ϖ : PiSys l e) (O)

def teichR : OA l O := 1 ⊗ₜ ϖ.teich

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem complete_teichR : IsAdicComplete (Ideal.span {ϖ.teichR O}) (OA l O) :=
  GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) _ (h := ϖ.complete_teich)

theorem sep_teichR (x : OA l O) (h : ∀ n, ϖ.teichR O ^ n ∣ x) : x = 0 :=
  have := ϖ.complete_teichR O
  GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (h n)

theorem exists_evO : ∃ f : O⟦X⟧ →ₐ[O] OA l O, f X = ϖ.teichR O :=
  have := ϖ.complete_teichR O
  GlobalTheory.Cyc.IoMap.algHom_exists _ (GlobalTheory.Per.AinfComplete.summ_of_precomplete _) (ϖ.sep_teichR O)

def evO : O⟦X⟧ →ₐ[O] OA l O := (ϖ.exists_evO O).choose

theorem evO_X : ϖ.evO O X = ϖ.teichR O := (ϖ.exists_evO O).choose_spec

def iA : A O K →ₐ[O] OA l O := (ϖ.evO O).comp (equivA O K).symm.toAlgHom

theorem iA_equivA (f : O⟦X⟧) : ϖ.iA O K (equivA _ _ f) = ϖ.evO O f :=
  congrArg (ϖ.evO O) ((equivA O K).symm_apply_apply f)

theorem iA_u : ϖ.iA O K (uIn _) = ϖ.teichR O := by
  rw [← evO_X, ← ϖ.iA_equivA O K]
  exact congrArg _ (Subtype.ext (PowerSeries.map_X _).symm)

variable (a) in

theorem iA_E : ϖ.iA O K (EIn l e _) = 1 ⊗ₜ ϖ.ev a (eis l a e) := by
  have : EIn l e (A O K) = uIn _ ^ e + (l : A O K) := Subtype.ext (by simp [E])
  rw [this, map_add, map_pow, iA_u, map_natCast, eis, map_add, map_pow, ev_X, map_natCast, tmul_add, teichR,
    Algebra.TensorProduct.tmul_pow, one_pow]
  exact congrArg _ (map_natCast (Algebra.TensorProduct.includeRight : Ainf l →ₐ[ℤ_[l]] OA l O) l).symm

variable {O}

def iTot : (ZMod a → A O K) →ₐ[O] OA l O := glue (constA t) (ϖ.iA O K)

theorem iTot_u : ϖ.iTot t K (fun _ => uIn _) = 1 ⊗ₜ ϖ.teich := (glue_const _ _ _).trans (ϖ.iA_u O K)

theorem iTot_E : ϖ.iTot t K (fun _ => EIn l e _) = 1 ⊗ₜ ϖ.ev a (eis l a e) := (glue_const _ _ _).trans (ϖ.iA_E a O K)

theorem iTot_toAc (x : (Wq l a)⟦X⟧) : ϖ.iTot t K (toAc t K x) = 1 ⊗ₜ ϖ.ev a x := by
  have hX : ϖ.iTot t K (toAc t K X) = ϖ.teichR O :=
    (congrArg _ (funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _)))).trans (ϖ.iTot_u t K)
  refine RingHom.congr_fun (ringHom_ext_of_sep ((ϖ.iTot t K).toRingHom.comp (toAc t K))
    ((Algebra.TensorProduct.includeRight : Ainf l →ₐ[ℤ_[l]] OA l O).toRingHom.comp (ϖ.ev a)) (fun w => ?_) ?_
    fun y hy => ϖ.sep_teichR O y fun n => hX ▸ hy n) x
  · change ϖ.iTot t K (toAc t K (C w)) = 1 ⊗ₜ ϖ.ev a (C w)
    rw [ev_C, ← constA_emb, eq_sum_idem, iTot, glue_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [show toAc t K (C w) τ = equivA _ _ (PowerSeries.map (emb t τ).toRingHom (C w)) from rfl,
      iA_equivA, map_C]
    exact congrArg _ ((ϖ.evO O).commutes _)
  · change ϖ.iTot t K (toAc t K X) = 1 ⊗ₜ ϖ.ev a X
    rw [hX, ev_X, teichR]

variable (O) in

theorem iA_frob (f : A O K) : ϖ.iA O K ⟨frob _ l f, frob_mem_A l f.2⟩ = frobOA l O (ϖ.iA O K f) := by
  obtain ⟨f, rfl⟩ := (equivA O K).surjective f
  have h0 : (⟨frob _ l (equivA O K f), frob_mem_A l (equivA O K f).2⟩ : A O K) =
      equivA _ _ (PowerSeries.expand l hl.out.ne_zero f) :=
    Subtype.ext (PowerSeries.map_expand _ _ _ _).symm
  have h1 : frobOA l O (ϖ.teichR O) = ϖ.teichR O ^ l := by
    rw [teichR, frobOA_tmul, Algebra.TensorProduct.tmul_pow, one_pow, WittVector.frobenius_eq_map_frobenius,
      teich, WittVector.map_teichmuller, frobenius_def, map_pow]
  have h2 : ((ϖ.evO O).comp (PowerSeries.expand l hl.out.ne_zero)) X = ϖ.teichR O ^ l := by
    rw [AlgHom.comp_apply, expand_X, map_pow, evO_X]
  rw [h0, iA_equivA, iA_equivA]
  refine AlgHom.congr_fun (GlobalTheory.Cyc.IoMap.algHom_unique ((ϖ.evO O).comp (PowerSeries.expand l hl.out.ne_zero))
    ((frobOA l O).comp (ϖ.evO O)) ?_ fun y hy => ϖ.sep_teichR O y fun n => ?_) f
  · rw [h2, AlgHom.comp_apply, evO_X, h1]
  · exact (pow_dvd_pow_of_dvd (dvd_pow_self _ hl.out.ne_zero) n).trans (h2 ▸ hy n)

theorem iTot_frob (f : ZMod a → A O K) : ϖ.iTot t K (frobAc l f) = frobOA l O (ϖ.iTot t K f) :=
  (map_glue (frobOA l O).toRingHom 1 (frobOA_idem t) fun τ => (ϖ.iA_frob O K (f (τ - 1))).symm).symm

variable [NeZero e]

variable (O) in

theorem galOA_teichR (g : GQ l) : galOA O g (ϖ.teichR O) = (1 + 1 ⊗ₜ ϖ.mu g) * ϖ.teichR O := by
  rw [teichR, galOA_tmul, gal_teich, Algebra.TensorProduct.one_def, ← tmul_add,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem galOA_iTot {g : GQ l} (hg : g ∈ ϖ.GfieldInf a) (f : ZMod a → A O K) :
    galOA O g (ϖ.iTot t K f) = ϖ.iTot t K f := by
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) f
  simp only [map_sum, map_smul, iTot_toAc, galOA_tmul, ϖ.gal_ev l a hg]

variable (O)

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem isUnit_inclO_teichR : IsUnit (inclO l O (ϖ.teichR O)) :=
  ϖ.isUnit_inclW_teich.map (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O)

theorem isUnit_inclO_iA_E : IsUnit (inclO l O (ϖ.iA O K (EIn l e _))) := by
  rw [ϖ.iA_E 1 O K]
  exact (ϖ.isUnit_inclW_ev_eis 1).map (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O)

variable [NormedAlgebra ℚ_[l] K]

def iE : invE l e (A O K) →ₐ[O] OW l O where
  toRingHom := IsLocalization.Away.lift (EIn l e (A O K)) (g := ((inclO l O).comp (ϖ.iA O K)).toRingHom)
    (ϖ.isUnit_inclO_iA_E O K)
  commutes' o := (IsLocalization.Away.lift_eq (S := invE l e (A O K)) (EIn l e (A O K)) (ϖ.isUnit_inclO_iA_E O K)
    (algebraMap _ _ o)).trans (((inclO l O).comp (ϖ.iA O K)).commutes o)

theorem iE_of_mem {f : K⟦X⟧} (h : f ∈ A O K) (h' : f ∈ invE l e (A O K)) :
    ϖ.iE O K ⟨f, h'⟩ = inclO l O (ϖ.iA O K ⟨f, h⟩) :=
  IsLocalization.Away.lift_eq (S := invE l e (A O K)) (EIn l e (A O K)) (ϖ.isUnit_inclO_iA_E O K) ⟨f, h⟩

variable {O}

theorem iTot_injective : Function.Injective (ϖ.iTot t K) := by
  have hy : ∀ x : OA l O, ϖ.teichR O * x = 0 → x = 0 := fun x hx => inclO_injective (by
    rw [map_zero, ← (ϖ.isUnit_inclO_teichR O).mul_right_eq_zero, ← map_mul, hx, map_zero])
  have hn : ¬ IsUnit ϖ.flat := fun h => ϖ.not_isUnit_teich (h.map (WittVector.teichmuller l))
  let Q := OCb l ⧸ Ideal.span {ϖ.flat}
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  have : CharP Q l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (Ideal.Quotient.mk _), CharP.cast_eq_zero, map_zero])
  let _ : Algebra ℤ_[l] (WittVector l Q) := (zlW l Q).toAlgebra
  let r : Ainf l →ₐ[ℤ_[l]] WittVector l Q :=
    { toRingHom := WittVector.map (Ideal.Quotient.mk _), commutes' := map_zlW l _ }
  have hr : Function.Injective (r.comp (wA l a)) := fun x y h => WittVector.ext fun n =>
    ((Ideal.Quotient.mk (Ideal.span {ϖ.flat})).comp (Fq.val l a)).injective
      (congrArg (WittVector.coeff · n) h)
  let R : OA l O →ₐ[O] O ⊗[ℤ_[l]] WittVector l Q := Algebra.TensorProduct.map (AlgHom.id _ _) r
  have hR : R (ϖ.teichR O) = 0 := by
    change (1 : O) ⊗ₜ[ℤ_[l]] WittVector.map (Ideal.Quotient.mk _) (WittVector.teichmuller l ϖ.flat) = 0
    rw [WittVector.map_teichmuller, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _),
      WittVector.teichmuller_zero, tmul_zero]
  have hc : ∀ c, R (constA t c) = 0 → c = 0 := fun c h => by
    obtain ⟨y, rfl⟩ := (splitHom_bijective t).2 c
    have h1 : (r.comp (wA l a)).toLinearMap.lTensor O y = R (constA t (splitHom t y)) := by
      rw [constA_splitHom]
      clear h
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul o w => rfl
      | add y y' h h' => simp only [map_add, h, h']
    rw [Module.Flat.lTensor_preserves_injective_linearMap (M := O) _ hr (h1.trans (h.trans (map_zero _).symm)),
      map_zero]
  have key : ∀ (τ : ZMod a) (n : ℕ) (f : O⟦X⟧), idem (constA t) τ * ϖ.evO O f = 0 → coeff n f = 0 := by
    intro τ n
    have h0 : ∀ f : O⟦X⟧, idem (constA t) τ * ϖ.evO O f = 0 → constantCoeff f = 0 := fun f hf => by
      have h2 : ϖ.evO O (C (constantCoeff f)) = algebraMap O _ (constantCoeff f) := (ϖ.evO O).commutes _
      rw [f.eq_X_mul_shift_add_const, map_add, map_mul, evO_X, mul_add, h2, mul_comm _ (algebraMap _ _ _),
        ← Algebra.smul_def, idem, ← map_smul] at hf
      have h1 := congrArg R hf
      rw [map_add, map_mul, map_mul, hR, zero_mul, mul_zero, zero_add, map_zero] at h1
      simpa using congrFun (hc _ h1) τ
    induction n with
    | zero => exact fun f hf => by simpa using h0 f hf
    | succ n ih =>
      intro f hf
      have h1 := h0 f hf
      rw [f.eq_X_mul_shift_add_const, h1, map_zero, add_zero, map_mul, evO_X, mul_left_comm] at hf
      simpa using ih _ (hy _ hf)
  refine (injective_iff_map_eq_zero _).2 fun f hf => funext fun τ => ?_
  obtain ⟨g, hg⟩ := (equivA O K).surjective (f τ)
  have h1 := idem_mul_glue (constA t) (ϖ.iA O K) f τ
  rw [show glue (constA t) (ϖ.iA O K) f = 0 from hf, mul_zero, ← hg, iA_equivA] at h1
  rw [← hg, show g = 0 from PowerSeries.ext fun n => key τ n g h1.symm, map_zero]
  rfl

def iW : (ZMod a → invE l e (A O K)) →ₐ[O] OW l O := glue (constW t) (ϖ.iE O K)

theorem iW_of_mem (f : ZMod a → A O K) :
    ϖ.iW t K (fun τ => ⟨f τ, le_away _ _ (f τ).2⟩) = inclO l O (ϖ.iTot t K f) :=
  (map_glue (inclO l O).toRingHom 0 (fun τ => by rw [add_zero]; rfl) fun τ => by
    rw [sub_zero]; exact (ϖ.iE_of_mem O K _ _).symm).symm

theorem iW_injective : Function.Injective (ϖ.iW t K) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  choose n hn using fun τ => (f τ).2
  let m := Finset.univ.sup n
  have h1 : ∀ τ, E K l e ^ m * (f τ : K⟦X⟧) ∈ A O K := fun τ => by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ τ))
    rw [show m = c + n τ from hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (hn τ)
  have h2 := ϖ.iW_of_mem t K fun τ => ⟨_, h1 τ⟩
  have h3 : (fun τ => (⟨E K l e ^ m * (f τ : K⟦X⟧), le_away _ _ (h1 τ)⟩ : invE l e (A O K))) =
      (fun _ => EIn l e _) ^ m * f := rfl
  rw [h3, map_mul, hf, mul_zero, ← map_zero (inclO l O), ← map_zero (ϖ.iTot t K)] at h2
  have h4 := ϖ.iTot_injective t K (inclO_injective h2)
  refine funext fun τ => Subtype.ext (((isUnit_E l e).pow m).mul_right_eq_zero.1 ?_)
  exact (congrArg Subtype.val (congrFun h4 τ)).symm

theorem galOW_iW {g : GQ l} (hg : g ∈ ϖ.GfieldInf a) (f : ZMod a → invE l e (A O K)) :
    galOW O g (ϖ.iW t K f) = ϖ.iW t K f := by
  refine map_glue (galOW O g).toRingHom 0 (fun τ => ?_) fun τ => ?_
  · rw [add_zero, ← inclO_idem]
    exact (galOW_inclO g _).trans (congrArg _ (galOA_constA t (fun x hx =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x
        (ϖ.field_le_fieldInf a (ϖ.Kunr_le_field a hx))) _))
  · rw [sub_zero]
    refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (EIn l e (A O K)))
      (j := (galOW O g).toRingHom.comp (ϖ.iE O K).toRingHom) (k := (ϖ.iE O K).toRingHom)
      (RingHom.ext fun y => ?_)) (f τ)
    change galOW O g (ϖ.iE O K ⟨y, _⟩) = ϖ.iE O K ⟨y, _⟩
    rw [ϖ.iE_of_mem O K y.2, galOW_inclO, ← glue_const (constA t) (ϖ.iA O K)]
    exact congrArg _ (ϖ.galOA_iTot t K hg _)

end PiSys

end Coeff

section FinExt

variable (a : ℕ) [NeZero a]

class HasUnr (a : ℕ) (LL : FinExt l) : Prop where
  le : Kunr l a ≤ LL.1

instance : HasUnr a (unrExt l a) := ⟨le_rfl⟩

instance {e : ℕ} (ϖ : PiSys l e) : HasUnr a (ϖ.field a) := ⟨ϖ.Kunr_le_field a⟩

theorem intToOC_injective (LL : FinExt l) : Function.Injective (intToOC LL) := fun _ _ h =>
  Subtype.ext (Subtype.ext ((algebraMap (Om l) ℂ_[l]).injective (congrArg Subtype.val h)))

theorem intToOC_algebraMap (LL : FinExt l) (z : ℤ_[l]) :
    intToOC LL (algebraMap ℤ_[l] ↥(OL LL) z) = Per.θ l (algebraMap ℤ_[l] (Ainf l) z) :=
  Subtype.ext ((GlobalTheory.UnramIdem.ringHom_eq ((intToOC LL).comp (algebraMap ℤ_[l] ↥(OL LL))) z).trans
    (GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) z).symm)

variable (LL : FinExt l) [HasUnr a LL]

theorem exists_intToOC_eq (w : Wq l a) : ∃ y, intToOC LL y = Per.θ l (wA l a w) := by
  obtain ⟨z, ω, hω, hz, h⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have h2 : ω ∈ LL.1 := HasUnr.le (a := a) (IntermediateField.subset_adjoin _ _ (show ω ^ l ^ a = ω by
    rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul]))
  have h3 : (⟨ω, h2⟩ : ↥LL.1) ∈ OL LL := IsIntegral.of_pow (n := l ^ a - 1) (by omega) (by
    rw [show (⟨ω, h2⟩ : ↥LL.1) ^ (l ^ a - 1) = 1 from Subtype.ext hω.pow_eq_one]; exact isIntegral_one)
  have h4 : intToOC LL ⟨_, h3⟩ = Per.θ l (wA l a (WittVector.teichmuller l z)) := by
    rw [wA_teich, WittVector.fontaineTheta_teichmuller]
    exact Subtype.ext (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz).symm
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) :=
    span_teich l a ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, rfl⟩ := hx
    rcases eq_or_ne x 0 with rfl | h0
    · exact ⟨0, by rw [WittVector.teichmuller_zero, map_zero, map_zero, map_zero]⟩
    · obtain ⟨k, rfl⟩ := h x h0
      exact ⟨⟨_, h3⟩ ^ k, by rw [map_pow, h4, map_pow, map_pow, map_pow]⟩
  | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx⟩ := hx
    obtain ⟨y', hy⟩ := hy
    exact ⟨x' + y', by rw [map_add, map_add, map_add, hx, hy]⟩
  | smul c x _ hx =>
    obtain ⟨x', hx⟩ := hx
    exact ⟨algebraMap _ _ c * x', by
      rw [map_mul, hx, intToOC_algebraMap, Algebra.smul_def, map_mul, map_mul, AlgHom.commutes]⟩

def thetaW : Wq l a →ₐ[ℤ_[l]] ↥(OL LL) where
  toRingHom := liftInj ((Per.θ l).comp (wA l a).toRingHom) (intToOC LL) (intToOC_injective LL)
    (exists_intToOC_eq a LL)
  commutes' z := intToOC_injective LL ((liftInj_spec _ _ _ _ _).trans
    ((congrArg (Per.θ l) ((wA l a).commutes z)).trans (intToOC_algebraMap LL z).symm))

theorem intToOC_thetaW (w : Wq l a) : intToOC LL (thetaW a LL w) = Per.θ l (wA l a w) :=
  liftInj_spec _ _ (intToOC_injective LL) (exists_intToOC_eq a LL) w

instance free_OL : Module.Free ℤ_[l] ↥(OL LL) := GlobalTheory.Decompl.free_OL LL

instance finite_OL : Module.Finite ℤ_[l] ↥(OL LL) := GlobalTheory.Decompl.finite_OL LL

theorem inclO_eq : inclO l ↥(OL LL) = inclR LL := rfl

theorem frobOW_eq : frobOW l ↥(OL LL) = φRW LL := rfl

theorem galOW_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) : galOW ↥(OL LL) g = AI.gRW LL g := by
  rw [LocAinf.gRW, locAinf_actWCbHom_eq]
  rfl

example {e : ℕ} [NeZero e] (ϖ : PiSys l e) : Function.Injective (ϖ.iW (thetaW a LL) ↥LL.1) :=
  ϖ.iW_injective _ _

end FinExt

end GlobalTheory.BKReal
