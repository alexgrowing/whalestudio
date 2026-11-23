import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedFixed

theorem exists_lift {Z O W k T : Type} [CommRing Z] [CommRing O] [CommRing W] [CommRing k] [CommRing T]
    [Algebra Z O] [Algebra Z W] [Algebra O k] (a : k →+* T) (b : W →+* T)
    (h : ∀ z : Z, a (algebraMap O k (algebraMap Z O z)) = b (algebraMap Z W z)) :
    ∃ F : k ⊗[O] (O ⊗[Z] W) →+* T, ∀ c o w, F (c ⊗ₜ (o ⊗ₜ w)) = a c * (a (algebraMap O k o) * b w) := by
  let _ : Algebra O T := (a.comp (algebraMap O k)).toAlgebra
  let _ : Algebra Z T := (b.comp (algebraMap Z W)).toAlgebra
  have : IsScalarTower Z O T := IsScalarTower.of_algebraMap_eq fun z => (h z).symm
  let b' : W →ₐ[Z] T := { b with commutes' := fun _ => rfl }
  let a' : k →ₐ[O] T := { a with commutes' := fun _ => rfl }
  let F₁ : O ⊗[Z] W →ₐ[O] T :=
    Algebra.TensorProduct.lift (Algebra.ofId O T) b' fun _ _ => Commute.all _ _
  exact ⟨(Algebra.TensorProduct.lift a' F₁ fun _ _ => Commute.all _ _).toRingHom, fun c o w => rfl⟩

variable {l : ℕ} [Fact l.Prime]

theorem map_padicInt {R : Type} [CommRing R] [CharP R l] [Algebra (ZMod l) R] (f : ℤ_[l] →+* R) (z : ℤ_[l]) :
    f z = algebraMap (ZMod l) R (PadicInt.toZMod z) := by
  have h := PadicInt.toZMod_spec z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  have h2 := congrArg f hy
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_sub, sub_eq_zero] at h2
  rw [h2]
  generalize PadicInt.toZMod z = n
  rw [ZMod.cast_eq_val, map_natCast, ← map_natCast (algebraMap (ZMod l) R), ZMod.natCast_zmod_val]

theorem perfect_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem fixed_tensor {k C : Type} [Field k] [Field C] [CharP C l] [Algebra (ZMod l) k] [Algebra (ZMod l) C]
    (f : C →ₗ[ZMod l] C) (hf : ∀ x, f x = x ^ l) (y : k ⊗[ZMod l] C) (hy : f.lTensor k y = y) :
    ∃ c : k, y = c ⊗ₜ[ZMod l] (1 : C) := by
  have hex : Function.Exact (Algebra.linearMap (ZMod l) C) (f - LinearMap.id : C →ₗ[ZMod l] C) := by
    intro x
    rw [LinearMap.sub_apply, hf, sub_eq_zero, LinearMap.id_apply]
    constructor
    · intro h
      have h2 := (Subfield.mem_bot_iff_pow_eq_self C l).2 h
      have h3 : (⊥ : Subfield C) ≤ (algebraMap (ZMod l) C).fieldRange := bot_le
      exact h3 h2
    · rintro ⟨a, rfl⟩
      rw [Algebra.linearMap_apply, ← map_pow, ZMod.pow_card]
  obtain ⟨t, ht⟩ := (Module.Flat.lTensor_exact k hex y).1 (by
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, hy, LinearMap.lTensor_id, LinearMap.id_apply, sub_self])
  refine ⟨TensorProduct.rid (ZMod l) k t, ?_⟩
  rw [← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  | add a b ha hb => simp [ha, hb, TensorProduct.add_tmul]

theorem fixed_witt {O k C : Type} [CommRing O] [Field k] [Field C] [CharP k l] [CharP C l] [PerfectRing C l]
    [Algebra ℤ_[l] O] [Algebra O k] [Algebra ℤ_[l] (WittVector l C)]
    (φ : WittVector l C →ₐ[ℤ_[l]] WittVector l C) (hφ0 : ∀ w, (φ w).coeff 0 = w.coeff 0 ^ l)
    (x : k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C))
    (hx : Algebra.TensorProduct.map (AlgHom.id k k) (Algebra.TensorProduct.map (AlgHom.id O O) φ) x = x) :
    ∃ c : k, x = algebraMap k (k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C)) c := by
  let _ : Algebra (ZMod l) k := ZMod.algebra k l
  let _ : Algebra (ZMod l) C := ZMod.algebra C l
  obtain ⟨F, hF⟩ := exists_lift (Z := ℤ_[l]) (O := O) (W := WittVector l C) (k := k) (T := k ⊗[ZMod l] C)
    Algebra.TensorProduct.includeLeftRingHom
    ((Algebra.TensorProduct.includeRight : C →ₐ[ZMod l] k ⊗[ZMod l] C).toRingHom.comp
      WittVector.constantCoeff) (fun z => by
      have h1 := map_padicInt ((algebraMap O k).comp (algebraMap ℤ_[l] O)) z
      have h2 := map_padicInt ((WittVector.constantCoeff : WittVector l C →+* C).comp (algebraMap ℤ_[l] (WittVector l C))) z
      rw [RingHom.comp_apply] at h1 h2
      rw [RingHom.comp_apply, h1, h2]
      simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
  have hF' : ∀ (c : k) (o : O) (w : WittVector l C),
      F (c ⊗ₜ (o ⊗ₜ w)) = (o • c) ⊗ₜ[ZMod l] w.coeff 0 := by
    intro c o w
    rw [hF]
    simp [Algebra.smul_def, mul_comm]
  let j : WittVector l C →+* k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C) :=
    (Algebra.TensorProduct.includeRight : O ⊗[ℤ_[l]] WittVector l C →ₐ[O] k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : WittVector l C →ₐ[ℤ_[l]] (O ⊗[ℤ_[l]] WittVector l C)).toRingHom
  have hl : ((l : ℕ) : k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C)) = 0 := by
    rw [← map_natCast (algebraMap k (k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C))), CharP.cast_eq_zero, map_zero]
  have hs : Function.Surjective (WittVector.constantCoeff : WittVector l C →+* C) := fun c =>
    ⟨WittVector.teichmuller l c, by simp⟩
  let g : C →+* k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C) := RingHom.liftOfSurjective _ hs ⟨j, by
    rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff]
    change j _ = 0
    rw [map_natCast, hl]⟩
  have hg : ∀ w : WittVector l C, g (w.coeff 0) = (1 : k) ⊗ₜ ((1 : O) ⊗ₜ w) := fun w =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ w
  let G : k ⊗[ZMod l] C →+ k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C) := TensorProduct.liftAddHom
    { toFun := fun c =>
        { toFun := fun t => c • g t
          map_zero' := by simp
          map_add' := fun _ _ => by simp }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_smul] }
    (fun n c t => by
      obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective n
      change ((m : ZMod l) • c) • g t = c • g ((m : ZMod l) • t)
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul, smul_assoc, smul_comm])
  have hG : ∀ c t, G (c ⊗ₜ t) = c • g t := fun _ _ => rfl
  have hGF : ∀ y, G (F y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul c r =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]
      | tmul o w =>
        rw [hF', hG, hg, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let f : C →ₗ[ZMod l] C := (frobenius C l).toAddMonoidHom.toZModLinearMap l
  have hφ : ∀ y, F (Algebra.TensorProduct.map (AlgHom.id k k) (Algebra.TensorProduct.map (AlgHom.id O O) φ) y) = f.lTensor k (F y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul c r =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, map_add]
      | tmul o w =>
        rw [hF']
        exact (hF' c o (φ w)).trans (by rw [hφ0]; rfl)
  obtain ⟨c, hc⟩ := fixed_tensor f (fun _ => rfl) (F x) (by rw [← hφ, hx])
  refine ⟨c, ?_⟩
  rw [← hGF x, hc, hG, map_one, Algebra.algebraMap_eq_smul_one]

theorem fixed_red : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] [CharP k l] (x : k ⊗[↥(OL LL)] RW LL), Algebra.TensorProduct.map (AlgHom.id k k) (φRW LL) x = x → ∃ c : k, x = algebraMap k (k ⊗[↥(OL LL)] RW LL) c := by
  intro l _ LL k _ _ _ x hx
  have := perfect_Cb (l := l)
  exact fixed_witt (frobW l) (fun _ => rfl) x hx

end GlobalTheory.RedFixed
