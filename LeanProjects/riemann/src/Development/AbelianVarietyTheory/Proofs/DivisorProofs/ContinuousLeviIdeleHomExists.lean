import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviIdeleHom

open Matrix

section Alg

variable {R : Type*} [CommRing R] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

def levM (x y a b : n → R) (t s : R) : Matrix n n R :=
  1 + (t - 1) • vecMulVec x a + (s - 1) • vecMulVec y b

variable {x y a b : n → R}

theorem levM_mul (hax : a ⬝ᵥ x = 1) (hay : a ⬝ᵥ y = 0) (hbx : b ⬝ᵥ x = 0) (hby : b ⬝ᵥ y = 1) (t s t' s' : R) :
    levM x y a b t s * levM x y a b t' s' = levM x y a b (t * t') (s * s') := by
  have hPP : vecMulVec x a * vecMulVec x a = vecMulVec x a := by rw [vecMulVec_mul_vecMulVec, hax, one_smul]
  have hPQ : vecMulVec x a * vecMulVec y b = 0 := by
    rw [vecMulVec_mul_vecMulVec, hay, zero_smul]; ext i j; simp [vecMulVec_apply]
  have hQP : vecMulVec y b * vecMulVec x a = 0 := by
    rw [vecMulVec_mul_vecMulVec, hbx, zero_smul]; ext i j; simp [vecMulVec_apply]
  have hQQ : vecMulVec y b * vecMulVec y b = vecMulVec y b := by rw [vecMulVec_mul_vecMulVec, hby, one_smul]
  simp only [levM, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm, hPP, hPQ, hQP, hQQ,
    smul_zero, add_zero, zero_add, smul_smul]
  module

theorem levM_one : levM x y a b 1 1 = 1 := by simp [levM]

theorem levi_matrix_mulVec_first_vector (hax : a ⬝ᵥ x = 1) (hbx : b ⬝ᵥ x = 0) (t s : R) : levM x y a b t s *ᵥ x = t • x := by
  simp only [levM, add_mulVec, one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, hax, hbx, op_smul_eq_smul]
  simp only [one_smul, zero_smul, smul_zero, add_zero]
  module

theorem levM_mulVec_y (hay : a ⬝ᵥ y = 0) (hby : b ⬝ᵥ y = 1) (t s : R) : levM x y a b t s *ᵥ y = s • y := by
  simp only [levM, add_mulVec, one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, hay, hby, op_smul_eq_smul]
  simp only [one_smul, zero_smul, smul_zero, add_zero]
  module

theorem levM_mul_fix {ι : Matrix n m R} (haι : a ᵥ* ι = 0) (hbι : b ᵥ* ι = 0) (t s : R) : levM x y a b t s * ι = ι := by
  simp only [levM, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul, haι, hbι]
  have : vecMulVec x (0 : m → R) = 0 := by ext i j; simp [vecMulVec_apply]
  have h2 : vecMulVec y (0 : m → R) = 0 := by ext i j; simp [vecMulVec_apply]
  rw [this, h2, smul_zero, smul_zero, add_zero, add_zero]

theorem levM_map {S : Type*} [CommRing S] (f : R →+* S) (t s : R) :
    (levM x y a b t s).map f = levM (f ∘ x) (f ∘ y) (f ∘ a) (f ∘ b) (f t) (f s) := by
  ext i j
  simp [levM, Matrix.one_apply, vecMulVec_apply, map_add, map_mul, map_sub]

theorem levM_unitary (c : R →+* R) (hc : ∀ r, c (c r) = r) {J : Matrix n n R}
    (ha : J *ᵥ (c ∘ y) = a) (hb : J *ᵥ (c ∘ x) = -b) (hxJ : x ᵥ* J = c ∘ b) (hyJ : y ᵥ* J = -(c ∘ a))
    (hax : a ⬝ᵥ x = 1) (hay : a ⬝ᵥ y = 0) (hbx : b ⬝ᵥ x = 0) (hby : b ⬝ᵥ y = 1)
    {t s : R} (h1 : t * c s = 1) (h2 : s * c t = 1) :
    (levM x y a b t s)ᵀ * J * (levM x y a b t s).map c = J := by
  have hcc : c ∘ (c ∘ x) = x := funext fun i => hc _
  have hcc' : c ∘ (c ∘ y) = y := funext fun i => hc _
  have d1 : (c ∘ b) ⬝ᵥ (c ∘ x) = 0 := by rw [← RingHom.map_dotProduct, hbx, map_zero]
  have d2 : (c ∘ b) ⬝ᵥ (c ∘ y) = 1 := by rw [← RingHom.map_dotProduct, hby, map_one]
  have d3 : (c ∘ a) ⬝ᵥ (c ∘ x) = 1 := by rw [← RingHom.map_dotProduct, hax, map_one]
  have d4 : (c ∘ a) ⬝ᵥ (c ∘ y) = 0 := by rw [← RingHom.map_dotProduct, hay, map_zero]
  rw [levM_map, levM]
  simp only [levM, transpose_add, transpose_one, transpose_smul, transpose_vecMulVec, add_mul, mul_add, Matrix.one_mul,
    Matrix.mul_one, smul_mul_assoc, mul_smul_comm, vecMulVec_mul, mul_vecMulVec, hxJ, hyJ, ha, hb, vecMulVec_mul_vecMulVec,
    neg_dotProduct, d1, d2, d3, d4, smul_smul]
  simp only [vecMulVec_mulVec, op_smul_eq_smul, d1, d2, d3, d4, dotProduct_neg, neg_dotProduct, Matrix.vecMulVec_neg,
    Matrix.neg_vecMulVec, Matrix.smul_vecMulVec, zero_smul, one_smul, neg_zero, smul_zero, add_zero, neg_neg]
  simp only [Matrix.neg_mulVec, vecMulVec_mulVec, op_smul_eq_smul, d1, d2, d3, d4, Matrix.zero_vecMulVec, Matrix.neg_vecMulVec,
    Matrix.smul_vecMulVec, zero_smul, one_smul, neg_zero, smul_zero, add_zero, neg_neg, smul_neg]
  linear_combination (norm := module) h1 • vecMulVec a (c ∘ b) - h2 • vecMulVec b (c ∘ a)

end Alg

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.includeRight_apply]

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

def homOf (σ : E →ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (M : (AE F E)ˣ → Matrix (Fin N) (Fin N) (AE F E))
    (hone : M 1 = 1) (hmul : ∀ t t', M (t * t') = M t * M t')
    (hunit : ∀ t, (M t)ᵀ * incM F J * (M t).map (cA σ) = incM F J) : (AE F E)ˣ →* UA σ J where
  toFun t := ⟨⟨M t, M t⁻¹, by rw [← hmul, mul_inv_cancel, hone], by rw [← hmul, inv_mul_cancel, hone]⟩, hunit t⟩
  map_one' := Subtype.ext (Units.ext hone)
  map_mul' t t' := Subtype.ext (Units.ext (hmul t t'))

end Adelic

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Matrix

theorem map_comp_mulVec {R S : Type*} [CommRing R] [CommRing S] {n m : Type*} [Fintype m] (f : R →+* S)
    (M : Matrix n m R) (v : m → R) : M.map f *ᵥ (f ∘ v) = f ∘ (M *ᵥ v) := funext fun i => (RingHom.map_mulVec f M v i).symm

theorem map_comp_vecMul {R S : Type*} [CommRing R] [CommRing S] {n m : Type*} [Fintype n] (f : R →+* S)
    (M : Matrix n m R) (v : n → R) : (f ∘ v) ᵥ* M.map f = f ∘ (v ᵥ* M) := funext fun i => (RingHom.map_vecMul f M v i).symm

theorem dual_facts {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {N N₁ : ℕ} {J : Matrix (Fin N) (Fin N) E}
    (hsk : ∀ i j, σ (J j i) = -J i j) {x y : Fin N → E} {ι : Matrix (Fin N) (Fin N₁) E}
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) :
    let aE := J *ᵥ (⇑σ ∘ y); let bE := -(J *ᵥ (⇑σ ∘ x))
    aE ⬝ᵥ x = 1 ∧ aE ⬝ᵥ y = 0 ∧ bE ⬝ᵥ x = 0 ∧ bE ⬝ᵥ y = 1 ∧ x ᵥ* J = ⇑σ ∘ bE ∧ y ᵥ* J = -(⇑σ ∘ aE) ∧
      aE ᵥ* ι = 0 ∧ bE ᵥ* ι = 0 := by
  intro aE bE
  have hconj : ∀ v : Fin N → E, ⇑σ ∘ (J *ᵥ (⇑σ ∘ v)) = -(v ᵥ* J) := by
    intro v; funext i
    simp only [Function.comp_apply, mulVec, dotProduct, vecMul, map_sum, map_mul, hσ, Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show J i j = -σ (J j i) by rw [hsk, neg_neg], map_neg, hσ]
    ring
  have hform : ∀ u v : Fin N → E, form σ J u v = (J *ᵥ (⇑σ ∘ v)) ⬝ᵥ u := fun u v => dotProduct_comm _ _
  have hyx : form σ J y x = -1 := by
    have h := congrArg σ hxy
    rw [map_one] at h
    have : σ (form σ J x y) = -form σ J y x := by
      unfold form
      change σ.toRingHom (x ⬝ᵥ J *ᵥ (⇑σ ∘ y)) = -(y ⬝ᵥ J *ᵥ (⇑σ ∘ x))
      rw [RingHom.map_dotProduct]
      change (⇑σ ∘ x) ⬝ᵥ (⇑σ ∘ (J *ᵥ (⇑σ ∘ y))) = _
      rw [hconj, dotProduct_neg, dotProduct_comm, ← dotProduct_mulVec]
    rw [this] at h
    linear_combination -h
  have hvanish : ∀ w : Fin N → E, (∀ u, (ι *ᵥ u) ⬝ᵥ w = 0) → w ᵥ* ι = 0 := by
    intro w hw; funext j
    have := hw (Pi.single j 1)
    rw [dotProduct_comm, dotProduct_mulVec, dotProduct_single, mul_one] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hform]; exact hxy
  · rw [← hform]; exact hyy
  · simp only [bE, neg_dotProduct]; rw [← hform, hxx, neg_zero]
  · simp only [bE, neg_dotProduct]; rw [← hform, hyx, neg_neg]
  · simp only [bE]
    funext i
    have := congrFun (hconj x) i
    simp only [Function.comp_apply, Pi.neg_apply, map_neg] at this ⊢
    rw [this, neg_neg]
  · simp only [aE]; rw [hconj, neg_neg]
  · exact hvanish _ fun u => (dotProduct_comm _ _).trans ((hform _ _).symm.trans (horth u).2)
  · refine hvanish _ fun u => ?_
    simp only [bE, dotProduct_neg]
    rw [dotProduct_comm]; exact neg_eq_zero.2 ((hform _ _).symm.trans (horth u).1)

end Main

section Thm

open Matrix

theorem levi_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∃ mt : (AE F E)ˣ →* UA σ G.W.J, (∀ g, Continuous fun t => mt t * g) ∧ (∀ t, IsLevi (W₁ := W₁) H' t 1 (mt t)) ∧ (∀ x : Eˣ, mt (Units.map (inclR (F := F) (AF F)).toMonoidHom x) ∈ ratU σ G.W.J) ∧ ∀ t, ∀ u ∈ unip σ G.W H', mt t * u * (mt t)⁻¹ ∈ unip σ G.W H' := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA
  have hσ : ∀ e, σ (σ e) = e := sigma_sigma hT.base.cm
  obtain ⟨hax, hay, hbx, hby, hxJ, hyJ, haι, hbι⟩ := dual_facts hσ hT.geo.hW.skew hA.xx hA.yy hA.xy hA.orth
  set aE := G.W.J *ᵥ (⇑σ ∘ H'.y) with haE
  set bE := -(G.W.J *ᵥ (⇑σ ∘ H'.x)) with hbE
  set f : E →+* AE F E := inclR (F := F) (AF F) with hf
  have hcf : ∀ {k : ℕ} (v : Fin k → E), ⇑(cA σ) ∘ (f ∘ v) = f ∘ (⇑σ ∘ v) := fun v => funext fun i => cA_inclR σ (v i)
  have hdot : ∀ v w : Fin (a + a') → E, (f ∘ v) ⬝ᵥ (f ∘ w) = f (v ⬝ᵥ w) := fun v w => (RingHom.map_dotProduct f v w).symm
  have hneg : ∀ v : Fin (a + a') → E, f ∘ (-v) = -(f ∘ v) := fun v => funext fun i => map_neg f (v i)
  have hax' : (f ∘ aE) ⬝ᵥ (f ∘ H'.x) = 1 := by rw [hdot, hax, map_one]
  have hay' : (f ∘ aE) ⬝ᵥ (f ∘ H'.y) = 0 := by rw [hdot, hay, map_zero]
  have hbx' : (f ∘ bE) ⬝ᵥ (f ∘ H'.x) = 0 := by rw [hdot, hbx, map_zero]
  have hby' : (f ∘ bE) ⬝ᵥ (f ∘ H'.y) = 1 := by rw [hdot, hby, map_one]
  have haι' : (f ∘ aE) ᵥ* incM F H'.ι = 0 := by
    change (f ∘ aE) ᵥ* H'.ι.map f = 0
    rw [map_comp_vecMul, haι]; funext i; simp
  have hbι' : (f ∘ bE) ᵥ* incM F H'.ι = 0 := by
    change (f ∘ bE) ᵥ* H'.ι.map f = 0
    rw [map_comp_vecMul, hbι]; funext i; simp
  let M : (AE F E)ˣ → Matrix (Fin (a + a')) (Fin (a + a')) (AE F E) := fun t =>
    levM (f ∘ H'.x) (f ∘ H'.y) (f ∘ aE) (f ∘ bE) t.1 (cA σ (t⁻¹).1)
  have hone : M 1 = 1 := by simp only [M, inv_one, Units.val_one, map_one]; exact levM_one
  have hmul : ∀ t t', M (t * t') = M t * M t' := by
    intro t t'
    simp only [M]
    rw [levM_mul hax' hay' hbx' hby', _root_.mul_inv_rev, Units.val_mul, Units.val_mul, map_mul, mul_comm (cA σ _)]
  have hunit : ∀ t, (M t)ᵀ * incM F G.W.J * (M t).map (cA σ) = incM F G.W.J := by
    intro t
    have ha' : G.W.J.map f *ᵥ ((cA σ).toRingHom ∘ (f ∘ H'.y)) = f ∘ aE := by
      change _ *ᵥ (⇑(cA σ) ∘ (f ∘ H'.y)) = _
      rw [hcf, map_comp_mulVec]
    have hb' : G.W.J.map f *ᵥ ((cA σ).toRingHom ∘ (f ∘ H'.x)) = -(f ∘ bE) := by
      change _ *ᵥ (⇑(cA σ) ∘ (f ∘ H'.x)) = _
      rw [hcf, map_comp_mulVec, hbE, hneg, neg_neg]
    have hxJ' : (f ∘ H'.x) ᵥ* G.W.J.map f = (cA σ).toRingHom ∘ (f ∘ bE) := by
      change _ = ⇑(cA σ) ∘ (f ∘ bE)
      rw [map_comp_vecMul, hxJ, hcf]
    have hyJ' : (f ∘ H'.y) ᵥ* G.W.J.map f = -((cA σ).toRingHom ∘ (f ∘ aE)) := by
      change _ = -(⇑(cA σ) ∘ (f ∘ aE))
      rw [map_comp_vecMul, hyJ, hcf, hneg]
    have h1 : t.1 * (cA σ).toRingHom (cA σ (t⁻¹).1) = 1 := by
      change t.1 * cA σ (cA σ (t⁻¹).1) = 1
      rw [cA_cA hσ, Units.mul_inv]
    have h2 : cA σ (t⁻¹).1 * (cA σ).toRingHom t.1 = 1 := by
      change cA σ (t⁻¹).1 * cA σ t.1 = 1
      rw [← map_mul, Units.inv_mul, map_one]
    exact levM_unitary (cA σ).toRingHom (cA_cA hσ) ha' hb' hxJ' hyJ' hax' hay' hbx' hby' h1 h2
  have hfix : ∀ (t : (AE F E)ˣ) (z : Fin d₁ → AE F E), M t *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z := by
    intro t z
    rw [mulVec_mulVec]
    exact congrArg (· *ᵥ z) (levM_mul_fix haι' hbι' _ _)
  refine ⟨homOf σ G.W.J M hone hmul hunit, ?_, ?_, ?_, ?_⟩
  · intro g
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
    have hM : ∀ p q : (AE F E)ˣ → AE F E, Continuous p → Continuous q →
        Continuous fun t => levM (f ∘ H'.x) (f ∘ H'.y) (f ∘ aE) (f ∘ bE) (p t) (q t) := by
      intro p q hp hq
      unfold levM
      exact (continuous_const.add ((hp.sub continuous_const).smul continuous_const)).add
        ((hq.sub continuous_const).smul continuous_const)
    have hc : Continuous (homOf σ G.W.J M hone hmul hunit) := by
      apply continuous_induced_rng.2
      apply Units.continuous_iff.2
      constructor
      · change Continuous fun t => M t
        exact hM _ _ Units.continuous_val (hcA.comp Units.continuous_coe_inv)
      · change Continuous fun t : (AE F E)ˣ => M t⁻¹
        simp only [M, inv_inv]
        exact hM _ _ Units.continuous_coe_inv (hcA.comp Units.continuous_val)
    exact (continuous_mul_right g).comp hc
  · intro t
    refine ⟨levi_matrix_mulVec_first_vector hax' hbx' _ _, levM_mulVec_y hay' hby' _ _, ?_⟩
    change M t * incM F H'.ι = incM F H'.ι * 1
    rw [Matrix.mul_one]
    exact levM_mul_fix haι' hbι' _ _
  · intro x
    rw [ratU, Subgroup.mem_subgroupOf]
    have hE1 := levM_mul (x := H'.x) (y := H'.y) hax hay hbx hby
    refine ⟨⟨levM H'.x H'.y aE bE x.1 (σ (x⁻¹).1), levM H'.x H'.y aE bE (x⁻¹).1 (σ x.1), ?_, ?_⟩, ?_⟩
    · rw [hE1, Units.mul_inv, ← map_mul, Units.inv_mul, map_one, levM_one]
    · rw [hE1, Units.inv_mul, ← map_mul, Units.mul_inv, map_one, levM_one]
    · apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [Matrix.GeneralLinearGroup.map_apply]
      change f (levM H'.x H'.y aE bE x.1 (σ (x⁻¹).1) i j) = M _ i j
      rw [← Matrix.map_apply (f := f), levM_map]
      show _ = levM (f ∘ H'.x) (f ∘ H'.y) (f ∘ aE) (f ∘ bE) (f x.1) (cA σ (f (x⁻¹).1)) i j
      rw [show cA σ (f (x⁻¹).1) = f (σ (x⁻¹).1) from cA_inclR σ _]
  · intro t u hu
    have hsub : unip σ G.W H' ≤ (unip σ G.W H').comap (MulAut.conj (homOf σ G.W.J M hone hmul hunit t)).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro v ⟨hvx, hvι⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      apply Subgroup.subset_closure
      refine ⟨?_, fun z => ?_⟩
      · change (M t * mat v * M t⁻¹) *ᵥ incV F H'.x = incV F H'.x
        rw [← mulVec_mulVec, ← mulVec_mulVec]
        change M t *ᵥ (mat v *ᵥ (M t⁻¹ *ᵥ (f ∘ H'.x))) = f ∘ H'.x
        rw [levi_matrix_mulVec_first_vector hax' hbx', mulVec_smul]
        change M t *ᵥ ((t⁻¹).1 • (mat v *ᵥ incV F H'.x)) = f ∘ H'.x
        rw [hvx, mulVec_smul]
        change (t⁻¹).1 • (M t *ᵥ (f ∘ H'.x)) = f ∘ H'.x
        rw [levi_matrix_mulVec_first_vector hax' hbx', smul_smul, Units.inv_mul, one_smul]
      · obtain ⟨c, hc⟩ := hvι z
        refine ⟨c * t.1, ?_⟩
        change (M t * mat v * M t⁻¹) *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + (c * t.1) • incV F H'.x
        rw [← mulVec_mulVec, ← mulVec_mulVec, hfix, hc, mulVec_add, hfix, mulVec_smul, ← smul_smul]
        change incM F H'.ι *ᵥ z + c • (M t *ᵥ (f ∘ H'.x)) = incM F H'.ι *ᵥ z + c • (t.1 • (f ∘ H'.x))
        rw [levi_matrix_mulVec_first_vector hax' hbx']
    have := hsub hu
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

end Thm

end GlobalTheory.LeviIdeleHom
