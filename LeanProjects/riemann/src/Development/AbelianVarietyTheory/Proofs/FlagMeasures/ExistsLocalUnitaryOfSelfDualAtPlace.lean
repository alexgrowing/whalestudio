import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingSemiLoc

noncomputable section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.St.G.Unimod

section Abstract

variable {A : Type} [CommRing A] {n : ℕ} (c : A →+* A)

theorem hform_eq (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    hform c J x y = ∑ i, c (x i) * (J *ᵥ y) i := by
  simp only [hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (J g : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    hform c J (g *ᵥ x) (g *ᵥ y) = hform c (cT c g * J * g) x y := by
  have h : (fun i => c ((g *ᵥ x) i)) = g.map c *ᵥ fun i => c (x i) :=
    funext fun i => RingHom.map_mulVec c g x i
  rw [hform_eq, hform_eq]
  change (fun i => c ((g *ᵥ x) i)) ⬝ᵥ _ = (fun i => c (x i)) ⬝ᵥ _
  rw [h, cT, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (g.map c)ᵀ,
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

theorem mulVec_mem {O : Subring A} {P : Matrix (Fin n) (Fin n) A} (hP : ∀ i j, P i j ∈ O)
    {x : Fin n → A} (hx : ∀ i, x i ∈ O) (i : Fin n) : (P *ᵥ x) i ∈ O := by
  rw [Matrix.mulVec, dotProduct]
  exact O.sum_mem fun j _ => mul_mem (hP i j) (hx j)

theorem single_mem (O : Subring A) (j i : Fin n) : (Pi.single j 1 : Fin n → A) i ∈ O := by
  rw [Pi.single_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem exists_orthonormal (hc : ∀ x, c (c x) = x) (O : Subring A) (hO : ∀ x ∈ O, c x ∈ O)
    (hnf : ∀ G : Matrix (Fin n) (Fin n) O, (∀ a b, c.restrict O O hO (G a b) = G b a) → IsUnit G.det →
      ∃ P : Matrix (Fin n) (Fin n) O, IsUnit P.det ∧ G = Pᵀ * P.map (c.restrict O O hO))
    {J : Matrix (Fin n) (Fin n) A} (hJ : IsHerm c J) (hd : IsUnit J.det)
    (Λ : Set (Fin n → A)) (g : GL (Fin n) A) (hg : ∀ x, x ∈ Λ ↔ ∀ i, ((g⁻¹).1 *ᵥ x) i ∈ O)
    (hsd : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, hform c J z y ∈ O) :
    ∃ k : GL (Fin n) A, cT c k.1 * J * k.1 = 1 ∧ ∀ x, x ∈ Λ ↔ ∀ i, ((k⁻¹).1 *ᵥ x) i ∈ O := by
  have hg' : ∀ x, g.1 *ᵥ x ∈ Λ ↔ ∀ i, x i ∈ O := fun x => by
    rw [hg, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  set G := cT c g.1 * J * g.1 with hG
  have hGd : IsUnit G.det := by
    have h1 := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    rw [hG, cT, det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((h1.map c).mul hd).mul h1
  have hcc : ∀ M : Matrix (Fin n) (Fin n) A, cT c (cT c M) = M := fun M => by
    ext i j; exact hc _
  have hGh : cT c G = G := by
    rw [hG, cT_mul, cT_mul, hcc, hJ, Matrix.mul_assoc]
  have h1 : ∀ i j, G i j ∈ O := fun i j => by
    have := (hsd _).1 ((hg' _).2 (single_mem O j)) _ ((hg' _).2 (single_mem O i))
    rw [hform_mulVec, ← hG, hform_eq] at this
    simpa [Pi.single_apply, apply_ite c] using this
  have h2 : ∀ i j, G⁻¹ i j ∈ O := fun i j => by
    have := (hg' (G⁻¹ *ᵥ Pi.single j 1)).1 ((hsd _).2 fun z hz => by
      have e : z = g.1 *ᵥ ((g⁻¹).1 *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e, hform_mulVec, ← hG, hform_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGd,
        Matrix.one_mulVec]
      exact O.sum_mem fun k _ => mul_mem (hO _ ((hg z).1 hz k)) (single_mem O j k)) i
    simpa using this
  let M' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨G i j, h1 i j⟩
  let N' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨G⁻¹ i j, h2 i j⟩
  have h3 : M' * N' = 1 := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    change (M' * N').map O.subtype = Matrix.map 1 O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.mul_nonsing_inv _ hGd
  obtain ⟨P, hP, h⟩ := hnf M' (fun i j => Subtype.ext (congrFun (congrFun hGh j) i))
    (Matrix.isUnit_det_of_right_inverse h3)
  obtain ⟨P, rfl⟩ := (Matrix.isUnit_iff_isUnit_det P).2 hP
  let φ : O →+* A := c.comp O.subtype
  let Q : GL (Fin n) A := Matrix.GeneralLinearGroup.map φ P
  have hQ : ∀ i j, Q.1 i j ∈ O := fun i j => hO _ (P.1 i j).2
  have hQ' : ∀ i j, (Q⁻¹).1 i j ∈ O := fun i j => by
    rw [← map_inv]; exact hO _ ((P⁻¹).1 i j).2
  have hGQ : G = cT c Q.1 * Q.1 := by
    have := congrArg (fun X => Matrix.map X O.subtype) h
    simp only [Matrix.map_mul] at this
    refine this.trans ?_
    congr 1
    ext i j
    exact (hc _).symm
  refine ⟨g * Q⁻¹, ?_, fun x => ?_⟩
  · rw [Units.val_mul, cT_mul]
    calc _ = cT c (Q⁻¹).1 * G * (Q⁻¹).1 := by rw [hG]; simp only [Matrix.mul_assoc]
      _ = cT c (Q.1 * (Q⁻¹).1) * (Q.1 * (Q⁻¹).1) := by
        rw [hGQ, cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, cT_one, Matrix.one_mul]
  · rw [hg, _root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
    refine ⟨fun h => mulVec_mem hQ h, fun h i => ?_⟩
    have := mulVec_mem hQ' h i
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem exists_unitary {O : Subring A} {J : Matrix (Fin n) (Fin n) A} {Λ Λ' : Set (Fin n → A)}
    {k k' : GL (Fin n) A} (hk : cT c k.1 * J * k.1 = 1) (hk' : cT c k'.1 * J * k'.1 = 1)
    (h : ∀ x, x ∈ Λ ↔ ∀ i, ((k⁻¹).1 *ᵥ x) i ∈ O) (h' : ∀ x, x ∈ Λ' ↔ ∀ i, ((k'⁻¹).1 *ᵥ x) i ∈ O) :
    ∃ u ∈ UJ c J, ∀ x, x ∈ Λ ↔ u.1 *ᵥ x ∈ Λ' := by
  refine ⟨k' * k⁻¹, ?_, fun x => ?_⟩
  · change cT c (k' * k⁻¹).1 * J * (k' * k⁻¹).1 = J
    rw [Units.val_mul, cT_mul]
    calc _ = cT c (k⁻¹).1 * (cT c k'.1 * J * k'.1) * (k⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = cT c (k.1 * (k⁻¹).1) * J * (k.1 * (k⁻¹).1) := by
        rw [hk', ← hk, cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]
  · rw [h, h', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]

end Abstract

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem inclE_mem (x : 𝓞 E) : inclE (F := F) (v.adicCompletion F) (x : E) ∈ intV E v :=
  Subring.subset_closure (Or.inl ⟨⟨x, x, rfl⟩, rfl⟩)

theorem one_tmul_mem (a : v.adicCompletionIntegers F) :
    (1 : E) ⊗ₜ[F] (a : v.adicCompletion F) ∈ intV E v :=
  Subring.subset_closure (Or.inr ⟨⟨a, a.2⟩, rfl⟩)

variable (E) in

def baseMap : v.adicCompletionIntegers F →+* intV E v :=
  (((Algebra.TensorProduct.includeRight : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F) :
    v.adicCompletion F →+* E ⊗[F] v.adicCompletion F).comp
      (v.adicCompletionIntegers F).subtype).codRestrict (intV E v) (one_tmul_mem v)

theorem coe_baseMap_algebraMap (s : 𝓞 F) :
    (baseMap E v (algebraMap (𝓞 F) _ s) : E ⊗[F] v.adicCompletion F) =
      inclE (F := F) (v.adicCompletion F) (algebraMap F E (s : F)) := by
  change (1 : E) ⊗ₜ[F] (algebraMap F (v.adicCompletion F) (s : F)) = algebraMap F E (s : F) ⊗ₜ[F] 1
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_inv {s : 𝓞 F} (hs : s ∉ v.asIdeal) : ∃ t ∈ intV E v,
    t * inclE (F := F) (v.adicCompletion F) (algebraMap F E (s : F)) = 1 := by
  obtain ⟨t, ht⟩ :=
    (((SelfDualGenus.isUnit_algebraMap_iff v s).2 hs).map (baseMap E v)).exists_left_inv
  exact ⟨t, t.2, by rw [← coe_baseMap_algebraMap]; exact congrArg Subtype.val ht⟩

theorem exists_frame {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : IsLat L) :
    ∃ g : GL (Fin n) (E ⊗[F] v.adicCompletion F),
      ∀ x, x ∈ loc v L ↔ ∀ i, ((g⁻¹).1 *ᵥ x) i ∈ intV E v := by
  obtain ⟨B, s, hs, h1, h2⟩ := SemiLocalFrame.exists_frame_denominator F E n L hL.1 hL.2 v
  obtain ⟨t, ht, hts⟩ := exists_inv (E := E) v hs
  let g := Matrix.GeneralLinearGroup.map (inclE (F := F) (E := E) (v.adicCompletion F)) B
  refine ⟨g, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨a, ha⟩ := h1 y hy i
      have h3 := mul_mem ht (inclE_mem v a)
      have ha' : (a : E) = _ := ha
      rw [ha', map_mul, ← mul_assoc, hts, one_mul, RingHom.map_mulVec] at h3
      rw [← map_inv]
      exact h3
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, Matrix.mulVec_smul]; exact mul_mem a.2 hx
  · have e : x = g.1 *ᵥ ((g⁻¹).1 *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [e, Matrix.mulVec_eq_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have := Submodule.smul_mem (loc v L) ⟨_, mul_mem (hx j) ht⟩
      (Submodule.subset_span ⟨_, h2 j, rfl⟩)
    convert this using 1
    funext k
    change g.1 k j * ((g⁻¹).1 *ᵥ x) j = (((g⁻¹).1 *ᵥ x) j * t) * inclE (F := F) _ (_ * B.1 k j)
    rw [map_mul, mul_assoc, ← mul_assoc t, hts, one_mul, mul_comm]
    rfl

variable (σ : E →ₐ[F] E)

omit [NumberField E] in
theorem sigR_tmul (x : E) (a : v.adicCompletion F) :
    sigR σ (v.adicCompletion F) (x ⊗ₜ[F] a) = σ x ⊗ₜ[F] a := rfl

omit [NumberField E] in
theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (z : E ⊗[F] v.adicCompletion F) :
    sigR σ (v.adicCompletion F) (sigR σ (v.adicCompletion F) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => rw [sigR_tmul, sigR_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem intV_induction {p : E ⊗[F] v.adicCompletion F → Prop} (h0 : p 0)
    (h1 : ∀ (x : 𝓞 E) (a : v.adicCompletionIntegers F), p ((x : E) ⊗ₜ[F] (a : v.adicCompletion F)))
    (h2 : ∀ x y, p x → p y → p (x + y)) {z : E ⊗[F] v.adicCompletion F} (hz : z ∈ intV E v) :
    p z := by
  let φ := Algebra.TensorProduct.productMap
    ((inclE (F := F) (E := E) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E)).toIntAlgHom
    ((intV E v).subtype.comp (baseMap E v)).toIntAlgHom
  have hφ : ∀ (x : 𝓞 E) (a : v.adicCompletionIntegers F),
      φ (x ⊗ₜ[ℤ] a) = (x : E) ⊗ₜ[F] (a : v.adicCompletion F) := fun x a => by
    change ((x : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (a : v.adicCompletion F)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hle : intV E v ≤ φ.toRingHom.range := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · exact ⟨x ⊗ₜ 1, hφ x 1⟩
    · exact ⟨1 ⊗ₜ ⟨a, ha⟩, hφ 1 ⟨a, ha⟩⟩
  obtain ⟨y, rfl⟩ := hle hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => rwa [map_zero]
  | tmul x a => exact (hφ x a).symm ▸ h1 x a
  | add x y hx hy => rw [map_add]; exact h2 _ _ hx hy

theorem sigR_mem (z : E ⊗[F] v.adicCompletion F) (hz : z ∈ intV E v) :
    sigR σ (v.adicCompletion F) z ∈ intV E v := by
  refine intV_induction v (p := fun z => sigR σ (v.adicCompletion F) z ∈ intV E v) (by simp)
    (fun x a => ?_) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy) hz
  have := mul_mem (inclE_mem v ⟨σ x, map_isIntegral_int σ x.isIntegral_coe⟩) (one_tmul_mem v a)
  convert this using 1
  change _ = (σ x ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (a : v.adicCompletion F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, sigR_tmul]

omit [NumberField F] [NumberField E] in
theorem exists_int_of_fixed (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range) {x : E}
    (hx : IsIntegral ℤ x) (h : σ x = x) : ∃ s : 𝓞 F, algebraMap F E (s : F) = x := by
  obtain ⟨a, rfl⟩ := hfix x h
  exact ⟨⟨a, (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 hx⟩,
    rfl⟩

theorem exists_trace (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    {z : E ⊗[F] v.adicCompletion F} (hz : z ∈ intV E v) :
    ∃ a, (baseMap E v a : E ⊗[F] v.adicCompletion F) = z + sigR σ (v.adicCompletion F) z := by
  refine intV_induction v (p := fun z => ∃ a, (baseMap E v a : E ⊗[F] v.adicCompletion F) =
    z + sigR σ (v.adicCompletion F) z) ⟨0, by simp⟩ (fun x a => ?_) ?_ hz
  · obtain ⟨s, hs⟩ := exists_int_of_fixed σ hfix (x := (x : E) + σ x)
      (x.isIntegral_coe.add (map_isIntegral_int σ x.isIntegral_coe)) (by rw [map_add, hσ, add_comm])
    refine ⟨algebraMap (𝓞 F) _ s * a, ?_⟩
    rw [map_mul, Subring.coe_mul, coe_baseMap_algebraMap, hs, sigR_tmul, ← TensorProduct.add_tmul]
    change (((x : E) + σ x) ⊗ₜ[F] (1 : v.adicCompletion F)) *
      ((1 : E) ⊗ₜ[F] (a : v.adicCompletion F)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, Subring.coe_add, ha, hb, map_add]; ring⟩

theorem exists_isUnit_sub (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (hun : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) :
    ∃ ω : intV E v, IsUnit (ω - (sigR σ (v.adicCompletion F)).restrict _ _ (sigR_mem v σ) ω) := by
  haveI := v.isMaximal
  obtain ⟨w, hw, hwv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 F) (𝓞 E))).1
      (FaithfulSMul.algebraMap_injective _ _)]
    exact bot_le)
  obtain ⟨θ, t, ht, hθ⟩ := hun w hw
  obtain ⟨s, hs⟩ := exists_int_of_fixed σ hfix (x := (((θ - t) * (θ - t) : 𝓞 E) : E))
    (RingOfIntegers.isIntegral_coe _) (by
      change σ (((θ : E) - (t : E)) * ((θ : E) - (t : E))) = ((θ : E) - (t : E)) * ((θ : E) - (t : E))
      rw [ht, map_mul, map_sub, hσ]; ring)
  have hsv : s ∉ v.asIdeal := fun h => by
    rw [← hwv, Ideal.mem_comap,
      show algebraMap (𝓞 F) (𝓞 E) s = (θ - t) * (θ - t) from RingOfIntegers.ext hs] at h
    exact hθ ((hw.isPrime.mem_or_mem h).elim id id)
  refine ⟨⟨_, inclE_mem v θ⟩, isUnit_of_mul_isUnit_left (y := ⟨_, inclE_mem v (θ - t)⟩) ?_⟩
  convert ((SelfDualGenus.isUnit_algebraMap_iff v s).2 hsv).map (baseMap E v)
  apply Subtype.ext
  rw [coe_baseMap_algebraMap, hs]
  change (inclE (F := F) _ (θ : E) - inclE (F := F) _ (σ θ)) * inclE (F := F) _ ((θ - t : 𝓞 E) : E) = _
  rw [← map_sub, ← map_mul, ← ht]
  rfl

theorem normal_form (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (hun : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) (intV E v))
    (hG : ∀ a b, (sigR σ (v.adicCompletion F)).restrict _ _ (sigR_mem v σ) (G a b) = G b a)
    (hd : IsUnit G.det) : ∃ P : Matrix (Fin n) (Fin n) (intV E v), IsUnit P.det ∧
      G = Pᵀ * P.map ((sigR σ (v.adicCompletion F)).restrict _ _ (sigR_mem v σ)) := by
  haveI := SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := SelfDualGenus.finite_residueField_adicCompletionIntegers v
  letI := (baseMap E v).toAlgebra
  have hc : ∀ x : intV E v, (sigR σ (v.adicCompletion F)).restrict _ _ (sigR_mem v σ)
      ((sigR σ (v.adicCompletion F)).restrict _ _ (sigR_mem v σ) x) = x :=
    fun x => Subtype.ext (sigR_sigR v σ hσ x)
  have hgal := exists_isUnit_sub v σ hσ hfix hun
  refine UnramifiedHermitian.exists_eq_transpose_mul_map_of_henselian
    (R₀ := v.adicCompletionIntegers F) _ hc (fun a => Subtype.ext ?_) (fun x hx => ?_) hgal hG hd
  · change σ 1 ⊗ₜ[F] (a : v.adicCompletion F) = 1 ⊗ₜ[F] (a : v.adicCompletion F)
    rw [map_one]
  · obtain ⟨w, hw⟩ := QuadraticEtale.exists_add_eq_one _ hc hgal
    obtain ⟨a, ha⟩ := exists_trace v σ hσ hfix (x * w).2
    refine ⟨a, ?_⟩
    have : baseMap E v a = x * w +
        (sigR σ (v.adicCompletion F)).restrict _ _ (sigR_mem v σ) (x * w) := Subtype.ext ha
    rw [map_mul, hx, ← mul_add, hw, mul_one] at this
    exact this

end Local

theorem exists_unitary_of_selfDualAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ (v : HeightOneSpectrum (𝓞 F)), SelfDualAt cm.sig J v L → SelfDualAt cm.sig J v M → ∃ h ∈ UPts cm.sig J (v.adicCompletion F), ∀ x, x ∈ loc v L ↔ h.1 *ᵥ x ∈ loc v M := by
  intro F E _ _ _ _ _ _ cm n J hJ hd L M hL hM v sL sM
  have hσ : ∀ x, cm.sig (cm.sig x) = x := fun x => star_star x
  have hnf := normal_form v cm.sig hσ (fun x hx => (cm.fixed x).1 hx) cm.cmUnram.2.2 (n := n)
  have hJ' : IsHerm (sigR cm.sig (v.adicCompletion F))
      (J.map (inclE (F := F) (v.adicCompletion F))) := by
    ext i j
    exact congrArg (inclE (F := F) (v.adicCompletion F)) (congrFun (congrFun hJ i) j)
  have hd' : IsUnit (J.map (inclE (F := F) (v.adicCompletion F))).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hd.isUnit.map _
  obtain ⟨g, hg⟩ := exists_frame v hL
  obtain ⟨g', hg'⟩ := exists_frame v hM
  obtain ⟨k, hk, h⟩ := exists_orthonormal _ (sigR_sigR v _ hσ) _ (sigR_mem v _) hnf hJ' hd'
    (loc v L) g hg sL
  obtain ⟨k', hk', h'⟩ := exists_orthonormal _ (sigR_sigR v _ hσ) _ (sigR_mem v _) hnf hJ' hd'
    (loc v M) g' hg' sM
  exact exists_unitary _ hk hk' h h'

end GlobalTheory.St.G.Unimod

end
