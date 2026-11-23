import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmUnitPowFourIdempotentModEight
import Development.AutomorphicArithmetic.WeightCongruences.DvdNormSubOneOfIdempotentInterpolationRelNormOne
import Development.AutomorphicArithmetic.WeightCongruences.NormRootOfUnityQuadraticSubfield

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AdaptedDet

namespace GlobalTheory.AdaptedDetSign

theorem det_interp_gen {E : Type} [Field E] [NumberField E] {r : ℕ} (n : ℕ) (hn : n ≠ 0)
    (e t δ : 𝓞 E) (he0 : e ≠ 0) (he : e * e - e = n * t)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, g *ᵥ v ∈ Λ) (hdet : g.det = (δ : E)) :
    ∃ y : 𝓞 E, ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det =
      ((e * δ + (1 - e) + n * y : 𝓞 E) : E) := by
  classical
  let K := AlgebraicClosure E
  have hinj := (algebraMap E K).injective
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hint : ∀ x : 𝓞 E, IsIntegral ℤ (algebraMap E K (x : E)) := fun x =>
    x.isIntegral_coe.algebraMap
  have hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have := CongruenceDet.isIntegral_root (R := 𝓞 E) (M := 1) one_ne_zero Λ g hfg hspan
      (fun v hv => ⟨g *ᵥ v - v, sub_mem (hg v hv) hv, by simp⟩) μ
      (Polynomial.isRoot_of_mem_roots hμ)
    have h2 : IsIntegral ℤ ((μ - 1) / ((1 : ℕ) : K)) := isIntegral_trans (A := 𝓞 E) _ this
    simpa using h2.add isIntegral_one
  obtain ⟨y, hy, h⟩ := prod_interp (n : K) (algebraMap E K e) (algebraMap E K t)
    (by
      have := congrArg (fun x : 𝓞 E => algebraMap E K (x : E)) he
      simpa using this) (hint e) (hint t) _ hroots
  rw [← det_smul_add _ _ _ (by simpa using he0), ← Matrix.det_eq_prod_roots_charpoly,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet] at h
  set d := ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det with hd
  have hd' : algebraMap E K d = algebraMap E K ((e : E) * (δ : E) + (1 - (e : E))) + n * y := by
    rw [hd, RingHom.map_det]
    have : (algebraMap E K).mapMatrix ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E))
        = algebraMap E K e • (algebraMap E K).mapMatrix g + (1 - algebraMap E K e) • 1 := by
      generalize (e : E) = x
      ext i j
      by_cases h : i = j <;> simp [h, -algebraMap_smul]
    rw [this, h, map_add, map_mul, map_sub, map_one]
  have hy' : IsIntegral ℤ ((d - ((e : E) * (δ : E) + (1 - (e : E)))) / n) := by
    rw [← isIntegral_algebraMap_iff hinj, map_div₀, map_sub, map_natCast, hd',
      add_sub_cancel_left, mul_div_cancel_left₀ _ hn']
    exact hy
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (d - ((e : E) * (δ : E) + (1 - (e : E)))) / n := ⟨⟨_, hy'⟩, rfl⟩
  refine ⟨z, ?_⟩
  have hn'' : (n : E) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : ((e * δ + (1 - e) + n * z : 𝓞 E) : E) =
      (e : E) * (δ : E) + (1 - (e : E)) + n * (z : E) := by simp
  rw [h1, hz]
  field_simp
  ring

theorem norm_one_add_two {E : Type} [Field E] [NumberField E] (u : 𝓞 E) :
    (4 : ℤ) ∣ Algebra.norm ℤ (1 + 2 * u : 𝓞 E) - (1 + 2 * Algebra.trace ℤ (𝓞 E) u) := by
  classical
  have h2 : (2 * u : 𝓞 E) = (2 : ℤ) • u := by simp
  rw [Algebra.norm_eq_matrix_det (RingOfIntegers.basis E), map_add, map_one, h2, map_smul,
    Matrix.det_one_add_smul, Algebra.trace_eq_matrix_trace (RingOfIntegers.basis E)]
  generalize Polynomial.eval (2 : ℤ) _ = c
  exact ⟨c, by ring⟩

theorem det_interp_pm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (A : Matrix (Fin r) (Fin r) E)
    (hinj : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hA : ∀ x, φ (gam x) = A *ᵥ φ x)
    (hdet : A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E))
    (T : D.La →ₗ[ℤ] D.La) (hT : ∀ x, T x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x)) :
    (4 : ℤ) ∣ (LinearMap.toMatrix b b T).det - 1 := by
  have hsm : ∀ (a : 𝓞 E) (x : D.La), φ (a • x) = (a : E) • φ x := fun a x => by
    rw [map_smul]; rfl
  haveI := D.fin
  have hfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  obtain ⟨he0, t, ht⟩ := cmUnit_pow_four_idempotent_mod_eight H
  have h := det_eq_norm b φ hinj hspan T
    (((H.w0 ^ 4 : 𝓞 E) : E) • A + (1 - ((H.w0 ^ 4 : 𝓞 E) : E)) • 1) (by
      intro x
      rw [hT, map_add, map_sub, hsm, hsm, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, hA, Matrix.one_mulVec, sub_smul, one_smul])
  have hst : ∀ v ∈ LinearMap.range φ, A *ᵥ v ∈ LinearMap.range φ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨gam x, hA x⟩
  rcases hdet with hdet | ⟨hdet, h4⟩
  · obtain ⟨y, hy⟩ := det_interp_gen 8 (by norm_num) _ t 1 he0 ht (LinearMap.range φ) A hfg hspan
      hst (by simpa using hdet)
    rw [hy, ← Algebra.coe_norm_int] at h
    have h1 : (H.w0 ^ 4 * 1 + (1 - H.w0 ^ 4) + (8 : ℕ) * y : 𝓞 E) = 1 + 2 * ((4 : ℤ) • y) := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    have h2 := norm_one_add_two ((4 : ℤ) • y)
    rw [Int.cast_injective h, h1]
    rw [map_zsmul, smul_eq_mul] at h2
    omega
  · obtain ⟨m, hm, hpow⟩ := hdet
    have hi : IsIntegral ℤ A.det := IsIntegral.of_pow hm (hpow ▸ isIntegral_one)
    obtain ⟨δ, hδ⟩ : ∃ δ : 𝓞 E, (δ : E) = A.det := ⟨⟨_, hi⟩, rfl⟩
    obtain ⟨y, hy⟩ := det_interp_gen 8 (by norm_num) _ t δ he0 ht (LinearMap.range φ) A hfg hspan hst hδ.symm
    rw [hy, ← Algebra.coe_norm_int] at h
    have hrt : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hN := UpperTheory.norm_root_of_unity_quadratic_subfield E (H.rt : E) H.d H.d_prime (by have := H.d_mod; omega) hrt h4 (δ : E)
      ⟨m, hm, by rw [hδ, hpow]⟩
    have hw : ((H.w0 ^ 4 : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(H.rt : E)} := by
      have h2 : (H.w0 : E) = (1 + (H.rt : E)) / ((2 : ℕ) : E) := by
        have h3 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
          have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
          rwa [map_mul, map_add, map_one, map_ofNat] at this
        rw [← h3]
        push_cast
        ring
      have h4' : ((H.w0 ^ 4 : 𝓞 E) : E) = (H.w0 : E) ^ 4 := by push_cast; rfl
      rw [h4', h2]
      exact pow_mem (div_mem (add_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self _ _)) (natCast_mem _ 2)) 4
    have h8 := UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one E _ 8 _ t δ y hw ht hN
    rw [Int.cast_injective h]
    exact (show (4 : ℤ) ∣ ((8 : ℕ) : ℤ) by norm_num).trans h8

theorem blocks_det_mod_four : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (g r : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (A : Matrix (Fin r) (Fin r) E), (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a, φ (gam a) = A *ᵥ φ a) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ i j, (8 : ℤ) ∣ N (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ N (Sum.inr i) (Sum.inl j)) ∧ (4 : ℤ) ∣ N.toBlocks₁₁.det - 1 := by
  intro E _ _ _ H D g r bas gam N φ A ⟨hl, hr⟩ hinj hspan hA hdet hN
  classical
  let π : D.La →+ (Fin g ⊕ Fin g → ZMod 8) :=
    { toFun := fun x u => ((bas.symm x u : ℤ) : ZMod 8)
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have hπ : ∀ x u, π x u = ((bas.symm x u : ℤ) : ZMod 8) := fun _ _ => rfl
  have h8 : ∀ x, π ((8 : ℕ) • x) = 0 := fun x => by
    rw [map_nsmul]
    ext u
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hπb : ∀ v u, π (bas (Pi.single v 1)) u = if u = v then 1 else 0 := fun v u => by
    simp [hπ, Pi.single_apply]

  have he : ∀ x u, π (H.w0 ^ 4 • x) u = Sum.elim (fun _ => π x u) (fun _ => 0) u := by
    intro x u
    obtain ⟨c, rfl⟩ := bas.surjective x
    induction c using Pi.single_induction with
    | zero => cases u <;> simp
    | add a b ha hb => rw [map_add, smul_add, map_add, map_add, Pi.add_apply, ha, hb]; cases u <;> simp
    | single v n =>
      have : (Pi.single v n : Fin g ⊕ Fin g → ℤ) = n • Pi.single v 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this, map_zsmul, smul_comm, map_zsmul, map_zsmul, Pi.smul_apply, Pi.smul_apply]
      cases v with
      | inl k =>
        obtain ⟨e, h⟩ := hl k
        rw [h, map_add, h8, add_zero]
        cases u <;> simp [hπb]
      | inr k =>
        obtain ⟨e, h⟩ := hr k
        rw [h, h8]
        cases u <;> simp [hπb]
  have hN' : ∀ u v, ((N u v : ℤ) : ZMod 8) = π (gam (bas (Pi.single v 1))) u := fun u v => by
    rw [hN, hπ]
  constructor
  · intro i j
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hr j
      have h1 := he (gam (bas (Pi.single (Sum.inr j) 1))) (Sum.inl i)
      rw [← map_smul, h, map_nsmul, h8] at h1
      rw [hN']
      exact h1.symm
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hl j
      have h1 := he (gam (bas (Pi.single (Sum.inl j) 1))) (Sum.inr i)
      rw [← map_smul, h, map_add, map_nsmul, map_add, h8, add_zero] at h1
      rw [hN']
      exact h1
  · let b : Module.Basis (Fin g ⊕ Fin g) ℤ D.La := (Pi.basisFun ℤ _).map bas
    let T : D.La →ₗ[𝓞 E] D.La :=
      H.w0 ^ 4 • gam.toLinearMap + (LinearMap.id - H.w0 ^ 4 • LinearMap.id)
    have hT : ∀ x, T.restrictScalars ℤ x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x) := fun x => rfl
    have h := det_interp_pm D b gam φ A hinj hspan hA hdet (T.restrictScalars ℤ) hT
    suffices h8 : (8 : ℤ) ∣ N.toBlocks₁₁.det - (LinearMap.toMatrix b b (T.restrictScalars ℤ)).det by
      omega
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    rw [Int.cast_sub, sub_eq_zero, ← eq_intCast (Int.castRingHom (ZMod 8)),
      ← eq_intCast (Int.castRingHom (ZMod 8)), RingHom.map_det, RingHom.map_det]
    have hent : ∀ u v, (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) u v =
        π (T.restrictScalars ℤ (bas (Pi.single v 1))) u := fun u v => by
      simp [LinearMap.toMatrix_apply, b, hπ]
    have hblk : (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) =
        Matrix.fromBlocks ((Int.castRingHom (ZMod 8)).mapMatrix N.toBlocks₁₁)
          (Matrix.of fun i j => (Int.castRingHom (ZMod 8)).mapMatrix
            (LinearMap.toMatrix b b (T.restrictScalars ℤ)) (Sum.inl i) (Sum.inr j)) 0 1 := by
      ext u v
      rcases u with i | i <;> rcases v with j | j
      · rw [hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [Matrix.toBlocks₁₁, hN']
      · rfl
      · rw [hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb]
      · rw [hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb, Matrix.one_apply]
    rw [hblk, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one]

end GlobalTheory.AdaptedDetSign
