import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedTensorIntNumberField

noncomputable section
namespace GlobalTheory.UPel.HT.Gen

open NumberField
open scoped TensorProduct

theorem GDatum.O_nontrivial (G : GDatum) : Nontrivial G.O := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have h1 := G.rankO
  rw [Module.finrank_zero_of_subsingleton] at h1
  have : 0 < G.m ^ 2 * Module.finrank ℚ G.F := Nat.mul_pos (pow_pos G.m_pos 2) Module.finrank_pos
  omega

theorem GDatum.tmul_one_injective (G : GDatum) : Function.Injective (fun o : G.O => (1 : ℚ) ⊗ₜ[ℤ] o) := by
  haveI := G.freeO
  have := Algebra.TensorProduct.includeRight_injective (R := ℤ) (A := ℚ) (B := G.O)
    (algebraMap ℤ ℚ).injective_int
  exact fun a b h => this h

theorem GDatum.exists_smul_eq_tmul (G : GDatum) (z : ℚ ⊗[ℤ] G.O) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ x : G.O, N • z = (1 : ℚ) ⊗ₜ x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q o =>
    refine ⟨q.den, by exact_mod_cast q.den_nz, q.num • o, ?_⟩
    have : ((q.den : ℤ) • q) = (q.num : ℤ) • (1 : ℚ) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]; push_cast; exact Rat.den_mul_eq_num q
    rw [TensorProduct.smul_tmul', this, TensorProduct.smul_tmul]
  | add x y ihx ihy =>
    obtain ⟨N1, h1, x1, e1⟩ := ihx
    obtain ⟨N2, h2, x2, e2⟩ := ihy
    refine ⟨N1 * N2, mul_ne_zero h1 h2, N2 • x1 + N1 • x2, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm N1 N2 x, e1, e2, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]

theorem GDatum.algebraMap_injective (G : GDatum) : Function.Injective (algebraMap (𝓞 G.F) G.O) := by
  haveI := G.freeO
  haveI := GDatum.O_nontrivial G
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hI : (RingHom.ker (algebraMap (𝓞 G.F) G.O)).comap (algebraMap ℤ (𝓞 G.F)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem h0 hc (Algebra.IsIntegral.isIntegral c)
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply] at hk
  have h2 : k • (1 : G.O) = 0 := by rw [zsmul_eq_mul, mul_one]; simpa using hk
  exact one_ne_zero ((smul_eq_zero.mp h2).resolve_left hk0)

theorem GDatum.smul_eq_zero_int (G : GDatum) {N : ℤ} (hN : N ≠ 0) {z : ℚ ⊗[ℤ] G.O} (h : N • z = 0) : z = 0 := by
  rw [← Int.cast_smul_eq_zsmul ℚ] at h
  exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast hN)

theorem GDatum.central_idem (G : GDatum) (e : ℚ ⊗[ℤ] G.O) (he : IsIdempotentElem e)
    (hc : ∀ y, e * y = y * e) : e = 0 ∨ e = 1 := by
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G e
  have hxc : ∀ y : G.O, x * y = y * x := by
    intro y
    apply GDatum.tmul_one_injective G
    have e1 : (1:ℚ) ⊗ₜ[ℤ] (x*y) = N • (e * (1 ⊗ₜ y)) := by
      rw [← smul_mul_assoc, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e2 : (1:ℚ) ⊗ₜ[ℤ] (y*x) = N • ((1 ⊗ₜ y) * e) := by
      rw [← mul_smul_comm, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    show (1:ℚ) ⊗ₜ[ℤ] (x*y) = (1:ℚ) ⊗ₜ[ℤ] (y*x)
    rw [e1, e2, hc]
  obtain ⟨c, k, hk, hkc⟩ := G.central x hxc
  set a := algebraMap (𝓞 G.F) G.O c with ha
  set M := N * k with hMdef
  have hM0 : M ≠ 0 := mul_ne_zero hN hk
  have hM : M • e = (1:ℚ) ⊗ₜ[ℤ] a := by
    rw [hMdef, mul_comm, mul_smul, hx, ← TensorProduct.tmul_smul, hkc]
  have hsq : (1:ℚ) ⊗ₜ[ℤ] (a * a) = (1:ℚ) ⊗ₜ[ℤ] (M • a) := by
    calc (1:ℚ) ⊗ₜ[ℤ] (a * a) = ((1:ℚ) ⊗ₜ[ℤ] a) * ((1:ℚ) ⊗ₜ[ℤ] a) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      _ = (M • e) * (M • e) := by rw [hM]
      _ = M • (M • (e * e)) := by rw [smul_mul_assoc, mul_smul_comm]
      _ = M • ((1:ℚ) ⊗ₜ[ℤ] a) := by rw [he.eq, hM]
      _ = _ := by rw [TensorProduct.tmul_smul]
  have haa : a * a = M • a := GDatum.tmul_one_injective G hsq
  have hc2 : c * (c - (M : 𝓞 G.F)) = 0 := by
    apply GDatum.algebraMap_injective G
    rw [map_mul, map_sub, map_intCast, map_zero, mul_sub, sub_eq_zero, ← ha, haa, zsmul_eq_mul]
    exact Int.cast_comm M a
  rcases mul_eq_zero.mp hc2 with h | h
  · left
    apply GDatum.smul_eq_zero_int G hM0
    rw [hM, ha, h, map_zero, TensorProduct.tmul_zero]
  · right
    rw [sub_eq_zero] at h
    have : M • (e - 1) = 0 := by
      rw [smul_sub, hM, ha, h, map_intCast, Algebra.TensorProduct.one_def, ← TensorProduct.tmul_smul,
        zsmul_eq_mul, mul_one, sub_self]
    exact sub_eq_zero.mp (GDatum.smul_eq_zero_int G hM0 this)

theorem isSimpleRing_of_central_idem {R : Type} [Ring R] [IsSemisimpleRing R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → (∀ y, e * y = y * e) → e = 0 ∨ e = 1) : IsSimpleRing R := by
  obtain ⟨n, D, d, _, hd, ⟨φ⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  have hne : ∀ i, (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) ≠ 0 := fun i => by
    haveI := hd i
    exact one_ne_zero
  obtain _ | _ | n := n
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_pair_ne R
    exact hab (φ.injective (Subsingleton.elim _ _))
  · haveI : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    exact IsSimpleRing.of_ringEquiv (φ.trans (RingEquiv.piUnique _)).symm inferInstance
  · exfalso
    let s : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := Pi.single 0 1
    have hs : ∀ y, s * y = y * s := fun y => by
      funext i
      by_cases hi : i = 0
      · subst hi; simp [s]
      · simp [s, Pi.single_apply, hi]
    have hidem : IsIdempotentElem (φ.symm s) := by
      rw [IsIdempotentElem, ← map_mul]; congr 1
      funext i; by_cases hi : i = 0
      · subst hi; simp [s]
      · simp [s, Pi.single_apply, hi]
    rcases h (φ.symm s) hidem (fun y => by
        apply φ.injective; rw [map_mul, map_mul, RingEquiv.apply_symm_apply, hs]) with h0 | h1
    · have : s = 0 := by rw [← map_zero φ.symm] at h0; exact φ.symm.injective h0
      exact hne 0 (by simpa [s] using congr_fun this 0)
    · have : s = 1 := by rw [← map_one φ.symm] at h1; exact φ.symm.injective h1
      have h1' := congr_fun this 1
      simp [s, Pi.single_apply] at h1' <;> exact hne 1 h1'.symm

theorem GDatum.isSemisimpleRing (G : GDatum) : IsSemisimpleRing (ℚ ⊗[ℤ] G.O) := by
  haveI := G.finO
  haveI := G.freeO
  haveI : IsArtinianRing (ℚ ⊗[ℤ] G.O) := IsArtinianRing.of_finite ℚ _
  obtain ⟨q, hq, ⟨Φ⟩⟩ := G.splitSome
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  obtain ⟨k, hk⟩ := IsSemiprimaryRing.isNilpotent (R := ℚ ⊗[ℤ] G.O)
  have hnil : ∀ z ∈ Ring.jacobson (ℚ ⊗[ℤ] G.O), z ^ k = 0 := fun z hz => by
    have := Ideal.pow_mem_pow hz k
    rw [hk, Submodule.zero_eq_bot, Submodule.mem_bot] at this
    exact this
  intro z hz
  rw [Submodule.mem_bot]
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G z
  have hxJ : (1:ℚ) ⊗ₜ[ℤ] x ∈ Ring.jacobson (ℚ ⊗[ℤ] G.O) := hx ▸ zsmul_mem hz N
  have hox : ∀ o : G.O, (o * x) ^ k = 0 := fun o => by
    apply GDatum.tmul_one_injective G
    have hm : ((1:ℚ) ⊗ₜ[ℤ] o) * ((1:ℚ) ⊗ₜ[ℤ] x) ∈ Ring.jacobson (ℚ ⊗[ℤ] G.O) :=
      Ideal.mul_mem_left _ _ hxJ
    have := hnil _ hm
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.TensorProduct.tmul_pow, one_pow] at this
    show (1:ℚ) ⊗ₜ[ℤ] ((o * x) ^ k) = (1:ℚ) ⊗ₜ[ℤ] 0
    rw [this, TensorProduct.tmul_zero]
  haveI : IsReduced (𝓞 G.F ⊗[ℤ] ℤ_[q]) := by
    have h1 : Function.Injective
        ((algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom.toLinearMap.lTensor (𝓞 G.F)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective ℤ_[q] ℚ_[q])
    have h2 : Function.Injective
        ((algebraMap (𝓞 G.F) G.F).toIntAlgHom.toLinearMap.rTensor ℚ_[q]) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective (𝓞 G.F) G.F)
    let f : 𝓞 G.F ⊗[ℤ] ℤ_[q] →ₐ[ℤ] ℚ_[q] ⊗[ℤ] G.F :=
      (Algebra.TensorProduct.comm ℤ G.F ℚ_[q]).toAlgHom.comp
        (Algebra.TensorProduct.map (algebraMap (𝓞 G.F) G.F).toIntAlgHom (algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom)
    have hmap : Function.Injective (Algebra.TensorProduct.map (algebraMap (𝓞 G.F) G.F).toIntAlgHom
        (algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom) := by
      have : ⇑(Algebra.TensorProduct.map (algebraMap (𝓞 G.F) G.F).toIntAlgHom
          (algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom) =
          ((algebraMap (𝓞 G.F) G.F).toIntAlgHom.toLinearMap.rTensor ℚ_[q]) ∘
          ((algebraMap ℤ_[q] ℚ_[q]).toIntAlgHom.toLinearMap.lTensor (𝓞 G.F)) := by
        funext w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => rfl
        | add a b ha hb => simp only [map_add, Function.comp_apply] at ha hb ⊢; rw [ha, hb]
      rw [this]; exact h2.comp h1
    have hf : Function.Injective f := fun a b hab => hmap ((Algebra.TensorProduct.comm ℤ G.F ℚ_[q]).injective hab)
    haveI := GlobalTheory.isReduced_tensor_int_numberField G.F ℚ_[q]
    exact isReduced_of_injective f.toRingHom hf
  set y := Φ (x ⊗ₜ[ℤ] (1 : ℤ_[q])) with hy
  have htr : ∀ w : G.O ⊗[ℤ] ℤ_[q], (Φ w * y).trace = 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul o c =>
      apply IsReduced.eq_zero
      apply Matrix.isNilpotent_trace_of_isNilpotent
      refine ⟨k, ?_⟩
      rw [hy, ← map_mul, ← map_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        Algebra.TensorProduct.tmul_pow, hox, TensorProduct.zero_tmul, map_zero]
    | add a b ha hb => rw [map_add, add_mul, Matrix.trace_add, ha, hb, add_zero]
  have hy0 : y = 0 := by
    ext i j
    have := htr (Φ.symm (Matrix.single j i 1))
    rw [AlgEquiv.apply_symm_apply, Matrix.trace_single_mul, one_smul] at this
    exact this
  have hx0 : x = 0 := by
    have h0 : x ⊗ₜ[ℤ] (1 : ℤ_[q]) = 0 := Φ.injective (hy0.trans (map_zero Φ).symm)
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := ℤ) (S := ℤ) (A := G.O) (B := ℤ_[q])
      (algebraMap ℤ ℤ_[q]).injective_int
    exact hinj (h0.trans (TensorProduct.zero_tmul _ _).symm)
  apply GDatum.smul_eq_zero_int G hN
  rw [hx, hx0, TensorProduct.tmul_zero]

theorem GDatum.isSimpleRing (G : GDatum) : IsSimpleRing (ℚ ⊗[ℤ] G.O) := by
  haveI := GDatum.isSemisimpleRing G
  haveI := GDatum.O_nontrivial G
  haveI : Nontrivial (ℚ ⊗[ℤ] G.O) := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have : (1 : G.O) = 0 := GDatum.tmul_one_injective G (by
      show (1:ℚ) ⊗ₜ[ℤ] (1 : G.O) = (1:ℚ) ⊗ₜ[ℤ] 0
      rw [TensorProduct.tmul_zero]; exact h)
    exact one_ne_zero this
  exact isSimpleRing_of_central_idem (fun e he hc => GDatum.central_idem G e he hc)
