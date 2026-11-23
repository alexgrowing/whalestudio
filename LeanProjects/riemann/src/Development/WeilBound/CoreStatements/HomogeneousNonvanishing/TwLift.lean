import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem lift_dense (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (k : ℕ) (w : ℤ_[p] ⊗[ℤ] M) :
    ∃ (y : M) (w' : ℤ_[p] ⊗[ℤ] M), w = 1 ⊗ₜ y + (p : ℤ_[p]) ^ k • w' := by
  refine TensorProduct.induction_on (motive := fun w : ℤ_[p] ⊗[ℤ] M =>
    ∃ (y : M) (w' : ℤ_[p] ⊗[ℤ] M), w = 1 ⊗ₜ y + (p : ℤ_[p]) ^ k • w') w ?_ ?_ ?_
  · exact ⟨0, 0, by simp⟩
  · intro a m
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)
    have ha : a = ((PadicInt.appr a k : ℕ) : ℤ) • (1 : ℤ_[p]) + (p : ℤ_[p]) ^ k • c := by
      rw [smul_eq_mul, ← hc, zsmul_eq_mul, mul_one, Int.cast_natCast]
      ring
    refine ⟨((PadicInt.appr a k : ℕ) : ℤ) • m, c ⊗ₜ[ℤ] m, ?_⟩
    calc a ⊗ₜ[ℤ] m = (((PadicInt.appr a k : ℕ) : ℤ) • (1 : ℤ_[p]) + (p : ℤ_[p]) ^ k • c) ⊗ₜ[ℤ] m :=
          congrArg (· ⊗ₜ[ℤ] m) ha
      _ = 1 ⊗ₜ[ℤ] (((PadicInt.appr a k : ℕ) : ℤ) • m) + (p : ℤ_[p]) ^ k • c ⊗ₜ[ℤ] m := by
          rw [TensorProduct.add_tmul, TensorProduct.smul_tmul ((PadicInt.appr a k : ℕ) : ℤ) (1 : ℤ_[p]) m,
            ← TensorProduct.smul_tmul' ((p : ℤ_[p]) ^ k) c m]
  · rintro w1 w2 ⟨y1, w1', rfl⟩ ⟨y2, w2', rfl⟩
    exact ⟨y1 + y2, w1' + w2', by rw [TensorProduct.tmul_add, smul_add]; abel⟩

theorem lift_sat (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M] (k : ℕ)
    (y : M) (w : ℤ_[p] ⊗[ℤ] M) (h : 1 ⊗ₜ y = (p : ℤ_[p]) ^ k • w) : ∃ e, y = p ^ k • e := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  have hdiv : ∀ i, (p : ℤ) ^ k ∣ b.repr y i := by
    intro i
    have h1 := congrArg (fun z => (b.baseChange ℤ_[p]).repr z i) h
    rw [← PadicInt.pow_p_dvd_int_iff]
    refine Dvd.intro ((b.baseChange ℤ_[p]).repr w i) ?_
    simpa [Module.Basis.baseChange_repr_tmul] using h1.symm
  choose c hc using hdiv
  refine ⟨∑ i, c i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr y]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, ← Nat.cast_pow, natCast_zsmul]

theorem tw_lift : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') := by
  intro p _ O _ L L' _ _ _ _ B B' _ _ _ _ _ φ hO hB
  have htm : ∀ (n : ℕ) (y : L'),
      (1 : ℤ_[p]) ⊗ₜ[ℤ] (n • y) = (n : ℤ_[p]) • ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) := by
    intro n y
    rw [Nat.cast_smul_eq_nsmul]
    exact map_nsmul (TensorProduct.mk ℤ ℤ_[p] L' 1) n y
  have hls : ∀ (c : O) (y : L'),
      LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' c).toAddMonoidHom.toIntLinearMap
        ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) = (1 : ℤ_[p]) ⊗ₜ[ℤ] (c • y) := by
    intro c y
    rw [LinearMap.baseChange_tmul]
    rfl
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Submodule O (L' × L), ∀ k z, z ∈ G k ↔
      ∃ w : ℤ_[p] ⊗[ℤ] L', (1 : ℤ_[p]) ⊗ₜ[ℤ] z.1 = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] z.2) + (p : ℤ_[p]) ^ k • w :=
    ⟨fun k =>
      { carrier := {z | ∃ w : ℤ_[p] ⊗[ℤ] L',
          (1 : ℤ_[p]) ⊗ₜ[ℤ] z.1 = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] z.2) + (p : ℤ_[p]) ^ k • w}
        add_mem' := by
          rintro z1 z2 ⟨w1, hw1⟩ ⟨w2, hw2⟩
          show ∃ w : ℤ_[p] ⊗[ℤ] L', _
          refine ⟨w1 + w2, ?_⟩
          rw [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add,
            hw1, hw2, smul_add]
          abel
        zero_mem' := by
          show ∃ w : ℤ_[p] ⊗[ℤ] L', _
          exact ⟨0, by simp⟩
        smul_mem' := by
          rintro c z ⟨w, hw⟩
          show ∃ w : ℤ_[p] ⊗[ℤ] L', _
          refine ⟨LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' c).toAddMonoidHom.toIntLinearMap w,
            ?_⟩
          rw [Prod.smul_fst, Prod.smul_snd, hO c z.2, ← hls c z.1, hw, map_add, map_smul] },
      fun k z => Iff.rfl⟩
  have hsurj : ∀ k, Function.Surjective ((LinearMap.snd O L' L).comp (G k).subtype) := by
    intro k x
    obtain ⟨y, w, hw⟩ := PositivityTheory.UnitarySelfGeneration.lift_dense p L' k (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x))
    refine ⟨⟨(y, x), (hG k (y, x)).mpr ⟨-w, ?_⟩⟩, rfl⟩
    show (1 : ℤ_[p]) ⊗ₜ[ℤ] y = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • -w
    rw [hw, smul_neg]
    abel
  choose h hh using fun k => Module.projective_lifting_property
    ((LinearMap.snd O L' L).comp (G k).subtype) LinearMap.id (hsurj k)
  obtain ⟨a, ha⟩ : ∃ a : ℕ → L →ₗ[O] L', ∀ k x, ∃ w : ℤ_[p] ⊗[ℤ] L',
      (1 : ℤ_[p]) ⊗ₜ[ℤ] a k x = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • w := by
    refine ⟨fun k => (LinearMap.fst O L' L).comp ((G k).subtype.comp (h k)), fun k x => ?_⟩
    have h2 : (h k x : L' × L).2 = x := LinearMap.congr_fun (hh k) x
    have hmem := (hG k _).mp (h k x).prop
    rw [h2] at hmem
    exact hmem
  refine ⟨⟨a, ?_, ?_, ?_, ?_⟩⟩
  · intro k x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨w, hw⟩ := ha k x
      rw [hy, htm, Nat.cast_pow] at hw
      have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = (p : ℤ_[p]) ^ k • φ.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] y - w) := by
        apply φ.injective
        rw [map_smul, LinearEquiv.apply_symm_apply, smul_sub, hw]
        abel
      exact PositivityTheory.UnitarySelfGeneration.lift_sat p L k x _ h1
    · rintro ⟨y, rfl⟩
      exact ⟨a k y, map_nsmul (a k) (p ^ k) y⟩
  · intro k y
    obtain ⟨x, v, hv⟩ := PositivityTheory.UnitarySelfGeneration.lift_dense p L k (φ.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] y))
    obtain ⟨w, hw⟩ := ha k x
    have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] y = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • φ v := by
      rw [← map_smul, ← map_add, ← hv, LinearEquiv.apply_symm_apply]
    have h2 : (1 : ℤ_[p]) ⊗ₜ[ℤ] (y - a k x) = (p : ℤ_[p]) ^ k • (φ v - w) := by
      rw [TensorProduct.tmul_sub, h1, hw, smul_sub]
      abel
    obtain ⟨e, he⟩ := PositivityTheory.UnitarySelfGeneration.lift_sat p L' k _ _ h2
    exact ⟨x, e, by rw [← he]; abel⟩
  · intro k x y
    obtain ⟨w1, hw1⟩ := ha k x
    obtain ⟨w2, hw2⟩ := ha k y
    rw [← PadicInt.pow_p_dvd_int_iff, Int.cast_sub]
    have e1 : ((B' (a k x) (a k y) : ℤ) : ℤ_[p]) =
        B'.baseChange ℤ_[p] ((1 : ℤ_[p]) ⊗ₜ[ℤ] a k x) ((1 : ℤ_[p]) ⊗ₜ[ℤ] a k y) := by
      rw [LinearMap.BilinForm.baseChange_tmul]
      simp
    have e2 : ((B x y : ℤ) : ℤ_[p]) =
        B'.baseChange ℤ_[p] (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x)) (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] y)) := by
      rw [hB, LinearMap.BilinForm.baseChange_tmul]
      simp
    rw [e1, e2, hw1, hw2]
    refine Dvd.intro (B'.baseChange ℤ_[p] (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x)) w2 +
      B'.baseChange ℤ_[p] w1 (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) + (p : ℤ_[p]) ^ k • w2)) ?_
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro k x
    obtain ⟨w1, hw1⟩ := ha (k + 1) x
    obtain ⟨w2, hw2⟩ := ha k x
    have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] (a (k + 1) x - a k x) =
        (p : ℤ_[p]) ^ k • ((p : ℤ_[p]) • w1 - w2) := by
      rw [TensorProduct.tmul_sub, hw1, hw2, smul_sub, smul_smul, ← pow_succ]
      abel
    obtain ⟨e, he⟩ := PositivityTheory.UnitarySelfGeneration.lift_sat p L' k _ _ h1
    exact ⟨e, by rw [← he]; abel⟩

end PositivityTheory.UnitarySelfGeneration
