import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.Cover

open Matrix

theorem isPosDef_toReal_of_pos {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y) (hp : ∀ x, x ≠ 0 → 0 < β x x) :
    IsPosDef (toReal β) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let GZ : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℤ := fun i j => β (b i) (b j)
  let G : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℝ := GZ.map (Int.cast : ℤ → ℝ)
  have hval : ∀ v : Module.Free.ChooseBasisIndex ℤ X → ℤ,
      β (∑ i, v i • b i) (∑ i, v i • b i) = v ⬝ᵥ (GZ *ᵥ v) := fun v => by
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, GZ,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hx : ∀ v : Module.Free.ChooseBasisIndex ℤ X → ℤ, v ≠ 0 → ∑ i, v i • b i ≠ 0 := fun v hv h0 =>
    hv (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent v h0 i)
  have hcast : ∀ c : Module.Free.ChooseBasisIndex ℤ X → ℤ,
      (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) = ((c ⬝ᵥ (GZ *ᵥ c) : ℤ) : ℝ) := fun c => by
    simp [dotProduct, mulVec, G]
  have hG : G.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star ((β (b j) (b i) : ℤ) : ℝ) = ((β (b i) (b j) : ℤ) : ℝ)
    rw [star_trivial, hs]
  have hpsd : G.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hG ?_
    intro x
    have hd : DenseRange (Pi.map (fun (_ : Module.Free.ChooseBasisIndex ℤ X) (q : ℚ) => (q : ℝ))) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    rw [star_trivial]
    refine hd.induction_on (p := fun y => 0 ≤ y ⬝ᵥ (G *ᵥ y)) x ?_ ?_
    · refine isClosed_le continuous_const ?_
      simp only [dotProduct, mulVec]
      fun_prop
    · intro q
      obtain ⟨⟨d, hd0⟩, hq⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
      choose c hc using hq
      have hd1 : (d : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd0
      have e : (fun i => (c i : ℝ)) = (d : ℝ) • Pi.map (fun (_ : Module.Free.ChooseBasisIndex ℤ X) (q : ℚ) => (q : ℝ)) q := by
        funext i
        have h1 : (c i : ℚ) = (d : ℚ) * q i := by simpa using hc i
        have h2 : ((c i : ℚ) : ℝ) = (((d : ℚ) * q i : ℚ) : ℝ) := by rw [h1]
        simpa using h2
      have h3 : (0 : ℝ) ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) := by
        rw [hcast]
        by_cases hc0 : c = 0
        · simp [hc0]
        · rw [← hval]; exact_mod_cast (hp _ (hx c hc0)).le
      rw [e, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc] at h3
      exact (mul_nonneg_iff_of_pos_left (mul_self_pos.mpr hd1)).mp h3
  have hdef : ∀ c : Module.Free.ChooseBasisIndex ℤ X → ℝ, c ≠ 0 → 0 < c ⬝ᵥ (G *ᵥ c) := by
    intro c hc
    have h0 := hpsd.dotProduct_mulVec_nonneg c
    rw [star_trivial] at h0
    refine h0.lt_of_ne fun h1 => ?_
    have h2 : G *ᵥ c = 0 := by
      have := (hpsd.dotProduct_mulVec_zero_iff c).1
      rw [star_trivial] at this
      exact this h1.symm
    have h3 : G.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc, h2⟩
    have h4 : GZ.det = 0 := by
      have : ((GZ.det : ℤ) : ℝ) = G.det := (Int.castRingHom ℝ).map_det GZ
      exact_mod_cast this.trans h3
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h4
    have := hp _ (hx v hv)
    rw [hval, hv0, dotProduct_zero] at this
    exact lt_irrefl _ this
  refine (isPosDef_iff_basis b _).2 fun c hc => (hdef c hc).trans_eq ?_
  have hGij : ∀ i j, G i j = ((β (b i) (b j) : ℤ) : ℝ) := fun _ _ => rfl
  simp only [dotProduct, mulVec, hGij, toReal_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Poinc.Cover

namespace GlobalTheory.Poinc.Cover

theorem coeff_int {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hmem : ∀ i, γ i ∈ balForms bar X)
    (hb : IsPartOfBasis fun i => (⟨γ i, hmem i⟩ : balForms bar X)) {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (hs : toReal β = ∑ i, c i • toReal (γ i)) :
    ∃ n : Fin m → ℤ, ∀ i, c i = n i := by
  classical
  obtain ⟨k, bb, hbb⟩ := hb
  refine ⟨fun i => bb.coord (Sum.inl i) ⟨β, hβ⟩, fun i => ?_⟩
  let v : Option (Fin m) → balForms bar X := fun o => o.elim ⟨β, hβ⟩ fun i => ⟨γ i, hmem i⟩
  let w : Option (Fin m) → ℝ := fun o => o.elim (-1) c
  have h : ∑ o, w o • toReal ((balForms bar X).subtype (v o)) = 0 := by
    rw [Fintype.sum_option]
    simp only [w, v, Option.elim, Submodule.subtype_apply]
    rw [← hs]; simp
  have := sum_mul_eq_zero_of_sum_toReal (j := (balForms bar X).subtype) Subtype.val_injective
    (bb.coord (Sum.inl i)) h
  rw [Fintype.sum_option] at this
  simp only [w, v, Option.elim] at this
  have hc : ∀ i' : Fin m, bb.coord (Sum.inl i) ⟨γ i', hmem i'⟩ = if i' = i then 1 else 0 := fun i' => by
    rw [show (⟨γ i', hmem i'⟩ : balForms bar X) = bb (Sum.inl i') from (hbb i').symm, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h' : i' = i
    · simp [h']
    · simp [h', Ne.symm h']
  simp only [hc] at this
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  linarith

theorem exists_cone : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X →
    ∀ β ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < β x x) → ∃ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (k : ℕ)
      (c : Fin r → ℕ), IsCone bar φ γ ∧ 0 < k ∧ (∀ j, 0 < c j) ∧ k • β = ∑ j, c j • γ j := by
  intro O _ bar φ X _ _ _ _ _ _ hF β hβ hp
  classical
  have hB : toReal β ∈ psdCone bar X :=
    (isPosDef_toReal_of_pos hβ.1 hp).mem_psdCone (toReal_mem hβ)
  obtain ⟨m, γ, c, hγ, hc, hsum⟩ := hF.cover _ hB
  obtain ⟨nZ, hnZ⟩ := coeff_int hγ.mem hγ.basis hβ hsum
  have hn0 : ∀ i, 0 ≤ nZ i := fun i => by exact_mod_cast (hnZ i) ▸ hc i
  let n : Fin m → ℕ := fun i => (nZ i).toNat
  have hn : ∀ i, ((n i : ℤ) : ℝ) = c i := fun i => by simp [n, Int.toNat_of_nonneg (hn0 i), hnZ i]
  have heq : β = ∑ i, n i • γ i := LinearMap.ext₂ fun a b => by
    have h1 := LinearMap.congr_fun₂ hsum a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← hn] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact_mod_cast h1
  let S : Finset (Fin m) := Finset.univ.filter fun i => n i ≠ 0
  let e := S.orderEmbOfFin rfl
  refine ⟨S.card, fun j => γ (e j), 1, fun j => n (e j), hF.face _ _ γ e.toEmbedding hγ, one_pos,
    fun j => Nat.pos_of_ne_zero (Finset.mem_filter.1 (S.orderEmbOfFin_mem rfl j)).2, ?_⟩
  rw [one_smul, heq]
  have h2 : ∑ i ∈ S, n i • γ i = ∑ i, n i • γ i :=
    Finset.sum_filter_of_ne fun i _ h => fun h0 => h (by rw [h0, zero_smul])
  have h3 := Finset.sum_map (Finset.univ : Finset (Fin S.card)) e.toEmbedding fun i => n i • γ i
  rw [Finset.map_orderEmbOfFin_univ S rfl] at h3
  rw [← h2, h3]
  rfl

end GlobalTheory.Poinc.Cover
