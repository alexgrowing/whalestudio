import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockComplementLattice
open GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.StableLattice

theorem exists_matrix_of_saturated {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {n : ℕ} (L : Submodule O (Fin n → O))
    (hL : ∀ (c : O) (v : Fin n → O), c ≠ 0 → c • v ∈ L → v ∈ L) :
    ∃ (m : ℕ) (B : Matrix (Fin n) (Fin m) O) (P : Matrix (Fin m) (Fin n) O),
      P * B = 1 ∧ ∀ v, v ∈ L ↔ B.mulVec (P.mulVec v) = v := by
  have : Module.IsTorsionFree O ((Fin n → O) ⧸ L) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c x hx
    obtain ⟨v, rfl⟩ := L.mkQ_surjective x
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hL c v hc hx
  obtain ⟨s, hs⟩ := Module.projective_lifting_property L.mkQ LinearMap.id L.mkQ_surjective
  have hs' : ∀ x, L.mkQ (s x) = x := fun x => LinearMap.congr_fun hs x
  let p : (Fin n → O) →ₗ[O] L := LinearMap.codRestrict L (LinearMap.id - s ∘ₗ L.mkQ) (by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs',
      sub_self])
  have hp : ∀ x : L, p x = x := by
    intro x
    apply Subtype.ext
    have : L.mkQ (x : Fin n → O) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact x.2
    simp only [p, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, this, map_zero, sub_zero]
  let e := (Module.finBasis O L).equivFun
  refine ⟨Module.finrank O L, LinearMap.toMatrix' (L.subtype ∘ₗ e.symm.toLinearMap),
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ p), ?_, fun v => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro u
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hp, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · rw [← Matrix.toLin'_apply, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix',
      Matrix.toLin'_toMatrix']
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    constructor
    · intro hv
      exact congrArg Subtype.val (hp ⟨v, hv⟩)
    · intro hv
      rw [← hv]
      exact (p v).2

theorem exists_integral_model (O Γ : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [Group Γ] [TopologicalSpace Γ] (n a : ℕ)
    (r : Γ →* GL (Fin n) O) (hr : LatticeContinuous r)
    (W : Submodule (FractionRing O) (Fin n → FractionRing O))
    (hW : ∀ g, ∀ v ∈ W, fracRep r g v ∈ W) (ha : Module.finrank (FractionRing O) W = a) :
    ∃ (ρ : Γ →* GL (Fin a) O)
      (k : (Fin a → FractionRing O) →ₗ[FractionRing O] (Fin n → FractionRing O)),
      LatticeContinuous ρ ∧ Function.Injective k ∧ LinearMap.range k = W ∧
        ∀ g v, fracRep r g (k v) = k (fracRep ρ g v) := by
  set φ := algebraMap O (FractionRing O) with hφ
  have hφi : Function.Injective φ := IsFractionRing.injective O (FractionRing O)
  let c : (Fin n → O) →ₗ[O] (Fin n → FractionRing O) :=
    (Algebra.linearMap O (FractionRing O)).compLeft (Fin n)
  have hc : ∀ v, c v = φ ∘ v := fun v => rfl
  let L : Submodule O (Fin n → O) := (W.restrictScalars O).comap c
  have hLm : ∀ v, v ∈ L ↔ φ ∘ v ∈ W := fun v => Iff.rfl
  have hsm : ∀ (x : O) (v : Fin n → O), φ ∘ (x • v) = φ x • (φ ∘ v) := by
    intro x v; funext i; simp
  obtain ⟨m, B, P, hPB, hL⟩ := exists_matrix_of_saturated L (by
    intro x v hx hv
    rw [hLm, hsm] at hv
    rw [hLm]
    exact (W.smul_mem_iff (by simpa using (map_ne_zero_iff φ hφi).2 hx)).1 hv)
  have hfr : ∀ {b : ℕ} (σ : Γ →* GL (Fin b) O) g v, fracRep σ g v =
      (((σ g : GL (Fin b) O) : Matrix (Fin b) (Fin b) O).map φ).mulVec v := fun σ g v => rfl
  have hmv : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) O) (v : Fin q → O),
      φ ∘ A.mulVec v = (A.map φ).mulVec (φ ∘ v) := by
    intro p q A v; funext i; exact RingHom.map_mulVec φ A v i
  have hBL : ∀ u, B.mulVec u ∈ L := by
    intro u
    rw [hL, Matrix.mulVec_mulVec u P B, hPB, Matrix.one_mulVec]
  have hst : ∀ g, B * (P * (r g : Matrix (Fin n) (Fin n) O) * B) =
      (r g : Matrix (Fin n) (Fin n) O) * B := by
    intro g
    apply Matrix.ext_of_mulVec_single
    intro j
    have h1 : (r g : Matrix (Fin n) (Fin n) O).mulVec (B.mulVec (Pi.single j 1)) ∈ L := by
      rw [hLm, hmv, ← hfr]
      exact hW g _ ((hLm _).1 (hBL _))
    have h2 := (hL _).1 h1
    simp only [← Matrix.mulVec_mulVec]
    exact h2
  let k : (Fin m → FractionRing O) →ₗ[FractionRing O] (Fin n → FractionRing O) :=
    (B.map φ).mulVecLin
  have hk : ∀ v, k v = (B.map φ).mulVec v := fun v => rfl
  have hki : Function.Injective k := by
    apply Function.LeftInverse.injective (g := (P.map φ).mulVec)
    intro v
    rw [hk, Matrix.mulVec_mulVec, ← Matrix.map_mul, hPB, Matrix.map_one _ (map_zero φ) (map_one φ),
      Matrix.one_mulVec]
  have hkr : LinearMap.range k = W := by
    apply le_antisymm
    · rw [Matrix.range_mulVecLin, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have := (hLm _).1 (hBL (Pi.single j 1))
      rw [Matrix.mulVec_single_one] at this
      exact this
    · intro w hw
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
        (nonZeroDivisors O) (S := FractionRing O) w
      choose v hv using hd
      have hd0 : φ (d : O) ≠ 0 := (map_ne_zero_iff φ hφi).2 (nonZeroDivisors.coe_ne_zero d)
      have hvw : φ ∘ v = φ (d : O) • w := by
        funext i
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
        rw [hφ, hv i, Algebra.smul_def]
      have hvL : v ∈ L := by rw [hLm, hvw]; exact W.smul_mem _ hw
      rw [← (LinearMap.range k).smul_mem_iff hd0, ← hvw, ← (hL v).1 hvL, hmv]
      exact ⟨_, hk _⟩
  obtain rfl : m = a := by
    rw [← ha, ← hkr, LinearMap.finrank_range_of_inj hki, Module.finrank_fin_fun]
  let ρ₀ : Γ →* Matrix (Fin m) (Fin m) O :=
    { toFun := fun g => P * (r g : Matrix (Fin n) (Fin n) O) * B
      map_one' := by rw [map_one, Units.val_one, Matrix.mul_one, hPB]
      map_mul' := by
        intro g h
        rw [Matrix.mul_assoc (P * _) B, hst, map_mul, Units.val_mul]
        simp only [Matrix.mul_assoc] }
  refine ⟨ρ₀.toHomUnits, k, ?_, hki, hkr, fun g v => ?_⟩
  · exact (continuous_const.matrix_mul hr).matrix_mul continuous_const
  · rw [hfr, hfr, hk, hk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      ← Matrix.map_mul, ← hst g]
    rfl

end GlobalTheory.StableLattice
