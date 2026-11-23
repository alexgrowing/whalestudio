import Mathlib
import Formalism.PeriodIntegrals.XgCTieBr

open scoped ComplexOrder Matrix

noncomputable section

namespace PI.XgCTieBrWork.Chars

variable {G : Type} [Group G]

def toGL {k : Type} [Field k] {n : ℕ} (ρ : Representation k G (Fin n → k)) : G →* GL (Fin n) k :=
  (Units.map (LinearMap.toMatrixAlgEquiv' (R := k) (n := Fin n)).toMonoidHom).comp ρ.toHomUnits

def ofGL {k : Type} [Field k] {n : ℕ} (ρ : G →* GL (Fin n) k) : Representation k G (Fin n → k) :=
  (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toMonoidHom.comp ((Units.coeHom _).comp ρ)

theorem char_eq_trace {k : Type} [Field k] {n : ℕ} (ρ : Representation k G (Fin n → k)) (x : G) :
    ρ.character x = Matrix.trace (LinearMap.toMatrix' (ρ x)) := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)),
    LinearMap.toMatrix_eq_toMatrix']

theorem trace_toGL {k : Type} [Field k] {n : ℕ} (ρ : Representation k G (Fin n → k)) (x : G) :
    Matrix.trace ((toGL ρ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = ρ.character x := by
  rw [char_eq_trace]
  rfl

theorem char_ofGL {k : Type} [Field k] {n : ℕ} (ρ : G →* GL (Fin n) k) (x : G) :
    (ofGL ρ).character x = Matrix.trace ((ρ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [char_eq_trace]
  show Matrix.trace (LinearMap.toMatrix' (Matrix.toLin' _)) = _
  rw [LinearMap.toMatrix'_toLin']
  rfl

theorem trace_map {k k' : Type} [Field k] [Field k'] {n : ℕ} (f : k →+* k') (M : Matrix (Fin n) (Fin n) k) :
    Matrix.trace (M.map f) = f (Matrix.trace M) := by
  simp [Matrix.trace, map_sum]

theorem star_trace_inv [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) (g : G) :
    star (Matrix.trace ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) =
      Matrix.trace ((ρ g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  set A : G → Matrix (Fin n) (Fin n) ℂ := fun h => ((ρ h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hA
  have hmul : ∀ a b, A a * A b = A (a * b) := fun a b => by simp [hA, map_mul]
  have hone : A 1 = 1 := by simp [hA]
  have hinj : ∀ h, Function.Injective (A h).mulVec := fun h v w hvw => by
    have := congrArg (A h⁻¹).mulVec hvw
    simpa [Matrix.mulVec_mulVec, hmul, hone] using this
  set H : Matrix (Fin n) (Fin n) ℂ := ∑ h, (A h)ᴴ * A h with hH
  have hpd : H.PosDef :=
    Matrix.posDef_sum Finset.univ_nonempty fun h _ => Matrix.PosDef.conjTranspose_mul_self _ (hinj h)
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hpd.isUnit
  have key : (A g)ᴴ * H * A g = H := by
    rw [hH, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    rw [Equiv.coe_mulRight, ← hmul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have e1 : (A g)ᴴ * H = H * A g⁻¹ := by
    calc (A g)ᴴ * H = (A g)ᴴ * H * (A g * A g⁻¹) := by rw [hmul, mul_inv_cancel, hone, Matrix.mul_one]
      _ = H * A g⁻¹ := by rw [← Matrix.mul_assoc, key]
  have key2 : (A g)ᴴ = H * A g⁻¹ * H⁻¹ := by
    calc (A g)ᴴ = (A g)ᴴ * H * H⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = H * A g⁻¹ * H⁻¹ := by rw [e1]
  show star (Matrix.trace (A g)) = Matrix.trace (A g⁻¹)
  rw [← Matrix.trace_conjTranspose, key2, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

theorem irr_of_finrank_one {k : Type} [Field k] [Finite G] [NeZero (Nat.card G : k)] {V : Type} [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (h : Module.finrank k (Representation.IntertwiningMap ρ ρ) = 1) :
    ρ.IsIrreducible := by
  classical
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hE : Module.finrank k (Module.End (MonoidAlgebra k G) ρ.asModule) = 1 := by
    rw [← (Representation.IntertwiningMap.equivAlgEnd ρ).toLinearEquiv.finrank_eq]
    exact h
  haveI : Nontrivial ρ.asModule := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    haveI : Subsingleton (Module.End (MonoidAlgebra k G) ρ.asModule) :=
      ⟨fun f g => LinearMap.ext fun x => Subsingleton.elim _ _⟩
    rw [Module.finrank_zero_of_subsingleton] at hE
    exact zero_ne_one hE
  have h1 : (1 : Module.End (MonoidAlgebra k G) ρ.asModule) ≠ 0 := one_ne_zero
  refine { eq_bot_or_eq_top := fun N => ?_ }
  obtain ⟨q, hq⟩ := exists_isCompl N
  set e : Module.End (MonoidAlgebra k G) ρ.asModule := N.subtype ∘ₗ Submodule.projectionOnto N q hq with he
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End (MonoidAlgebra k G) ρ.asModule) h1).mp hE e
  have hcx : ∀ x : ρ.asModule, e x = c • x := fun x => by
    rw [← hc, LinearMap.smul_apply, Module.End.one_apply]
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  have hex : e x = x := by
    rw [he, LinearMap.comp_apply]
    have := Submodule.projectionOnto_apply_left hq ⟨x, hxN⟩
    show N.subtype (Submodule.projectionOnto N q hq ((⟨x, hxN⟩ : N) : ρ.asModule)) = x
    rw [this]
    rfl
  have hc1 : c = 1 := by
    by_contra hne
    have h0 : (c - 1) • x = 0 := by rw [sub_smul, one_smul, ← hcx, hex, sub_self]
    have h2 : (c - 1)⁻¹ • ((c - 1) • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
    exact hx0 (by rw [← h2, h0, smul_zero])
  have hq0 : q = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hey : e y = 0 := by
      rw [he, LinearMap.comp_apply]
      have := Submodule.projectionOnto_apply_right hq ⟨y, hy⟩
      show N.subtype (Submodule.projectionOnto N q hq ((⟨y, hy⟩ : q) : ρ.asModule)) = 0
      rw [this, map_zero]
    rw [hcx, hc1, one_smul] at hey
    rw [hey]
    exact Submodule.zero_mem _
  have := hq.sup_eq_top
  rwa [hq0, sup_bot_eq] at this

theorem absIrr_isIrr [Fintype G] {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) {χ : G → K}
    (hχ : Formalism.L2.DIV.IsAbsIrrChar χ) : Formalism.L2.NT.IsIrrChar (fun x => σ (χ x)) := by
  classical
  obtain ⟨n, ρ, hρ, hch⟩ := hχ
  letI : Algebra K ℂ := σ.toAlgebra
  let τ : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  have hτ : ∀ a : K, τ (algebraMap K _ a) = σ a := fun a => by rw [τ.commutes]; rfl
  haveI : CharZero (AlgebraicClosure K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  let ρc : G →* GL (Fin n) ℂ := (Matrix.GeneralLinearGroup.map τ.toRingHom).comp (toGL ρ)
  have htr : ∀ x, σ (χ x) = Matrix.trace ((ρc x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    intro x
    have e1 : ((ρc x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        ((toGL ρ x : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map τ.toRingHom := rfl
    rw [e1, trace_map, trace_toGL, hch x]
    exact (hτ _).symm
  refine ⟨⟨n, ρc, htr⟩, ?_⟩
  have hstar : ∀ x, star (σ (χ x)) = σ (χ x⁻¹) := fun x => by rw [htr, htr, star_trace_inv]
  show ∑ x, σ (χ x) * star (σ (χ x)) = _
  simp_rw [hstar]
  have horth := Formalism.L2.Col.gx_orth (G := G) (k := AlgebraicClosure K) ⟨n, ρ, hρ, rfl⟩ ⟨n, ρ, hρ, rfl⟩
  rw [if_pos rfl] at horth
  have hne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [inv_mul_eq_one₀ hne] at horth
  have := congrArg τ horth
  simp only [map_sum, map_mul, map_natCast, hch, hτ] at this
  rw [← this, Nat.card_eq_fintype_card]

theorem isIrr_absIrr [Fintype G] {K : Type} [Field K] (σ : K →+* ℂ) (hB : PI.XgNamed.BrauerSplit) (z : K)
    (hz : IsPrimitiveRoot z (Fintype.card G)) {χc : G → ℂ} (hc : Formalism.L2.NT.IsIrrChar χc) :
    ∃ χ : G → K, Formalism.L2.DIV.IsAbsIrrChar χ ∧ (fun x => σ (χ x)) = χc := by
  classical
  obtain ⟨⟨n, ρc, htr⟩, hip⟩ := hc
  have hchar : ∀ x, (ofGL ρc).character x = χc x := fun x => by rw [char_ofGL, htr]
  haveI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  have hfr := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ofGL ρc) (ofGL ρc)
  have hsum : ∑ g : G, (ofGL ρc).character g * (ofGL ρc).character g⁻¹ = (Nat.card G : ℂ) := by
    simp_rw [hchar]
    rw [Nat.card_eq_fintype_card, ← hip]
    unfold Formalism.L2.NT.ipG
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [htr x, htr x⁻¹, star_trace_inv]
  rw [hsum, inv_mul_cancel₀ (NeZero.ne _)] at hfr
  have h1 : Module.finrank ℂ (Representation.IntertwiningMap (ofGL ρc) (ofGL ρc)) = 1 := by
    exact_mod_cast hfr.symm
  have hirr := irr_of_finrank_one (ofGL ρc) h1
  obtain ⟨m, τ, τb, hτb, hmat, hσ⟩ := hB G K σ z hz n (ofGL ρc) hirr
  refine ⟨fun t => τ.character t, ⟨m, τb, hτb, fun t => ?_⟩, funext fun t => ?_⟩
  · show _ = algebraMap K _ (τ.character t)
    rw [char_eq_trace, hmat t, trace_map, char_eq_trace]
  · show σ (τ.character t) = χc t
    rw [hσ t, hchar]

end PI.XgCTieBrWork.Chars
