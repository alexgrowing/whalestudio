import Mathlib

open scoped TensorProduct

namespace GlobalTheory.EmbUnitBallConj

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E]

theorem sum_eq_zero (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) {ι : Type}
    [Fintype ι] (y : ι → E) (c : ι → ℚ_[l]) (hc : ∑ k, c k • a (y k) = 0) :
    ∑ k, c k • b (y k) = 0 := by
  haveI : CharZero E := a.charZero
  have hd : DenseRange (Pi.map fun _ : ι => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : ι → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1} := by
    intro f
    have := (IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage
      (f := fun c : ι → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)
    convert this using 1
    ext c
    simp
  have key : ∀ c : ι → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1 := by
    intro c
    refine hd.induction_on c ?_ fun q => ?_
    · have := (hcl a).compl.isClosed.union (hcl b).isClosed
      convert this using 1
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    · have e : ∀ f : E →+* PadicAlgCl l,
          ∑ k, (Pi.map (fun _ : ι => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) =
            f (∑ k, (q k : E) * y k) := by
        intro f
        simp [Algebra.smul_def]
      rw [e a, e b]
      exact (h _).1
  by_contra hne
  have hpos : 0 < ‖∑ k, c k • b (y k)‖ := norm_pos_iff.2 hne
  obtain ⟨r, hr⟩ := NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹
  have h1 := key (r • c) (by
    simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])
  simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1
  rw [inv_lt_iff_one_lt_mul₀ hpos] at hr
  linarith

theorem exists_equiv_of_ker_le {F T K : Type} [Field F] [CommRing T] [Algebra F T] [Field K]
    [Algebra F K] [IsAlgClosed K] [Algebra.IsAlgebraic F K] (f g : T →ₐ[F] K)
    (h : RingHom.ker f ≤ RingHom.ker g) : ∃ σ : K ≃ₐ[F] K, ∀ x, σ (f x) = g x := by
  let S : IntermediateField F K :=
    Subalgebra.IsAlgebraic.toIntermediateField (S := f.range)
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)
  let φ : f.range →ₐ[F] K :=
    (Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)).comp
      (Ideal.quotientKerEquivRange f).symm.toAlgHom
  have hφ : ∀ x, φ ⟨f x, x, rfl⟩ = g x := by
    intro x
    have : (Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩ = Ideal.Quotient.mk _ x := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)
      ((Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩) = g x
    rw [this]
    rfl
  let φ' : S →ₐ[F] K := φ
  obtain ⟨ψ, hψ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := F) (L := S) (M := K)
    (E := K) φ'
  refine ⟨AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ), fun x => ?_⟩
  rw [← hφ x]
  exact DFunLike.congr_fun hψ (⟨f x, x, rfl⟩ : S)

noncomputable def ext (a : E →+* PadicAlgCl l) : ℚ_[l] ⊗[ℤ] E →ₐ[ℚ_[l]] PadicAlgCl l :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) a.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem ext_tmul (a : E →+* PadicAlgCl l) (c : ℚ_[l]) (x : E) : ext a (c ⊗ₜ x) = c • a x := by
  simp [ext, Algebra.smul_def, Algebra.ofId_apply]

theorem exists_conj : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] (j₁ j₂ : Ω →+* PadicAlgCl l), (∀ x, ‖j₁ x‖ ≤ 1 ↔ ‖j₂ x‖ ≤ 1) → ∃ σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, σ (j₁ x) = j₂ x := by
  intro l _ Ω _ a b h
  have h' : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have ha : 0 < ‖a x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
      have hb : 0 < ‖b x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
      have := h x⁻¹
      rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_le_one₀ ha, inv_le_one₀ hb] at this
      rw [← not_le, ← not_le, this]
  obtain ⟨σ, hσ⟩ := exists_equiv_of_ker_le (ext a) (ext b) (by
    intro t ht
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
    rw [RingHom.mem_ker, map_sum] at ht ⊢
    simp only [ext_tmul] at ht ⊢
    rw [← Finset.sum_coe_sort] at ht ⊢
    exact sum_eq_zero a b h' _ _ ht)
  refine ⟨σ, fun x => ?_⟩
  simpa [ext_tmul] using hσ (1 ⊗ₜ x)

end GlobalTheory.EmbUnitBallConj
