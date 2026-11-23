import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EmbCount

theorem exists_equiv (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) :
    ∃ Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O), ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E) := by
  have hinj := hv.hom_inj
  have h1 : ∀ (σ : E →ₐ[ℚ] C) (y : 𝓞 E), ∃ o : O, algebraMap O C o = σ (y : E) := by
    intro σ y
    have hi : IsIntegral ℤ (σ (y : E)) := (y.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    have hi' : IsIntegral O (σ (y : E)) := hi.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral hi')
  choose f hf using h1
  let Ψ : (E →ₐ[ℚ] C) → (𝓞 E →+* O) := fun σ =>
    { toFun := f σ
      map_one' := hinj (by simp [hf])
      map_mul' := fun a b => hinj (by simp [hf])
      map_zero' := hinj (by simp [hf])
      map_add' := fun a b => hinj (by simp [hf]) }
  have hΨ : ∀ σ (y : 𝓞 E), algebraMap O C (Ψ σ y) = σ (y : E) := hf
  refine ⟨Equiv.ofBijective Ψ ⟨?_, ?_⟩, hΨ⟩
  · intro σ σ' h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext y
    have := hΨ σ y
    rw [h, hΨ] at this
    exact this.symm
  · intro τ
    have hu : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ),
        IsUnit (((algebraMap O C).comp τ) y) := by
      rintro ⟨_, n, hn, rfl⟩
      have : (n : C) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hn
      simpa using this
    refine ⟨(IsLocalization.lift (S := E) hu).toRatAlgHom, ?_⟩
    ext y
    apply hinj
    rw [hΨ]
    exact IsLocalization.lift_eq hu y

theorem trace_eq_sum (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type)
    [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    [Algebra ℤ_[p] O] (Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O))
    (hΦ : ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E)) (x : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    algebraMap O C (algebraMap ℤ_[p] O (LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] x))) =
      ∑ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    have : LinearMap.mulLeft ℤ_[p] (x + y) =
        LinearMap.mulLeft ℤ_[p] x + LinearMap.mulLeft ℤ_[p] y := by
      apply LinearMap.ext; intro z; simp [add_mul]
    simp only [this, map_add, hx, hy, Finset.sum_add_distrib]
  | tmul a y =>
    have h1 : LinearMap.mulLeft ℤ_[p] (a ⊗ₜ[ℤ] y) =
        a • (LinearMap.mulLeft ℤ y).baseChange ℤ_[p] := by
      ext z
      simp [TensorProduct.smul_tmul']
    have h2 : ((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℚ) = Algebra.trace ℚ E (y : E) :=
      Algebra.coe_trace_int y
    have h3 := trace_eq_sum_embeddings C (K := ℚ) (L := E) (x := (y : E))
    have h4 : LinearMap.trace ℤ _ (LinearMap.mulLeft ℤ y) = Algebra.trace ℤ (𝓞 E) y := rfl
    rw [h1, map_smul, LinearMap.trace_baseChange, h4]
    rw [← h2] at h3
    simp only [tauExt, Algebra.TensorProduct.lift_tmul, map_mul, smul_eq_mul, Algebra.ofId_apply]
    rw [← Finset.mul_sum]
    congr 1
    simp only [RingHom.toIntAlgHom_apply, hΦ]
    rw [← h3]
    simp

theorem card_emb : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Algebra ℤ_[p] O] (e : ℤ_[p] ⊗[ℤ] 𝓞 E), e * e = e → Nonempty (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))) ≃ Emb (O := O) e) ∧ Nat.card (𝓞 E →+* O) = Module.finrank ℚ E := by
  intro E _ _ p _ C _ _ _ v O _ _ hv _ e he
  classical
  obtain ⟨Φ, hΦ⟩ := exists_equiv E C v O hv
  have hinj := hv.hom_inj
  refine ⟨?_, ?_⟩
  · have ht := trace_eq_sum E p C O Φ hΦ e
    have hproj : LinearMap.IsProj (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))
        (LinearMap.mulLeft ℤ_[p] e) :=
      ⟨fun x => ⟨x, rfl⟩, by
        rintro _ ⟨x, rfl⟩
        simp [← mul_assoc, he]⟩
    haveI : Module.Free ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := inferInstance
    haveI : Module.Finite ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := inferInstance
    rw [hproj.trace] at ht
    have hterm : ∀ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) e) =
        if Φ σ ∈ Emb (O := O) e then 1 else 0 := by
      intro σ
      split_ifs with h
      · have h' : tauExt (Φ σ) e = 1 := h
        rw [h', map_one]
      · have hid : IsIdempotentElem (algebraMap O C (tauExt (Φ σ) e)) := by
          unfold IsIdempotentElem
          rw [← map_mul, ← map_mul, he]
        rcases IsIdempotentElem.iff_eq_zero_or_one.mp hid with h0 | h1
        · exact h0
        · exact absurd (hinj (h1.trans (map_one _).symm)) h
    simp only [hterm, map_natCast, Finset.sum_boole, Nat.cast_inj] at ht
    rw [ht]
    refine ⟨(Finset.equivFin _).symm.trans (Φ.subtypeEquiv ?_)⟩
    intro σ
    simp
  · rw [← Nat.card_congr Φ, Nat.card_eq_fintype_card, AlgHom.card]

end GlobalTheory.EmbCount
