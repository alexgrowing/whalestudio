import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.GrSpan

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem inj_of_sandwich {R Q F ι : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]
    [AddCommGroup F] [Module R F] [Fintype ι] (g : (ι → R) →ₗ[R] Q) (f : Q →ₗ[R] F)
    (e : F ≃ₗ[R] (ι → R)) (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Injective f := by
  have hs : Function.Surjective (e.toLinearMap ∘ₗ f ∘ₗ g) := e.surjective.comp (hf.comp hg)
  have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs
  intro a b hab
  obtain ⟨x, rfl⟩ := hg a
  obtain ⟨y, rfl⟩ := hg b
  have : x = y := hi (by simp [hab])
  rw [this]

theorem UpperTheory.V.AlgebraTools.groupRing_ker :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (l : ℕ), l.Prime → (l : Λ) ∈ IsLocalRing.maximalIdeal Λ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (e : σ → ℕ) (φ : MvPowerSeries σ Λ →ₐ[Λ] MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))), (∀ s : σ, φ (1 + MvPowerSeries.X s) = MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s))) (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))))) → Function.Surjective φ →
      RingHom.ker φ = Ideal.span (Set.range fun s => (1 + MvPowerSeries.X s : MvPowerSeries σ Λ) ^ l ^ e s - 1) := by
  intro Λ _ _ _ _ l hl hlm σ _ _ e φ hφ hsurj
  haveI : ∀ s, NeZero (l ^ e s) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  set w : σ → MvPowerSeries σ Λ := fun s => (1 + MvPowerSeries.X s) ^ l ^ e s - 1 with hw
  set I : Ideal (MvPowerSeries σ Λ) := Ideal.span (Set.range w) with hI
  have hle : I ≤ RingHom.ker φ := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    have h1 : (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))) :
        ∀ s, Multiplicative (ZMod (l ^ e s))) ^ (l ^ e s) = 1 := by
      rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero,
        Pi.mulSingle_one]
    simp only [SetLike.mem_coe, RingHom.mem_ker, hw, map_sub, map_pow, hφ, map_one]
    rw [← map_pow, h1, map_one, sub_self]
  have hwm : ∀ s, w s - MvPowerSeries.X s ^ (l ^ e s) ∈
      Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
    intro s
    obtain ⟨m, hm⟩ : ∃ m, l ^ e s = m + 1 := ⟨l ^ e s - 1, (Nat.succ_pred_eq_of_pos (pow_pos hl.pos _)).symm⟩
    have hlC : ((l : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := Λ))]
      exact Ideal.mem_map_of_mem _ hlm
    simp only [hw]
    rw [add_comm, add_pow, hm, Finset.sum_range_succ, Finset.sum_range_succ']
    have key : ∀ k ∈ Finset.range m, MvPowerSeries.X s ^ (k + 1) * (1 : MvPowerSeries σ Λ) ^ (m + 1 - (k + 1)) *
        (((m + 1).choose (k + 1) : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      intro k hk
      have hd : l ∣ (m + 1).choose (k + 1) := by
        rw [← hm]
        refine hl.dvd_choose_pow (Nat.succ_ne_zero k) ?_
        rw [hm]; have := Finset.mem_range.mp hk; omega
      obtain ⟨t, ht⟩ := hd
      rw [ht, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hlC)
    have hsum := Ideal.sum_mem _ key
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
      Nat.sub_zero, one_mul] at hsum ⊢
    convert hsum using 1
    ring
  have hIφ : ∀ a ∈ I, φ a = 0 := fun a ha => hle ha
  refine le_antisymm ?_ hle
  have hspan := UpperTheory.V.AlgebraTools.mvPowerSeries_span_monomials Λ σ (fun s => l ^ e s) w hwm
  let ψ := Ideal.Quotient.liftₐ I φ hIφ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  let v := fun α : ((s : σ) → Fin (l ^ e s)) => Ideal.Quotient.mk I (∏ s, MvPowerSeries.X s ^ (α s : ℕ))
  have hg : Function.Surjective (Fintype.linearCombination Λ v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  let eqv : ((s : σ) → Fin (l ^ e s)) ≃ (∀ s, Multiplicative (ZMod (l ^ e s))) :=
    Equiv.piCongrRight fun s => (ZMod.finEquiv (l ^ e s)).toEquiv.trans Multiplicative.ofAdd
  let E : MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))) ≃ₗ[Λ] (((s : σ) → Fin (l ^ e s)) → Λ) :=
    (MonoidAlgebra.coeffLinearEquiv Λ).trans
      ((Finsupp.linearEquivFunOnFinite Λ Λ _).trans (LinearEquiv.funCongrLeft Λ Λ eqv))
  have hinj := inj_of_sandwich (Fintype.linearCombination Λ v) ψ.toLinearMap E hg hψs
  intro x hx
  have h0 : ψ (Ideal.Quotient.mk I x) = 0 := hx
  have : Ideal.Quotient.mk I x = 0 := hinj (by simpa using h0)
  exact Ideal.Quotient.eq_zero_iff_mem.mp this
