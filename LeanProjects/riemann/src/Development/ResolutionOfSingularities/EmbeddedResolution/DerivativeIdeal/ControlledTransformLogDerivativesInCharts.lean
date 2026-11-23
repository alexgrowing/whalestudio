import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativesInBlowupCharts
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PartialDerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section

variable (k : Type*) [CommRing k] (ι : Type*)
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]

theorem partialDerivIdeal_iSup_le {κ : Sort*} (h : ι) (F : κ → Ideal S) :
    partialDerivIdeal k ι S h (⨆ j, F j) ≤ ⨆ j, partialDerivIdeal k ι S h (F j) := by
  refine partialDerivIdeal_le k ι S h (iSup_mono fun j => le_partialDerivIdeal k ι S h (F j)) ?_
  intro g hg
  refine Submodule.iSup_induction (motive := fun x =>
      partialDeriv k ι S h x ∈ ⨆ j, partialDerivIdeal k ι S h (F j)) (fun j => F j) hg ?_ ?_ ?_
  · intro j x hx
    exact le_iSup (fun j => partialDerivIdeal k ι S h (F j)) j
      (partialDeriv_mem_partialDerivIdeal k ι S h (F j) hx)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    simp only [map_add]
    exact Submodule.add_mem _ hx hy

theorem partialDerivIdeal_biSup_le (h : ι) (n : ℕ) (F : ℕ → Ideal S) :
    partialDerivIdeal k ι S h (⨆ i, ⨆ _ : i ≤ n, F i) ≤
      ⨆ i, ⨆ _ : i ≤ n, partialDerivIdeal k ι S h (F i) :=
  (partialDerivIdeal_iSup_le k ι S h (fun i => ⨆ _ : i ≤ n, F i)).trans
    (iSup_mono fun i => partialDerivIdeal_iSup_le k ι S h (fun _ : i ≤ n => F i))

end

section

variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s h : ι)

theorem partialDerivIdeal_controlledTransform_le_sup
    (_hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S₁) (m : ℕ)
    (hL : ∀ i ≤ m,
      Ideal.span {coord k ι S₁ s ^ (m - i)} * L i = Ideal.map φ (derivIdealIterate k i J))
    (i : ℕ) (hi : i < m) :
    partialDerivIdeal k ι S₁ h (L i) ≤ L i ⊔ L (i + 1) := by
  refine partialDerivIdeal_le k ι S₁ h le_sup_left ?_
  intro g hg
  have hc : m - i = (m - i - 1) + 1 := by omega
  have hJ : Ideal.span {coord k ι S₁ s ^ ((m - i - 1) + 1)} * L i
      = Ideal.map φ (derivIdealIterate k i J) := by
    rw [← hc]
    exact hL i (le_of_lt hi)
  have hD : Ideal.map φ (derivIdeal k (derivIdealIterate k i J)) ≤
      Ideal.span {coord k ι S₁ s ^ (m - i - 1)} * L (i + 1) := by
    have h2 := hL (i + 1) (by omega)
    have h3 : m - (i + 1) = m - i - 1 := by omega
    rw [h3] at h2
    rw [← derivIdealIterate_succ]
    exact le_of_eq h2.symm
  exact partialDeriv_mem_sup_of_span_pow_mul_eq_map k ι S S₁ φ T s hin hs hout hnzd h hhT hhs
    (derivIdealIterate k i J) (L i) (L (i + 1)) (m - i - 1) hJ hD g hg

theorem partialDerivIdealIterate_controlledTransform_le_iSup
    (hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S₁) (m : ℕ)
    (hL : ∀ i ≤ m,
      Ideal.span {coord k ι S₁ s ^ (m - i)} * L i = Ideal.map φ (derivIdealIterate k i J))
    (l : ℕ) (hl : l ≤ m) :
    partialDerivIdealIterate k ι S₁ h l (L 0) ≤ ⨆ i, ⨆ _ : i ≤ l, L i := by
  revert hl
  induction l with
  | zero =>
      intro _
      rw [partialDerivIdealIterate_zero]
      exact le_iSup₂ (f := fun i (_ : i ≤ 0) => L i) 0 le_rfl
  | succ l ih =>
      intro hl
      rw [partialDerivIdealIterate_succ]
      have hlm : l ≤ m := Nat.le_of_succ_le hl
      have h1 := ih hlm
      refine le_trans (partialDerivIdeal_mono k ι S₁ h h1) ?_
      refine le_trans (partialDerivIdeal_biSup_le k ι S₁ h l L) ?_
      refine iSup_le fun i => iSup_le fun hi => ?_
      have him : i < m := lt_of_le_of_lt hi (by omega)
      have hstep := partialDerivIdeal_controlledTransform_le_sup k ι S S₁ φ T s h
        hsT hin hs hout hnzd hhT hhs J L m hL i him
      refine hstep.trans (sup_le ?_ ?_)
      · exact le_iSup₂ (f := fun j (_ : j ≤ l + 1) => L j) i (by omega)
      · exact le_iSup₂ (f := fun j (_ : j ≤ l + 1) => L j) (i + 1) (by omega)

theorem derivIdealIterate_le_iSup_logDerivIdealIterate_controlledTransform [Fintype ι]
    (hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S₁) (m : ℕ)
    (hL : ∀ i ≤ m,
      Ideal.span {coord k ι S₁ s ^ (m - i)} * L i = Ideal.map φ (derivIdealIterate k i J))
    (n : ℕ) (hn : n ≤ m) :
    derivIdealIterate k n (L 0) ≤
      ⨆ i, ⨆ _ : i ≤ n,
        logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - i) (L i) := by
  refine (derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate k ι S₁ h n (L 0)).trans ?_
  refine iSup_le fun l => iSup_le fun hln => ?_
  have hlm : l ≤ m := hln.trans hn
  have h1 : partialDerivIdealIterate k ι S₁ h l (L 0) ≤ ⨆ i, ⨆ _ : i ≤ l, L i :=
    partialDerivIdealIterate_controlledTransform_le_iSup k ι S S₁ φ T s h
      hsT hin hs hout hnzd hhT hhs J L m hL l hlm
  refine (logDerivIdealIterate_mono k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l) h1).trans ?_
  refine (logDerivIdealIterate_iSup_le k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l)
    (fun i => ⨆ _ : i ≤ l, L i)).trans ?_
  refine iSup_le fun i => ?_
  refine (logDerivIdealIterate_iSup_le k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l)
    (fun _ : i ≤ l => L i)).trans ?_
  refine iSup_le fun hi => ?_
  have h2 : logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l) (L i) ≤
      logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - i) (L i) :=
    logDerivIdealIterate_le_of_le k (Ideal.span ({coord k ι S₁ h} : Set S₁))
      (by omega : n - l ≤ n - i) (L i)
  exact h2.trans (le_iSup₂
    (f := fun j (_ : j ≤ n) =>
      logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - j) (L j))
    i (hi.trans hln))

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
