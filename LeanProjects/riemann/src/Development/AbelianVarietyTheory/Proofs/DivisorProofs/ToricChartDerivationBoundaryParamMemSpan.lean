import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDerBd

theorem X_dvd_of_X_mul {σ K : Type} [Field K] {s t : σ} (hst : t ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ MvPowerSeries.X t * g) : MvPowerSeries.X s ∣ g := by
  classical
  rw [MvPowerSeries.X_dvd_iff] at h ⊢
  intro n hn
  have h1 := h (n + Finsupp.single t 1) (by simp [Finsupp.single_apply, hst, hn])
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul] at h1
  simpa using h1

theorem X_dvd_of_prod_mul {σ K : Type} [Field K] {Idx : Type} (f : Idx → σ) {s : σ}
    (S : Finset Idx) (hS : ∀ j ∈ S, f j ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ (∏ j ∈ S, MvPowerSeries.X (f j)) * g) : MvPowerSeries.X s ∣ g := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, _root_.mul_assoc] at h
    exact ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
      (X_dvd_of_X_mul (hS a (Finset.mem_insert_self a S)) h)

theorem deriv_bdParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  classical
  intro A _ k _ m d ψ δ D' I hI hD hJ i

  have hpres : ∀ x ∈ I.map ψ, D' x ∈ I.map ψ := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD]
      exact Ideal.mem_map_of_mem ψ (hI a ha)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    | smul r x hxm hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ r hx)
        (Ideal.mul_mem_right _ _ (Ideal.span_le.2 (fun y hy => Ideal.subset_span hy) hxm))
  set t := bdParam k m d with ht
  have hP : t i * ∏ j ∈ Finset.univ.erase i, t j = ∏ j, t j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hmem : D' (∏ j, t j) ∈ Ideal.span {∏ j, t j} := by
    rw [← hJ]; apply hpres; rw [hJ]; exact Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton] at hmem ⊢
  rw [← hP, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hmem
  have h1 : t i ∣ t i * D' (∏ j ∈ Finset.univ.erase i, t j) + (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_mul_right (t i) _).trans hmem
  have h2 : t i ∣ (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_add_right (dvd_mul_right _ _)).1 h1
  exact X_dvd_of_prod_mul (fun j : Fin m => (Sum.inl j : Fin m ⊕ Fin d)) (Finset.univ.erase i)
    (fun j hj h => (Finset.ne_of_mem_erase hj) (Sum.inl_injective h)) h2

end GlobalTheory.ChartDerBd
