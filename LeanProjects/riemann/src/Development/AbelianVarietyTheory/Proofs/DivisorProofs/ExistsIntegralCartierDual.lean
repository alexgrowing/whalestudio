import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HopfFitt

theorem det_mul_mem {D : Type} [CommRing D] {n : ℕ} (T : Matrix (Fin n) (Fin n) D) (v : Fin n → D)
    (J : Ideal D) (h : ∀ k, T.mulVec v k ∈ J) (k : Fin n) : T.det * v k ∈ J := by
  have e : T.adjugate.mulVec (T.mulVec v) = (T.det • (1 : Matrix (Fin n) (Fin n) D)).mulVec v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
  have ek := congrFun e k
  have h1 : (T.det • (1 : Matrix (Fin n) (Fin n) D)).mulVec v k = T.det * v k := by
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [← h1, ← ek]
  simp only [Matrix.mulVec, dotProduct]
  exact J.sum_mem fun j _ => J.mul_mem_left _ (h j)

theorem map_det_diag_sub {D S : Type} [CommRing D] [CommRing S] (f : D →+* S) {n : ℕ} (β : D)
    (A : Matrix (Fin n) (Fin n) D) (hA : ∀ i j, f (A i j) = 0) :
    f (Matrix.diagonal (fun _ => β) - A).det = f β ^ n := by
  rw [RingHom.map_det]
  have : f.mapMatrix (Matrix.diagonal (fun _ => β) - A) = Matrix.diagonal (fun _ => f β) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hA]
    · simp [Matrix.diagonal_apply_ne _ hij, hA]
  rw [this, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem exists_integral : ∀ (R : Type) [CommRing R] (D : Type) [CommRing D] [HopfAlgebra R D] [Module.Finite R D] (g : ℕ) (x : Fin g → Cot R D) (r c : R), (∀ w : Cot R D, r • w ∈ Submodule.span R (Set.range x)) → (∀ w : Cot R D, c • w = 0) → ∃ (k : ℕ) (Λ : D), (∀ d : D, d * Λ = algebraMap R D (Coalgebra.counit (R := R) d) * Λ) ∧ Coalgebra.counit (R := R) Λ = r ^ k * c ^ g := by
  intro R _ D _ _ _ g x r c hr hc
  set ε : D →ₐ[R] R := counitAlgHom R D with hε
  set I : Ideal D := RingHom.ker ε with hI
  have memI : ∀ a : D, a ∈ I ↔ ε a = 0 := fun a => RingHom.mem_ker
  haveI : Module.Finite R I := Module.Finite.of_surjective (AugCot.projKer ε)
    (fun a => ⟨a, AugCot.projKer_coe ε a⟩)
  obtain ⟨m, y, hy⟩ := Module.Finite.exists_fin (R := R) (M := I)
  have hyR : ∀ a : I, ∃ s : Fin m → R, ∑ l, s l • y l = a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (hy ▸ Submodule.mem_top)
  set yD : Fin m → D := fun l => (y l : D) with hyD
  have hIspan : I = Ideal.span (Set.range yD) := by
    apply le_antisymm
    · intro a ha
      obtain ⟨s, hs⟩ := hyR ⟨a, ha⟩
      have hs' : a = ∑ l, algebraMap R D (s l) * yD l := by
        calc a = ((⟨a, ha⟩ : I) : D) := rfl
          _ = _ := by rw [← hs]; simp [Algebra.smul_def, yD]
      rw [hs']
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
    · rw [Ideal.span_le]; rintro _ ⟨l, rfl⟩; exact (y l).2
  have hsq : ∀ z ∈ I ^ 2, ∃ a : Fin m → D, (∀ l, a l ∈ I) ∧ ∑ l, a l * yD l = z := by
    intro z hz
    have hz' : z ∈ I • Submodule.span D (Set.range yD) := by
      rw [pow_two, ← Ideal.smul_eq_mul] at hz
      convert hz using 2
      exact hIspan.symm
    obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum I yD z).1 hz'
    refine ⟨fun l => a l, ha, ?_⟩
    rw [← hsum, Finsupp.sum_fintype a (fun i c => c • yD i) (fun i => zero_smul _ _)]
    simp [smul_eq_mul]
  choose xt hxt using fun i => I.toCotangent_surjective (x i)
  set xD : Fin g → D := fun i => (xt i : D) with hxD
  set J : Ideal D := Ideal.span (Set.range xD) with hJ

  choose s hs using fun l => (Submodule.mem_span_range_iff_exists_fun R).1 (hr (I.toCotangent (y l)))
  have h1 : ∀ l, algebraMap R D r * yD l - ∑ i, algebraMap R D (s l i) * xD i ∈ I ^ 2 := by
    intro l
    have h0 : I.toCotangent (r • y l - ∑ i, s l i • xt i) = 0 := by
      rw [map_sub, map_sum]
      simp only [LinearMap.map_smul_of_tower, hxt]
      rw [hs l, sub_self]
    have := (I.toCotangent_eq_zero _).1 h0
    simpa [Algebra.smul_def, yD, xD] using this
  choose A hA hAsum using fun l => hsq _ (h1 l)
  set T : Matrix (Fin m) (Fin m) D := Matrix.diagonal (fun _ => algebraMap R D r) - Matrix.of A with hT
  have hTv : ∀ l, T.mulVec yD l ∈ J := by
    intro l
    have e : T.mulVec yD l = ∑ i, algebraMap R D (s l i) * xD i := by
      have := hAsum l
      simp only [hT, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [this]; ring
    rw [e]
    exact J.sum_mem fun i _ => J.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
  set b := T.det with hb
  have hbI : ∀ a ∈ I, b * a ∈ J := by
    intro a ha
    rw [hIspan] at ha
    obtain ⟨t, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 ha
    rw [Finset.mul_sum]
    exact J.sum_mem fun l _ => by
      rw [mul_left_comm]; exact J.mul_mem_left _ (det_mul_mem T yD J hTv l)
  have hεb : ε b = r ^ m := by
    have := map_det_diag_sub (ε : D →+* R) (algebraMap R D r) (Matrix.of A)
      (fun i j => (memI _).1 (hA i j))
    simpa [hb, hT] using this

  have h2 : ∀ i, b * (algebraMap R D c * xD i) ∈ I • Submodule.span D (Set.range xD) := by
    intro i
    have h0 : I.toCotangent (c • xt i) = 0 := by
      rw [LinearMap.map_smul_of_tower, hxt]; exact hc _
    have hz := (I.toCotangent_eq_zero _).1 h0
    obtain ⟨a, ha, hsum⟩ := hsq _ hz
    have e : b * (algebraMap R D c * xD i) = ∑ l, a l • (b * yD l) := by
      rw [show algebraMap R D c * xD i = ((c • xt i : I) : D) by simp [Algebra.smul_def, xD], ← hsum,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul]; ring
    rw [e]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem_smul (ha l) (hbI _ (y l).2)
  choose A' hA' hA'sum using fun i => (Submodule.mem_ideal_smul_span_iff_exists_sum I xD _).1 (h2 i)
  set T' : Matrix (Fin g) (Fin g) D :=
    Matrix.diagonal (fun _ => b * algebraMap R D c) - Matrix.of (fun i j => A' i j) with hT'
  have hT'v : ∀ i, T'.mulVec xD i ∈ (⊥ : Ideal D) := by
    intro i
    have := hA'sum i
    rw [Finsupp.sum_fintype (A' i) (fun i c => c • xD i) (fun i => zero_smul _ _)] at this
    simp only [smul_eq_mul] at this
    rw [Ideal.mem_bot]
    simp only [hT', Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [this]; ring
  set Δ := T'.det with hΔ
  have hΔx : ∀ i, Δ * xD i = 0 := fun i => Ideal.mem_bot.1 (det_mul_mem T' xD ⊥ hT'v i)
  have hεΔ : ε Δ = (r ^ m * c) ^ g := by
    have key : ε Δ = ε (b * algebraMap R D c) ^ g :=
      map_det_diag_sub (ε : D →+* R) (b * algebraMap R D c) (Matrix.of (fun i j => A' i j))
        (fun i j => (memI _).1 (hA' i j))
    rw [key, map_mul, AlgHom.commutes, hεb, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨m + m * g, b * Δ, fun d => ?_, ?_⟩
  · have hd : d - algebraMap R D (ε d) ∈ I := by
      rw [memI, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have hk : (d - algebraMap R D (ε d)) * (b * Δ) = 0 := by
      obtain ⟨t, ht⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hbI _ hd)
      calc (d - algebraMap R D (ε d)) * (b * Δ) = Δ * (b * (d - algebraMap R D (ε d))) := by ring
        _ = 0 := by
          rw [← ht, Finset.mul_sum]
          exact Finset.sum_eq_zero fun i _ => by rw [mul_left_comm, hΔx, mul_zero]
    rw [sub_mul, sub_eq_zero] at hk
    exact hk
  · show ε (b * Δ) = _
    rw [map_mul, hεb, hεΔ]
    ring

end GlobalTheory.HopfFitt
