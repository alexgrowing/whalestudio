import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WedgeDiag

variable {R : Type} [CommRing R] {I : Type} [LinearOrder I]

noncomputable def lowerWedge :
    (I →₀ R) →ₗ[R] (I →₀ R) →ₗ[R] ⋀[R]^2 (I →₀ R) :=
  Finsupp.linearCombination R (fun i => Finsupp.linearCombination R (fun j =>
    if i < j then exteriorPower.ιMulti R 2 ![Finsupp.single i 1, Finsupp.single j 1] else 0))

noncomputable def wedgeBil {M : Type} [AddCommGroup M] [Module R M] :
    M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun x y => exteriorPower.ιMulti R 2 ![x, y])
    (fun x x' y => by
      simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_add ![y] x x')
    (fun c x y => by
      simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_smul ![y] c x)
    (fun x y y' => by
      have h := fun a b : M => (exteriorPower.ιMulti R 2).map_swap ![a, b] (i := 0) (j := 1) (by decide)
      have e : ∀ a b : M, ![a, b] ∘ Equiv.swap 0 1 = ![b, a] := by
        intro a b; ext k; fin_cases k <;> rfl
      simp only [e] at h
      have h1 : exteriorPower.ιMulti R 2 ![y + y', x] = exteriorPower.ιMulti R 2 ![y, x] + exteriorPower.ιMulti R 2 ![y', x] := by
        simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_add ![x] y y'
      rw [h (y + y') x, h y x, h y' x, h1, neg_add])
    (fun c x y => by
      have h := fun a b : M => (exteriorPower.ιMulti R 2).map_swap ![a, b] (i := 0) (j := 1) (by decide)
      have e : ∀ a b : M, ![a, b] ∘ Equiv.swap 0 1 = ![b, a] := by
        intro a b; ext k; fin_cases k <;> rfl
      simp only [e] at h
      have h1 : exteriorPower.ιMulti R 2 ![c • y, x] = c • exteriorPower.ιMulti R 2 ![y, x] := by
        simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_smul ![x] c y
      rw [h (c • y) x, h y x, h1, smul_neg])

theorem wedgeBil_apply {M : Type} [AddCommGroup M] [Module R M] (x y : M) :
    wedgeBil x y = exteriorPower.ιMulti R 2 ![x, y] := rfl

theorem lowerWedge_sub_flip :
    lowerWedge (R := R) (I := I) - lowerWedge.flip = wedgeBil (M := I →₀ R) := by
  ext i j
  simp only [lowerWedge, LinearMap.sub_apply, LinearMap.flip_apply, LinearMap.coe_comp,
    Function.comp_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single, one_smul,
    LinearMap.smul_apply, wedgeBil_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.not_gt]
  · simp only [lt_irrefl, if_false, sub_zero]
    exact congrArg _ ((exteriorPower.ιMulti R 2 (M := I →₀ R)).map_eq_zero_of_eq ![Finsupp.single i 1, Finsupp.single i 1] (i := 0) (j := 1) rfl (by decide)).symm
  · have hs := (exteriorPower.ιMulti R 2).map_swap ![Finsupp.single j (1:R), Finsupp.single i 1] (i := 0) (j := 1) (by decide)
    have e : ![Finsupp.single j (1:R), Finsupp.single i 1] ∘ Equiv.swap 0 1 = ![Finsupp.single i 1, Finsupp.single j 1] := by
      ext k; fin_cases k <;> rfl
    rw [e] at hs
    simp [h, h.not_gt, hs]

end GlobalTheory.WedgeDiag

namespace GlobalTheory.WedgeDiag

variable {R : Type} [CommRing R] {I : Type} [LinearOrder I]

noncomputable def crossWedge :
    ((I →₀ R) × (I →₀ R)) [⋀^Fin 2]→ₗ[R] ⋀[R]^2 (I →₀ R) where
  toFun v := lowerWedge (v 0).1 (v 1).2 - lowerWedge (v 1).1 (v 0).2
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [Function.update_of_ne, map_add, LinearMap.add_apply] <;> abel
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp [Function.update_of_ne, map_smul, LinearMap.smul_apply, smul_sub]
  map_eq_zero_of_eq' := by
    intro v i j h hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem crossWedge_apply (v : Fin 2 → (I →₀ R) × (I →₀ R)) :
    crossWedge v = lowerWedge (v 0).1 (v 1).2 - lowerWedge (v 1).1 (v 0).2 := rfl

noncomputable def crossWedgeLin : ⋀[R]^2 ((I →₀ R) × (I →₀ R)) →ₗ[R] ⋀[R]^2 (I →₀ R) :=
  exteriorPower.alternatingMapLinearEquiv crossWedge

theorem crossWedgeLin_inl :
    crossWedgeLin ∘ₗ exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R)) = 0 := by
  ext v
  simp [crossWedgeLin, crossWedge_apply]

theorem crossWedgeLin_inr :
    crossWedgeLin ∘ₗ exteriorPower.map 2 (LinearMap.inr R (I →₀ R) (I →₀ R)) = 0 := by
  ext v
  simp [crossWedgeLin, crossWedge_apply]

theorem crossWedgeLin_diag :
    crossWedgeLin ∘ₗ exteriorPower.map 2
      (LinearMap.inl R (I →₀ R) (I →₀ R) + LinearMap.inr R (I →₀ R) (I →₀ R)) = LinearMap.id := by
  ext v
  have h := LinearMap.congr_fun₂ (lowerWedge_sub_flip (R := R) (I := I)) (v 0) (v 1)
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, wedgeBil_apply] at h
  have hv : ![v 0, v 1] = v := by ext k; fin_cases k <;> rfl
  rw [hv] at h
  simp [crossWedgeLin, crossWedge_apply, h]

theorem free_case (t : ⋀[R]^2 (I →₀ R))
    (H : exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R) + LinearMap.inr R (I →₀ R) (I →₀ R)) t =
      exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R)) t +
        exteriorPower.map 2 (LinearMap.inr R (I →₀ R) (I →₀ R)) t) : t = 0 := by
  have h := congrArg crossWedgeLin H
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply crossWedgeLin, ← LinearMap.comp_apply crossWedgeLin,
    crossWedgeLin_diag, crossWedgeLin_inl, crossWedgeLin_inr] at h
  simpa using h

end GlobalTheory.WedgeDiag

namespace GlobalTheory.WedgeDiag

theorem eq_zero_of_diag_additive : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (t : ⋀[R]^2 M), exteriorPower.map 2 (LinearMap.inl R M M + LinearMap.inr R M M) t = exteriorPower.map 2 (LinearMap.inl R M M) t + exteriorPower.map 2 (LinearMap.inr R M M) t → t = 0 := by
  intro R M _ _ _ _ t H
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  letI : LinearOrder M := IsWellOrder.linearOrder WellOrderingRel
  set p : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have e0 : (LinearMap.inl R (M →₀ R) (M →₀ R) + LinearMap.inr R (M →₀ R) (M →₀ R)) ∘ₗ s =
      (s.prodMap s) ∘ₗ (LinearMap.inl R M M + LinearMap.inr R M M) := by
    ext x <;> simp
  have e1 : (s.prodMap s) ∘ₗ LinearMap.inl R M M = LinearMap.inl R (M →₀ R) (M →₀ R) ∘ₗ s := by
    ext x <;> simp
  have e2 : (s.prodMap s) ∘ₗ LinearMap.inr R M M = LinearMap.inr R (M →₀ R) (M →₀ R) ∘ₗ s := by
    ext x <;> simp
  have hu : exteriorPower.map 2 s t = 0 := by
    apply free_case
    have h := congrArg (exteriorPower.map 2 (s.prodMap s)) H
    rw [map_add] at h
    simp only [← LinearMap.comp_apply, ← exteriorPower.map_comp] at h ⊢
    rw [e0, ← e1, ← e2]
    exact h
  have := congrArg (exteriorPower.map 2 p) hu
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hs, exteriorPower.map_id, map_zero] at this
  exact this

end GlobalTheory.WedgeDiag
