import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem of_lmul (a : Matrix (Fin n) (Fin n) (Cinf E)) (x : Lie E n) :
    lmul (toL a) x = toL (a * Matrix.of x) := rfl

private theorem lmul_one_add (a : Matrix (Fin n) (Fin n) (Cinf E)) (x : Lie E n) :
    lmul (toL (1 + a)) x = x + lmul (toL a) x := by
  rw [of_lmul, of_lmul, add_mul, one_mul]; rfl

private theorem exists_bil {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : V →ₗ[ℝ] Matrix (Fin n) (Fin n) (Cinf E)) :
    ∃ B : V →L[ℝ] Lie E n →L[ℝ] Lie E n, ∀ u x, B u x = lmul (toL (L u)) x := by
  let B0 : V →ₗ[ℝ] Lie E n →L[ℝ] Lie E n :=
    { toFun := fun u => lmul (toL (L u))
      map_add' := fun u v => by
        ext1 x
        rw [ContinuousLinearMap.add_apply, of_lmul, of_lmul, of_lmul, map_add, add_mul]; rfl
      map_smul' := fun c u => by
        ext1 x
        rw [ContinuousLinearMap.smul_apply, of_lmul, of_lmul, map_smul, smul_mul_assoc]; rfl }
  exact ⟨LinearMap.toContinuousLinearMap B0, fun _ _ => rfl⟩

private theorem isUnit_of_inj (a : Matrix (Fin n) (Fin n) (Cinf E)) (h : ∀ y : Lie E n, lmul (toL a) y = 0 → y = 0) :
    IsUnit a := by
  have hi : Function.Injective (LinearMap.mulLeft ℝ a) :=
    (injective_iff_map_eq_zero _).2 fun y hy => h (toL y) hy
  obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.1 hi 1
  exact IsUnit.of_mul_eq_one b hb

variable {d : ℕ} (b : Module.Basis (Fin d) ℝ (Cinf E))

private noncomputable def crd (i : Fin n) : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] Cinf E where
  toFun u := b.equivFun.symm fun v => u (i, v)
  map_add' u v := map_add b.equivFun.symm (fun x => u (i, x)) fun x => v (i, x)
  map_smul' c u := map_smul b.equivFun.symm c fun x => u (i, x)

private noncomputable def colL (m : Fin n) : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Cinf E) where
  toFun u := Matrix.of fun i j => if i ≤ m ∧ j.val = m.val + 1 then crd b i u else 0
  map_add' u v := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def rowL (m : Fin n) : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Cinf E) where
  toFun u := Matrix.of fun i j => if i = m ∧ j ≤ m then -crd b j u else 0
  map_add' u v := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp [add_comm]
  map_smul' c u := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def eta (m : Fin n) (ξ : Fin n → Cinf E) : EuclideanSpace ℝ (Fin n × Fin d) :=
  WithLp.toLp 2 fun z => if z.1 ≤ m then -b.repr (ξ z.1) z.2 else 0

private theorem crd_eta (m : Fin n) (ξ : Fin n → Cinf E) {j : Fin n} (h : j ≤ m) : crd b j (eta b m ξ) = -ξ j := by
  change b.equivFun.symm _ = _
  rw [LinearEquiv.symm_apply_eq]
  funext v
  simp [eta, h]

private theorem repr_crd (j : Fin n) (u : EuclideanSpace ℝ (Fin n × Fin d)) (v : Fin d) :
    b.repr (crd b j u) v = u (j, v) :=
  congrFun (b.equivFun.apply_symm_apply fun v => u (j, v)) v

private theorem colL_sq (m : Fin n) (u : EuclideanSpace ℝ (Fin n × Fin d)) : colL b m u * colL b m u = 0 := by
  ext1 i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [colL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  by_cases h : k ≤ m
  · rw [if_neg, zero_mul]
    rintro ⟨-, h'⟩
    rw [Fin.le_def] at h
    omega
  · rw [if_neg (fun h' : k ≤ m ∧ _ => h h'.1), mul_zero]

private theorem rowM_eq (m : Fin n) (ξ : Fin n → Cinf E) :
    rowM m ξ = 1 + rowL b m (eta b m ξ - eta b m ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m)) := by
  ext1 i j
  simp only [rowM, rowL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply]
  split_ifs with h
  · obtain ⟨rfl, h⟩ := h
    rw [map_sub, crd_eta b _ _ h, crd_eta b _ _ h]
    ring
  · simp

private theorem inner_eta (b' : Module.Basis (Fin d) ℝ (Cinf E))
    (H : ∀ x y, TG.tr E (x * y) = ∑ i, b'.repr x i * b.repr y i) (m : Fin n) (ξ : Fin n → Cinf E)
    (u : EuclideanSpace ℝ (Fin n × Fin d)) :
    ⟪eta b' m ξ, u⟫ = -TG.tr E (dotLe m ξ fun j => crd b j u) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, dotLe, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ≤ m
  · rw [if_pos h, H, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [eta, h, repr_crd, mul_comm]
  · simp [eta, h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.StrongMultiplicityOne.archStep :
    UpperTheory.V.Af.StrongMultiplicityOne.TrDual → UpperTheory.V.Af.Smo.SchTw → UpperTheory.V.Af.Smo.PftSch → UpperTheory.V.Af.Smo.BetaSch → UpperTheory.V.Af.Smo.BetaInt → UpperTheory.V.Af.StrongMultiplicityOne.ArchStep := by
  intro h0 h1 h2 h3 h4 E _ _ n m _
  obtain ⟨d, b, b', H⟩ := h0 E
  obtain ⟨B, hB⟩ := exists_bil (colL b m)
  obtain ⟨A, hA⟩ := exists_bil (rowL b' m)
  have hBB : ∀ u x, B u (B u x) = 0 := fun u x => by
    rw [hB, hB, of_lmul, of_lmul]
    change toL (colL b m u * (colL b m u * Matrix.of x)) = 0
    rw [← mul_assoc, colL_sq, zero_mul]; rfl
  obtain ⟨h, he, hu, hG⟩ := h1 _ _ A (eta b' m ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m))
  have hrow : ∀ ξ y, y + A (eta b' m ξ - eta b' m ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m)) y = lmul (toL (rowM m ξ)) y :=
    fun ξ y => by rw [rowM_eq b', lmul_one_add, hA]
  refine ⟨fun ξ => h (eta b' m ξ), he, fun ξ hξ => isUnit_of_inj _ fun y hy => hu _ hξ y (by rw [hrow, hy]), fun α => ?_⟩
  obtain ⟨G, hG⟩ := hG α
  obtain ⟨K, hK⟩ := h2 _ _ G
  obtain ⟨K', β, hK', hβ⟩ := h3 _ _ B hBB K
  refine ⟨β, fun w ξ hw hb hw' => ?_⟩
  haveI : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := h4 _ _ (volume : Measure (Lie E n)) B hBB G K K' hK hK' w (eta b' m ξ) hw hb fun u x => by
    rw [hB, ← lmul_one_add, inner_eta b b' H]
    exact hw' (fun j => crd b j u) x
  simp only [hβ]
  rw [this, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hG, hrow]
  ring
