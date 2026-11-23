import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.UnitriHaar

theorem map_add_nilpotent {k G : Type*} [NormedField k] [IsUltrametricDist k] [ProperSpace k]
    [AddCommGroup G] [Module k G] [Module.Finite k G] [TopologicalSpace G] [IsModuleTopology k G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (N : Module.End k G) (hN : IsNilpotent N) : μ.map (fun x => x + N x) = μ := by
  have : IsTopologicalAddGroup G := IsModuleTopology.topologicalAddGroup k G
  let e₀ : G ≃ₗ[k] (Fin (Module.finrank k G) → k) := (Module.finBasis k G).equivFun
  let e : G ≃ₜ (Fin (Module.finrank k G) → k) :=
    { e₀.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap }
  have : LocallyCompactSpace G := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology G := e.secondCountableTopology
  have hc : ∀ f : Module.End k G, Continuous f := fun f => IsModuleTopology.continuous_of_linearMap f
  let K₀ := IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank k G) → k) one_pos
  let K : AddSubgroup G := K₀.toAddSubgroup.comap e₀.toLinearMap.toAddMonoidHom
  have hKo : IsOpen (K : Set G) := K₀.isOpen.preimage e.continuous
  have hKc : IsCompact (K : Set G) :=
    e.isCompact_preimage.2 (isCompact_closedBall (0 : Fin (Module.finrank k G) → k) 1)
  obtain ⟨m, hm⟩ := hN
  let B : AddSubgroup G := ⨅ j : ℕ, K.comap (N ^ j).toAddMonoidHom
  have hB : ∀ x, x ∈ B ↔ ∀ j : ℕ, (N ^ j) x ∈ K := fun x => by
    simp [B, AddSubgroup.mem_iInf]
  have hBo : IsOpen (B : Set G) := by
    have : (B : Set G) = ⋂ j ∈ Finset.range m, (N ^ j : Module.End k G) ⁻¹' (K : Set G) := by
      ext x
      simp only [SetLike.mem_coe, hB, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
      refine ⟨fun h j _ => h j, fun h j => ?_⟩
      by_cases hj : j < m
      · exact h j hj
      · rw [pow_eq_zero_of_le (not_lt.1 hj) hm]; exact K.zero_mem
    rw [this]
    exact isOpen_biInter_finset fun j _ => hKo.preimage (hc _)
  have hBc : IsCompact (B : Set G) :=
    hKc.of_isClosed_subset (B.isClosed_of_isOpen hBo) fun x hx => by
      simpa using (hB x).1 hx 0
  have hNB : ∀ x ∈ B, N x ∈ B := fun x hx => (hB _).2 fun j => by
    rw [← Module.End.mul_apply, ← pow_succ]; exact (hB x).1 hx _
  have hNp : ∀ (j : ℕ), ∀ x ∈ B, ((-N) ^ j) x ∈ B := fun j => by
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      exact B.neg_mem (hNB _ (ih x hx))
  have hm' : (-N) ^ m = 0 := by rw [neg_pow, hm, mul_zero]
  have h1 : (∑ j ∈ Finset.range m, (-N) ^ j) * (1 + N) = 1 := by
    have := geom_sum_mul_neg (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  have h2 : (1 + N) * (∑ j ∈ Finset.range m, (-N) ^ j) = 1 := by
    have := mul_neg_geom_sum (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  let L : G ≃ₜ+ G :=
    { toFun := fun x => x + N x
      invFun := (∑ j ∈ Finset.range m, (-N) ^ j : Module.End k G)
      left_inv := fun x => LinearMap.congr_fun h1 x
      right_inv := fun x => LinearMap.congr_fun h2 x
      map_add' := fun x y => by rw [map_add]; abel
      continuous_toFun := continuous_id.add (hc N)
      continuous_invFun := hc _ }
  have hLB : L ⁻¹' (B : Set G) = B := by
    ext x
    refine ⟨fun hx => ?_, fun hx => B.add_mem hx (hNB x hx)⟩
    have : x = (∑ j ∈ Finset.range m, (-N) ^ j : Module.End k G) (L x) := (L.left_inv x).symm
    rw [this, LinearMap.sum_apply]
    exact B.sum_mem fun j _ => hNp j _ hx
  change μ.map L = μ
  have : (μ.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have h3 := Measure.isAddLeftInvariant_eq_smul (μ.map L) μ
  have h4 : μ.map L B = μ B := by
    rw [Measure.map_apply (show Continuous L from L.continuous).measurable hBo.measurableSet, hLB]
  have h5 : μ B ≠ 0 := (hBo.measure_pos μ ⟨0, B.zero_mem⟩).ne'
  have h6 : μ B ≠ ⊤ := hBc.measure_lt_top.ne
  have h7 : Measure.addHaarScalarFactor (μ.map L) μ = 1 := by
    rw [h3, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
    have := (ENNReal.mul_left_inj h5 h6).1 (h4.trans (one_mul _).symm)
    exact_mod_cast this
  rw [h3, h7, one_smul]

theorem nilpotent_of_strict {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ a b, ¬ a < b → A a b = 0) : A ^ n = 0 := by
  have : ∀ (j : ℕ) (a b : Fin n), b.val < a.val + j → (A ^ j) a b = 0 := fun j => by
    induction j with
    | zero => intro a b h; rw [pow_zero, Matrix.one_apply_ne]; rintro rfl; omega
    | succ j ih =>
      intro a b h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c < b
      · rw [ih a c (by have : c.val < b.val := hc; omega), zero_mul]
      · rw [hA c b hc, mul_zero]
  exact Matrix.ext fun a b => this n a b (by omega)

def strictOf (R : Type*) [CommRing R] (n : ℕ) :
    ({p : Fin n × Fin n // p.1 < p.2} → R) →ₗ[R] Matrix (Fin n) (Fin n) R where
  toFun x := Matrix.of fun a b => if h : a < b then x ⟨(a, b), h⟩ else 0
  map_add' x y := by ext a b; simp only [Matrix.add_apply, Matrix.of_apply]; split_ifs <;> simp
  map_smul' c x := by ext a b; simp only [Matrix.smul_apply, Matrix.of_apply]; split_ifs <;> simp

def above (R : Type*) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →ₗ[R] ({p : Fin n × Fin n // p.1 < p.2} → R) where
  toFun A p := A p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_nilpotent {R : Type*} [CommRing R] {n : ℕ} (u : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ i, u i i = 1) (h0 : ∀ i j, j < i → u i j = 0) :
    ∃ N : Module.End R ({p : Fin n × Fin n // p.1 < p.2} → R), IsNilpotent N ∧
      ∀ x : {p : Fin n × Fin n // p.1 < p.2} → R,
        (fun p : {p : Fin n × Fin n // p.1 < p.2} => (u * Matrix.of (fun a b : Fin n =>
          (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : R))) p.1.1 p.1.2) =
        above R n u + (x + N x) := by
  have hu : ∀ a b, ¬ a < b → (u - 1) a b = 0 := fun a b h => by
    rcases (not_lt.1 h).eq_or_lt with rfl | h
    · simp [h1]
    · simp [h0 a b h, Matrix.one_apply_ne h.ne']
  have hs : ∀ x a b, ¬ a < b → strictOf R n x a b = 0 := fun x a b h => dif_neg h
  have has : ∀ x, above R n (strictOf R n x) = x := fun x => funext fun p => dif_pos p.2
  let N : Module.End R ({p : Fin n × Fin n // p.1 < p.2} → R) :=
    above R n ∘ₗ LinearMap.mulLeft R (u - 1) ∘ₗ strictOf R n
  have hN : ∀ x, strictOf R n (N x) = (u - 1) * strictOf R n x := fun x => by
    ext a b
    by_cases h : a < b
    · exact dif_pos h
    · rw [hs _ a b h, Matrix.mul_apply]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      by_cases hc : a < c
      · rw [hs x c b fun h' => h (hc.trans h'), mul_zero]
      · rw [hu a c hc, zero_mul]
  have hp : ∀ (j : ℕ) x, strictOf R n ((N ^ j) x) = (u - 1) ^ j * strictOf R n x := fun j => by
    induction j with
    | zero => simp
    | succ j ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, hN, ih, mul_assoc]
  refine ⟨N, ⟨n, LinearMap.ext fun x => ?_⟩, fun x => ?_⟩
  · rw [← has ((N ^ n) x), hp, nilpotent_of_strict _ hu, zero_mul, map_zero, LinearMap.zero_apply]
  · have : Matrix.of (fun a b : Fin n =>
        (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : R)) = 1 + strictOf R n x := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [hs x a a (lt_irrefl a)]
      · simp [hab, strictOf]
    rw [this]
    change above R n (u * (1 + strictOf R n x)) = _
    have h2 : u * (1 + strictOf R n x) = u + (strictOf R n x + (u - 1) * strictOf R n x) := by
      noncomm_ring
    rw [h2, map_add, map_add, has]
    rfl

open GlobalTheory.GaugeEx in

theorem map_unitri_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) (μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E)), μU.IsAddHaarMeasure → ∀ u : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → μU.map (fun (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}) => (u * Matrix.of (fun a b : Fin (r + 1) => (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E))) p.1.1 p.1.2) = μU := by
  intro F E _ _ _ _ _ v r μ hμ u h1 h0
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨N, hN, hx⟩ := exists_nilpotent u h1 h0
  have hN' : IsNilpotent (N.restrictScalars (Fv F v) : Module.End (Fv F v) _) := by
    obtain ⟨m, hm⟩ := hN
    refine ⟨m, LinearMap.ext fun x => ?_⟩
    have := LinearMap.congr_fun hm x
    rw [Module.End.pow_apply] at this ⊢
    exact this
  have h2 := map_add_nilpotent μ _ hN'
  have hc : Continuous fun x => x + N.restrictScalars (Fv F v) x :=
    continuous_id.add (IsModuleTopology.continuous_of_linearMap _)
  rw [funext hx]
  refine Eq.trans ?_ (map_add_left_eq_self μ (above _ (r + 1) u))
  conv_rhs => rw [← h2]
  rw [Measure.map_map (measurable_const_add _) hc.measurable]
  rfl

end GlobalTheory.UnitriHaar
