import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilpotentOfStrict

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.UnitriTuple

theorem exists_compactOpen (k G : Type*) [NormedField k] [IsUltrametricDist k] [ProperSpace k]
    [AddCommGroup G] [Module k G] [Module.Finite k G] [TopologicalSpace G] [IsModuleTopology k G] :
    ∃ K : AddSubgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) := by
  have : IsTopologicalAddGroup G := IsModuleTopology.topologicalAddGroup k G
  let e₀ : G ≃ₗ[k] (Fin (Module.finrank k G) → k) := (Module.finBasis k G).equivFun
  let e : G ≃ₜ (Fin (Module.finrank k G) → k) :=
    { e₀.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap }
  let K₀ := IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank k G) → k) one_pos
  exact ⟨K₀.toAddSubgroup.comap e₀.toLinearMap.toAddMonoidHom, K₀.isOpen.preimage e.continuous,
    e.isCompact_preimage.2 (isCompact_closedBall (0 : Fin (Module.finrank k G) → k) 1)⟩

theorem map_add_nilpotent_of_compactOpen {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (K : AddSubgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (N : Module.End ℤ G) (hNc : Continuous N) (hN : IsNilpotent N) :
    μ.map (fun x => x + N x) = μ := by
  have hpow : ∀ (f : Module.End ℤ G), Continuous f → ∀ j : ℕ, Continuous (f ^ j : Module.End ℤ G) :=
    fun f hf j => by rw [Module.End.coe_pow]; exact hf.iterate j
  have hnegc : Continuous (-N : Module.End ℤ G) := by
    have : ⇑(-N : Module.End ℤ G) = fun x => -(N x) := rfl
    rw [this]; exact hNc.neg
  obtain ⟨m, hm⟩ := hN
  let B : AddSubgroup G := ⨅ j : ℕ, K.comap (N ^ j).toAddMonoidHom
  have hB : ∀ x, x ∈ B ↔ ∀ j : ℕ, (N ^ j) x ∈ K := fun x => by
    simp [B, AddSubgroup.mem_iInf]
  have hBo : IsOpen (B : Set G) := by
    have : (B : Set G) = ⋂ j ∈ Finset.range m, (N ^ j : Module.End ℤ G) ⁻¹' (K : Set G) := by
      ext x
      simp only [SetLike.mem_coe, hB, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
      refine ⟨fun h j _ => h j, fun h j => ?_⟩
      by_cases hj : j < m
      · exact h j hj
      · rw [pow_eq_zero_of_le (not_lt.1 hj) hm]; exact K.zero_mem
    rw [this]
    exact isOpen_biInter_finset fun j _ => hKo.preimage (hpow N hNc j)
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
  have hinv : Continuous (∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G) := by
    have : ⇑(∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G) =
        fun x => ∑ j ∈ Finset.range m, ((-N) ^ j : Module.End ℤ G) x :=
      funext fun x => LinearMap.sum_apply _ _ _
    rw [this]
    exact continuous_finset_sum _ fun j _ => hpow _ hnegc j
  let L : G ≃ₜ+ G :=
    { toFun := fun x => x + N x
      invFun := (∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G)
      left_inv := fun x => LinearMap.congr_fun h1 x
      right_inv := fun x => LinearMap.congr_fun h2 x
      map_add' := fun x y => by rw [map_add]; abel
      continuous_toFun := continuous_id.add hNc
      continuous_invFun := hinv }
  have hLB : L ⁻¹' (B : Set G) = B := by
    ext x
    refine ⟨fun hx => ?_, fun hx => B.add_mem hx (hNB x hx)⟩
    have : x = (∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G) (L x) := (L.left_inv x).symm
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

theorem sub_one_pow {R : Type*} [CommRing R] {a : ℕ} (u : Matrix (Fin a) (Fin a) R)
    (h1 : ∀ i, u i i = 1) (h0 : ∀ i j, j < i → u i j = 0) : (u - 1) ^ a = 0 := by
  refine GlobalTheory.UnitriHaar.nilpotent_of_strict _ fun i j h => ?_
  rcases (not_lt.1 h).eq_or_lt with rfl | h
  · simp [h1]
  · simp [h0 i j h, Matrix.one_apply_ne h.ne']

def colOp {R : Type*} [CommRing R] {a n : ℕ} (w : Matrix (Fin a) (Fin a) R) :
    Module.End R (Fin a → Fin n → R) where
  toFun X b := ∑ c, w c b • X c
  map_add' X Y := by funext b; simp [Finset.sum_add_distrib, smul_add]
  map_smul' r X := by funext b; simp [Finset.smul_sum, smul_comm r]

theorem colOp_pow {R : Type*} [CommRing R] {a n : ℕ} (w : Matrix (Fin a) (Fin a) R) (j : ℕ)
    (X : Fin a → Fin n → R) (b : Fin a) :
    ((colOp (n := n) w ^ j) X) b = ∑ c, (w ^ j) c b • X c := by
  induction j generalizing b with
  | zero => simp [Matrix.one_apply]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ]
    change ∑ c, w c b • (((colOp (n := n) w ^ j) X) c) = _
    simp only [ih, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by rw [mul_comm]

open GlobalTheory.GaugeEx in

theorem unitri_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun X b => ∑ c, u c b • X c) = μ) ∧ ∀ ν : Measure (HermR (Fv F v) σ a), ν.IsAddHaarMeasure → ∀ φ : HermR (Fv F v) σ a → HermR (Fv F v) σ a, (∀ S, (φ S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u) → ν.map φ = ν := by
  intro F E _ _ _ _ _ σ _ n J _ v a u h1 h0
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨fun μ hμ => ?_, fun ν hν φ hφ => ?_⟩
  · let N := colOp (n := n) (u - 1)
    have hN : IsNilpotent N := ⟨a, LinearMap.ext fun X => funext fun b => by
      rw [colOp_pow, sub_one_pow u h1 h0]; simp⟩
    have hN' : IsNilpotent (N.restrictScalars (Fv F v) : Module.End (Fv F v) _) := by
      obtain ⟨m, hm⟩ := hN
      refine ⟨m, LinearMap.ext fun x => ?_⟩
      have := LinearMap.congr_fun hm x
      rw [Module.End.pow_apply] at this ⊢
      exact this
    have h2 := GlobalTheory.UnitriHaar.map_add_nilpotent μ _ hN'
    have hx : (fun (X : Fin a → Fin n → Fv F v ⊗[F] E) b => ∑ c, u c b • X c) =
        fun X => X + N.restrictScalars (Fv F v) X := by
      funext X b
      change _ = X b + ∑ c, (u - 1) c b • X c
      simp [sub_smul, Finset.sum_sub_distrib, Matrix.one_apply]
    rw [hx]; exact h2
  · have hTR : IsTopologicalRing (Fv F v) := inferInstance
    let Ev := Fv F v ⊗[F] E
    have : LocallyCompactSpace (Matrix (Fin a) (Fin a) Ev) :=
      inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ev))
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) Ev) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ev))
    have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
    have hc : IsClosed (HermR (Fv F v) σ a : Set (Matrix (Fin a) (Fin a) Ev)) := by
      have : (HermR (Fv F v) σ a : Set (Matrix (Fin a) (Fin a) Ev)) =
          ⋂ i, ⋂ j, {S | sigR (Fv F v) σ (S j i) = S i j} := by
        ext S
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rfl
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
      · exact (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Fv F v) σ).comp (continuous_id.matrix_elem j i)
      · exact continuous_id.matrix_elem i j
    have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
      hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : SecondCountableTopology (HermR (Fv F v) σ a) :=
      hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
    obtain ⟨K₀, hK₀o, hK₀c⟩ := exists_compactOpen (Fv F v) (Fin a → Fin a → Ev)
    let K : AddSubgroup (HermR (Fv F v) σ a) :=
      AddSubgroup.comap (HermR (Fv F v) σ a).subtype K₀
    have hKo : IsOpen (K : Set (HermR (Fv F v) σ a)) := hK₀o.preimage continuous_subtype_val
    have hKc : IsCompact (K : Set (HermR (Fv F v) σ a)) :=
      hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK₀c
    set A : Matrix (Fin a) (Fin a) Ev := (u.map (sigR (Fv F v) σ)).transpose with hA
    have hS1 : ∀ i, (u.map (sigR (Fv F v) σ)) i i = 1 := fun i => by simp [h1]
    have hS0 : ∀ i j, j < i → (u.map (sigR (Fv F v) σ)) i j = 0 := fun i j h => by simp [h0 i j h]
    have hAn : (A - 1) ^ a = 0 := by
      have := sub_one_pow _ hS1 hS0
      have h3 : A - 1 = (u.map (sigR (Fv F v) σ) - 1).transpose := by
        rw [Matrix.transpose_sub, Matrix.transpose_one]
      rw [h3, ← Matrix.transpose_pow, this, Matrix.transpose_zero]
    have hun : (u - 1) ^ a = 0 := sub_one_pow u h1 h0
    let La : Module.End Ev (Matrix (Fin a) (Fin a) Ev) := LinearMap.mulLeft Ev A
    let Ru : Module.End Ev (Matrix (Fin a) (Fin a) Ev) := LinearMap.mulRight Ev u
    have hLR : Commute La Ru := LinearMap.commute_mulLeft_right A u
    have hLn : IsNilpotent (La - 1) := by
      have : La - 1 = LinearMap.mulLeft Ev (A - 1) := by
        ext1 S; simp [La, sub_mul]
      rw [this]
      exact ⟨a, by rw [LinearMap.pow_mulLeft, hAn, LinearMap.mulLeft_zero_eq_zero]⟩
    have hRn : IsNilpotent (Ru - 1) := by
      have : Ru - 1 = LinearMap.mulRight Ev (u - 1) := by
        ext1 S; simp [Ru, mul_sub]
      rw [this]
      exact ⟨a, by rw [LinearMap.pow_mulRight, hun, LinearMap.mulRight_zero_eq_zero]⟩
    have hTn : IsNilpotent (La * Ru - 1) := by
      have : La * Ru - 1 = (La - 1) * Ru + (Ru - 1) := by noncomm_ring
      rw [this]
      have c1 : Commute (La - 1) Ru := hLR.sub_left (Commute.one_left _)
      have c2 : Commute ((La - 1) * Ru) (Ru - 1) :=
        Commute.mul_left (c1.sub_right (Commute.one_right _))
          ((Commute.refl Ru).sub_right (Commute.one_right _))
      exact c2.isNilpotent_add (c1.isNilpotent_mul_right hLn) hRn
    have hadd : ∀ S S', φ (S + S') = φ S + φ S' := fun S S' => Subtype.ext (by
      rw [AddSubgroup.coe_add, hφ, hφ, hφ, AddSubgroup.coe_add, mul_add, add_mul])
    let N₀ : HermR (Fv F v) σ a →+ HermR (Fv F v) σ a :=
      AddMonoidHom.mk' (fun S => φ S - S) fun S S' => by rw [hadd]; abel
    let N : Module.End ℤ (HermR (Fv F v) σ a) := N₀.toIntLinearMap
    have hNa : ∀ S, ((N S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) =
        (La * Ru - 1) (S : Matrix (Fin a) (Fin a) Ev) := fun S => by
      change ((φ S - S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) = _
      rw [AddSubgroup.coe_sub, hφ]
      simp [La, Ru, mul_assoc]
    have hNp : ∀ (j : ℕ) S, (((N ^ j) S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) =
        ((La * Ru - 1) ^ j) (S : Matrix (Fin a) (Fin a) Ev) := fun j => by
      induction j with
      | zero => intro S; simp
      | succ j ih =>
        intro S
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hNa, ih]
    have hN : IsNilpotent N := by
      obtain ⟨m, hm⟩ := hTn
      refine ⟨m, LinearMap.ext fun S => Subtype.ext ?_⟩
      rw [hNp, hm]; rfl
    have hNc : Continuous N := by
      refine continuous_induced_rng.2 ?_
      have : (Subtype.val ∘ ⇑N) = fun S : HermR (Fv F v) σ a =>
          A * (S : Matrix (Fin a) (Fin a) Ev) * u - (S : Matrix (Fin a) (Fin a) Ev) :=
        funext fun S => by
          change ((N S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) = _
          rw [hNa]; simp [La, Ru, mul_assoc]
      rw [this]
      exact ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).sub
        continuous_subtype_val
    have h2 := map_add_nilpotent_of_compactOpen ν K hKo hKc N hNc hN
    have hx : φ = fun S => S + N S := funext fun S => by
      change φ S = S + (φ S - S); abel
    rw [hx]; exact h2

end GlobalTheory.UnitriTuple
