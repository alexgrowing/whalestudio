import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.MeasurePreservingOfAddEquiv

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace ShNu

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem stable (v : HeightOneSpectrum (𝓞 F)) {L : AddSubgroup (Fin n → Fv F v ⊗[F] E)} (hL : IsCO L) :
    ∃ r > 0, ∀ d : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v d ≤ r → ∀ y ∈ L,
      ((1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) + d).mulVec y ∈ L := by
  obtain ⟨ε, hε, hεL⟩ := exists_ballV_subset (v := v) (U := (L : Set (Fin n → Fv F v ⊗[F] E)))
    (hL.1.mem_nhds L.zero_mem)
  obtain ⟨ρ, hρ⟩ := exists_bound_nV (v := v) hL.2
  obtain ⟨C, hC0, hC⟩ := exists_nM_mulVec v (E := E) n n
  set ρ' := max ρ 0 with hρ'
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  refine ⟨ε / (C * ρ' + 1), by positivity, fun g hg y hy => ?_⟩
  have hy' : nV v y ≤ ρ' := (hρ y hy).trans (le_max_left _ _)
  have hsmall : nV v (g.mulVec y) ≤ ε := by
    calc nV v (g.mulVec y) ≤ C * nM v g * nV v y := hC _ _
      _ ≤ C * (ε / (C * ρ' + 1)) * ρ' :=
          mul_le_mul (mul_le_mul_of_nonneg_left hg hC0) hy' (nV_nonneg _) (by positivity)
      _ = ε * (C * ρ' / (C * ρ' + 1)) := by ring
      _ ≤ ε := mul_le_of_le_one_right hε.le (div_le_one_of_le₀ (by linarith) (by positivity))
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  exact L.add_mem hy (hεL hsmall)

theorem nM_transpose (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : nM v xᵀ = nM v x := by
  apply le_antisymm
  · exact (nM_le_iff (nM_nonneg x)).2 fun i j => nA_le_nM x j i
  · exact (nM_le_iff (nM_nonneg (v := v) (xᵀ : Fin n → Fin n → Fv F v ⊗[F] E))).2 fun i j =>
      nA_le_nM (v := v) (xᵀ : Fin n → Fin n → Fv F v ⊗[F] E) j i

theorem inv_small {C : ℝ} (hC : ∀ x y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v (x * y) ≤ C * nM v x * nM v y)
    {x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (hx : C * nM v x ≤ 1 / 2) (hu : IsUnit (1 + x).det) :
    nM v (((1 + x)⁻¹ - 1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ≤ nM v x := by
  set u : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (1 + x)⁻¹ - 1 with hu_def
  have hmul : (1 + x) * (1 + x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h1 : (1 + x) * (1 + u) = 1 := by rw [hu_def, add_sub_cancel]; exact hmul
  have h2 : (1 + x) * (1 + u) = 1 + (u + (x + x * u)) := by noncomm_ring
  rw [h2] at h1
  have h3 : u + (x + x * u) = 0 := by simpa using h1
  have h4 : u = -(x + x * u) := eq_neg_of_add_eq_zero_left h3
  have e1 : nM v u = nM v (x + x * u) := by
    conv_lhs => rw [h4]
    exact nM_neg (v := v) ((x + x * u : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Fin n → Fin n → Fv F v ⊗[F] E)
  have hb : nM v u ≤ max (nM v x) (C * nM v x * nM v u) :=
    calc nM v u = nM v (x + x * u) := e1
      _ ≤ max (nM v x) (nM v (x * u)) := nM_add_le (v := v) (x : Fin n → Fin n → Fv F v ⊗[F] E) (x * u)
      _ ≤ max (nM v x) (C * nM v x * nM v u) := max_le_max le_rfl (hC _ _)
  by_contra hcon
  push Not at hcon
  have hx0 := nM_nonneg (v := v) x
  rcases le_max_iff.1 hb with h | h
  · linarith
  · have : nM v u ≤ 1 / 2 * nM v u := h.trans (mul_le_mul_of_nonneg_right hx (nM_nonneg _))
    linarith

def cs (σ : E →ₐ[F] E) (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  (x.map (sigR (Fv F v) σ))ᵀ

theorem cs_one_add (σ : E →ₐ[F] E) (x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    cs σ (1 + x) = 1 + cs σ x := by
  simp only [cs]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add,
    Matrix.transpose_one]

theorem isUnit_det_cs (σ : E →ₐ[F] E) {a : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (ha : IsUnit a.det) :
    IsUnit (cs σ a).det := by
  simp only [cs, Matrix.det_transpose]
  have : (a.map (sigR (Fv F v) σ)).det = sigR (Fv F v) σ a.det := (RingHom.map_det _ _).symm
  rw [this]
  exact ha.map _

def Sx (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    Set (Fin n → Fv F v ⊗[F] E) := {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + B.mulVec y'}

theorem measurableSet_Sx {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)} (h₁ : IsCO L₁) (h₂ : IsCO L₂)
    (B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : MeasurableSet (Sx L₁ L₂ B) := by
  have e : Sx L₁ L₂ B = (fun p : (Fin n → Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) => p.1 + B.mulVec p.2) ''
      ((L₁ : Set (Fin n → Fv F v ⊗[F] E)) ×ˢ (L₂ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext z
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩; exact ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
    · rintro ⟨⟨y, y'⟩, ⟨hy, hy'⟩, rfl⟩; exact ⟨y, hy, y', hy', rfl⟩
  rw [e]
  have hc : Continuous fun p : (Fin n → Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) => p.1 + B.mulVec p.2 :=
    continuous_fst.add (Continuous.matrix_mulVec continuous_const continuous_snd)
  exact ((h₁.2.prod h₂.2).image hc).isClosed.measurableSet

def mulVecEquiv (P Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (Fin n → Fv F v ⊗[F] E) ≃+ (Fin n → Fv F v ⊗[F] E) where
  toFun := P.mulVec
  invFun := Q.mulVec
  left_inv y := by simp only [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  right_inv y := by simp only [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add P

end ShNu

open ShNu in

theorem lattice_norm_conj_invariant (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {n : ℕ}
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure] (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (h₁ : IsCO L₁) (h₂ : IsCO L₂) :
    ∃ r > 0, ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r → ∀ B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      nu2 lam L₁ L₂ (((1 + x).map (sigR (Fv F v) σ))ᵀ * B * (1 + x)) = nu2 lam L₁ L₂ B := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_nM_mul v (E := E) n n n
  obtain ⟨Cs, hCs0, hCs⟩ := exists_nM_sig v σ n n
  obtain ⟨rd, hrd, hdet⟩ := exists_isUnit_det v (E := E) n
  obtain ⟨r₁, hr₁, hst₁⟩ := stable v h₁
  obtain ⟨r₂, hr₂, hst₂⟩ := stable v h₂
  set rh : ℝ := 1 / (2 * (Cm + 1)) with hrh
  have hrh0 : 0 < rh := by positivity
  have hrhC : ∀ t, 0 ≤ t → t ≤ rh → Cm * t ≤ 1 / 2 := by
    intro t ht0 ht
    calc Cm * t ≤ (Cm + 1) * rh := mul_le_mul (by linarith) ht ht0 (by linarith)
      _ = 1 / 2 := by rw [hrh]; field_simp
  refine ⟨min (min rd rh) (min r₂ (min r₁ rh / (Cs + 1))), by positivity, fun x hx B => ?_⟩
  have hx0 := nM_nonneg (v := v) x
  have hxd : nM v x ≤ rd := hx.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hxh : nM v x ≤ rh := hx.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hx2 : nM v x ≤ r₂ := hx.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hxs : nM v x ≤ min r₁ rh / (Cs + 1) := hx.trans ((min_le_right _ _).trans (min_le_right _ _))

  have hcs : nM v (cs σ x) ≤ min r₁ rh := by
    calc nM v (cs σ x) = nM v (x.map (sigR (Fv F v) σ)) := nM_transpose _
      _ ≤ Cs * nM v x := hCs x
      _ ≤ (Cs + 1) * nM v x := by nlinarith
      _ ≤ min r₁ rh := by
          rw [le_div_iff₀ (by linarith)] at hxs; linarith
  have hcs0 := nM_nonneg (v := v) (cs σ x)
  have hcs1 : nM v (cs σ x) ≤ r₁ := hcs.trans (min_le_left _ _)
  have hcsh : nM v (cs σ x) ≤ rh := hcs.trans (min_le_right _ _)

  set a : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := 1 + x with ha_def
  have ha : IsUnit a.det := hdet x hxd
  have has : IsUnit (cs σ a).det := isUnit_det_cs σ ha
  have has' : IsUnit (1 + cs σ x).det := by rw [← cs_one_add]; exact has
  have hai : nM v ((a⁻¹ - 1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ≤ r₂ :=
    (inv_small hCm (hrhC _ hx0 hxh) ha).trans hx2
  have hasi : nM v (((cs σ a)⁻¹ - 1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ≤ r₁ := by
    rw [ha_def, cs_one_add]; exact (inv_small hCm (hrhC _ hcs0 hcsh) has').trans hcs1
  have hsplit : ∀ P : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), P = 1 + (P - 1) := fun P => by abel
  have hL2a : ∀ y ∈ L₂, a.mulVec y ∈ L₂ := hst₂ x hx2
  have hL2ai : ∀ y ∈ L₂, a⁻¹.mulVec y ∈ L₂ := by rw [hsplit a⁻¹]; exact hst₂ _ hai
  have hL1as : ∀ y ∈ L₁, (cs σ a).mulVec y ∈ L₁ := by rw [ha_def, cs_one_add]; exact hst₁ _ hcs1
  have hL1asi : ∀ y ∈ L₁, (cs σ a)⁻¹.mulVec y ∈ L₁ := by rw [hsplit (cs σ a)⁻¹]; exact hst₁ _ hasi

  have hPQ : (cs σ a)⁻¹ * cs σ a = 1 := Matrix.nonsing_inv_mul _ has
  have hQP : cs σ a * (cs σ a)⁻¹ = 1 := Matrix.mul_nonsing_inv _ has
  set e := mulVecEquiv _ _ hPQ hQP with he
  have hmp : MeasurePreserving e lam lam := by
    refine measurePreserving_of_addEquiv lam e (Continuous.matrix_mulVec continuous_const continuous_id)
      (Continuous.matrix_mulVec continuous_const continuous_id) (L₁ : Set (Fin n → Fv F v ⊗[F] E)) h₁.2
      (by rw [h₁.1.interior_eq]; exact ⟨0, L₁.zero_mem⟩) ?_
    ext y
    simp only [Set.mem_preimage, SetLike.mem_coe, he, mulVecEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
    constructor
    · intro hy
      have := hL1as _ hy
      rwa [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec] at this
    · exact hL1asi y

  have hset : Sx L₁ L₂ ((a.map (sigR (Fv F v) σ))ᵀ * B * a) = e ⁻¹' Sx L₁ L₂ B := by
    have hcsa : (a.map (sigR (Fv F v) σ))ᵀ = cs σ a := rfl
    rw [hcsa]
    ext z
    simp only [Sx, Set.mem_preimage, Set.mem_setOf_eq, he, mulVecEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨(cs σ a)⁻¹.mulVec y, hL1asi y hy, a.mulVec y', hL2a y' hy', ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ,
        Matrix.one_mul]
    · rintro ⟨y, hy, y', hy', hz⟩
      refine ⟨(cs σ a).mulVec y, hL1as y hy, a⁻¹.mulVec y', hL2ai y' hy', ?_⟩
      have hz' : z = (cs σ a).mulVec ((cs σ a)⁻¹.mulVec z) := by
        rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
      rw [hz', hz, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]
  have hmeas := hmp.measure_preimage (measurableSet_Sx h₁ h₂ B).nullMeasurableSet
  show (lam (Sx L₁ L₂ ((a.map (sigR (Fv F v) σ))ᵀ * B * a)) / lam L₁).toReal = (lam (Sx L₁ L₂ B) / lam L₁).toReal
  rw [hset, hmeas]

end PositivityTheory.SiegelWeilFormula.SwLocFin
