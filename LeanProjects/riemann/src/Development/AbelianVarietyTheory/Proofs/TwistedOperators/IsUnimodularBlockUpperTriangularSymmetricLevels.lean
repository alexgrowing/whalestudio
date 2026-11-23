import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlCharacterEqOneOfTransposeInv

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology

namespace GlobalTheory.LevelUnimod

section General

open scoped Pointwise NNReal ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [SecondCountableTopology G] [T2Space G] [BorelSpace G] in
theorem smul_inj {μ : Measure G} [μ.IsHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, hK, h1⟩ := exists_compact_mem_nhds (1 : G)
  have h2 := congrArg (fun m : Measure G => m K) h
  simp only [Measure.coe_nnreal_smul_apply] at h2
  exact_mod_cast (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds μ h1).ne' hK.measure_lt_top.ne).1 h2

omit [T2Space G] in
theorem map_mul_right_eq (μ : Measure G) [μ.IsHaarMeasure] (g : G) :
    μ.map (fun x => x * g) = Measure.modularCharacter g • μ :=
  Measure.map_right_mul_eq_modularCharacterFun_smul μ g

omit [T2Space G] in

theorem modular_aut (e : G ≃* G) (hc : Continuous e) (hc' : Continuous e.symm) (g : G) :
    Measure.modularCharacter (e g) = Measure.modularCharacter g := by
  let μ : Measure G := Measure.haar
  haveI : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ hc hc'
  refine smul_inj (μ := μ.map e) ?_
  rw [← map_mul_right_eq, ← Measure.map_smul, ← map_mul_right_eq,
    Measure.map_map (measurable_mul_const _) hc.measurable, Measure.map_map hc.measurable (measurable_mul_const _)]
  congr 1
  funext x
  simp

theorem modular_bdd : ∃ K ∈ nhds (1 : G), ∃ C : ℝ≥0, ∀ g ∈ K, Measure.modularCharacter g ≤ C := by
  let μ : Measure G := Measure.haar
  obtain ⟨K, hK, h1⟩ := exists_compact_mem_nhds (1 : G)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ h1).ne'
  have ht : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have ht2 : μ (K * K⁻¹) ≠ ⊤ := (hK.mul hK.inv).measure_lt_top.ne
  refine ⟨K, h1, (μ (K * K⁻¹) / μ K).toNNReal, fun g hg => ?_⟩
  have h2 := congrArg (fun m : Measure G => m K) (map_mul_right_eq μ g)
  simp only [Measure.coe_nnreal_smul_apply] at h2
  rw [Measure.map_apply (measurable_mul_const _) hK.isClosed.measurableSet] at h2
  have h3 : μ ((fun x => x * g) ⁻¹' K) ≤ μ (K * K⁻¹) :=
    measure_mono fun x hx => ⟨x * g, hx, g⁻¹, Set.inv_mem_inv.2 hg, by simp⟩
  rw [h2] at h3
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ENNReal.div_ne_top ht2 h0)]
  exact (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht)).2 h3

theorem modular_eq_one
    (h : ∀ g : G, ∀ U ∈ nhds (1 : G), ∃ g' ∈ U, Measure.modularCharacter g' = Measure.modularCharacter g) (g : G) :
    Measure.modularCharacter g = 1 := by
  obtain ⟨K, hK, C, hC⟩ := modular_bdd (G := G)
  have hb : ∀ x : G, Measure.modularCharacter x ≤ C := fun x => by
    obtain ⟨e, h1, h2⟩ := h x K hK
    rw [← h2]
    exact hC _ h1
  have hle : ∀ x : G, Measure.modularCharacter x ≤ 1 := fun x => by
    by_contra hx
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.1 hx)
    rw [← map_pow] at hk
    exact absurd (hb _) (not_le.2 hk)
  refine le_antisymm (hle g) ?_
  calc (1 : ℝ≥0) = Measure.modularCharacter g * Measure.modularCharacter g⁻¹ := by
        rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ Measure.modularCharacter g * 1 := by gcongr; exact hle _
    _ = _ := mul_one _

end General

theorem modular_restrict {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G)
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (E : G ≃* G) (hc : Continuous E) (hc' : Continuous E.symm) (h1 : ∀ g ∈ S, E g ∈ S)
    (h2 : ∀ g ∈ S, E.symm g ∈ S) (g g' : S) (h : (g' : G) = E g) :
    Measure.modularCharacter g' = Measure.modularCharacter g := by
  let e : S ≃* S :=
    { toFun := fun x => ⟨E x, h1 x x.2⟩
      invFun := fun x => ⟨E.symm x, h2 x x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have : g' = e g := Subtype.ext h
  rw [this]
  exact modular_aut e (Continuous.subtype_mk (hc.comp continuous_subtype_val) _)
    (Continuous.subtype_mk (hc'.comp continuous_subtype_val) _) g

section Mat

variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

def levDiag (lev : ι → ℕ) (t : kˣ) : GL ι k where
  val := diagonal fun r => (t : k) ^ lev r
  inv := diagonal fun r => ((t⁻¹ : kˣ) : k) ^ lev r
  val_inv := by simp [diagonal_mul_diagonal, ← mul_pow]
  inv_val := by simp [diagonal_mul_diagonal, ← mul_pow]

theorem levDiag_inv (lev : ι → ℕ) (t : kˣ) : (levDiag lev t)⁻¹ = levDiag lev t⁻¹ := by
  ext1; rfl

theorem conj_levDiag (lev : ι → ℕ) (t : kˣ) (g : GL ι k) (r s : ι) :
    ((levDiag lev t)⁻¹ * g * levDiag lev t).val r s =
      ((t⁻¹ : kˣ) : k) ^ lev r * g.val r s * (t : k) ^ lev s := by
  rw [levDiag_inv, Units.val_mul, Units.val_mul]
  simp only [levDiag, mul_diagonal, diagonal_mul]

def flipInv (σ : ι ≃ ι) (g : GL ι k) : GL ι k where
  val := (g⁻¹ : GL ι k).valᵀ.submatrix σ σ
  inv := g.valᵀ.submatrix σ σ
  val_inv := by rw [submatrix_mul_equiv, ← transpose_mul, Units.mul_inv, transpose_one, submatrix_one_equiv]
  inv_val := by rw [submatrix_mul_equiv, ← transpose_mul, Units.inv_mul, transpose_one, submatrix_one_equiv]

def flipAut (σ : ι ≃ ι) (hσ : ∀ r, σ (σ r) = r) : GL ι k ≃* GL ι k where
  toFun := flipInv σ
  invFun := flipInv σ
  left_inv g := by
    ext r s
    exact congrArg₂ g.val (hσ r) (hσ s)
  right_inv g := by
    ext r s
    exact congrArg₂ g.val (hσ r) (hσ s)
  map_mul' g h := by
    ext1
    change ((g * h)⁻¹ : GL ι k).valᵀ.submatrix σ σ =
      (g⁻¹ : GL ι k).valᵀ.submatrix σ σ * (h⁻¹ : GL ι k).valᵀ.submatrix σ σ
    rw [submatrix_mul_equiv, ← transpose_mul, _root_.mul_inv_rev, Units.val_mul]

theorem continuous_flipInv [TopologicalSpace k] (σ : ι ≃ ι) : Continuous (flipInv (k := k) σ) :=
  Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_transpose).matrix_submatrix σ σ,
    (Units.continuous_val.matrix_transpose).matrix_submatrix σ σ⟩

end Mat

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem neBot_punctured : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem neBot_units : (Filter.comap (Units.val : kˣ → k) (𝓝 0)).NeBot := by
  haveI := neBot_punctured (k := k)
  refine Filter.comap_neBot fun U hU => ?_
  obtain ⟨x, hx, hx0⟩ := Filter.nonempty_of_mem (inter_mem_nhdsWithin ({0}ᶜ : Set k) hU)
  exact ⟨Units.mk0 x hx, hx0⟩

theorem infinite_field : Infinite k := by
  haveI := neBot_punctured (k := k)
  haveI := t2Space k
  by_contra h
  haveI : Finite k := not_infinite_iff_finite.1 h
  exact (neBot_punctured (k := k)).ne (discreteTopology_iff_nhds_ne.1 inferInstance 0)

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem tendsto_conj (l : ℕ) (L : Fin c → ℕ) (g : GL (n ⊕ Fin c) k)
    (hg : ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => l) L s ≤ Sum.elim (fun _ => l) L r →
      g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) :
    Filter.Tendsto (fun t : kˣ => ((levDiag (Sum.elim (fun _ => l) L) t)⁻¹ * g *
      levDiag (Sum.elim (fun _ => l) L) t).val) (Filter.comap (Units.val : kˣ → k) (𝓝 0))
      (𝓝 (fromBlocks g.val.toBlocks₁₁ 0 0 1)) := by
  set lev : n ⊕ Fin c → ℕ := Sum.elim (fun _ => l) L with hlev
  refine tendsto_pi_nhds.2 fun r => tendsto_pi_nhds.2 fun s => ?_
  simp only [conj_levDiag]
  have hcan : ∀ (t : kˣ) (a : ℕ) (x : k), ((t⁻¹ : kˣ) : k) ^ a * x * (t : k) ^ a = x := fun t a x => by
    rw [mul_right_comm, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  by_cases hR : r.isRight ∨ s.isRight
  · have hlim : fromBlocks g.val.toBlocks₁₁ 0 0 1 r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
      rcases r with r | r <;> rcases s with s | s <;> simp_all [one_apply]
    rw [hlim]
    by_cases hle : lev s ≤ lev r
    · rw [hg r s hR hle]
      by_cases e : r = s
      · subst e
        simp only [hcan]
        exact tendsto_const_nhds
      · simp only [one_apply_ne e, mul_zero, zero_mul]
        exact tendsto_const_nhds
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (not_le.1 hle)
      have e : r ≠ s := fun e => hle (e ▸ le_rfl)
      have h2 : ∀ t : kˣ, ((t⁻¹ : kˣ) : k) ^ lev r * g.val r s * (t : k) ^ lev s =
          g.val r s * (t : k) ^ (d + 1) := fun t => by
        rw [hd, add_assoc, pow_add, ← mul_assoc, hcan]
      simp only [h2, one_apply_ne e]
      have h3 : Continuous fun x : k => g.val r s * x ^ (d + 1) := by fun_prop
      have h4 := (h3.tendsto 0).comp (Filter.tendsto_comap (f := (Units.val : kˣ → k)) (x := 𝓝 0))
      simpa [Function.comp_def] using h4
  · rcases r with r | r <;> rcases s with s | s <;> simp only [Sum.isRight_inl, Sum.isRight_inr, or_true,
      true_or, not_true] at hR
    simp only [hlev, Sum.elim_inl, hcan]
    exact tendsto_const_nhds

end Local

theorem unimodular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c l : ℕ) (L : Fin c → ℕ) (_ : ∀ i, L (Fin.rev i) + L i = 2 * l) (S : Subgroup (GL (n ⊕ Fin c) k)) (_ : ∀ g : GL (n ⊕ Fin c) k, g ∈ S ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => l) L s ≤ Sum.elim (fun _ => l) L r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) (m : Measure S), m.IsHaarMeasure → m.IsMulRightInvariant := by
  intro k _ _ _ _ _ _ n _ _ c l L hL S hS m hm
  haveI := t2Space k
  haveI := infinite_field (k := k)
  haveI := neBot_units (k := k)
  obtain ⟨i1, i2, i3, -⟩ := volGL_haar k (n ⊕ Fin c) Measure.addHaar
  set lev : n ⊕ Fin c → ℕ := Sum.elim (fun _ => l) L with hlev
  have hcl : IsClosed (S : Set (GL (n ⊕ Fin c) k)) := by
    have : (S : Set (GL (n ⊕ Fin c) k)) = ⋂ (r) (s) (_ : r.isRight ∨ s.isRight) (_ : lev s ≤ lev r),
        {g | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
      ext g
      simp only [SetLike.mem_coe, hS, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    refine isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_eq (Units.continuous_val.matrix_elem r s) continuous_const
  haveI : LocallyCompactSpace S := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set (GL (n ⊕ Fin c) k))
  have hX : ∀ x : GL n k, embX c x ∈ S := fun x => by
    rw [hS]
    intro r s hR _
    change fromBlocks x.val 0 0 1 r s = _
    rcases r with r | r <;> rcases s with s | s <;> simp_all [one_apply]

  let σ : n ⊕ Fin c ≃ n ⊕ Fin c := Equiv.sumCongr (Equiv.refl n) Fin.revPerm
  have hσ : ∀ r, σ (σ r) = r := fun r => by rcases r with r | r <;> simp [σ]
  have hσl : ∀ r, lev (σ r) + lev r = 2 * l := fun r => by
    rcases r with r | r
    · simp [σ, hlev, two_mul]
    · simpa [σ, hlev] using hL r
  have hσR : ∀ r, (σ r).isRight = r.isRight := fun r => by rcases r with r | r <;> simp [σ]
  have hflip : ∀ g ∈ S, flipInv σ g ∈ S := fun g hg => by
    rw [hS]
    intro r s hR hle
    change (g⁻¹ : GL (n ⊕ Fin c) k).val (σ s) (σ r) = _
    rw [(hS _).1 (S.inv_mem hg) (σ s) (σ r) (by rw [hσR, hσR]; exact hR.symm)
      (by have := hσl r; have := hσl s; omega)]
    simp only [one_apply, σ.apply_eq_iff_eq, eq_comm]
  have hchar : ∀ x : GL n k, Measure.modularCharacter (⟨embX c x, hX x⟩ : S) = 1 := by
    refine GlobalTheory.gl_character_eq_one_of_transpose_inv k n (Measure.modularCharacter.comp ((embX c).codRestrict S hX)) fun g g' h => ?_
    refine modular_restrict S (flipAut σ hσ) (continuous_flipInv σ) (continuous_flipInv σ) hflip hflip _ _ ?_
    ext r s
    change fromBlocks g'.val 0 0 1 r s = ((embX c g)⁻¹ : GL (n ⊕ Fin c) k).val (σ s) (σ r)
    rw [← map_inv, h]
    change _ = fromBlocks (g⁻¹ : GL n k).val 0 0 1 (σ s) (σ r)
    rcases r with r | r <;> rcases s with s | s <;> simp [σ, one_apply, eq_comm]

  have hconj : ∀ (t : kˣ), ∀ g ∈ S, (levDiag lev t)⁻¹ * g * levDiag lev t ∈ S := fun t g hg => by
    rw [hS]
    intro r s hR hle
    rw [conj_levDiag, (hS _).1 hg r s hR hle]
    by_cases e : r = s
    · subst e
      rw [mul_right_comm, ← mul_pow, Units.inv_mul, one_pow, one_mul]
    · simp only [one_apply_ne e, mul_zero, zero_mul]
  have hone : ∀ g : S, Measure.modularCharacter g = 1 := by
    refine modular_eq_one fun g U hU => ?_
    have t1 := tendsto_conj l L g.1 ((hS _).1 g.2)
    have t2 := tendsto_conj l L (g.1)⁻¹ ((hS _).1 (S.inv_mem g.2))
    rw [← hlev] at t1 t2
    have key : ∀ a b : GL (n ⊕ Fin c) k, a * b = 1 → a ∈ S → b ∈ S →
        a.val.toBlocks₁₁ * b.val.toBlocks₁₁ = 1 := fun a b hab ha hb => by
      have u := (tendsto_conj l L a ((hS _).1 ha)).mul (tendsto_conj l L b ((hS _).1 hb))
      have e : ∀ d : GL (n ⊕ Fin c) k, (d⁻¹ * a * d).val * (d⁻¹ * b * d).val = 1 := fun d => by
        rw [← Units.val_mul, show d⁻¹ * a * d * (d⁻¹ * b * d) = d⁻¹ * (a * b) * d by group, hab]
        simp
      simp only [e] at u
      have := tendsto_nhds_unique u tendsto_const_nhds
      rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at this
      simpa using this.1
    let x : GL n k := ⟨g.1.val.toBlocks₁₁, (g.1)⁻¹.val.toBlocks₁₁,
      key _ _ (mul_inv_cancel _) g.2 (S.inv_mem g.2), key _ _ (inv_mul_cancel _) (S.inv_mem g.2) g.2⟩
    have t3 : Filter.Tendsto (fun t : kˣ => (levDiag lev t)⁻¹ * g.1 * levDiag lev t)
        (Filter.comap (Units.val : kˣ → k) (𝓝 0)) (𝓝 (embX c x)) := by
      rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
      refine Filter.Tendsto.prodMk_nhds t1 ((MulOpposite.continuous_op.tendsto _).comp ?_)
      rw [← map_inv]
      refine t2.congr fun t => ?_
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
    have t4 : Filter.Tendsto (fun t : kˣ => (⟨(levDiag lev t)⁻¹ * g.1 * levDiag lev t, hconj t _ g.2⟩ : S) *
        (⟨embX c x, hX x⟩ : S)⁻¹) (Filter.comap (Units.val : kˣ → k) (𝓝 0)) (𝓝 1) := by
      rw [← mul_inv_cancel (⟨embX c x, hX x⟩ : S)]
      exact (tendsto_subtype_rng.2 t3).mul tendsto_const_nhds
    obtain ⟨t, ht⟩ := (t4.eventually_mem hU).exists
    refine ⟨_, ht, ?_⟩
    have hi : Measure.modularCharacter (⟨embX c x, hX x⟩ : S)⁻¹ = 1 := by
      rw [← hchar x⁻¹]
      congr 1
    rw [map_mul, hi, mul_one]
    refine modular_restrict S (MulAut.conj (levDiag lev t)⁻¹) ?_ ?_ ?_ ?_ _ _ ?_
    · exact (continuous_const.mul continuous_id).mul continuous_const
    · exact (continuous_const.mul continuous_id).mul continuous_const
    · intro a ha
      simpa using hconj t a ha
    · intro a ha
      have := hconj t⁻¹ a ha
      rw [← levDiag_inv] at this
      simpa using this
    · simp
  exact ⟨fun g => by rw [map_mul_right_eq, hone, one_smul]⟩

end GlobalTheory.LevelUnimod
