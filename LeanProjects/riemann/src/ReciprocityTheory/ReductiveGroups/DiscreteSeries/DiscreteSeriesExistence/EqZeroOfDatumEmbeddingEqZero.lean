import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def IsPsiFor (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Prop :=
  (∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
    Ψ 1 = 1 ∧ S7.SmoothOnGV ε Ψ ∧
    (∀ g, inUJ ε g → S7.casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
    ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure → MemLp (fun g : S7.UJ ε => Ψ (S7.toM g)) 2 μ

theorem exists_isPsiFor (hS7 : S7.PsiExistsStatement n) {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    (T : S7.KType ε (lowK ε lam)) (hlam : S7.IsHCParam lam) (hh : GapAtLeast ε lam h) (hq : 1 ≤ S7.q0 ε)
    (h8 : 8 * (n : ℝ) * S7.q0 ε < h) :
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V), IsPsiFor ε lam T Ψ ∧
      ∀ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (S7.toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))) := by
  obtain ⟨Ψ, h1, h2, h3, h4, h5, h6⟩ := hS7 ε lam h T hlam hh hq
  exact ⟨Ψ, ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 h8⟩, h5⟩

section Datum

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}

def jfun (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ v : T.V) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => inner ℂ v₀ (Ψ g v)

def uniformisationL2 (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ v : T.V) : L2 ε :=
  toL2 ε (jfun Ψ v₀ v)

def datumV (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) :
    Submodule ℂ (smD ε (rreg ε)) :=
  (Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀))).comap (smD ε (rreg ε)).subtype

variable {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem jfun_CasF (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) :
    ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.CasF ε (jfun Ψ v₀ v) g = ((casVal lam : ℝ) : ℂ) * jfun Ψ v₀ v g := by
  intro g hg
  have e := pdA_casF_clm (pdA_coef v₀ v) (f := Ψ) hP.2.2.1 (g := g) hg
  rw [show jfun Ψ v₀ v = fun x => pdA_coef v₀ v (Ψ x) from rfl, e, hP.2.2.2.1 g hg, map_smul, smul_eq_mul]

def dt_jfunLin (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) :
    T.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  toFun := jfun Ψ v₀
  map_add' v w := funext fun x => by simp [jfun]
  map_smul' c v := funext fun x => by simp [jfun]

theorem dt_memLp (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have hH : (Formalism.REAL.muG ε).IsHaarMeasure := by
    unfold Formalism.REAL.muG
    infer_instance
  have h := hP.2.2.2.2 (Formalism.REAL.muG ε) hH
  exact ((innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ T.V v)).comp_memLp' h

theorem datumFunction_isSmoothL2 (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) : IsSmoothL2 ε (jfun Ψ v₀ v) := by
  refine isSmoothL2_of_casimir_eigen ε (LinearMap.range (dt_jfunLin Ψ v₀)) ((casVal lam : ℝ) : ℂ) inferInstance
    ?_ ?_ ?_ ?_ (jfun Ψ v₀ v) (LinearMap.mem_range.2 ⟨v, rfl⟩)
  · intro w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    exact pdA_smooth_clm (pdA_coef v₀ u) (f := Ψ) hP.2.2.1
  · intro w hw i j hij
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    exact ⟨jfun Ψ v₀ (T.dτ (Matrix.single i j 1) u), LinearMap.mem_range.2 ⟨_, rfl⟩,
      fun g hg => pdA_eab_compact T hP.1 v₀ u hij hg⟩
  · intro w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    exact jfun_CasF hP v₀ u
  · intro w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    exact dt_memLp hP v₀ u

theorem datumEmbedding_mem_smooth (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) : uniformisationL2 ε Ψ v₀ v ∈ smD ε (rreg ε) := by
  exact toL2_mem_smD_of_isSmoothL2 (datumFunction_isSmoothL2 hP v₀ v)

theorem datumEmbedding_add (hP : IsPsiFor ε lam T Ψ) (v₀ v v' : T.V) :
    uniformisationL2 ε Ψ v₀ (v + v') = uniformisationL2 ε Ψ v₀ v + uniformisationL2 ε Ψ v₀ v' := by
  have h1 := dt_memLp hP v₀ v
  have h2 := dt_memLp hP v₀ v'
  have h3 := dt_memLp hP v₀ (v + v')
  simp only [uniformisationL2, toL2, dif_pos h1, dif_pos h2, dif_pos h3]
  rw [← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun g => by simp [jfun, inner_add_right])

theorem datumEmbedding_smul (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) (c : ℂ) (v : T.V) :
    uniformisationL2 ε Ψ v₀ (c • v) = c • uniformisationL2 ε Ψ v₀ v := by
  have h1 := dt_memLp hP v₀ v
  have h3 := dt_memLp hP v₀ (c • v)
  simp only [uniformisationL2, toL2, dif_pos h1, dif_pos h3]
  rw [← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun g => by simp [jfun, inner_smul_right])

def datumEmbeddingToL2 (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] L2 ε where
  toFun := uniformisationL2 ε Ψ v₀
  map_add' := datumEmbedding_add hP v₀
  map_smul' := datumEmbedding_smul hP v₀

private theorem toL2_congr_of_eq_on_umat (F G : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ g : Formalism.REAL.UJ ε, F (Formalism.MainNotions.S.umat g) = G (Formalism.MainNotions.S.umat g)) : toL2 ε F = toL2 ε G := by
  have hfg : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) := funext h
  unfold toL2
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hfg ▸ hF
    rw [dif_pos hF, dif_pos hG]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall h)
  · have hG : ¬ MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hfg ▸ hF
    rw [dif_neg hF, dif_neg hG]

theorem rightRegular_datumEmbedding (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) (k : S7.KG ε) :
    rreg ε (S7.toMK k) (uniformisationL2 ε Ψ v₀ v) = uniformisationL2 ε Ψ v₀ (T.op k v) := by
  have hk : S7.toMK k ∈ UJset ε := by
    simp [S7.toMK, UJset]
    exact (k : S7.UJ ε).2
  rw [uniformisationL2, uniformisationL2, rightRegular_toL2 ε _ hk]
  apply toL2_congr_of_eq_on_umat
  intro x
  have h1 := hP.1 1 k (Formalism.MainNotions.S.umat x) x.2
  rw [show S7.toMK (1 : S7.KG ε) = 1 by simp [S7.toMK], one_mul] at h1
  simp only [jfun]
  rw [h1]
  clear h1 hk hP
  first
  | rw [T.op_one]; simp
  | rw [T.map_one]; simp
  | rw [map_one]; simp
  | simp [S7.KType.op]

theorem rightDerivative_datum_embedding (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) {a b : Fin n} (hab : ε a = ε b) :
    ((smE ε (rreg ε) a b ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩ : smD ε (rreg ε)) : L2 ε) =
      uniformisationL2 ε Ψ v₀ (T.dτ (Matrix.single a b 1) v) := by
  exact (rightDerivative_toL2 (datumFunction_isSmoothL2 hP v₀ v) a b).trans
    (toL2_congr_of_forall_inUJ_eq fun g hg => pdA_eab_compact T hP.1 v₀ v hab hg)

theorem mem_datumV_iff (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) (x : smD ε (rreg ε)) :
    x ∈ datumV ε Ψ v₀ ↔ ∃ v : T.V, (x : L2 ε) = uniformisationL2 ε Ψ v₀ v := by
  have hr : Set.range (uniformisationL2 ε Ψ v₀) =
      ((LinearMap.range (datumEmbeddingToL2 hP v₀) : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    ext x
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    rfl
  simp only [datumV, Submodule.mem_comap, Submodule.coe_subtype]
  rw [hr, Submodule.span_eq, LinearMap.mem_range]
  exact exists_congr fun w => eq_comm

theorem datumV_casimir (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    ∀ v ∈ datumV ε Ψ v₀, casimir (smE ε (rreg ε)) v = ((casVal lam : ℝ) : ℂ) • v := by
  intro x hx
  obtain ⟨v, hv⟩ := (mem_datumV_iff hP v₀ x).1 hx
  have hF := datumFunction_isSmoothL2 hP v₀ v
  have hx' : x = ⟨toL2 ε (jfun Ψ v₀ v), toL2_mem_smD_of_isSmoothL2 hF⟩ := Subtype.ext hv
  have key : ∀ a b, ((smE ε (rreg ε) a b (smE ε (rreg ε) b a x) : smD ε (rreg ε)) : L2 ε) =
      toL2 ε (Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v))) := by
    intro a b
    have h1 : smE ε (rreg ε) b a x =
        ⟨toL2 ε (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)), toL2_mem_smD_of_isSmoothL2 (hF.Eab b a)⟩ :=
      Subtype.ext (by rw [hx']; exact rightDerivative_toL2 hF b a)
    rw [h1]
    exact rightDerivative_toL2 (hF.Eab b a) a b
  have hG : ∀ a b, MemLp (fun g : Formalism.REAL.UJ ε =>
      Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    fun a b => ((hF.Eab b a).Eab a b).2 []
  apply Subtype.ext
  rw [Submodule.coe_smul, hv]
  unfold casimir
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, key]
  calc ∑ a, ∑ b, toL2 ε (Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)))
      = ∑ a, toL2 ε (fun x => ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)) x) :=
        Finset.sum_congr rfl fun a _ => (toL2_finset_sum_of_memLp _ _ fun b => hG a b).symm
    _ = toL2 ε (fun x => ∑ a, ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)) x) :=
        (toL2_finset_sum_of_memLp _ (fun a x => ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)) x)
          fun a => memLp_finsetSum _ fun b _ => hG a b).symm
    _ = toL2 ε (((casVal lam : ℝ) : ℂ) • jfun Ψ v₀ v) := toL2_congr_of_forall_inUJ_eq fun g hg => by
        rw [Pi.smul_apply, smul_eq_mul, ← jfun_CasF hP v₀ v g hg]
        rfl
    _ = ((casVal lam : ℝ) : ℂ) • uniformisationL2 ε Ψ v₀ v := toL2_smul_smooth ε _ _

theorem datumV_kStable (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    ∀ k ∈ Kset ε, ∀ v ∈ datumV ε Ψ v₀, ∃ w ∈ datumV ε Ψ v₀, (w : L2 ε) = rreg ε k v := by
  intro k hk x hx
  obtain ⟨u, hu⟩ := (mem_datumV_iff hP v₀ x).1 hx
  have hK : ∃ k' : S7.KG ε, S7.toMK k' = k := by
    clear hu hx hP
    refine ⟨⟨⟨⟨k, star k, ?_, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · exact Matrix.mem_unitaryGroup_iff.1 hk.1
    · exact Matrix.mem_unitaryGroup_iff'.1 hk.1
    · show kᴴ * Jm ε * k = Jm ε
      rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
        Matrix.mem_unitaryGroup_iff'.1 hk.1, Matrix.one_mul]
    · first
      | exact hk
      | exact ⟨hk.1, hk.2⟩
      | exact hk.2
      | exact hk.2.symm
      | (simp only [S7.KG, Kset] at hk ⊢; done)
  obtain ⟨k', rfl⟩ := hK
  refine ⟨⟨uniformisationL2 ε Ψ v₀ (T.op k' u), datumEmbedding_mem_smooth hP v₀ _⟩, (mem_datumV_iff hP v₀ _).2 ⟨_, rfl⟩, ?_⟩
  rw [hu, rightRegular_datumEmbedding hP v₀ u k']

theorem datumEmbedding_self_ne_zero (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) : uniformisationL2 ε Ψ v₀ v₀ ≠ 0 := by
  intro h0
  have hm := dt_memLp hP v₀ v₀
  have hc : Continuous (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v₀ (Formalism.MainNotions.S.umat g)) := by
    rw [continuous_iff_continuousAt]
    intro g
    obtain ⟨U, F, hU, hgU, hF, hEq⟩ := hP.2.2.1 (Formalism.MainNotions.S.umat g) g.2
    have hFc : ContinuousAt F (Formalism.MainNotions.S.umat g) := by
      first
      | (letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAddCommGroup
         letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
         exact hF.continuousOn.continuousAt (hU.mem_nhds hgU))
      | (letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
         letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
         exact hF.continuousOn.continuousAt (hU.mem_nhds hgU))
      | (letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
         letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedSpace
         exact hF.continuousOn.continuousAt (hU.mem_nhds hgU))
    have hev : (fun y : Formalism.REAL.UJ ε => jfun Ψ v₀ v₀ (Formalism.MainNotions.S.umat y)) =ᶠ[nhds g]
        fun y => inner ℂ v₀ (F (Formalism.MainNotions.S.umat y) v₀) := by
      filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with y hy
      simp only [jfun, hEq _ hy y.2]
    refine ContinuousAt.congr ?_ hev.symm
    exact ((innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ T.V v₀)).continuous.continuousAt.comp
      (hFc.comp hc.continuousAt)
  have hae : (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v₀ (Formalism.MainNotions.S.umat g)) =ᵐ[Formalism.REAL.muG ε] 0 := by
    have h1 : uniformisationL2 ε Ψ v₀ v₀ = hm.toLp _ := by simp only [uniformisationL2, toL2, dif_pos hm]
    rw [h1] at h0
    have h2 := hm.coeFn_toLp
    rw [h0] at h2
    exact h2.symm.trans (Lp.coeFn_zero ℂ 2 (Formalism.REAL.muG ε))
  haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by
    unfold Formalism.REAL.muG
    infer_instance
  have hall := (Continuous.ae_eq_iff_eq (Formalism.REAL.muG ε) hcont continuous_zero).1 hae
  have h1 := congrFun hall 1
  simp [jfun, hP.2.1] at h1
  have hu1 : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  rw [hu1, hP.2.1] at h1
  simp at h1
  exact hv₀ h1

theorem eq_zero_of_datumEmbedding_eq_zero (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) {v : T.V}
    (h : uniformisationL2 ε Ψ v₀ v = 0) : v = 0 := by
  have hst : ∀ k : S7.KG ε, ∀ u ∈ LinearMap.ker (datumEmbeddingToL2 hP v₀),
      ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) u ∈ LinearMap.ker (datumEmbeddingToL2 hP v₀) := by
    intro k u hu
    have hu' : uniformisationL2 ε Ψ v₀ u = 0 := LinearMap.mem_ker.1 hu
    apply LinearMap.mem_ker.2
    show uniformisationL2 ε Ψ v₀ (T.op k u) = 0
    rw [← rightRegular_datumEmbedding hP v₀ u k, hu', map_zero]
  rcases T.irred _ hst with hb | ht
  · have hm : v ∈ LinearMap.ker (datumEmbeddingToL2 hP v₀) := LinearMap.mem_ker.2 h
    rw [hb] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · have hm : v₀ ∈ LinearMap.ker (datumEmbeddingToL2 hP v₀) := by rw [ht]; trivial
    exact absurd (LinearMap.mem_ker.1 hm) (datumEmbedding_self_ne_zero hP hv₀)

theorem datumV_ne_bot (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) : datumV ε Ψ v₀ ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨⟨uniformisationL2 ε Ψ v₀ v₀, datumEmbedding_mem_smooth hP v₀ v₀⟩, (mem_datumV_iff hP v₀ _).2 ⟨v₀, rfl⟩, ?_⟩
  intro h0
  exact datumEmbedding_self_ne_zero hP hv₀ (congrArg Subtype.val h0)

theorem datumV_weight_le (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) {μ : Fin n → ℝ}
    {x : smD ε (rreg ε)} (hx : x ∈ datumV ε Ψ v₀) (hx0 : x ≠ 0)
    (hμ : ∀ a, smE ε (rreg ε) a a x = ((μ a : ℝ) : ℂ) • x) :
    Formalism.MainNotions.S.CDom ε μ (lowK ε lam) := by
  obtain ⟨v, hv⟩ := (mem_datumV_iff hP v₀ x).1 hx
  have hxe : x = ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩ := Subtype.ext hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hx0
    apply Subtype.ext
    rw [hv]
    exact (datumEmbeddingToL2 hP v₀).map_zero
  have hμ' : ∀ a, T.dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v := by
    intro a
    have e1 := rightDerivative_datum_embedding hP v₀ v (a := a) (b := a) rfl
    have e2 := congrArg Subtype.val (hμ a)
    rw [hxe] at e2
    rw [e1, Submodule.coe_smul] at e2
    have e3 : datumEmbeddingToL2 hP v₀ (T.dτ (Matrix.single a a 1) v - ((μ a : ℝ) : ℂ) • v) = 0 := by
      rw [map_sub, map_smul]
      exact sub_eq_zero.2 e2
    exact sub_eq_zero.1 (eq_zero_of_datumEmbedding_eq_zero hP hv₀ e3)
  obtain ⟨c, hc1, hc2⟩ := HW.KType.weight_le T hv0 hμ'
  exact ⟨c, hc1, hc2⟩

end Datum

end ReciprocityTheory.ChartRestriction.DS
