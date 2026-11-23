import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerRealizeEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGramComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalMulVecApply
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompAdds

theorem totallyComplex {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} (c : Coeff l) :
    IsTotallyComplex c.F := by
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro h
  exact GlobalTheory.CompHt.conj_comp_ne v.embedding (RingHom.ext fun a => by
    simpa [ComplexEmbedding.conjugate_coe_eq] using
      congrArg (fun f : c.F →+* ℂ => f a) (ComplexEmbedding.isReal_iff.1 h))

theorem pos_of_hasGram {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    {N : (K →+* ℂ) → W → ℝ} (h : HasGram N) (hn : ∀ σ x, 0 ≤ N σ x)
    (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) {x : W} (hx : x ≠ 0) (σ : K →+* ℂ) : 0 < N σ x := by
  have e : N σ x = N (InfinitePlace.mk σ).embedding x := by
    rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · rw [h1]
    · have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun a => ComplexEmbedding.conjugate_coe_eq σ a
      rw [h1, this, hc]
  rw [e]
  exact lt_of_le_of_ne (hn _ _) fun h0 => hx (GlobalTheory.HSApp.HasGram_eq_zero h _ h0.symm)

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

section Basic

variable (Z : Comp Xo c) (G : WTZ D.host.E)

theorem normRes_nonneg (σ : c.F →+* ℂ) (f : cuspOn U Z G) : 0 ≤ normRes U V dict Z G σ f :=
  petAt_nonneg _ _ _ _ _ _ _

theorem normOn_nonneg (σ : c.F →+* ℂ) (f : cuspOn U Z G) : 0 ≤ normOn U (xiR D) V dict Z G σ f :=
  petAt_nonneg _ _ _ _ _ _ _

theorem normRes_conj (σ : c.F →+* ℂ) (f : cuspOn U Z G) :
    normRes U V dict Z G ((starRingEnd ℂ).comp σ) f = normRes U V dict Z G σ f :=
  congrArg (fun s => petAt (U s) (xiR D) (V s) (dict s) (muQ1 (V s)) G (f : Rul Xo c)) (GlobalTheory.CompHt.goodOf_conj σ)

theorem mass_conj (σ : c.F →+* ℂ) : mass U V dict Z ((starRingEnd ℂ).comp σ) = mass U V dict Z σ :=
  congrArg (fun s => (muQ1 (V s) (classesOver (V s) (dict s) (framesOn (U s) Z))).toReal) (GlobalTheory.CompHt.goodOf_conj σ)

theorem mass_nonneg (σ : c.F →+* ℂ) : 0 ≤ mass U V dict Z σ := ENNReal.toReal_nonneg

theorem normRes_zero (σ : c.F →+* ℂ) : normRes U V dict Z G σ 0 = 0 := by
  have a := petW_smul U (xiR D) V dict G σ 0 0
  simp only [zero_smul, map_zero, norm_zero, zero_mul] at a
  exact a

theorem normOn_zero (σ : c.F →+* ℂ) : normOn U (xiR D) V dict Z G σ 0 = 0 := by
  have a := petOn_smul U (xiR D) V dict Z G σ 0 0
  simp only [zero_smul, map_zero, norm_zero, zero_mul] at a
  exact a

theorem exists_normOn_eq (σ : c.F →+* ℂ) : ∃ k : ℝ, 0 ≤ k ∧
    ∀ f : cuspOn U Z G, normOn U (xiR D) V dict Z G σ f = k * normRes U V dict Z G σ f :=
  ⟨_, ENNReal.toReal_nonneg, fun f => GlobalTheory.HSApp.petAt_muOn (U (goodOf c σ)) (xiR D) (V (goodOf c σ))
    (dict (goodOf c σ)) Z G (Submodule.mem_inf.1 f.2).2⟩

theorem hasGram_normRes (h : HasGram (normOn U (xiR D) V dict Z G)) : HasGram (normRes U V dict Z G) := by
  by_cases h0 : ∃ f : cuspOn U Z G, f ≠ 0
  · obtain ⟨f, hf⟩ := h0
    choose k hk0 hk using fun σ => exists_normOn_eq U V dict Z G σ
    have hkpos : ∀ v : InfinitePlace c.F, 0 < k v.embedding := fun v => by
      refine lt_of_le_of_ne (hk0 _) fun h2 => hf (GlobalTheory.HSApp.HasGram_eq_zero h v ?_)
      rw [hk, ← h2, zero_mul]
    refine GlobalTheory.HSApp.hasGram_of_injective h LinearMap.id (fun _ _ h => h) (fun v => (k v.embedding)⁻¹)
      (fun v => inv_pos.2 (hkpos v)) fun v x => ?_
    rw [LinearMap.id_apply, hk, ← mul_assoc, inv_mul_cancel₀ (hkpos v).ne', one_mul]
  · push_neg at h0
    refine GlobalTheory.HSApp.hasGram_of_injective h LinearMap.id (fun _ _ h => h) (fun _ => 1) (fun _ => one_pos)
      fun v x => ?_
    rw [h0 x, LinearMap.id_apply, one_mul, normRes_zero, normOn_zero]

def sub : Submodule c.F (cuspW Xo c U G) := (cuspOn U Z G).comap (cuspW Xo c U G).subtype

def toOn : sub U Z G →ₗ[c.F] cuspOn U Z G :=
  LinearMap.codRestrict (cuspOn U Z G) ((cuspW Xo c U G).subtype ∘ₗ (sub U Z G).subtype) fun x => x.2

theorem toOn_injective : Function.Injective (toOn U Z G) := fun a b h =>
  Subtype.ext (Subtype.ext (congrArg (fun y : cuspOn U Z G => (y : Rul Xo c)) h))

theorem hasGram_sub (h : HasGram (normRes U V dict Z G)) :
    HasGram (fun σ (x : sub U Z G) => normW U (xiR D) V dict G σ x) :=
  GlobalTheory.HSApp.hasGram_of_injective h (toOn U Z G) (toOn_injective U Z G) (fun _ => 1) (fun _ => one_pos)
    fun _ _ => (one_mul _).symm

theorem span_partLat_le : Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G)) ≤ sub U Z G :=
  Submodule.span_le.2 (by rintro _ ⟨g, _, rfl⟩; exact g.2)

end Basic

variable {U V dict} {G : WTZ D.host.E}

theorem sub_indep (hS : Splits U G) : iSupIndep (fun Z => sub U Z G) := by
  intro Z
  refine Disjoint.mono_right (iSup₂_le fun j hj =>
    Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ Z) => cuspOn U j G) j hj)) ?_
  rw [disjoint_iff]
  show Submodule.comap (cuspW Xo c U G).subtype (cuspOn U Z G) ⊓
    Submodule.comap (cuspW Xo c U G).subtype (⨆ j, ⨆ (_ : j ≠ Z), cuspOn U j G) = ⊥
  rw [← Submodule.comap_inf, disjoint_iff.1 (hS.2.1.1 Z), Submodule.comap_bot, Submodule.ker_subtype]

theorem sub_iSup (hS : Splits U G) : ⨆ Z, sub U Z G = ⊤ := by
  apply Submodule.map_injective_of_injective (cuspW Xo c U G).injective_subtype
  rw [Submodule.map_iSup, Submodule.map_subtype_top]
  simp only [sub, Submodule.map_comap_subtype]
  rw [iSup_congr fun Z => inf_eq_right.2 (cuspOn_le U Z G)]
  exact hS.2.1.2

theorem pyth [Fintype (Comp Xo c)] (hO : Orthogonal U V dict G) (σ : c.F →+* ℂ) (f : ∀ Z, sub U Z G) :
    normW U (xiR D) V dict G σ (∑ Z, (f Z : cuspW Xo c U G)) ^ 2 =
      ∑ Z, normW U (xiR D) V dict G σ (f Z) ^ 2 := by
  have h := (hO σ).1 (fun Z => toOn U Z G (f Z))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h
  unfold normW
  rw [Submodule.coe_sum]
  exact h

theorem goodW_of (hS : Splits U G) (hO : Orthogonal U V dict G) (h : ∀ Z, GoodOn U (xiR D) V dict Z G) :
    GoodW U (xiR D) V dict G := by
  classical
  haveI : Finite (Comp Xo c) := CompFin.finite_comp Xo c
  letI := Fintype.ofFinite (Comp Xo c)
  refine ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.OrthSumGram.orth_sum_hasGram c.F (cuspW Xo c U G) (Comp Xo c) (normW U (xiR D) V dict G)
      (fun Z => sub U Z G) (fun σ x => petAt_nonneg _ _ _ _ _ _ _) (sub_indep hS) (sub_iSup hS)
      (fun Z => hasGram_sub U V dict Z G (hasGram_normRes U V dict Z G (h Z).1)) (pyth hO)
  · rw [← hS.2.2.2]
    exact Submodule.fg_iSup _ fun Z => (h Z).2.1.map _
  · rw [eq_top_iff, ← sub_iSup hS]
    refine iSup_le fun Z y hy => ?_
    have h1 : toOn U Z G ⟨y, hy⟩ ∈ Submodule.span c.F (latOn U Z G : Set (cuspOn U Z G)) :=
      by rw [(h Z).2.2]; exact Submodule.mem_top
    have h3 : Submodule.span c.F (latOn U Z G : Set (cuspOn U Z G)) ≤
        (Submodule.span c.F (latW U G : Set (cuspW Xo c U G))).comap (Submodule.inclusion (cuspOn_le U Z G)) :=
      Submodule.span_le.2 fun g hg => Submodule.subset_span ((mem_latOn U).1 hg)
    exact h3 h1

theorem normOn_eq_of_mass (hO : Orthogonal U V dict G) (Z : Comp Xo c) (σ : c.F →+* ℂ)
    (hm : 0 < mass U V dict Z σ) (f : cuspOn U Z G) :
    normOn U (xiR D) V dict Z G σ f = (Real.sqrt (mass U V dict Z σ))⁻¹ * normRes U V dict Z G σ f := by
  have h1 := (hO σ).2 Z f
  have hs := Real.sqrt_pos.2 hm
  have h2 : normRes U V dict Z G σ f = Real.sqrt (mass U V dict Z σ) * normOn U (xiR D) V dict Z G σ f := by
    rw [← sq_eq_sq₀ (normRes_nonneg U V dict Z G σ f) (mul_nonneg hs.le (normOn_nonneg U V dict Z G σ f)),
      mul_pow, Real.sq_sqrt hm.le]
    exact h1
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

theorem mass_pos (hO : Orthogonal U V dict G) (Z : Comp Xo c) (hR : HasGram (normRes U V dict Z G))
    (hr : rankOn U Z G ≠ 0) (σ : c.F →+* ℂ) : 0 < mass U V dict Z σ := by
  have hne : latOn U Z G ≠ ⊥ := fun h0 => hr (by
    rw [show rankOn U Z G = Module.finrank c.F (Submodule.span c.F ((latOn U Z G : Submodule _ _) : Set (cuspOn U Z G)))
      from rfl, h0, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot])
  obtain ⟨f, -, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hp := pos_of_hasGram hR (normRes_nonneg U V dict Z G) (normRes_conj U V dict Z G) hf σ
  have h1 := (hO σ).2 Z f
  refine lt_of_le_of_ne (mass_nonneg U V dict Z σ) fun h0 => ?_
  rw [← h0, zero_mul] at h1
  exact hp.ne' ((pow_eq_zero_iff two_ne_zero).1 h1)

theorem degRes_zero (Z : Comp Xo c) (hr : rankOn U Z G = 0) : degRes U V dict Z G = 0 := by
  unfold degRes GlobalTheory.AllWt.deg
  unfold rankOn at hr
  rw [hr, Nat.cast_zero, zero_mul]

theorem degOn_zero (Z : Comp Xo c) (hr : rankOn U Z G = 0) : degOn U (xiR D) V dict Z G = 0 := by
  unfold degOn GlobalTheory.AllWt.deg
  unfold rankOn at hr
  rw [hr, Nat.cast_zero, zero_mul]

theorem degRes_eq [IsTotallyComplex c.F] (hO : Orthogonal U V dict G) (Z : Comp Xo c)
    (hR : HasGram (normRes U V dict Z G)) (hfg : (latOn U Z G).FG) :
    degRes U V dict Z G = degOn U (xiR D) V dict Z G - (rankOn U Z G : ℝ) / 2 *
      ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (Module.finrank ℚ c.F : ℝ)) := by
  by_cases hr : rankOn U Z G = 0
  · rw [degRes_zero Z hr, degOn_zero Z hr, hr]; simp
  · have hm := mass_pos hO Z hR hr
    have hsc := (GlobalTheory.NormScale.deg_scale c.F (cuspOn U Z G) (normRes U V dict Z G)
      (normOn U (xiR D) V dict Z G) (fun σ => (Real.sqrt (mass U V dict Z σ))⁻¹) hR
      (fun σ => inv_pos.2 (Real.sqrt_pos.2 (hm σ)))
      (fun σ => congrArg (fun m => (Real.sqrt m)⁻¹) (mass_conj U V dict Z σ))
      (fun σ f => normOn_eq_of_mass hO Z σ (hm σ) f)).2 (latOn U Z G) hfg
    have hl : ∀ σ, Real.log (Real.sqrt (mass U V dict Z σ))⁻¹ = -(Real.log (mass U V dict Z σ) / 2) :=
      fun σ => by rw [Real.log_inv, Real.log_sqrt (mass_nonneg U V dict Z σ)]
    simp only [hl, Finset.sum_neg_distrib, ← Finset.sum_div] at hsc
    unfold degRes degOn rankOn
    rw [hsc]
    ring

theorem sums [IsTotallyComplex c.F] (hS : Splits U G) (hO : Orthogonal U V dict G) (hW : GoodW U (xiR D) V dict G)
    (hOn : ∀ Z, GoodOn U (xiR D) V dict Z G) :
    rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧ degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, degRes U V dict Z G := by
  haveI : Finite (Comp Xo c) := CompFin.finite_comp Xo c
  letI := Fintype.ofFinite (Comp Xo c)
  have hrd := fun Z => (GlobalTheory.RestrictNorm.restrict_deg c.F (cuspW Xo c U G) (cuspOn U Z G)
    (normW U (xiR D) V dict G) (Submodule.inclusion (cuspOn_le U Z G)) (Submodule.inclusion_injective _)
    hW.1).2 (latOn U Z G) (hOn Z).2.1
  obtain ⟨hs1, hs2⟩ := GlobalTheory.OrthRankDeg.rkK_deg_iSup c.F (cuspW Xo c U G) (Comp Xo c) (normW U (xiR D) V dict G)
    (fun Z => partLat U Z G) hW.1 (fun Z => (hOn Z).2.1.map _)
    (fun σ f hf => pyth hO σ (fun Z => ⟨f Z, span_partLat_le U Z G (hf Z)⟩))
  refine ⟨?_, ?_⟩
  · rw [finsum_eq_sum_of_fintype]
    unfold GlobalTheory.AllWt.rankW
    rw [← hS.2.2.2]
    exact hs1.trans (Finset.sum_congr rfl fun Z _ => (hrd Z).1)
  · rw [finsum_eq_sum_of_fintype]
    unfold GlobalTheory.AllWt.degW
    rw [← hS.2.2.2]
    exact hs2.trans (Finset.sum_congr rfl fun Z _ => (hrd Z).2)

theorem adds : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E),
    Splits U G → Orthogonal U V dict G → Adds U V dict G := by
  intro D H Dw l Xo c r U V dict G hS hO
  haveI : Finite (Comp Xo c) := CompFin.finite_comp Xo c
  letI := Fintype.ofFinite (Comp Xo c)
  haveI : IsTotallyComplex c.F := totallyComplex c
  refine ⟨⟨fun h Z => GlobalTheory.HSApp.goodOn_of_goodW U (xiR D) V dict Z G h, goodW_of hS hO⟩, fun hW => ?_⟩
  have hOn : ∀ Z, GoodOn U (xiR D) V dict Z G := fun Z => GlobalTheory.HSApp.goodOn_of_goodW U (xiR D) V dict Z G hW
  have hRes : ∀ Z, HasGram (normRes U V dict Z G) := fun Z => hasGram_normRes U V dict Z G (hOn Z).1
  obtain ⟨hs1, hs2⟩ := sums hS hO hW hOn
  refine ⟨hRes, hs1, hs2, fun Z => mass_pos hO Z (hRes Z), ?_⟩
  rw [hs2]
  exact finsum_congr fun Z => degRes_eq hO Z (hRes Z) (hOn Z).2.1

end GlobalTheory.CompAdds
