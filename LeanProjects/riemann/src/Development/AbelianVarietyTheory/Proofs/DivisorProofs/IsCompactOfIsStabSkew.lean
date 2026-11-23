import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfIsStabDefinite
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section
namespace GlobalTheory.DblUnfoldCont

open Matrix

theorem pairVec_dotProduct {n : ℕ} (x y x' y' : Fin n → ℂ) :
    pairVec finSumFinEquiv x y ⬝ᵥ pairVec finSumFinEquiv x' y' = x ⬝ᵥ x' + y ⬝ᵥ y' := by
  simp only [dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [pairVec_inl, pairVec_inr]

theorem star_pairVec {n : ℕ} (x y : Fin n → ℂ) :
    star (pairVec finSumFinEquiv x y) = pairVec finSumFinEquiv (star x) (star y) := by
  funext j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j <;> simp only [Pi.star_apply, pairVec_inl, pairVec_inr]

theorem transpose_blkMat {n : ℕ} (x y : Matrix (Fin n) (Fin n) ℂ) :
    (blkMat finSumFinEquiv x y)ᵀ = blkMat finSumFinEquiv xᵀ yᵀ := by
  simp [blkMat, Matrix.fromBlocks_transpose]

theorem smul_blkMat {n : ℕ} (c : ℂ) (x y : Matrix (Fin n) (Fin n) ℂ) :
    c • blkMat finSumFinEquiv x y = blkMat finSumFinEquiv (c • x) (c • y) := by
  simp only [blkMat]
  rw [show fromBlocks (c • x) 0 0 (c • y) = c • fromBlocks x 0 0 y by rw [Matrix.fromBlocks_smul, smul_zero]]
  rfl

theorem isCartan_dbl {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (h : IsCartan M θ) :
    IsCartan (blkMat finSumFinEquiv M (-M)) (blkMat finSumFinEquiv θ (-θ)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [blkMat_mul, neg_mul_neg, h1, blkMat_one]
  · rw [transpose_blkMat, blkMat_map _ _ (star_zero _), blkMat_mul, blkMat_mul]
    have hs : (-θ).map star = -(θ.map star) := by ext i j; simp
    simp only [Matrix.transpose_neg, hs, neg_mul_neg, Matrix.mul_neg, h2]
  · intro x hx
    rw [← pairVec_eta finSumFinEquiv x] at hx ⊢
    set u : Fin n → ℂ := fun i => x (finSumFinEquiv (.inl i))
    set v : Fin n → ℂ := fun i => x (finSumFinEquiv (.inr i))
    rw [star_pairVec, blkMat_mulVec, blkMat_mulVec, pairVec_dotProduct, Complex.add_re, Matrix.neg_mulVec,
      Matrix.neg_mulVec, neg_dotProduct, dotProduct_neg, neg_neg]
    have key : ∀ z : Fin n → ℂ, 0 ≤ ((θ *ᵥ z) ⬝ᵥ M *ᵥ star z).re := fun z => by
      by_cases hz : z = 0
      · simp [hz]
      · exact (h3 z hz).le
    by_cases hu : u = 0
    · have hv : v ≠ 0 := by
        rintro hv; apply hx; rw [hu, hv]; funext j
        obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j <;> simp only [pairVec_inl, pairVec_inr, Pi.zero_apply]
      exact add_pos_of_nonneg_of_pos (key u) (h3 v hv)
    · exact add_pos_of_pos_of_nonneg (h3 u hu) (key v)

theorem isCompact_of_isStab_skew {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (B : Base F E) {n : ℕ} (X : Spc F E n) (hL : X.L.IsLattice E)
    (hθ : ∀ w, IsCartan (Complex.I • X.J.map (B.emb w).1) (X.θ w)) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) :
    IsCompact (K : Set (UA σ X.J)) := by
  have e : K = GlobalTheory.StabHaar.stabK B X := by
    ext g
    rw [hK g, GlobalTheory.StabHaar.isStab_stabK B X g]
  subst e
  have hJ : X.J.det ≠ 0 := by
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hd : (X.J.map (B.emb w).1).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have hx : star v ≠ 0 := by simpa using hv
    have := (hθ w).2.2 (star v) hx
    rw [star_star, Matrix.smul_mulVec, hMv, smul_zero, dotProduct_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  choose Rw hRw using fun w => GlobalTheory.T.cartan_commuting_isometries_bounded _ _ (hθ w)
  set R : ℝ := ∑ w, |Rw w|
  obtain ⟨Cf, hCf, hCfe⟩ := GlobalTheory.StabCompact.exists_compact_entries F E X.L hL.fg hL.span_eq_top
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.T.bounded_norm_compact_preimage F E σ hcm B.emb Cf hCf R
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.T.unitary_group_bounded_entries_compact F E σ n X.J hJ K hK
  have hsub : ((GlobalTheory.StabHaar.stabK B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) ⊆ C := by
    refine fun g hg => hCe g fun i j => hKe _ ?_ ?_
    · exact hCfe _ (GlobalTheory.T.lattice_completion_stable_base_change F E n X (mat g) fun z hz => (hg.2 z hz).1) i j
    · intro w
      have hu : ((mat g).map (piInf (B.emb w))).transpose * X.J.map (B.emb w).1 * ((mat g).map (piInf (B.emb w))).map star = X.J.map (B.emb w).1 := by
        have h2 := congrArg (fun Y : Matrix (Fin n) (Fin n) (AE F E) => Y.map (piInf (B.emb w)))
          (show (mat g).transpose * incM F X.J * (mat g).map (cA σ) = incM F X.J from g.2)
        simp only [Matrix.map_mul] at h2
        have e1 : (incM F X.J).map (piInf (B.emb w)) = X.J.map (B.emb w).1 := by
          ext i j
          simp [incM, piInf, compInf, inclR, infEmb_tmul]
        have e2 : ((mat g).map (cA σ)).map (piInf (B.emb w)) = ((mat g).map (piInf (B.emb w))).map star := by
          ext i j
          simp only [Matrix.map_apply]
          exact GlobalTheory.StabBounded.cA_piInf hcm _ _
        rw [e1] at h2
        rw [← e2, ← Matrix.transpose_map]
        exact h2
      have hu' : ((mat g).map (piInf (B.emb w))).transpose * (Complex.I • X.J.map (B.emb w).1) *
          ((mat g).map (piInf (B.emb w))).map star = Complex.I • X.J.map (B.emb w).1 := by
        rw [Matrix.mul_smul, Matrix.smul_mul, hu]
      have hb := hRw w _ hu' (hg.1 w).eq i j
      calc ‖piInf (B.emb w) (mat g i j)‖ = ‖(mat g).map (piInf (B.emb w)) i j‖ := rfl
        _ ≤ Rw w := hb
        _ ≤ |Rw w| := le_abs_self _
        _ ≤ R := Finset.single_le_sum (f := fun w => |Rw w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
  exact hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.LatHatClosed.isClosed_latHat F E n X hL)) hsub

theorem continuity : GlobalTheory.Published.SiegelEisensteinDoubled → GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ W₂ : Spc F E ((a + a') + (a + a')), W₂.J = dblGram finSumFinEquiv G.W.J → W₂.L = sumLat finSumFinEquiv G.W.L G.W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (G.W.θ w) (-G.W.θ w)) →
    ∀ i : UA σ G.W.J × UA σ G.W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ φ₀ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K X.α (-(a : ℂ) / 2),
    (∀ s : ℂ, ((a + a' : ℕ) : ℝ) / 2 < s.re →
        GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (-(a : ℂ) / 2) s) ∧
        ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (-(a : ℂ) / 2) s) g) →
    ∀ μ : Measure (UA σ G.W.J), μ.IsHaarMeasure →
    Continuous i ∧ (∀ s : ℂ, Continuous (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (-(a : ℂ) / 2) s)) ∧ Continuous (fun g : UA σ G.W.J => (((X.α (Matrix.GeneralLinearGroup.det g.1))⁻¹ : Circle) : ℂ)) := by
  intro hSE hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hconv μ hμ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := eh.isEmbedding.t2Space
  haveI := (GlobalTheory.UnipCT.topFacts σ W₂.J).1
  have hW := hM.triple.geo.hW
  have hcm := hM.triple.base.cm
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (Subtype.val ∘ i : UA σ G.W.J × UA σ G.W.J → GL (Fin _) (AE F E)) =
        fun x => blkGL finSumFinEquiv ((x.1 : GL (Fin _) (AE F E)), (x.2 : GL (Fin _) (AE F E))) :=
      funext fun x => Units.ext (hi x.1 x.2)
    refine continuous_induced_rng.2 ?_
    rw [h1]
    exact (continuous_blkGL _).comp (continuous_subtype_val.prodMap continuous_subtype_val)
  · have hL₂ : W₂.L.IsLattice E := by rw [hL]; haveI : Submodule.IsLattice E G.W.L := hW.lat; infer_instance
    have hθ₂ : ∀ w, IsCartan (Complex.I • W₂.J.map (B.emb w).1) (W₂.θ w) := by
      intro w
      rw [hθ w, hJ, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), smul_blkMat, smul_neg]
      exact isCartan_dbl _ _ (hW.cartan w)
    have hKc := isCompact_of_isStab_skew hcm B W₂ hL₂ hθ₂ hK
    intro s
    have hh := hIw.continuous_hgtOf continuous_subtype_val continuous_absE hKc
    have e1 : flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (-(a : ℂ) / 2) s =
        fun g => φ₀ g * npow (hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K g) (s - (-(a : ℂ) / 2)) :=
      funext fun g => flatOf_apply _ _ _ g
    rw [e1]
    exact (mem_degPSOf.1 hφ₀).2.1.mul (continuous_npow hh (fun g => hgtOf_pos g) _)
  · have hα : Continuous X.α := hM.triple.chars.heckeα.1
    exact continuous_subtype_val.comp ((hα.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)).inv)

theorem continuity_pair : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → 1 ≤ d →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ φ₀ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χX (((n : ℂ) - (d : ℂ)) / 2),
    (∀ s : ℂ, (d : ℝ) / 2 < s.re →
        GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) ∧
        ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) g) →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    Continuous i ∧ (∀ s : ℂ, Continuous (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s)) ∧ Continuous (fun g : UA σ W.J => (((χX (Matrix.GeneralLinearGroup.det g.1))⁻¹ : Circle) : ℂ)) := by
  intro hKP F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hconv μ hμ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := eh.isEmbedding.t2Space
  haveI := (GlobalTheory.UnipCT.topFacts σ W₂.J).1
  have hW := hP.skew
  have hcm := hP.base.cm
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (Subtype.val ∘ i : UA σ W.J × UA σ W.J → GL (Fin _) (AE F E)) =
        fun x => blkGL finSumFinEquiv ((x.1 : GL (Fin _) (AE F E)), (x.2 : GL (Fin _) (AE F E))) :=
      funext fun x => Units.ext (hi x.1 x.2)
    refine continuous_induced_rng.2 ?_
    rw [h1]
    exact (continuous_blkGL _).comp (continuous_subtype_val.prodMap continuous_subtype_val)
  · have hL₂ : W₂.L.IsLattice E := by rw [hL]; haveI : Submodule.IsLattice E W.L := hW.lat; infer_instance
    have hθ₂ : ∀ w, IsCartan (Complex.I • W₂.J.map (B.emb w).1) (W₂.θ w) := by
      intro w
      rw [hθ w, hJ, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), smul_blkMat, smul_neg]
      exact isCartan_dbl _ _ (hW.cartan w)
    have hKc := isCompact_of_isStab_skew hcm B W₂ hL₂ hθ₂ hK
    intro s
    have hh := hIw.continuous_hgtOf continuous_subtype_val continuous_absE hKc
    have e1 : flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s =
        fun g => φ₀ g * npow (hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K g) (s - (((n : ℂ) - (d : ℂ)) / 2)) :=
      funext fun g => flatOf_apply _ _ _ g
    rw [e1]
    exact (mem_degPSOf.1 hφ₀).2.1.mul (continuous_npow hh (fun g => hgtOf_pos g) _)
  · have hα : Continuous χX := hP.hX.1
    exact continuous_subtype_val.comp ((hα.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)).inv)

end GlobalTheory.DblUnfoldCont
