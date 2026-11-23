import Formalism.HermitianCurvature.StatementC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroEstimateProduct
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice

namespace Formalism.FourierDecayAlt.P

open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory

open scoped ComplexOrder ComplexConjugate RealInnerProductSpace

noncomputable section

namespace Cx2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem idl_ne_zero (g : ℕ) (hg : 0 < g) (k ν : ℤ) : S6.idl E g k ν ≠ 0 := by
  unfold S6.idl
  refine mul_ne_zero (zpow_ne_zero _ ?_) ?_
  · unfold S6.dd
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  · rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr hg.ne')

theorem idl_two_le_one (g : ℕ) (ν : ℤ) : S6.idl E g 2 ν ≤ S6.idl E g 1 ν := by
  unfold S6.idl
  have hg1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (g : E) ≤ 1 := by
    rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff]
    exact ⟨(g : 𝓞 E), by simp⟩
  have h2 : ((g : E) ^ (2 : ℤ)) = (g : E) * (g : E) ^ (1 : ℤ) := by
    rw [zpow_one, zpow_two]
  have key : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ (2 : ℤ)) ≤
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ (1 : ℤ)) := by
    rw [h2, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    calc _ ≤ 1 * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ (1 : ℤ)) := by
          first
            | exact FractionalIdeal.mul_right_mono _ hg1
            | exact FractionalIdeal.mul_le_mul_right hg1 _
            | gcongr
      _ = _ := one_mul _
  first
    | exact FractionalIdeal.mul_left_mono _ key
    | exact FractionalIdeal.mul_le_mul_left key _
    | gcongr

theorem frame_facts (g : ℕ) (hg : 0 < g) (ν : ℤ) :
    DiscreteTopology (S6.frameLat E (S6.perLat E g ν 1) 1) ∧
    Submodule.span ℝ (S6.frameLat E (S6.perLat E g ν 1) 1 : Set (mixedEmbedding.mixedSpace E)) = ⊤ := by
  have hA : S6.idl E g 1 ν ≠ 0 := idl_ne_zero g hg 1 ν
  have hB : S6.idl E g 2 ν ≠ 0 := idl_ne_zero g hg 2 ν
  obtain ⟨hBL, hLA⟩ := twistedLatticeBetween E (S6.idl E g 1 ν) (S6.idl E g 2 ν) 1 (idl_two_le_one g ν)
    (different_power_conj_stable E g 2 ν)
  have hmem : ∀ x, x ∈ S6.frameLat E (S6.perLat E g ν 1) 1 ↔
      ∃ t ∈ S6.perLat E g ν 1, mixedEmbedding E t = x := by
    intro x
    simp [S6.frameLat]
  constructor
  · have hsub : (S6.frameLat E (S6.perLat E g ν 1) 1 : Set (mixedEmbedding.mixedSpace E)) ⊆
        (mixedEmbedding.idealLattice E (Units.mk0 _ hA) : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (hmem x).1 hx
      exact (mixedEmbedding.mem_idealLattice E _).2 ⟨t, hLA ht, rfl⟩
    exact DiscreteTopology.of_subset
      (inferInstanceAs (DiscreteTopology (mixedEmbedding.idealLattice E (Units.mk0 _ hA)))) hsub
  · have hsub : (mixedEmbedding.idealLattice E (Units.mk0 _ hB) : Set (mixedEmbedding.mixedSpace E)) ⊆
        (S6.frameLat E (S6.perLat E g ν 1) 1 : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (mixedEmbedding.mem_idealLattice E _).1 hx
      exact (hmem _).2 ⟨t, hBL ht, rfl⟩
    classical
    have hr : Set.range (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)) ⊆
        (S6.frameLat E (S6.perLat E g ν 1) 1 : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      have hx' : x ∈ mixedEmbedding.idealLattice E (Units.mk0 _ hB) := by
        rw [← mixedEmbedding.span_idealLatticeBasis]
        exact Submodule.subset_span hx
      exact hsub hx'
    rw [eq_top_iff, ← (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)).span_eq]
    exact Submodule.span_mono hr

theorem eLat_facts (hEF : J.EuclidFrame) (g : ℕ) (hg : 0 < g) (ν : ℤ) :
    ∃ _ : DiscreteTopology (J.eLat E (S6.perLat E g ν 1) 1), IsZLattice ℝ (J.eLat E (S6.perLat E g ν 1) 1) := by
  obtain ⟨hd, hs⟩ := frame_facts (E := E) g hg ν
  obtain ⟨hd', hs', -⟩ := hEF E (S6.perLat E g ν 1) 1 hd hs
  exact ⟨hd', { span_top := hs' }⟩

theorem inner_dm (g : ℕ) (l : E) (c : J.CV E) :
    inner ℝ c (J.dm E g 1 (-l)) = -((∑ w : InfinitePlace E, 2 * (w.embedding l * c w).re) / g) := by
  rw [PiLp.inner_apply, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hd : (J.dm E g 1 (-l)) w = ((2 / ((g : ℝ) * 1) : ℝ) : ℂ) * conj (w.embedding (-l)) := rfl
  rw [hd, Complex.inner]
  simp only [map_neg, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_one]
  ring

variable {Wp Wq : InfinitePlace E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem σ_or (S : HidaSetting E Wp Wq) (v : Fin S.f) :
    S.σ v = (S.pl v).embedding ∨ ComplexEmbedding.conjugate (S.σ v) = (S.pl v).embedding := by
  have h := NumberField.InfinitePlace.embedding_mk_eq (S.emb v)
  rw [S.hemb v] at h
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem norm_σ (S : HidaSetting E Wp Wq) (v : Fin S.f) (t : E) : ‖S.σ v t‖ = S.pl v t := by
  rw [← S.hemb v]
  exact (NumberField.InfinitePlace.apply (S.emb v) t).symm

open Classical in

def cj (S : HidaSetting E Wp Wq) : J.CV E ≃ₗᵢ[ℝ] J.CV E :=
  LinearIsometryEquiv.piLpCongrRight 2 fun w =>
    if S.σ (S.pl.symm w) = w.embedding then LinearIsometryEquiv.refl ℝ ℂ else Complex.conjLIE

theorem cj_apply (S : HidaSetting E Wp Wq) (c : J.CV E) (v : Fin S.f) :
    (S.σ v = (S.pl v).embedding → cj S c (S.pl v) = c (S.pl v)) ∧
      (S.σ v ≠ (S.pl v).embedding → cj S c (S.pl v) = conj (c (S.pl v))) := by
  constructor
  · intro h
    simp [cj, h]
  · intro h
    simp [cj, h]

theorem cj_cemb (S : HidaSetting E Wp Wq) (t : E) (v : Fin S.f) : cj S (J.cemb E t) (S.pl v) = S.σ v t := by
  have hc : J.cemb E t (S.pl v) = (S.pl v).embedding t := rfl
  by_cases h : S.σ v = (S.pl v).embedding
  · rw [(cj_apply S _ v).1 h, hc, h]
  · rw [(cj_apply S _ v).2 h, hc]
    rcases σ_or S v with h' | h'
    · exact absurd h' h
    · rw [← h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem norm_cj (S : HidaSetting E Wp Wq) (c : J.CV E) (v : Fin S.f) : ‖cj S c (S.pl v)‖ = ‖c (S.pl v)‖ := by
  by_cases h : S.σ v = (S.pl v).embedding
  · rw [(cj_apply S c v).1 h]
  · rw [(cj_apply S c v).2 h, Complex.norm_conj]

theorem re_cj (S : HidaSetting E Wp Wq) (c : J.CV E) (l : E) (v : Fin S.f) :
    (S.σ v l * cj S c (S.pl v)).re = ((S.pl v).embedding l * c (S.pl v)).re := by
  by_cases h : S.σ v = (S.pl v).embedding
  · rw [(cj_apply S c v).1 h, h]
  · rw [(cj_apply S c v).2 h]
    rcases σ_or S v with h' | h'
    · exact absurd h' h
    · rw [← h', ComplexEmbedding.conjugate_coe_eq]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring

theorem cj_mp (S : HidaSetting E Wp Wq) : MeasurePreserving (cj S) := (cj S).measurePreserving

theorem mem_comap_cj (S : HidaSetting E Wp Wq) (L : Submodule ℤ E) (x : J.CV E) :
    x ∈ ZLattice.comap ℝ (J.eLat E L 1) (cj S).toLinearEquiv.toLinearMap ↔
      ∃ t ∈ L, ∀ v, x (S.pl v) = S.σ v t := by
  have hinv : ∀ c : J.CV E, cj S (cj S c) = c := by
    intro c
    ext w
    obtain ⟨v, rfl⟩ := S.pl.surjective w
    by_cases h : S.σ v = (S.pl v).embedding
    · rw [(cj_apply S _ v).1 h, (cj_apply S _ v).1 h]
    · rw [(cj_apply S _ v).2 h, (cj_apply S _ v).2 h, Complex.conj_conj]
  have hs : ∀ t : E, (J.semb E 1).toIntLinearMap t = J.cemb E t := fun t => by
    simp [J.semb]
  change cj S x ∈ J.eLat E L 1 ↔ _
  simp only [J.eLat, Submodule.mem_map, hs]
  constructor
  · rintro ⟨t, ht, he⟩
    refine ⟨t, ht, fun v => ?_⟩
    rw [← hinv x, ← he, cj_cemb]
  · rintro ⟨t, ht, he⟩
    refine ⟨t, ht, ?_⟩
    rw [← hinv (J.cemb E t)]
    congr 1
    ext w
    obtain ⟨v, rfl⟩ := S.pl.surjective w
    rw [cj_cemb, he]

theorem covolume_comap_cj (S : HidaSetting E Wp Wq) (L : Submodule ℤ E) [DiscreteTopology (J.eLat E L 1)]
    [IsZLattice ℝ (J.eLat E L 1)] :
    ZLattice.covolume (ZLattice.comap ℝ (J.eLat E L 1) (cj S).toLinearEquiv.toLinearMap) =
      ZLattice.covolume (J.eLat E L 1) :=
  ZLattice.covolume_comap (J.eLat E L 1) volume volume (e := (cj S).toContinuousLinearEquiv) (cj_mp S)

theorem first_norm_real_nonneg (S : HidaSetting E Wp Wq) (hP : ThmPPos S) (ε : ℝ) (hε : 0 < ε) (i : ℕ)
    (hi : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (hκ : TB.PSDOn Y κ) (c : J.CV E) :
    ∃ x : ℝ, 0 ≤ x ∧ S.N1 ε i w.1 Y κ c = x := by
  classical
  let k : Option (Fin S.f) → TB.Pt E → TB.Pt E → ℂ := fun o => match o with
    | none => κ
    | some v => fun h h' => S.gramLoc v ε i (w.1 v) (loc (S.σ v) h ++ [(1, c (S.pl v))])
        (loc (S.σ v) h' ++ [(1, c (S.pl v))])
  have hk : ∀ o, TB.PSDOn Y (k o) := by
    intro o
    cases o with
    | none => exact hκ
    | some v =>
      exact Cx1.psd_pullback Y (fun h => loc (S.σ v) h ++ [(1, c (S.pl v))]) _ _
        (fun x hx => Finset.mem_image_of_mem _ hx) (hP v ε hε i hi w _)
  have hM := schur_product (TB.Pt E) (Option (Fin S.f)) Y k hk
  have hsum : 0 ≤ ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
      (loc (S.σ v) h ++ [(1, c (S.pl v))]) (loc (S.σ v) h' ++ [(1, c (S.pl v))]) := by
    have h3 : ∀ F : TB.Pt E → TB.Pt E → ℂ,
        ∑ a ∈ Y.attach, ∑ b ∈ Y.attach, F a b = ∑ a ∈ Y, ∑ b ∈ Y, F a b := by
      intro F
      rw [← Finset.sum_attach Y (fun a => ∑ b ∈ Y, F a b)]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_attach Y (F a)
    have := hM.dotProduct_mulVec_nonneg (fun _ => 1)
    simp [dotProduct, Matrix.mulVec, Fintype.prod_option, k] at this
    exact this.trans_eq (h3 (fun h h' => κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
      (loc (S.σ v) h ++ [(1, c (S.pl v))]) (loc (S.σ v) h' ++ [(1, c (S.pl v))])))
  have hsize : 0 ≤ Word.size S.P w.1 :=
    Finset.prod_nonneg fun v _ => List.prod_nonneg (fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨a, _, rfl⟩ := hx
      exact abs_nonneg _)
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hsum
  refine ⟨(∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
      (loc (S.σ v) h ++ [(1, c (S.pl v))]) (loc (S.σ v) h' ++ [(1, c (S.pl v))])).re /
      Word.size S.P w.1, div_nonneg hre hsize, ?_⟩
  show (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
      (loc (S.σ v) h ++ [(1, c (S.pl v))]) (loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
      (Word.size S.P w.1 : ℂ) = _
  rw [Complex.ofReal_div]
  congr 1
  exact Complex.ext (by simp) (by simp [← him])

theorem ae_allNe (S : HidaSetting E Wp Wq) : ∀ᵐ c : J.CV E, ∀ v, c (S.pl v) ≠ 0 := by
  classical
  rw [ae_all_iff]
  intro v
  let p : J.CV E →ₗ[ℝ] ℂ :=
    ((EuclideanSpace.proj (S.pl v) : J.CV E →L[ℂ] ℂ) : J.CV E →ₗ[ℂ] ℂ).restrictScalars ℝ
  have hne : LinearMap.ker p ≠ ⊤ := by
    intro htop
    have hm : EuclideanSpace.single (S.pl v) (1 : ℂ) ∈ LinearMap.ker p := htop ▸ Submodule.mem_top
    simp [p] at hm
  have h0 := MeasureTheory.Measure.addHaar_submodule volume (LinearMap.ker p) hne
  rw [ae_iff]
  refine measure_mono_null (fun c hc => ?_) h0
  simp only [Set.mem_setOf_eq, not_not] at hc
  simp [p, hc]

theorem dense_allNe (S : HidaSetting E Wp Wq) : Dense {c : J.CV E | ∀ v, c (S.pl v) ≠ 0} := MeasureTheory.Measure.dense_of_ae (ae_allNe S)

end Cx2

theorem poisson_input_of_parts : C.PoissonInputOfParts := by
  intro hEmb hEF hTD _ E _ _ _ Wp Wq _ _ _ _ S hg1 hg2 hP _ hI Kr hK0 Th e
  have hg : 0 < S.g := Nat.mul_pos hg1 hg2
  have hD : ∀ i : ℕ, DiscreteTopology (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) :=
    fun i => (Cx2.eLat_facts (E := E) hEF S.g hg _).fst
  have hZ : ∀ i : ℕ, IsZLattice ℝ (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) := by
    intro i
    obtain ⟨_, h⟩ := Cx2.eLat_facts (E := E) hEF S.g hg (S6.nuBlock S.G.r i 1)
    exact h
  obtain ⟨hinj, hbij, _, hsemb, _⟩ := hEmb E
  refine ⟨J.CV E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    InfinitePlace E, inferInstance, J.coord E,
    fun i => J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1, hD, hZ,
    fun _ => J.cemb E, fun _ l => J.dm E S.g 1 (-l), hbij, ?_, ?_⟩
  · intro i _ _
    refine ⟨hinj, ?_, ?_, ?_⟩
    · intro t ht
      have h1 : J.cemb E t = J.semb E 1 t := by rw [hsemb, one_smul]
      rw [h1]
      exact Submodule.mem_map_of_mem (f := (J.semb E 1).toIntLinearMap) ht
    · ext w; simp [J.dm]
    · intro μ hμ
      have hfl := twistedIsRealOrderLattice E (S6.idl E S.g 1 (S6.nuBlock S.G.r i 1))
        (S6.idl E S.g 2 (S6.nuBlock S.G.r i 1)) 1 (Cx2.idl_ne_zero S.g hg 2 _)
        (Cx2.idl_two_le_one S.g _) (different_power_conj_stable E S.g 2 _)
      obtain ⟨l, hl, hlμ⟩ :=
        (hTD E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) S.g 1 hg one_ne_zero hfl.2 μ).1 hμ
      refine ⟨-l, ?_, ?_⟩
      · exact neg_mem hl
      · simpa using hlμ
  · intro ε hε i hi1 hi2 w Y hY κ hκ
    have hi2' : i ≤ S.G.r + 1 := hi2
    obtain ⟨⟨φ, hcont, hext, Cφ, hdec⟩, _⟩ := hI ε hε i hi1 hi2 w Y hY κ hκ
    have hreal : ∀ c, ((φ c).re : ℂ) = φ c ∧ 0 ≤ (φ c).re := by
      have hcl : IsClosed {c : J.CV E | 0 ≤ (φ c).re ∧ (φ c).im = 0} :=
        (isClosed_le continuous_const (Complex.continuous_re.comp hcont)).inter
          (isClosed_eq (Complex.continuous_im.comp hcont) continuous_const)
      have hsub : {c : J.CV E | ∀ v, c (S.pl v) ≠ 0} ⊆
          {c : J.CV E | 0 ≤ (φ c).re ∧ (φ c).im = 0} := by
        intro c hc
        obtain ⟨x, hx, hxe⟩ := Cx2.first_norm_real_nonneg S hP ε hε i hi2 w Y κ hκ c
        rw [Set.mem_ofPred_eq, hext c hc, hxe, Complex.ofReal_re, Complex.ofReal_im]
        exact ⟨hx, rfl⟩
      have hall : ∀ c, 0 ≤ (φ c).re ∧ (φ c).im = 0 := by
        intro c
        have h := closure_minimal hsub hcl
        rw [(Cx2.dense_allNe S).closure_eq] at h
        exact h (Set.mem_univ c)
      intro c
      exact ⟨Complex.ext (by simp) (by simp [(hall c).2]), (hall c).1⟩
    refine ⟨fun c => (φ (Cx2.cj S c)).re, Cφ, Complex.continuous_re.comp (hcont.comp (Cx2.cj S).continuous), ?_,
      fun c => (hreal _).2, ?_, ?_⟩
    · intro c
      refine (Complex.abs_re_le_norm _).trans ((hdec _).trans (le_of_eq ?_))
      congr 1
      exact Fintype.prod_equiv S.pl _ _ (fun v => by simp [J.coord, Cx2.norm_cj])
    · intro t ht
      have hne : ∀ v, (Cx2.cj S (J.cemb E t)) (S.pl v) ≠ 0 := by
        intro v
        rw [Cx2.cj_cemb]
        exact (map_ne_zero (S.σ v)).mpr ht
      have h1 : S.N1 ε i w.1 Y κ (Cx2.cj S (J.cemb E t)) = (S.mkData Kr hK0 Th e).Nst ε i 1 w Y κ t t := by
        simp [HidaSetting.N1, TB.Data.Nst, HidaSetting.mkData, HidaSetting.gram, loc, TB.join, Cx2.cj_cemb, hi2']
      show _ = (φ (Cx2.cj S (J.cemb E t))).re
      rw [hext _ hne, h1]
    · intro l
      show S.Nhat ε i w.1 Y κ l = _
      unfold HidaSetting.Nhat
      congr 1
      rw [integral_congr_ae (g := fun c => φ c * S.psiInf l c)
        ((Cx2.ae_allNe S).mono fun c hc => by simp only [hext c hc])]
      rw [← (Cx2.cj_mp S).integral_comp (Cx2.cj S).toHomeomorph.measurableEmbedding
        (fun c => φ c * S.psiInf l c)]
      rw [Real.fourier_eq]
      congr 1
      funext c
      rw [(hreal (Cx2.cj S c)).1, Circle.smul_def, smul_eq_mul, mul_comm]
      congr 1
      unfold HidaSetting.psiInf
      rw [Real.fourierChar_apply, Cx2.inner_dm]
      have hs : (∑ v : Fin S.f, 2 * (S.σ v l * (Cx2.cj S c) (S.pl v)).re) =
          ∑ w : InfinitePlace E, 2 * (w.embedding l * c w).re :=
        Fintype.sum_equiv S.pl _ _ (fun v => by rw [Cx2.re_cj])
      rw [hs]
      congr 1
      push_cast
      ring

end

end Formalism.FourierDecayAlt.P
