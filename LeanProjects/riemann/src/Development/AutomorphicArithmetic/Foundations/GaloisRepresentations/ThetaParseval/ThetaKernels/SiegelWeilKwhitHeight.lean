import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Height
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitHtA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilHeightdictStd

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem k_int_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {k : d.G} (hk : k ∈ d.K) (v : HeightOneSpectrum (𝓞 F)) (i j : Fin d.n ⊕ Fin d.n) :
    compFin F E v (inFrame d.b k i j) ∈ OE E v ∧ compFin F E v (inFrame d.b k⁻¹ i j) ∈ OE E v := by
  have h := ((d.ok.stdK k).1 hk).2
  have e : ∀ z : AE F E, compFin F E v (finOne F • z) = compFin F E v z := fun z => by
    rw [compFin_smul, evFin_finOne, one_smul]
  exact ⟨e _ ▸ compFin_intHat v (h k (by simp) i j), e _ ▸ compFin_intHat v (h k⁻¹ (by simp) i j)⟩
theorem k_unit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {k : d.G} (hk : k ∈ d.K) (w : InfinitePlace F) :
    (inFrame d.b k).map (piInf (d.B.emb w)) * ((inFrame d.b k).map (piInf (d.B.emb w)))ᴴ = 1 :=
  ((d.ok.stdK k).1 hk).1 w
theorem inFrame_mul_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (k : d.G) : inFrame d.b k * inFrame d.b k⁻¹ = 1 := by
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, mul_inv_cancel]
  simp only [inFrame, mat2, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
theorem piInf_cA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (z : AE F E) :
    piInf (d.B.emb w) (cA σ z) = star (piInf (d.B.emb w) z) := by
  simp only [piInf, RingHom.comp_apply, compInf_cA]
  exact (GlobalTheory.AdelicU.infEmb_sigR d.ok.good.cm (d.B.emb w) _).symm
theorem piInf_inclR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (e : E) :
    piInf (d.B.emb w) (inclR (F := F) (AF F) e) = (d.B.emb w).1 e := by
  simp [piInf, compInf, inclR, Algebra.TensorProduct.map_tmul, infEmb_tmul]
theorem real_at_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (ε : ℤˣ) (β : nA σ d.Y d.b)
    (D : GL (Fin d.n) (AE F E)) {k : d.G} (hk : k ∈ d.K)
    (h1 : ((ε : ℤ) : AE F E) • t.1 = D.1 * (inFrame d.b k).toBlocks₂₁)
    (h2 : ((ε : ℤ) : AE F E) • (β.1 * u.1) = D.1 * (inFrame d.b k).toBlocks₂₂) (w : InfinitePlace F) :
    ‖piInf (d.B.emb w) D.1.det‖ ^ 2 = ‖piInf (d.B.emb w) t.1.det‖ ^ 2 *
      (1 + (((g w)⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w) * (((g w)⁻¹).1)ᴴ) *
        (((g w)⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w) * (((g w)⁻¹).1)ᴴ)).det.re := by
  set pw := piInf (d.B.emb w) with hpw
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map pw = X.map pw * Y.map pw := fun X Y => Matrix.map_mul
  have hsm : ∀ {a b : Type} (c : AE F E) (X : Matrix a b (AE F E)), (c • X).map pw = pw c • X.map pw := by
    intro a b c X; ext i j; simp
  have hθ : (Gen.matInf (hOf β).1).map (θ w) = ((hOf β).1.map pw).map star := by
    ext i j
    exact hR.th w _
  have hK : ((inFrame d.b k).map pw).toBlocks₂₁ * (((inFrame d.b k).map pw).toBlocks₂₁)ᴴ +
      ((inFrame d.b k).map pw).toBlocks₂₂ * (((inFrame d.b k).map pw).toBlocks₂₂)ᴴ = 1 := by
    have hu := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.k_unit_k d hk w
    ext i j
    have := congrFun (congrFun hu (Sum.inr i)) (Sum.inr j)
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply, Matrix.one_apply,
      Sum.inr.injEq] at this
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.add_apply] using this
  have h1' := congrArg (fun M => M.map pw) h1
  have h2' := congrArg (fun M => M.map pw) h2
  simp only [hsm, hmap, map_intCast] at h1' h2'
  have htu : (t.1.map pw)ᴴ * u.1.map pw = 1 := by
    have h0 := congrArg (fun M => M.map pw) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.levi_tu_k d x t u hR.levi)
    simp only [hmap, Matrix.map_one _ (map_zero pw) (map_one pw)] at h0
    have h3 : ((t.1ᵀ.map pw) * ((u.1.map (cA σ)).map pw)).map (starRingEnd ℂ) =
        (1 : Matrix (Fin d.n) (Fin d.n) ℂ).map (starRingEnd ℂ) := by rw [h0]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    have e1 : ((u.1.map (cA σ)).map pw).map (starRingEnd ℂ) = u.1.map pw := by
      ext i j
      simp only [Matrix.map_apply]
      rw [hpw, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.piInf_cA_k]
      simp
    rw [e1] at h3
    rw [← h3]
    rfl
  have hh : ((hOf β).1.map pw)ᴴ = (hOf β).1.map pw := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← (hOf β).2 a b, sigR_eq_cA', _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.piInf_cA_k]
  have hβ : β.1.map pw = -(((d.B.emb w).1 η) • ((hOf β).1.map pw)ᵀ) := by
    rw [hR.hof β]
    ext i j
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.scalar_apply, incM, Matrix.diagonal_apply, hpw, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.piInf_inclR_k]
  have hg : (g w).1 * (u.1.map pw)ᴴ = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 := hR.gc w
  have he : ‖(((ε : ℤ) : ℂ))‖ = 1 := by rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hη : (d.B.emb w).1 η ≠ 0 := (map_ne_zero _).2 hR.ne
  have hgi : IsUnit (g w).1.det := (Matrix.isUnit_iff_isUnit_det _).1 (g w).isUnit
  have key := GlobalTheory.T.det_sq_norm_eq_hermitian_block_formula (t.1.map pw) (u.1.map pw) (D.1.map pw) ((inFrame d.b k).map pw).toBlocks₂₁
    ((inFrame d.b k).map pw).toBlocks₂₂ (β.1.map pw) ((hOf β).1.map pw) (g w).1 ((ε : ℤ) : ℂ) ((d.B.emb w).1 η)
    he hη hK h1' h2' htu hh hβ hg hgi
  rw [det_map, det_map] at key
  rw [hθ, Matrix.coe_units_inv]
  exact key
theorem fin_at_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (ε : ℤˣ) (β : nA σ d.Y d.b)
    (D : GL (Fin d.n) (AE F E)) {k : d.G} (hk : k ∈ d.K)
    (h1 : ((ε : ℤ) : AE F E) • t.1 = D.1 * (inFrame d.b k).toBlocks₂₁)
    (h2 : ((ε : ℤ) : AE F E) • (β.1 * u.1) = D.1 * (inFrame d.b k).toBlocks₂₂) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure] :
    ‖Algebra.norm (v.adicCompletion F) (compFin F E v D.1.det)‖ =
      ‖Algebra.norm (v.adicCompletion F) (compFin F E v t.1.det)‖ *
        Gen.nu2 lam (L1 σ t v) (L2 σ u η v) (Gen.matV v (hOf β).1) := by
  set cf := compFin F E v with hcf
  have hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map cf = X.map cf * Y.map cf := fun X Y => Matrix.map_mul
  have hsm : ∀ {a b : Type} (c : AE F E) (X : Matrix a b (AE F E)), (c • X).map cf = cf c • X.map cf := by
    intro a b c X; ext i j; simp
  have ht : IsUnit (t.1.map cf).det := by
    rw [det_map]; exact (Matrix.GeneralLinearGroup.det t).isUnit.map cf
  have hD : IsUnit (D.1.map cf).det := by
    rw [det_map]; exact (Matrix.GeneralLinearGroup.det D).isUnit.map cf
  have htu : (t.1.map cf)ᵀ * (u.1.map cf).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    have h0 := congrArg (fun M => M.map cf) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.levi_tu_k d x t u hR.levi)
    simp only [hmap, Matrix.map_one _ (map_zero cf) (map_one cf)] at h0
    rw [← h0, Matrix.transpose_map]
    congr 1
    ext i j
    exact (compFin_cA v _).symm
  have hη : IsUnit (inclR (F := F) (v.adicCompletion F) η) := (Ne.isUnit hR.ne).map _
  have he : IsUnit (((ε : ℤ) : v.adicCompletion F ⊗[F] E)) := ε.isUnit.map (Int.castRingHom _)
  have he1 : ‖Algebra.norm (v.adicCompletion F) (((ε : ℤ) : v.adicCompletion F ⊗[F] E))‖ = 1 := by
    rcases Int.units_eq_one_or ε with h | h
    · simp [h]
    · have : (((ε : ℤ) : v.adicCompletion F ⊗[F] E)) = algebraMap (v.adicCompletion F) _ (-1) := by
        rw [h]; simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, map_neg, map_one]
      rw [this, Algebra.norm_algebraMap, norm_pow, norm_neg, norm_one, one_pow]
  have hβ : β.1.map cf = -((inclR (F := F) (v.adicCompletion F) η) • ((hOf β).1.map cf)ᵀ) := by
    rw [hR.hof β]
    ext i j
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.scalar_apply, incM, Matrix.diagonal_apply, hcf,
      compFin_inclR]
  have hh : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (((hOf β).1.map cf) b a) = ((hOf β).1.map cf) a b := by
    intro a b
    simp only [Matrix.map_apply]
    rw [← (hOf β).2 a b]
    exact (compFin_sigR v _).symm
  have hkk : (inFrame d.b k).map cf * (inFrame d.b k⁻¹).map cf = 1 := by
    rw [← hmap, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_mul_inv_k, Matrix.map_one _ (map_zero cf) (map_one cf)]
  have h1' := congrArg (fun M => M.map cf) h1
  have h2' := congrArg (fun M => M.map cf) h2
  simp only [hsm, hmap, map_intCast] at h1' h2'
  have key := PositivityTheory.SiegelWeilFormula.HeightDict.fin_index hcm v d.n (t.1.map cf) (u.1.map cf) (D.1.map cf) (β.1.map cf) ((hOf β).1.map cf)
    (inclR (F := F) (v.adicCompletion F) η) (((ε : ℤ) : v.adicCompletion F ⊗[F] E))
    ((inFrame d.b k).map cf) ((inFrame d.b k⁻¹).map cf) ht hD htu hη he he1 hβ hh hkk
    (fun i j => (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.k_int_k d hk v i j).1) (fun i j => (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.k_int_k d hk v i j).2) h1' h2' lam
  rw [det_map, det_map] at key
  exact key
theorem absE_split_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : (AE F E)ˣ) :
    ((GlobalTheory.Doubling.absE F E x : ℝ≥0) : ℝ) =
      (∏ w, ‖piInf (d.B.emb w) x.1‖ ^ 2) * ∏ᶠ v, ‖Algebra.norm (v.adicCompletion F) (compFin F E v x.1)‖ := by
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_eq_sq d.ok.good.cm (d.B.emb w), NNReal.coe_pow, coe_nnnorm]
    rfl
  · set s := (GlobalTheory.Doubling.finite_mulSupport_absEv x).toFinset with hs
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) (by simp [s]), NNReal.coe_prod,
      finprod_eq_prod_of_mulSupport_subset _ (s := s) ?_]
    · exact Finset.prod_congr rfl fun v _ => (normV_eq x v).symm
    · intro v hv
      simp only [Set.Finite.coe_toFinset, s, Function.mem_mulSupport] at hv ⊢
      rw [normV_eq] at hv
      exact fun h => hv (by rw [h, NNReal.coe_one])
theorem heightDict_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.HeightDict_k := by
  intro F E _ _ _ _ _ σ d R x t u T η T₀ hOf θ fr g hR nb lam 𝓖 hc ε w hw
  choose lv hlv using fun v : HeightOneSpectrum (𝓞 F) => exists_haar_tup (E := E) v d.n
  obtain ⟨hCO, hstd⟩ := _root_.PositivityTheory.SiegelWeilFormula.HeightDict.fin_std_k (σ := σ) d d.n t u η hR.ne
  have hat : (0 : ℝ) < ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ) :=
    absE_pos _
  refine ⟨lv, L1 σ t, L2 σ u η, ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ)⁻¹,
    inv_pos.2 hat, hlv, hCO, hstd, fun β => ?_⟩
  obtain ⟨D, k, hk, ha, hb1, hb2⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.frame_iwa_k d (w * nb β * x)
  obtain ⟨hr1, hr2⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.bottom_rows_k d x t u hR.levi nb hc.1 ε w hw β
  have h1 := hr1.symm.trans hb1
  have h2 := hr2.symm.trans hb2
  have hre := fun w' => _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.real_at_k d R hR ε β D hk h1 h2 w'
  have hfi := fun v => _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.fin_at_k d R hR ε β D hk h1 h2 v (lv v)
  set X : InfinitePlace F → ℝ := fun w' => (1 + (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ) *
        (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ)).det.re with hX
  set N : HeightOneSpectrum (𝓞 F) → ℝ := fun v => Gen.nu2 (lv v) (L1 σ t v) (L2 σ u η v) (Gen.matV v (hOf β).1)
    with hN
  have hnuA : Gen.nuA θ g lv (L1 σ t) (L2 σ u η) (hOf β).1 = (∏ w', X w') * ∏ᶠ v, N v := rfl
  have hsD := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.absE_split_k d (Matrix.GeneralLinearGroup.det D)
  have hsT := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.absE_split_k d (Matrix.GeneralLinearGroup.det t)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hsD hsT
  have hfT := fin_supp (Matrix.GeneralLinearGroup.det t)
  have hfD := fin_supp (Matrix.GeneralLinearGroup.det D)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hfT hfD
  have hT0 := normV_ne (Matrix.GeneralLinearGroup.det t)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hT0
  have hNv : ∀ v, N v = ‖Algebra.norm (v.adicCompletion F) (compFin F E v D.1.det)‖ /
      ‖Algebra.norm (v.adicCompletion F) (compFin F E v t.1.det)‖ := fun v => by
    rw [hfi v, mul_div_cancel_left₀ _ (hT0 v)]
  have hNs : (Function.mulSupport N).Finite := by
    refine (hfD.union hfT).subset fun v hv => ?_
    by_contra hc'
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hc'
    exact hv (by rw [hNv v, hc'.1, hc'.2, div_one])
  have hA : ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det D) : ℝ≥0) : ℝ) =
      ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ) *
        Gen.nuA θ g lv (L1 σ t) (L2 σ u η) (hOf β).1 := by
    rw [hsD, hsT, hnuA, Finset.prod_congr rfl fun w' _ => hre w', Finset.prod_mul_distrib,
      finprod_congr fun v => hfi v, finprod_mul_distrib hfT hNs]
    ring
  have hDpos := absE_pos (Matrix.GeneralLinearGroup.det D)
  refine ⟨?_, ?_⟩
  · rw [hA] at hDpos
    exact pos_of_mul_pos_right hDpos hat.le
  · rw [ha, hA, mul_inv]
end PositivityTheory.SiegelWeilFormula.KWhit.Ht
end
end
