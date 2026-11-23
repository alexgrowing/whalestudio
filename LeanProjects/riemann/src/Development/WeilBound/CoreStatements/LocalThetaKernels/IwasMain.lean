import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasLoc
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasFrame
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasAd

noncomputable section

namespace PositivityTheory.ThKH.Iwas

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG PositivityTheory.ThK
open GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

section Alg

variable {L : Type} [Field L] {c : L →+* L} {m : ℕ}

theorem iso_smul_iff {ι : Type} [Fintype ι] {l : L} (hl : l ≠ 0) (A N : Matrix ι ι L) :
    Iso c (l • A) (l • A) N ↔ Iso c A A N := by
  unfold Iso
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact (smul_right_injective _ hl).eq_iff

theorem iso_submatrix {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) {A N : Matrix ι ι L} (h : Iso c A A N) :
    Iso c (A.submatrix e e) (A.submatrix e e) (N.submatrix e e) := by
  unfold Iso at *
  change Nᵀ.submatrix e e * _ * (N.map c).submatrix e e = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

variable (σ) in

def USub (X : Spc F E n) (v : Pl F) : Subgroup (UA σ X.J) where
  carrier := UAt σ X (evFin F v)
  one_mem' := fun u _ => by
    have : mat (1 : UA σ X.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  mul_mem' := fun {g h} hg hh => by
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      have : mat (g * h) = mat g * mat h := rfl
      rw [this, sub_mul, one_mul]; abel
    change At _ (mat (g * h) - 1)
    rw [e]
    exact at_add (at_mul_left hg _) hh
  inv_mem' := fun {g} hg => by
    have e0 : mat g⁻¹ * mat g = 1 := g.1.inv_mul
    have e : mat g⁻¹ - 1 = 0 - mat g⁻¹ * (mat g - 1) := by rw [mul_sub, e0, mul_one, zero_sub, neg_sub]
    change At _ (mat g⁻¹ - 1)
    rw [e]
    exact at_sub at_zero (at_mul_right _ hg)

theorem exists_lift_UA (hw : IsInertAt F E v w) {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E}
    (hc : IsConjAt σ h c) (W : Spc F E n) {g g' : Matrix (Fin n) (Fin n) (w.adicCompletion E)} (hg : g * g' = 1)
    (hi : Iso c (W.J.map (algebraMap E _)) (W.J.map (algebraMap E _)) g) :
    ∃ k ∈ UAt σ W (evFin F v), (mat k).map (piE h) = g := by
  obtain ⟨X, hX, eX⟩ := mat_surj h (g - 1)
  obtain ⟨X', hX', eX'⟩ := mat_surj h (g' - 1)
  have one : (1 : Matrix (Fin n) (Fin n) (AE F E)).map (piE h) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e1 : (1 + X).map (piE h) = g := by rw [Matrix.map_add _ (map_add _), one, eX, add_sub_cancel]
  have e2 : (1 + X').map (piE h) = g' := by rw [Matrix.map_add _ (map_add _), one, eX', add_sub_cancel]
  have e3 : (1 + X) * (1 + X') = 1 := mat_inj hw h (by
    rw [show (1 + X) * (1 + X') - 1 = X * (1 + X') + X' by noncomm_ring]
    exact at_add (at_mul_left hX _) hX') (by rw [Matrix.map_mul, e1, e2, hg, one])
  refine ⟨⟨⟨1 + X, 1 + X', e3, mul_eq_one_comm.1 e3⟩, ?_⟩, ?_, e1⟩
  · change (1 + X)ᵀ * incM F W.J * (1 + X).map (cA σ) = incM F W.J
    refine mat_inj hw h ?_ ?_
    · have a1 : (1 + X).map (cA σ) = 1 + X.map (cA σ) := by
        rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
      rw [show (1 + X)ᵀ * incM F W.J * (1 + X).map (cA σ) - incM F W.J =
          Xᵀ * (incM F W.J * (1 + X).map (cA σ)) + incM F W.J * X.map (cA σ) by
        rw [a1, Matrix.transpose_add, Matrix.transpose_one]; noncomm_ring]
      exact at_add (at_mul_left (at_transpose hX) _) (at_mul_right _ (at_map hX))
    · rw [map_gram hc, e1, hi]
      exact Matrix.ext fun i j => (piE_incl h _).symm
  · change At _ (1 + X - 1)
    rwa [add_sub_cancel_left]

section Frame

variable (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {W : Spc F E n} {a : GL (Fin n) (w.adicCompletion E)}
  (ha : IsFrameAt w W.L a)

theorem mulVec_int {ι κ : Type} [Fintype κ] {N : Matrix ι κ (w.adicCompletion E)} (hN : ∀ i j, N i j ∈ Ov E w)
    {z : κ → w.adicCompletion E} (hz : ∀ j, z j ∈ Ov E w) (i : ι) : (N *ᵥ z) i ∈ Ov E w :=
  sum_mem fun j _ => mul_mem (hN i j) (hz j)

theorem one_int {ι : Type} [DecidableEq ι] (i j : ι) : (1 : Matrix ι ι (w.adicCompletion E)) i j ∈ Ov E w := by
  rw [Matrix.one_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

include ha in
theorem coord_int {z : Fin n → w.adicCompletion E} (hz : z ∈ latAt w W.L) (i : Fin n) : ((a⁻¹).1 *ᵥ z) i ∈ Ov E w :=
  (ha _).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) i

include hw ha in
theorem stab_iff (g : Matrix (Fin n) (Fin n) (AE F E)) :
    (∀ y ∈ latW W v, g *ᵥ y ∈ latW W v) ↔ ∀ i j, ((a⁻¹).1 * g.map (piE h) * a.1) i j ∈ Ov E w := by
  constructor
  · intro hg i j
    obtain ⟨y, hy, ey⟩ := vec_surj h (a.1 *ᵥ fun k => (1 : Matrix _ _ (w.adicCompletion E)) k j)
    have h1 := ((mem_latW_iff hw h W _).1 (hg y ((mem_latW_iff hw h W y).2
      ⟨hy, ey ▸ (ha _).1 fun k => one_int k j⟩))).2
    have h2 := coord_int ha h1 i
    rw [piE_mulVec, ey, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h2
    change ((a⁻¹).1 * g.map (piE h) * a.1 * 1 : Matrix _ _ _) i j ∈ _ at h2
    rwa [Matrix.mul_one] at h2
  · intro hg y hy
    obtain ⟨h1, h2⟩ := (mem_latW_iff hw h W y).1 hy
    refine (mem_latW_iff hw h W _).2 ⟨at_mulVec_right _ h1, ?_⟩
    have := (ha _).1 (mulVec_int hg (coord_int ha h2))
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← piE_mulVec] at this

variable {m : ℕ} {f : Fin m → Fin n} {C : Matrix (Fin n) (Fin m) (AE F E)} (hC : At (evFin F v) C)
  (eC : C.map (piE h) = a.1.submatrix id f)

include hw ha hC eC in
theorem cols_mem {s : Fin m → AE F E} (hs : ∀ j, piE h (s j) ∈ Ov E w) : C *ᵥ s ∈ latW W v := by
  refine (mem_latW_iff hw h W _).2 ⟨at_mulVec_left hC _, ?_⟩
  have e : a.1.submatrix id f = a.1 * (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).submatrix id f := by
    conv_lhs => rw [← Matrix.mul_one a.1]
    rfl
  rw [piE_mulVec, eC, e, ← Matrix.mulVec_mulVec]
  exact (ha _).1 (mulVec_int (fun i j => one_int _ _) hs)

include hw hC eC in
theorem isLagAt_cols {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) (hn : n = 2 * m)
    (hf : Function.Injective f) (h0 : ∀ i j, (a.1ᵀ * W.J.map (algebraMap E _) * a.1.map c : Matrix _ _ _) (f i) (f j) = 0) :
    IsLagAt σ W v C where
  rank := hn
  supp := hC
  iso := mat_inj hw h (at_sub (at_mul_right _ (at_map hC)) at_zero) (by
    rw [map_gram hc, eC, Matrix.map_zero _ (map_zero _)]
    exact Matrix.ext h0)
  free := fun t ht e => vec_inj hw h (at_sub ht at_zero) (funext fun i => by
    have e1 := congrArg (fun y => ((a⁻¹).1 *ᵥ (piE h ∘ y)) (f i)) e
    have e2 : (a⁻¹).1 * a.1.submatrix id f = (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).submatrix id f := by
      rw [← a.inv_mul]
      rfl
    simp only [piE_mulVec, eC, Matrix.mulVec_mulVec, e2] at e1
    rw [show piE h ∘ (0 : Fin n → AE F E) = 0 from funext fun _ => map_zero _, Matrix.mulVec_zero] at e1
    simpa [Matrix.mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using e1)

end Frame

theorem iwasawa : PositivityTheory.ThK.Iwasawa := by
  intro F E _ _ _ _ _ σ n d B X W M om hP v ⟨m, hm⟩ ⟨w, hw⟩
  subst hm
  obtain ⟨r, s, hW⟩ := hP.skew
  have hσ := hP.base.cm
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨a, ha, l, hl, hg⟩ := exists_frame hσ hw h hc hW
  obtain ⟨Cy, hy, ey⟩ := mat_surj h (a.1.submatrix id (ee m ∘ Sum.inl))
  obtain ⟨Cx, hx, ex⟩ := mat_surj h (a.1.submatrix id (ee m ∘ Sum.inr))
  have hA : ∀ x y, antiJ (w.adicCompletion E) (m + m) (ee m x) (ee m y) = Wm _ (Fin m) x y := fun x y =>
    congrFun (congrFun (antiJ_submatrix _ m) x) y
  have hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1 := hg
  have one : (1 : Matrix (Fin (m + m)) (Fin (m + m)) (AE F E)).map (piE h) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let Φ : UA σ W.J →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E) :=
    { toFun := fun g => ((a⁻¹).1 * (mat g).map (piE h) * a.1).submatrix (ee m) (ee m)
      map_one' := by
        rw [show mat (1 : UA σ W.J) = 1 from rfl, one, Matrix.mul_one, Units.inv_mul, Matrix.submatrix_one_equiv]
      map_mul' := fun g g' => by
        rw [show mat (g * g') = mat g * mat g' from rfl, Matrix.submatrix_mul_equiv, Matrix.map_mul]
        simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left] }
  have hΦ : ∀ g, Φ g = ((a⁻¹).1 * (mat g).map (piE h) * a.1).submatrix (ee m) (ee m) := fun _ => rfl
  have hint : ∀ g, (∀ i j, Valued.v (Φ g i j) ≤ 1) ↔ ∀ y ∈ latW W v, mat g *ᵥ y ∈ latW W v := fun g => by
    rw [stab_iff hw h ha]
    refine ⟨fun H i j => ?_, fun H i j => H _ _⟩
    obtain ⟨i, rfl⟩ := (ee m).surjective i
    obtain ⟨j, rfl⟩ := (ee m).surjective j
    exact H i j
  refine ⟨m, Cy, isLagAt_cols hw h hy ey hc (two_mul m).symm ((ee m).injective.comp Sum.inl_injective) fun i j => ?_,
    ⟨Cx, isLagAt_cols hw h hx ex hc (two_mul m).symm ((ee m).injective.comp Sum.inr_injective) fun i j => ?_,
      fun y hy' => ?_⟩,
    group_main hU (USub σ W v) Φ (fun g => ?_) (fun g hg g' hg' e => ?_) (fun N hN => ?_) _ _ (fun g => ?_) fun g hg h0 => ?_⟩
  · rw [hg, Matrix.smul_apply, Function.comp, Function.comp, hA]
    exact smul_zero _
  · rw [hg, Matrix.smul_apply, Function.comp, Function.comp, hA]
    exact smul_zero _
  · obtain ⟨h1, h2⟩ := (mem_latW_iff hw h W y).1 hy'
    set z := (a⁻¹).1 *ᵥ (piE h ∘ y) with hz
    obtain ⟨s, -, es⟩ := vec_surj h (z ∘ ee m ∘ Sum.inl)
    obtain ⟨t, -, et⟩ := vec_surj h (z ∘ ee m ∘ Sum.inr)
    refine ⟨s, t, cols_mem hw h ha hy ey fun j => ?_, cols_mem hw h ha hx ex fun j => ?_,
      vec_inj hw h (at_sub h1 (at_add (at_mulVec_left hy _) (at_mulVec_left hx _))) ?_⟩
    · rw [show piE h (s j) = _ from congrFun es j]; exact coord_int ha h2 _
    · rw [show piE h (t j) = _ from congrFun et j]; exact coord_int ha h2 _
    · have e : piE h ∘ y = a.1 *ᵥ z := by rw [hz, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [show piE h ∘ (Cy *ᵥ s + Cx *ᵥ t) = piE h ∘ (Cy *ᵥ s) + piE h ∘ (Cx *ᵥ t) from funext fun i => map_add _ _ _,
        piE_mulVec, piE_mulVec, ey, ex, es, et, e]
      funext i
      change ∑ k, a.1 i k * z k = _
      rw [← (ee m).sum_comp, Fintype.sum_sum_type]
      rfl
  · have h1 : Iso c (W.J.map (algebraMap E _)) (W.J.map (algebraMap E _)) ((mat g).map (piE h)) := by
      unfold Iso
      rw [← map_gram hc, show (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J from g.2]
      exact Matrix.ext fun i j => piE_incl h _
    rw [hΦ, ← antiJ_submatrix]
    exact iso_submatrix _ ((iso_smul_iff hl _ _).1 (((hai.inv a.mul_inv).mul h1).mul hai))
  · have e1 : (mat g).map (piE h) = (mat g').map (piE h) := by
      have e2 := congrArg (fun N => a.1 * N.submatrix (ee m).symm (ee m).symm * (a⁻¹).1) e
      simpa [hΦ, Matrix.mul_assoc] using e2
    refine Subtype.ext (Units.ext (mat_inj hw h ?_ e1))
    have := at_sub (show At (evFin F v) (mat g - 1) from hg) (show At (evFin F v) (mat g' - 1) from hg')
    rwa [sub_sub_sub_cancel_right] at this
  · have h1 := iso_submatrix (ee m).symm hN
    rw [← antiJ_submatrix, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at h1
    have h2 := (hai.mul ((iso_smul_iff hl _ _).2 h1)).mul (hai.inv a.mul_inv)
    have h3 := h2.isUnit_det (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((map_ne_zero _).2 (det_ne_zero hW)).isUnit)
    obtain ⟨k, hk, ek⟩ := exists_lift_UA hw hc W (Matrix.mul_nonsing_inv _ h3) h2
    refine ⟨k, hk, ?_⟩
    rw [hΦ, ek]
    simp [Matrix.mul_assoc]
  · rw [hint, hint]
    exact and_congr Iff.rfl ⟨fun H => ⟨fun y hy => (H y hy).1, fun y hy => (H y hy).2⟩, fun H y hy => ⟨H.1 y hy, H.2 y hy⟩⟩
  · obtain ⟨t, -, et⟩ := mat_surj h (Φ g).toBlocks₁₁
    refine ⟨hg, t, mat_inj hw h (at_sub (at_mul_right _ hy) (at_mul_left hy _)) ?_⟩
    have e : (mat g).map (piE h) * a.1 = a.1 * ((a⁻¹).1 * (mat g).map (piE h) * a.1) := by
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [Matrix.map_mul, Matrix.map_mul, ey, et]
    refine Matrix.ext fun i j => (congrFun (congrFun e i) (ee m (Sum.inl j))).trans ?_
    rw [Matrix.mul_apply, ← (ee m).sum_comp, Fintype.sum_sum_type]
    exact (congrArg _ (Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ (h0 k j))).trans (add_zero _)

end PositivityTheory.ThKH.Iwas
