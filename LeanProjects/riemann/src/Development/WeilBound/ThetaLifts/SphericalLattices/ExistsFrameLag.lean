import Development.WeilBound.ThetaLifts.SphericalLattices.ChartSt
import Development.WeilBound.ThetaLifts.SphericalLattices.MemIntGLIff

noncomputable section

namespace PositivityTheory.Sph.M2

open scoped Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

namespace Chart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem frame_mul {n : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {a κ : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w Λ a)
    (h1 : ∀ i j, κ.1 i j ∈ Ov E w) (h2 : ∀ i j, (κ⁻¹).1 i j ∈ Ov E w) : IsFrameAt w Λ (a * κ) := fun z => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha]
  refine ⟨fun hz => mulVec_int h1 hz, fun hz i => ?_⟩
  have := mulVec_int h2 hz i
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem free_loc (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w) {n : ℕ} {W : Spc F E n}
    {Cy : Matrix (Fin n) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) (z : Fin m → w.adicCompletion E)
    (hz : Cy.map (piE h) *ᵥ z = 0) : z = 0 := by
  obtain ⟨t, ht, rfl⟩ := vec_surj h z
  have z0 : ∀ {k : ℕ}, piE h ∘ (0 : Fin k → AE F E) = 0 := funext fun _ => map_zero _
  rw [hL.free t ht (vec_inj hw h (at_sub (at_mulVec_right _ ht) at_zero) (by rw [piE_mulVec, hz, z0])), z0]

theorem exists_frame_lag (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {B : Base F E} {W : Spc F E (m + m)} {r s : ℕ}
    (hW : W.IsSkew σ B r s) {Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) :
    ∃ a : GL (Fin (m + m)) (w.adicCompletion E), IsFrameAt w W.L a ∧ ∃ l : w.adicCompletion E, l ≠ 0 ∧
      Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1 ∧
      ∃ T : Matrix (Fin m) (Fin m) (w.adicCompletion E), IsUnit T.det ∧
        ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id = Matrix.fromRows T (0 : Matrix (Fin m) (Fin m) _) := by
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨a, ha, l, hl, hg⟩ := exists_frame hσ hw h hc hW
  have hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1 := hg
  have hC : (Cy.map (piE h))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) * (Cy.map (piE h)).map c = 0 := by
    rw [← map_gram hc, hL.iso, Matrix.map_zero _ (map_zero _)]
  have hf := free_loc h hw hL
  generalize Cy.map (piE h) = C at hC hf ⊢
  obtain ⟨Z, rfl⟩ : ∃ Z, C = a.1 * Z := ⟨(a⁻¹).1 * C, by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
  have hZ : Zᵀ * antiJ (w.adicCompletion E) (m + m) * Z.map c = 0 := by
    refine (smul_eq_zero_iff_right hl).1 ?_
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hg, ← hC, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨k, k', hkk, hk, hi, hi', T, hT, eT⟩ := exists_move hU (Y := Z.submatrix (ee m) id) (fun z hz => hf z (by
      have : Z *ᵥ z = 0 := funext fun i => by
        obtain ⟨i, rfl⟩ := (ee m).surjective i
        exact congrFun hz i
      rw [← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero])) (by
      rw [← antiJ_submatrix]
      change Zᵀ.submatrix id (ee m) * _ * (Z.map c).submatrix (ee m) id = _
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hZ]
      rfl)
  let κ : GL (Fin (m + m)) (w.adicCompletion E) :=
    ⟨k'.submatrix (ee m).symm (ee m).symm, k.submatrix (ee m).symm (ee m).symm,
      by rw [Matrix.submatrix_mul_equiv, mul_eq_one_comm.1 hkk, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, hkk, Matrix.submatrix_one_equiv]⟩
  refine ⟨a * κ, frame_mul ha (fun i j => hi' _ _) (fun i j => hi _ _), l, hl, hai.mul ((iso_smul_iff hl _ _).2 ?_), T, hT, ?_⟩
  · have h1 := iso_submatrix (ee m).symm (hk.inv hkk)
    rwa [← antiJ_submatrix, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at h1
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (a⁻¹).1, Units.inv_mul, Matrix.one_mul, ← eT,
      ← Matrix.submatrix_mul_equiv _ _ _ (ee m)]
    rw [show (κ⁻¹).1 = k.submatrix (ee m).symm (ee m).symm from rfl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

def phi (h : w.under (𝓞 F) = v) (W : Spc F E (m + m)) (a : GL (Fin (m + m)) (w.adicCompletion E)) :
    UA σ W.J →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E) where
  toFun := fun g => ((a⁻¹).1 * (mat g).map (piE h) * a.1).submatrix (ee m) (ee m)
  map_one' := by
    rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Units.inv_mul,
      Matrix.submatrix_one_equiv]
  map_mul' := fun g g' => by
    rw [show mat (g * g') = mat g * mat g' from rfl, Matrix.submatrix_mul_equiv, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

variable {h : w.under (𝓞 F) = v} {W : Spc F E (m + m)} {a : GL (Fin (m + m)) (w.adicCompletion E)}
  {c : w.adicCompletion E →+* w.adicCompletion E} {l : w.adicCompletion E}

theorem phi_apply (g : UA σ W.J) : phi h W a g = ((a⁻¹).1 * (mat g).map (piE h) * a.1).submatrix (ee m) (ee m) := rfl

theorem phi_iso (hc : IsConjAt σ h c) (hl : l ≠ 0) (hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1)
    (g : UA σ W.J) : Iso c (Wm _ (Fin m)) (Wm _ (Fin m)) (phi h W a g) := by
  have h1 : Iso c (W.J.map (algebraMap E _)) (W.J.map (algebraMap E _)) ((mat g).map (piE h)) := by
    unfold Iso
    rw [← map_gram hc, show (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J from g.2]
    exact Matrix.ext fun i j => piE_incl h _
  rw [phi_apply, ← antiJ_submatrix]
  exact iso_submatrix _ ((iso_smul_iff hl _ _).1 (((hai.inv a.mul_inv).mul h1).mul hai))

theorem phi_inj (hw : IsInertAt F E v w) {g g' : UA σ W.J} (hg : g ∈ USub σ W v) (hg' : g' ∈ USub σ W v)
    (e : phi h W a g = phi h W a g') : g = g' := by
  have e1 : (mat g).map (piE h) = (mat g').map (piE h) := by
    have e2 := congrArg (fun N => a.1 * N.submatrix (ee m).symm (ee m).symm * (a⁻¹).1) e
    simpa [phi_apply, Matrix.mul_assoc] using e2
  refine Subtype.ext (Units.ext (mat_inj hw h ?_ e1))
  have := at_sub (show At (evFin F v) (mat g - 1) from hg) (show At (evFin F v) (mat g' - 1) from hg')
  rwa [sub_sub_sub_cancel_right] at this

theorem phi_surj (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) (hl : l ≠ 0) (hJ : W.J.det ≠ 0)
    (hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1)
    {N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)} (hN : Iso c (Wm _ (Fin m)) (Wm _ (Fin m)) N) :
    ∃ g ∈ USub σ W v, phi h W a g = N := by
  have h1 := iso_submatrix (ee m).symm hN
  rw [← antiJ_submatrix, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at h1
  have h2 := (hai.mul ((iso_smul_iff hl _ _).2 h1)).mul (hai.inv a.mul_inv)
  have h3 := h2.isUnit_det (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero _).2 hJ).isUnit)
  obtain ⟨k, hk, ek⟩ := exists_lift_UA hw hc W (Matrix.mul_nonsing_inv _ h3) h2
  refine ⟨k, hk, ?_⟩
  rw [phi_apply, ek]
  simp [Matrix.mul_assoc]

theorem phi_int (hw : IsInertAt F E v w) (ha : IsFrameAt w W.L a) (g : UA σ W.J) :
    (∀ i j, Valued.v (phi h W a g i j) ≤ 1) ↔ ∀ y ∈ latW W v, mat g *ᵥ y ∈ latW W v := by
  rw [stab_iff hw h ha]
  refine ⟨fun H i j => ?_, fun H i j => H _ _⟩
  obtain ⟨i, rfl⟩ := (ee m).surjective i
  obtain ⟨j, rfl⟩ := (ee m).surjective j
  exact H i j

theorem phi_col (hw : IsInertAt F E v w) {Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)} (hy : At (evFin F v) Cy)
    (g : UA σ W.J) (t : Matrix (Fin m) (Fin m) (AE F E)) :
    mat g * Cy = Cy * t ↔ phi h W a g * ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id =
      ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id * t.map (piE h) := by
  have e1 : phi h W a g * ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id =
      ((a⁻¹).1 * (mat g * Cy).map (piE h)).submatrix (ee m) id := by
    rw [phi_apply, Matrix.submatrix_mul_equiv, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc a.1, Units.mul_inv,
      Matrix.one_mul, Matrix.mul_assoc]
  have e2 : ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id * t.map (piE h) =
      ((a⁻¹).1 * (Cy * t).map (piE h)).submatrix (ee m) id := by
    rw [Matrix.map_mul, ← Matrix.mul_assoc]
    rfl
  rw [e1, e2]
  refine ⟨fun e => by rw [e], fun e => mat_inj hw h (at_sub (at_mul_right _ hy) (at_mul_left hy _)) ?_⟩
  have e3 : (a⁻¹).1 * (mat g * Cy).map (piE h) = (a⁻¹).1 * (Cy * t).map (piE h) := by
    refine Matrix.ext fun i j => ?_
    obtain ⟨i, rfl⟩ := (ee m).surjective i
    exact congrFun (congrFun e i) j
  have e4 := congrArg (fun N => a.1 * N) e3
  simpa only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] using e4

theorem phi_par (hw : IsInertAt F E v w) {Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)} (hy : At (evFin F v) Cy)
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} (hT : IsUnit T.det)
    (eT : ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id = Matrix.fromRows T (0 : Matrix (Fin m) (Fin m) _))
    (g : UA σ W.J) : (∃ t : Matrix (Fin m) (Fin m) (AE F E), mat g * Cy = Cy * t) ↔ (phi h W a g).toBlocks₂₁ = 0 := by
  rw [← block_iff hT, ← eT]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨_, (phi_col hw hy g t).1 ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨t', -, rfl⟩ := mat_surj h t
    exact ⟨t', (phi_col hw hy g t').2 ht⟩

end Chart

open Chart in
theorem chart : ChartSt := by
  intro F E _ _ _ _ _ σ B r s m W hB hW v w hw h c hc Cy hL
  obtain ⟨a, ha, l, hl, hai, T, hT, eT⟩ := exists_frame_lag hB.cm hw h hc hW hL
  have hG : ∀ g, (phi h W a).toHomUnits g ∈ GW (w.adicCompletion E) c m := fun g => phi_iso hc hl hai g
  have hP : ∀ g, (phi h W a).toHomUnits g ∈ PW (w.adicCompletion E) c m ↔
      ∃ t : Matrix (Fin m) (Fin m) (AE F E), mat g * Cy = Cy * t := fun g => by
    rw [phi_par hw hL.supp hT eT g]
    exact ⟨fun H => GlobalTheory.LGrp.mem_blockQ_two.1 H.2, fun H => ⟨hG g, GlobalTheory.LGrp.mem_blockQ_two.2 H⟩⟩
  refine ⟨(phi h W a).toHomUnits, hG, fun g hg g' hg' e => phi_inj hw hg hg' (congrArg Units.val e), fun M hM => ?_,
    fun g hg => ?_, fun g hg => ?_, fun p _ t ht => ?_⟩
  · obtain ⟨g, hg, e⟩ := phi_surj hw hc hl (det_ne_zero hW) hai hM
    exact ⟨g, hg, Units.ext e⟩
  · rw [mem_IntGL_iff, ← map_inv]
    exact ⟨fun H => ⟨(phi_int hw ha g).2 fun y hy => (H.2 y hy).1, (phi_int hw ha g⁻¹).2 fun y hy => (H.2 y hy).2⟩,
      fun H => ⟨hg, fun y hy => ⟨(phi_int hw ha g).1 H.1 y hy, (phi_int hw ha g⁻¹).1 H.2 y hy⟩⟩⟩
  · refine ⟨fun H => (hP g).2 H.1.2, fun H => ⟨⟨hg, (hP g).1 H⟩, (USub σ W v).inv_mem hg, (hP g⁻¹).1 ?_⟩⟩
    rw [map_inv]
    exact inv_mem H
  · have e := (phi_col (a := a) (h := h) hw hL.supp p t).1 ht
    rw [eT] at e
    exact (block_det hT e).trans (RingHom.map_det (piE h) t).symm

end PositivityTheory.Sph.M2

end
