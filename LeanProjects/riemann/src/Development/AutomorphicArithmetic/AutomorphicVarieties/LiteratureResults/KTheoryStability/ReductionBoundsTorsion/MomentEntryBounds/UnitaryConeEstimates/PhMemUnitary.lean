import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.ExistsFinsetCosets

noncomputable section

set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL GroundTheory.Automorphic
open scoped NumberField.AdeleRing

namespace PositivityTheory.KB.MomentRationality.Cz.Arch

open PositivityTheory.KB.MomentRationality.RedGL

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

abbrev ph {w : InfinitePlace L} (hw : w.IsComplex) :
    Matrix (Fin N) (Fin N) w.Completion →+* Matrix (Fin N) (Fin N) ℂ :=
  (Completion.ringEquivComplexOfIsComplex hw).toRingHom.mapMatrix

theorem ph_apply {w : InfinitePlace L} (hw : w.IsComplex) (A : Matrix (Fin N) (Fin N) w.Completion) (i j : Fin N) :
    ph hw A i j = Completion.ringEquivComplexOfIsComplex hw (A i j) := rfl

theorem e_alg {w : InfinitePlace L} (hw : w.IsComplex) (l : L) :
    Completion.ringEquivComplexOfIsComplex hw (algebraMap L w.Completion l) = w.embedding l := by
  rw [Completion.ringEquivComplexOfIsComplex_apply]
  simp

theorem ph_diag {w : InfinitePlace L} (hw : w.IsComplex) (γ : GL (Fin N) L) :
    ph hw ((Reduction.infAt w (AdelicGLn.diagonal L N γ) : GL (Fin N) w.Completion) :
      Matrix (Fin N) (Fin N) w.Completion) = (γ : Matrix (Fin N) (Fin N) L).map w.embedding := by
  ext i j
  rw [ph_apply, Matrix.map_apply, ← e_alg hw]
  rfl

private theorem moduleSection_component_self_eq_posRealElem {w : InfinitePlace L} (ρ : ℝ) (hρ : 0 < ρ) :
    ((GroundTheory.Global.moduleSection w ⟨ρ, hρ⟩ : 𝔸[𝓞 L, L]ˣ) : 𝔸[𝓞 L, L]).1 w = GroundTheory.Global.posRealElem w ρ := by
  classical
  show @Pi.mulSingle _ (fun j : InfinitePlace L => j.Completion) _ _ w _ w = _
  unfold Pi.mulSingle Function.update
  split
  · rfl
  · exact absurd rfl ‹_›

private theorem moduleSection_component_eq_one_of_ne {w v : InfinitePlace L} (h : v ≠ w) (ρ : ℝ) (hρ : 0 < ρ) :
    ((GroundTheory.Global.moduleSection v ⟨ρ, hρ⟩ : 𝔸[𝓞 L, L]ˣ) : 𝔸[𝓞 L, L]).1 w = 1 := by
  classical
  show @Pi.mulSingle _ (fun j : InfinitePlace L => j.Completion) _ _ v _ w = _
  unfold Pi.mulSingle Function.update
  split
  · exact absurd ‹w = v›.symm h
  · rfl

private theorem finset_prod_units_component_eq_prod (w : InfinitePlace L) (s : Finset (InfinitePlace L))
    (f : InfinitePlace L → 𝔸[𝓞 L, L]ˣ) :
    ((∏ v ∈ s, f v : 𝔸[𝓞 L, L]ˣ) : 𝔸[𝓞 L, L]).1 w = ∏ v ∈ s, ((f v : 𝔸[𝓞 L, L]).1 w) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih]
    rfl

private theorem posIdele_infinite_component (w : InfinitePlace L) (ρ : ℝ) (hρ : 0 < ρ) :
    ((Reduction.posIdele (K := L) ρ hρ : 𝔸[𝓞 L, L]ˣ) : 𝔸[𝓞 L, L]).1 w =
      GroundTheory.Global.posRealElem w (ρ ^ w.mult) := by
  unfold Reduction.posIdele
  rw [finset_prod_units_component_eq_prod, Finset.prod_eq_single w]
  · exact moduleSection_component_self_eq_posRealElem _ _
  · intro v _ hv
    exact moduleSection_component_eq_one_of_ne hv _ _
  · simp

theorem ph_posIdele {w : InfinitePlace L} (hw : w.IsComplex) (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) :
    ph hw ((Reduction.infAt w (Reduction.diagUnits N fun i => Reduction.posIdele (K := L) (r i) (hr i)) :
      GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) =
        diagonal fun i => ((r i : ℝ) : ℂ) := by
  ext i j
  rw [ph_apply]
  have hent : ((Reduction.infAt w (Reduction.diagUnits N fun i => Reduction.posIdele (K := L) (r i) (hr i)) :
      GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i j =
      ((diagonal fun k => ((Reduction.posIdele (K := L) (r k) (hr k) : 𝔸[𝓞 L, L]ˣ) : 𝔸[𝓞 L, L])) i j).1 w := rfl
  rw [hent]
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq, diagonal_apply_eq, posIdele_infinite_component,
      InfinitePlace.mult_isComplex ⟨w, hw⟩]
    have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
    unfold GroundTheory.Global.posRealElem
    rw [dif_neg hnr, RingEquiv.apply_symm_apply, Real.sqrt_sq (hr i).le]
  · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ h]
    show Completion.ringEquivComplexOfIsComplex hw 0 = 0
    exact map_zero _

private theorem mem_unitaryGroup_of_vecMul_norm_sq_preserved (M : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ y : Fin N → ℂ, ∑ i, ‖(y ᵥ* M) i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2) : M ∈ unitaryGroup (Fin N) ℂ := by
  rw [← Matrix.transpose_mem_unitaryGroup_iff, mem_unitaryGroup_iff']
  apply EquivLike.injective (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N))
  have hn : ∀ x, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N) Mᵀ x‖ = ‖x‖ := by
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_transpose, h]
  have ha := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp hn
  rw [← ContinuousLinearMap.star_eq_adjoint] at ha
  rw [map_mul, map_star, map_one]
  exact ha

theorem ph_mem_unitary {w : InfinitePlace L} (hw : w.IsComplex) {k : GL (Fin N) w.Completion}
    (hk : k ∈ Reduction.archCompact w) :
    ph hw (k : Matrix (Fin N) (Fin N) w.Completion) ∈ unitaryGroup (Fin N) ℂ := by
  apply mem_unitaryGroup_of_vecMul_norm_sq_preserved
  intro y
  let e := Completion.ringEquivComplexOfIsComplex hw
  have hnorm : ∀ x, ‖e x‖ = ‖x‖ := fun x => by
    show ‖Completion.ringEquivComplexOfIsComplex hw x‖ = ‖x‖
    rw [Completion.ringEquivComplexOfIsComplex_apply]
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  let y' : Fin N → w.Completion := fun i => e.symm (y i)
  have hy : ∀ i, y i = e (y' i) := fun i => (e.apply_symm_apply (y i)).symm
  have hk' : Reduction.euclidNorm (y' ᵥ* (k : Matrix (Fin N) (Fin N) w.Completion)) = Reduction.euclidNorm y' := hk y'
  unfold Reduction.euclidNorm at hk'
  rw [Real.sqrt_inj (by positivity) (by positivity)] at hk'
  have hv : ∀ i, (y ᵥ* ph hw (k : Matrix (Fin N) (Fin N) w.Completion)) i =
      e ((y' ᵥ* (k : Matrix (Fin N) (Fin N) w.Completion)) i) := by
    intro i
    have h1 := RingHom.map_vecMul e.toRingHom (k : Matrix (Fin N) (Fin N) w.Completion) y' i
    have : y = (e.toRingHom : w.Completion → ℂ) ∘ y' := funext hy
    rw [this]
    exact h1.symm
  simp only [hv, hnorm, hk']
  simp only [hy, hnorm]

private theorem infAt_apply_entry_eq_adele_component (w : InfinitePlace L) (g : AdelicGLn.AdelicGL L N) (i j : Fin N) :
    ((Reduction.infAt w g : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i j =
      ((g : Matrix (Fin N) (Fin N) 𝔸[𝓞 L, L]) i j).1 w := rfl

private theorem infAt_inv' (w : InfinitePlace L) (g : AdelicGLn.AdelicGL L N) :
    Reduction.infAt w g⁻¹ = (Reduction.infAt w g)⁻¹ := by
  unfold Reduction.infAt
  rw [map_inv]
  rfl

private theorem infAt_blockTriangular_of_mem_adelicBorel (w : InfinitePlace L) {b : AdelicGLn.AdelicGL L N}
    (hB : b ∈ Reduction.adelicBorel) :
    ((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion).BlockTriangular id := by
  intro i j hij
  rw [infAt_apply_entry_eq_adele_component]
  have h0 : (b : Matrix (Fin N) (Fin N) 𝔸[𝓞 L, L]) i j = 0 := hB hij
  rw [h0]
  rfl

private theorem diag_mul_diag_eq_one_of_blockTriangular_mul_eq_one {K : Type*} [Field K] (A C : Matrix (Fin N) (Fin N) K)
    (hA : A.BlockTriangular id) (hC : C.BlockTriangular id) (h : A * C = 1) (i : Fin N) :
    A i i * C i i = 1 := by
  have := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at this
  · exact this
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [hA hlt, zero_mul]
    · rw [hC hgt, mul_zero]
  · simp

private theorem norm_ringEquivComplexOfIsComplex {w : InfinitePlace L} (hw : w.IsComplex) (x : w.Completion) :
    ‖Completion.ringEquivComplexOfIsComplex hw x‖ = ‖x‖ := by
  rw [Completion.ringEquivComplexOfIsComplex_apply]
  exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem ph_borel {w : InfinitePlace L} (hw : w.IsComplex) {b : AdelicGLn.AdelicGL L N}
    (hB : b ∈ Reduction.adelicBorel) {M0 : ℝ}
    (hb : ∀ i j : Fin N,
      ‖((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i j‖ ≤ M0 ∧
        ‖((Reduction.infAt w b⁻¹ : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i j‖ ≤ M0) :
    (ph hw ((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion)).BlockTriangular id ∧
      (∀ i j, ‖ph hw ((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i j‖ ≤
        M0 + 1) ∧
      ∀ i, (M0 + 1)⁻¹ ≤ ‖ph hw ((Reduction.infAt w b : GL (Fin N) w.Completion) :
        Matrix (Fin N) (Fin N) w.Completion) i i‖ := by
  have hU := infAt_blockTriangular_of_mem_adelicBorel w hB
  have hC := infAt_blockTriangular_of_mem_adelicBorel w (inv_mem hB)
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    rw [ph_apply, hU hij, map_zero]
  · intro i j
    rw [ph_apply, norm_ringEquivComplexOfIsComplex]
    linarith [(hb i j).1]
  · intro i
    rw [ph_apply, norm_ringEquivComplexOfIsComplex]
    have hmul : ((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) *
        ((Reduction.infAt w b⁻¹ : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) = 1 := by
      rw [infAt_inv']
      exact Units.mul_inv _
    have hd := diag_mul_diag_eq_one_of_blockTriangular_mul_eq_one _ _ hU hC hmul i
    have hn : ‖((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i i‖ *
        ‖((Reduction.infAt w b⁻¹ : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i i‖ = 1 := by
      rw [← norm_mul, hd, norm_one]
    have hpos : 0 < ‖((Reduction.infAt w b⁻¹ : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i i‖ := by
      by_contra hle
      rw [not_lt] at hle
      rw [le_antisymm hle (norm_nonneg _), mul_zero] at hn
      exact zero_ne_one hn
    rw [eq_inv_of_mul_eq_one_left hn]
    exact inv_anti₀ hpos (by linarith [(hb i i).2])

end PositivityTheory.KB.MomentRationality.Cz.Arch

namespace PositivityTheory.KB

open MomentRationality MomentRationality.RedGL MomentRationality.Cz.Arch

theorem sRedGL2 : SRedGL := by
  intro L _ _ hTC N hN
  haveI := hTC
  obtain ⟨ω, hωc, hωB, t, ht, hS⟩ := Reduction.exists_siegelSet (K := L) N
  obtain ⟨M0, hM0, hM⟩ := exists_bound_omega hωc
  let C : Set (AdelicGLn.FiniteAdelicGL L N) :=
    (fun p : AdelicGLn.AdelicGL L N × AdelicGLn.AdelicGL L N => (AdelicGLn.prodEquiv L N (p.1 * p.2)).2) ''
      (ω ×ˢ ((Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL L N)) : Set (AdelicGLn.AdelicGL L N)))
  have hCc : IsCompact C :=
    (hωc.prod Reduction.isCompact_maxCompact).image
      (continuous_snd.comp ((AdelicGLn.prodEquiv L N).continuous.comp continuous_mul))
  obtain ⟨R, hR⟩ := exists_finset_cosets hCc
  classical
  refine ⟨R.image (·⁻¹), M0 + 1, t, by linarith, ht, ?_⟩
  intro x
  let e : ∀ w : InfinitePlace L, w.Completion ≃+* ℂ := fun w =>
    Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  let xC : (w : InfinitePlace L) → GL (Fin N) w.Completion := fun w =>
    Matrix.GeneralLinearGroup.map (e w).symm.toRingHom (x w)
  let gx : AdelicGLn.AdelicGL L N :=
    (AdelicGLn.prodEquiv L N).symm ((AdelicGLn.infiniteEquiv L N).symm xC, 1)
  have hgx : ∀ w, Reduction.infAt w gx = xC w := by
    intro w
    ext a b
    rw [Reduction.infAt_apply, ← AdelicGLn.prodEquiv_apply_fst, ← AdelicGLn.infiniteEquiv_apply]
    simp [gx]
  have hgx2 : (AdelicGLn.prodEquiv L N gx).2 = 1 := by simp [gx]
  obtain ⟨γ, hγ⟩ := hS gx
  obtain ⟨b, hbω, a, ⟨r, hr, hrt, rfl⟩, k, hk, hbak⟩ := hγ
  have hfin : ((AdelicGLn.prodEquiv L N) ((AdelicGLn.diagonal L N) γ)).2 ∈ C := by
    refine ⟨(b, k), ⟨hbω, hk⟩, ?_⟩
    have h1 := congrArg (fun G => (AdelicGLn.prodEquiv L N G).2) hbak
    simp only [map_mul, Prod.snd_mul, hgx2, mul_one, Reduction.prodEquiv_diagUnits_posIdele_snd] at h1
    simpa using h1.symm
  obtain ⟨g, hgR, δ, hδ⟩ := hR γ hfin
  refine ⟨δ, g⁻¹, Finset.mem_image.mpr ⟨g, hgR, rfl⟩, r, hr, hrt, ?_⟩
  intro w
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  obtain ⟨hU, hB1, hB2⟩ := ph_borel hw (hωB hbω) (hM b hbω w)
  refine ⟨ph hw ((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion),
    hU, hB1, hB2, ph hw ((Reduction.infAt w k : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion),
    ph_mem_unitary hw (hk.1 w), ?_⟩
  have key := congrArg
    (fun G => ph hw ((Reduction.infAt w G : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion)) hbak
  simp only [Reduction.infAt_mul, Units.val_mul, map_mul, hgx] at key
  rw [ph_diag, ph_posIdele hw r hr] at key
  have hx : ph hw ((xC w : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) =
      ((x w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j
    rw [ph_apply]
    simp [xC, e]
  rw [hx] at key
  have hinv : (toK L N δ : Matrix (Fin N) (Fin N) L) =
      ((g⁻¹ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) * (γ : Matrix (Fin N) (Fin N) L) := by
    rw [hδ, Units.val_mul]
  show ((emb L N δ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * ((x w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = _
  have hemb : ((emb L N δ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (toK L N δ : Matrix (Fin N) (Fin N) L).map w.embedding := rfl
  rw [hemb, hinv, Matrix.map_mul, Matrix.mul_assoc, key]
  simp only [Matrix.mul_assoc]

end PositivityTheory.KB

end
