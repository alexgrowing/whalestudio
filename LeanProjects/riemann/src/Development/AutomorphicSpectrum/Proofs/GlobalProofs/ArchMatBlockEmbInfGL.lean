import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviBlockCentreFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFiniteIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGLiAddSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingArchimedeanComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DetALeviTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BlockEntry

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exp_sandwich' {n d : ℕ} (U : Matrix (Fin n) (Fin d) ℂ) (V : Matrix (Fin d) (Fin n) ℂ) (h : V * U = 1)
    (A : Matrix (Fin d) (Fin d) ℂ) : NormedSpace.exp (U * A * V) = 1 + U * (NormedSpace.exp A - 1) * V := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.complete ℝ _
  have h' : ∀ W : Matrix (Fin d) (Fin n) ℂ, V * (U * W) = W := fun W => by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  let f : Matrix (Fin d) (Fin d) ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => U * p.1 * V + p.2 • (1 - U * V)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h', Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero,
          smul_smul, sub_zero, add_zero, zero_add]
        module
      map_zero' := by simp
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, add_smul]; abel }
  have hf : Continuous f :=
    ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).add (continuous_snd.smul continuous_const)
  have e := NormedSpace.map_exp f hf (A, 0)
  have e1 : f (A, 0) = U * A * V := by simp [f]
  rw [e1] at e
  refine e.symm.trans ?_
  change U * (NormedSpace.exp (A, (0 : ℂ))).1 * V + (NormedSpace.exp (A, (0 : ℂ))).2 • (1 - U * V) = _
  have f1 : (NormedSpace.exp (A, (0 : ℂ))).1 = NormedSpace.exp A := Prod.fst_exp (A, (0 : ℂ))
  have f2 : (NormedSpace.exp (A, (0 : ℂ))).2 = NormedSpace.exp 0 := Prod.snd_exp (A, (0 : ℂ))
  rw [f1, f2, NormedSpace.exp_zero, one_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

theorem exp_isoFrame' : ∀ (n d : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin d) ℂ),
    Xᴴ * J * X = 0 → Yᴴ * J * Y = 0 → Xᴴ * J * Y = 1 → Yᴴ * J * X = 1 →
    ∀ B : Matrix (Fin d) (Fin d) ℂ, NormedSpace.exp (X * B * (Yᴴ * J) - Y * Bᴴ * (Xᴴ * J)) =
      1 + X * (NormedSpace.exp B - 1) * (Yᴴ * J) + Y * ((NormedSpace.exp (-B))ᴴ - 1) * (Xᴴ * J) := by
  intro n d J X Y xx yy xy yx B
  have h1 : (Yᴴ * J) * X = 1 := yx
  have h2 : (Xᴴ * J) * Y = 1 := xy
  have yy' : ∀ {m : ℕ} (W : Matrix (Fin d) (Fin m) ℂ), Yᴴ * (J * (Y * W)) = 0 := fun W => by
    rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, ← Matrix.mul_assoc Yᴴ J Y, yy, Matrix.zero_mul]
  have xx' : ∀ {m : ℕ} (W : Matrix (Fin d) (Fin m) ℂ), Xᴴ * (J * (X * W)) = 0 := fun W => by
    rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ J X, xx, Matrix.zero_mul]
  have c12 : X * B * (Yᴴ * J) * (Y * (-Bᴴ) * (Xᴴ * J)) = 0 := by
    simp only [Matrix.mul_assoc]; rw [yy']; simp
  have c21 : Y * (-Bᴴ) * (Xᴴ * J) * (X * B * (Yᴴ * J)) = 0 := by
    simp only [Matrix.mul_assoc]; rw [xx']; simp
  have hc : Commute (X * B * (Yᴴ * J)) (Y * (-Bᴴ) * (Xᴴ * J)) := by
    unfold Commute SemiconjBy; rw [c12, c21]
  have hs : X * B * (Yᴴ * J) - Y * Bᴴ * (Xᴴ * J) = X * B * (Yᴴ * J) + Y * (-Bᴴ) * (Xᴴ * J) := by
    rw [Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]
  rw [hs, Matrix.exp_add_of_commute _ _ hc, exp_sandwich' X (Yᴴ * J) h1, exp_sandwich' Y (Xᴴ * J) h2,
    ← Matrix.conjTranspose_neg, Matrix.exp_conjTranspose]
  have cross : X * (NormedSpace.exp B - 1) * (Yᴴ * J) * (Y * ((NormedSpace.exp (-B))ᴴ - 1) * (Xᴴ * J)) = 0 := by
    simp only [Matrix.mul_assoc]; rw [yy']; simp
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, cross, add_zero]
  abel

theorem infEmb_compInf_sInf' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E), Continuous Φ → Continuous Φ.symm → (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) → (∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z))) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : GlobalTheory.CuspRep.Cinf E),
 infEmb τ (compInf F E w (Φ.symm (GlobalTheory.CuspRep.sInf E z))) = GlobalTheory.CuspRep.coord τ.1 z := by
  intro F E _ _ _ _ _ _ σ hcm Φ j hΦ hΦs hj hΦz w τ z
  have key : ∀ x, GlobalTheory.LFun.infTens F E (Φ.symm x) = j.symm x.1 := fun x => by
    have e := congrArg Prod.fst (hΦz (Φ.symm x))
    rw [RingEquiv.apply_symm_apply] at e
    rw [e, RingEquiv.symm_apply_apply]
  have hL : Continuous fun z : GlobalTheory.CuspRep.Cinf E =>
      infEmb τ (compInf F E w (Φ.symm (GlobalTheory.CuspRep.sInf E z))) :=
    (GlobalTheory.Published.LeviInducedModel.cont_piInf τ).comp
      (hΦs.comp ((GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const))
  have hR : Continuous (GlobalTheory.CuspRep.coord τ.1) := by
    unfold GlobalTheory.CuspRep.coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have hsymm : Continuous (GlobalTheory.CuspRep.infEq E).symm :=
    continuous_pi fun v =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
        (continuous_apply v)
  have hD : DenseRange fun x : E => (GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x) :=
    ((GlobalTheory.CuspRep.infEq E).symm.surjective.denseRange).comp
      (NumberField.InfiniteAdeleRing.denseRange_algebraMap E) hsymm
  have hE : ∀ x : E, infEmb τ (compInf F E w (Φ.symm (GlobalTheory.CuspRep.sInf E
      ((GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x))))) =
      GlobalTheory.CuspRep.coord τ.1 ((GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x)) := by
    intro x
    have h1 : GlobalTheory.CuspRep.sInf E ((GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x)) =
        ((algebraMap E (InfiniteAdeleRing E) x, 0) : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) := by
      change ((GlobalTheory.CuspRep.infEq E ((GlobalTheory.CuspRep.infEq E).symm _), 0) : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) = _
      rw [RingEquiv.apply_symm_apply]
    have h2 : j.symm (algebraMap E (InfiniteAdeleRing E) x) = (1 : Ainf F) ⊗ₜ[F] x := by
      rw [← hj x, RingEquiv.symm_apply_apply]
    have hci : ∀ y : AF F ⊗[F] E, compInf F E w y =
        (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom (GlobalTheory.LFun.infTens F E y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b => rfl
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [h1, hci]
    erw [key]
    change infEmb τ ((Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom
      (j.symm (algebraMap E (InfiniteAdeleRing E) x))) = _
    rw [h2]
    have h3 := GlobalTheory.CuspRep.coord_algebraMap τ.1 x
    change GlobalTheory.CuspRep.coord τ.1 ((GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x)) = τ.1 x at h3
    rw [h3]
    change infEmb τ ((GlobalTheory.AutFunCompare.evW w 1) ⊗ₜ[F] x) = _
    rw [map_one, infEmb_tmul, map_one, one_mul]
  exact congrFun (hD.equalizer hL hR (funext hE)) z

open GlobalTheory.CuspRep GlobalTheory.BlockArch in

theorem archMat_blockEmb_infGL' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J X Y h ι → ∀ (y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E)), ι (GlobalTheory.CuspRep.infGL E d y) ∈ infPts σ J ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w),
 GlobalTheory.Orb.archMat σ J τ (projArch σ J w (ι (GlobalTheory.CuspRep.infGL E d y))) =
  1 + (GlobalTheory.BlockForms.blkCols h X).map τ.1 * (y.1.map (GlobalTheory.CuspRep.coord τ.1) - 1) * (((GlobalTheory.BlockForms.blkCols h Y).map τ.1)ᴴ * J.map τ.1) + (GlobalTheory.BlockForms.blkCols h Y).map τ.1 * (((y⁻¹).1.map (GlobalTheory.CuspRep.coord τ.1))ᴴ - 1) * (((GlobalTheory.BlockForms.blkCols h X).map τ.1)ᴴ * J.map τ.1) := by
  intro F E _ _ _ _ _ _ σ hcm n J _ r X Y _ l d h ι hB y
  have hmem := ((GlobalTheory.BlockForms.exists_archComp_of_isBlockEmb F E σ hcm n J r X Y l d h ι hB).choose_spec.2.2 y).1
  refine ⟨hmem, fun w τ => ?_⟩
  obtain ⟨Φ, j, hΦ, hΦs, hj1, hs, hform⟩ := hB
  let π : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)
  have hco : ∀ z : Cinf E, π (Φ.symm (sInf E z)) = coord τ.1 z := fun z =>
    infEmb_compInf_sInf' F E σ hcm Φ j hΦ hΦs hj1 hs w τ z
  have hp : ∀ y : GL (Fin d) (Cinf E), ((infGL E d y).1.map Φ.symm).map π = y.1.map (coord τ.1) := fun y => by
    rw [Matrix.map_map]
    exact congrArg Units.val (map_cornerGL_of_hom (sInf E) (π.comp Φ.symm.toRingHom) (coord τ.1) hco y)
  have hA : ∀ {m p : Type} (M : Matrix m p E), (adMat F M).map π = M.map τ.1 := fun M => by
    have e1 : (adMat F M).map (compInf F E w) = M.map (inclR (F := F) w.Completion) := map_inclR_map (evInf F w) M
    change (adMat F M).map (⇑(infEmb τ) ∘ ⇑(compInf F E w)) = _
    rw [← Matrix.map_map, e1, Matrix.map_map]
    ext i k
    simp [inclR]
  have hC : ∀ {m p : Type} (M : Matrix m p (AF F ⊗[F] E)), (Formalism.UG.cT (sigR (AF F) σ) M).map π = (M.map π)ᴴ := fun M => by
    have e1 : (Formalism.UG.cT (sigR (AF F) σ) M).map (compInf F E w) =
        Formalism.UG.cT (sigR w.Completion σ) (M.map (compInf F E w)) := map_cT_sigR_map (evInf F w) σ M
    change (Formalism.UG.cT (sigR (AF F) σ) M).map (⇑(infEmb τ) ∘ ⇑(compInf F E w)) = _
    rw [← Matrix.map_map, e1]
    ext i k
    exact (GlobalTheory.AdelicU.infEmb_sigR hcm τ _).symm
  rw [GlobalTheory.Orb.archMat_apply, matHom_projArch]
  change (((matHom _ σ J (ι (infGL E d y))).1).map (compInf F E w)).map (infEmb τ) = _
  rw [Matrix.map_map]
  change ((matHom _ σ J (ι (infGL E d y))).1).map π = _
  rw [hform, ← map_inv, map_blockForm, hA, hA, hA, hA, hC, hp, hp, Matrix.map_mul, Matrix.map_mul,
    GlobalTheory.CentreFin.map_cT_emb hcm, GlobalTheory.CentreFin.map_cT_emb hcm]

section Coord
open GlobalTheory.CuspRep (Cinf coord atEmb expGLi infGL)

variable {E : Type} [Field E] [NumberField E]

theorem continuous_coordE (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem coord_smul (τ : E →+* ℂ) (t : ℝ) (x : Cinf E) : coord τ (t • x) = (t : ℂ) * coord τ x := by
  unfold coord
  split_ifs
  · change (t • x) _ = (t : ℂ) * x _
    rw [Pi.smul_apply, Complex.real_smul]
  · change starRingEnd ℂ ((t • x) _) = (t : ℂ) * starRingEnd ℂ (x _)
    rw [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]

theorem map_coord_exp {d : ℕ} (τ : E →+* ℂ) (M : Matrix (Fin d) (Fin d) (Cinf E)) :
    (NormedSpace.exp M).map (coord τ) = NormedSpace.exp (M.map (coord τ)) := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) (Cinf E)) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hc : Continuous ((coord τ).mapMatrix : Matrix (Fin d) (Fin d) (Cinf E) → Matrix (Fin d) (Fin d) ℂ) :=
    continuous_id.matrix_map (continuous_coordE τ)
  exact NormedSpace.map_exp (coord τ).mapMatrix hc M

theorem map_coord_smul_atEmb {d : ℕ} (τ τ' : E →+* ℂ) (t : ℝ) (B : Matrix (Fin d) (Fin d) ℂ) :
    (t • B.map (atEmb τ)).map (coord τ') = (t : ℂ) • B.map (fun z => coord τ' (atEmb τ z)) := by
  ext a b
  simp [coord_smul]

end Coord

section Line
open GlobalTheory.CuspRep (Cinf coord atEmb expGLi infGL)

theorem isLineOf_blockEmb_exp' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J X Y h ι → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (B : Matrix (Fin d) (Fin d) ℂ),
 IsLineOf σ J τ ((GlobalTheory.BlockForms.blkCols h X).map τ.1 * B * (((GlobalTheory.BlockForms.blkCols h Y).map τ.1)ᴴ * J.map τ.1) - (GlobalTheory.BlockForms.blkCols h Y).map τ.1 * Bᴴ * (((GlobalTheory.BlockForms.blkCols h X).map τ.1)ᴴ * J.map τ.1))
  fun t : ℝ => ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • B.map (GlobalTheory.CuspRep.atEmb τ.1)))) := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r X Y hW l d h ι hι w τ B
  classical
  have hga := archMat_blockEmb_infGL' F E σ hcm n J hJ r X Y hW l d h ι hι
  have hoff : ∀ (w' : InfinitePlace F), w' ≠ w → ∀ (τ' : EmbOver E w') (z : ℂ), coord τ'.1 (atEmb τ.1 z) = 0 := by
    intro w' hw' τ' z
    have hmk : InfinitePlace.mk τ'.1 ≠ InfinitePlace.mk τ.1 := by
      intro e
      apply hw'
      have e' := congrArg (fun v : InfinitePlace E => v.comap (algebraMap F E)) e
      simp only [InfinitePlace.comap_mk, τ'.2, τ.2, InfinitePlace.mk_embedding] at e'
      exact e'
    unfold coord atEmb
    split_ifs <;> simp [Pi.single_eq_of_ne hmk]
  have hinv : ∀ t : ℝ, (expGLi d (t • B.map (atEmb τ.1)))⁻¹ = expGLi d ((-t) • B.map (atEmb τ.1)) := fun t => by
    have e := GlobalTheory.CuspRep.expGLi_add_smul d (B.map (atEmb τ.1)) (-t) t
    rw [neg_add_cancel, zero_smul, GlobalTheory.CuspRep.expGLi_zero] at e
    exact (eq_inv_of_mul_eq_one_left e.symm).symm
  have hexpmap : ∀ (τ' : E →+* ℂ) (s : ℝ), (expGLi d (s • B.map (atEmb τ.1))).1.map (coord τ') =
      NormedSpace.exp ((s : ℂ) • B.map (fun z => coord τ' (atEmb τ.1 z))) := fun τ' s => by
    rw [GlobalTheory.CuspRep.val_expGLi, map_coord_exp, map_coord_smul_atEmb]
  intro t
  obtain ⟨hmem, hmat⟩ := hga (expGLi d (t • B.map (atEmb τ.1)))
  refine ⟨projArch σ J w (ι (infGL E d (expGLi d (t • B.map (atEmb τ.1))))), ?_, ?_⟩
  · refine GAd_ext σ J (fun w'' => ?_) fun v => ?_
    · by_cases e : w'' = w
      · subst e; rw [projArch_embArch_self]
      · rw [projArch_embArch_ne σ J e]
        obtain ⟨τ'⟩ : Nonempty (EmbOver E w'') := inferInstance
        have inj : Function.Injective (GlobalTheory.Orb.archMat σ J τ') := fun a b e => by
          rw [GlobalTheory.Orb.archMat_eq_archEquiv J hcm, GlobalTheory.Orb.archMat_eq_archEquiv J hcm] at e
          exact (archEquiv J hcm τ').injective (Subtype.ext (Units.ext e))
        apply inj
        have hz : B.map (fun z => coord τ'.1 (atEmb τ.1 z)) = 0 := by
          ext a b; simp [hoff w'' e τ']
        rw [hmat w'' τ', map_one, hinv, hexpmap, hexpmap, hz]
        simp
    · rw [proj_embArch, ← projFinLoc_projFin, mem_infPts.1 hmem, map_one]
  · have hb : B.map (fun z => coord τ.1 (atEmb τ.1 z)) = B := by
      ext a b; simp [GlobalTheory.CuspRep.coord_atEmb]
    rw [hmat w τ, hinv, hexpmap, hexpmap, hb]
    have hJh : (J.map τ.1)ᴴ = J.map τ.1 := conjTranspose_map hcm hJ τ.1
    obtain ⟨hxx, hyy, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW τ.1
    let f : Fin d → Fin r := fun j => ⟨l + j.val, by omega⟩
    have hf : Function.Injective f := fun a b e => Fin.ext (by simpa [f] using congrArg Fin.val e)
    have key : ∀ A C : Matrix (Fin n) (Fin r) E,
        ((GlobalTheory.BlockForms.blkCols h A).map τ.1)ᴴ * J.map τ.1 * (GlobalTheory.BlockForms.blkCols h C).map τ.1 =
          ((A.map τ.1)ᴴ * J.map τ.1 * C.map τ.1).submatrix f f := by
      intro A C; ext i j; rfl
    have bxx := (key X X).trans (by rw [hxx])
    have byy := (key Y Y).trans (by rw [hyy])
    have bxy := (key X Y).trans (by rw [hxy, Matrix.submatrix_one f hf])
    have byx := GlobalTheory.CentreFin.dual_swap hJh bxy
    have ha := exp_isoFrame' n d (J.map τ.1) _ _ bxx byy bxy byx ((t : ℂ) • B)
    have hneg : ((-t : ℝ) : ℂ) • B = -((t : ℂ) • B) := by push_cast; rw [neg_smul]
    rw [hneg, ← ha]
    congr 1
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ← Complex.coe_smul, smul_sub,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]

end Line

open GlobalTheory.CuspRep in

theorem lie_eq_deriv_exp' : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ) (f : GlobalTheory.CuspRep.Sm E d) (B : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) (x : GlobalTheory.CuspRep.GA E d),
 (GlobalTheory.CuspRep.lie E d (GlobalTheory.CuspRep.toL B) f).1 x = deriv (fun t : ℝ => f.1 (x * GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • B)))) 0 := by
  intro E _ _ _ d f B x
  have hc : HasDerivAt (fun t : ℝ => toL (expGLi d (t • B)).val) (toL B) 0 := by
    letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
    haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) B (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h1
    let L : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  rw [GlobalTheory.CuspRep.lie_apply]
  exact ((hasDerivAt_curve f x (fun t : ℝ => expGLi d (t • B)) (toL B) (by simp) hc).deriv).symm

end GlobalTheory.CompanionTheory.BlockEntry
