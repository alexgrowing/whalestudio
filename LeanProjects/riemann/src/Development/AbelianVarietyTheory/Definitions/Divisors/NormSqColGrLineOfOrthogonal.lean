import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic

namespace GlobalTheory.FlagZ

section Minor

variable {N : ℕ} {A B : Type} [CommRing A] [CommRing B]

abbrev Rows (N : ℕ) (l : Fin (N + 1)) : Type := Set.powersetCard (Fin N) l

def plDim (N : ℕ) (l : Fin (N + 1)) : ℕ := N.choose l - 1

theorem card_rows (N : ℕ) (l : Fin (N + 1)) : Fintype.card (Rows N l) = plDim N l + 1 := by
  rw [plDim, Nat.sub_add_cancel (Nat.choose_pos l.is_le), ← Nat.card_eq_fintype_card,
    Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin]

def rowsEquiv (N : ℕ) (l : Fin (N + 1)) : Rows N l ≃ Fin (plDim N l + 1) :=
  Fintype.equivFinOfCardEq (card_rows N l)

def cols (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) : Matrix (Fin N) (Fin l) A :=
  g.submatrix id (Fin.castLE l.is_le)

def minor (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) (I : Rows N l) : A :=
  (g.submatrix (subsetEnum I) (Fin.castLE l.is_le)).det

def plVec (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) : Fin (plDim N l + 1) → A :=
  fun a => minor g l ((rowsEquiv N l).symm a)

@[simp] theorem plVec_rowsEquiv (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) (I : Rows N l) :
    plVec g l (rowsEquiv N l I) = minor g l I := by simp [plVec]

theorem minor_map (ψ : A →+* B) (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) (I : Rows N l) :
    minor (g.map ψ) l I = ψ (minor g l I) := (ψ.map_det _).symm

theorem span_plVec (g : GL (Fin N) A) (l : Fin (N + 1)) : Ideal.span (Set.range (plVec g.1 l)) = ⊤ := by
  have h := det_submatrix_mul_eq_sum_minors (g⁻¹).1 g.1 (Fin.castLE l.is_le) (Fin.castLE l.is_le)
  rw [Units.inv_mul, submatrix_one _ (Fin.castLE_injective _), det_one] at h
  rw [Ideal.eq_top_iff_one, h]
  exact Ideal.sum_mem _ fun I _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨rowsEquiv N l I, plVec_rowsEquiv _ _ _⟩)

theorem minor_mul (g b : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1))
    (hb : ∀ i j : Fin N, (j : ℕ) < l → (l : ℕ) ≤ i → b i j = 0) (I : Rows N l) :
    minor (g * b) l I = minor g l I * (b.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
  rw [minor, minor, ← det_mul]
  congr 1
  ext i j
  simp only [submatrix_apply, mul_apply]
  refine (Fintype.sum_of_injective (Fin.castLE l.is_le) (Fin.castLE_injective _) _ _ (fun k hk => ?_)
    fun _ => rfl).symm
  rw [hb k _ j.2 (not_lt.1 fun h => hk ⟨⟨k, h⟩, rfl⟩), mul_zero]

def volSq (g : Matrix (Fin N) (Fin N) ℂ) (l : Fin (N + 1)) : ℝ := ∑ I, ‖minor g l I‖ ^ 2

theorem volSq_eq_det (g : Matrix (Fin N) (Fin N) ℂ) (l : Fin (N + 1)) :
    (volSq g l : ℂ) = ((cols g l)ᴴ * cols g l).det := by
  have h := det_mul_conjTranspose_eq_sum_norm_sq (cols g l)ᴴ
  rw [conjTranspose_conjTranspose] at h
  rw [h, volSq]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, norm_star]
  rfl

theorem volSq_of_orthogonal {g : Matrix (Fin N) (Fin N) ℂ} {d : Fin N → ℝ}
    (h : gᴴ * g = diagonal fun i => (d i : ℂ)) (l : Fin (N + 1)) :
    volSq g l = ∏ i : Fin l, d (Fin.castLE l.is_le i) := by
  have e : (cols g l)ᴴ * cols g l = (gᴴ * g).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le) := rfl
  apply Complex.ofReal_injective
  rw [volSq_eq_det, e, h, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal]
  simp

end Minor

section Ring

variable (ι : Type) [Fintype ι] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]

def genDet : MvPolynomial (ι × Fin N × Fin N) ℤ :=
  ∏ τ, (Matrix.of fun i j => MvPolynomial.X (τ, i, j)).det

variable {ι N} in

theorem eval₂_genDet (g : ι → Matrix (Fin N) (Fin N) A) :
    MvPolynomial.eval₂Hom (Int.castRingHom A) (fun x => g x.1 x.2.1 x.2.2) (genDet ι N) = ∏ τ, (g τ).det := by
  rw [genDet, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem genDet_ne_zero : genDet ι N ≠ 0 := fun h => by
  have := eval₂_genDet (ι := ι) (fun _ => (1 : Matrix (Fin N) (Fin N) ℤ))
  simp [h] at this

abbrev GLRing : Type := Localization.Away (genDet ι N)

instance : IsDomain (GLRing ι N) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (genDet_ne_zero ι N))

def univGL (τ : ι) : GL (Fin N) (GLRing ι N) :=
  GeneralLinearGroup.mk'' (Matrix.of fun i j => algebraMap _ _ (MvPolynomial.X (R := ℤ) (τ, i, j))) (by
    classical
    have h : IsUnit (algebraMap _ (GLRing ι N) (∏ τ, (Matrix.of fun i j => MvPolynomial.X (R := ℤ) (τ, i, j)).det)) :=
      IsLocalization.Away.algebraMap_isUnit (S := GLRing ι N) (genDet ι N)
    rw [map_prod] at h
    have := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ τ)) h
    rwa [RingHom.map_det] at this)

variable {ι N}

theorem univGL_apply (τ : ι) (i j : Fin N) :
    (univGL ι N τ).1 i j = algebraMap _ _ (MvPolynomial.X (R := ℤ) (τ, i, j)) := rfl

def evalGL (g : ι → GL (Fin N) A) : GLRing ι N →+* A :=
  IsLocalization.Away.lift (genDet ι N)
    (g := MvPolynomial.eval₂Hom (Int.castRingHom A) fun x => (g x.1).1 x.2.1 x.2.2) (by
      rw [eval₂_genDet fun τ => (g τ).1]
      exact IsUnit.prod_univ_iff.2 fun τ => (isUnit_iff_isUnit_det _).1 (g τ).isUnit)

theorem evalGL_X (g : ι → GL (Fin N) A) (x : ι × Fin N × Fin N) :
    evalGL g (algebraMap _ _ (MvPolynomial.X (R := ℤ) x)) = (g x.1).1 x.2.1 x.2.2 := by
  rw [evalGL, IsLocalization.Away.lift_eq, MvPolynomial.eval₂Hom_X']

theorem map_evalGL_univGL (g : ι → GL (Fin N) A) (τ : ι) :
    GeneralLinearGroup.map (evalGL g) (univGL ι N τ) = g τ := by
  ext i j
  rw [GeneralLinearGroup.map_apply, univGL_apply, evalGL_X]

theorem evalGL_map_univGL (ψ : GLRing ι N →+* A) :
    evalGL (fun τ => GeneralLinearGroup.map ψ (univGL ι N τ)) = ψ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (genDet ι N)) (MvPolynomial.ringHom_ext'
    (RingHom.ext_int _ _) fun x => ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply, evalGL_X, GeneralLinearGroup.map_apply, univGL_apply]

end Ring

def toZ (X : Scheme.{0}) : X ⟶ Sp ℤ := specZIsTerminal.from X

theorem toZ_ext {X : Scheme.{0}} (f g : X ⟶ Sp ℤ) : f = g := specZIsTerminal.hom_ext f g

theorem isProjOver_pi (κ : Type) [Finite κ] :
    ∀ (X : κ → Scheme.{0}) [HasProduct X], (∀ k, IsProjOver (toZ (X k))) → IsProjOver (toZ (∏ᶜ X)) := by
  induction κ using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro X _ h
    have := hasProduct_of_equiv_of_iso X (X ∘ e) e (fun _ => Iso.refl _)
    rw [toZ_ext (toZ _) ((Pi.reindex e X).inv ≫ toZ _)]
    exact isProjOver_comp_of_isClosedImmersion _ (ih _ fun k => h _)
  | h_empty =>
    intro X _ _
    have : IsIso (toZ (∏ᶜ X)) :=
      ⟨Pi.lift fun k => k.elim, Pi.hom_ext _ _ fun k => k.elim, toZ_ext _ _⟩
    rw [← Category.comp_id (toZ _)]
    exact isProjOver_comp_of_isClosedImmersion _ ArithBase.isArithVar_int.isProjOver
  | h_option ih =>
    intro X _ h
    have sq : IsPullback (Pi.π X none) (Pi.lift fun k => Pi.π X (some k)) (toZ _)
        (toZ (∏ᶜ fun k => X (some k))) := by
      refine ⟨⟨toZ_ext _ _⟩, ⟨PullbackCone.IsLimit.mk _
        (fun s => Pi.lift fun k => Option.rec s.fst (fun k => s.snd ≫ Pi.π _ k) k) (fun s => by simp)
        (fun s => Pi.hom_ext _ _ fun k => by simp) fun s m h₁ h₂ => Pi.hom_ext _ _ fun k => ?_⟩⟩
      cases k with
      | none => simpa using h₁
      | some k => simp [← h₂]
    rw [toZ_ext (toZ _) (Pi.π X none ≫ toZ _)]
    exact isProjOver_of_isPullback sq (h _) (ih _ fun k => h _)

section Part

variable {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1))
  {A B : Type} [CommRing A] [CommRing B]

abbrev Amb : Scheme.{0} := ∏ᶜ fun k => PSpace ℤ (plDim N (l k))

theorem isProjOver_amb : IsProjOver (toZ (Amb l)) :=
  isProjOver_pi κ _ fun _ => by
    rw [toZ_ext (toZ _) (PSpace.str ℤ _)]
    exact isProjOver_pspace_str ℤ _

omit [Fintype ι] in

def plPt (g : ι → GL (Fin N) A) : Sp A ⟶ Amb l :=
  Pi.lift fun k => pt (Int.castRingHom A) (plVec (g (a k)).1 (l k)) (span_plVec _ _)

omit [Fintype ι] in

@[reassoc] theorem plPt_π (g : ι → GL (Fin N) A) (k : κ) :
    plPt a l g ≫ Pi.π _ k = pt (Int.castRingHom A) (plVec (g (a k)).1 (l k)) (span_plVec _ _) :=
  Pi.lift_π _ _

omit [Fintype ι] in

@[reassoc] theorem spMap_plPt (ψ : A →+* B) (g : ι → GL (Fin N) A) :
    spMap ψ ≫ plPt a l g = plPt a l fun τ => GeneralLinearGroup.map ψ (g τ) :=
  Pi.hom_ext _ _ fun k => by
    rw [Category.assoc, plPt_π, plPt_π, spMap_pt]
    congr 1
    · exact RingHom.ext_int _ _
    · exact funext fun c => (minor_map ψ _ _ _).symm

instance : QuasiCompact (plPt a l (univGL ι N)) := quasiCompact_of_noetherianSpace_source _

def Part : Scheme.{0} := (plPt a l (univGL ι N)).image

def plEmb : Part a l ⟶ Amb l := (plPt a l (univGL ι N)).imageι

instance : IsClosedImmersion (plEmb a l) :=
  inferInstanceAs (IsClosedImmersion (plPt a l (univGL ι N)).imageι)

instance : IsIntegral (Part a l) := isIntegral_image _

def orbit : Sp (GLRing ι N) ⟶ Part a l := (plPt a l (univGL ι N)).toImage

instance : IsSchemeTheoreticallyDominant (orbit a l) := schemeDominant_toImage _

def flagPt (g : ι → GL (Fin N) A) : Sp A ⟶ Part a l := spMap (evalGL g) ≫ orbit a l

@[reassoc] theorem flagPt_plEmb (g : ι → GL (Fin N) A) : flagPt a l g ≫ plEmb a l = plPt a l g := by
  rw [flagPt, Category.assoc]
  erw [Scheme.Hom.toImage_imageι]
  simp only [spMap_plPt, map_evalGL_univGL]

@[reassoc] theorem spMap_flagPt (ψ : A →+* B) (g : ι → GL (Fin N) A) :
    spMap ψ ≫ flagPt a l g = flagPt a l fun τ => GeneralLinearGroup.map ψ (g τ) := by
  rw [← cancel_mono (plEmb a l), Category.assoc, flagPt_plEmb, flagPt_plEmb, spMap_plPt]

theorem flagPt_univGL : flagPt a l (univGL ι N) = orbit a l := by
  rw [← cancel_mono (plEmb a l), flagPt_plEmb]
  exact (Scheme.Hom.toImage_imageι _).symm

theorem flagPt_eq_iff (g h : ι → GL (Fin N) A) : flagPt a l g = flagPt a l h ↔
    ∀ k, ∃ u : Aˣ, ∀ I, minor (h (a k)).1 (l k) I = u * minor (g (a k)).1 (l k) I := by
  rw [← cancel_mono (plEmb a l), flagPt_plEmb, flagPt_plEmb]
  refine ⟨fun e k => ?_, fun e => Pi.hom_ext _ _ fun k => ?_⟩
  · have := congrArg (· ≫ Pi.π _ k) e
    simp only [plPt_π] at this
    obtain ⟨u, hu⟩ := (pt_eq_pt_iff _ _ _).1 this
    exact ⟨u, fun I => by simpa [Units.smul_def] using congrFun hu (rowsEquiv _ _ I)⟩
  · obtain ⟨u, hu⟩ := e k
    rw [plPt_π, plPt_π]
    exact (pt_eq_pt_iff _ _ _).2 ⟨u, funext fun c => hu _⟩

theorem flagPt_mul (g b : ι → GL (Fin N) A)
    (hb : ∀ k (i j : Fin N), (j : ℕ) < l k → (l k : ℕ) ≤ i → (b (a k)).1 i j = 0) :
    flagPt a l (g * b) = flagPt a l g := by
  refine ((flagPt_eq_iff a l _ _).2 fun k => ?_).symm
  have h (g : GL (Fin N) A) := minor_mul g.1 (b (a k)).1 (l k) (hb k)
  have hu : IsUnit ((b (a k)).1.submatrix (Fin.castLE (l k).is_le) (Fin.castLE (l k).is_le)).det := by
    refine Ideal.span_singleton_eq_top.1 (top_le_iff.1 ((span_plVec (b (a k)) (l k)).ge.trans ?_))
    refine Ideal.span_le.2 (Set.range_subset_iff.2 fun c => Ideal.mem_span_singleton.2 ?_)
    have := h 1 ((rowsEquiv _ _).symm c)
    rw [Units.val_one, one_mul] at this
    exact Dvd.intro_left _ this.symm
  exact ⟨hu.unit, fun I => (h _ I).trans (mul_comm _ _)⟩

abbrev str : Part a l ⟶ Sp ℤ := toZ _

theorem isProjOver_str : IsProjOver (str a l) := by
  rw [toZ_ext (str a l) (plEmb a l ≫ toZ _)]
  exact isProjOver_comp_of_isClosedImmersion _ (isProjOver_amb l)

theorem charZero : CharZero Γ(Part a l, ⊤) :=
  ((Scheme.ΓSpecIso (.of ℤ)).hom.hom.comp (flagPt (A := ℤ) a l 1).appTop.hom).charZero

theorem isArithVar_of_dim {D : ℕ} (h : topologicalKrullDim (Part a l) = (D + 1 : ℕ)) : IsArithVar (str a l) D :=
  ⟨inferInstance, inferInstance, inferInstance, isProjOver_str a l, (flat_int_iff_charZero _).2 (charZero a l), h⟩

def comap {ι' κ' : Type} [Fintype ι'] [Finite κ'] (a' : κ' → ι') (f : ι' → ι) (e : κ' → κ)
    (h : ∀ k, a (e k) = f (a' k)) : Part a l ⟶ Part a' (fun k => l (e k)) :=
  closureMap (plPt a l (univGL ι N)) (plPt a' (fun k => l (e k)) (univGL ι' N)) (spMap (evalGL (univGL ι N ∘ f)))
    (Pi.lift fun k => Pi.π _ (e k)) (Pi.hom_ext _ _ fun k => by
      simp only [spMap_plPt, map_evalGL_univGL, Category.assoc, Pi.lift_π, plPt_π, Function.comp_apply, h])

@[reassoc] theorem comap_plEmb_π {ι' κ' : Type} [Fintype ι'] [Finite κ'] (a' : κ' → ι') (f : ι' → ι) (e : κ' → κ)
    (h : ∀ k, a (e k) = f (a' k)) (k : κ') :
    comap a l a' f e h ≫ plEmb a' (fun k => l (e k)) ≫ Pi.π _ k = plEmb a l ≫ Pi.π _ (e k) := by
  have e₁ : comap a l a' f e h ≫ plEmb a' (fun k => l (e k)) = plEmb a l ≫ Pi.lift fun k => Pi.π _ (e k) :=
    closureMap_imageι _ _ _ _ _
  rw [reassoc_of% e₁, Pi.lift_π]

def detDual (k : κ) : HermLB (str a l) :=
  (hermitianTwistingSheaf ℤ (plDim N (l k))).pull (plEmb a l ≫ Pi.π _ k) (toZ_ext _ _)

def plSec (k : κ) (I : Rows N (l k)) : (detDual a l k).B.Sec :=
  secPull (coord ℤ _ (rowsEquiv N (l k) I)) (plEmb a l ≫ Pi.π _ k)

def frameIdx (k : κ) (I : Rows N (l k)) : (detDual a l k).B.ι := fun _ => rowsEquiv N (l k) I

def cxPt (σ : ℤ →+* ℂ) (g : ι → GL (Fin N) ℂ) : CxPts (str a l) σ := ⟨flagPt a l g, toZ_ext _ _⟩

theorem map_cxPt (σ : ℤ →+* ℂ) (g : ι → GL (Fin N) ℂ) (k : κ) :
    PtsOver.map (plEmb a l ≫ Pi.π _ k) (toZ_ext _ (str a l)) _ (cxPt a l σ g) =
      projPt σ ⟨plVec (g (a k)).1 (l k), span_plVec _ _⟩ := by
  obtain rfl := RingHom.ext_int σ (Int.castRingHom ℂ)
  exact Subtype.ext ((flagPt_plEmb_assoc a l g _).trans (plPt_π a l g k))

theorem detDual_φ (σ : ℤ →+* ℂ) (g : ι → GL (Fin N) ℂ) (k : κ) (I : Rows N (l k))
    (hI : minor (g (a k)).1 (l k) I ≠ 0) :
    ((detDual a l k).φ σ).φ (frameIdx a l k I) (cxPt a l σ g) =
      Real.log (volSq (g (a k)).1 (l k) / ‖minor (g (a k)).1 (l k) I‖ ^ 2) := by
  refine (Weight.pull_φ _ _ _ _ _).trans ?_
  rw [map_cxPt]
  refine (ProjAn.fubiniStudyWeight_projPoint ℤ σ _ _ (rowsEquiv N (l k) I) (by simpa using hI)).trans (congrArg _ ?_)
  rw [volSq, Finset.sum_div, ← (rowsEquiv N (l k)).sum_comp]
  simp [div_pow]

theorem iSup_nonzeroLocus_plSec (k : κ) : ⨆ I, nonzeroLocus (plSec a l k I) = ⊤ := by
  have e (I) : nonzeroLocus (plSec a l k I) =
      (plEmb a l ≫ Pi.π _ k) ⁻¹ᵁ nonzeroLocus (coord ℤ _ (rowsEquiv N (l k) I)) := nonzeroLocus_secPull _ _
  simp only [e]
  rw [← Scheme.Hom.preimage_iSup, (rowsEquiv N (l k)).iSup_comp (g := fun c => nonzeroLocus (coord ℤ _ c)),
    iSup_nonzeroLocus_coord]
  rfl

theorem sum_nsq_plSec (σ : ℤ →+* ℂ) (k : κ) (y : CxPts (str a l) σ) :
    ∑ I, ((detDual a l k).φ σ).nsq (secVal _ σ (plSec a l k I)) y = 1 := by
  have e (c) : Weight.combVal (PSpace.str ℤ (plDim N (l k))) σ (coord ℤ _) 1 c = secVal _ σ (coord ℤ _ c) := by
    simp [Weight.combVal, Matrix.one_apply]
  refine Eq.trans ?_ (Weight.sum_nsq_fs (hB := O1_isLB ℤ _) (he := fun c => e c ▸ secVal_mem _)
    (h := Weight.noCommonZero_combVal (iSup_nonzeroLocus_coord ℤ _) (M := 1) (by simp))
    (PtsOver.map (plEmb a l ≫ Pi.π _ k) (toZ_ext _ (str a l)) _ y))
  rw [← (rowsEquiv N (l k)).sum_comp]
  exact Finset.sum_congr rfl fun I _ => (Weight.nsq_pull_secPull _ _ _ _ _).trans
    (congrArg (Weight.nsq _ · _) (e _).symm)

theorem plSec_mem_smallSec (k : κ) (I : Rows N (l k)) : plSec a l k I ∈ (detDual a l k).smallSec :=
  fun σ y => le_of_le_of_eq (Finset.single_le_sum
    (f := fun I => ((detDual a l k).φ σ).nsq (secVal _ σ (plSec a l k I)) y)
    (fun _ _ => Weight.nsq_nonneg _ _ y) (Finset.mem_univ I)) (sum_nsq_plSec a l σ k y)

theorem semiPos_detDual (k : κ) (D : ℕ) : (detDual a l k).SemiPos D := fun σ i c y hy ξ => by
  have hb : ⨆ I, nonzeroLocus (plSec a l k I) = ⊤ := iSup_nonzeroLocus_plSec a l k
  have h := Weight.semiPosReg_fsBasis (p := str a l) (σ := σ) (D := D) (detDual a l k).isLB (plSec a l k) hb 1
    (by simp) i c y hy ξ
  refine h.trans_eq (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ _))
  filter_upwards [(ChartGlue.isOpen_over c.e (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over c.e hy.1 hy.2)] with v hv
  refine congrArg _ ((Weight.fsBasis_φ _ _ _ _ _ _ _).trans (Eq.trans ?_
    ((Weight.pull_φ _ _ _ _ _).trans (Weight.fsBasis_φ _ _ (iSup_nonzeroLocus_coord ℤ _) 1 (by simp) _ _)).symm))
  rw [← (rowsEquiv N (l k)).sum_comp]
  refine congrArg _ (Finset.sum_congr rfl fun I _ => ?_)
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact congrArg (‖·‖ ^ 2) (valR_appLE (c.e.symm v).1 _ _ hv.2 _)

end Part

section Cell

variable {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1)) {A : Type} [CommRing A]

def Below (τ : ι) (i j : Fin N) : Prop := ∃ k, a k = τ ∧ (j : ℕ) < l k ∧ (l k : ℕ) ≤ i

abbrev CellVar : Type := {x : ι × Fin N × Fin N // Below a l x.1 x.2.1 x.2.2}

abbrev CellRing : Type := MvPolynomial (CellVar a l) ℤ

open Classical in

def lowMat (τ : ι) : Matrix (Fin N) (Fin N) (CellRing a l) :=
  Matrix.of fun i j => if h : Below a l τ i j then MvPolynomial.X ⟨(τ, i, j), h⟩ else (1 : Matrix _ _ _) i j

omit [Fintype ι] [Finite κ] in

theorem det_lowMat (τ : ι) : (lowMat a l τ).det = 1 := by
  have h {i j : Fin N} (hij : i ≤ j) : lowMat a l τ i j = (1 : Matrix _ _ _) i j :=
    dif_neg fun ⟨_, _, h₁, h₂⟩ => (h₁.trans_le h₂).not_ge hij
  have ht : (lowMat a l τ).BlockTriangular OrderDual.toDual := fun i j hij =>
    (h (le_of_lt (show i < j from hij))).trans (one_apply_ne (ne_of_lt (show i < j from hij)))
  rw [det_of_lowerTriangular _ ht]
  simp [h le_rfl]

def cellGL (w : ι → Equiv.Perm (Fin N)) (τ : ι) : GL (Fin N) (CellRing a l) :=
  GeneralLinearGroup.mk'' ((lowMat a l τ).submatrix (w τ) id) (by
    rw [det_permute, det_lowMat, mul_one]
    exact (Equiv.Perm.sign (w τ)).isUnit.map (Int.castRingHom _))

def cell (w : ι → Equiv.Perm (Fin N)) : Sp (CellRing a l) ⟶ Part a l := flagPt a l (cellGL a l w)

theorem flagPt_eq_comp_cell (w : ι → Equiv.Perm (Fin N)) (L b : ι → GL (Fin N) A)
    (hL : ∀ τ i j, ¬ Below a l τ (w τ i) j → (L τ).1 i j = (1 : Matrix _ _ A) (w τ i) j)
    (hb : ∀ τ i j, Below a l τ i j → (b τ).1 i j = 0) :
    flagPt a l (L * b) = spMap (MvPolynomial.eval₂Hom (Int.castRingHom A)
      fun x : CellVar a l => (L x.1.1).1 ((w x.1.1).symm x.1.2.1) x.1.2.2) ≫ cell a l w := by
  rw [flagPt_mul a l L b fun k i j h₁ h₂ => hb _ i j ⟨k, rfl, h₁, h₂⟩, cell, spMap_flagPt]
  congr 1
  ext τ i j
  rw [GeneralLinearGroup.map_apply]
  change _ = MvPolynomial.eval₂Hom _ _ (lowMat a l τ (w τ i) j)
  by_cases h : Below a l τ (w τ i) j
  · simp [lowMat, h]
  · by_cases e : w τ i = j
    · subst e
      simp [lowMat, h, hL τ i _ h]
    · simp [lowMat, h, hL τ i j h, e]

end Cell

section Full

open GlobalTheory.FlagPoly GlobalTheory.ArInt Formalism.DegreeFormula

variable (ι : Type) [Fintype ι] (N : ℕ)

abbrev Fl : Scheme.{0} := Part (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd

abbrev flStr : Fl ι N ⟶ Sp ℤ := str _ _

abbrev Gr (j : Fin (N + 1)) : Scheme.{0} := Part (id : ι → ι) fun _ => j

def toGr (j : Fin (N + 1)) : Fl ι N ⟶ Gr ι N j :=
  comap Prod.fst Prod.snd id id (fun τ => (τ, j)) fun _ => rfl

variable {ι N}

abbrev FlOmit (x : ι × Fin (N + 1)) : Scheme.{0} :=
  Part (fun y : {y // y ≠ x} => y.1.1) fun y => y.1.2

def forget (x : ι × Fin (N + 1)) : Fl ι N ⟶ FlOmit x :=
  comap Prod.fst Prod.snd _ id Subtype.val fun _ => rfl

def permute (s : ι → ι) : Fl ι N ⟶ Fl ι N :=
  comap Prod.fst Prod.snd Prod.fst s (fun x => (s x.1, x.2)) fun _ => rfl

abbrev flDet (τ : ι) (l : Fin (N + 1)) : HermLB (flStr ι N) := detDual Prod.fst Prod.snd (τ, l)

def grLine (x : ι × Fin N) : HermLB (flStr ι N) :=
  (flDet x.1 x.2.castSucc).tens (flDet x.1 x.2.succ).dual

def grIdx (x : ι × Fin N) (I : Rows N x.2.castSucc) (J : Rows N x.2.succ) : (grLine x).B.ι :=
  (frameIdx Prod.fst Prod.snd (x.1, x.2.castSucc) I, frameIdx Prod.fst Prod.snd (x.1, x.2.succ) J)

theorem flagPt_mul_upper {A : Type} [CommRing A] (g b : ι → GL (Fin N) A)
    (hb : ∀ τ, (b τ).1.BlockTriangular id) :
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (g * b) = flagPt Prod.fst Prod.snd g :=
  flagPt_mul _ _ g b fun k _ _ h₁ h₂ => hb k.1 (h₁.trans_le h₂)

variable (ι N)

def IsHh (Φ : Pol ι N →ₗ[ℝ] ℝ) : Prop := IsArFun (grLine (ι := ι) (N := N)) (dimFl ι N) Φ

def HasHh : Prop := ∃ Φ, IsHh ι N Φ

variable {ι N}

def hh (h : HasHh ι N) : Pol ι N →ₗ[ℝ] ℝ := h.choose

theorem isHh_hh (h : HasHh ι N) : IsHh ι N (hh h) := h.choose_spec

theorem IsHh.eq_hh {E : ℕ} (hd : topologicalKrullDim (Fl ι N) = (E + 1 : ℕ)) {Φ : Pol ι N →ₗ[ℝ] ℝ}
    (hΦ : IsHh ι N Φ) : Φ = hh ⟨Φ, hΦ⟩ :=
  Model.isArFun_unique (isArithVar_of_dim _ _ hd) hΦ (isHh_hh _)

def hFl (h : HasHh ι N) (lam : ι → Fin N → ℝ) : ℝ := hh h (linRoot lam ^ (dimFl ι N + 1))

def wtLine (lam : ι → Fin N → ℤ) : HermLB (flStr ι N) := comb grLine fun x => -lam x.1 x.2

theorem IsHh.isSelfInter {Φ : Pol ι N →ₗ[ℝ] ℝ} (hΦ : IsHh ι N Φ) (lam : ι → Fin N → ℤ) :
    (wtLine lam).IsSelfInter (Φ (linRoot (fun τ i => (lam τ i : ℝ)) ^ (dimFl ι N + 1))) := by
  have e : linRoot (fun τ i => (lam τ i : ℝ)) = lin fun x : ι × Fin N => ((-lam x.1 x.2 : ℤ) : ℝ) := by
    simp [linRoot, lin]
  rw [e]
  exact hΦ.1 _

theorem IsHh.eq_zero {Φ : Pol ι N →ₗ[ℝ] ℝ} (hΦ : IsHh ι N Φ) {F : Pol ι N} {d : ℕ} (hd : d ≠ dimFl ι N + 1)
    (hF : F.IsHomogeneous d) : Φ F = 0 := hΦ.2 F d hd hF

end Full

def swapTwo : GL (Fin 2) ℤ := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by decide, by decide⟩

example : flagPt (Prod.fst : Unit × Fin 3 → Unit) Prod.snd (fun _ => swapTwo) ≠ flagPt Prod.fst Prod.snd 1 := fun h => by
  obtain ⟨u, hu⟩ := (flagPt_eq_iff _ _ _ _).1 h ((), 1)
  have := hu ⟨{0}, rfl⟩
  have e : subsetEnum (⟨{0}, rfl⟩ : Set.powersetCard (Fin 2) 1) = fun _ => 0 :=
    funext fun i => Finset.orderEmbOfFin_singleton _ _
  change (Matrix.submatrix (1 : Matrix (Fin 2) (Fin 2) ℤ) (subsetEnum (⟨{0}, rfl⟩ : Set.powersetCard (Fin 2) 1)) (Fin.castLE _)).det =
    u * (Matrix.submatrix !![0, 1; 1, 0] (subsetEnum (⟨{0}, rfl⟩ : Set.powersetCard (Fin 2) 1)) (Fin.castLE _)).det at this
  simp [e, Matrix.one_apply, Fin.ext_iff] at this

example {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (h : gᴴ * g = 1) (l : Fin (N + 1)) : volSq g l = 1 :=
  (volSq_of_orthogonal (d := fun _ => 1) (by simpa using h) l).trans (by simp)

example : Formalism.DegreeFormula.dimFl Unit 2 = 1 ∧ plDim 2 1 = 1 ∧ plDim 2 0 = 0 ∧ plDim 2 2 = 0 := by decide

end GlobalTheory.FlagZ
