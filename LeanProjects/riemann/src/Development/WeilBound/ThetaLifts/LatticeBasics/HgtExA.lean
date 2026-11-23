import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtArch
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasAd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSiegelHProjArchEq

noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped Matrix TensorProduct NNReal
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl GlobalTheory.WeilM
open GlobalTheory.CompanionTheory.IwaDbl.FrameCore
open Formalism.UG (cT bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

variable (F) in

def eF : AF F := LinearMap.inr F (Ainf F) (Af F) 1

omit [NumberField E] in
theorem smul_incl (a : AF F) (x : E) : a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := by
  change (a * 1) ⊗ₜ[F] x = _
  rw [mul_one]

theorem mem_latHat (hL : Y.L.FG) (z : Fin n → AE F E) :
    z ∈ latHat Y ↔ eF F • z = z ∧ ∀ v, compFin F E v ∘ z ∈ latLoc F Y.L v := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      refine ⟨?_, fun v => ?_⟩
      · have : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 ha
        rw [smul_smul]
        congr 1
        exact Prod.ext ((zero_mul _).trans this.symm) (one_mul _)
      · convert tmul_mem_latLoc (ha' v) hx using 1
        exact funext fun i => congrArg (compFin F E v) (smul_incl a (x i))
    | zero => exact ⟨smul_zero _, fun v => by
        convert zero_mem (latLoc F Y.L v) using 1
        exact funext fun i => map_zero _⟩
    | add y z _ _ hy hz => exact ⟨by rw [smul_add, hy.1, hz.1], fun v => by
        convert add_mem (hy.2 v) (hz.2 v) using 1
        exact funext fun i => map_add _ _ _⟩
    | neg y _ hy => exact ⟨by rw [smul_neg, hy.1], fun v => by
        convert neg_mem (hy.2 v) using 1
        exact funext fun i => map_neg _ _⟩
  · rintro ⟨h1, h2⟩
    let π := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
    let ι : Af F ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id
    have e1 : ∀ y, ι (π y) = eF F • y := fun y => by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]
      | tmul a x => exact congrArg (· ⊗ₜ[F] x) (Prod.ext (zero_mul _).symm (one_mul _).symm)
    have e2 : ∀ v y, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (π y) = compFin F E v y := fun v y => by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => rfl
    have e3 : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Y.L : Set (Fin n → E)), ι ∘ y ∈ latHat Y := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨LinearMap.inr F (Ainf F) (Af F) a, map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F),
          ha, x, hx, funext fun i => (smul_incl _ _).symm⟩
      | zero =>
        convert zero_mem (latHat Y) using 1
        exact funext fun i => map_zero _
      | add y z _ _ hy hz =>
        convert add_mem hy hz using 1
        exact funext fun i => map_add _ _ _
      | neg y _ hy =>
        convert neg_mem hy using 1
        exact funext fun i => map_neg _ _
    convert e3 (π ∘ z) ((mem_latHat_iff hL _).2 fun v => by
      convert h2 v using 1
      exact funext fun i => e2 v _) using 1
    exact funext fun i => (congrFun h1 i).symm.trans (e1 _).symm

omit [NumberField E] in
theorem cA_eq : ⇑(cA (F := F) σ) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ := funext fun z => by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

omit [NumberField E] in
theorem mem_HR {ξ : E} (hξ : ξ ≠ 0) (x : GL (Fin (n + n)) (AE F E)) :
    x ∈ HR (AF F) σ (dblGram finSumFinEquiv (ξ • Y.Jᵀ)) ↔ reGL finSumFinEquiv.symm x ∈ UG (cA σ) (dbl (incM F Y.J)) := by
  have e : (JR (F := F) (AF F) (ξ • Y.Jᵀ))ᵀ = inclR (F := F) (AF F) ξ • incM F Y.J :=
    Matrix.ext fun i j => map_mul (inclR (F := F) (AF F)) _ _
  change cT _ x.1 * JR _ _ * x.1 = JR _ _ ↔ (x.1.submatrix _ _)ᵀ * _ * (x.1.submatrix _ _).map _ = _
  rw [JR_dblGram, iso_iff, e, dbl_smul, Matrix.mul_smul, Matrix.smul_mul, (hξ.isUnit.map _).smul_left_cancel, cA_eq]
  rfl

variable (σ Y) in

def back {ξ : E} (hξ : ξ ≠ 0) : GAd σ (dblGram finSumFinEquiv (ξ • Y.Jᵀ)) →* G2 σ Y :=
  MonoidHom.mk' (fun g => ⟨reGL finSumFinEquiv.symm (matHom _ σ _ g), (mem_HR hξ _).1 g.2⟩) fun _ _ =>
    Subtype.ext (Units.ext (Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _).symm)

omit [NumberField E] in
theorem back_surj {ξ : E} (hξ : ξ ≠ 0) : Function.Surjective (back σ Y hξ) := fun x => by
  have e : reGL finSumFinEquiv.symm (reGL finSumFinEquiv x.1) = x.1 := Units.ext (by simp [reGL])
  exact ⟨⟨reGL finSumFinEquiv x.1, (mem_HR hξ _).2 (e.symm ▸ x.2)⟩, Subtype.ext e⟩

def Keeps (k : G2 σ Y) : Prop := ∀ z z', z ∈ latHat Y → z' ∈ latHat Y →
  (mat2 k *ᵥ Sum.elim z z') ∘ Sum.inl ∈ latHat Y ∧ (mat2 k *ᵥ Sum.elim z z') ∘ Sum.inr ∈ latHat Y

theorem keeps_back (hL : Y.L.FG) {ξ : E} (hξ : ξ ≠ 0) {k : GAd σ (dblGram finSumFinEquiv (ξ • Y.Jᵀ))}
    (hk : ∀ v, proj σ _ v k ∈ GlobalTheory.Doubling.KFin σ _ Y.L v) : Keeps (back σ Y hξ k) := fun z z' hz hz' => by
  rw [mem_latHat hL] at hz hz' ⊢
  rw [mem_latHat hL]
  have e0 : eF F • (mat2 (back σ Y hξ k) *ᵥ Sum.elim z z') = mat2 (back σ Y hξ k) *ᵥ Sum.elim z z' := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    rcases i with i | i
    exacts [congrFun hz.1 i, congrFun hz'.1 i]
  have e1 : mat2 (back σ Y hξ k) *ᵥ Sum.elim z z' = ((matHom _ σ _ k).1 *ᵥ pairVec finSumFinEquiv z z') ∘ finSumFinEquiv :=
    Matrix.submatrix_mulVec_equiv _ _ _ finSumFinEquiv
  have e2 : ∀ v, compFin F E v ∘ ((matHom _ σ _ k).1 *ᵥ pairVec finSumFinEquiv z z') ∈
      sumLat finSumFinEquiv (latLoc F Y.L v) (latLoc F Y.L v) := fun v => by
    have := (mem_stabLoc.1 (hk v) (compFin F E v ∘ pairVec finSumFinEquiv z z')).1 (by
      rw [latLoc_sumLat, mem_sumLat]
      simp only [Function.comp_apply, pairVec_inl, pairVec_inr]
      exact ⟨hz.2 v, hz'.2 v⟩)
    rw [latLoc_sumLat] at this
    convert this using 1
    exact funext fun i => RingHom.map_mulVec _ _ _ i
  refine ⟨⟨funext fun i => congrFun e0 _, fun v => ?_⟩, funext fun i => congrFun e0 _, fun v => ?_⟩ <;> rw [e1]
  exacts [(e2 v).1, (e2 v).2]

variable (σ Y) in

def stab2 (B : Base F E) : Subgroup (G2 σ Y) where
  carrier := {k | (∀ w, Commute ((mat2 k).map (piInf (B.emb w))) (Matrix.fromBlocks (Y.θ w) 0 0 (-Y.θ w))) ∧ Keeps k ∧ Keeps k⁻¹}
  one_mem' := by
    have : Keeps (1 : G2 σ Y) := fun z z' hz hz' => by
      rw [show mat2 (1 : G2 σ Y) = 1 from rfl, Matrix.one_mulVec]; exact ⟨hz, hz'⟩
    refine ⟨fun w => ?_, this, by rwa [inv_one]⟩
    rw [show mat2 (1 : G2 σ Y) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _
  mul_mem' := by
    have : ∀ {a b : G2 σ Y}, Keeps a → Keeps b → Keeps (a * b) := fun {a b} ha hb z z' hz hz' => by
      have := ha _ _ (hb z z' hz hz').1 (hb z z' hz hz').2
      rwa [Sum.elim_comp_inl_inr, Matrix.mulVec_mulVec] at this
    intro a b ha hb
    refine ⟨fun w => ?_, this ha.2.1 hb.2.1, by rw [mul_inv_rev]; exact this hb.2.2 ha.2.2⟩
    rw [show mat2 (a * b) = mat2 a * mat2 b from rfl, Matrix.map_mul]
    exact (ha.1 w).mul_left (hb.1 w)
  inv_mem' := fun {a} ha => ⟨fun w => Commute.units_inv_left (u := bc (piInf (B.emb w)) a.1) (ha.1 w), ha.2.2,
    by rw [inv_inv]; exact ha.2.1⟩

omit [NumberField E] in
theorem isStab2_stab2 (B : Base F E) : IsStab2 B (stab2 σ Y B) := fun k =>
  and_congr Iff.rfl ⟨fun h z z' hz hz' k' hk' => by
    rcases hk' with rfl | rfl
    exacts [h.1 z z' hz hz', h.2 z z' hz hz'],
    fun h => ⟨fun z z' hz hz' => h z z' hz hz' _ (.inl rfl), fun z z' hz hz' => h z z' hz hz' _ (.inr rfl)⟩⟩

theorem isUnit_of_cartan {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : IsUnit M := by
  refine Matrix.mulVec_injective_iff_isUnit.1 ((injective_iff_map_eq_zero M.mulVecLin).2 fun y hy => by_contra fun h0 => ?_)
  have := h.2.2 (star y) (by simpa using h0)
  rw [star_star, show M *ᵥ y = 0 from hy] at this
  simp at this

theorem exists_scal {B : Base F E} (hB : B.IsGood σ) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) :
    ∃ ξ : E, ξ ≠ 0 ∧ (∀ i j, σ ((ξ • Y.Jᵀ) j i) = (ξ • Y.Jᵀ) i j) ∧ ∀ w, ∃ (M : Matrix (Fin n) (Fin n) ℂ) (r : ℝ), Mᴴ = M ∧
      IsCartan M (Y.θ w) ∧ r ≠ 0 ∧ (ξ • Y.Jᵀ).map (B.emb w).1 = (r : ℂ) • Mᵀ := by
  have hc := hB.cm
  rcases hY with h | h
  · refine ⟨1, one_ne_zero, fun i j => by simpa using h.herm j i, fun w => ⟨_, 1, ?_, h.cartan w, one_ne_zero, ?_⟩⟩
    · exact Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))
    · ext i j; simp
  · obtain ⟨x, hx⟩ : ∃ x, x - σ x ≠ 0 := by
      by_contra! e
      have := hc.2.1
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
        (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
          (hc.2.2.2 τ y).symm.trans (congrArg τ (sub_eq_zero.1 (e y)).symm))))
    have hs : σ (x - σ x) = -(x - σ x) := by rw [map_sub, cm_conj_conj hc, neg_sub]
    refine ⟨_, hx, fun i j => ?_, fun w => ?_⟩
    · change σ (_ * Y.J i j) = _ * Y.J j i
      rw [map_mul, hs, h.skew, neg_mul_neg]
    · have h1 := hc.2.2.2 (B.emb w).1 (x - σ x)
      rw [hs, map_neg] at h1
      have h2 : (B.emb w).1 (x - σ x) = ((B.emb w).1 (x - σ x)).im * Complex.I := by
        have := congrArg Complex.re h1
        simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
        exact Complex.ext (by simp only [Complex.mul_I_re, Complex.ofReal_im]; linarith) (by simp)
      refine ⟨_, ((B.emb w).1 (x - σ x)).im, Matrix.ext fun i j => ?_, h.cartan w, fun e => hx ?_, Matrix.ext fun i j => ?_⟩
      · change star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)
        rw [star_mul', ← hc.2.2.2, h.skew]; simp
      · rw [e] at h2
        exact (map_eq_zero _).1 (h2.trans (by simp))
      · change (B.emb w).1 (_ * Y.J j i) = _ * (Complex.I * (B.emb w).1 (Y.J j i))
        rw [map_mul, ← mul_assoc, ← h2]

theorem det_ne {B : Base F E} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) : Y.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have e : (Y.J.map (B.emb w).1).det = 0 := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  rcases hY with h | h
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_cartan (h.cartan w))).ne_zero e
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_cartan (h.cartan w))).ne_zero (by rw [Matrix.det_smul, e, mul_zero])

theorem par_iff {S β : Type} [CommRing S] [Fintype β] [DecidableEq β] (M : Matrix (β ⊕ β) (β ⊕ β) S) (t : Matrix β β S) :
    M * diagCols (E := S) β = diagCols (E := S) β * t ↔ KeepsDiag (Equiv.refl _) M ∧ leviMat (Equiv.refl _) M = t := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M, diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.fromRows_ext_iff]
  exact ⟨fun h => ⟨h.2.trans h.1.symm, h.1⟩, fun h => ⟨h.2, h.1.trans h.2⟩⟩

omit [NumberField E] in
theorem isPar_iff {p : G2 σ Y} {t : GL (Fin n) (AE F E)} :
    IsPar p t ↔ KeepsDiag (Equiv.refl _) (mat2 p) ∧ leviMat (Equiv.refl _) (mat2 p) = t := par_iff (mat2 p) t.1

omit [NumberField E] in
theorem back_mem_par {ξ : E} (hξ : ξ ≠ 0) {p : GAd σ (dblGram finSumFinEquiv (ξ • Y.Jᵀ))} (hp : p ∈ siegelH (AF F) σ _) :
    back σ Y hξ p ∈ siegelOf (Equiv.refl (Fin n ⊕ Fin n)) (UG (cA σ) (dbl (incM F Y.J))).subtype := by
  have h : ∀ M : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E), KeepsDiag finSumFinEquiv M →
    KeepsDiag (Equiv.refl _) (M.submatrix finSumFinEquiv finSumFinEquiv) := fun _ h => h
  rw [mem_siegelOf] at hp ⊢
  exact h _ hp

omit [NumberField E] in
theorem back_comm {ξ : E} (hξ : ξ ≠ 0) {k : GAd σ (dblGram finSumFinEquiv (ξ • Y.Jᵀ))} {w : InfinitePlace F} (τ : EmbOver E w)
    {θ : Matrix (Fin n) (Fin n) ℂ} (h : Commute ((matHom _ σ _ (projArch σ _ w k)).1.map (infEmb τ)) (blkMat finSumFinEquiv θ (-θ))) :
    Commute ((mat2 (back σ Y hξ k)).map (piInf τ)) (Matrix.fromBlocks θ 0 0 (-θ)) := by
  have e : (mat2 (back σ Y hξ k)).map (piInf τ) =
    ((matHom _ σ _ (projArch σ _ w k)).1.map (infEmb τ)).submatrix finSumFinEquiv finSumFinEquiv := Matrix.ext fun _ _ => rfl
  rw [e, ← submatrix_blkMat finSumFinEquiv, Commute, SemiconjBy, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h.eq]

theorem iwasawa2 {B : Base F E} (hB : B.IsGood σ) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (x : G2 σ Y) :
    ∃ p : siegelOf (Equiv.refl (Fin n ⊕ Fin n)) (UG (cA σ) (dbl (incM F Y.J))).subtype, ∃ k ∈ stab2 σ Y B, x = p * k := by
  have hL : Y.L.IsLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨ξ, hξ, hh, hw⟩ := exists_scal hB hY
  choose M r h1 h2 h3 h4 using hw
  choose b hb hb' using fun w => exists_arch hB.cm (B.emb w) (h1 w) (isUnit_of_cartan (h2 w)) (h2 w) (h3 w) (h4 w)
  obtain ⟨a, -, ha⟩ := Frames.exists_isLatticeFrame_of_arch Y.L b
  obtain rfl : b = fun w => bc (compInf F E w) a := (funext ha).symm
  obtain ⟨g, rfl⟩ := back_surj hξ x
  obtain ⟨p, k, hk, rfl⟩ := HasIwasawa.adelic (a := a) (hasIwasawa_fin' hB hY (det_ne hY) hξ hh) hb g
  have k2 := keeps_back hL.fg hξ (mem_KAd.1 (inv_mem hk)).1
  rw [map_inv] at k2
  exact ⟨⟨_, back_mem_par hξ p.2⟩, back σ Y hξ k, ⟨fun w => back_comm hξ _ ((hb' w _).1 ((mem_KAd.1 hk).2 w)),
    keeps_back hL.fg hξ (mem_KAd.1 hk).1, k2⟩, map_mul _ _ _⟩

variable (σ Y) in

def emb2 : UA σ Y.J × UA σ Y.J →* G2 σ Y :=
  ((blkGL (Equiv.refl (Fin n ⊕ Fin n))).comp ((Subgroup.subtype _).prodMap (Subgroup.subtype _))).codRestrict _ fun x => by
    change (Matrix.fromBlocks (mat x.1) 0 0 (mat x.2))ᵀ * _ * (Matrix.fromBlocks (mat x.1) 0 0 (mat x.2)).map _ = _
    have h1 : (mat x.1)ᵀ * incM F Y.J * (mat x.1).map (cA σ) = incM F Y.J := x.1.2
    have h2 : (mat x.2)ᵀ * incM F Y.J * (mat x.2).map (cA σ) = incM F Y.J := x.2.2
    simp [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, h1, h2]

theorem hgtEx_core {B : Base F E} (hB : B.IsGood σ) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hK : IsCompact (stab2 σ Y B : Set (G2 σ Y))) :
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h')) := by
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hI := iwasawaOf_of_isCompact (ν := absE F E) continuous_subtype_val continuous_absE hK (iwasawa2 hB hY)
  refine ⟨⟨_, fun x => hgtOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype (absE F E) (stab2 σ Y B) x, isStab2_stab2 B,
    ⟨fun x => ?_, fun p t hp k hk => ?_⟩,
    NNReal.continuous_coe.comp (hI.continuous_hgtOf continuous_subtype_val continuous_absE hK), fun x => hgtOf_pos x⟩,
    emb2 σ Y, ((continuous_blkGL _).comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _, fun _ _ => rfl⟩
  · obtain ⟨p, h⟩ := iwasawa2 hB hY x
    exact ⟨p, leviOf _ _ p, isPar_iff.2 ⟨mem_siegelOf.1 p.2, rfl⟩, h⟩
  · obtain ⟨h1, h2⟩ := isPar_iff.1 hp
    have := hI.hgtOf_mul ⟨p, mem_siegelOf.2 h1⟩ hk
    rw [show t = leviOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype ⟨p, mem_siegelOf.2 h1⟩ from Units.ext h2.symm]
    exact congrArg NNReal.toReal this

end GlobalTheory.ThK.Dbl.Hgt

end
