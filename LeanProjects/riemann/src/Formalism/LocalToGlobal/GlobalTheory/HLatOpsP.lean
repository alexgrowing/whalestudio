import Formalism.LocalToGlobal.GlobalTheory.HLatOps
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Formalism.LocalRingCardinality.DataDIVDefs

open Module NumberField ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.HLatOps

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory

section Basic

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem cnorm_sq (u : ι → ℂ) : cnorm u ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  unfold cnorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem cnorm_nonneg (u : ι → ℂ) : 0 ≤ cnorm u := by
  unfold cnorm
  exact Real.sqrt_nonneg _

theorem cnorm_eq_zero {u : ι → ℂ} (h : cnorm u = 0) : u = 0 := by
  unfold cnorm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h
  funext i
  have hi := h i (Finset.mem_univ i)
  simpa using hi

theorem normAt_eq_zero (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (hX : IsUnit (X v).det) {x : V} (h : normAt b X v x = 0) : x = 0 := by
  have h1 : (X v)⁻¹.mulVec (vecAt b v x) = 0 := cnorm_eq_zero h
  have h2 : vecAt b v x = 0 := by
    have h3 : (X v).mulVec ((X v)⁻¹.mulVec (vecAt b v x)) = 0 := by
      rw [h1, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec] at h3
  apply b.repr.injective
  ext i
  have h4 := congrFun h2 i
  simp only [vecAt, Pi.zero_apply, map_eq_zero] at h4
  simpa using h4

theorem majAt_self (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : majAt b X v x x = ((normAt b X v x ^ 2 : ℝ) : ℂ) := by
  show (∑ i, star (fcoord b X v x i) * fcoord b X v x i) =
    (((cnorm (fcoord b X v x)) ^ 2 : ℝ) : ℂ)
  rw [cnorm_sq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem normAt_eq_sqrt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : normAt b X v x = Real.sqrt (majAt b X v x x).re := by
  rw [majAt_self, Complex.ofReal_re]
  exact (Real.sqrt_sq (cnorm_nonneg _)).symm

theorem isSesq_maj (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    IsSesq (fun v => majAt b X v) := by
  intro v
  have hadd : ∀ x y : V, fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
    intro x y
    have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
      funext i
      simp [vecAt]
    unfold fcoord
    rw [hv, Matrix.mulVec_add]
  have hsmul : ∀ (a : K) (x : V), fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
    intro a x
    have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
      funext i
      simp [vecAt]
    unfold fcoord
    rw [hv, Matrix.mulVec_smul]
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [majAt, hadd, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]
  · simp only [majAt, hadd, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [majAt, hsmul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    first
    | (rw [Complex.star_def]; ring)
    | (simp only [RCLike.star_def]; ring)
    | ring
  · simp only [majAt, hsmul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem sesq_eq_sum {H : InfinitePlace K → V → V → ℂ} (hH : IsSesq H) (b : Basis ι K V)
    (v : InfinitePlace K) (x y : V) :
    H v x y = ∑ i, ∑ j, starRingEnd ℂ (vecAt b v x i) * gramOf b (H v) i j * vecAt b v y j := by
  obtain ⟨h1, h2, h3, h4⟩ := hH v
  have hz1 : ∀ y, H v 0 y = 0 := by
    intro y
    have e := h1 0 0 y
    rw [add_zero] at e
    linear_combination (-1 : ℂ) * e
  have hz2 : ∀ x, H v x 0 = 0 := by
    intro x
    have e := h2 x 0 0
    rw [add_zero] at e
    linear_combination (-1 : ℂ) * e
  have hsumL : ∀ (s : Finset ι) (c : ι → K) (y : V),
      H v (∑ i ∈ s, c i • b i) y = ∑ i ∈ s, starRingEnd ℂ (v.embedding (c i)) * H v (b i) y := by
    intro s c y
    refine Finset.induction_on s ?_ ?_
    · simp [hz1]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, h3, ih]
  have hsumR : ∀ (s : Finset ι) (c : ι → K) (x : V),
      H v x (∑ i ∈ s, c i • b i) = ∑ i ∈ s, v.embedding (c i) * H v x (b i) := by
    intro s c x
    refine Finset.induction_on s ?_ ?_
    · simp [hz2]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, h2, h4, ih]
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [hsumL, hsumR, vecAt, gramOf, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramOf_maj (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) :
    gramOf b (majAt b X v) = ((X v)⁻¹).conjTranspose * (X v)⁻¹ := by
  have hv : ∀ i, vecAt b v (b i) = Pi.single i 1 := by
    intro i
    funext j
    simp only [vecAt]
    rw [b.repr_self]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Finsupp.single_apply, Pi.single_apply, hj, Ne.symm hj]
  have hf : ∀ i k, fcoord b X v (b i) k = (X v)⁻¹ k i := by
    intro i k
    simp [fcoord, hv, Matrix.mulVec, dotProduct, Pi.single_apply]
  ext i j
  simp [gramOf, majAt, hf, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem sesq_ext {F G : V → V → ℂ} {σ : K →+* ℂ} (hσ : ∃ a : K, (σ a).im ≠ 0)
    (hF : (∀ x x' y, F (x + x') y = F x y + F x' y) ∧ (∀ x y y', F x (y + y') = F x y + F x y') ∧
      (∀ (a : K) x y, F (a • x) y = starRingEnd ℂ (σ a) * F x y) ∧
      (∀ (a : K) x y, F x (a • y) = σ a * F x y))
    (hG : (∀ x x' y, G (x + x') y = G x y + G x' y) ∧ (∀ x y y', G x (y + y') = G x y + G x y') ∧
      (∀ (a : K) x y, G (a • x) y = starRingEnd ℂ (σ a) * G x y) ∧
      (∀ (a : K) x y, G x (a • y) = σ a * G x y))
    (h : ∀ x, F x x = G x x) (x y : V) : F x y = G x y := by
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  obtain ⟨hG1, hG2, hG3, hG4⟩ := hG
  have key : ∀ u w : V, F u w + F w u = G u w + G w u := by
    intro u w
    have h1 := h (u + w)
    rw [hF1, hF2, hF2, hG1, hG2, hG2] at h1
    linear_combination h1 - h u - h w
  have k1 := key x y
  have k2 := key x (a • y)
  rw [hF4, hF3, hG4, hG3] at k2
  have hne : σ a - starRingEnd ℂ (σ a) ≠ 0 := by
    intro h0
    apply ha
    have h5 := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h5
    linarith
  have hprod : (σ a - starRingEnd ℂ (σ a)) * (F x y - G x y) = 0 := by
    linear_combination k2 - (starRingEnd ℂ (σ a)) * k1
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.1 h0

theorem exists_im_ne_zero [IsTotallyComplex K] (v : InfinitePlace K) :
    ∃ a : K, (v.embedding a).im ≠ 0 := by
  have hc : v.IsComplex := IsTotallyComplex.isComplex v
  rw [InfinitePlace.isComplex_iff] at hc
  by_contra hcon
  push_neg at hcon
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hcon a)

end Basic

section IsoSec

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def Iso.refl (A : HLat K) : Iso A A where
  e := LinearEquiv.refl K A.V
  map_L := by
    ext x
    simp
  norm := fun _ _ => rfl

def Iso.symm {A B : HLat K} (I : Iso A B) : Iso B A where
  e := I.e.symm
  map_L := by
    rw [← I.map_L]
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨I.e x, ⟨x, hx, rfl⟩, by simp⟩
  norm := fun v x => by
    have := I.norm v (I.e.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm

def Iso.trans {A B C : HLat K} (I : Iso A B) (J : Iso B C) : Iso A C where
  e := I.e.trans J.e
  map_L := by
    rw [← J.map_L, ← I.map_L]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨I.e y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
  norm := fun v x => by
    show normAt C.b C.X v (J.e (I.e x)) = _
    rw [J.norm, I.norm]

variable {A B : HLat K}

theorem Iso.mem_L (I : Iso A B) {x : A.V} : I.e x ∈ B.L ↔ x ∈ A.L := by
  rw [← I.map_L]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := I.e.injective hxy
    exact hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem Iso.span_L (I : Iso A B) : Submodule.span K (B.L : Set B.V) =
    (Submodule.span K (A.L : Set A.V)).map I.e.toLinearMap := by
  rw [← I.map_L, Submodule.map_coe, ← Submodule.span_image]
  rfl

theorem Iso.rank_eq (I : Iso A B) : A.rank = B.rank := by
  unfold HLat.rank rkK
  rw [I.span_L]
  exact (LinearEquiv.finrank_map_eq I.e _).symm

theorem Iso.frameOK (I : Iso A B) (h : FrameOK A) : FrameOK B := by
  intro v
  by_contra hv
  have h0 : ∀ y : B.V, y = 0 := by
    intro y
    have hy : normAt A.b A.X v (I.e.symm y) = 0 := by
      rw [← I.norm, LinearEquiv.apply_symm_apply]
      show cnorm ((B.X v)⁻¹.mulVec (vecAt B.b v y)) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hv, Matrix.zero_mulVec]
      simp [cnorm]
    have hz := normAt_eq_zero A.b A.X v (h v) hy
    simpa using hz
  haveI hι : IsEmpty B.ι := ⟨fun i => B.b.ne_zero i (h0 _)⟩
  apply hv
  rw [Matrix.det_isEmpty]
  exact isUnit_one

theorem Iso.fg (I : Iso A B) (h : A.L.FG) : B.L.FG := by
  rw [← I.map_L]
  exact h.map _

theorem Iso.good (I : Iso A B) (h : A.Good) : B.Good := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨I.frameOK h1, I.fg h2, ?_⟩
  rw [I.span_L, h3, Submodule.map_top]
  exact I.e.range

theorem Iso.numbers (I : Iso A B) (hX : FrameOK A) (hL : A.L.FG) :
    A.mu = B.mu ∧ A.muMax = B.muMax ∧ A.muMin = B.muMin ∧ A.lcv = B.lcv := by
  obtain ⟨h1, -, h3, h4, h5, -, -⟩ := rerealize K A.V A.ι B.V B.ι A.b A.X B.b B.X I.e.toLinearMap hX
    (I.frameOK hX) I.e.injective I.norm A.L hL
  rw [I.map_L] at h1 h3 h4 h5
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold HLat.mu muDef; rw [h3]
  · unfold HLat.muMax muMaxDef; rw [h4]
  · unfold HLat.muMin muMinDef; rw [h5]
  · unfold HLat.lcv; rw [h1]

def Iso.withL (I : Iso A B) (L' : Submodule (𝓞 K) A.V) :
    Iso (withL A L') (HLatOps.withL B (L'.map (I.e.toLinearMap.restrictScalars (𝓞 K)))) where
  e := I.e
  map_L := rfl
  norm := I.norm

theorem frame_free : FrameFree := by
  intro K V ι κ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' hn L hL
  obtain ⟨h1, -, h3, h4, h5, -, -⟩ := rerealize K V ι V κ b X b' X' LinearMap.id hX hX'
    Function.injective_id (fun v x => (hn v x).symm) L hL
  have hid : L.map ((LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)) = L := by
    ext x
    simp
  rw [hid] at h1 h3 h4 h5
  refine ⟨h1.symm, ?_, ?_, ?_⟩
  · unfold muDef; rw [h3]
  · unfold muMaxDef; rw [h4]
  · unfold muMinDef; rw [h5]

theorem Iso.maj [IsTotallyComplex K] (I : Iso A B) (v : InfinitePlace K) (x y : A.V) :
    majAt B.b B.X v (I.e x) (I.e y) = majAt A.b A.X v x y := by
  obtain ⟨a, ha⟩ := exists_im_ne_zero v
  have hA := isSesq_maj A.b A.X v
  have hB := isSesq_maj B.b B.X v
  refine sesq_ext (F := fun x y => majAt B.b B.X v (I.e x) (I.e y)) (G := majAt A.b A.X v)
    (σ := v.embedding) ⟨a, ha⟩ ⟨?_, ?_, ?_, ?_⟩ hA ?_ x y
  · intro x x' y
    simp only [map_add]
    exact hB.1 _ _ _
  · intro x y y'
    simp only [map_add]
    exact hB.2.1 _ _ _
  · intro c x y
    simp only [map_smul]
    exact hB.2.2.1 _ _ _
  · intro c x y
    simp only [map_smul]
    exact hB.2.2.2 _ _ _
  · intro z
    show majAt B.b B.X v (I.e z) (I.e z) = majAt A.b A.X v z z
    rw [majAt_self, majAt_self, I.norm]

end IsoSec

section Forms

open scoped MatrixOrder in
theorem exists_frame {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) :
    ∃ B : Matrix ι ι ℂ, IsUnit B.det ∧ B.conjTranspose * B = G := by
  have hex : ∃ B : Matrix ι ι ℂ, G = B.conjTranspose * B := by
    first
    | exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.1 hG.posSemidef
    | (obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.1 hG.posSemidef
       exact ⟨B, hB⟩)
    | (have h0 : (0 : Matrix ι ι ℂ) ≤ G := Matrix.nonneg_iff_posSemidef.2 hG.posSemidef
       refine ⟨CFC.sqrt G, ?_⟩
       have hs : (CFC.sqrt G).conjTranspose = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint
       rw [hs]
       exact (CFC.sqrt_mul_sqrt_self G h0).symm)
  obtain ⟨B, hB⟩ := hex
  refine ⟨B, ?_, hB.symm⟩
  have hdet : G.det ≠ 0 := by
    first
    | exact hG.det_pos.ne'
    | exact hG.det_ne_zero
    | exact (Matrix.isUnit_iff_isUnit_det G).1 hG.isUnit |>.ne_zero
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hdet
  rw [hB, Matrix.det_mul, h0, mul_zero]

theorem frameOf_spec {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) :
    IsUnit (frameOf G).det ∧ ((frameOf G)⁻¹).conjTranspose * (frameOf G)⁻¹ = G := by
  have h := exists_frame hG
  have hspec := Classical.choose_spec h
  unfold frameOf
  rw [dif_pos h]
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hspec.1, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ hspec.1]
  exact hspec.2

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem of_form_spec : OfFormSpec := by
  unfold OfFormSpec
  intro K V ι _ _ _ _ _ _ _ _ _ b L H hH hP
  have hF : ∀ v, IsUnit (frameOf (gramOf b (H v))).det ∧
      ((frameOf (gramOf b (H v)))⁻¹).conjTranspose * (frameOf (gramOf b (H v)))⁻¹ =
        gramOf b (H v) := fun v => frameOf_spec (hP v)
  have hmaj : ∀ v x y, majAt b (fun v => frameOf (gramOf b (H v))) v x y = H v x y := by
    intro v x y
    have e1 : majAt b (fun v => frameOf (gramOf b (H v))) v x y =
        ∑ i, ∑ j, starRingEnd ℂ (vecAt b v x i) *
          gramOf b (majAt b (fun v => frameOf (gramOf b (H v))) v) i j * vecAt b v y j :=
      sesq_eq_sum (isSesq_maj b _) b v x y
    have e2 : H v x y = ∑ i, ∑ j, starRingEnd ℂ (vecAt b v x i) * gramOf b (H v) i j *
        vecAt b v y j := sesq_eq_sum hH b v x y
    rw [e1, e2, gramOf_maj, (hF v).2]
  refine ⟨fun v => (hF v).1, hmaj, fun v x => ?_⟩
  rw [normAt_eq_sqrt]
  exact congrArg (fun t => Real.sqrt t.re) (hmaj v x x)

theorem posAt_comp {V ι W κ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (c : Basis κ K W)
    {H : InfinitePlace K → V → V → ℂ} (hH : IsSesq H) (hP : PosAt b H) (f : W →ₗ[K] V)
    (hf : Function.Injective f) : PosAt c (fun v x y => H v (f x) (f y)) := by
  intro v
  have hG := hP v
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.2 hf)
  obtain ⟨M, hM⟩ : ∃ M, M = (LinearMap.toMatrix c b f).map v.embedding := ⟨_, rfl⟩
  have hinv : ((LinearMap.toMatrix b c g).map v.embedding) * M = 1 := by
    rw [hM, ← Matrix.map_mul, ← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hinj : Function.Injective M.mulVec := by
    intro a a' h
    have h1 := congrArg ((LinearMap.toMatrix b c g).map v.embedding).mulVec h
    simpa [Matrix.mulVec_mulVec, hinv] using h1
  have hvec : ∀ j, vecAt b v (f (c j)) = fun k => M k j := by
    intro j
    funext k
    rw [hM]
    simp only [vecAt, Matrix.map_apply]
    rw [LinearMap.toMatrix_apply]
  have hgram : gramOf c (fun x y => H v (f x) (f y)) = M.conjTranspose * gramOf b (H v) * M := by
    ext i j
    simp only [gramOf, Matrix.of_apply]
    rw [sesq_eq_sum hH b v (f (c i)) (f (c j)), hvec, hvec]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rfl
  show (gramOf c (fun x y => H v (f x) (f y))).PosDef
  rw [hgram]
  first
  | exact hG.conjTranspose_mul_mul_same hinj
  | exact Matrix.PosDef.conjTranspose_mul_mul_same hG hinj

theorem isSesq_comp {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {H : InfinitePlace K → V → V → ℂ} (hH : IsSesq H) (f : W →ₗ[K] V) :
    IsSesq (fun v x y => H v (f x) (f y)) := by
  intro v
  obtain ⟨h1, h2, h3, h4⟩ := hH v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [map_add]
    exact h1 _ _ _
  · simp only [map_add]
    exact h2 _ _ _
  · simp only [map_smul]
    exact h3 _ _ _
  · simp only [map_smul]
    exact h4 _ _ _

theorem posAt_maj {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    PosAt b (fun v => majAt b X v) := by
  intro v
  show (gramOf b (majAt b X v)).PosDef
  rw [gramOf_maj]
  have hinj : Function.Injective ((X v)⁻¹).mulVec := by
    intro a c hac
    have h1 := congrArg (X v).mulVec hac
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v)] using h1
  first
  | exact Matrix.PosDef.conjTranspose_mul_self _ hinj
  | exact (Matrix.posDef_conjTranspose_mul_self_iff _).2 hinj
  | (have h1 := Matrix.PosDef.one.conjTranspose_mul_mul_same hinj
     simpa using h1)

end Forms

section Pull

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem pull_spec1 (B : HLat K) {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] [Fintype κ] [DecidableEq κ] (c : Basis κ K W) (f : W →ₗ[K] B.V)
    (hB : FrameOK B) (hf : Function.Injective f) :
    FrameOK (pull B c f) ∧
    (∀ v (x y : W), majAt (pull B c f).b (pull B c f).X v x y = majAt B.b B.X v (f x) (f y)) ∧
    (∀ v (x : W), normAt (pull B c f).b (pull B c f).X v x = normAt B.b B.X v (f x)) := by
  have hS : IsSesq (fun v x y => majAt B.b B.X v (f x) (f y)) :=
    isSesq_comp (isSesq_maj B.b B.X) f
  have hPos : PosAt c (fun v x y => majAt B.b B.X v (f x) (f y)) :=
    posAt_comp B.b c (isSesq_maj B.b B.X) (posAt_maj B.b B.X hB) f hf
  obtain ⟨h1, h2, h3⟩ := of_form_spec K W κ c (B.L.comap (f.restrictScalars (𝓞 K))) _ hS hPos
  refine ⟨h1, h2, fun v x => ?_⟩
  rw [h3, normAt_eq_sqrt]

theorem map_comap_eq' {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (f : W →ₗ[K] V) (L : Submodule (𝓞 K) V) :
    (L.comap (f.restrictScalars (𝓞 K))).map (f.restrictScalars (𝓞 K)) =
      L ⊓ (LinearMap.range f).restrictScalars (𝓞 K) := by
  rw [Submodule.map_comap_eq, inf_comm]
  first
  | rfl
  | (congr 1
     ext y
     simp [LinearMap.mem_range])

theorem rkK_map {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (f : W →ₗ[K] V) (hf : Function.Injective f)
    (N : Submodule (𝓞 K) W) : rkK (N.map (f.restrictScalars (𝓞 K))) = rkK N := by
  unfold rkK
  have hs : Submodule.span K ((N.map (f.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (N : Set W)).map f := by
    rw [Submodule.map_coe, ← Submodule.span_image]
    rfl
  rw [hs]
  exact (Submodule.equivMapOfInjective f hf _).finrank_eq.symm

theorem pull_spec : PullSpec := by
  intro K _ _ _ B W κ _ _ _ _ _ _ c f hB hf
  obtain ⟨h1, h2, h3⟩ := pull_spec1 B c f hB hf
  have hf' : Function.Injective (f.restrictScalars (𝓞 K)) := hf
  have hfg : B.L.FG → (pull B c f).L.FG := by
    intro hL
    apply Submodule.fg_of_fg_map_injective (f.restrictScalars (𝓞 K)) hf'
    show ((B.L.comap (f.restrictScalars (𝓞 K))).map (f.restrictScalars (𝓞 K))).FG
    rw [map_comap_eq']
    exact Formalism.LFunctionChainParameters.slopeLatticeData.fg_of_le hL inf_le_left
  refine ⟨h1, h2, h3, fun hL => ?_, fun hG => ⟨h1, hfg hG.2.1, ?_⟩⟩
  · obtain ⟨-, -, r3, r4, r5, -, -⟩ := rerealize K W κ B.V B.ι (pull B c f).b (pull B c f).X B.b B.X f
      h1 hB hf (fun v x => (h3 v x).symm) (pull B c f).L (hfg hL)
    have hm : (pull B c f).L.map (f.restrictScalars (𝓞 K)) =
        B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K) := map_comap_eq' f B.L
    rw [hm] at r3 r4 r5
    refine ⟨hfg hL, ?_, ?_, ?_, ?_⟩
    · show rkK (pull B c f).L = rkK (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))
      rw [← hm, rkK_map f hf]
    · show muDef (pull B c f).b (pull B c f).X (pull B c f).L =
        muDef B.b B.X (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))
      unfold muDef; rw [r3]
    · show muMaxDef (pull B c f).b (pull B c f).X (pull B c f).L =
        muMaxDef B.b B.X (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))
      unfold muMaxDef; rw [r4]
    · show muMinDef (pull B c f).b (pull B c f).X (pull B c f).L =
        muMinDef B.b B.X (B.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K))
      unfold muMinDef; rw [r5]
  · rw [eq_top_iff]
    intro x _
    have hx : f x ∈ Submodule.span K (B.L : Set B.V) := by rw [hG.2.2]; trivial
    obtain ⟨d, hd, hdx⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS B.L hx
    have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have h4 : d • x ∈ (pull B c f).L := by
      show (f.restrictScalars (𝓞 K)) (d • x) ∈ B.L
      rw [map_smul]
      exact hdx
    have h5 : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [h5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h4)

theorem embIso' (A B : HLat K) (ψ : A.V →ₗ[K] B.V) (U : Submodule K B.V) (hB : FrameOK B)
    (hψ : Function.Injective ψ) (hU : LinearMap.range ψ = U)
    (hn : ∀ v x, normAt A.b A.X v x = normAt B.b B.X v (ψ x))
    (hL : A.L = B.L.comap (ψ.restrictScalars (𝓞 K))) :
    ∃ I : Iso A (sub B U), ∀ x : A.V, U.subtype (I.e x) = ψ x := by
  let e : A.V ≃ₗ[K] U := (LinearEquiv.ofInjective ψ hψ).trans (LinearEquiv.ofEq _ _ hU)
  have he : ∀ a, ((e a : U) : B.V) = ψ a := fun a => rfl
  have hps := pull_spec1 B (sub B U).b U.subtype hB Subtype.val_injective
  refine ⟨⟨e, ?_, fun v x => ?_⟩, fun x => rfl⟩
  · ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hL] at ha
      exact ha
    · intro hy
      obtain ⟨a, ha⟩ := e.surjective y
      refine ⟨a, ?_, ha⟩
      rw [hL]
      show ψ a ∈ B.L
      rw [← he a, ha]
      exact hy
  · rw [hn]
    exact hps.2.2 v (e x)

theorem with_lattice_index : WithLIndex := by
  intro K _ _ _ _ A L' hA hL hle h0
  exact ⟨Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_mono A.b A.X hA hL hle h0,
    fun hr => Formalism.LFunctionChainParameters.slopeLatticeData.muDef_index A.b A.X hA hL hle h0 hr⟩

end Pull

section Unitary

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem cnorm_sq_eq (u : ι → ℂ) : ((cnorm u ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  rw [cnorm_sq]
  push_cast
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem cnorm_mulVec {M : Matrix κ ι ℂ} (h : M.conjTranspose * M = 1) (a : ι → ℂ) :
    cnorm (M.mulVec a) = cnorm a := by
  have h2 : ((cnorm (M.mulVec a) ^ 2 : ℝ) : ℂ) = ((cnorm a ^ 2 : ℝ) : ℂ) := by
    rw [cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have h3 : cnorm (M.mulVec a) ^ 2 = cnorm a ^ 2 := by exact_mod_cast h2
  rw [← Real.sqrt_sq (cnorm_nonneg (M.mulVec a)), h3, Real.sqrt_sq (cnorm_nonneg a)]

end Unitary

section DualSec

variable {K : Type} [Field K] [NumberField K] [StarRing K] {A B : HLat K}

theorem vecAt_basis {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (v : InfinitePlace K) (i : ι) : vecAt b v (b i) = Pi.single i 1 := by
  funext j
  simp only [vecAt]
  rw [b.repr_self]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Finsupp.single_apply, Pi.single_apply, hj, Ne.symm hj]

theorem fcoord_basis {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (i : ι) :
    fcoord b X v (b i) = ((X v)⁻¹).col i := by
  unfold fcoord
  rw [vecAt_basis]
  ext j
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

def Iso.umat (I : Iso A B) (v : InfinitePlace K) : Matrix B.ι A.ι ℂ :=
  (B.X v)⁻¹ * (LinearMap.toMatrix A.b B.b I.e.toLinearMap).map v.embedding * A.X v

theorem Iso.fcoord_eq (I : Iso A B) (hA : FrameOK A) (v : InfinitePlace K) (x : A.V) :
    fcoord B.b B.X v (I.e x) = (I.umat v).mulVec (fcoord A.b A.X v x) := by
  have hv : vecAt B.b v (I.e x) =
      ((LinearMap.toMatrix A.b B.b I.e.toLinearMap).map v.embedding).mulVec (vecAt A.b v x) := by
    funext i
    show v.embedding (B.b.repr (I.e x) i) =
      (((LinearMap.toMatrix A.b B.b I.e.toLinearMap).map v.embedding).mulVec
        (v.embedding ∘ (A.b.repr x))) i
    rw [← RingHom.map_mulVec, LinearMap.toMatrix_mulVec_repr]
    rfl
  unfold fcoord
  rw [hv]
  simp only [Iso.umat, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hA v),
    Matrix.mul_one]

theorem Iso.umat_star_mul [IsTotallyComplex K] (I : Iso A B) (hA : FrameOK A)
    (v : InfinitePlace K) : (I.umat v).conjTranspose * I.umat v = 1 := by
  have hcol : ∀ i, fcoord B.b B.X v (I.e (A.b i)) = fun k => (I.umat v * (A.X v)⁻¹) k i := by
    intro i
    rw [I.fcoord_eq hA, fcoord_basis]
    ext k
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hG : (I.umat v * (A.X v)⁻¹).conjTranspose * (I.umat v * (A.X v)⁻¹) =
      ((A.X v)⁻¹).conjTranspose * (A.X v)⁻¹ := by
    ext i j
    have h1 := I.maj v (A.b i) (A.b j)
    have h2 := congrFun (congrFun (gramOf_maj A.b A.X v) i) j
    simp only [gramOf, Matrix.of_apply] at h2
    rw [← h2, ← h1]
    simp only [majAt, hcol, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hPu : IsUnit ((A.X v)⁻¹) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hA v))
  have hPHu : IsUnit ((A.X v)⁻¹).conjTranspose := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hPu).star
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc] at hG
  have hG2 := hPHu.mul_left_cancel hG
  rw [← Matrix.mul_assoc] at hG2
  have hG3 : (I.umat v).conjTranspose * I.umat v * (A.X v)⁻¹ = 1 * (A.X v)⁻¹ := by
    rw [hG2, Matrix.one_mul]
  exact hPu.mul_right_cancel hG3

theorem Iso.umat_mul_symm (I : Iso A B) (hA : FrameOK A) (v : InfinitePlace K) :
    I.umat v * I.symm.umat v = 1 := by
  have hB := I.frameOK hA
  have hM : (LinearMap.toMatrix A.b B.b I.e.toLinearMap) *
      (LinearMap.toMatrix B.b A.b I.symm.e.toLinearMap) = 1 := by
    rw [← LinearMap.toMatrix_comp]
    have hc : I.e.toLinearMap ∘ₗ I.symm.e.toLinearMap = LinearMap.id := by
      ext y
      exact I.e.apply_symm_apply y
    rw [hc, LinearMap.toMatrix_id]
  have hM' : (LinearMap.toMatrix A.b B.b I.e.toLinearMap).map v.embedding *
      (LinearMap.toMatrix B.b A.b I.symm.e.toLinearMap).map v.embedding = 1 := by
    rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold Iso.umat
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hA v),
    ← Matrix.mul_assoc ((LinearMap.toMatrix A.b B.b I.e.toLinearMap).map v.embedding), hM',
    Matrix.one_mul, Matrix.nonsing_inv_mul _ (hB v)]

theorem Iso.umat_conjTranspose [IsTotallyComplex K] (I : Iso A B) (hA : FrameOK A)
    (v : InfinitePlace K) : (I.umat v).conjTranspose = I.symm.umat v := by
  calc (I.umat v).conjTranspose
      = (I.umat v).conjTranspose * (I.umat v * I.symm.umat v) := by
        rw [I.umat_mul_symm hA, Matrix.mul_one]
    _ = I.symm.umat v := by
        rw [← Matrix.mul_assoc, I.umat_star_mul hA, Matrix.one_mul]

theorem Iso.umat_mul_star [IsTotallyComplex K] (I : Iso A B) (hA : FrameOK A)
    (v : InfinitePlace K) : I.umat v * (I.umat v).conjTranspose = 1 := by
  rw [I.umat_conjTranspose hA, I.umat_mul_symm hA]

def Iso.dual [IsTotallyComplex K] (I : Iso A B) (hA : FrameOK A) :
    Iso (HLatOps.dual A) (HLatOps.dual B) where
  e := I.e.symm.dualMap
  map_L := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      intro y hy
      exact hf (I.e.symm y) (I.symm.mem_L.2 hy)
    · intro hg
      refine ⟨I.e.dualMap g, fun x hx => hg (I.e x) (I.mem_L.2 hx), ?_⟩
      apply LinearMap.ext
      intro y
      show g (I.e (I.e.symm y)) = g y
      rw [LinearEquiv.apply_symm_apply]
  norm := by
    intro v f
    have hB := I.frameOK hA
    show cnorm (fcoord B.b.dualBasis (dualFrame B.X) v (I.e.symm.dualMap f)) =
      cnorm (fcoord A.b.dualBasis (dualFrame A.X) v f)
    set φB := fcoord B.b.dualBasis (dualFrame B.X) v (I.e.symm.dualMap f) with hφB
    set φA := fcoord A.b.dualBasis (dualFrame A.X) v f with hφA
    have hpair : ∀ x : A.V, ((I.umat v).transpose.mulVec φB) ⬝ᵥ fcoord A.b A.X v x =
        φA ⬝ᵥ fcoord A.b A.X v x := by
      intro x
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, ← I.fcoord_eq hA]
      have h1 := DualPolygon.ident_sum_fcoord B.b B.X hB v (I.e.symm.dualMap f) (I.e x)
      have h2 := DualPolygon.ident_sum_fcoord A.b A.X hA v f x
      have h3 : (I.e.symm.dualMap f) (I.e x) = f x := by
        show f (I.e.symm (I.e x)) = f x
        rw [LinearEquiv.symm_apply_apply]
      rw [h3] at h1
      exact h1.trans h2.symm
    have hw : (I.umat v).transpose.mulVec φB = φA := by
      have h0 : ∀ i, (Matrix.vecMul ((I.umat v).transpose.mulVec φB) (A.X v)⁻¹) i =
          (Matrix.vecMul φA (A.X v)⁻¹) i := by
        intro i
        have := hpair (A.b i)
        rw [fcoord_basis] at this
        exact this
      have h1 : Matrix.vecMul ((I.umat v).transpose.mulVec φB) (A.X v)⁻¹ =
          Matrix.vecMul φA (A.X v)⁻¹ := funext h0
      have h2 := congrArg (fun w => Matrix.vecMul w (A.X v)) h1
      simpa [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hA v)] using h2
    have hU : ((I.umat v).transpose).conjTranspose * (I.umat v).transpose = 1 := by
      have : ((I.umat v).transpose).conjTranspose * (I.umat v).transpose =
          (I.umat v * (I.umat v).conjTranspose).transpose := by
        rw [Matrix.transpose_mul]
        congr 1
      rw [this, I.umat_mul_star hA, Matrix.transpose_one]
    rw [← hw, cnorm_mulVec hU]

theorem iso_inv_dual : IsoInvDual := by
  intro K _ _ _ _ A B I hG
  have hd := dualPl K A.V A.ι A.b A.X hG.1 A.L hG.2.1 hG.2.2
  have hX : FrameOK (HLatOps.dual A) := DualPolygon.dualFrame_unit A.X hG.1
  obtain ⟨h1, h2, h3, -⟩ := (I.dual hG.1).numbers hX hd.1
  exact ⟨h1, h2, h3⟩

theorem dual_numbers : DualNumbers := by
  intro K _ _ _ _ A hG hr
  have hL : A.L ≠ ⊥ := Formalism.LFunctionChainParameters.slopeLatticeData.ne_bot_of_rkK_pos hr
  have hd := dualPl K A.V A.ι A.b A.X hG.1 A.L hG.2.1 hG.2.2
  have hXd : ∀ v, IsUnit (dualFrame A.X v).det := DualPolygon.dualFrame_unit A.X hG.1
  have : Module.Finite K A.V := Module.Finite.of_basis A.b
  have hdne : dualLat A.L ≠ ⊥ := by
    intro h
    have htop := hd.2.1
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at htop
    have h0 : Module.finrank K (Module.Dual K A.V) = 0 := by
      rw [← finrank_top K (Module.Dual K A.V), ← htop, finrank_bot]
    rw [Subspace.dual_finrank_eq] at h0
    have : rkK A.L ≤ Module.finrank K A.V := Submodule.finrank_le _
    simp only [HLat.rank] at hr
    omega
  have hs1 := sizeMu K A.V A.ι A.b A.X hG.1 A.L hG.2.1 hL
  have hs2 := sizeMu K (Module.Dual K A.V) A.ι A.b.dualBasis (dualFrame A.X) hXd
    (dualLat A.L) hd.1 hdne
  simp only at hs1 hs2
  have hc : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) =
      logDisc K / (Module.finrank ℚ K : ℝ) / 2 := by rw [div_div, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · show muDef A.b.dualBasis (dualFrame A.X) (dualLat A.L) = -muDef A.b A.X A.L
    rw [hs2.2.1, hs1.2.1, hd.2.2.2.1, Real.log_inv]
    ring
  · have e := hd.2.2.2.2.1
    rw [hs2.2.2.2.1, hs1.2.2.2.2.1, ← Real.exp_neg] at e
    have e2 := Real.exp_injective e
    rw [hc] at e2
    show muMaxDef A.b.dualBasis (dualFrame A.X) (dualLat A.L) = -muMinDef A.b A.X A.L
    unfold muMaxDef muMinDef
    linarith
  · have e := hd.2.2.2.2.2.1
    rw [hs2.2.2.2.2.1, hs1.2.2.2.1, ← Real.exp_neg] at e
    have e2 := Real.exp_injective e
    rw [hc] at e2
    show muMinDef A.b.dualBasis (dualFrame A.X) (dualLat A.L) = -muMaxDef A.b A.X A.L
    unfold muMaxDef muMinDef
    linarith

end DualSec

section HtMap

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end HtMap

section Emb

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem frameOK_of_emb (A B : HLat K) (ψ : A.V →ₗ[K] B.V) (hB : FrameOK B)
    (hψ : Function.Injective ψ) (hn : ∀ v x, normAt A.b A.X v x = normAt B.b B.X v (ψ x)) :
    FrameOK A := by
  intro v
  by_contra hv
  have h0 : ∀ y : A.V, y = 0 := by
    intro y
    have hy : normAt B.b B.X v (ψ y) = 0 := by
      rw [← hn]
      show cnorm ((A.X v)⁻¹.mulVec (vecAt A.b v y)) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hv, Matrix.zero_mulVec]
      simp [cnorm]
    exact hψ (by rw [normAt_eq_zero B.b B.X v (hB v) hy, map_zero])
  haveI hι : IsEmpty A.ι := ⟨fun i => A.b.ne_zero i (h0 _)⟩
  apply hv
  rw [Matrix.det_isEmpty]
  exact isUnit_one

theorem emb_numbers : EmbNumbers := by
  intro K _ _ _ A B ψ hB hψ hn
  have hA := frameOK_of_emb A B ψ hB hψ hn
  refine ⟨hA, fun N => ⟨(rkK_map ψ hψ N).symm, fun hN => ?_⟩⟩
  obtain ⟨h1, -, h3, h4, h5, -, -⟩ := rerealize K A.V A.ι B.V B.ι A.b A.X B.b B.X ψ hA hB hψ
    (fun v x => (hn v x).symm) N hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · show muDef A.b A.X N = muDef B.b B.X (N.map (ψ.restrictScalars (𝓞 K)))
    unfold muDef; rw [h3]
  · show muMaxDef A.b A.X N = muMaxDef B.b B.X (N.map (ψ.restrictScalars (𝓞 K)))
    unfold muMaxDef; rw [h4]
  · show muMinDef A.b A.X N = muMinDef B.b B.X (N.map (ψ.restrictScalars (𝓞 K)))
    unfold muMinDef; rw [h5]
  · show (2 / (finrank ℚ K : ℝ)) * Real.log (ht A.b A.X N) =
      (2 / (finrank ℚ K : ℝ)) * Real.log (ht B.b B.X (N.map (ψ.restrictScalars (𝓞 K))))
    rw [h1]

theorem comap_fg {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (f : W →ₗ[K] V) (hf : Function.Injective f)
    {L : Submodule (𝓞 K) V} (hL : L.FG) : (L.comap (f.restrictScalars (𝓞 K))).FG := by
  apply Submodule.fg_of_fg_map_injective (f.restrictScalars (𝓞 K)) hf
  rw [map_comap_eq']
  have hN : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  exact isNoetherian_submodule.mp hN _ inf_le_left

end Emb

section Ext

open TensorProduct

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K']
  [StarRing K'] [Algebra K K']

end Ext

section Record

open Formalism.BasicNotions.DV

example (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) : L.NuH u = withL (D.div.Nu u) (L.NuLat u) := rfl
example (D : D7) (u : D.what₂.Word) :
    (D.fm u).ramLat = withL ((D.fm u).lat 0) (D.fm u).ramL := rfl

end Record

section Checks

variable {K : Type} [Field K] [NumberField K] [StarRing K]

example (A : HLat K) : (dual A).mu = A.muDual := rfl
example (A : HLat K) : (dual A).muMax = A.muMaxDual := rfl
example (A : HLat K) : (dual A).muMin = A.muMinDual := rfl
example (A : HLat K) : withL A A.L = A := rfl
example {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Module.Finite K V] (L : Submodule (𝓞 K) V) (H : InfinitePlace K → V → V → ℂ) :
    ofForm L H = ofFormB (Module.finBasis K V) L H := rfl
example (A : HLat K) (L' : Submodule (𝓞 K) A.V) : withL A L' = { A with L := L' } := rfl
example (A : HLat K) (L' : Submodule (𝓞 K) A.V) : (withL A L').mu = muDef A.b A.X L' := rfl

end Checks

end Formalism.L2.GlobalTheoryTheory.HLatOps
