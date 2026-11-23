import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.IsOrthSplit
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormalFrame0
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mi MeasureTheory NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Doubling

namespace GlobalTheory.CompanionTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_cols (S : HSp D) {a b : ℕ} (M : Matrix (Fin S.rank) (Fin a) D.host.E) (N : Matrix (Fin S.rank) (Fin b) D.host.E)
    (i : Fin a) (l : Fin b) : (Mᴴ * S.gram * N) i l =
      S.hT (S.frame.equivFun.symm fun k => M k i) (S.frame.equivFun.symm fun k => N k l) := by
  simp only [Module.Basis.equivFun_symm_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_smul,
    LinearMap.map_smulₛₗ₂, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum, HSpace.gram]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem col_frameMat (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (i : Fin B.rank) :
    (A.frame.equivFun.symm fun k => frameMat A B ι k i) = ι (B.frame i) := by
  simp only [frameMat, LinearMap.toMatrix_apply, Module.Basis.equivFun_symm_apply, Module.Basis.sum_repr]

theorem frameMat_comp (A B C : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (κ : C.V →ₗ[D.host.E] B.V) :
    frameMat A C (ι ∘ₗ κ) = frameMat A B ι * frameMat B C κ := LinearMap.toMatrix_comp _ _ _ _ _

theorem gram_frameMat {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : HSpace.IsIsomEmb B A ι) :
    (frameMat A B ι)ᴴ * A.gram * frameMat A B ι = B.gram := by
  ext i l
  rw [gram_cols, col_frameMat, col_frameMat, h]; rfl

theorem hT_symm_zero (S : HSp D) {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

theorem exists_piT (D : D7) : ∃ π : D.host.E, star π * π = (D.sp.T : D.host.E) := by
  obtain ⟨π, -, h, -⟩ := D.T_norm D.u₀
  refine ⟨π, ?_⟩
  rw [D.sp_T, ← h, mul_comm, GlobalTheory.StdFrames.conj_eq_star]

def piT (D : D7) : D.host.E := (exists_piT D).choose

theorem star_piT_mul (D : D7) : star (piT D) * piT D = (D.sp.T : D.host.E) := (exists_piT D).choose_spec

theorem T_ne_zero (D : D7) : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 D.sp.T_prime.ne_zero

theorem piT_ne_zero (D : D7) : piT D ≠ 0 := fun h => T_ne_zero D (by rw [← star_piT_mul, h, mul_zero])

@[reducible] def lineT (D : D7) (neg : Bool) : HSp D where
  V := Fin 1 → D.host.E
  hT := Examples₂.diagForm 1 fun _ => neg
  herm := Examples₂.diagForm_isSymm 1 _
  nondeg := Examples₂.diagForm_nondeg 1 _
  rank := 1
  rank_eq := Module.finrank_fin_fun _
  frame := (Pi.basisFun D.host.E (Fin 1)).unitsSMul fun _ => Units.mk0 (piT D) (piT_ne_zero D)
  sig := fun _ => if neg then (0, 1) else (1, 0)
  L0 := Examples₂.stdLat 1
  standardTuple_isLattice := Examples₂.stdLat_isLattice 1
  baseLattice_isUnimodular := Examples₂.stdLat_unimod Examples₂.star_isIntegral 1 _

abbrev lineNeg (D : D7) : HSp D := lineT D true

abbrev linePos (D : D7) : HSp D := lineT D false

theorem lineT_gram (neg : Bool) (i l : Fin 1) :
    (lineT D neg).gram i l = if neg then -(D.sp.T : D.host.E) else (D.sp.T : D.host.E) := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : l = 0 := Subsingleton.elim _ _
  change Examples₂.diagForm 1 (fun _ => neg) _ _ = _
  rw [Examples₂.diagForm_apply, ← star_piT_mul]
  cases neg <;> simp [Module.Basis.unitsSMul_apply, Examples₂.sgn, Units.smul_def]

theorem lineNeg_gram (i l : Fin 1) : (lineNeg D).gram i l = -(D.sp.T : D.host.E) := lineT_gram true i l

theorem linePos_gram (i l : Fin 1) : (linePos D).gram i l = (D.sp.T : D.host.E) := lineT_gram false i l

theorem hasSignature_nat {T : ℕ} (hT : 0 < T) :
    Formalism.UG.HasSignature (Matrix.of fun _ _ : Fin 1 => (T : ℂ)) 1 0 ∧
      Formalism.UG.HasSignature (Matrix.of fun _ _ : Fin 1 => -(T : ℂ)) 0 1 := by
  have h1 : ((√(T : ℝ) : ℝ) : ℂ) * ((√(T : ℝ) : ℝ) : ℂ) = T := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg T)]; simp
  have h2 : ((√(T : ℝ) : ℝ) : ℂ) ≠ 0 := fun h => by
    rw [h, mul_zero] at h1
    exact hT.ne' (by exact_mod_cast h1.symm)
  constructor
  · refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp) (Matrix.of fun _ _ => ((√(T : ℝ) : ℝ) : ℂ)⁻¹) ?_
    ext (r | r) (s | s)
    · obtain rfl : r = s := Subsingleton.elim _ _
      simp [Matrix.mul_apply, Formalism.UG.Jpq]
      rw [← h1]; field_simp
    · exact s.elim0
    · exact r.elim0
    · exact r.elim0
  · refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp) (Matrix.of fun _ _ => ((√(T : ℝ) : ℝ) : ℂ)⁻¹) ?_
    ext (r | r) (s | s)
    · exact r.elim0
    · exact r.elim0
    · exact s.elim0
    · obtain rfl : r = s := Subsingleton.elim _ _
      simp [Matrix.mul_apply, Formalism.UG.Jpq]
      rw [← h1]; field_simp

theorem lineT_sigOK (neg : Bool) : (lineT D neg).SigOK := fun τ => by
  have h := hasSignature_nat D.sp.T_prime.pos
  cases neg
  · have e : (lineT D false).gram.map τ = Matrix.of fun _ _ : Fin 1 => (D.sp.T : ℂ) := by
      ext i l; rw [Matrix.map_apply, lineT_gram]; simp
    show Formalism.UG.HasSignature _ 1 0
    rw [e]; exact h.1
  · have e : (lineT D true).gram.map τ = Matrix.of fun _ _ : Fin 1 => -(D.sp.T : ℂ) := by
      ext i l; rw [Matrix.map_apply, lineT_gram]; simp
    show Formalism.UG.HasSignature _ 0 1
    rw [e]; exact h.2

theorem isLineVec_lineT (neg : Bool) : IsLineVec (lineT D neg) fun _ => 1 := by
  refine ⟨rfl, ?_⟩
  have := T_ne_zero D
  cases neg <;> simp [dotProduct, Matrix.mulVec, lineT_gram, this]

def lineMap (neg : Bool) (S : HSp D) (v : S.V) : (lineT D neg).V →ₗ[D.host.E] S.V :=
  (lineT D neg).frame.constr D.host.E fun _ => v

theorem lineMap_frame (neg : Bool) (S : HSp D) (v : S.V) (i : Fin 1) : lineMap neg S v ((lineT D neg).frame i) = v :=
  Module.Basis.constr_basis _ _ _ _

theorem lineMap_apply (neg : Bool) (S : HSp D) (v : S.V) (a : (lineT D neg).V) :
    lineMap neg S v a = (lineT D neg).frame.repr a 0 • v := by
  rw [lineMap, Module.Basis.constr_apply_fintype]
  exact Fin.sum_univ_one _

theorem lineMap_isom {neg : Bool} {S : HSp D} {v : S.V}
    (hv : S.hT v v = if neg then -(D.sp.T : D.host.E) else (D.sp.T : D.host.E)) :
    HSpace.IsIsomEmb (lineT D neg) S (lineMap neg S v) := fun a b => by
  have e : ∀ a : (lineT D neg).V, a = (lineT D neg).frame.repr a 0 • (lineT D neg).frame 0 := fun a => by
    conv_lhs => rw [← (lineT D neg).frame.sum_repr a]
    exact Fin.sum_univ_one _
  rw [lineMap_apply, lineMap_apply]
  conv_rhs => rw [e a, e b]
  simp only [LinearMap.map_smulₛₗ₂, map_smul, hv]
  rw [← lineT_gram neg 0 0]; rfl

theorem exists_topScalar (D : D7) : ∃ l : D.host.E,
    star l * l * (D.sp.X D.R.m).hT D.sp.z D.sp.z = (D.sp.T : D.host.E) := by
  have hr : (D.sp.X D.R.m).rank = D.sp.X'.rank + 1 := by
    have h1 := D.sp.X_rank D.R.m le_rfl
    have h2 := D.sp.X'_rank
    have h3 := D.R.two_le_m
    have h4 : D.R.m * (D.R.t + 1) = D.R.m * D.R.t + D.R.m := by ring
    simp only [Ranks.N, Ranks.rankX', Ranks.r] at h1 h2
    omega
  obtain ⟨b, hb, hd, hs, a, ha, hdet⟩ := GlobalTheory.FrameComplement.exists_complement (p := 1) (q := 0) D.sp.cm.cmUnram.2.1
    D.sp.X' (D.sp.X D.R.m) D.sp.iX' D.sp.iX'_isom hr
    (fun τ => by have := D.sp.X'_sig τ; rwa [D.X'_posDef τ] at this)
    (fun τ => by have := D.sp.X_sig D.R.m τ; rw [D.X_posDef D.R.m le_rfl τ] at this; rw [← hr]; exact this)
  have hX := GlobalTheory.FrameComplement.gram_det_ne D.sp.X'
  have hT0 := T_ne_zero D
  obtain ⟨P, -, hP⟩ := GlobalTheory.HermAdelicNorm.congr_of_signature_of_adelic_norm D.host.F D.host.E D.sp.cm 1
    (Matrix.of fun i l => (D.sp.X D.R.m).hT (b i) (b l)) (Matrix.of fun _ _ => (D.sp.T : D.host.E))
    (Matrix.ext fun i l => (D.sp.X D.R.m).herm.eq _ _) (by ext i l; simp) hd (by simpa using hT0)
    (fun τ => ⟨_, _, hs τ, by
      convert (hasSignature_nat D.sp.T_prime.pos).1 using 1
      ext i l; simp⟩)
    (by
      have h2 := (((GlobalTheory.DetNorm.isN_det (D.sp.X D.R.m)).mul ((GlobalTheory.DetNorm.isN_det D.sp.X').inv
        (GlobalTheory.DetNorm.star_det _))).mul (GlobalTheory.DetNorm.isN_star a⁻¹)).mul ((GlobalTheory.DetNorm.isNormFromTensorFiniteAdele_levelNormT (D := D)).inv (by simp))
      have ha' : star a ≠ 0 := star_ne_zero.2 ha
      have h3 : ∀ x g u : D.host.E, x ≠ 0 → star a * a * x * g * x⁻¹ * (star a⁻¹ * a⁻¹) * u⁻¹ = g / u :=
        fun x g u hx => by rw [star_inv₀, div_eq_mul_inv]; field_simp
      rw [hdet, h3 _ _ _ hX] at h2
      rw [Matrix.det_unique (Matrix.of fun _ _ : Fin 1 => (D.sp.T : D.host.E))]
      exact h2)

  let o : OrthDec (D.sp.X D.R.m) D.sp.X' (linePos D) :=
    { iA := frameMat _ _ D.sp.iX'
      iB := frameMat _ _ (lineMap false _ (P 0 0 • b 0))
      isoA := gram_frameMat D.sp.iX'_isom
      isoB := gram_frameMat (lineMap_isom (by
        have := congrFun (congrFun hP 0) 0
        simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, Matrix.of_apply] at this
        simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply, Bool.false_eq_true, if_false]
        linear_combination this))
      orth := by
        ext i l
        rw [gram_cols, col_frameMat, col_frameMat, lineMap_frame]
        have h0 : (D.sp.X D.R.m).hT (D.sp.iX' (D.sp.X'.frame l)) (P 0 0 • b 0) = 0 := by
          rw [map_smul, hb, smul_zero]
        rw [hT_symm_zero _ h0]; rfl
      rank_add := hr.symm }
  let y : Fin (D.sp.X D.R.m).rank → D.host.E := (D.sp.X D.R.m).frame.equivFun D.sp.z
  let Y : Matrix (Fin (D.sp.X D.R.m).rank) (Fin 1) D.host.E := Matrix.of fun k _ => y k
  have hY : ∀ i, ((D.sp.X D.R.m).frame.equivFun.symm fun k => Y k i) = D.sp.z := fun i =>
    (D.sp.X D.R.m).frame.equivFun.symm_apply_apply _
  have h1 : o.iAᴴ * (D.sp.X D.R.m).gram * Y = 0 := by
    ext i l
    rw [gram_cols, hY, col_frameMat, D.sp.z_orth]; rfl
  have h2 : Y = o.iB * (o.qB * Y) := by
    conv_lhs => rw [← Matrix.one_mul Y, ← o.iA_qA_add]
    rw [Matrix.add_mul, Matrix.mul_assoc, OrthDec.qA, Matrix.mul_assoc _ _ Y, h1, Matrix.mul_zero, Matrix.mul_zero, zero_add,
      Matrix.mul_assoc]
  have h3 : Yᴴ * (D.sp.X D.R.m).gram * Y = (o.qB * Y)ᴴ * (linePos D).gram * (o.qB * Y) := by
    conv_lhs => rw [h2]
    rw [← o.isoB, Matrix.conjTranspose_mul o.iB]
    simp only [Matrix.mul_assoc]
  have h4 := congrFun (congrFun h3 0) 0
  rw [gram_cols, hY] at h4
  simp only [Matrix.mul_apply (M := (o.qB * Y)ᴴ * (linePos D).gram), Matrix.mul_apply (M := (o.qB * Y)ᴴ),
    Fin.sum_univ_one, Matrix.conjTranspose_apply, linePos_gram] at h4
  generalize (o.qB * Y) 0 0 = c at h4
  have hc : c ≠ 0 := fun h => D.sp.z_anis (by rw [h4, h, mul_zero])
  have hc' : star c ≠ 0 := star_ne_zero.2 hc
  refine ⟨c⁻¹, ?_⟩
  rw [h4, star_inv₀]; field_simp

section Hyp

variable {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

def IsFrame0 (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) : Prop :=
  IsIsoSub T C ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C' = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C = 1 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B0 * T.gram * B0 = T0.gram ∧
    T.rank = 2 * r + T0.rank

theorem isQuotFrame_iff {T T0 : HSp D} {r : ℕ} {C C' : Matrix (Fin T.rank) (Fin r) D.host.E}
    {B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E} : IsQuotFrame T C C' T0 B0 ↔ 0 < r ∧ IsFrame0 T C C' T0 B0 :=
  ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem gram_swap_zero {a b : ℕ} {M : Matrix (Fin S.rank) (Fin a) D.host.E} {N : Matrix (Fin S.rank) (Fin b) D.host.E}
    (h : Mᴴ * S.gram * N = 0) : Nᴴ * S.gram * M = 0 := by
  have := congrArg Matrix.conjTranspose h
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
    ← Matrix.mul_assoc] at this

theorem isFrame0_hyp : IsFrame0 S d.e d.e' S₀ d.i₀ :=
  ⟨isIsoSub_e d, d.e'e', d.e'e, gram_swap_zero d.i₀e, gram_swap_zero d.i₀e', d.iso, by have := d.rank_add; omega⟩

theorem isLeviEmb_witt_embedding (g : GA D S₀) : IsLeviEmb S d.e d.e' S₀ d.i₀ g (d.emb0 g) :=
  ⟨d.wittDecomp_anisotropicEmbedding_inclX g, d.wittDecomp_anisotropicEmbedding_inclY g, d.wittDecomp_anisotropicEmbedding_inclAnisotropic g⟩

def scaleHyp (y : D.host.E) (hy : y ≠ 0) : HypDec S S₀ ρ where
  e := y • d.e
  e' := (star y)⁻¹ • d.e'
  i₀ := d.i₀
  ee := by rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, d.ee, smul_zero, smul_zero]
  e'e' := by rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, d.e'e', smul_zero, smul_zero]
  e'e := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, d.e'e, smul_smul, star_inv₀, star_star,
      inv_mul_cancel₀ hy, one_smul]
  iso := d.iso
  i₀e := by rw [Matrix.mul_smul, d.i₀e, smul_zero]
  i₀e' := by rw [Matrix.mul_smul, d.i₀e', smul_zero]
  rank_add := d.rank_add

theorem incA_mul_inv {y : D.host.E} (hy : y ≠ 0) : incA D y⁻¹ * incA D y = 1 := by
  rw [← map_mul, inv_mul_cancel₀ hy, map_one]

theorem scaleHyp_jX (y : D.host.E) (hy : y ≠ 0) : (scaleHyp d y hy).jX = incA D y • d.jX := rat_smul y d.e

theorem scaleHyp_pX (y : D.host.E) (hy : y ≠ 0) : (scaleHyp d y hy).pX = incA D y⁻¹ • d.pX := by
  rw [HypDec.pX, HypDec.pX, ← rat_smul]
  congr 1
  change ((star y)⁻¹ • d.e')ᴴ * S.gram = y⁻¹ • (d.e'ᴴ * S.gram)
  rw [conjTranspose_smul, Matrix.smul_mul, star_inv₀, star_star]

theorem blockX_scaleHyp (y : D.host.E) (hy : y ≠ 0) (g : GA D S) : blockX (scaleHyp d y hy) g = blockX d g := by
  rw [blockX, blockX, scaleHyp_jX, scaleHyp_pX, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    incA_mul_inv hy, one_smul]

theorem witt_embedding_scale_invariant (y : D.host.E) (hy : y ≠ 0) : (scaleHyp d y hy).emb0 = d.emb0 := by
  ext1 g
  refine (scaleHyp d y hy).ga_ext ?_ ?_ ?_
  · rw [HypDec.wittDecomp_anisotropicEmbedding_inclX, scaleHyp_jX, Matrix.mul_smul, d.wittDecomp_anisotropicEmbedding_inclX]
  · rw [HypDec.wittDecomp_anisotropicEmbedding_inclAnisotropic]; exact (d.wittDecomp_anisotropicEmbedding_inclAnisotropic g).symm
  · have e : (scaleHyp d y hy).jY = incA D (star y)⁻¹ • d.jY := rat_smul _ d.e'
    rw [HypDec.wittDecomp_anisotropicEmbedding_inclY, e, Matrix.mul_smul, d.wittDecomp_anisotropicEmbedding_inclY]

theorem mem_flagN_of_blocks {g : GA D S} {T : Mx D ρ ρ} {b : Mx D ρ S₀.rank} (hT : GlobalTheory.BesselChar.StrictUp T)
    (hX : mt S g ⬝ d.jX = d.jX + d.jX ⬝ T) (h0 : mt S g ⬝ d.j0 = d.j0 + d.jX ⬝ b) : g ∈ NFlag S d.e := by
  have h1 : subOne S g ⬝ d.jX = d.jX ⬝ T := by rw [HypDec.subOne_mul, hX, add_sub_cancel_left]
  have h2 : subOne S g ⬝ d.j0 = d.jX ⬝ b := by rw [HypDec.subOne_mul, h0, add_sub_cancel_left]
  refine Subgroup.subset_closure ⟨fun i => ⟨fun j => T j i, fun j hj => hT j i hj, ?_⟩,
    fun x hx => ⟨_, d.mulVec_perp h1 h2 _ (d.pY_ratV hx)⟩⟩
  funext k
  exact congrFun (congrFun h1 k) i

theorem flagN_le_scaleHyp (y : D.host.E) (hy : y ≠ 0) : NFlag S d.e ≤ NFlag S (scaleHyp d y hy).e := fun g hg => by
  obtain ⟨T, b, hT, h1, h2⟩ := exists_blocks d hg
  refine mem_flagN_of_blocks (scaleHyp d y hy) hT (b := incA D y⁻¹ • b) ?_ ?_
  · rw [scaleHyp_jX, Matrix.mul_smul, h1, smul_add, Matrix.smul_mul]
  · rw [scaleHyp_jX, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, incA_mul_inv hy, one_smul]
    exact h2

theorem flagN_scaleHyp (y : D.host.E) (hy : y ≠ 0) : NFlag S (scaleHyp d y hy).e = NFlag S d.e := by
  refine le_antisymm ?_ (flagN_le_scaleHyp d y hy)
  have h := flagN_le_scaleHyp (scaleHyp d y hy) y⁻¹ (inv_ne_zero hy)
  have e : (scaleHyp (scaleHyp d y hy) y⁻¹ (inv_ne_zero hy)).e = d.e := by
    change y⁻¹ • y • d.e = d.e
    rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
  rwa [e] at h

theorem conj_mem_flagN (g : GA D S₀) {n : GA D S} (hn : n ∈ NFlag S d.e) :
    d.emb0 g * n * (d.emb0 g)⁻¹ ∈ NFlag S d.e := by
  obtain ⟨T, b, hT, h1, h2⟩ := exists_blocks d hn
  rw [← map_inv]
  refine mem_flagN_of_blocks d hT (b := b ⬝ mt S₀ g⁻¹) ?_ ?_
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, h1, Matrix.mul_add, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX g),
      d.wittDecomp_anisotropicEmbedding_inclX]
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ h2, Matrix.add_mul, Matrix.mul_add,
      cancel₂ (d.wittDecomp_anisotropicEmbedding_inclAnisotropic g), Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one, Matrix.mul_assoc, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX g)]

theorem eq_one_of_levi_embedding_mem_flag {g : GA D S₀} (h : d.emb0 g ∈ NFlag S d.e) : g = 1 := by
  obtain ⟨T, b, -, -, h2⟩ := exists_blocks d h
  have h3 : d.p0 ⬝ (mt S (d.emb0 g) ⬝ d.j0) = d.p0 ⬝ (d.j0 + d.jX ⬝ b) := by rw [h2]
  rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul, Matrix.mul_add, d.p0_j0, cancel₂ d.p0_jX, Matrix.zero_mul, add_zero]
    at h3
  exact mt_injective S₀ (h3.trans (mt_one S₀).symm)

variable (ψ : AddChar (AF D.host.F) ℂ)

theorem psiU_eq_psiFlag {n : GA D S} (hn : n ∈ NFlag S d.e) : psiU ψ S d.e n = psiFlag ψ d n := by
  obtain ⟨T, b, -, h1, -⟩ := exists_blocks d hn
  have key : ∀ v, IsPsiUVal ψ S d.e n v → v = psiFlag ψ d n := by
    rintro v ⟨u, hu, rfl⟩
    have hu' : mt S n ⬝ d.jX = d.jX ⬝ (show Mx D ρ ρ from u) := hu
    rw [psiFlag, blockX, hu', cancel₂ d.pX_jX, Matrix.one_mul]; rfl
  have hex : ∃ v, IsPsiUVal ψ S d.e n v :=
    ⟨_, (1 : Mx D ρ ρ) + T, h1.trans (by rw [Matrix.mul_add, Matrix.mul_one]; rfl), rfl⟩
  rw [psiU, dif_pos hex]
  exact key _ hex.choose_spec

theorem psiBes_conj (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (g : GA D S₀) (hg : mt S₀ g⁻¹ *ᵥ ratV z = ratV z)
    (n : GA D S) : psiBes ψ d θ z (d.emb0 g * n * (d.emb0 g)⁻¹) = psiBes ψ d θ z n := by
  have h1 : blockX d (d.emb0 g * n * (d.emb0 g)⁻¹) = blockX d n := by
    rw [← map_inv, blockX, blockX, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, cancel₂ (d.wittDecomp_projX_anisotropicEmbedding g)]
  have h2 : coefX d z (d.emb0 g * n * (d.emb0 g)⁻¹) = coefX d z n := by
    rw [← map_inv, coefX, coefX, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ (d.wittDecomp_projX_anisotropicEmbedding g),
      ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.pX, ← Matrix.mulVec_mulVec, hg]
  rw [psiBes, psiBes, simpleSum, simpleSum, h1, h2]

theorem psiBes_rat (hψ : PsiRat ψ) (θ : D.host.E) (z : Fin S₀.rank → D.host.E) {n : GA D S} (hn : n ∈ GQ S) :
    psiBes ψ d θ z n = 1 := by
  obtain ⟨γ, hγ⟩ := (mem_GQ_iff S n).1 hn
  replace hγ : rat γ = mt S n := hγ
  have h1 : blockX d n = rat (d.qX * (γ * d.e)) := by rw [blockX, ← hγ, rat_mul, rat_mul]; rfl
  have h2 : coefX d z n = ratV ((d.qX * (γ * d.i₀)) *ᵥ z) := by rw [coefX, ← hγ, ratV_mulVec, rat_mul, rat_mul]; rfl
  have h3 : incA D θ * simpleSum d z n ∈ (incA D).range := by
    rw [simpleSum, h1, h2]
    refine mul_mem ⟨θ, rfl⟩ (add_mem (sum_mem fun i _ => sum_mem fun j _ => ?_) (sum_mem fun i _ => mul_mem ?_ ⟨_, rfl⟩))
    · split_ifs
      · exact ⟨_, rfl⟩
      · exact zero_mem _
    · unfold ell
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  obtain ⟨x, hx⟩ := h3
  rw [psiBes, ← hx]
  exact hψ x

theorem psiRat_of_isStdChar {s : ℤ} (hψ : IsStdChar D ψ s) : PsiRat ψ := fun x => by
  rw [GlobalTheory.BesselChar.trace_incA]
  exact hψ.1.2.2.1 _

end Hyp

section Zero

variable {S S₀ : HSp D} (d : HypDec S S₀ 0)

theorem matrix_mul_empty_inner {a b : ℕ} (M : Mx D a 0) (N : Mx D 0 b) : M ⬝ N = 0 := by
  ext i l; simp [Matrix.mul_apply]

theorem witt_decomposition_zero_section_embed_eq_one : d.j0 ⬝ d.p0 = 1 := by
  have h := d.sum_eq_one
  rwa [matrix_mul_empty_inner, matrix_mul_empty_inner d.jY, zero_add, add_zero] at h

def emb0Equiv : GA D S₀ ≃* GA D S where
  toFun := d.emb0
  invFun g := ofMat S₀ (d.p0 ⬝ (mt S g ⬝ d.j0)) (by
    have h := d.gA_eq
    rw [matrix_mul_empty_inner (adj d.pY), matrix_mul_empty_inner (adj d.pX), zero_add, add_zero] at h
    rw [adj_mul, adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, cancel₃ h.symm, cancel₃ (mt_unitary S g), d.gram_00])
  left_inv g := mt_injective S₀ (by rw [mt_ofMat, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul])
  right_inv g := mt_injective S (by
    rw [← Matrix.mul_one (mt S (d.emb0 _)), ← witt_decomposition_zero_section_embed_eq_one d, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, mt_ofMat, cancel₂ (witt_decomposition_zero_section_embed_eq_one d),
      Matrix.one_mul, Matrix.mul_assoc, witt_decomposition_zero_section_embed_eq_one, Matrix.mul_one])
  map_mul' := map_mul d.emb0

theorem isHaar_map_levi_embedding (μ : Measure (GA D S₀)) (hμ : μ.IsHaarMeasure) : (μ.map d.emb0).IsHaarMeasure := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S₀
  exact MulEquiv.isHaarMeasure_map μ (emb0Equiv d) d.continuous_embed
    (continuous_of_mt S₀ (continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)))

end Zero

theorem exists_isQuotPair (V : HSp D) : ∃ μ 𝓕, IsQuotPair V μ 𝓕 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, 𝓕, h⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V Measure.haar inferInstance
  exact ⟨_, 𝓕, inferInstance, h⟩

def IsUPair (r : ℕ) (μ : Measure (SUp D r)) (𝓕 : Set (SUp D r)) : Prop :=
  μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratSU D r) 𝓕 μ ∧ μ 𝓕 = 1

theorem exists_isUPair (r : ℕ) : ∃ μ 𝓕, IsUPair (D := D) r μ 𝓕 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D r r
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  let p : Mx D r r → SUp D r := fun x => ⟨fun i j => if j ≤ i then 0 else x i j, fun i j h => if_pos h⟩
  have hp : Continuous p := Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => by
    split_ifs
    · exact continuous_const
    · exact (continuous_apply j).comp (continuous_apply i)) _
  have hpx : ∀ x : SUp D r, p x.1 = x := fun x => Subtype.ext (funext fun i => funext fun j => by
    change (if j ≤ i then 0 else x.1 i j) = x.1 i j
    split_ifs with h
    · exact (x.2 i j h).symm
    · rfl)
  have hcl : IsClosed ((SUp D r : AddSubgroup (Mx D r r)) : Set (Mx D r r)) := by
    have : ((SUp D r : AddSubgroup (Mx D r r)) : Set (Mx D r r)) = {x | (p x).1 = x} :=
      Set.ext fun x => ⟨fun h => congrArg Subtype.val (hpx ⟨x, h⟩), fun h => by
        simp only [Set.mem_ofPred_eq] at h
        rw [← h]; exact (p x).2⟩
    rw [this]
    exact isClosed_eq (continuous_subtype_val.comp hp) continuous_id
  haveI : LocallyCompactSpace (SUp D r) := hcl.locallyCompactSpace
  haveI : SecondCountableTopology (SUp D r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : DiscreteTopology (ratSU D r) :=
    DiscreteTopology.of_continuous_injective (f := fun γ : ratSU D r => (⟨γ.1.1, γ.2⟩ : GlobalTheory.MixModel.ratMx D r r))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      fun a b h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  refine (GlobalTheory.exists_normalise_meanSquare_of_cocompact (SUp D r) (ratSU D r) (p '' K) (hK.image hp) (fun (x : SUp D r) => ?_)
    (fun _ => 1) continuous_const (fun h => one_ne_zero (congrFun h 0)) (fun _ _ _ => rfl)).1
  obtain ⟨γx, hγx, hK'⟩ := hKc x.1
  obtain ⟨γ, rfl⟩ := mem_ratMx.1 hγx
  refine ⟨p (rat γ), ⟨fun i j => if j ≤ i then 0 else γ i j, ?_⟩, rat γ + x.1, hK', ?_⟩
  · funext i j
    change incA D (if j ≤ i then 0 else γ i j) = if j ≤ i then 0 else incA D (γ i j)
    split_ifs
    · exact map_zero _
    · rfl
  · refine Subtype.ext (funext fun i => funext fun j => ?_)
    change (if j ≤ i then 0 else incA D (γ i j) + x.1 i j) = (if j ≤ i then 0 else incA D (γ i j)) + x.1 i j
    split_ifs with h
    · rw [x.2 i j h, add_zero]
    · rfl

theorem exists_pull {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (hρ : ρ = 0) (μ : Measure (GA D S)) (hμ : μ.IsHaarMeasure) :
    ∃ μ' 𝓕', IsQuotPair S₀ μ' 𝓕' ∧ μ = μ'.map d.emb0 := by
  subst hρ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S₀
  have hc : Continuous (emb0Equiv d).symm :=
    continuous_of_mt S₀ (continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const))
  have h1 : (μ.map (emb0Equiv d).symm).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ (emb0Equiv d).symm hc d.continuous_embed
  obtain ⟨-, 𝓕, h⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D S₀ _ h1
  refine ⟨_, 𝓕, ⟨h1, h⟩, ?_⟩
  rw [Measure.map_map d.continuous_embed.measurable hc.measurable]
  have e : (d.emb0 : GA D S₀ → GA D S) ∘ (emb0Equiv d).symm = id := funext (emb0Equiv d).apply_symm_apply
  rw [e, Measure.map_id]

theorem embRel_embA {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ι : A.V →ₗ[D.host.E] S.V)
    (hι : frameMat S A ι = d.i₀ * o.iA) (h : GA D A) : EmbRel S A ι (embA d o h) h := by
  rw [EmbRel, hι]
  refine ⟨?_, fun x hx => ?_⟩
  · change mt S (d.emb0 (o.emb (h, 1))) ⬝ rat (d.i₀ * o.iA) = rat (d.i₀ * o.iA) ⬝ mt A h
    rw [rat_mul, ← Matrix.mul_assoc]
    change mt S (d.emb0 (o.emb (h, 1))) ⬝ d.j0 ⬝ o.jA = d.j0 ⬝ o.jA ⬝ mt A h
    rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
  · have h1 : (o.qA * d.q0) *ᵥ x = 0 := by
      have e : o.qA * d.q0 = A.gram⁻¹ * ((d.i₀ * o.iA)ᴴ * S.gram) := by
        rw [OrthDec.qA, HypDec.q0, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det S₀), Matrix.mul_assoc]
      rw [e, ← Matrix.mulVec_mulVec]
      exact (congrArg (A.gram⁻¹ *ᵥ ·) hx).trans (Matrix.mulVec_zero _)
    have h2 : o.pA *ᵥ (d.p0 *ᵥ ratV x) = 0 := by
      rw [Matrix.mulVec_mulVec, OrthDec.pA, HypDec.p0, ← rat_mul, ← ratV_mulVec, h1]
      exact funext fun _ => map_zero _
    have h3 := congrArg (· *ᵥ ratV x) d.sum_eq_one
    have h4 := congrArg (· *ᵥ (d.p0 *ᵥ ratV x)) o.sum_eq_one
    change mt S (d.emb0 (o.emb (h, 1))) *ᵥ ratV x = ratV x
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero, Matrix.one_mulVec, zero_add] at h3 h4
    simp only [HypDec.unitaryMatrix_wittCoreEmbedding, OrthDec.mt_emb, mt_one, Matrix.mul_one, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h2,
      Matrix.mulVec_zero, zero_add, h4, h3]

def rho (D : D7) (j : ℕ) : ℕ := (D.R.m - 1 - j) / 2

theorem rank_Y (j : ℕ) (hj : j < D.R.m) :
    (D.sp.Y j).rank = (D.sp.X j).rank + 2 * rho D j + (if Even j then 1 else 0) := by
  have h1 := D.sp.X_rank j hj.le
  have h2 := D.sp.Y_rank j hj.le
  obtain ⟨a, ha⟩ := D.R.m_even
  have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
  simp only [Ranks.N, Ranks.rankY, Ranks.r] at h1 h2
  unfold rho
  split_ifs with he
  · obtain ⟨b, hb⟩ := he; omega
  · rw [Nat.not_even_iff_odd] at he; obtain ⟨b, hb⟩ := he; omega

theorem rho_eq_zero {j : ℕ} (hj : D.R.m ≤ j + 2) : rho D j = 0 := by unfold rho; omega

theorem xi_zero_ne_zero : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D

theorem odd_c {j : ℕ} (hj : j < D.R.m) (he : Even j) : (D.R.m - 1 - j) % 2 = 1 :=
  (GlobalTheory.NormalFramesLevels.even_iff_odd_c hj).1 he

structure Frames (D : D7) where
  e : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E
  ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E
  z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E
  lam : D.host.E
  aux : IsAdaptedVectorSystem e ev z
  lam_norm : star lam * lam * (D.sp.X D.R.m).hT D.sp.z D.sp.z = (D.sp.T : D.host.E)

namespace Frames

variable (F : Frames D)

def colMat (j r : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin r) D.host.E := fun k i => F.e j i k

def dualMat (j r : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin r) D.host.E := fun k i => F.ev j i k

def srcScal (D : D7) (j : ℕ) : D.host.E := if Even j then 1 else D.host.xi0

theorem srcScal_ne (j : ℕ) : srcScal D j ≠ 0 := by
  unfold srcScal; split_ifs
  · exact one_ne_zero
  · exact xi_zero_ne_zero

def srcMat (j r : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin r) D.host.E := srcScal D j • F.colMat j r

def srcDual (j r : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin r) D.host.E := (star (srcScal D j))⁻¹ • F.dualMat j r

def skewDual (j r : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin r) D.host.E := D.host.xi0⁻¹ • F.dualMat j r

theorem srcMat_even {j : ℕ} (he : Even j) (r : ℕ) : F.srcMat j r = F.colMat j r := by
  rw [srcMat, srcScal, if_pos he, one_smul]

theorem srcDual_even {j : ℕ} (he : Even j) (r : ℕ) : F.srcDual j r = F.dualMat j r := by
  rw [srcDual, srcScal, if_pos he, star_one, inv_one, one_smul]

theorem srcMat_odd {j : ℕ} (ho : ¬ Even j) (r : ℕ) : F.srcMat j r = D.host.xi0 • F.colMat j r := by
  rw [srcMat, srcScal, if_neg ho]

theorem srcDual_odd {j : ℕ} (ho : ¬ Even j) (r : ℕ) : F.srcDual j r = -F.skewDual j r := by
  rw [srcDual, srcScal, if_neg ho, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_smul, skewDual]

def base (j r : ℕ) : Matrix (Fin (D.sp.Y j).rank) (Fin r) D.host.E :=
  fun k i => if i.1 < rho D j then F.e j i k else F.z j k

def ztop : (D.sp.X D.R.m).V := F.lam • D.sp.z

theorem ztop_norm : (D.sp.X D.R.m).hT F.ztop F.ztop = (D.sp.T : D.host.E) := by
  rw [ztop, map_smul, LinearMap.map_smulₛₗ₂, ← F.lam_norm]
  simp only [smul_eq_mul, starRingEnd_apply]; ring

abbrev V0 (D : D7) (j : ℕ) : HSp D := hsum (D.sp.X j) (lineNeg D)

def embeddingLineSum (j : ℕ) : (V0 D j).V →ₗ[D.host.E] (D.sp.Y j).V :=
  LinearMap.coprod (D.sp.iXY j) (lineMap true (D.sp.Y j) (vecY j (F.z j)))

theorem embedding_line_sum_inl (j : ℕ) : F.embeddingLineSum j ∘ₗ LinearMap.inl D.host.E _ _ = D.sp.iXY j := by
  ext x; simp [embeddingLineSum]

def orthogonalDecompLineSum (D : D7) (j : ℕ) : OrthDec (V0 D j) (D.sp.X j) (lineNeg D) where
  iA := frameMat _ _ (LinearMap.inl D.host.E _ _)
  iB := frameMat _ _ (LinearMap.inr D.host.E _ _)
  isoA := gram_frameMat (isIsomEmb_inl _ _)
  isoB := gram_frameMat (isIsomEmb_inr _ _)
  orth := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat, col_frameMat]
    change (D.sp.X j).hT 0 _ + (lineNeg D).hT _ 0 = 0
    rw [map_zero, map_zero, LinearMap.zero_apply, add_zero]
  rank_add := rfl

section Rel

variable {j : ℕ} (hj : j < D.R.m)
include hj

theorem hT_X_e {i : ℕ} (hi : i < rho D j) (x : (D.sp.X j).V) : (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (F.e j i)) = 0 := by
  have h := (F.aux j hj).2.2 x i (by unfold rho at hi; omega)
  unfold adaptedVector at h
  rwa [if_pos (show i < (D.R.m - 1 - j) / 2 from hi)] at h

theorem hT_X_ev {i : ℕ} (hi : i < rho D j) (x : (D.sp.X j).V) : (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (F.ev j i)) = 0 := by
  unfold rho at hi
  have h := (F.aux j hj).2.2 x (D.R.m - 1 - j - 1 - i) (by omega)
  unfold adaptedVector at h
  rwa [if_neg (by omega), if_neg (by omega), show D.R.m - 1 - j - 1 - (D.R.m - 1 - j - 1 - i) = i by omega] at h

theorem hT_X_alt (he : Even j) (x : (D.sp.X j).V) : (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (F.z j)) = 0 := by
  have hc := odd_c hj he
  have h := (F.aux j hj).2.2 x ((D.R.m - 1 - j) / 2) (by omega)
  unfold adaptedVector at h
  rwa [if_neg (lt_irrefl _), if_pos ⟨hc, rfl⟩] at h

theorem z_norm (he : Even j) : (D.sp.Y j).hT (vecY j (F.z j)) (vecY j (F.z j)) = -(D.sp.T : D.host.E) :=
  ((F.aux j hj).2.1 (odd_c hj he)).1

theorem embedding_line_sum_orthogonal (he : Even j) {v : (D.sp.Y j).V} (h1 : ∀ x, (D.sp.Y j).hT (D.sp.iXY j x) v = 0)
    (h2 : (D.sp.Y j).hT (vecY j (F.z j)) v = 0) (w : (V0 D j).V) : (D.sp.Y j).hT (F.embeddingLineSum j w) v = 0 := by
  change (D.sp.Y j).hT (D.sp.iXY j w.1 + lineMap true (D.sp.Y j) (vecY j (F.z j)) w.2) v = 0
  rw [map_add, LinearMap.add_apply, h1, lineMap_apply, LinearMap.map_smulₛₗ₂, h2, smul_zero, add_zero]

theorem embedding_line_sum_isometry (he : Even j) : HSpace.IsIsomEmb (V0 D j) (D.sp.Y j) (F.embeddingLineSum j) := fun a b => by
  have h1 : ∀ x c, (D.sp.Y j).hT (D.sp.iXY j x) (lineMap true (D.sp.Y j) (vecY j (F.z j)) c) = 0 := fun x c => by
    rw [lineMap_apply, map_smul, F.hT_X_alt hj he, smul_zero]
  have h2 := lineMap_isom (neg := true) (F.z_norm hj he)
  change (D.sp.Y j).hT (D.sp.iXY j a.1 + lineMap true (D.sp.Y j) (vecY j (F.z j)) a.2)
    (D.sp.iXY j b.1 + lineMap true (D.sp.Y j) (vecY j (F.z j)) b.2) = (D.sp.X j).hT a.1 b.1 + (lineNeg D).hT a.2 b.2
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h1, hT_symm_zero _ (h1 _ _), D.sp.iXY_isom j hj, h2,
    add_zero, zero_add]

variable {r : ℕ} (hr : r = rho D j)
include hr

theorem col_col : (F.colMat j r)ᴴ * (D.sp.Y j).gram * F.colMat j r = 0 := by
  subst hr
  refine Matrix.ext fun i l => (gram_cols _ _ _ i l).trans ((F.aux j hj).1 i i.2 l l.2).2.1

theorem dual_dual : (F.dualMat j r)ᴴ * (D.sp.Y j).gram * F.dualMat j r = 0 := by
  subst hr
  refine Matrix.ext fun i l => (gram_cols _ _ _ i l).trans ((F.aux j hj).1 i i.2 l l.2).2.2

theorem dual_col : (F.dualMat j r)ᴴ * (D.sp.Y j).gram * F.colMat j r = 1 := by
  subst hr
  refine Matrix.ext fun i l => (gram_cols _ _ _ i l).trans ?_
  refine ((D.sp.Y j).herm.eq _ _).symm.trans ?_
  refine (congrArg (starRingEnd D.host.E) ((F.aux j hj).1 l l.2 i i.2).1).trans ?_
  rw [Matrix.one_apply]
  by_cases h : i = l
  · subst h; simp
  · rw [if_neg h, if_neg fun e => h (Fin.ext e.symm), map_zero]

theorem skewDual_spec : (-D.host.xi0) • ((F.skewDual j r)ᴴ * (D.sp.Y j).gram * F.colMat j r) = 1 := by
  rw [skewDual, conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, F.dual_col hj hr, smul_smul, star_inv₀,
    GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, mul_inv_cancel₀ (neg_ne_zero.2 xi_zero_ne_zero), one_smul]

end Rel

def hypEven {j : ℕ} (hj : j < D.R.m) (he : Even j) {r : ℕ} (hr : r = rho D j) : HypDec (D.sp.Y j) (V0 D j) r where
  e := F.colMat j r
  e' := F.dualMat j r
  i₀ := frameMat _ _ (F.embeddingLineSum j)
  ee := F.col_col hj hr
  e'e' := F.dual_dual hj hr
  e'e := F.dual_col hj hr
  iso := gram_frameMat (F.embedding_line_sum_isometry hj he)
  i₀e := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat]
    exact F.embedding_line_sum_orthogonal hj he (F.hT_X_e hj (hr ▸ l.2)) (((F.aux j hj).2.1 (odd_c hj he)).2 l (hr ▸ l.2 : l.1 < rho D j)).1 _
  i₀e' := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat]
    exact F.embedding_line_sum_orthogonal hj he (F.hT_X_ev hj (hr ▸ l.2)) (((F.aux j hj).2.1 (odd_c hj he)).2 l (hr ▸ l.2 : l.1 < rho D j)).2 _
  rank_add := by
    have h := rank_Y j hj
    rw [if_pos he] at h
    change (D.sp.X j).rank + 1 + 2 * r = _
    omega

def hypOdd {j : ℕ} (hj : j < D.R.m) (ho : ¬ Even j) {r : ℕ} (hr : r = rho D j) : HypDec (D.sp.Y j) (D.sp.X j) r where
  e := F.colMat j r
  e' := F.dualMat j r
  i₀ := frameMat _ _ (D.sp.iXY j)
  ee := F.col_col hj hr
  e'e' := F.dual_dual hj hr
  e'e := F.dual_col hj hr
  iso := gram_frameMat (D.sp.iXY_isom j hj)
  i₀e := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat]
    exact F.hT_X_e hj (hr ▸ l.2) _
  i₀e' := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat]
    exact F.hT_X_ev hj (hr ▸ l.2) _
  rank_add := by
    have h := rank_Y j hj
    rw [if_neg ho] at h
    omega

def hypSrc {j : ℕ} (hj : j < D.R.m) (ho : ¬ Even j) {r : ℕ} (hr : r = rho D j) : HypDec (D.sp.Y j) (D.sp.X j) r :=
  scaleHyp (F.hypOdd hj ho hr) (srcScal D j) (srcScal_ne j)

def orthTop : OrthDec (D.sp.X D.R.m) D.sp.X' (linePos D) where
  iA := frameMat _ _ D.sp.iX'
  iB := frameMat _ _ (lineMap false _ F.ztop)
  isoA := gram_frameMat D.sp.iX'_isom
  isoB := gram_frameMat (lineMap_isom F.ztop_norm)
  orth := Matrix.ext fun i l => by
    rw [gram_cols, col_frameMat, col_frameMat, lineMap_frame]
    have h0 : (D.sp.X D.R.m).hT (D.sp.iX' (D.sp.X'.frame l)) F.ztop = 0 := by
      rw [ztop, map_smul, D.sp.z_orth, smul_zero]
    exact hT_symm_zero _ h0
  rank_add := by
    have h1 := D.sp.X_rank D.R.m le_rfl
    have h2 := D.sp.X'_rank
    have h3 := D.R.two_le_m
    have h4 : D.R.m * (D.R.t + 1) = D.R.m * D.R.t + D.R.m := by ring
    simp only [Ranks.N, Ranks.rankX', Ranks.r] at h1 h2
    change D.sp.X'.rank + 1 = _
    omega

def hypTop (D : D7) : HypDec (D.sp.Y D.R.m) D.sp.X' 0 where
  e := 0
  e' := 0
  i₀ := frameMat _ _ D.sp.eYm.toLinearMap
  ee := Matrix.ext fun i => i.elim0
  e'e' := Matrix.ext fun i => i.elim0
  e'e := Matrix.ext fun i => i.elim0
  iso := gram_frameMat D.sp.eYm_isom
  i₀e := Matrix.ext fun _ l => l.elim0
  i₀e' := Matrix.ext fun _ l => l.elim0
  rank_add := by rw [D.sp.Y_rank D.R.m le_rfl, D.sp.X'_rank]; rfl

theorem frameMat_iXY (j : ℕ) : frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j) =
    frameMat (D.sp.Y j) (V0 D j) (F.embeddingLineSum j) * (orthogonalDecompLineSum D j).iA := by
  rw [← F.embedding_line_sum_inl j]; exact frameMat_comp _ _ _ _ _

theorem frameMat_alt (j : ℕ) : frameMat (D.sp.Y j) (V0 D j) (F.embeddingLineSum j) *ᵥ vecB (orthogonalDecompLineSum D j) (fun _ => 1) = F.z j := by
  rw [vecB, Matrix.mulVec_mulVec]
  refine Eq.trans (congrArg (· *ᵥ fun _ => (1 : D.host.E))
    (frameMat_comp (D.sp.Y j) (V0 D j) (lineNeg D) (F.embeddingLineSum j) (LinearMap.inr D.host.E _ _)).symm) ?_
  apply (D.sp.Y j).frame.equivFun.symm.injective
  have h := col_frameMat (D.sp.Y j) (lineNeg D) (F.embeddingLineSum j ∘ₗ LinearMap.inr D.host.E _ _) 0
  have h2 : (F.embeddingLineSum j ∘ₗ LinearMap.inr D.host.E _ _) ((lineNeg D).frame 0) = vecY j (F.z j) := by
    rw [embeddingLineSum, LinearMap.coprod_inr]; exact lineMap_frame _ _ _ _
  refine Eq.trans (congrArg _ (funext fun k => ?_)) (h.trans h2)
  simp only [Matrix.mulVec, dotProduct, mul_one]
  exact Fin.sum_univ_one _

def besDat {j : ℕ} (hj : j < D.R.m) (he : Even j) : BesDat (D.sp.X j) (D.sp.Y j) (D.sp.iXY j) :=
  toBesDat (F.hypEven hj he rfl) (orthogonalDecompLineSum D j) (isLineVec_lineT true) one_ne_zero (D.sp.iXY j) (F.frameMat_iXY j)

theorem besDat_rho {j : ℕ} (hj : j < D.R.m) (he : Even j) : (F.besDat hj he).ρ = rho D j := rfl

theorem besDat_e {j : ℕ} (hj : j < D.R.m) (he : Even j) : (F.besDat hj he).e = F.colMat j (rho D j) := rfl

theorem besDat_alt {j : ℕ} (hj : j < D.R.m) (he : Even j) : (F.besDat hj he).z = F.z j := F.frameMat_alt j

theorem besDat_c {j : ℕ} (hj : j < D.R.m) (he : Even j) (i) : (F.besDat hj he).c i = 1 := rfl

theorem besDat_y {j : ℕ} (hj : j < D.R.m) (he : Even j) : ((F.besDat hj he).y : GA D (D.sp.Y j)) = 1 := rfl

theorem isFrame0_even {j : ℕ} (hj : j < D.R.m) (he : Even j) {r : ℕ} (hr : r = rho D j) :
    IsFrame0 (D.sp.Y j) (F.colMat j r) (F.dualMat j r) (V0 D j) (frameMat _ _ (F.embeddingLineSum j)) :=
  isFrame0_hyp (F.hypEven hj he hr)

theorem isFrame0_odd {j : ℕ} (hj : j < D.R.m) (ho : ¬ Even j) {r : ℕ} (hr : r = rho D j) :
    IsFrame0 (D.sp.Y j) (F.colMat j r) (F.dualMat j r) (D.sp.X j) (frameMat _ _ (D.sp.iXY j)) :=
  isFrame0_hyp (F.hypOdd hj ho hr)

theorem isFrame_source_odd {j : ℕ} (hj : j < D.R.m) (ho : ¬ Even j) {r : ℕ} (hr : r = rho D j) :
    IsFrame0 (D.sp.Y j) (F.srcMat j r) (F.srcDual j r) (D.sp.X j) (frameMat _ _ (D.sp.iXY j)) :=
  isFrame0_hyp (F.hypSrc hj ho hr)

def embeddingIntoLineSum (D : D7) (j : ℕ) : GA D (D.sp.X j) →* GA D (V0 D j) := (orthogonalDecompLineSum D j).emb.comp (MonoidHom.inl _ _)

def emb (j : ℕ) : GA D (D.sp.X j) →* GA D (D.sp.Y j) :=
  if hj : j < D.R.m then
    (if he : Even j then embA (F.hypEven hj he rfl) (orthogonalDecompLineSum D j) else (F.hypOdd hj he rfl).emb0)
  else 1

def embYm (D : D7) : GA D D.sp.X' →* GA D (D.sp.Y D.R.m) := (hypTop D).emb0

def embTop : GA D D.sp.X' →* GA D (D.sp.X D.R.m) := F.orthTop.emb.comp (MonoidHom.inl _ _)

abbrev grpN (j : ℕ) : Subgroup (GA D (D.sp.Y j)) := NFlag (D.sp.Y j) (F.colMat j (rho D j))

def grpR (j : ℕ) : Subgroup (GA D (D.sp.Y j)) := F.grpN j ⊔ (F.emb j).range

def psiN (ψ : AddChar (AF D.host.F) ℂ) (j : ℕ) : GA D (D.sp.Y j) → ℂ :=
  if h : j < D.R.m ∧ Even j then besChar ψ (F.besDat h.1 h.2) else psiU ψ (D.sp.Y j) (F.colMat j (rho D j))

section Grp

variable {j : ℕ} (hj : j < D.R.m) (ψ : AddChar (AF D.host.F) ℂ)
include hj

theorem emb_even (he : Even j) (h : GA D (D.sp.X j)) : F.emb j h = (F.hypEven hj he rfl).emb0 (embeddingIntoLineSum D j h) := by
  rw [emb, dif_pos hj, dif_pos he]; rfl

theorem emb_odd (ho : ¬ Even j) : F.emb j = (F.hypOdd hj ho rfl).emb0 := by
  rw [emb, dif_pos hj, dif_neg ho]

theorem continuous_emb : Continuous (F.emb j) := by
  by_cases he : Even j
  · rw [show ⇑(F.emb j) = _ from funext (F.emb_even hj he)]
    exact (F.hypEven hj he rfl).continuous_embed.comp ((orthogonalDecompLineSum D j).continuous_emb.comp (Continuous.prodMk_left 1))
  · rw [F.emb_odd hj he]; exact HypDec.continuous_embed _

theorem emb_injective : Function.Injective (F.emb j) := by
  by_cases he : Even j
  · intro a b h
    rw [F.emb_even hj he, F.emb_even hj he] at h
    exact (Prod.ext_iff.1 ((orthogonalDecompLineSum D j).emb_injective ((F.hypEven hj he rfl).wittDecomp_anisotropicEmbedding_injective h))).1
  · rw [F.emb_odd hj he]; exact HypDec.wittDecomp_anisotropicEmbedding_injective _

theorem emb_mem_GQ {h : GA D (D.sp.X j)} (hh : h ∈ GQ (D.sp.X j)) : F.emb j h ∈ GQ (D.sp.Y j) := by
  by_cases he : Even j
  · rw [F.emb_even hj he]
    exact HypDec.wittDecomp_anisotropicEmbedding_mem_rationalPoints _ ((orthogonalDecompLineSum D j).emb_mem_GQ hh (one_mem _))
  · rw [F.emb_odd hj he]; exact HypDec.wittDecomp_anisotropicEmbedding_mem_rationalPoints _ hh

theorem isLeviEmb_even (he : Even j) (h : GA D (D.sp.X j)) : IsLeviEmb (D.sp.Y j) (F.colMat j (rho D j))
    (F.dualMat j (rho D j)) (V0 D j) (frameMat _ _ (F.embeddingLineSum j)) (embeddingIntoLineSum D j h) (F.emb j h) := by
  rw [F.emb_even hj he]; exact isLeviEmb_witt_embedding (F.hypEven hj he rfl) _

theorem isLeviEmb_odd (ho : ¬ Even j) (h : GA D (D.sp.X j)) : IsLeviEmb (D.sp.Y j) (F.colMat j (rho D j))
    (F.dualMat j (rho D j)) (D.sp.X j) (frameMat _ _ (D.sp.iXY j)) h (F.emb j h) := by
  rw [F.emb_odd hj ho]; exact isLeviEmb_witt_embedding (F.hypOdd hj ho rfl) _

theorem isLeviEmb_source_frame_odd (ho : ¬ Even j) (h : GA D (D.sp.X j)) : IsLeviEmb (D.sp.Y j) (F.srcMat j (rho D j))
    (F.srcDual j (rho D j)) (D.sp.X j) (frameMat _ _ (D.sp.iXY j)) h (F.emb j h) := by
  rw [F.emb_odd hj ho, ← witt_embedding_scale_invariant _ (srcScal D j) (srcScal_ne j)]
  exact isLeviEmb_witt_embedding (F.hypSrc hj ho rfl) _

theorem grpN_alt : NFlag (D.sp.Y j) (F.srcMat j (rho D j)) = F.grpN j := by
  by_cases he : Even j
  · rw [F.srcMat_even he]
  · exact flagN_scaleHyp (F.hypOdd hj he rfl) _ (srcScal_ne j)

theorem conj_mem_grpN (h : GA D (D.sp.X j)) {n : GA D (D.sp.Y j)} (hn : n ∈ F.grpN j) :
    F.emb j h * n * (F.emb j h)⁻¹ ∈ F.grpN j := by
  by_cases he : Even j
  · rw [F.emb_even hj he]; exact conj_mem_flagN (F.hypEven hj he rfl) _ hn
  · rw [F.emb_odd hj he]; exact conj_mem_flagN (F.hypOdd hj he rfl) _ hn

theorem eq_one_of_emb_mem {h : GA D (D.sp.X j)} (hh : F.emb j h ∈ F.grpN j) : h = 1 := by
  by_cases he : Even j
  · apply F.emb_injective hj
    rw [F.emb_even hj he] at hh
    rw [F.emb_even hj he, eq_one_of_levi_embedding_mem_flag (F.hypEven hj he rfl) hh, map_one, map_one]
  · rw [F.emb_odd hj he] at hh; exact eq_one_of_levi_embedding_mem_flag (F.hypOdd hj he rfl) hh

theorem mem_grpR {g : GA D (D.sp.Y j)} : g ∈ F.grpR j ↔ ∃ n ∈ F.grpN j, ∃ h, g = n * F.emb j h := by
  refine ⟨fun hg => ?_, ?_⟩
  · let K : Subgroup (GA D (D.sp.Y j)) :=
      { carrier := {g | ∃ n ∈ F.grpN j, ∃ h, g = n * F.emb j h}
        one_mem' := ⟨1, one_mem _, 1, by rw [map_one, one_mul]⟩
        mul_mem' := by
          rintro _ _ ⟨n, hn, h, rfl⟩ ⟨n', hn', h', rfl⟩
          exact ⟨_, mul_mem hn (F.conj_mem_grpN hj h hn'), h * h', by rw [map_mul]; group⟩
        inv_mem' := by
          rintro _ ⟨n, hn, h, rfl⟩
          exact ⟨_, F.conj_mem_grpN hj h⁻¹ (inv_mem hn), h⁻¹, by rw [map_inv]; group⟩ }
    have : F.grpR j ≤ K := sup_le (fun n hn => ⟨n, hn, 1, by rw [map_one, mul_one]⟩)
      (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, (one_mul _).symm⟩)
    exact this hg
  · rintro ⟨n, hn, h, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem psiN_even (he : Even j) : F.psiN ψ j = besChar ψ (F.besDat hj he) := dif_pos ⟨hj, he⟩

omit hj in
theorem psiN_odd (ho : ¬ Even j) : F.psiN ψ j = psiU ψ (D.sp.Y j) (F.colMat j (rho D j)) := dif_neg fun h => ho h.2

theorem psiN_even_eq (he : Even j) {n : GA D (D.sp.Y j)} (hn : n ∈ F.grpN j) :
    F.psiN ψ j n = psiBes ψ (F.hypEven hj he rfl) 1 (vecB (orthogonalDecompLineSum D j) fun _ => 1) n := by
  rw [F.psiN_even hj ψ he]; exact besChar_toBesDat _ _ ψ _ _ _ _ hn

theorem psiN_odd_eq (ho : ¬ Even j) {n : GA D (D.sp.Y j)} (hn : n ∈ F.grpN j) :
    F.psiN ψ j n = psiFlag ψ (F.hypOdd hj ho rfl) n := by
  rw [F.psiN_odd ψ ho]; exact psiU_eq_psiFlag (F.hypOdd hj ho rfl) ψ hn

theorem psiU_alt (ho : ¬ Even j) {n : GA D (D.sp.Y j)} (hn : n ∈ F.grpN j) :
    psiU ψ (D.sp.Y j) (F.srcMat j (rho D j)) n = F.psiN ψ j n := by
  rw [F.psiN_odd_eq hj ψ ho hn]
  refine (psiU_eq_psiFlag (F.hypSrc hj ho rfl) ψ ((F.grpN_alt hj).ge hn)).trans ?_
  rw [psiFlag, psiFlag, hypSrc, blockX_scaleHyp]

theorem psiN_mul {n n' : GA D (D.sp.Y j)} (hn : n ∈ F.grpN j) (hn' : n' ∈ F.grpN j) :
    F.psiN ψ j (n * n') = F.psiN ψ j n * F.psiN ψ j n' := by
  by_cases he : Even j
  · rw [F.psiN_even_eq hj ψ he hn, F.psiN_even_eq hj ψ he hn', F.psiN_even_eq hj ψ he (mul_mem hn hn')]
    exact psiBes_mul _ ψ _ _ hn hn'
  · rw [F.psiN_odd_eq hj ψ he hn, F.psiN_odd_eq hj ψ he hn', F.psiN_odd_eq hj ψ he (mul_mem hn hn')]
    exact psiFlag_mul _ ψ hn hn'

theorem psiN_rat {s : ℤ} (hψ : IsStdChar D ψ s) {n : GA D (D.sp.Y j)} (hn : n ∈ F.grpN j) (hq : n ∈ GQ (D.sp.Y j)) :
    F.psiN ψ j n = 1 := by
  by_cases he : Even j
  · rw [F.psiN_even_eq hj ψ he hn]; exact psiBes_rat _ ψ (psiRat_of_isStdChar ψ hψ) _ _ hq
  · rw [F.psiN_odd_eq hj ψ he hn, psiFlag_eq]; exact psiBes_rat _ ψ (psiRat_of_isStdChar ψ hψ) _ _ hq

theorem psiN_conj (h : GA D (D.sp.X j)) {n : GA D (D.sp.Y j)} (hn : n ∈ F.grpN j) :
    F.psiN ψ j (F.emb j h * n * (F.emb j h)⁻¹) = F.psiN ψ j n := by
  have hn' := F.conj_mem_grpN hj h hn
  by_cases he : Even j
  · rw [F.psiN_even_eq hj ψ he hn, F.psiN_even_eq hj ψ he hn', F.emb_even hj he]
    refine psiBes_conj _ ψ _ _ _ ?_ n
    have e := (orthogonalDecompLineSum D j).emb_jB h⁻¹ 1
    rw [mt_one, Matrix.mul_one] at e
    rw [← map_inv, vecB, ratV_mulVec, Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ _) e
  · rw [F.psiN_odd_eq hj ψ he hn, F.psiN_odd_eq hj ψ he hn', F.emb_odd hj he, psiFlag_eq, psiFlag_eq]
    refine psiBes_conj _ ψ _ _ _ ?_ n
    have e : ratV (0 : Fin (D.sp.X j).rank → D.host.E) = 0 := funext fun _ => map_zero _
    rw [e, Matrix.mulVec_zero]

end Grp

theorem isEmbHom_emb {j : ℕ} (hj : j < D.R.m) : IsEmbHom (D.sp.iXY j) (F.emb j) := fun h => by
  by_cases he : Even j
  · rw [emb, dif_pos hj, dif_pos he]; exact embRel_embA _ _ _ (F.frameMat_iXY j) h
  · rw [F.emb_odd hj he]; exact HypDec.embRel_isometric_embedding _ h _ rfl

theorem isEmbHom_embedding_into_line_sum (j : ℕ) : IsEmbHom (B := V0 D j) (LinearMap.inl D.host.E _ _) (embeddingIntoLineSum D j) :=
  fun h => (orthogonalDecompLineSum D j).embRel_left _ rfl h

theorem isEmbHom_embYm : IsEmbHom D.sp.eYm.toLinearMap (embYm D) := fun h => (hypTop D).embRel_isometric_embedding h _ rfl

theorem isEmbHom_embTop : IsEmbHom D.sp.iX' F.embTop := fun h => F.orthTop.embRel_left _ rfl h

theorem isIsoSub_colMat (j : ℕ) : IsIsoSub (D.sp.Y j) (F.colMat j (rho D j)) := by
  by_cases hj : j < D.R.m
  · by_cases he : Even j
    · exact (F.isFrame0_even hj he rfl).1
    · exact (F.isFrame0_odd hj he rfl).1
  · haveI : IsEmpty (Fin (rho D j)) := by rw [rho_eq_zero (by omega)]; infer_instance
    exact ⟨linearIndependent_empty_type, Matrix.ext fun i => isEmptyElim i⟩

def IsBase : Prop :=
  (∀ i : Fin D.R.rS, vecY 0 (F.e 0 i) = D.sp.hypE i ∧ vecY 0 (F.ev 0 i) = D.sp.hypF i) ∧ vecY 0 (F.z 0) = D.sp.zm

def std (D : D7) : Frames D where
  e := GlobalTheory.NormalFramesLevels.eC D
  ev := GlobalTheory.NormalFramesLevels.evC D
  z := GlobalTheory.NormalFramesLevels.zC D
  lam := (exists_topScalar D).choose
  aux := GlobalTheory.NormalFramesLevels.normal_frame_level_conditions_C
  lam_norm := (exists_topScalar D).choose_spec

theorem std_isBase (D : D7) : (std D).IsBase := by
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩ <;>
    simp only [std, GlobalTheory.NormalFramesLevels.eC, GlobalTheory.NormalFramesLevels.evC, GlobalTheory.NormalFramesLevels.zC,
      Formalism.IndefR.Seed.Frm.vecY_repr, GlobalTheory.NormalFramesLevels.normalFrameVectorSequences, Fin.is_lt, dif_pos, Fin.eta]

def withTop (h : (D.sp.X D.R.m).hT D.sp.z D.sp.z = (D.sp.T : D.host.E)) : Frames D :=
  { F with lam := 1, lam_norm := by rw [star_one, one_mul, one_mul, h] }

instance : Inhabited (Frames D) := ⟨std D⟩

end Frames

structure Meas (F : Frames D) where
  μY : ∀ j, Measure (GA D (D.sp.Y j))
  fdY : ∀ j, Set (GA D (D.sp.Y j))
  μX : ∀ j, Measure (GA D (D.sp.X j))
  fdX : ∀ j, Set (GA D (D.sp.X j))
  μX' : Measure (GA D D.sp.X')
  fdX' : Set (GA D D.sp.X')
  μN : ∀ j, Measure (F.grpN j)
  fdN : ∀ j, Set (F.grpN j)
  μU : ∀ r, Measure (SUp D r)
  fdU : ∀ r, Set (SUp D r)
  μM : ∀ a b, Measure (Mx D a b)
  fdM : ∀ a b, Set (Mx D a b)
  quotY : ∀ j, IsQuotPair (D.sp.Y j) (μY j) (fdY j)
  quotX : ∀ j, IsQuotPair (D.sp.X j) (μX j) (fdX j)
  quotX' : IsQuotPair D.sp.X' μX' fdX'
  unitN : ∀ j, GlobalTheory.Per.IsUnitN (D.sp.Y j) (F.colMat j (rho D j)) (μN j) (fdN j)
  unitU : ∀ r, IsUPair r (μU r) (fdU r)
  unitM : ∀ a b, IsCovolOne (Formalism.IndefR.Eqv.ratMx D a b) (μM a b) (fdM a b)
  tieLast : ∀ j, j + 1 = D.R.m → μY j = (μX j).map (F.emb j)
  tieTop : μY D.R.m = μX'.map (Frames.embYm D)

theorem nonempty_meas (F : Frames D) : Nonempty (Meas F) := by
  choose μY fdY hY using fun j => exists_isQuotPair (D.sp.Y j)
  have hX : ∀ j, ∃ μ 𝓕, IsQuotPair (D.sp.X j) μ 𝓕 ∧ (j + 1 = D.R.m → μY j = μ.map (F.emb j)) := fun j => by
    by_cases h : j + 1 = D.R.m
    · have hj : j < D.R.m := by omega
      have ho : ¬ Even j := fun he => by
        have := D.R.m_even
        rw [← h, Nat.even_add_one] at this
        exact this he
      obtain ⟨μ, 𝓕, h1, h2⟩ := exists_pull (F.hypOdd hj ho rfl) (rho_eq_zero (by omega)) (μY j) (hY j).1
      exact ⟨μ, 𝓕, h1, fun _ => by rw [F.emb_odd hj ho]; exact h2⟩
    · obtain ⟨μ, 𝓕, h1⟩ := exists_isQuotPair (D.sp.X j)
      exact ⟨μ, 𝓕, h1, fun h' => absurd h' h⟩
  choose μX fdX hX1 hX2 using hX
  obtain ⟨μX', fdX', h1, h2⟩ := exists_pull (Frames.hypTop D) rfl (μY D.R.m) (hY D.R.m).1
  choose μN fdN hN using fun j => GlobalTheory.Per.UnitN.exists_isUnitN D (D.sp.Y j) _ _ (F.isIsoSub_colMat j)
  choose μU fdU hU using fun r => exists_isUPair (D := D) r
  choose μM fdM hM using fun a b => exists_isCovolOne D a b
  exact ⟨⟨μY, fdY, μX, fdX, μX', fdX', μN, fdN, μU, fdU, μM, fdM, hY, hX1, h1, hN, hU, hM, hX2, h2⟩⟩

namespace Meas

variable {F : Frames D} (M : Meas F)

theorem isNPair {j : ℕ} (hj : j < D.R.m) (he : Even j) : IsNPair (F.besDat hj he) (M.μN j) (M.fdN j) := M.unitN j

def IsCut (j : ℕ) (β : GA D (D.sp.Y j) → ℝ) : Prop :=
  IsCutoffB (D.sp.Y j) (D.sp.X j) (F.colMat j (rho D j)) (F.emb j) (M.μN j) (M.μX j) β

def IsCutFam (β : ∀ j, GA D (D.sp.Y j) → ℝ) : Prop := ∀ j < D.R.m, M.IsCut j (β j)

def quotInt (j : ℕ) (β : GA D (D.sp.Y j) → ℝ) (Φ : GA D (D.sp.Y j) → ℂ) : ℂ := cutInt (D.sp.Y j) (M.μY j) β Φ

def cutMeas (j : ℕ) (β : GA D (D.sp.Y j) → ℝ) : Measure (GA D (D.sp.Y j)) :=
  (M.μY j).withDensity fun g => ENNReal.ofReal (β g)

theorem integral_cutMeas {j : ℕ} {β : GA D (D.sp.Y j) → ℝ} (hβ : M.IsCut j β) (Φ : GA D (D.sp.Y j) → ℂ) :
    ∫ g, Φ g ∂(M.cutMeas j β) = M.quotInt j β Φ := by
  refine (integral_withDensity_eq_integral_smul (f := fun g => (β g).toNNReal) hβ.2.1.real_toNNReal Φ).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hβ.1 g), Complex.real_smul]

theorem integrable_cutMeas {j : ℕ} {β : GA D (D.sp.Y j) → ℝ} (hβ : M.IsCut j β) (Φ : GA D (D.sp.Y j) → ℂ) :
    Integrable Φ (M.cutMeas j β) ↔ Integrable (fun g => (β g : ℂ) * Φ g) (M.μY j) := by
  refine (integrable_withDensity_iff_integrable_smul (f := fun g => (β g).toNNReal) hβ.2.1.real_toNNReal).trans ?_
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hβ.1 _), Complex.real_smul]

end Meas

theorem rho_step (j : ℕ) : (Odd j → rho D (j - 1) = rho D j) ∧
    (Even j → 2 ≤ j → j + 2 ≤ D.R.m → rho D (j - 1) = rho D j + 1) ∧ rho D 0 = D.R.rS := by
  have hm := Nat.even_iff.1 D.R.m_even
  simp only [rho, Ranks.rS, Nat.even_iff, Nat.odd_iff]
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> omega

example (D : D7) : (D.sp.Y 0).hT (vecY 0 ((Frames.std D).z 0)) (vecY 0 ((Frames.std D).z 0)) = -(D.sp.T : D.host.E) := by
  rw [(Frames.std_isBase D).2, D.sp.zm_norm]

example (F : Frames D) (ψ : AddChar (AF D.host.F) ℂ) {j : ℕ} (hj : j < D.R.m) (he : Even j)
    (b : Mx D (rho D j) (Frames.V0 D j).rank) : F.psiN ψ j ((F.hypEven hj he rfl).nB b) =
      psiE ψ (ell D (rho D j) ⬝ᵥ b *ᵥ ratV (vecB (Frames.orthogonalDecompLineSum D j) fun _ => 1)) := by
  rw [F.psiN_even_eq hj ψ he ((F.hypEven hj he rfl).nB_mem_NFlag b), psiBes_nB, map_one, one_mul]

example (F : Frames D) (ψ : AddChar (AF D.host.F) ℂ) {j : ℕ} (hj : j < D.R.m) (ho : ¬ Even j)
    (b : Mx D (rho D j) (D.sp.X j).rank) : F.psiN ψ j ((F.hypOdd hj ho rfl).nB b) = 1 := by
  rw [F.psiN_odd_eq hj ψ ho ((F.hypOdd hj ho rfl).nB_mem_NFlag b), psiFlag,
    blockX_of_fix _ ((F.hypOdd hj ho rfl).nB_jX b), upSum_one, psiE_zero]

example (D : D7) : Nonempty (Meas (Frames.std D)) := nonempty_meas _

end GlobalTheory.CompanionTheory.Chain

end
