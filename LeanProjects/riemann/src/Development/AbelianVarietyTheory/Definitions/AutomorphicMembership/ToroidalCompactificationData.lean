import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMoebZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

section Domain

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)

def coW (f : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin j) (Fin j) ℂ :=
  (frameCo X hj f τ).toBlocks₁₁ - moeb (frameCo X hj f τ) 0 * (frameCo X hj f τ).toBlocks₂₁

def coOm (f : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin (r - j)) (Fin (r - j)) ℂ := (frameCo X hj f τ).toBlocks₂₂

theorem frameCo_eq (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) :
    frameCo X hj f τ = fromBlocks 1 (moeb (frameCo X hj f τ) 0) 0 1 *
      fromBlocks (coW X hj f τ) 0 (frameCo X hj f τ).toBlocks₂₁ (coOm X hj f τ) := by
  rw [fromBlocks_multiply, coW, coOm]
  conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj f τ)]
  simp [moeb_zero, nonsing_inv_mul_cancel_right _ _ (frameCo_isUnit₂₂ X hj hp hf τ)]

theorem isUnit_coOm (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) : IsUnit (coOm X hj f τ).det :=
  frameCo_isUnit₂₂ X hj hp hf τ

theorem isUnit_coW (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) : IsUnit (coW X hj f τ).det := by
  have h : IsUnit (frameCo X hj f τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ (det_x0F X τ).isUnit).mul (hf τ).1.isUnit
  rw [frameCo_eq X hj hp hf, det_mul, det_fromBlocks_zero₁₂] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)

theorem co_x0F (τ : X.Ψ) : coW X hj (x0F X) τ = 1 ∧ coOm X hj (x0F X) τ = 1 := by
  have e : frameCo X hj (x0F X) τ = fromBlocks 1 0 0 1 := by
    rw [frameCo, nonsing_inv_mul _ (det_x0F X τ).isUnit, fromBlocks_one, reindex_apply, submatrix_one_equiv]
  rw [coW, coOm, e, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp

theorem hodge_co (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : IsOrth X f) (τ : X.Ψ) :
    (coW X hj f τ)ᴴ * (hP (moeb (frameCo X hj f τ) 0))⁻¹ * coW X hj f τ = 1 ∧
      (coOm X hj f τ)ᴴ * hQ (moeb (frameCo X hj f τ) 0) * coOm X hj f τ = 1 := by
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp hf τ
  have h1 := hP_inv_moeb hg (zero_mem_hcDom _ _)
  have h2 := hQ_moeb hg (zero_mem_hcDom _ _)
  rw [jW, e] at h1
  rw [kapQ, e, Matrix.mul_zero, zero_add] at h2
  exact ⟨h1.trans (by simp [hP]), h2.trans (by simp [hQ])⟩

end Frames

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

instance FinalTheorems.smooth (s : FinalTheorems S κ) : SmoothOfRelativeDimension S.Dw.dim (genStr s.T.Z) := s.T.smooth

abbrev ToroidalCompactificationData (s : FinalTheorems S κ) : Type := OddPrimesWithRootsOfUnity s.T.Z

theorem Lv.relab_σ₀ (κ : Lv A) (τ : D.host.E →+* ℂ) : Formalism.L2.PjFree.relab κ.c κ.σ₀ τ = τ := rfl

theorem Sig.mult_psi (S : Sig A N j) (L : CmList A) (t : D.what₂.Tau) : S.Dw.mult (L.ψ t).1 = j :=
  (if_pos (L.ψ t).2).trans S.p_eq

theorem Sig.mult_conj (S : Sig A N j) (L : CmList A) (t : D.what₂.Tau) : S.Dw.mult (conjEmb (L.ψ t).1) = N - j :=
  (if_neg (GlobalTheory.AllWt.conj_not_mem (L.ψ t))).trans (by have := S.p_eq; have := S.rank_eq; omega)

namespace FinalTheorems

variable (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp)

abbrev fd : Data D.host.E N := (s.U κ.σ₀).X k

include s in

theorem j_le : j ≤ N := le_of_isUnf _ s.isUnf S.p_eq

abbrev lab : D.what₂.Tau ≃ (s.fd k).Ψ := cmEquiv _ s.isUnf L.ψ k

theorem p0_eq : (s.fd k).p0 = N - j := first_index_eq_of_unfolded _ s.isUnf S.p_eq k

abbrev zOf (f : (s.fd k).dom) : Pt D.what₂.Tau j (N - j) := domPt (s.fd k) s.j_le (s.lab L k) f.1

def framePt (f : (s.fd k).dom) : CxPts (genStr s.T.Z) κ.σ₀ := cxPt s.T.Z ((s.U κ.σ₀).un k f)

def lieFrame (f : (s.fd k).dom) : EigFrame s.T.Z κ.σ₀ ((s.framePt k f).1 ≫ genι s.T.Z) :=
  cxFrame s.T.Z ((s.U κ.σ₀).un k f)

open Classical in

def frameOver (z : Pt D.what₂.Tau j (N - j)) : (s.fd k).dom :=
  if h : ∃ f, s.zOf L k f = z then h.choose else ⟨x0F _, IW.orth_mem_dom _ _ (isOrth_x0F _)⟩

def toCpt (z : Pt D.what₂.Tau j (N - j)) : CxPts (genStr s.T.Z) κ.σ₀ := s.framePt k (s.frameOver L k z)

theorem zOf_mem (f : (s.fd k).dom) : s.zOf L k f ∈ DomI D.what₂.Tau j (N - j) := domPt_mem _ _ _ (s.p0_eq k) f.2

theorem zOf_frameOver {z : Pt D.what₂.Tau j (N - j)} (hz : z ∈ DomI D.what₂.Tau j (N - j)) :
    s.zOf L k (s.frameOver L k z) = z := by
  have h : ∃ f, s.zOf L k f = z := by
    obtain ⟨f, hf, e⟩ := FrameOnto.frame_onto _ N j (s.fd k) s.j_le _ (s.lab L k) (s.p0_eq k) z hz
    exact ⟨⟨f, hf⟩, e⟩
  rw [frameOver, dif_pos h]
  exact h.choose_spec

theorem framePt_eq {f f' : (s.fd k).dom} {g : D.what₂.Tau → GL (Fin j ⊕ Fin (N - j)) ℂ}
    (hg : g ∈ gammaU (s.fd k) s.j_le (s.lab L k))
    (h : moebI g (s.zOf L k f) = s.zOf L k f') : s.framePt k f = s.framePt k f' :=
  cxPt_congr (PointWell.pt_eq_of_ptOfFrame_eq _ _ _ _ _ _ _ N j _ s.isUnf S.p_eq _ (lt_of_lt_of_le two_pos S.two_le) L.ψ
    (invariantB _ _ (first_index_eq_of_unfolded _ s.isUnf S.p_eq) _) (fun _ _ => 1) κ.good_σ₀ k k f f'
    (congrArg (Sigma.mk k) (Quot.sound ⟨g, hg, h⟩)))

theorem toCpt_zOf (f : (s.fd k).dom) : s.toCpt L k (s.zOf L k f) = s.framePt k f :=
  s.framePt_eq L k (one_mem _)
    ((funext fun _ => PointWell.moeb_one _).trans (s.zOf_frameOver L k (s.zOf_mem L k f)))

theorem toCpt_moeb {g : D.what₂.Tau → GL (Fin j ⊕ Fin (N - j)) ℂ}
    (hg : g ∈ gammaU (s.fd k) s.j_le (s.lab L k)) {z : Pt D.what₂.Tau j (N - j)}
    (hz : z ∈ DomI D.what₂.Tau j (N - j)) : s.toCpt L k (moebI g z) = s.toCpt L k z :=
  (s.framePt_eq L k hg (by
    rw [s.zOf_frameOver L k hz, s.zOf_frameOver L k (z := moebI g z)
      fun t => moeb_mem (gammaU_le _ _ _ (s.p0_eq k) hg t trivial) (hz t)])).symm

theorem not_liesIn_toCpt (z : Pt D.what₂.Tau j (N - j)) : ¬ LiesIn (s.toCpt L k z) (genBd s.T.Z) := not_liesIn_cxPt _

end FinalTheorems

variable {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (L : CmList A)

def ToroidalCompactificationData.gramW (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : Matrix (Fin j) (Fin j) ℂ :=
  (x.gram (s.framePt k f) (s.lieFrame k f) (L.ψ t).1).submatrix
    (Fin.cast (S.mult_psi L t).symm) (Fin.cast (S.mult_psi L t).symm)

def ToroidalCompactificationData.gramOm (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : Matrix (Fin (N - j)) (Fin (N - j)) ℂ :=
  ((hodgeC (s.fd k) (s.lab L k) t : ℂ) ^ 2) •
    (dualGram (x.gram (s.framePt k f) (s.lieFrame k f) (conjEmb (L.ψ t).1))).submatrix
      (fun a => Fin.cast (S.mult_conj L t).symm a.rev) (fun a => Fin.cast (S.mult_conj L t).symm a.rev)

theorem ToroidalCompactificationData.gramW_posDef (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : (x.gramW L k f t).PosDef :=
  (x.gram_posDef _ _).submatrix (Fin.cast_injective _)

theorem ToroidalCompactificationData.gramOm_posDef (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : (x.gramOm L k f t).PosDef :=
  ((dualGram_posDef (x.gram_posDef _ _)).submatrix ((Fin.cast_injective _).comp Fin.rev_injective)).smul
    (pow_pos (Complex.zero_lt_real.2 (hodgeC_pos _ _ t)) 2)

theorem ToroidalCompactificationData.gram_hodge (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau)
    (h : ∀ τ, x.gram (s.framePt k f) (s.lieFrame k f) τ = (hodgeC (s.fd k) (s.lab L k) t : ℂ) • 1) :
    x.gramW L k f t = (hodgeC (s.fd k) (s.lab L k) t : ℂ) • 1 ∧
      x.gramOm L k f t = (hodgeC (s.fd k) (s.lab L k) t : ℂ) • 1 := by
  have h0 : (hodgeC (s.fd k) (s.lab L k) t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hodgeC_pos _ _ t).ne'
  constructor
  · ext a b
    simp [ToroidalCompactificationData.gramW, h, one_apply]
  · ext a b
    rw [ToroidalCompactificationData.gramOm, h, dualGram_smul_one h0]
    simp [one_apply, sq, h0]

def ToroidalCompactificationData.metW (k : s.Comp) (z : Pt D.what₂.Tau j (N - j)) (t : D.what₂.Tau) : Matrix (Fin j) (Fin j) ℂ :=
  ((coW (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹)ᴴ * x.gramW L k (s.frameOver L k z) t *
    (coW (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹

def ToroidalCompactificationData.metOm (k : s.Comp) (z : Pt D.what₂.Tau j (N - j)) (t : D.what₂.Tau) : Matrix (Fin (N - j)) (Fin (N - j)) ℂ :=
  ((coOm (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹)ᴴ * x.gramOm L k (s.frameOver L k z) t *
    (coOm (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹

theorem ToroidalCompactificationData.met_posDef (k : s.Comp) (z : Pt D.what₂.Tau j (N - j)) (t : D.what₂.Tau) :
    (x.metW L k z t).PosDef ∧ (x.metOm L k z t).PosDef :=
  ⟨(x.gramW_posDef L k _ t).conjTranspose_mul_mul_same (mulVec_injective_of_isUnit (isUnit_nonsing_inv_iff.2
    ((isUnit_iff_isUnit_det _).2 (isUnit_coW _ _ (s.p0_eq k) (s.frameOver L k z).2 _)))),
   (x.gramOm_posDef L k _ t).conjTranspose_mul_mul_same (mulVec_injective_of_isUnit (isUnit_nonsing_inv_iff.2
    ((isUnit_iff_isUnit_det _).2 (isUnit_coOm _ _ (s.p0_eq k) (s.frameOver L k z).2 _))))⟩

structure IsBdOf (B : s.Bd L) : Prop where
  m_eq : ∀ k, (B k).m = x.m
  nrm : ∀ k i, ∀ z ∈ DomI D.what₂.Tau j (N - j), (B k).nrm i z = x.nrm κ.σ₀ (Fin.cast (m_eq k) i) (s.toCpt L k z)
  kae : ∀ k W φ, IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W φ → ∀ z ∈ DomI D.what₂.Tau j (N - j),
    s.toCpt L k z ∈ W → ∀ ξ, ((B k).kae z ξ ξ).re = ddc (φ ∘ s.toCpt L k) z ξ
  cst : ∀ k, (B k).cst = x.cst
  metW : ∀ k f t, (coW (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * (B k).metW (s.zOf L k f) t *
    coW (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramW L k f t
  metOm : ∀ k f t, (coOm (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * (B k).metOm (s.zOf L k f) t *
    coOm (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramOm L k f t

def bdOf (h : ∃ B, IsBdOf x L B) : s.Bd L := h.choose

theorem isBdOf_bdOf (h : ∃ B, IsBdOf x L B) : IsBdOf x L (bdOf x L h) := h.choose_spec

namespace IsBdOf

variable {x L} {B B' : s.Bd L} (h : IsBdOf x L B) (k : s.Comp) {z : Pt D.what₂.Tau j (N - j)}
include h

theorem nrm_zOf (i : Fin (B k).m) (f : (s.fd k).dom) :
    (B k).nrm i (s.zOf L k f) = x.nrm κ.σ₀ (Fin.cast (h.m_eq k) i) (s.framePt k f) := by
  rw [h.nrm k i _ (s.zOf_mem L k f), s.toCpt_zOf]

theorem r_eq (hz : z ∈ DomI D.what₂.Tau j (N - j)) : (B k).r z = x.r κ.σ₀ (s.toCpt L k z) := by
  rw [BdData.r, OddPrimesWithRootsOfUnity.r, Fintype.prod_equiv (finCongr (h.m_eq k)) _ (fun i => x.nrm κ.σ₀ i (s.toCpt L k z))
    fun i => h.nrm k i z hz]

theorem m_ne_zero (hb : (genBd s.T.Z : Set (gen s.T.Z : Scheme.{0})).Nonempty) : (B k).m ≠ 0 :=
  fun h0 => hb.ne_empty (x.m_eq_zero_iff.1 ((h.m_eq k).symm.trans h0))

theorem nrm_unique (h' : IsBdOf x L B') (hz : z ∈ DomI D.what₂.Tau j (N - j)) (i : Fin (B k).m) :
    (B k).nrm i z = (B' k).nrm (Fin.cast ((h.m_eq k).trans (h'.m_eq k).symm) i) z :=
  (h.nrm k i z hz).trans (h'.nrm k (Fin.cast ((h.m_eq k).trans (h'.m_eq k).symm) i) z hz).symm

theorem met_eq (hz : z ∈ DomI D.what₂.Tau j (N - j)) (t : D.what₂.Tau) :
    (B k).metW z t = x.metW L k z t ∧ (B k).metOm z t = x.metOm L k z t := by
  have key : ∀ {n : Type} [Fintype n] [DecidableEq n] {T M G : Matrix n n ℂ}, IsUnit T.det →
      Tᴴ * M * T = G → M = (T⁻¹)ᴴ * G * T⁻¹ := fun hT e => by
    rw [← e, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hT, ← Matrix.mul_assoc, ← conjTranspose_mul,
      mul_nonsing_inv _ hT, conjTranspose_one, Matrix.one_mul]
  have h1 := h.metW k (s.frameOver L k z) t
  have h2 := h.metOm k (s.frameOver L k z) t
  rw [s.zOf_frameOver L k hz] at h1 h2
  exact ⟨key (isUnit_coW _ _ (s.p0_eq k) (s.frameOver L k z).2 _) h1,
    key (isUnit_coOm _ _ (s.p0_eq k) (s.frameOver L k z).2 _) h2⟩

theorem kae_unique (h' : IsBdOf x L B') (hz : z ∈ DomI D.what₂.Tau j (N - j)) : (B k).kae z = (B' k).kae z := by
  obtain ⟨W, φ, hW, hφ⟩ := (x.kae_kaehler κ.σ₀).1 (s.toCpt L k z)
  have e : ∀ ξ, ((B k).kae z - (B' k).kae z) ξ ξ = 0 := fun ξ => sub_eq_zero.2 (Complex.ext
    ((h.kae k W φ hφ z hz hW ξ).trans (h'.kae k W φ hφ z hz hW ξ).symm)
    ((Complex.conj_eq_iff_im.1 ((B k).kae_herm z hz ξ ξ).symm).trans
      (Complex.conj_eq_iff_im.1 ((B' k).kae_herm z hz ξ ξ).symm).symm))
  rw [← sub_eq_zero]
  generalize (B k).kae z - (B' k).kae z = b at e
  refine LinearMap.ext₂ fun ξ ζ => ?_
  have e1 := e (ξ + ζ)
  have e2 := e (ξ + Complex.I • ζ)
  simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, e, smul_eq_mul, Complex.conj_I,
    RingHom.id_apply] at e1 e2
  show b ξ ζ = 0
  linear_combination (1 / 2) * e1 + (Complex.I / 2) * e2 + ((b ξ ζ - b ζ ξ) / 2) * Complex.I_mul_I

end IsBdOf

end Domain

end GlobalTheory.ShFam
