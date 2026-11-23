import Formalism.LocalToGlobal.GlobalTheory.GL4.PacketOfFrameDegree
import Formalism.LocalToGlobal.GlobalTheory.GL4.PTenFrames
import Formalism.LocalToGlobal.Columns.BrpStarLatLattice

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GramSelf

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem gramJ_self_det (A : HLat K) (v : InfinitePlace K) : (gramJ A A.b v).det.re = (‖(A.X v).det‖ ^ 2)⁻¹ := by
  classical
  have h : ∀ i', (A.X v)⁻¹ *ᵥ vecAt A.b v (A.b i') = fun k => (A.X v)⁻¹ k i' := by
    intro i'
    funext k
    simp [vecAt, Matrix.mulVec, dotProduct, Finsupp.single_apply]
  have e : gramJ A A.b v = ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ := by
    ext i j
    simp only [gramJ, Matrix.of_apply, majAt, fcoord, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [h, h]
  have hz : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [show star z * z = ((Complex.normSq z : ℝ) : ℂ) by rw [Complex.normSq_eq_conj_mul_self]; rfl,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [e, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hz, norm_inv, inv_pow]

end GramSelf

section F

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem crd_fam (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)
    (a : Fin (D.R.N 0)) :
    crdQ CV c τ (∑ i, B i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) = famOf (Pi.basisFun D.what₂.LL (Fin (D.R.N 0))) B a := by
  ext j
  simp [crdQ, famOf, Basis.equivFun_apply, Finset.sum_apply, Pi.basisFun_apply,
    Finsupp.single_apply, Pi.single_apply]

theorem latOf_map_crd (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) :
    (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) => ∑ i, B i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)).map
        ((crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)).restrictScalars (𝓞 D.what₂.LL)) =
      latOf (K := D.what₂.LL) (famOf (Pi.basisFun D.what₂.LL (Fin (D.R.N 0))) B) := by
  simp only [latOf, Submodule.map_span, ← Set.range_comp]
  congr 1
  congr 1
  funext a
  exact crd_fam CV c τ B a

theorem q_frame_degree (D : D7) : QFrameDeg D := by
  intro u CV c τ
  classical
  have := (columnHypotheses D u).tc
  have hQ := CV.Q_good c τ
  have hn : 0 < D.R.N 0 := rank_zero_pos D
  haveI : Nonempty (Fin (D.R.N 0)) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (CV.Q c τ).ι := ⟨(CV.eQ c τ).symm ⟨0, hn⟩⟩
  have hfr : Module.finrank D.what₂.LL (CV.Q c τ).V = D.R.N 0 := by
    rw [Module.finrank_eq_card_basis (CV.Q c τ).b, Fintype.card_congr (CV.eQ c τ), Fintype.card_fin]
  choose bK hbK using fun p : FinPl D.what₂.LL => exists_basis_locP (toH p) hQ.2.1 hQ.2.2 hfr
  set g : FinPl D.what₂.LL → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
    fun p => ((CV.Q c τ).b.reindex (CV.eQ c τ)).toMatrix (bK p) with hgdef
  have hg : ∀ p, (g p).det ≠ 0 := fun p => by
    have := ((CV.Q c τ).b.reindex (CV.eQ c τ)).isUnit_det (bK p)
    rw [Basis.det_apply] at this
    exact this.ne_zero
  have hfam : ∀ p, (fun a : Fin (D.R.N 0) => ∑ i, g p i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) = bK p := fun p => by
    funext a
    have := ((CV.Q c τ).b.reindex (CV.eQ c τ)).sum_repr (bK p a)
    simpa [hgdef, Basis.toMatrix_apply, Basis.reindex_apply] using this
  have hloc : ∀ p, localization₂ (toH p).asIdeal (CV.Q c τ).L = localization₂ (toH p).asIdeal
      (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) => ∑ i, g p i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) := fun p => by
    rw [hfam p, hbK p]
  obtain ⟨-, -, hmuQ⟩ := mu_of_frames (CV.Q c τ) hQ (ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc)
  have hML := MQ_lattice CV c τ
  have hstdGood : (stdHL D.what₂.LL (MQ CV c τ)).Good := ⟨fun _ => by simp, hML.fg, hML.span_eq_top⟩
  let FS : FrameData (stdHL D.what₂.LL (MQ CV c τ)) (Fin (D.R.N 0)) :=
    { e := Pi.basisFun D.what₂.LL (Fin (D.R.N 0))
      Γ := g
      det_ne := hg
      loc := fun p => by
        show localization₂ (toH p).asIdeal (MQ CV c τ) = _
        ext z
        obtain ⟨q, rfl⟩ := (crdQ CV c τ).surjective z
        unfold MQ
        rw [mem_localization_map_equiv, hloc p, ← latOf_map_crd CV c τ (g p), mem_localization_map_equiv] }
  obtain ⟨-, -, hmuS⟩ := mu_of_frames (stdHL D.what₂.LL (MQ CV c τ)) hstdGood FS
  rw [brp_latK_mu D.what₂.LL (MQ CV c τ) hML.fg]
  have hQinf : infPart (fun v => (gramJ (CV.Q c τ) (ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc).e v).det.re) =
      -((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)) := by
    unfold infPart
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    beta_reduce
    rw [show ((ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc).e : (CV.Q c τ).ι → (CV.Q c τ).V) = (CV.Q c τ).b from rfl,
      gramJ_self_det, Real.log_inv]
  have hSinf : infPart (fun v => (gramJ (stdHL D.what₂.LL (MQ CV c τ)) FS.e v).det.re) = 0 := by
    unfold infPart
    rw [Finset.sum_eq_zero fun v _ => ?_, mul_zero]
    beta_reduce
    rw [show (FS.e : Fin (D.R.N 0) → (Fin (D.R.N 0) → D.what₂.LL)) = (stdHL D.what₂.LL (MQ CV c τ)).b from rfl,
      gramJ_self_det]
    simp
  have hfin : finPart (fun p => ((ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc).Γ p).det) = finPart (fun p => (FS.Γ p).det) := by
    congr 1
    funext p
    exact Matrix.det_submatrix_equiv_self _ _
  have hcQ : (Fintype.card (CV.Q c τ).ι : ℝ) = (D.R.N 0 : ℝ) := by
    rw [Fintype.card_congr (CV.eQ c τ), Fintype.card_fin]
  rw [hcQ] at hmuQ
  rw [Fintype.card_fin] at hmuS
  rw [hmuQ, hmuS, hQinf, hSinf, hfin]
  ring

theorem class_map_archimedean (D : D7) : ClassMapT D :=
  classMapT_of (q_frame_degree D)

theorem third_link_family : Link6F :=
  Link6F_of_frameDeg q_frame_degree

theorem packet_family : KudlaFamilyOfMinkowskiTransference :=
  packet_of_third_proposition third_link_family

end F

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
