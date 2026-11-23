import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaAtEqProdAhG
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ArchPhase
open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Matrix

variable {D : D7}

theorem gram_inv_eq (V : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) :
    (HSpace.gram V)⁻¹ = b * bᴴ := by
  have h1 : bᴴ * (HSpace.gram V * b) = 1 := by
    refine Matrix.ext fun a a' => ?_
    have := hb.1 a a'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Finset.mul_sum] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : (HSpace.gram V * b) * bᴴ = 1 := mul_eq_one_comm.1 h1
  rw [Matrix.mul_assoc] at h2
  exact Matrix.inv_eq_right_inv h2

theorem infPart_realPt (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    infPart D (realPt S T X i j) = infPart D (incA D (X i j)) := rfl

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [← h4, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

end GlobalTheory.ArchPhase

namespace GlobalTheory.ArchPhase
open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Matrix

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000

def hRat (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  Matrix.trace ((HSpace.gram S)⁻¹ * Yᴴ * HSpace.gram T * X)

theorem infPart_cA_realPt (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank)
    (j : Fin S.rank) : infPart D (cA D (realPt S T X i j)) = infPart D (incA D (star (X i j))) := by
  rw [GlobalTheory.PhaseReal.infPart_cA, infPart_realPt, ← GlobalTheory.PhaseReal.infPart_cA, GlobalTheory.DualPairCheck.cA_incA]

theorem infPart_hO_realPt (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    infPart D (hO S T (realPt S T X) (realPt S T Y)) = infPart D (incA D (hRat S T X Y)) := by
  rw [GlobalTheory.PhaseReal.hO_eq_trace, hRat]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply, infPart_realPt, infPart_cA_realPt]

theorem finPart_hO_realPt (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finPart D (hO S T (realPt S T X) (realPt S T Y)) = 0 := by
  have h : ∀ i j, finPart D (realPt S T X i j) = 0 := fun i j =>
    congrFun (congrFun (GlobalTheory.FrameConst.realPt_fin S T X) i) j
  simp only [hO, map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

theorem hermitian_column_sum_neg_mul_rearrange {n : ℕ} (ξ u : D.host.E) (v : Fin n → D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E) (c : Fin n) :
    - -ξ * ∑ x, u * -G x c * ReciprocityTheory.ChartRestriction.G.FD.cc (v x) = -(ξ * ((∑ j, star (v j) * G j c) * u)) := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hst : star (v x) = ReciprocityTheory.ChartRestriction.G.FD.cc (v x) := rfl
  rw [hst]
  ring

theorem sum_herm_eq (V W : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (r : ℕ)
    (hr : W.rank = r) (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (hX : ModelW W hr X)
    (Xm Ym : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    ∑ a, (-X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (fun m => ∑ n, Xm (Fin.cast hr.symm m) n * b n a)
        (fun m => ∑ n, Ym (Fin.cast hr.symm m) n * b n a)) = -(D.host.xi0 * hRat V W Xm Ym) := by
  subst hr
  obtain ⟨hG, hξ⟩ := hX
  have e1 : hRat V W Xm Ym = Matrix.trace ((Ym * b)ᴴ * HSpace.gram W * (Xm * b)) := by
    rw [hRat, gram_inv_eq V b hb, Matrix.conjTranspose_mul, Matrix.mul_assoc b, Matrix.mul_assoc b,
      Matrix.mul_assoc b, Matrix.trace_mul_comm b]
    simp only [Matrix.mul_assoc]
  rw [e1, hξ, hG, Matrix.trace, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.neg_apply,
    Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm,
    Equiv.refl_apply, Fin.cast_eq_self]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  exact hermitian_column_sum_neg_mul_rearrange (n := W.rank) _ _ (fun j : Fin W.rank => ∑ k : Fin V.rank, Ym j k * b k a) _ c

end GlobalTheory.ArchPhase

namespace GlobalTheory.ArchPhase
open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Matrix

set_option synthInstance.maxHeartbeats 400000 in

theorem psi_symplOH_realPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D)
    (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis V b → ∀ (r : ℕ) (hr : W.rank = r)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r), ModelW W hr X → ∀ (Xm Ym : Matrix (Fin W.rank) (Fin V.rank) D.host.E),
    ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W Xm) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W Ym)) =
      Complex.exp (Real.pi * Complex.I * ∑ a, ((Algebra.trace ℚ D.host.E (-X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm
        (fun m => ∑ n, Xm (Fin.cast hr.symm m) n * b n a) (fun m => ∑ n, Ym (Fin.cast hr.symm m) n * b n a)) : ℚ) : ℂ)) := by
  intro D ψ hψ V W b hb r hr X hX Xm Ym
  obtain ⟨θ, hθ⟩ := hψ.2.1
  set t := incA D D.host.xi0 * hO V W (realPt V W Xm) (realPt V W Ym) with ht
  have hfin : finPart D t = 0 := by rw [ht, map_mul, finPart_hO_realPt, mul_zero]
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have hθt : ∀ ρ, θ ρ (infPart D t) = tauE D ρ (D.host.xi0 * hRat V W Xm Ym) := fun ρ => by
    rw [ht, map_mul (infPart D), infPart_hO_realPt, ← map_mul (infPart D), ← map_mul (incA D)]
    exact (hθ ρ).1 _
  have hL : symplOH V W (realPt V W Xm) (realPt V W Ym) =
      pairA D.host.F (algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F T) 0 := by
    unfold symplOH symplO
    rw [← ht, ← hTdef, hT]
    exact Prod.ext rfl (mul_zero _)
  have hs : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F T) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      (1 / 2 : ℂ) * ((2 * (tauE D ρ (D.host.xi0 * hRat V W Xm Ym)).re : ℝ) : ℂ) := fun ρ => by
    rw [show (algebraMap D.host.F (Ainf D.host.F) (1 / 2) * fstA D.host.F T) ⊗ₜ[D.host.F] (1 : D.host.E) =
        ((algebraMap D.host.F (Ainf D.host.F) (1 / 2)) ⊗ₜ[D.host.F] (1 : D.host.E)) *
          ((fstA D.host.F T) ⊗ₜ[D.host.F] (1 : D.host.E)) by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
      map_mul, hTdef, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, hθt, GlobalTheory.StdRat.tmul_one_eq, (hθ ρ).1]
    congr 1
    simp only [one_div, map_inv₀]
    rw [map_ofNat (algebraMap D.host.F D.host.E) 2, map_ofNat]
  rw [hL]
  change psiInf D.host.F ψ _ = _
  rw [hψ.2.2 θ hθ]
  simp only [hs]
  rw [← Finset.mul_sum, sum_two_re_tauE, ← Rat.cast_sum, ← map_sum, sum_herm_eq V W b hb r hr X hX Xm Ym, map_neg]
  congr 1
  push_cast
  ring

end GlobalTheory.ArchPhase
