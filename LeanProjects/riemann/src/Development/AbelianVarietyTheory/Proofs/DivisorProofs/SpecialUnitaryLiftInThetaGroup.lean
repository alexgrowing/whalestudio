import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MassLift
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem key {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) (σ : E →ₐ[F] E) (hσ : ∀ x, σ x = c x) {n r : ℕ} (h : n = r)
    (J : Matrix (Fin n) (Fin n) E) (s : Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA F E))
    (hs : GlobalTheory.UCls.IsUA c (Matrix.transpose (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))) s) :
    IsUnit (s.submatrix (Fin.cast h) (Fin.cast h)).det ∧
    Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 F) F) σ) (s.submatrix (Fin.cast h) (Fin.cast h)) *
      JR (FiniteAdeleRing (𝓞 F) F) J * s.submatrix (Fin.cast h) (Fin.cast h) = JR (FiniteAdeleRing (𝓞 F) F) J := by
  subst h
  have hs' : GlobalTheory.UCls.IsUA c Jᵀ s := hs
  show IsUnit s.det ∧ Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 F) F) σ) s * JR (FiniteAdeleRing (𝓞 F) F) J * s = JR (FiniteAdeleRing (𝓞 F) F) J
  refine ⟨hs'.1, ?_⟩
  have hsg : ∀ z : GlobalTheory.AdLat.RA F E, sigR (FiniteAdeleRing (𝓞 F) F) σ z = GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [sigR, GlobalTheory.AdLat.sg, hσ]
    | add a b ha hb => simp only [map_add, ha, hb]
  ext a b
  have e := hs'.2 (Pi.single b 1) (Pi.single a 1)
  simp only [GlobalTheory.AdLat.hermA, Matrix.mulVec_single, mul_one] at e
  simp only [Matrix.mul_apply, Formalism.UG.cT, JR, inclR, Matrix.transpose_apply, Matrix.map_apply, hsg, Finset.sum_mul]
  simp only [MulOpposite.op_one, one_smul, Matrix.col_apply, Matrix.transpose_apply, Pi.single_apply, ite_mul, one_mul,
    zero_mul] at e
  simp only [apply_ite (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c), map_one, map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero] at e
  simp only [RingHom.coe_coe, AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.includeRight_apply]
  refine Eq.trans ?_ e
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring

theorem lift_spec : ∀ (D : D7) (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E), GlobalTheory.SUVol.IsSA (GlobalTheory.MassLink.gm D i) s → GlobalTheory.MassLink.lift D i s ∈ Theta.GfC (Wc D i) ∧ ((Theta.finHom (Wc D i) (GlobalTheory.MassLink.lift D i s)).val : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) := by
  intro D i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  intro s hs
  obtain ⟨hdet, hU⟩ := key (IsCMField.complexConj D.host.E) D.sp.cm.sig (fun _ => rfl) (rank_Wc i) (Wc D i).gram s hs.1
  let b : GL (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    ((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit
  have hb : b ∈ HR (Af D.host.F) D.sp.cm.sig (Wc D i).gram := hU
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig (Wc D i).gram
  obtain ⟨g, g1, g2⟩ := h2 1 b
  have hg : g ∈ HR (AF D.host.F) D.sp.cm.sig (Wc D i).gram := (h1 g).2 ⟨g1 ▸ one_mem _, g2 ▸ hb⟩
  have hex : ∃ k : Theta.GA D (Wc D i), k ∈ Theta.GfC (Wc D i) ∧
      (((Theta.finHom (Wc D i) k).val :
        Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))) =
        s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) := by
    refine ⟨⟨g, hg⟩, g1, ?_⟩
    have e : Theta.finHom (Wc D i) ⟨g, hg⟩ = b := g2
    rw [e]
    rfl
  unfold GlobalTheory.MassLink.lift
  rw [dif_pos hex]
  exact hex.choose_spec

end GlobalTheory.MassLift
