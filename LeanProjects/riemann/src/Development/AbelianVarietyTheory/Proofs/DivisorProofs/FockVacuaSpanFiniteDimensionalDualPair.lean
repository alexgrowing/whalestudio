import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDeriva
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
open scoped Matrix

noncomputable section

namespace GlobalTheory.FockKFin.VacFin

open GlobalTheory.ThK.EvAt0.PolD Formalism.BasicNotions.TH

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem Jm_transpose (p q : ℕ) : (Jm p q)ᵀ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem vac_mem_line {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (h : GlobalTheory.ThK.IsPair B M χX χW om r s r' s') :
    ∃ v : SInf F (Fin n × Fin d), ∀ g, GaussD M B.emb g → ∃ z : ℂ, g = z • v := by
  have hb := h.base
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.FockMapEx.fockEx_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I
    A C hb.cm hb.std fr
  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hb.std
  have hDd : ∀ u, At (evI F) u → ∀ f : SInf F (Fin n × Fin d), D u f = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
    intro u hu f
    refine DFunLike.ext _ _ fun x => ?_
    rw [(hD u hu f).2 x, dOp_apply]
    try rfl
  have tw : ∀ w (c : Matrix (Ix r s) (Ix r' s') ℂ) (e : ℂ),
      A w * (e • (Jm r s * c * Jm r' s')) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm r' s' * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hCθ w, Matrix.transpose_mul, Jm_transpose]
    calc A w * (e • (Jm r s * c * Jm r' s')) * (C w)ᵀ = e • ((A w * Jm r s) * c * (Jm r' s' * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hAθ w, ← h2]; simp only [Matrix.mul_assoc]
  refine ⟨Φ (PiTensorProduct.tprod ℂ fun _ => 1), fun g ⟨ε, hε⟩ => ?_⟩
  refine GlobalTheory.VacLn.vacLine_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ
    hb.cm hb.std fr hΦ g ε ?_
  intro u u' hu hu' c hc hc' f f' hf hf'
  have e1 : f = D u g := (GlobalTheory.RealLift.actsLaws F _ g f (D u g)).2.2.2.2 _ hf (hD u hu g).1
  have e2 : f' = D u' g := (GlobalTheory.RealLift.actsLaws F _ g f' (D u' g)).2.2.2.2 _ hf' (hD u' hu' g).1
  rw [e1, e2, hDd u hu, hDd u' hu']
  exact hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w])

end GlobalTheory.FockKFin.VacFin

theorem GlobalTheory.FockKFin.vacSp_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → FiniteDimensional ℂ (GlobalTheory.FockKFin.vacSp M B.emb) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  obtain ⟨v, hv⟩ := GlobalTheory.FockKFin.VacFin.vac_mem_line σ B n d X W M χX χW om r s r' s' h
  have hle : GlobalTheory.FockKFin.vacSp M B.emb ≤ Submodule.span ℂ {v} := by
    refine Submodule.span_le.2 fun g hg => ?_
    obtain ⟨z, rfl⟩ := hv g hg
    exact Submodule.smul_mem _ z (Submodule.subset_span rfl)
  exact Submodule.finiteDimensional_of_le hle

end
