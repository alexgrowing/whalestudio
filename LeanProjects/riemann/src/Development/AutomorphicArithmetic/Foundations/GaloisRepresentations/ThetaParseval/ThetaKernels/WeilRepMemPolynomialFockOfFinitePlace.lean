import Development.AutomorphicArithmetic.AdelicQuotients.PolynomialDataStableFinitePlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.weilRep_mem_polynomialFock_of_finite_place :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), ∀ r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ v : Pl F, ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ PolData B M, om (g, h) Φ ∈ PolData B M := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v g hg h hh Φ hΦ
  classical
  refine Submodule.span_induction (p := fun Φ _ => om (g, h) Φ ∈ PolData B M) ?_ (by simp)
    (fun x y _ _ a b => by rw [map_add]; exact add_mem a b)
    (fun c x _ a => by rw [map_smul]; exact Submodule.smul_mem _ c a) hΦ
  rintro _ ⟨f, hf, φ, hSB, hcof, rfl⟩
  obtain ⟨φ₁, ⟨s1, a1⟩, -⟩ := (T.acts F E σ B n d X W M χX χW om r s r' s' hp v).1 g hg h hh (φ v) (hSB v)
  have e := (PositivityTheory.ThKF.pureAct F _ v (om (g, h)) f φ hSB
    ((hcof.and hp.good.std).mono fun _ k => k.1.trans k.2)).2.2 φ₁ a1
  refine e ▸ Submodule.subset_span ⟨f, hf, Function.update φ v φ₁, fun u => ?_, ?_, ?_⟩
  · by_cases hu : u = v
    · subst hu; simpa using s1
    · simpa [Function.update_of_ne hu] using hSB u
  · have : ∀ᶠ u in cofinite, u ≠ v := (Set.finite_singleton v).compl_mem_cofinite
    exact (hcof.and this).mono fun u k => by rw [Function.update_of_ne k.2, k.1]
  · congr!
end
