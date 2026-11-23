import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalVSum
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitNbhd

open PositivityTheory.RgEis (eSF)

section Gen

variable {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]

theorem exists_mul_eq_norm (a : A) : ∃ c, a * c = algebraMap R A (Algebra.norm R a) := by
  classical
  let b := Module.Free.chooseBasis R A
  let M := Algebra.leftMulMatrix b a
  refine ⟨Matrix.toLin b b M.adjugate 1, ?_⟩
  have h1 : Algebra.norm R a = M.det := Algebra.norm_eq_matrix_det b a
  have h2 : Matrix.toLin b b M = LinearMap.mulLeft R a := by
    simp only [M, Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
    rfl
  have h3 : Matrix.toLin b b M (Matrix.toLin b b M.adjugate 1) = Matrix.toLin b b (M * M.adjugate) 1 := by
    rw [Matrix.toLin_mul b b b]; rfl
  have h4 : a * Matrix.toLin b b M.adjugate 1 = Matrix.toLin b b M (Matrix.toLin b b M.adjugate 1) := by
    rw [h2]; rfl
  rw [h4, h3, Matrix.mul_adjugate, h1, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply, Algebra.algebraMap_eq_smul_one]

theorem continuous_norm [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace A] [IsModuleTopology R A] :
    Continuous (fun a : A => Algebra.norm R a) := by
  classical
  let b := Module.Free.chooseBasis R A
  have h : (fun a : A => Algebra.norm R a) = fun a => (Algebra.leftMulMatrix b a).det := by
    funext a; exact Algebra.norm_eq_matrix_det b a
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  have : (fun a : A => Algebra.leftMulMatrix b a i j) = (b.coord i) ∘ₗ (LinearMap.mulRight R (b j)) := by
    funext a
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

end Gen

theorem exists_mul_eq_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : AF F)
    (h1 : ∀ w, evInf F w n ≠ 0) (h2 : ∀ v ∈ S, evFin F v n ≠ 0) : ∃ m : AF F, n * m = eSF S := by
  classical
  refine ⟨((fun w => (evInf F w n)⁻¹ : Ainf F), ∑ v ∈ S, singleFin v (evFin F v n)⁻¹), ?_⟩
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  refine Prod.ext ?_ (af_ext fun u => ?_)
  · funext w
    exact mul_inv_cancel₀ (h1 w)
  · change evalV F u (n.2 * ∑ v ∈ S, singleFin v (evFin F v n)⁻¹) = evalV F u (∑ v ∈ S, singleFin v 1)
    rw [map_mul, GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.evalV_sum, map_sum]
    split_ifs with h
    · rw [Finset.sum_eq_single_of_mem u h (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _), evalV_singleFin_self]
      exact mul_inv_cancel₀ (h2 u h)
    · rw [Finset.sum_eq_zero, mul_zero]
      intro v hv
      exact evalV_singleFin_ne (by rintro rfl; exact h hv) _

theorem evInf_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    evInf F w (eSF S) = 1 := by
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  rfl

open Classical in
theorem evFin_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) : evFin F v (eSF S) = if v ∈ S then 1 else 0 := by
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  exact GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.evalV_sum S v

theorem compInf_eSF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) (eSF S)) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  change (Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E)) _ = 1
  rw [Algebra.TensorProduct.map_tmul, show algebraMap (AF F) (AF F) (eSF S) = eSF S from rfl, evInf_eSF]
  simp [Algebra.TensorProduct.one_def]

open Classical in
theorem compFin_eSF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) (eSF S)) = if v ∈ S then 1 else 0 := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  change (Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E)) _ = _
  rw [Algebra.TensorProduct.map_tmul, show algebraMap (AF F) (AF F) (eSF S) = eSF S from rfl, evFin_eSF]
  split_ifs <;> simp [Algebra.TensorProduct.one_def]

theorem eq_algebraMap_eSF
    (hc : ∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0)
    (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) (eSF S) := by
  classical
  rw [← sub_eq_zero]
  refine hc D _ (fun w => ?_) (fun v => ?_)
  · rw [RingHom.map_sub, he.1 w, compInf_eSF, sub_self]
  · refine (RingHom.map_sub _ _ _).trans ?_
    rw [he.2 v]
    refine sub_eq_zero.2 ?_
    exact (compFin_eSF S v).symm

theorem exists_open_mul_eq_idem :
    (∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0) →
    ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∃ U : Set (AE D), IsOpen U ∧ 1 ∈ U ∧ ∀ x ∈ U, ∃ b, x * b = e := by
  intro hc D S e he
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hn := continuous_norm (R := AF D.host.F) (A := AE D)
  have cI : ∀ w, Continuous (evInf D.host.F w) := fun w => (continuous_apply w).comp continuous_fst
  have cF : ∀ v, Continuous (evFin D.host.F v) := fun v => (RestrictedProduct.continuous_eval v).comp continuous_snd
  refine ⟨{a | (∀ w, evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0) ∧
    ∀ v ∈ S, evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0}, ?_, ?_, ?_⟩
  · have h : {a : AE D | (∀ w, evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0) ∧
        ∀ v ∈ S, evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0} =
        (⋂ w, {a : AE D | evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0}) ∩
        ⋂ v ∈ S, {a : AE D | evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [h]
    refine (isOpen_iInter_of_finite fun w => ?_).inter (isOpen_biInter_finset fun v _ => ?_)
    · exact isOpen_ne_fun ((cI w).comp hn) continuous_const
    · exact isOpen_ne_fun ((cF v).comp hn) continuous_const
  · simp only [Set.mem_setOf_eq, map_one]
    exact ⟨fun _ => one_ne_zero, fun _ _ => one_ne_zero⟩
  · rintro x ⟨h1, h2⟩
    obtain ⟨c, hxc⟩ := exists_mul_eq_norm (R := AF D.host.F) x
    obtain ⟨m, hm⟩ := exists_mul_eq_eSF S _ h1 h2
    refine ⟨c * algebraMap (AF D.host.F) (AE D) m, ?_⟩
    rw [← mul_assoc, hxc, ← map_mul, hm, eq_algebraMap_eSF hc D S e he]

end GlobalTheory.CompanionTheory.UnitNbhd
