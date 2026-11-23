import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWB
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter

namespace PositivityTheory.Rg.Rsw.L.LFixW

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]

theorem trace_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (z : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) =
      φ (Algebra.trace R (R ⊗[F] E) z) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R' (bE F E)),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R (bE F E)), Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply]
  have e : Algebra.TensorProduct.map φ (AlgHom.id F E) (z * (1 ⊗ₜ[F] bE F E i)) =
      Algebra.TensorProduct.map φ (AlgHom.id F E) z * (1 ⊗ₜ[F] bE F E i) := by
    rw [map_mul]; simp
  rw [← e, LIdemEx.repr_map']

theorem sgl_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : (singleV F v y) v = y :=
  GlobalTheory.CompanionTheory.PsiCondLoc.single_self v y

theorem sgl_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) :
    (singleV F v y) w = 0 :=
  GlobalTheory.CompanionTheory.PsiCondLoc.single_ne v y h

theorem sgl_mul (u : Af F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    u * singleV F v y = singleV F v (u v * y) :=
  GlobalTheory.CompanionTheory.PsiCondLoc.mul_single u v y

def iV (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F where
  toFun a := pairA F 0 (singleV F v a)
  map_add' a b := by
    refine Prod.ext (by show (0 : Ainf F) = 0 + 0; rw [add_zero]) (Subtype.ext (funext fun w => ?_))
    show (singleV F v (a + b)) w = (singleV F v a) w + (singleV F v b) w
    by_cases h : w = v
    · subst h; rw [sgl_self, sgl_self, sgl_self]
    · rw [sgl_ne v _ h, sgl_ne v _ h, sgl_ne v _ h,
        add_zero]
  map_smul' c a := by
    rw [Algebra.smul_def (A := AF F), RingHom.id_apply]
    refine Prod.ext (by show (0 : Ainf F) = _ * 0; rw [mul_zero]) ?_
    show singleV F v (c • a) = (algebraMap F (Af F) c) * singleV F v a
    rw [sgl_mul, Algebra.smul_def]
    rfl

theorem iV_fst (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (iV v a).1 = 0 := rfl

theorem iV_snd (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (iV v a).2 = singleV F v a := rfl

variable (E) in

def plc (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (iV v) LinearMap.id

theorem plc_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) : plc E v (a ⊗ₜ[F] e) = iV v a ⊗ₜ[F] e := rfl

theorem evFin_apply (v : HeightOneSpectrum (𝓞 F)) (y : AF F) : evFin F v y = y.2 v := rfl

theorem evInf_apply (w : InfinitePlace F) (y : AF F) : evInf F w y = y.1 w := rfl

theorem compFin_plc_self (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v ⊗[F] E) : compFin F E v (plc E v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a e =>
    rw [plc_tmul]
    show evFin F v (iV v a) ⊗ₜ[F] e = _
    rw [evFin_apply, iV_snd, sgl_self]

theorem compFin_plc_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (t : Fv F v ⊗[F] E) :
    compFin F E w (plc E v t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul a e =>
    rw [plc_tmul]
    show evFin F w (iV v a) ⊗ₜ[F] e = 0
    rw [evFin_apply, iV_snd, sgl_ne v _ h, TensorProduct.zero_tmul]

theorem compInf_plc (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v ⊗[F] E) :
    compInf F E w (plc E v t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul a e =>
    rw [plc_tmul]
    show evInf F w (iV v a) ⊗ₜ[F] e = 0
    rw [evInf_apply, iV_fst]
    exact TensorProduct.zero_tmul _ _

theorem psi_kernel {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ y : AF F, y.1 = 0 → (∀ v ∈ S, y.2 v = 0) →
      (∀ v ∉ S, y.2 v ∈ v.adicCompletionIntegers F) → ψ y = 1 := by
  obtain ⟨α, hα, hk⟩ := GlobalTheory.CompanionTheory.PsiCondLoc.exists_int_kernel hψ
  have hα0 : (α : F) ≠ 0 := by exact_mod_cast hα
  have h1 := Filter.eventually_cofinite.1 (eventually_int (F := F) ((α : F)⁻¹))
  refine ⟨h1.toFinset, fun S hS y hy1 hyS hyI => ?_⟩
  have hu : algebraMap F (Af F) ((α : F)⁻¹) * y.2 ∈ Formalism.UG.intAd F := by
    intro v
    show (algebraMap F (Af F) ((α : F)⁻¹)) v * y.2 v ∈ v.adicCompletionIntegers F
    by_cases hv : v ∈ S
    · rw [hyS v hv, mul_zero]; exact zero_mem _
    · have hv' : v ∉ h1.toFinset := fun h => hv (hS h)
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv'
      exact mul_mem hv' (hyI v hv)
  have e : y = pairA F 0 (algebraMap F (Af F) (α : F) * (algebraMap F (Af F) ((α : F)⁻¹) * y.2)) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hα0, map_one, one_mul]
    exact Prod.ext hy1 rfl
  rw [e]
  exact hk _ hu

end Gen

section D

open Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.StdUnn

variable {D : D7}

theorem trA_fst (z : AE D) (w : InfinitePlace D.host.F) :
    (trA z).1 w = Algebra.trace w.Completion (w.Completion ⊗[D.host.F] D.host.E) (compInf D.host.F D.host.E w z) := by
  rw [← evInf_apply]
  exact (trace_map (evInf D.host.F w) z).symm

theorem trA_snd (z : AE D) (v : Pl D) :
    (trA z).2 v = Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) (cv D v z) := by
  rw [← evFin_apply]
  exact (trace_map (evFin D.host.F v) z).symm

theorem mul_plc (z : AE D) (v : Pl D) (t : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    z * plc D.host.E v t = plc D.host.E v (cv D v z * t) := by
  refine LIdemEx.ae_ext _ _ (fun w => ?_) (fun w => ?_)
  · rw [map_mul, compInf_plc, compInf_plc, mul_zero]
  · rw [map_mul]
    by_cases h : w = v
    · subst h; rw [compFin_plc_self, compFin_plc_self]
    · rw [compFin_plc_ne h, compFin_plc_ne h, mul_zero]

theorem trA_plc (v : Pl D) (t : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    trA (plc D.host.E v t) =
      pairA D.host.F 0 (singleV D.host.F v (Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) t)) := by
  refine Prod.ext (funext fun w => ?_) (Subtype.ext (funext fun w => ?_))
  · rw [trA_fst, compInf_plc, map_zero]; rfl
  · show (trA (plc D.host.E v t)).2 w = (singleV D.host.F v _) w
    rw [trA_snd]
    by_cases h : w = v
    · subst h; rw [compFin_plc_self, sgl_self]
    · rw [compFin_plc_ne h, map_zero, sgl_ne v _ h]

end D

end PositivityTheory.Rg.Rsw.L.LFixW

end
