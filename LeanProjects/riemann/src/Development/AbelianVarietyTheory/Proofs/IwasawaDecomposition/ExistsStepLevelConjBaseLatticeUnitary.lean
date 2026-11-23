import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Formalism.LocalToGlobal.Columns.RecLevelTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem exists_stepLevel_conj : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (b : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ v, bc (prV (E := E) v) b ∈ levelVL σ J v S.Lb) → (∀ v, (T : 𝓞 F) ∈ v.asIdeal → (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v) → (∀ v, v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) → ∃ S' : StepLevel F E σ J T f bad, S'.Lb = S.Lb ∧ S'.U = S.U.map (MulAut.conj b).toMonoidHom ∧ ∀ (x : S'.U) (z : S.U), x.1 = b * z.1 * b⁻¹ → S'.chi x = S.chi z := by
  intro F E _ _ _ _ _ σ n J T f bad S b hb hlev hT hone
  classical
  let eqv := Subgroup.equivMapOfInjective S.U (MulAut.conj b).toMonoidHom
    (fun x y h => (MulAut.conj b).injective h)
  have heqv : ∀ z : S.U, ((eqv z : S.U.map (MulAut.conj b).toMonoidHom) : GL (Fin n) _) = b * z.1 * b⁻¹ := fun z => rfl
  have hbc : ∀ v (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) (b⁻¹ * x * b) =
      (bc (prV (E := E) v) b)⁻¹ * bc (prV (E := E) v) x * bc (prV (E := E) v) b := fun v x => by
    rw [map_mul, map_mul, map_inv]
  have hP : ∀ x, b⁻¹ * x * b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ↔ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := fun x => by
    constructor
    · intro h
      have e2 : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
      rw [← e2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb h) (Subgroup.inv_mem _ hb)
    · intro h
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h) hb
  let S' : StepLevel F E σ J T f bad :=
    { Lb := S.Lb
      Lb_fin := S.Lb_fin
      Lb_span := S.Lb_span
      Lb_int := S.Lb_int
      Lb_dual := S.Lb_dual
      Lb_index := S.Lb_index
      Uloc := fun v => (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom
      Uloc_le := by
        intro v
        rintro _ ⟨y, hy, rfl⟩
        have hbv : bc (prV (E := E) v) b ∈ UPts σ J (v.adicCompletion F) := (hlev v).1
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbv (S.Uloc_le v hy)) (Subgroup.inv_mem _ hbv)
      Uloc_lev := by
        intro v
        rintro _ ⟨y, hy, rfl⟩
        have hbv := hlev v
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbv (S.Uloc_lev v hy)) (Subgroup.inv_mem _ hbv)
      Uloc_hyp := by
        intro v hv hTv
        show (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL σ J v S.Lb
        ext x
        rw [mem_map_conj, hone v hv hTv, inv_one, one_mul, mul_one, S.Uloc_hyp v hv hTv]
      fM := S.fM
      fM_acg := S.fM_acg
      fM_mod := S.fM_mod
      fT := S.fT
      fT_ne := S.fT_ne
      fT_T := S.fT_T
      fM_card := S.fM_card
      fT_L := S.fT_L
      UlocAlt := by
        intro v h
        show (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = _
        rw [hT v h]
        exact S.UlocAlt v h
      U := S.U.map (MulAut.conj b).toMonoidHom
      U_eq := by
        intro x
        rw [mem_map_conj, S.U_eq, hP]
        refine and_congr_right fun _ => forall_congr' fun v => ?_
        rw [hbc v x]
        exact (mem_map_conj _ _ _).symm
      U_compact := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
        have hc : Continuous (fun x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => b * x * b⁻¹) :=
          (continuous_const.mul continuous_id).mul continuous_const
        have := S.U_compact.image hc
        convert this using 1
        rw [Subgroup.coe_map]
        rfl
      U_open := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
        haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
          inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
        let b' : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨b, hb⟩
        have hc : Continuous (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => b'⁻¹ * x * b') :=
          (continuous_const.mul continuous_id).mul continuous_const
        have := S.U_open.preimage hc
        convert this using 1
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_map_conj]
        rfl
      chi := S.chi.comp eqv.symm.toMonoidHom
      chi_triv := by
        intro x hx
        show S.chi (eqv.symm x) = 1
        apply S.chi_triv
        intro v hv
        have e1 : ((eqv.symm x : S.U) : GL (Fin n) _) = b⁻¹ * x.1 * b := by
          have h2 := heqv (eqv.symm x)
          rw [MulEquiv.apply_symm_apply] at h2
          rw [h2]
          group
        rw [e1, hbc v, hx v hv, mul_one, inv_mul_cancel] }
  refine ⟨S', rfl, rfl, fun x z hxz => ?_⟩
  show S.chi (eqv.symm x) = S.chi z
  congr 1
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (hxz.trans (heqv z).symm)

end GlobalTheory.Mem.Col2.ChEx
