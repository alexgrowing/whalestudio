import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.IdemMulCompl
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.FiniteClassSetOfLe

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E)
  (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))

def awayG (p : ℕ) : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :=
  UPts σE J (FiniteAdeleRing (𝓞 F) F) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal), (Uloc v).comap (bc (prV (E := E) v))

theorem mem_awayG (p : ℕ) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    x ∈ awayG σE J Uloc p ↔ x ∈ UPts σE J (FiniteAdeleRing (𝓞 F) F) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) x ∈ Uloc v := by
  simp only [awayG, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

abbrev compG (p : ℕ) : Type := compC σE J (awayG σE J Uloc p)

def trivG (p : ℕ) (y : UPts σE J (FiniteAdeleRing (𝓞 F) F)) : UPts σE J (FiniteAdeleRing (𝓞 F) F) :=
  ⟨glue (epsP F p E) (isIdempotentElem_placeIdempotent F p E) ((y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), 1),
    glue_mem_UJ (epsP F p E) (isIdempotentElem_placeIdempotent F p E) _ (epsP_sig F p E σE) _ y.2 (Subgroup.one_mem _)⟩

theorem trivG_over (p : ℕ) (y : UPts σE J (FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (h : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    bc (prV (E := E) v) (trivG σE J p y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 := by
  show bc (prV (E := E) v) (glue (epsP F p E) (isIdempotentElem_placeIdempotent F p E) _) = 1
  rw [bc_glue_one _ _ _ (epsP_over F p E v h), map_one]

theorem trivG_off (p : ℕ) (y : UPts σE J (FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (h : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    bc (prV (E := E) v) (trivG σE J p y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      bc (prV (E := E) v) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
  show bc (prV (E := E) v) (glue (epsP F p E) (isIdempotentElem_placeIdempotent F p E) _) = _
  rw [bc_glue_zero _ _ _ (epsP_off F p E v h)]

theorem trivG_rel (p : ℕ) (y : UPts σE J (FiniteAdeleRing (𝓞 F) F)) :
    ((y⁻¹ * trivG σE J p y : UPts σE J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ awayG σE J Uloc p := by
  refine (mem_awayG σE J Uloc p _).2 ⟨(y⁻¹ * trivG σE J p y).2, ?_⟩
  intro v hv
  have : bc (prV (E := E) v) ((y⁻¹ * trivG σE J p y : UPts σE J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, trivG_off σE J p y v hv, inv_mul_cancel]
  rw [this]
  exact Subgroup.one_mem _

theorem mk_trivG (p : ℕ) (y : UPts σE J (FiniteAdeleRing (𝓞 F) F)) :
    (Quotient.mk'' (trivG σE J p y) : compG σE J Uloc p) = Quotient.mk'' y := by
  symm
  refine (DoubleCoset.eq _ _ y (trivG σE J p y)).2 ⟨1, Subgroup.one_mem _, y⁻¹ * trivG σE J p y, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (trivG_rel σE J Uloc p y)
  · rw [one_mul, mul_inv_cancel_left]

def repG (p : ℕ) (i : compG σE J Uloc p) : UPts σE J (FiniteAdeleRing (𝓞 F) F) :=
  trivG σE J p (Quotient.out i)

theorem repG_mk (p : ℕ) (i : compG σE J Uloc p) : (Quotient.mk'' (repG σE J Uloc p i) : compG σE J Uloc p) = i := by
  rw [repG, mk_trivG]
  exact Quotient.out_eq' i

theorem repG_over (p : ℕ) (i : compG σE J Uloc p) (v : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    bc (prV (E := E) v) (repG σE J Uloc p i : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 :=
  trivG_over σE J p _ v h

theorem le_awayG (p : ℕ) (U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hU : ∀ x, x ∈ U → x ∈ UPts σE J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v) :
    U ≤ awayG σE J Uloc p := fun x hx =>
  (mem_awayG σE J Uloc p x).2 ⟨(hU x hx).1, fun v _ => (hU x hx).2 v⟩

theorem finite_compG (p : ℕ) (U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hU : ∀ x, x ∈ U → x ∈ UPts σE J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v)
    (hfin : Finite (ClassSet ((ratPts σE J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σE J (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (UPts σE J (FiniteAdeleRing (𝓞 F) F))))) : Finite (compG σE J Uloc p) := by
  refine finite_classSet_of_le _ (U.subgroupOf (UPts σE J (FiniteAdeleRing (𝓞 F) F))) _ ?_
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (le_awayG σE J Uloc p U hU (Subgroup.mem_subgroupOf.1 hx))

section Col

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

end Col

end Formalism.L2.G
