import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitEmb
open GlobalTheory.SplitLift

section General
variable {n : ℕ} {K : Type*} (A : Type*) [CommRing K] [CommRing A]

def triMat (M : GL (Fin n) K) : Matrix (Fin n) (Fin n) (K × K × A) :=
  fun i j => ((M : Matrix (Fin n) (Fin n) K) i j, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j i,
    (1 : Matrix (Fin n) (Fin n) A) i j)

theorem triMat_one : triMat A (1 : GL (Fin n) K) = 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [triMat, inv_one, Units.val_one, Matrix.one_apply, eq_comm (a := j)]
  split_ifs <;> rfl

theorem triMat_mul (M N : GL (Fin n) K) : triMat A (M * N) = triMat A M * triMat A N := by
  symm
  apply matrix_prod_ext
  · exact Matrix.map_mul (L := triMat A M) (M := triMat A N) (f := RingHom.fst K (K × A))
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.fst K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    change ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose *
      ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose =
      (((M * N)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.snd K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    exact Matrix.mul_one (1 : Matrix (Fin n) (Fin n) A)

end General

theorem exists_hom_trivOutside_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L),
    ∃ e : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) →* GAf L n,
      (∀ g, TrivOutside {s.v} (e g)) ∧ ∀ g, s.loc n (e g) = g := by
  intro L _ _ _ n s
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : IsCMField.complexConj L (δ * δ) = δ * δ := by rw [map_mul, hδ]; ring
  let d : maximalRealSubfield L := ⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩
  have hd : δ * δ = algebraMap (maximalRealSubfield L) L d := rfl
  have hr : s.i δ ≠ 0 := (map_ne_zero _).2 hδ0
  let X : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) → Matrix (Fin n) (Fin n) (AL L) :=
    fun M => (triMat (AL L) M).map (θ s δ d hd hr)
  have hX1 : X 1 = 1 := by
    show (triMat (AL L) 1).map (θ s δ d hd hr) = 1
    rw [triMat_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXm : ∀ M N, X (M * N) = X M * X N := fun M N => by
    show (triMat (AL L) (M * N)).map (θ s δ d hd hr) = _
    rw [triMat_mul, Matrix.map_mul]
  have hconj : ∀ M, conjT (conjAL L) (X M) = X M⁻¹ := fun M => by
    refine Matrix.ext fun i j => ?_
    simp only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]
    rw [conj_θ s δ d hd hr hδ]
    congr 1
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [triMat, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have hX : ∀ M, X M * conjT (conjAL L) (X M) = 1 := fun M => by
    rw [hconj, ← hXm, mul_inv_cancel, hX1]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := fun M => ⟨⟨X M, conjT (conjAL L) (X M), hX M, mul_eq_one_comm.mp (hX M)⟩, hX M⟩
      map_one' := Subtype.ext (Units.ext hX1)
      map_mul' := fun M N => Subtype.ext (Units.ext (hXm M N)) }
  refine ⟨e, fun M w hw => ?_, fun M => ?_⟩
  · have hw' : w ≠ s.v := hw
    refine Matrix.ext fun i j => ?_
    change compAt L w (θ s δ d hd hr (triMat (AL L) M i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [compAt_θ s δ d hd hr _ hw']
    simp only [triMat, Matrix.one_apply]
    split_ifs <;> simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change s.proj (θ s δ d hd hr (triMat (AL L) M i j)) = _
    rw [proj_θ]
    rfl

end GlobalTheory.SplitEmb
