import Formalism.LocalToGlobal.Columns.TwQSurj
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG

section QLiftS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

def qdPair {R : Type} [CommRing R] (k : GL (Fin n) R) : Matrix (Fin n) (Fin n) (R × R) :=
  fun i j => ((k : Matrix (Fin n) (Fin n) R) i j, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j i)

theorem qdPair_mul_inv {R : Type} [CommRing R] (k : GL (Fin n) R) : qdPair k * qdPair k⁻¹ = 1 := by
  have h1 : (k : Matrix (Fin n) (Fin n) R) * ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := Units.mul_inv k
  ext i j
  · show (∑ l, ((k : Matrix (Fin n) (Fin n) R) i l, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i) *
        (((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l j, ((k⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j l)).1 = _
    rw [Prod.fst_sum]
    have := congrArg (fun A : Matrix (Fin n) (Fin n) R => A i j) h1
    simp only [Matrix.mul_apply] at this
    rw [Matrix.one_apply] at this ⊢
    simp only [Prod.fst_mul]
    rw [this]
    split_ifs <;> rfl
  · show (∑ l, ((k : Matrix (Fin n) (Fin n) R) i l, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i) *
        (((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l j, ((k⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j l)).2 = _
    rw [Prod.snd_sum, inv_inv]
    have := congrArg (fun A : Matrix (Fin n) (Fin n) R => A j i) h1
    simp only [Matrix.mul_apply] at this
    simp only [Prod.snd_mul]
    rw [Matrix.one_apply] at this ⊢
    rw [show (∑ l, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i * (k : Matrix (Fin n) (Fin n) R) j l) =
      ∑ l, (k : Matrix (Fin n) (Fin n) R) j l * ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i from
      Finset.sum_congr rfl fun l _ => mul_comm _ _, this]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]; rfl

def qdPairGL {R : Type} [CommRing R] (k : GL (Fin n) R) : GL (Fin n) (R × R) :=
  ⟨qdPair k, qdPair k⁻¹, qdPair_mul_inv k, by simpa using qdPair_mul_inv k⁻¹⟩

def qdLift (q : QLoc hc n Q Θ) (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)) : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F) :=
  bc (q.sp P).symm.toRingHom (qdPairGL k)

theorem qdf_sig_symm (q : QLoc hc n Q Θ) (P : Q) (a b : (qv F P.1).adicCompletion F) :
    sigR hc.sig ((qv F P.1).adicCompletion F) ((q.sp P).symm (a, b)) = (q.sp P).symm (b, a) := by
  apply (q.sp P).injective
  rw [q.sp_sig, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rfl

theorem qdLift_fst (q : QLoc hc n Q Θ) (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)) :
    bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) (qdLift q P k) = k := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show ((q.sp P) ((q.sp P).symm (qdPair k i j))).1 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem qdf_lift (q : QLoc hc n Q Θ) : QLift q := by
  intro P k hk
  refine ⟨qdLift q P k, ?_, ?_, qdLift_fst q P k⟩
  · show cT (sigR hc.sig ((qv F P.1).adicCompletion F)) ((qdLift q P k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *
        (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) ((qv F P.1).adicCompletion F)) * ((qdLift q P k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) ((qv F P.1).adicCompletion F))
    have hone : (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) ((qv F P.1).adicCompletion F)) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    have hcT : cT (sigR hc.sig ((qv F P.1).adicCompletion F)) ((qdLift q P k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) =
        ((qdLift q P k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
      refine Matrix.ext fun i j => ?_
      show sigR hc.sig ((qv F P.1).adicCompletion F) ((q.sp P).symm (qdPair k j i)) = (q.sp P).symm (qdPair k⁻¹ i j)
      rw [qdf_sig_symm]
      rfl
    rw [hone, mul_one, hcT]
    rw [← Units.val_mul, qdLift, qdLift, ← map_mul]
    have : qdPairGL k⁻¹ * qdPairGL k = 1 := Units.ext (by
      have h := qdPair_mul_inv k⁻¹
      rw [inv_inv] at h
      exact h)
    rw [this, map_one, Units.val_one]
  · rw [rll_locL_std, Formalism.UG.P.afsplit_stab_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (q.sp P).symm (qdPair k i j) ∈ Formalism.BasicNotions.intV E (qv F P.1)
      rw [q.sp_int, RingEquiv.apply_symm_apply]
      exact ⟨hk.1 i j, hk.2 j i⟩
    · show (q.sp P).symm (qdPair k⁻¹ i j) ∈ Formalism.BasicNotions.intV E (qv F P.1)
      rw [q.sp_int, RingEquiv.apply_symm_apply]
      refine ⟨hk.2 i j, ?_⟩
      have e : (k⁻¹⁻¹ : GL (Fin n) ((qv F P.1).adicCompletion F)) = k := inv_inv k
      show ((↑(k⁻¹⁻¹) : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F)) j i) ∈ _
      rw [e]
      exact hk.1 j i

end QLiftS

end Formalism.L2.Col
