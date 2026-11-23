import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertLevel

section MixMat
variable {R : Type*} [CommRing R] {n : ℕ}

theorem mix_mul (p : R) (hp : p * p = p) (A B C D : Matrix (Fin n) (Fin n) R) :
    (p • A + (1 - p) • B) * (p • C + (1 - p) • D) = p • (A * C) + (1 - p) • (B * D) := by
  have h1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have h2 : (1 - p) * p = 0 := by rw [mul_comm, h1]
  have h3 : (1 - p) * (1 - p) = 1 - p := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hp, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_one (p : R) : p • (1 : Matrix (Fin n) (Fin n) R) + (1 - p) • 1 = 1 := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem conjT_mix (σ : R →+* R) (p : R) (hp : σ p = p) (A B : Matrix (Fin n) (Fin n) R) :
    conjT σ (p • A + (1 - p) • B) = p • conjT σ A + (1 - p) • conjT σ B := by
  ext i j
  simp [conjT, map_sub, hp]

end MixMat

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem mem_GA_iff (x : GL (Fin n) (AL L)) :
    x ∈ ReciprocityTheory.Aut.GA L n ↔ (x : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x = 1 := Iff.rfl

def mixG (p : AL L) (hp : p * p = p) (hc : conjAL L p = p) (g h : GAf L n) : GAf L n :=
  ⟨⟨p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L)),
    p • ((g.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) +
      (1 - p) • ((h.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)),
    by rw [mix_mul p hp, Units.mul_inv, Units.mul_inv, mix_one],
    by rw [mix_mul p hp, Units.inv_mul, Units.inv_mul, mix_one]⟩, by
    rw [mem_GA_iff]
    show (p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L))) *
      conjT (conjAL L) (p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L))) = 1
    rw [conjT_mix _ p hc, mix_mul p hp, (mem_GA_iff _).1 g.2, (mem_GA_iff _).1 h.2, mix_one]⟩

theorem mixG_val (p : AL L) (hp : p * p = p) (hc : conjAL L p = p) (g h : GAf L n) :
    ((mixG p hp hc g h).1 : Matrix (Fin n) (Fin n) (AL L)) =
      p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open GlobalTheory.InertUmax in

def idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L :=
  (1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1

section Idem
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))

theorem compAt_idemAt_self : compAt L v (idemAt v) = 1 := by
  rw [idemAt, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same, ← Algebra.TensorProduct.one_def]

theorem compAt_idemAt_ne {w} (hw : w ≠ v) : compAt L w (idemAt v) = 0 := by
  rw [idemAt, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hw, tmul_zero]

theorem idemAt_mul_self : idemAt (L := L) v * idemAt v = idemAt v := by
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt
  intro w
  rw [map_sub, map_mul]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self]; simp
  · rw [compAt_idemAt_ne v hw]; simp

theorem conjAL_idemAt : conjAL L (idemAt v) = idemAt v := by
  simp [idemAt, conjAL, Algebra.TensorProduct.map_tmul]

theorem idemAt_mem : idemAt (L := L) v ∈ ALint L :=
  GlobalTheory.InertUmax.one_tmul_sgl_mem L v 1 (one_mem _)

theorem one_sub_idemAt_mem : 1 - idemAt (L := L) v ∈ ALint L :=
  Subring.sub_mem _ (one_mem _) (idemAt_mem v)

theorem one_entry_mem (S : Subring (AL L)) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ S := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem compAt_one_entry (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i j : Fin n) :
    compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem away_eq_zero {x : GAf L n} (hx : TrivOutside {v} x) (i j : Fin n) :
    (1 - idemAt v) * ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0 := by
  apply GlobalTheory.InertUmax.eq_zero_of_compAt
  intro w
  rw [map_mul, map_sub, map_sub, map_one, compAt_one_entry]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self]; simp
  · have h := congrFun (congrFun (hx w (by simpa using hw)) i) j
    rw [Matrix.map_apply] at h
    rw [h, sub_self, mul_zero]

end Idem

def DivBy (N : ℕ) (M : Matrix (Fin n) (Fin n) (AL L)) : Prop :=
  ∀ i j, ∃ y ∈ ALint L, M i j = (N : AL L) * y

theorem DivBy.add {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A) (hB : DivBy N B) :
    DivBy N (A + B) := fun i j => by
  obtain ⟨y, hy, e⟩ := hA i j
  obtain ⟨z, hz, f⟩ := hB i j
  exact ⟨y + z, Subring.add_mem _ hy hz, by rw [Matrix.add_apply, e, f, mul_add]⟩

theorem DivBy.neg {N : ℕ} {A : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A) : DivBy N (-A) := fun i j => by
  obtain ⟨y, hy, e⟩ := hA i j
  exact ⟨-y, Subring.neg_mem _ hy, by rw [Matrix.neg_apply, e, mul_neg]⟩

theorem DivBy.mul_int {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A)
    (hB : ∀ i j, B i j ∈ ALint L) : DivBy N (A * B) := fun i j => by
  choose y hy e using hA
  exact ⟨∑ k, y i k * B k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hB k j), by
    simp only [Matrix.mul_apply, e, Finset.mul_sum, mul_assoc]⟩

theorem DivBy.int_mul {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A)
    (hB : ∀ i j, B i j ∈ ALint L) : DivBy N (B * A) := fun i j => by
  choose y hy e using hA
  exact ⟨∑ k, B i k * y k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hB i k) (hy k j), by
    simp only [Matrix.mul_apply, e, Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring⟩

def levelAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | κ ∈ Umax L n ∧
    DivBy N ((1 - idemAt v) • ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) - 1))}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Umax L n).mul_mem ha hb, ?_⟩
    have e : ((a * b).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
        ((a.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) * (b.1 : Matrix (Fin n) (Fin n) (AL L)) +
          ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) := by
      simp only [Subgroup.coe_mul, Units.val_mul, sub_mul, one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul]
    exact (ha'.mul_int hb).add hb'
  one_mem' := ⟨(Umax L n).one_mem, fun i j => ⟨0, zero_mem _, by simp⟩⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Umax L n).inv_mem ha, ?_⟩
    have e : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
        -(((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * ((a.1 : Matrix (Fin n) (Fin n) (AL L)) - 1)) := by
      rw [mul_sub, mul_one]
      have : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
      rw [this]; abel
    rw [e, smul_neg, ← Matrix.mul_smul]
    exact (ha'.int_mul ((Umax L n).inv_mem ha)).neg

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

theorem exists_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), 0 < N → ∃ U : Subgroup (GAf L n), (∀ κ, NG.Cong L n N κ → κ ∈ U) ∧ (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧ ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := by
  intro L _ _ _ n v N _
  have hp := idemAt_mul_self (L := L) v
  have hc := conjAL_idemAt (L := L) v
  refine ⟨levelAt (n := n) v N, ?_, ?_, ?_⟩
  · rintro κ ⟨hU, hκ⟩
    refine ⟨hU, fun i j => ?_⟩
    obtain ⟨y, hy, e⟩ := hκ i j
    refine ⟨(1 - idemAt v) * y, Subring.mul_mem _ (one_sub_idemAt_mem v) hy, ?_⟩
    rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, e]; ring
  · intro κ hκ
    refine ⟨fun h => h.1, fun h => ⟨h, fun i j => ⟨0, zero_mem _, ?_⟩⟩⟩
    rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, away_eq_zero v hκ, mul_zero]
  · rintro κ ⟨hU, hκ⟩
    refine ⟨mixG (idemAt v) hp hc κ 1, mixG (idemAt v) hp hc 1 κ, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, mixG_val, mix_mul _ hp, OneMemClass.coe_one, Units.val_one,
        mul_one, one_mul]
      rw [← add_smul, add_sub_cancel, one_smul]
    · intro i j
      rw [mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact Subring.add_mem _ (Subring.mul_mem _ (idemAt_mem v) (hU i j))
        (Subring.mul_mem _ (one_sub_idemAt_mem v) (by simpa using one_entry_mem (ALint L) i j))
    · intro w hw
      have hw' : w ≠ v := by simpa using hw
      ext i j
      rw [Matrix.map_apply, mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
        smul_eq_mul, map_add, map_mul, map_mul, map_sub, map_one, compAt_idemAt_ne v hw']
      simp only [OneMemClass.coe_one, Units.val_one, compAt_one_entry, zero_mul, zero_add, sub_zero, one_mul]
    · intro i j
      rw [mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact Subring.add_mem _ (Subring.mul_mem _ (idemAt_mem v) (by simpa using one_entry_mem (ALint L) i j))
        (Subring.mul_mem _ (one_sub_idemAt_mem v) (hU i j))
    · intro i j
      obtain ⟨y, hy, e⟩ := hκ i j
      refine ⟨y, hy, ?_⟩
      rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at e
      rw [← e, mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      simp only [OneMemClass.coe_one, Units.val_one]
      ring
    · intro x hx
      have hX : (x.1 : Matrix (Fin n) (Fin n) (AL L)) =
          idemAt v • (x.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - idemAt v) • 1 := by
        ext i j
        have h := away_eq_zero v hx i j
        rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
        linear_combination h
      apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, mixG_val, OneMemClass.coe_one, Units.val_one]
      rw [hX, mix_mul _ hp, mix_mul _ hp]
      simp only [mul_one, one_mul]

end GlobalTheory.InertLevel
