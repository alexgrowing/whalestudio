import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct

namespace GlobalTheory.IdemSplit

variable {R : Type*} [CommRing R] {n : ℕ}

def fold (e : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := e • M + (1 - e) • 1

theorem fold_mul_fold {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold e X * fold (1 - e) Y = e • X + (1 - e) • Y := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, h0, sub_zero]
  simp only [fold, sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, h0, h0',
    he, h1, zero_smul, zero_add, add_zero]
  exact add_comm _ _

theorem fold_mul_fold' {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold (1 - e) Y * fold e X = e • X + (1 - e) • Y := by
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h := fold_mul_fold he' Y X
  rw [sub_sub_cancel] at h
  rw [h, add_comm]

theorem fold_mul {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold e X * fold e Y = fold e (X * Y) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, h0, sub_zero]
  simp only [fold, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, h0, h0',
    he, h1, zero_smul, zero_add, add_zero]

theorem fold_one (e : R) : fold e (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [fold, ← add_smul, add_sub_cancel, one_smul]

theorem conjT_fold (σ : R →+* R) {e : R} (hσ : σ e = e) (M : Matrix (Fin n) (Fin n) R) :
    conjT σ (fold e M) = fold e (conjT σ M) := by
  ext i j
  simp only [conjT, fold, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

def unitsFold {e : R} (he : e * e = e) (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨fold e g, fold e (g⁻¹ : GL (Fin n) R), by rw [fold_mul he, Units.mul_inv, fold_one],
    by rw [fold_mul he, Units.inv_mul, fold_one]⟩

theorem unitsFold_mem_UGroup (σ : R →+* R) (hσ2 : ∀ x, σ (σ x) = x) {e : R} (he : e * e = e)
    (hσ : σ e = e) (g : GL (Fin n) R) (hg : g ∈ UGroup n σ hσ2) :
    unitsFold he g ∈ UGroup n σ hσ2 := by
  have hg' : (g : Matrix (Fin n) (Fin n) R) * conjT σ g = 1 := hg
  show fold e (g : Matrix (Fin n) (Fin n) R) * conjT σ (fold e (g : Matrix (Fin n) (Fin n) R)) = 1
  rw [conjT_fold σ hσ, fold_mul he, hg', fold_one]

theorem fold_apply (e : R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    fold e M i j = e * M i j + (1 - e) * (1 : Matrix (Fin n) (Fin n) R) i j := by
  simp [fold]

end GlobalTheory.IdemSplit

namespace GlobalTheory.CongSplit

open GlobalTheory.IdemSplit GlobalTheory.InertUmax

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L :=
  (1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1

theorem compAt_idemAt_self (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    compAt L v (idemAt L v) = 1 := by
  rw [idemAt, compAt_tmul, sgl_same]; rfl

theorem compAt_idemAt_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hw : w ≠ v) :
    compAt L w (idemAt L v) = 0 := by
  rw [idemAt, compAt_tmul, sgl_ne L v 1 hw, tmul_zero]

theorem idemAt_mul_self (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    idemAt L v * idemAt L v = idemAt L v := by
  apply sub_eq_zero.1
  apply eq_zero_of_compAt
  intro w
  rw [map_sub, map_mul]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self, mul_one, sub_self]
  · rw [compAt_idemAt_ne L v hw, mul_zero, sub_self]

theorem idemAt_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idemAt L v ∈ ALint L :=
  one_tmul_sgl_mem L v 1 (one_mem _)

theorem conjAL_idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    conjAL L (idemAt L v) = idemAt L v := by
  simp [conjAL, idemAt, Algebra.TensorProduct.map_tmul]

theorem one_apply_mem {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem compAt_one_apply {n : ℕ} (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i j : Fin n) :
    compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp

variable {L} in

def gaFold {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (g : GAf L n) : GAf L n :=
  ⟨unitsFold hf g.1, unitsFold_mem_UGroup (conjAL L) (conjAL_conjAL L) hf hσ g.1 g.2⟩

theorem gaFold_val {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (g : GAf L n) :
    ((gaFold hf hσ g).1 : Matrix (Fin n) (Fin n) (AL L)) = fold f (g.1 : Matrix (Fin n) (Fin n) (AL L)) :=
  rfl

theorem gaFold_mem_Umax {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (hfi : f ∈ ALint L)
    (g : GAf L n) (hg : g ∈ Umax L n) : gaFold hf hσ g ∈ Umax L n := by
  intro i j
  rw [gaFold_val, fold_apply]
  exact Subring.add_mem _ (Subring.mul_mem _ hfi (hg i j))
    (Subring.mul_mem _ (Subring.sub_mem _ (one_mem _) hfi) (one_apply_mem L i j))

theorem decomp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) (c : GAf L n), NG.Cong L n N c → ∃ a b : GAf L n, c = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
  intro L _ _ _ n v N c hc
  set e := idemAt L v with he_def
  have he : e * e = e := idemAt_mul_self L v
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hσ : conjAL L e = e := conjAL_idemAt L v
  have hσ' : conjAL L (1 - e) = 1 - e := by rw [map_sub, map_one, hσ]
  have hei : e ∈ ALint L := idemAt_mem L v
  have hei' : 1 - e ∈ ALint L := Subring.sub_mem _ (one_mem _) hei
  refine ⟨gaFold he hσ c, gaFold he' hσ' c, ?_, gaFold_mem_Umax L he hσ hei c hc.1, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show (c.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e _ * fold (1 - e) _
    rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]
  · intro w hw
    have hw' : w ≠ v := by simpa using hw
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add, map_mul, map_mul, map_sub, map_one,
      compAt_idemAt_ne L v hw', compAt_one_apply]
    simp
  · refine ⟨gaFold_mem_Umax L he' hσ' hei' c hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨(1 - e) * y, Subring.mul_mem _ hei' hy, ?_⟩
    rw [gaFold_val, fold_apply, sub_sub_cancel]
    linear_combination (1 - e) * hEq
  · intro x hx
    have hxf : (x.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e (x.1 : Matrix (Fin n) (Fin n) (AL L)) := by
      ext i j
      apply sub_eq_zero.1
      rw [fold_apply]
      apply eq_zero_of_compAt
      intro w
      rcases eq_or_ne w v with rfl | hw
      · rw [map_sub, map_add, map_mul, map_mul, map_sub, map_one, compAt_idemAt_self]
        ring
      · have h := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h
        rw [map_sub, map_add, map_mul, map_mul, map_sub, map_one, compAt_idemAt_ne L v hw,
          compAt_one_apply, h]
        ring
    apply Subtype.ext; apply Units.ext
    show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * fold (1 - e) _ = fold (1 - e) _ * (x.1 : Matrix (Fin n) (Fin n) (AL L))
    rw [hxf, fold_mul_fold he, fold_mul_fold' he]

end GlobalTheory.CongSplit
