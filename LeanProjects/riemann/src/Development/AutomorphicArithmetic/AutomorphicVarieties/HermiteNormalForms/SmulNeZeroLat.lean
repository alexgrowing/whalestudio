import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulStrictMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open NumberField Matrix

noncomputable section

namespace UpperTheory.V.KT

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

abbrev NZ : Type := {y : Lat L N // y ≠ 0}

def qc (y : NZ L N) : HS L N →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (ev y.1)

def Psd : Set (HS L N) := {h | open ComplexOrder in ∀ w, (mat h w).PosSemidef}

variable {L N}

@[simp] theorem qc_apply (y : NZ L N) (h : HS L N) : qc L N y h = q h y.1 := rfl

theorem poly_qc : ConeExtensionAcyclic.poly (qc L N) = Ry L N := by
  ext h; exact ⟨fun H y hy => H ⟨y, hy⟩, fun H y => H y.1 y.2⟩

open ComplexOrder in
theorem smul_mem_Psd (g : Gm L N) {h : HS L N} (hh : h ∈ Psd L N) : g • h ∈ Psd L N :=
  fun w => (hh w).conjTranspose_mul_mul_same _

theorem smul_ne_zero_lat (g : Gm L N) {y : Lat L N} (hy : y ≠ 0) : g • y ≠ 0 :=
  fun e => hy (by rw [← inv_smul_smul g y, e, smul_zero])

def actL (g : Gm L N) : HS L N →L[ℝ] HS L N :=
  LinearMap.toContinuousLinearMap (pull ((g⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)))

@[simp] theorem actL_apply (g : Gm L N) (h : HS L N) : actL g h = g • h := rfl

theorem isVert_smul (g : Gm L N) {h : HS L N} (hh : ConeExtensionAcyclic.IsVert (qc L N) h) :
    ConeExtensionAcyclic.IsVert (qc L N) (g • h) := by
  refine ⟨?_, fun k hk => ?_⟩
  · have := hh.1
    rw [poly_qc] at this ⊢
    exact smul_mem_Ry g this
  · have : g⁻¹ • k = 0 := hh.2 _ fun y hy => by
      have := hk ⟨g • y.1, smul_ne_zero_lat g y.2⟩ (by simpa [q_smul] using hy)
      simpa [q_smul] using this
    rw [← smul_inv_smul g k, this, smul_zero]

variable (L N)

abbrev Vx : Type := ConeExtensionAcyclic.Vert (qc L N)

instance : MulAction (Gm L N) (Vx L N) where
  smul g v := ⟨g • v.1, isVert_smul g v.2⟩
  one_smul v := Subtype.ext (one_smul _ v.1)
  mul_smul g k v := Subtype.ext (mul_smul g k v.1)

variable {L N}

theorem Vx.smul_val (g : Gm L N) (v : Vx L N) : (g • v).1 = g • v.1 := rfl

theorem smul_mem_simp (g : Gm L N) {n : ℕ} {t : Fin n → Vx L N}
    (ht : t ∈ ConeExtensionAcyclic.simp (qc L N) (Psd L N) n) :
    (fun j => g • t j) ∈ ConeExtensionAcyclic.simp (qc L N) (Psd L N) n := by
  obtain ⟨x, hx, hj⟩ := ht
  refine ⟨x.comp (actL g⁻¹), fun k hk h0 => ?_, fun j h' hh' => ?_⟩
  · exact hx _ (smul_mem_Psd _ hk) (fun e => h0 (by
      have e' : g⁻¹ • k = 0 := e
      rw [← smul_inv_smul g k, e', smul_zero]))
  · rw [poly_qc] at hh'
    have := hj j (g⁻¹ • h') (by rw [poly_qc]; exact smul_mem_Ry _ hh')
    simpa [Vx.smul_val] using this

variable (L N)

def Sx (p : ℕ) : Type := {t : Fin (p + 1) → Vx L N // t ∈ ConeExtensionAcyclic.simp (qc L N) (Psd L N) (p + 1)}

instance (p : ℕ) : MulAction (Gm L N) (Sx L N p) where
  smul g t := ⟨fun j => g • t.1 j, smul_mem_simp g t.2⟩
  one_smul t := Subtype.ext (funext fun j => one_smul _ (t.1 j))
  mul_smul g k t := Subtype.ext (funext fun j => mul_smul g k (t.1 j))

def Sx.face (p : ℕ) (i : Fin (p + 2)) (t : Sx L N (p + 1)) : Sx L N p :=
  ⟨t.1 ∘ i.succAbove, ConeExtensionAcyclic.nerve_faceClosed _ _ _ t.1 t.2 i⟩

variable {L N}

theorem Sx.smul_val {p : ℕ} (g : Gm L N) (t : Sx L N p) (j : Fin (p + 1)) :
    (g • t).1 j = g • t.1 j := rfl

theorem Sx.face_smul (p : ℕ) (i : Fin (p + 2)) (g : Gm L N) (t : Sx L N (p + 1)) :
    Sx.face L N p i (g • t) = g • Sx.face L N p i t := rfl

def nearVx (A : Matrix (Fin N) (Fin N) (𝓞 L)) : Set (Vx L N) := {v | ColsMin A v.1}

abbrev BI (L : Type) [Field L] [NumberField L] : Type := Module.Free.ChooseBasisIndex ℤ (𝓞 L)

def intVec (c : Fin N × BI L → ℤ) : Lat L N :=
  fun a => ∑ i, c (a, i) • RingOfIntegers.basis L i

def realVec (x : Fin N × BI L → ℝ) : VR L N :=
  fun w a => ∑ i, (x (a, i) : ℂ) * embO w (RingOfIntegers.basis L i)

def gram (h : HS L N) : Matrix (Fin N × BI L) (Fin N × BI L) ℝ :=
  Matrix.of fun s t => ∑ w, (star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
    embO w (RingOfIntegers.basis L t.2)).re

end UpperTheory.V.KT
