import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocLocGLInvVal

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.HidaSetting

variable (I : AutInst)

def eOf (a : Af I.F) : I.E ⊗[I.F] Af I.F := (1 : I.E) ⊗ₜ[I.F] a

theorem LocB_eOf_mul (a b : Af I.F) : eOf I a * eOf I b = eOf I (a * b) := by
  unfold eOf
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem LocB_eOf_add (a b : Af I.F) : eOf I a + eOf I b = eOf I (a + b) := by
  unfold eOf
  rw [TensorProduct.tmul_add]

theorem LocB_eOf_sub (a b : Af I.F) : eOf I a - eOf I b = eOf I (a - b) := by
  unfold eOf
  rw [TensorProduct.tmul_sub]

theorem LocB_eOf_one : eOf I 1 = 1 := rfl

theorem LocB_eOf_zero : eOf I 0 = 0 := by
  unfold eOf
  rw [TensorProduct.tmul_zero]

theorem LocB_eOf_natCast (m : ℕ) : eOf I (m : Af I.F) = (m : I.E ⊗[I.F] Af I.F) := by
  induction m with
  | zero => rw [Nat.cast_zero, LocB_eOf_zero, Nat.cast_zero]
  | succ m ih => rw [Nat.cast_succ, ← LocB_eOf_add, ih, LocB_eOf_one, Nat.cast_succ]

theorem LocB_eOf_idem (a : Af I.F) (ha : a * a = a) : eOf I a * eOf I a = eOf I a := by
  rw [LocB_eOf_mul, ha]

theorem LocB_sig_eOf (a : Af I.F) : Formalism.UG.sigR I.cm.sig (Af I.F) (eOf I a) = eOf I a := by
  simp [Formalism.UG.sigR, eOf, Algebra.TensorProduct.map_tmul]

theorem LocB_eOf_mem (a : Af I.F) (ha : a ∈ Formalism.UG.intAd I.F) : eOf I a ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
  show eOf I a ∈ Formalism.UG.tensInt (F := I.F) (Af I.F) (Formalism.UG.intOE I.E) (Formalism.UG.intAd I.F)
  exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

open scoped Classical in

def locG (a : Af I.F) (x : I.Gf) : I.Gf :=
  if h : a * a = a then
    ⟨locGL (eOf I a) (LocB_eOf_idem I a h) (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)), by
      show Formalism.UG.cT _ (locM (eOf I a) (I.fmat x)) * _ * locM (eOf I a) (I.fmat x) = _
      exact Loc_locM_unitary _ _ (LocB_eOf_idem I a h) (LocB_sig_eOf I a) _ _ x.2⟩
  else x

theorem LocB_fmat (a : Af I.F) (ha : a * a = a) (x : I.Gf) :
    I.fmat (locG I a x) = locM (eOf I a) (I.fmat x) := by
  rw [locG, dif_pos ha]
  exact Loc_locGL_val _ _ _

theorem LocB_ext (x y : I.Gf) (h : I.fmat x = I.fmat y) : x = y := Subtype.ext (Units.ext h)

theorem LocB_fmat_mul (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl

theorem LocB_fmat_one : I.fmat (1 : I.Gf) = 1 := rfl

theorem LocB_locG_mul (a : Af I.F) (ha : a * a = a) (x y : I.Gf) :
    locG I a (x * y) = locG I a x * locG I a y := by
  apply LocB_ext
  rw [LocB_fmat_mul, LocB_fmat I a ha, LocB_fmat I a ha, LocB_fmat I a ha, LocB_fmat_mul]
  exact Loc_locM_mul _ (LocB_eOf_idem I a ha) _ _

theorem LocB_locG_add (a b : Af I.F) (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) (x : I.Gf) :
    locG I a x * locG I b x = locG I (a + b) x := by
  have hab2 : (a + b) * (a + b) = a + b := by
    calc (a + b) * (a + b) = a * a + a * b + b * a + b * b := by ring
      _ = a + b := by rw [ha, hb, hab, mul_comm b a, hab]; ring
  have hab' : eOf I a * eOf I b = 0 := by rw [LocB_eOf_mul, hab, LocB_eOf_zero]
  apply LocB_ext
  rw [LocB_fmat_mul, LocB_fmat I a ha, LocB_fmat I b hb, LocB_fmat I (a + b) hab2,
    Loc_locM_add _ _ hab', LocB_eOf_add]

theorem LocB_locG_split (a : Af I.F) (ha : a * a = a) (x : I.Gf) :
    locG I a x * locG I (1 - a) x = x := by
  have h1a : (1 - a) * (1 - a) = 1 - a := by
    have : (1 - a) * (1 - a) = 1 - a - a + a * a := by ring
    rw [this, ha]
    ring
  apply LocB_ext
  rw [LocB_fmat_mul, LocB_fmat I a ha, LocB_fmat I (1 - a) h1a, ← LocB_eOf_sub, LocB_eOf_one]
  exact Loc_locM_split _ (LocB_eOf_idem I a ha) _

theorem LocB_locG_zero (x : I.Gf) : locG I 0 x = 1 := by
  apply LocB_ext
  rw [LocB_fmat I 0 (mul_zero 0), LocB_eOf_zero, Loc_locM_zero, LocB_fmat_one]

theorem LocB_smul_mem (Λ : Submodule (Formalism.MainNotions.S.IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F))
    (a : Af I.F) (ha : a ∈ Formalism.UG.intAd I.F) {v : Fin I.n → I.E ⊗[I.F] Af I.F} (hv : v ∈ Λ) :
    eOf I a • v ∈ Λ := by
  have := Λ.smul_mem (⟨eOf I a, LocB_eOf_mem I a ha⟩ : Formalism.MainNotions.S.IntAf I.F I.E) hv
  exact this

theorem LocB_locM_mulVec (e : I.E ⊗[I.F] Af I.F) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (v : Fin I.n → I.E ⊗[I.F] Af I.F) : locM e M *ᵥ v = v + e • (M *ᵥ v - v) := by
  rw [locM, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec]

theorem LocB_Kset (a : Af I.F) (ha : a * a = a) (hi : a ∈ Formalism.UG.intAd I.F) (x : I.Gf) (hx : x ∈ I.Kset) :
    locG I a x ∈ I.Kset := by
  have fwd : ∀ w : I.Gf, w ∈ I.Kset → ∀ y ∈ I.Lf, I.fmat (locG I a w) *ᵥ y ∈ I.Lf := by
    intro w hw y hy
    have hw' : ∀ y, y ∈ I.Lf ↔ I.fmat w *ᵥ y ∈ I.Lf := hw
    rw [LocB_fmat I a ha, LocB_locM_mulVec]
    exact I.Lf.add_mem hy (LocB_smul_mem I _ a hi (I.Lf.sub_mem ((hw' y).mp hy) hy))
  have hxinv : x⁻¹ ∈ I.Kset := by
    show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    exact (Formalism.UG.stabGL I.Lf).inv_mem hx
  have hl1 : locG I a 1 = 1 := LocB_ext I _ _ (by
    rw [LocB_fmat I a ha, LocB_fmat_one, Loc_locM_one])
  show ∀ y, y ∈ I.Lf ↔ I.fmat (locG I a x) *ᵥ y ∈ I.Lf
  intro y
  refine ⟨fwd x hx y, fun hy => ?_⟩
  have := fwd x⁻¹ hxinv _ hy
  rwa [Matrix.mulVec_mulVec, ← LocB_fmat_mul, ← LocB_locG_mul I a ha, inv_mul_cancel, hl1,
    LocB_fmat_one, Matrix.one_mulVec] at this

theorem LocB_InMod (m : ℕ) (S : Set (VA I)) (a : Af I.F) (hi : a ∈ Formalism.UG.intAd I.F) (v : VA I)
    (hv : InMod I m S v) : InMod I m S (eOf I a • v) := by
  have hv' : v ∈ Submodule.span (Formalism.MainNotions.S.IntAf I.F I.E) S ⊔ mL I m := hv
  have := (Submodule.span (Formalism.MainNotions.S.IntAf I.F I.E) S ⊔ mL I m).smul_mem
    (⟨eOf I a, LocB_eOf_mem I a hi⟩ : Formalism.MainNotions.S.IntAf I.F I.E) hv'
  exact this

theorem LocB_K2set {r k : ℕ} (g : ℕ) (e0 : Fin r → VA I) (z0 : VA I) (β : Fin k → VA I)
    (a : Af I.F) (ha : a * a = a) (hi : a ∈ Formalism.UG.intAd I.F) (x : I.Gf) (hx : x ∈ K2set I g e0 z0 β) :
    locG I a x ∈ K2set I g e0 z0 β := by
  have hx' : x ∈ I.Kset ∧ K2cong I g e0 z0 β x := hx
  obtain ⟨hK, h1, h2, h3⟩ := hx'
  have key : ∀ w : VA I, (I.fmat (locG I a x) - 1) *ᵥ w = eOf I a • ((I.fmat x - 1) *ᵥ w) := by
    intro w
    rw [LocB_fmat I a ha, Loc_locM_sub_one]
  refine And.intro (LocB_Kset I a ha hi x hK) (And.intro ?_ (And.intro ?_ ?_))
  · intro r'
    rw [key]
    exact LocB_InMod I _ _ a hi _ (h1 r')
  · rw [key]
    exact LocB_InMod I _ _ a hi _ h2
  · intro i
    rw [key]
    exact LocB_InMod I _ _ a hi _ (h3 i)

theorem LocB_Kg (g : ℕ) (a c : Af I.F) (ha : a * a = a) (hc : c ∈ Formalism.UG.intAd I.F)
    (hgc : (g : Af I.F) * c = 1 - a) (x : I.Gf) (hx : x ∈ I.Kset) : locG I (1 - a) x ∈ I.Kg g := by
  have h1a : (1 - a) * (1 - a) = 1 - a := by
    have : (1 - a) * (1 - a) = 1 - a - a + a * a := by ring
    rw [this, ha]
    ring
  have hi1a : 1 - a ∈ Formalism.UG.intAd I.F := by
    rw [← hgc]
    exact mul_mem (natCast_mem _ g) hc
  have hx' : ∀ y, y ∈ I.Lf ↔ I.fmat x *ᵥ y ∈ I.Lf := hx
  refine And.intro (LocB_Kset I (1 - a) h1a hi1a x hx) (fun y hy => ?_)
  refine ⟨eOf I c • ((I.fmat x - 1) *ᵥ y), LocB_smul_mem I _ c hc ?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact I.Lf.sub_mem ((hx' y).mp hy) hy
  · rw [LocB_fmat I (1 - a) h1a, Loc_locM_sub_one, ← hgc, ← LocB_eOf_mul, LocB_eOf_natCast, mul_smul]

end PI.MassDataKppVolLemmas
