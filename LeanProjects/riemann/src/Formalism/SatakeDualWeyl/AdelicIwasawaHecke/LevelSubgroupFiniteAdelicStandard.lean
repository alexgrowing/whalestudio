import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

def easyc_fstAdd : ↥(stdLat (n := Fin 2) (A := ℚ) ℤ) →+ ZMod 2 where
  toFun x := (((x : Fin 2 → ℚ) 0).num : ZMod 2)
  map_zero' := by simp
  map_add' := by
    intro x y
    obtain ⟨a, ha⟩ := (mem_stdLat_iff' (R := ℤ) (x : Fin 2 → ℚ)).1 x.2 0
    obtain ⟨b, hb⟩ := (mem_stdLat_iff' (R := ℤ) (y : Fin 2 → ℚ)).1 y.2 0
    simp only [algebraMap_int_eq, eq_intCast] at ha hb
    simp only [Submodule.coe_add, Pi.add_apply, ← ha, ← hb]
    rw [← Int.cast_add, Rat.num_intCast, Rat.num_intCast, Rat.num_intCast]
    push_cast; rfl

def easyc_fst : ↥(stdLat (n := Fin 2) (A := ℚ) ℤ) →ₗ[ℤ] ZMod 2 := easyc_fstAdd.toIntLinearMap

def easyc_swap : GL (Fin 2) ℚ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

section Lattice

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type} [Fintype n]
  [DecidableEq n] (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

theorem easyc_inclE_mem (e : E) (he : e ∈ intOE E) :
    inclE (F := F) R e ∈ tensInt (F := F) R (intOE E) S₂ := by
  apply Subring.subset_closure
  left
  exact ⟨⟨e, he⟩, rfl⟩

theorem easyc_single_mem (i : n) :
    (Pi.single i (1 : E) : n → E) ∈ stdLat (n := n) (A := E) (𝓞 E) := by
  rw [mem_stdLat_iff']
  intro k
  by_cases hk : k = i
  · subst hk; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [hk]⟩

theorem easyc_latS_std :
    latS (F := F) R (tensInt (F := F) R (intOE E) S₂) (stdLat (n := n) (A := E) (𝓞 E)) =
      stdLat (n := n) (A := E ⊗[F] R) ↥(tensInt (F := F) R (intOE E) S₂) := by
  apply le_antisymm
  · rw [latS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_stdLat_iff']
    intro i
    have hxi := (mem_stdLat_iff' (R := 𝓞 E) x).1 hx i
    have hm : x i ∈ intOE E := by
      obtain ⟨y, hy⟩ := hxi
      exact ⟨y, hy⟩
    exact ⟨⟨_, easyc_inclE_mem R S₂ (x i) hm⟩, rfl⟩
  · intro x hx
    rw [mem_stdLat_iff'] at hx
    choose s hs using hx
    have hx : x = ∑ i, s i • (fun j => inclE (F := F) R ((Pi.single i (1 : E) : n → E) j)) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single j]
      · simp [← hs j, Algebra.smul_def]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨_, easyc_single_mem i, rfl⟩

end Lattice

theorem level_subgroup_finite_adelic_standard : Formalism.UG.LevelAfLStd := by
  intro F E _ _ _ _ _ n _ _ σ J
  unfold levelAfL levelAf
  rw [easyc_latS_std]

theorem level_subgroup_local_standard : Formalism.UG.LevelVLStd := by
  intro F E _ _ _ _ _ n _ _ σ J v
  unfold levelVL levelV
  rw [easyc_latS_std]

end Formalism.UG.P
