import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import GroundTheory.LocalFields.LocalFourierChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (n : ℕ) (N : ℤ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ i, x.toAdd i ∈ valBall k N}
  mul_mem' := by
    intro a b ha hb i
    simpa using add_mem (ha i) (hb i)
  one_mem' := by
    intro i
    simp
  inv_mem' := by
    intro a ha i
    simpa using neg_mem (ha i)

theorem mem_box {n : ℕ} {N : ℤ} {x : Multiplicative (Fin n → k)} :
    x ∈ box k n N ↔ ∀ i, x.toAdd i ∈ valBall k N := Iff.rfl

theorem box_antitone (n : ℕ) {M N : ℤ} (h : M ≤ N) : box k n N ≤ box k n M :=
  fun _ hx i => valBall_antitone h (hx i)

def chi (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) : Multiplicative (Fin n → k) →* ℂˣ where
  toFun x := Circle.toUnits (ψ (a ⬝ᵥ x.toAdd))
  map_one' := by simp
  map_mul' x y := by simp [dotProduct_add, AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (x : Multiplicative (Fin n → k)) :
    chi k ψ a x = Circle.toUnits (ψ (a ⬝ᵥ x.toAdd)) := rfl

abbrev chiOn (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (H : Subgroup (Multiplicative (Fin n → k))) :
    H →* ℂˣ := (chi k ψ a).comp H.subtype

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun x => MirU_le_Mir k n ⟨x, rfl⟩)

@[simp] theorem coe_unipMir (n : ℕ) (x : Multiplicative (Fin n → k)) :
    ((unipMir k n x : Mir k n) : GL (Fin (n + 1)) k) = unip k n x := rfl

variable {k}

theorem exists_unipMir {n : ℕ} (u : MirUin k n) : ∃ x, unipMir k n x = (u : Mir k n) := by
  obtain ⟨x, hx⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  exact ⟨x, Subtype.ext hx⟩

theorem mem_chi_zero {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (τ : Representation ℂ (Mir k (m + 1)) V) {w : V} (hw : w ∈ twKer τ (MirUin k (m + 1)) 1) :
    w ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤ (chiOn k ψ 0 ⊤) := by
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨u, w, rfl⟩
  obtain ⟨x, hx⟩ := exists_unipMir u
  refine Submodule.subset_span ⟨⟨x, trivial⟩, w, ?_⟩
  simp [chi_apply, hx]

theorem mem_chi_row {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (τ : Representation ℂ (Mir k (m + 1)) V) (g : GL (Fin (m + 1)) k) {w : V}
    (hw : w ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) :
    τ (levi k (m + 1) g⁻¹) w ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤
      (chiOn k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⊤) := by
  have hle : twKer τ (MirUin k (m + 1)) (mirChar k ψ m) ≤
      (twKer (τ.comp (unipMir k (m + 1))) ⊤
        (chiOn k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⊤)).comap
        (τ (levi k (m + 1) g⁻¹)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    obtain ⟨x, hx⟩ := exists_unipMir u
    set y : Multiplicative (Fin (m + 1) → k) :=
      Multiplicative.ofAdd (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec x.toAdd)
      with hy
    have hconj : levi k (m + 1) g⁻¹ * (u : Mir k (m + 1)) = unipMir k (m + 1) y * levi k (m + 1) g⁻¹ := by
      apply Subtype.ext
      show glEmb k (m + 1) g⁻¹ * ((u : Mir k (m + 1)) : GL (Fin (m + 2)) k) = unip k (m + 1) y * glEmb k (m + 1) g⁻¹
      rw [← hx, coe_unipMir, glEmb_mul_unip']
    have hchar : mirChar k ψ m u = chi k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) y := by
      rw [mirChar_eq k ψ m u x (by rw [← hx]; rfl), chi_apply]
      congr 2
      have : (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⬝ᵥ y.toAdd =
          ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec y.toAdd) (Fin.last m) := rfl
      rw [this, hy, toAdd_ofAdd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, hconj, map_mul,
      Module.End.mul_apply, hchar]
    exact Submodule.subset_span ⟨⟨y, trivial⟩, τ (levi k (m + 1) g⁻¹) w, rfl⟩
  exact hle hw

end GlobalTheory.CompanionTheory.MirFourier

end
