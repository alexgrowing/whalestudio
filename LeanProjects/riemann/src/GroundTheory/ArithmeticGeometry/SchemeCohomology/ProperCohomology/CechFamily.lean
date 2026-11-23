import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace

universe w u

variable {X : TopCat.{u}} {ι : Type w} (U : ι → Opens X)
  {P P' P'' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}

structure CechFamily (P P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) where

  φ : ∀ {n : ℕ} (i : Fin (n + 1) → ι), P.obj (op (inter U i)) →+ P'.obj (op (inter U i))

  res_comm : ∀ {m n : ℕ} (i : Fin (m + 1) → ι) (j : Fin (n + 1) → ι) (h : inter U i ≤ inter U j)
    (x : P.obj (op (inter U j))), φ i (res P h x) = res P' h (φ j x)

namespace CechFamily

variable {U}

noncomputable section

def cochain (Φ : CechFamily U P P') (n : ℕ) : Cochain P U n →+ Cochain P' U n where
  toFun σ i := Φ.φ i (σ i)
  map_zero' := by
    funext i
    exact map_zero _
  map_add' σ τ := by
    funext i
    exact map_add _ _ _

lemma cochain_apply (Φ : CechFamily U P P') (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 1) → ι) :
    Φ.cochain n σ i = Φ.φ i (σ i) := rfl

lemma cochain_d (Φ : CechFamily U P P') (n : ℕ) (σ : Cochain P U n) :
    Φ.cochain (n + 1) (d P U n σ) = d P' U n (Φ.cochain n σ) := by
  funext i
  rw [cochain_apply, d_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Φ.res_comm]
  rfl

lemma cochain_mem_cocycles (Φ : CechFamily U P P') {n : ℕ} {σ : Cochain P U n}
    (hσ : σ ∈ cocycles P U n) : Φ.cochain n σ ∈ cocycles P' U n := by
  rw [mem_cocycles] at hσ ⊢
  rw [← cochain_d, hσ, map_zero]

lemma cochain_mem_coboundaries (Φ : CechFamily U P P') {n : ℕ} {σ : Cochain P U n}
    (hσ : σ ∈ coboundaries P U n) : Φ.cochain n σ ∈ coboundaries P' U n := by
  cases n with
  | zero =>
    rw [coboundaries_zero, AddSubgroup.mem_bot] at hσ ⊢
    rw [hσ, map_zero]
  | succ n =>
    rw [coboundaries_succ] at hσ ⊢
    obtain ⟨τ, rfl⟩ := hσ
    exact ⟨Φ.cochain n τ, (cochain_d Φ n τ).symm⟩

def cocycles (Φ : CechFamily U P P') (n : ℕ) : cocycles P U n →+ GroundTheory.Arith.SchemeCoh.cocycles P' U n :=
  AddMonoidHom.codRestrict ((Φ.cochain n).comp (GroundTheory.Arith.SchemeCoh.cocycles P U n).subtype) _
    fun σ => cochain_mem_cocycles Φ σ.2

def cechH (Φ : CechFamily U P P') (n : ℕ) : GroundTheory.Arith.SchemeCoh.cechH P U n →+
    GroundTheory.Arith.SchemeCoh.cechH P' U n :=
  QuotientAddGroup.map _ _ (Φ.cocycles n) fun σ hσ => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact cochain_mem_coboundaries Φ (AddSubgroup.mem_addSubgroupOf.1 hσ)

lemma cechH_cls (Φ : CechFamily U P P') {n : ℕ} (σ : Cochain P U n) (hσ : d P U n σ = 0) :
    Φ.cechH n (cls σ hσ) = cls (Φ.cochain n σ) (by rw [← cochain_d, hσ, map_zero]) := rfl

def ofHom (f : P ⟶ P') : CechFamily U P P' where
  φ i := (f.app (op (inter U i))).hom
  res_comm i j h x := app_res f h x

lemma ofHom_cechH (f : P ⟶ P') (n : ℕ) (x : GroundTheory.Arith.SchemeCoh.cechH P U n) :
    (ofHom (U := U) f).cechH n x = cechHMap U f n x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rfl

def comp (Φ : CechFamily U P P') (Ψ : CechFamily U P' P'') : CechFamily U P P'' where
  φ i := (Ψ.φ i).comp (Φ.φ i)
  res_comm i j h x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [Φ.res_comm, Ψ.res_comm]

lemma comp_cechH (Φ : CechFamily U P P') (Ψ : CechFamily U P' P'') (n : ℕ)
    (x : GroundTheory.Arith.SchemeCoh.cechH P U n) :
    (Φ.comp Ψ).cechH n x = Ψ.cechH n (Φ.cechH n x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rfl

def add (Φ Ψ : CechFamily U P P') : CechFamily U P P' where
  φ i := Φ.φ i + Ψ.φ i
  res_comm i j h x := by
    simp only [AddMonoidHom.add_apply, map_add]
    rw [Φ.res_comm, Ψ.res_comm]

lemma add_cechH (Φ Ψ : CechFamily U P P') (n : ℕ) (x : GroundTheory.Arith.SchemeCoh.cechH P U n) :
    (Φ.add Ψ).cechH n x = Φ.cechH n x + Ψ.cechH n x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechH_cls, cechH_cls, cechH_cls]
  exact cls_congr U (by funext i; rfl) _ (by
    rw [map_add, ← cochain_d, ← cochain_d, hσ, map_zero, map_zero, add_zero])

lemma cechH_congr {Φ Ψ : CechFamily U P P'} (h : ∀ {n : ℕ} (i : Fin (n + 1) → ι) x, Φ.φ i x = Ψ.φ i x)
    (n : ℕ) (x : GroundTheory.Arith.SchemeCoh.cechH P U n) : Φ.cechH n x = Ψ.cechH n x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechH_cls, cechH_cls]
  exact cls_congr U (by funext i; exact h i _) _ _

end

end CechFamily

end GroundTheory.Arith.SchemeCoh
