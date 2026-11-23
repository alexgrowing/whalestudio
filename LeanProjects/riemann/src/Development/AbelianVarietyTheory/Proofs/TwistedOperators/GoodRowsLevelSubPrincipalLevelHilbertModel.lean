import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult MeasureTheory NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodRowsLevel

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_lev_of_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {x : GL (Fin (Yc D 0).rank) (EAf D)}
    (hx : x ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
      levFn (R.βY 0) (R.dat0 P) x = levFn (R.βY 0) (R.dat0 R.triv) x := by
  have h1 : rTup (R.βY 0) (R.dat0 R.triv) x = 1 := Subgroup.mem_bot.1 hx.2
  have h1' : rTup (R.βY 0) (R.dat0 P) x = 1 := h1
  refine ⟨⟨hx.1, ?_⟩, ?_⟩
  · rw [h1']; exact Subgroup.one_mem _
  · unfold levFn
    rw [h1, h1', blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]
    rfl

theorem isMultMap_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {S : MMap (R.MY 0)}
    (h : IsMultMap R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) S) :
    IsMultMap R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) S where
  aut := h.aut
  cusp := h.cusp
  equiv := h.equiv
  cont := h.cont
  lev v k hk g := by
    have hk2 : k ∈ GfC (Yc D 0) ⊓ (Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)).comap (finE (Yc D 0)) := hk
    rw [Subgroup.mem_inf, Subgroup.mem_comap] at hk2
    have hm := mem_lev_of_triv R P hk2.2
    have hk' : k ∈ levS _ (R.βY 0) (R.dat0 P) :=
      (show k ∈ GfC (Yc D 0) ⊓ (Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)).comap (finE (Yc D 0)) from
        Subgroup.mem_inf.2 ⟨hk2.1, Subgroup.mem_comap.2 hm.1⟩)
    rw [h.lev v k hk' g]
    simp only [levChi]
    rw [hm.2]

theorem eeat_le_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) : R.EEat P ≤ R.EEat R.triv := by
  intro S hS
  rw [RealDat.EEat, goodPart, Submodule.mem_inf] at hS ⊢
  refine ⟨?_, hS.2⟩
  exact Submodule.span_mono (fun S' hS' => isMultMap_triv R P hS') hS.1

theorem eeat_sub_principal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → (∀ P, R.EEat P ≤ R.EEat R.triv) ∧ (∀ P, R.EEat P ≤ LinearMap.range R.HE.e) ∧ ∀ P, ∀ S ∈ R.EEat P, ∀ S' ∈ R.EEat P, IsMultIP (R.MY 0) R.ν0 R.fd0 S S' (ipM (R.MY 0) R.ν0 R.fd0 S S') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hM
  have h2 : ∀ P, R.EEat P ≤ LinearMap.range R.HE.e := fun P => by
    rw [hM.HE.2.1]; exact eeat_le_triv R P
  refine ⟨eeat_le_triv R, h2, ?_⟩
  intro P S hS S' hS'
  obtain ⟨x, rfl⟩ := h2 P hS
  obtain ⟨y, rfl⟩ := h2 P hS'
  rw [← hM.HE.2.2 x y]
  exact GlobalTheory.SchurPolar.isMultiplicityInner_inner (R.MY 0) R.ν0 R.fd0 R.HE _ hM.HE x y

end GlobalTheory.GoodRowsLevel
