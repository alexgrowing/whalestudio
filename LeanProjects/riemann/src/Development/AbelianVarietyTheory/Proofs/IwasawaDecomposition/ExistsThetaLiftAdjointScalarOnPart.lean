import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalChoice

theorem exists_pin (P : ℝ → Prop) (h : ∀ a b, P a → P b → a = b) : ∃ a, ∀ l, P l → a = l := by
  by_cases hP : ∃ a, P a
  · obtain ⟨a, ha⟩ := hP
    exact ⟨a, fun l hl => h a l ha hl⟩
  · exact ⟨0, fun l hl => absurd ⟨l, hl⟩ hP⟩

theorem exists_eig {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (f : M → M) (c : ℝ) :
    ∃ a : ℝ, (∀ l : ℝ, S ≠ ⊥ → (∀ x ∈ S, f x = (l : ℂ) • x) → a = l) ∧ (S = ⊥ → a = c) := by
  rcases eq_or_ne S ⊥ with hW | hW
  · exact ⟨c, fun l h => absurd hW h, fun _ => rfl⟩
  · obtain ⟨a, ha⟩ := exists_pin (fun l => ∀ x ∈ S, f x = (l : ℂ) • x) (fun a b ha hb => by
        obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
        exact_mod_cast smul_left_injective ℂ hx0 ((ha x hx).symm.trans (hb x hx)))
    exact ⟨a, fun l _ h => ha l h, fun h => absurd h hW⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev withScal (R : RealDat D A Ks) (lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ) (kap : ℝ) :
    RealDat D A Ks := { R with lam := lam, kap := kap }

def OffEq (R : RealDat D A Ks) (F : Face D A) (b : Bool) (i : Fin D.R.m) (p : A.fam.base.Ix)
    (v : InfinitePlace D.what₂.LL) (l : ℝ) : Prop :=
  ∀ x, (R.toCx F).tC F.cr b i A.μ0 (Cx.cpt A.v0.embedding x) ∈ (R.toCx F).Wp i p → ∀ y,
      inner ℂ ((R.toCx F).wC b i v (Cx.cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec x)))
          ((R.toCx F).wC b i v (Cx.cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec y))) =
        ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((Cx.lv (F.fc (R.toCx F).zs) b).XT i A.μ0) v x y

theorem OffEq.unique {R : RealDat D A Ks} {F : Face D A} {b : Bool} {i : Fin D.R.m} {p : A.fam.base.Ix}
    {v : InfinitePlace D.what₂.LL} {l l' : ℝ} (hp : R.PartAt F b i p v) (h : OffEq R F b i p v l)
    (h' : OffEq R F b i p v l') : l = l' := by
  obtain ⟨x, hx, hx0⟩ := hp
  have h1 := (h x hx x).symm.trans (h' x hx x)
  have h2 := mul_right_cancel₀ (by exact_mod_cast hx0) h1
  exact_mod_cast h2

theorem zs_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) :
    ((withScal R lam kap).toCx F).zs = (R.toCx F).zs := rfl

theorem partAt_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) (b i p v) :
    (withScal R lam kap).PartAt F b i p v ↔ R.PartAt F b i p v := Iff.rfl

theorem offEq_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) (b i p v l) :
    OffEq (withScal R lam kap) F b i p v l ↔ OffEq R F b i p v l := Iff.rfl

theorem exists_thetaLift_adjoint_scalar_on_part (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (p : A.fam.base.Ix) (c : ℝ) :
    ∃ a : ℝ, (∀ l : ℝ, R.Wp i p ≠ ⊥ →
      (∀ x ∈ R.Wp i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x) → a = l) ∧ (R.Wp i p = ⊥ → a = c) :=
  exists_eig (R.Wp i p) (fun x => R.thG i t (LinearMap.adjoint (R.thG i t) x)) c

theorem exists_lamOff (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (p : A.fam.base.Ix)
    (v : InfinitePlace D.what₂.LL) (c : ℝ) :
    ∃ a : ℝ, (∀ b (l : ℝ), R.PartAt F b i p v → (b = false ∨ ¬ R.PartAt F false i p v) → OffEq R F b i p v l → a = l) ∧
      ((∀ b, ¬ R.PartAt F b i p v) → a = c) := by
  by_cases h0 : R.PartAt F false i p v
  · obtain ⟨a, ha⟩ := exists_pin (OffEq R F false i p v) (fun a b => OffEq.unique h0)
    refine ⟨a, fun b l _ hb h => ?_, fun h => absurd h0 (h false)⟩
    rcases hb with rfl | hb
    · exact ha l h
    · exact absurd h0 hb
  · by_cases h1 : R.PartAt F true i p v
    · obtain ⟨a, ha⟩ := exists_pin (OffEq R F true i p v) (fun a b => OffEq.unique h1)
      refine ⟨a, fun b l hp _ h => ?_, fun h => absurd h1 (h true)⟩
      cases b
      · exact absurd hp h0
      · exact ha l h
    · refine ⟨c, fun b l hp _ _ => ?_, fun _ => rfl⟩
      cases b
      · exact absurd hp h0
      · exact absurd hp h1

theorem exists_isScal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, ∃ lam kap, ({ R with lam := lam, kap := kap } : RealDat D A Ks).IsScal F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F
  classical
  choose f0 hf0 hf0' using fun i t p => exists_thetaLift_adjoint_scalar_on_part R i t p (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  choose f1 hf1 hf1' using fun i p v => exists_lamOff R F i p v (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  obtain ⟨lam, h0, h1⟩ : ∃ lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ,
      (∀ i t p, lam i t p A.v0 = f0 i t p) ∧ ∀ i t p v, v ≠ A.v0 → lam i t p v = f1 i p v :=
    ⟨fun i t p v => if v = A.v0 then f0 i t p else f1 i p v, fun i t p => if_pos rfl, fun i t p v hv => if_neg hv⟩
  obtain ⟨kap, hk⟩ := exists_pin (fun κ => Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp
      (withScal R lam 0).lamN κ ∧ ∃ t p, R.EEp p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (withScal R lam 0).lamN t j p ≠ 0)
    (fun a b ha hb => by
      obtain ⟨t, p, hp, hl⟩ := ha.2
      exact Lift.IsKap.unique ha.1 hb.1 t p hp hl)
  refine ⟨lam, kap, (?_ : (withScal R lam kap).IsScal F)⟩
  refine ⟨fun i t p l hW h => ?_, fun κ h h' => hk κ ⟨h, h'⟩, fun b i p v l hv hp hb h => ?_, fun i t p hW => ?_,
    fun i p v hv h => ?_, fun i t p v hv => ?_⟩
  · exact (h0 i t p).trans (hf0 i t p l hW h)
  · refine (h1 i _ p v hv).trans (hf1 i p v b l ((partAt_withScal R F lam kap b i p v).1 hp) ?_
      ((offEq_withScal R F lam kap b i p v l).1 h))
    rwa [partAt_withScal] at hb
  · exact (h0 i t p).trans (hf0' i t p hW)
  · exact (h1 i _ p v hv).trans (hf1' i p v fun b hb => h b ((partAt_withScal R F lam kap b i p v).2 hb))
  · exact (h1 i t p v hv).trans (h1 i _ p v hv).symm

end GlobalTheory.ScalChoice
