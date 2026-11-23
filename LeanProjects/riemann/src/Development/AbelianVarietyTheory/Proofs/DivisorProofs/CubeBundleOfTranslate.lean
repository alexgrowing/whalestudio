import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalizedBoth
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.LamTransl
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem foldr_eq {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (l : List (Fin n)) :
    l.foldr (fun k acc => padd G (x k) acc) (pzero G T) = (l.map x).prod := by
  induction l with
  | nil => simp [pzero, Hom.one_def]
  | cons k l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons, padd, Hom.mul_def]

def split3 (I : Finset (Fin 3)) : Finset (Fin 2) ⊕ Finset (Fin 2) :=
  if (2 : Fin 3) ∈ I then Sum.inl (Finset.univ.filter fun i : Fin 2 => Fin.castSucc i ∈ I)
  else Sum.inr (Finset.univ.filter fun i : Fin 2 => Fin.castSucc i ∈ I)

theorem split3_bij : Function.Bijective split3 := by decide

def splitEquiv : thK ≃ ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.ofBijective _ split3_bij).trans (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))

theorem mem8 : ∀ I : Finset (Fin 3),
    I ∈ ({∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))) := by decide

variable (a : 𝟙_ (Over S) ⟶ G)

def tr : G ⟶ G := (toUnit G ≫ a) * 𝟙 G

def pt3 : G2 G ⟶ G3 G := lift (fst G G) (lift (snd G G) (toUnit (G2 G) ≫ a))
def φA : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down ≫ tr G a).left
def φB : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down).left
def ε2 : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem splitEquiv_apply (I : Finset (Fin 3)) : splitEquiv ⟨I⟩ = Sum.map ULift.up ULift.up (split3 I) := by
  rfl

theorem split_eq (k : thK) : Sum.elim (φA G a) (φB G) (splitEquiv k) = (pt3 G a).left ≫ thφ G (x3 G) k ∧
    Sum.elim ε2 (fun k => -ε2 k) (splitEquiv k) = thε k := by
  rcases k with ⟨I⟩
  rw [splitEquiv_apply]
  have h := mem8 I
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [split3, if_true, if_false, Finset.mem_insert, Finset.mem_singleton,
      Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  all_goals
    refine ⟨?_, trivial⟩
    simp only [φA, φB, thφ]
    rw [← Over.comp_left]
    congr 1
    rw [psum, foldr_eq, psum, foldr_eq]
    simp [List.finRange_succ, x2, x3, pt3, tr, MonObj.comp_mul]
  all_goals ac_rfl

theorem sameSum : LB.SameSum (fun k => (pt3 G a).left ≫ thφ G (x3 G) k) thε (Sum.elim (φA G a) (φB G))
    (Sum.elim ε2 fun k => -ε2 k) := by
  classical
  intro ψ
  rw [← Equiv.sum_comp splitEquiv]
  exact Finset.sum_congr rfl fun k _ => by rw [(split_eq G a k).1, (split_eq G a k).2]

end GlobalTheory.Mum.LamTransl

namespace GlobalTheory.Mum

open LamTransl in

theorem lam_transl_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), CubicalStr G L →
    ∀ (a : 𝟙_ (Over S) ⟶ G) (N : LB G.left), N.IsLB → LBIso N (L.L.pull ((toUnit G ≫ a) * 𝟙 G).left) →
      LBIso (abelian₂ G N) (abelian₂ G L.L) := by
  intro S G _ _ L c a N hN hNL
  have hT : (L.L.pull (tr G a).left).IsLB := pull_isLB L.isLB _
  have hA : (LB.LinComb L.L (φA G a) ε2).IsLB := DVR.linComb_isLB _ L.isLB _ _
  have hLam := GlobalTheory.SabBaseChange.cube_isLB (x2 G) L.isLB
  have h1 : LBIso (abelian₂ G N) (abelian₂ G (L.L.pull (tr G a).left)) := GlobalTheory.SabBaseChange.lbIso_cube (x2 G) hNL
  have h2 : LBIso (abelian₂ G (L.L.pull (tr G a).left)) (LB.LinComb L.L (φA G a) ε2) :=
    LBIso.chartPull (chartPullLinComb L.L (tr G a).left _ (φA G a) ε2 (𝟙 _) fun k => (Category.id_comp _).symm)
      (chartPullSame L.L (φA G a) (φA G a) ε2 (𝟙 _) fun k => (Category.id_comp _).symm)
      (GlobalTheory.PolBaseChange.lbIso_refl hA)
  have h3 : LBIso (abelian₂ G L.L) (LB.LinComb L.L (φA G a) ε2) := by
    refine (GlobalTheory.TripleCompare.lbIso_iff_gen (L := L.L) (φB G) ε2 (φA G a) ε2).2 ?_
    obtain ⟨t', ht', -⟩ := DVR.gen_transport L.isLB (sameSum G a)
      _ (DVR.pullGen_isGen L.L _ _ c.t c.isGen (pt3 G a).left)
    exact ⟨t', ht'⟩
  exact LBIso.trans (GlobalTheory.SabBaseChange.cube_isLB _ hN) (GlobalTheory.SabBaseChange.cube_isLB _ hT) hLam h1
    (LBIso.trans (GlobalTheory.SabBaseChange.cube_isLB _ hT) hA hLam h2 (LBIso.symm h3))

end GlobalTheory.Mum
