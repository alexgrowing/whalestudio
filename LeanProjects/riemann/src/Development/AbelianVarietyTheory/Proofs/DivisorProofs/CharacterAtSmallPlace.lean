import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelCharExp

open Formalism.BasicNotions.TH Formalism.IndefR.Lev

theorem pow_of_dvd {G : Type} [Monoid G] {x : G} {n M : ℕ} (h : x ^ n = 1) (hd : n ∣ M) : x ^ M = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [pow_mul, h, one_pow]

theorem prod_pow_eq_one {ι G : Type} [CommMonoid G] (s : Finset ι) (f : ι → G) (M : ℕ) (h : ∀ i ∈ s, f i ^ M = 1) :
    (∏ i ∈ s, f i) ^ M = 1 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one h

theorem residue_char_pow {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) {LL : Type} [Monoid LL]
    (χ : (Formalism.L2.DIV.kP PP)ˣ →* LL) (u : (Formalism.L2.DIV.kP PP)ˣ) : χ u ^ Nat.card (Formalism.L2.DIV.kP PP)ˣ = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

theorem card_units_pos {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) : 0 < Nat.card (Formalism.L2.DIV.kP PP)ˣ := by
  have : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  exact Nat.card_pos

open Classical in

def expOf {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : ℕ :=
  ∏ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ

theorem expOf_pos {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : 0 < expOf L :=
  Finset.prod_pos fun PP _ => card_units_pos PP

open Classical in
theorem levFn_flag1_pow {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (x : GL (Fin V.rank) (Lev.EAf D)) :
    Formalism.L2.DIV.levFn β (flag1L L) x ^ expOf L = 1 := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    Formalism.IndefR.Lev.subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1, one_mul, mul_pow]
  have hd : ∀ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ ∣ expOf L := fun PP hP =>
    Finset.dvd_prod_of_mem (fun PP => Nat.card (Formalism.L2.DIV.kP PP)ˣ) hP
  rw [prod_pow_eq_one _ _ _ ?_, prod_pow_eq_one _ _ _ ?_, one_mul]
  · intro PP hP
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_right _ hP))
  · intro PP hP
    refine prod_pow_eq_one _ _ _ fun c _ => ?_
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_left _ hP))

theorem levEnv_chi_pow : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J), (levEnv V β L).χ k ^ expOf L = 1 := by
  intro D V β L k
  exact levFn_flag1_pow V β L _

end GlobalTheory.LevelCharExp

end

namespace GlobalTheory.LevelCharExp

theorem chiAt_inRange : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → ChiAt p j w := by
  unfold InRange AtPts
  refine Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ => EvPt.of_forall fun x hx i p _ _ j P W _ _ w _ _ _ => ?_
  refine ⟨expOf (p.R.datVt j (p.R.mu w)), expOf_pos _, fun κ => ?_⟩
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg Units.val (levEnv_chi_pow _ _ _ κ)

end GlobalTheory.LevelCharExp
