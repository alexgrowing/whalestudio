import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorKernel

open GlobalTheory.CechPic

section Local

variable {Y Y' B : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ Y), (∀ z, π (f z) ∈ V) → pull f c = 0

theorem LocZero.add {π : Y ⟶ B} {c d : Pic Y} (hc : LocZero π c) (hd : LocZero π d) : LocZero π (c + d) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  obtain ⟨V', hV', H'⟩ := hd p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, fun Z f hf => ?_⟩
  rw [map_add, H Z f fun z => (hf z).1, H' Z f fun z => (hf z).2, add_zero]

theorem LocZero.pull {π : Y ⟶ B} {c : Pic Y} (hc : LocZero π c) (k : Y' ⟶ Y) :
    LocZero (k ≫ π) (pull k c) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  exact ⟨V, hV, fun Z f hf => (pull_comp f k c).symm.trans (H Z (f ≫ k) hf)⟩

theorem locZero_base (π : Y ⟶ B) (d : Pic B) : LocZero π (pull π d) := by
  obtain ⟨D, hD, rfl⟩ := cls_surj d
  intro p
  obtain ⟨i, hi⟩ := exists_chart hD p
  refine ⟨D.U i, hi, fun Z f hf => (pull_comp f π _).symm.trans ?_⟩
  exact (cls_eq_zero_iff (pull_isLB hD (f ≫ π))).2
    (BoxKernel.gen_of_chart (pull_isLB hD _) (fun _ => i) fun z => mem_pull.2 (hf z))

theorem locZero_iff (π : Y ⟶ B) {M : LB Y} (hM : M.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (M.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls M hM) := by
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (pull_isLB hM _), cls_pull hM]
  refine ⟨fun H Z f hf => ?_, fun H => H _ _ fun z => z.2⟩
  have hr : Set.range f ⊆ Set.range (π ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hf z
  rw [← IsOpenImmersion.lift_fac (π ⁻¹ᵁ V).ι f hr, pull_comp, H, map_zero]

end Local

section Group

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

theorem translDiff_iff {L : LB A.left} (hL : L.IsLB) (x : T ⟶ A) :
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen) ↔
      LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  rw [locZero_iff _ hD]
  have e : lam (cls L hL) (fst T A ≫ x) (snd T A) = cls _ hD +
      pull (fst T A).left (pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL)) := by
    have e₁ : cls _ hD = pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
      refine (cls_linComb hL _ _ hD).trans ?_
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one, lam]
    abel
  refine ⟨fun H => e ▸ H.add (locZero_base _ _), fun H => ?_⟩
  have := H.add (locZero_base _ (-(pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL))))
  rwa [e, map_neg, add_neg_cancel_right] at this

theorem lam_mul_of_right [IsCommMonObj A] (c : Pic A.left) (u v y : T ⟶ A)
    (H : lam c u (v * y) = lam c u v + lam c u y) : lam c (u * v) y = lam c u y + lam c v y := by
  simp only [lam, _root_.mul_assoc] at H ⊢
  rw [← sub_eq_zero] at H ⊢
  rw [← H]
  abel

end Group

theorem kTriv_of_unimodular : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (O : Type) [CommRing O] (bar : O →+* O) (M : Type) [AddCommGroup M] [Module O M] (h : M → M → O) [Module.Finite O M] [Module.Projective O M] (A : Over S) [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (N : LB A.left), L.IsLB → N.IsLB → (∃ tθ : LB.Gen (Theta A N), tθ.IsGen) → (∀ m n, LBIso (cubeLB A ![fst G G ≫ t.tmul m, snd G G ≫ t.tmul n] N) (cubeLB G ![fst G G ≫ a.act (h m n), snd G G] L)) → ((∀ c, bar (bar c) = c) ∧ (∀ m m' n, h (m + m') n = h m n + h m' n) ∧ (∀ (c : O) m n, h (c • m) n = c * h m n) ∧ ∀ m n, h n m = bar (h m n)) → (∀ l : M →ₗ[O] O, ∃! n, ∀ m, l m = h m n) → Out.KTriv G L → Out.KTriv A N := by
  intro S G _ _ L O _ bar M _ _ h _ _ A _ _ a b t N hL hN hΘ hiso ⟨_, hadd, hsmul, _⟩ huni hK R _ s x hx
  have am := a.hom
  let l : M → (M →ₗ[O] O) := fun n => ⟨⟨fun m => h m n, fun m m' => hadd m m' n⟩, fun c m => hsmul c m n⟩
  let q : M → (A ⟶ G) := fun n => t.mapLeft (IsTensor.self a) (l n)
  have qm : ∀ n, IsMonHom (q n) := fun n => IsTensor.isMonHom_mapLeft _ _ _
  have hq : ∀ m n, t.tmul m ≫ q n = a.act (h m n) := fun m n => by
    simp only [q, IsTensor.tmul_mapLeft, IsTensor.self_tmul]
    rfl
  have basic : ∀ {T : Over S} (g y : T ⟶ G) (m n : M),
      lam (cls N hN) (g ≫ t.tmul m) (y ≫ t.tmul n) = lam (cls L hL) (g ≫ a.act (h m n)) y := by
    intro T g y m n
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (hiso m n)
    have h' := congrArg (pull (lift g y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  have right : ∀ {T : Over S} (u v w : T ⟶ A),
      lam (cls N hN) u (v * w) = lam (cls N hN) u v + lam (cls N hN) u w := fun u v w => by
    rw [lam_comm, lam_mul_left hN hΘ, lam_comm _ v, lam_comm _ w]
  have key : ∀ {T : Over S} (n : M) (u : T ⟶ A) (y : T ⟶ G),
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y := by
    intro T n u
    refine t.induction_on (P := fun u => ∀ y : T ⟶ G,
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y) u (fun y => ?_) (fun m g y => ?_)
      fun u v hu hv y => ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [Category.assoc, hq, basic]
    · rw [lam_mul_left hN hΘ, hu, hv, MonObj.mul_comp, lam_mul_of_right]
      rw [← hu, ← hu, ← hu, MonObj.mul_comp, right]
  have H := (translDiff_iff hN x).1 hx
  have z : ∀ n, x ≫ q n = 1 := fun n => by
    refine hK R s _ ((translDiff_iff hL (x ≫ q n)).2 ?_)
    have H' := H.pull (Over.mk s ◁ t.tmul n).left
    rwa [pull_lam, ← Over.comp_left, whiskerLeft_fst, whiskerLeft_fst_assoc, whiskerLeft_snd, key,
      Category.assoc] at H'
  let P := Summand.choose O M
  let p : Fin P.n → (A ⟶ G) := fun i => t.mapLeft (IsTensor.self a) (LinearMap.proj i ∘ₗ P.incl)
  have pm : ∀ i, IsMonHom (p i) := fun i => IsTensor.isMonHom_mapLeft _ _ _
  have zp : ∀ i, x ≫ p i = 1 := fun i => by
    obtain ⟨n, hn, -⟩ := huni (LinearMap.proj i ∘ₗ P.incl)
    have e : LinearMap.proj i ∘ₗ P.incl = l n := LinearMap.ext hn
    simpa only [p, e] using z n
  have dec : ∀ u : Over.mk s ⟶ A, u = ∏ i, (u ≫ p i) ≫ t.tmul (P.proj (Pi.single i 1)) := by
    intro u
    refine t.induction_on (P := fun u => u = ∏ i, (u ≫ p i) ≫ t.tmul (P.proj (Pi.single i 1))) u ?_
      (fun m g => ?_) fun u v hu hv => ?_
    · simp only [MonObj.one_comp, Finset.prod_const_one]
    · have hx : m = ∑ i, P.incl m i • P.proj (Pi.single i 1) := by
        have e : P.proj (P.incl m) = m := congr($(P.proj_incl) m)
        simp only [← map_smul, ← map_sum]
        rw [← pi_eq_sum_univ', e]
      have hp : ∀ i, t.tmul m ≫ p i = a.act (P.incl m i) := fun i => by simp [p]
      simp only [Category.assoc, reassoc_of% hp, ← t.tmul_smul']
      refine Eq.trans ?_ (map_prod (preHom g) _ _)
      rw [← t.tmul_sum, ← hx]
      rfl
    · simp only [MonObj.mul_comp, Finset.prod_mul_distrib, ← hu, ← hv]
  rw [dec x]
  simp only [zp, MonObj.one_comp, Finset.prod_const_one]
  rfl

end GlobalTheory.HermTensorKernel
