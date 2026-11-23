import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevelMapField

private theorem KA_mono_of_A_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.A ∣ l.A) : KA l₀ ≤ KA l := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | rfl
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [GlobalTheory.LevelCover.zeta_dvd l.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _

private theorem M'_dvd_of_level_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.Dvd l) : l₀.M' ∣ l.M' := by
  unfold Level.Dvd at h
  unfold Level.M'
  exact Nat.lcm_dvd (h.1.trans (Nat.dvd_lcm_left _ _)) (h.2.2.trans (Nat.dvd_lcm_right _ _))

private theorem M'_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Level H) : 0 < l.M' := by
  unfold Level.M'
  have h3 := l.three_le
  exact Nat.lcm_pos (by omega) l.A_pos

theorem exists_levelMap : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (c : Coeff l) (o : Obj D l (baseKA l) (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)) (_ : ObjMap o (Xo l).univ (pullback.fst _ _)), l₀.Dvd l → ∃ (k : KA l₀ →+* c.F) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap o.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k), IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k ∧ LevComp o (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) := by
  intro _ _ _ E _ _ _ H D Xo hN l₀ l c o mo hd
  have hA : l₀.A ∣ l.A := by
    unfold Level.Dvd at hd
    exact hd.2.2
  have hle : KA l₀ ≤ c.F := (KA_mono_of_A_dvd hA).trans c.le
  have hz : zeta l₀.M' ∈ c.F := by
    rw [GlobalTheory.LevelCover.zeta_dvd (M'_pos' l) (M'_dvd_of_level_dvd hd)]
    exact pow_mem c.zeta_mem _
  obtain ⟨r₀, -, m, -, -, hm1, hm2, -, hF⟩ := hN l₀ l (Xo l₀) (Xo l) hd
  obtain ⟨rF, h1, h2, hfin, het, hsurj, -⟩ := hF ⟨c.F, c.fin, c.conj, hz, hle⟩ c rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c.F)).toRingHom = 𝟙 (Sp c.F) :=
    GlobalTheory.LevelCover.spMap_inclusion_self _
  have hr : (rF ≫ pullback.fst _ _) ≫ (Xo l₀).s =
      pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h2]
    erw [hid, Category.comp_id]
  have hlift : pullback.lift (rF ≫ pullback.fst _ _) (pullback.snd _ _) hr = rF := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd, h2]
      erw [hid, Category.comp_id]
  obtain ⟨ν, hν⟩ := GlobalTheory.LevelCover.sab_comp mo.toSABMap m (e := rF ≫ pullback.fst _ _) h1.symm
  refine ⟨(IntermediateField.inclusion hle).toRingHom, rF ≫ pullback.fst _ _, ν, hr,
    fun x => rfl, ?_, ?_, ?_, ?_⟩
  · unfold LevComp
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.eta a) ((Xo l).univ.eta a) (mo.eta a),
        Category.assoc, hm1 a, ← Category.assoc, ← h1]
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.etaA a) ((Xo l).univ.etaA a) (mo.etaA a),
        Category.assoc, hm2 a, ← Category.assoc, ← h1]
  · rw [hlift]; exact hfin
  · rw [hlift]; exact het
  · rw [hlift]; exact hsurj

end GlobalTheory.LevelMapField
