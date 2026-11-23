import Development.EtaleCohomology.EtaleSheaves.ArchimedeanCokernel
import Development.EtaleCohomology.EtaleSheaves.ArchimedeanRelations

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
  LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelBase

def Step0 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
    rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
    ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
      LateralTheory.E.FiltGenPf.V ((chains R).map g) (-1) n ((z : Cochain _ _ n) - δ (n - 1) n c)

theorem Filt_of (h0 : Step0) : LateralTheory.E.FiltrationLevelInjectivity.Filt := by
  intro _ R _ F n Z' Z X' X g h a b comm ha hb hlev
  have hk : ∀ p : ℕ, 1 ≤ p → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map g).f (-(p : ℤ)))))
      (res R F) n) := by
    intro p hp
    refine LateralTheory.E.CechFiltPf.Piece_of LateralTheory.E.DiscLvlPf.DiscLvl_of LateralTheory.E.ShiftLvlPf.ShiftLvl_of R F g p n ?_
    obtain ⟨hi, hs⟩ := hlev p hp (n - p) (by omega)
    refine LateralTheory.E.RelativeTruncationSingleDegree.sub_of R F _ _ ⟨fun m hm => ?_, hi⟩ (LateralTheory.E.RelativeTruncationSingleDegree.pull_fgt R F _ _)
    obtain rfl : m = n - p - 1 := by omega
    exact hs
  have hk' : ∀ k : ℤ, k ≤ -1 → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) k).map (((chains R).map g).f k))) (res R F) n) := by
    intro k hk1
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact hk p (by omega)
  have claim : ∀ m : ℕ, ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
      rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
      ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
        LateralTheory.E.FiltGenPf.V ((chains R).map g) (-((m : ℤ) + 1)) n ((z : Cochain _ _ n) - δ (n - 1) n c) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      have e : (-(((0 : ℕ) : ℤ) + 1)) = -1 := by norm_num
      rw [e]
      exact h0 R F n g h a b comm ha hb z hz
    | succ m ih =>
      intro z hz
      obtain ⟨c, hc⟩ := ih z hz
      have hkm := hk' (-((m : ℤ) + 1)) (by omega)
      have hs1 := LateralTheory.E.FiltGenPf.step ((chains R).map g) (-((m : ℤ) + 1)) n hkm
      have hzz : δ n (n + 1) ((z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c) = 0 := by
        rw [δ_sub, δ_δ, sub_zero]; exact Cocycle.δ_eq_zero z (n + 1)
      have hs2 := hs1 _ hzz
      obtain ⟨c', hc'⟩ := hs2 hc
      refine ⟨c + c', ?_⟩
      have e : (-((((m + 1 : ℕ) : ℤ)) + 1)) = -((m : ℤ) + 1) - 1 := by push_cast; ring
      rw [e, δ_add, ← sub_sub]
      exact hc'
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨c, hc1, hc2⟩ := claim (n.toNat + 1) z hx
  change CohomologyClass.mk z = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨c, ?_⟩
  have hz0 : (z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c = 0 := by
    rw [mappingCone.ext_cochain_from_iff _ (n - 1) n (by omega)]
    constructor
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc1 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc2 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
  rw [sub_eq_zero] at hz0
  exact hz0.symm

theorem goal_of (h0 : Step0) : LateralTheory.E.RelDescPf.LevelInj :=
  LateralTheory.E.FiltrationLevelInjectivity.LevelInj_of (Filt_of h0) LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of

end LateralTheory.E.FiltrationLevelBase
