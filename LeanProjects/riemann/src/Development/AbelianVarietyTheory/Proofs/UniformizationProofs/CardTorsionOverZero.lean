import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GtCount

open GlobalTheory.TorusExt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.GtCount.card_torsion_eq_mul {G B : Type} [AddCommGroup G] [AddCommGroup B] (p : G →+ B) (n : ℕ)
    (h : ∀ b : B, n • b = 0 → ∃ g, p g = b ∧ n • g = 0) :
    Nat.card {g : G // n • g = 0} = Nat.card {b : B // n • b = 0} * Nat.card {g : G // n • g = 0 ∧ p g = 0} := by
  have h' : ∀ b : {b : B // n • b = 0}, ∃ g, p g = b ∧ n • g = 0 := fun b => h b b.2
  choose s hs using h'
  have hp : ∀ g : {g : G // n • g = 0}, n • p g = 0 := fun g => by
    rw [← map_nsmul, g.2, map_zero]
  have hsec : ∀ (b b' : {b : B // n • b = 0}), (b : B) = b' → s b = s b' := by
    rintro b b' hbb
    rw [Subtype.ext hbb]
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun g => (⟨p g, hp g⟩, ⟨g - s ⟨p g, hp g⟩, ?_, ?_⟩)
      invFun := fun x => ⟨s x.1 + x.2.1, by rw [nsmul_add, (hs _).2, x.2.2.1, add_zero]⟩
      left_inv := fun g => Subtype.ext (add_sub_cancel _ _)
      right_inv := fun x => ?_ }
  · rw [nsmul_sub, g.2, (hs _).2, sub_zero]
  · rw [map_sub, (hs _).1, sub_self]
  · have hx : p (s x.1 + x.2.1) = x.1 := by rw [map_add, (hs _).1, x.2.2.2, add_zero]
    refine Prod.ext (Subtype.ext hx) (Subtype.ext ?_)
    change s x.1 + x.2.1 - s ⟨p (s x.1 + x.2.1), _⟩ = x.2.1
    rw [hsec ⟨p (s x.1 + x.2.1), _⟩ x.1 hx, add_sub_cancel_left]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.GtCount.card_torus_torsion (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F]
    [IsAlgClosed F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {t : Multiplicative X →* Fˣ // t ^ n = 1} = n ^ Module.finrank ℤ X := by
  haveI : NeZero (n : F) := ⟨hn⟩
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have hroots : Nat.card (rootsOfUnity n F) = n := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
    exact hζ.card_rootsOfUnity
  let b := Module.Free.chooseBasis ℤ X
  let e₁ : {t : Multiplicative X →* Fˣ // t ^ n = 1} ≃ (Multiplicative X →* rootsOfUnity n F) :=
    { toFun := fun t => (t.1).codRestrict (rootsOfUnity n F) fun x => by
        have := DFunLike.congr_fun t.2 x
        simpa [MonoidHom.pow_apply, mem_rootsOfUnity] using this
      invFun := fun s => ⟨(rootsOfUnity n F).subtype.comp s, by
        refine MonoidHom.ext fun x => ?_
        simpa [MonoidHom.pow_apply] using (mem_rootsOfUnity _ _).1 (s x).2⟩
      left_inv := fun t => Subtype.ext (MonoidHom.ext fun x => rfl)
      right_inv := fun s => MonoidHom.ext fun x => Subtype.ext rfl }
  let e := e₁.trans (MonoidHom.toAdditiveRight.trans
    ((addMonoidHomLequivInt ℤ).toEquiv.trans (b.constr ℤ).symm.toEquiv))
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_congr Additive.toMul, hroots,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

attribute [local instance] gtGroup

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.gtTors_iff {R : Type} [CommRing R] [IsDomain R] {D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (n : ℕ) (g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) : _root_.GlobalTheory.UU.GtTors D n g ↔ n • g = 0 := by
  unfold _root_.GlobalTheory.UU.GtTors
  simp [_root_.GlobalTheory.TorusExt.isNsmul_iff_eq, _root_.GlobalTheory.TorusExt.isZero_iff_eq]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in

theorem _root_.GlobalTheory.GtCount.card_torsion_over_zero {R : Type} [CommRing R] [IsDomain R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} = n ^ D.rank := by
  let φ := _root_.GlobalTheory.TorusExt.torusPt D F
  have hinj : Function.Injective φ := _root_.GlobalTheory.TorusExt.torusPt_injective
  let e : {t : Multiplicative D.X →* Fˣ // t ^ n = 1} → {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} :=
    fun t => ⟨φ (Additive.ofMul t.1), by
      rw [← map_nsmul, ← ofMul_pow, t.2, ofMul_one, map_zero], _root_.GlobalTheory.TorusExt.torusPt_b _⟩
  have he : Function.Bijective e := by
    refine ⟨fun t t' htt => Subtype.ext ?_, fun g => ?_⟩
    · exact Additive.ofMul.injective (hinj (congrArg Subtype.val htt))
    · obtain ⟨t, ht⟩ := _root_.GlobalTheory.TorusExt.exists_torusPt_eq g.2.2
      refine ⟨⟨t, ?_⟩, Subtype.ext ht.symm⟩
      apply Additive.ofMul.injective
      apply hinj
      rw [ofMul_pow, map_nsmul, ← ht, g.2.1, ofMul_one, map_zero]
  rw [← Nat.card_congr (Equiv.ofBijective e he), _root_.GlobalTheory.GtCount.card_torus_torsion D.X F n hn]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in

theorem _root_.GlobalTheory.GtCount.card_gtTors : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws → _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), (N : F) ≠ 0 → Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g} = N ^ (2 * D.P.g + D.rank) ∧ Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g ∧ g.b = _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F} = N ^ D.rank) := by
  intro hL _ R _ _ _ D F _ _ _ N hN
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hz : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F = 1 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF; rfl
  have h0 : (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F).b = 1 := by
    simpa using _root_.GlobalTheory.TorusExt.nsmul_b 0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F)
  let p : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F →+ Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) :=
    { toFun := fun g => Additive.ofMul g.b
      map_zero' := by rw [h0]; rfl
      map_add' := fun g g' => by rw [_root_.GlobalTheory.TorusExt.add_b]; rfl }
  have hsurj : ∀ b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A), N • b = 0 → ∃ g, p g = b ∧ N • g = 0 := by
    intro b hb
    obtain ⟨g, hgb, hg⟩ := _root_.GlobalTheory.TorusExt.exists_nsmul_eq_of_pow_eq hN0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) (b := Additive.toMul b)
      (by rw [h0]; exact hb)
    exact ⟨g, by simp [p, hgb], hg⟩
  have hB : Nat.card {b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) // N • b = 0} = N ^ (2 * D.P.g) := by
    have := (hL.mulN (Spec (CommRingCat.of R)) D.P N (Nat.one_le_iff_ne_zero.2 hN0)).2.2.2.2 F
      (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F).hom hN
    rw [← this]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun b => Iff.rfl)
  simp only [_root_.GlobalTheory.GtCount.gtTors_iff, hz]
  refine ⟨?_, _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN⟩
  rw [_root_.GlobalTheory.GtCount.card_torsion_eq_mul p N hsurj, hB, pow_add]
  congr 1
  rw [← _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [p])

end GlobalTheory.GtCount
