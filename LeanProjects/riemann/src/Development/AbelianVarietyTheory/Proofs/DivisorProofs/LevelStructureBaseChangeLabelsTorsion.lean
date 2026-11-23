import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelCarry

theorem linComb_prod' {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : linComb y a = ∏ i, y i ^ a i := List.prod_ofFn

theorem unitOn_zpow' {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow _ _ _

theorem unitOn_inj' {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  simp only [unitOn, Units.coe_map] at h'
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective h'

end GlobalTheory.LevelCarry

open GlobalTheory.LevelCarry in

theorem GlobalTheory.levelPoint_baseChange_label : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := by
  intro K C _ _ _ f P P' io hW g k hg ζ lev hk
  subst hg
  have := P'.isAb.comm
  have hk0 : NeZero k := ⟨by omega⟩
  have E : ∀ c : Fin (2 * P'.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  have LP : ∀ a, levelPoint lev rfl a = ∏ i, lev.pt i ^ (a i).val := fun a => by
    rw [levelPoint_rfl]; exact linComb_prod' _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective
      (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.toMonoidHom) lev.prim unitOn_inj'
  · intro a b
    rw [← map_mul]
    congr 1
    rw [LP, LP, LP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, pow_eq_pow_mod ((a i).val + (b i).val) (lev.torsion i), Pi.add_apply, ZMod.val_add]
  · have inj : Function.Injective (levelPoint lev rfl) := by
      intro a b h
      have h₀ := lev.indep C (𝟙 _) (fun i => ⟨(a i).val, ZMod.val_lt _⟩) (fun i => ⟨(b i).val, ZMod.val_lt _⟩)
        ((E _).trans (h.trans (E _).symm))
      exact funext fun i => ZMod.val_injective k (congrArg Fin.val (congrFun h₀ i))
    exact io.symm.injective.comp inj
  · intro z hz
    have hz' : (io z) ^ k = 1 := by rw [← map_pow, hz, map_one]
    obtain ⟨c, hc⟩ := lev.span C (𝟙 _) (io z) hz'
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_⟩
    rw [MulEquiv.symm_apply_eq, levelPoint_rfl, Level.toPt]
    exact (congrArg (linComb lev.pt) (funext fun i => ZMod.val_natCast_of_lt (c i).isLt)).trans
      ((E _).symm.trans hc)
  · intro i j
    haveI : Fact (1 < k) := ⟨by omega⟩
    have hs : ∀ i, levelPoint lev rfl (Pi.single i 1) = lev.pt i := fun i => by
      rw [LP, Finset.prod_eq_single i]
      · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs, hs]
    apply hW
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, unitOn_zpow']
    exact lev.pairing i j
