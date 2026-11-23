import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanSelfIntersectionNonnegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightNonnegVerticalOfNefOnFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.KleimanNef

theorem htNef_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D := by
  intro hA hAmp hSP
  suffices H : ∀ D : ℕ, ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
      IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D by
    intro k _ X _ p D hX C hC
    exact H D k X p hX C hC
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro k _ X _ p hX C hC
  have hng : ∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h →
      ∀ z, z ≠ genericPoint X → 0 ≤ h z := by
    intro C h hC hh z hz
    by_cases hcz : CharZero (X.residueField z)
    swap
    · exact GlobalTheory.T.arithHeight_nonneg_vertical_of_nefOnFibres k X p D hX C h (nefFib_of_isNef hC) hh z hcz
    obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    rcases hX.vertical_or_horizontal i with ⟨ℓ, hℓ, ⟨alg⟩⟩ | ⟨hc, e, he⟩
    · exfalso
      have hcz' : CharZero (Z.residueField (genericPoint Z)) :=
        (RingHom.charZero_iff (i.residueFieldMap (genericPoint Z)).hom.injective).1 hcz
      let f : ZMod ℓ →+* Z.residueField (genericPoint Z) :=
        (Z.evaluation ⊤ (genericPoint Z) trivial).hom.comp (algebraMap (ZMod ℓ) Γ(Z, ⊤))
      have h2 := congrArg f (ZMod.natCast_self ℓ)
      rw [map_natCast, map_zero] at h2
      exact hℓ.out.ne_zero (by exact_mod_cast h2)
    · have hZ : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc he
      have hamb := GlobalTheory.MixHt.isAmb_of_isArithVar hX
      obtain ⟨-, -, -, -, hcl, hgd⟩ := GlobalTheory.MixHt.hasDim_basic k X p hamb
      have hd : GlobalTheory.MixHt.HasDim (i (genericPoint Z)) (e + 1) := (hcl Z i _ _).2 ((hgd Z _).2 he)
      have hco := GlobalTheory.DimCoheight.coheight_add_eq k X p hamb (D + 1) hX.dim_eq _ _ hd
      have hne : Order.coheight (i (genericPoint Z)) ≠ 0 := by
        intro h0
        rw [Order.coheight_eq_zero] at h0
        apply hz
        have h1 : i (genericPoint Z) ≤ genericPoint X := genericPoint_specializes _
        exact (Specializes.antisymm (h0 h1) (genericPoint_specializes _)).eq
      have heD : e < D := by
        by_contra hle
        push_neg at hle
        obtain ⟨c, hc'⟩ : ∃ c : ℕ, Order.coheight (i (genericPoint Z)) = c := by
          refine ⟨(Order.coheight (i (genericPoint Z))).toNat, (ENat.coe_toNat fun ht => ?_).symm⟩
          rw [ht, top_add] at hco
          exact ENat.top_ne_coe _ hco
        rw [hc'] at hco hne
        have : c + (e + 1) = D + 1 := by exact_mod_cast hco
        have : c ≠ 0 := by exact_mod_cast hne
        omega
      have hnef : (C.pull i rfl).IsNef e := GlobalTheory.T.hermitianLineBundle_isNef_pullback hA hSP k X Z p (i ≫ p) D e hX hZ i rfl C hC
      exact (ih e heD k Z (i ≫ p) hZ _ hnef).2 _ (hh.restrict hX i rfl) (genericPoint Z)
  refine ⟨hC.semiPos, fun h hh x => ?_⟩
  by_cases hx : x = genericPoint X
  · subst hx
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have := ((hh.isNef_iff hX).1 hC).2 X (𝟙 X) (by simpa using hX.dim_eq)
      simpa using this
    · exact GlobalTheory.T.arithKleiman_selfIntersection_nonneg hA hAmp k X p D hX hD hng C _ hC ⟨h, hh, rfl⟩
  · exact hng C h hC hh x hx

end GlobalTheory.KleimanNef
