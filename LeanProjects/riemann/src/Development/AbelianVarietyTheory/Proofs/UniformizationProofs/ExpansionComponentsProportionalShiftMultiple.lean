import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChainVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusTorsionToAbelianTorsionThetaAction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpacesStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAddFinrankOfKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisTwistField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProportionalField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProportionalRaw
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU.SchurComp

set_option maxHeartbeats 1000000 in

theorem components_proportional : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → ∀ (α mu : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (Kbar V) N α mu) (DegPre.deltaε N))), u.IsGen → U.Supp (Kbar V) N α → ∃ a : Kbar V, ∀ t s, U.ExpF (Kbar V) N t s → ∀ z J, Good D.P.L z J → sval (s (α + N • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) a ⊤) * (sval (s α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val)) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U N hN α mu u hu hS
  have := hV.1
  have := hV.2.2
  have hN0 : N ≠ 0 := by omega
  have hNF : (N : Kbar V) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨Φ, e, hfr, hθ, hmul, hcomm, hnd⟩ :=
    GlobalTheory.ThetaRep.exists_projective_rep hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) N hNF
  obtain ⟨m, hm, hact, -⟩ := GlobalTheory.UU.Eqv.main hL hL2 V hV D A G U N hN
  obtain ⟨hw1, hw2, hw3⟩ := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces hL hL2 V hV D A G U N hN
  have huniq := GlobalTheory.UU.ExpFUniq.main V hV D A G U (Kbar V) N
  choose xp hxp using GlobalTheory.UU.ExpTotal.expF_total hL hL2 V hV D A G U (Kbar V) N hN
  have hcA := (hL.mulN _ A N hN).2.2.2.2 (Kbar V) (jFK (R := V) (Kbar V)) hNF
  have hcH := (GlobalTheory.GtCount.card_gtTors hL hL2 V D (Kbar V) N hNF).1
  have hg : A.g = D.P.g + D.rank := GlobalTheory.UU.PreU.dim_eq V hV D A G U
  have hlinF := ExpLin.expF_linear V hV D A G U (Kbar V) N
  have hbas := exists_basis_twist_field hL hL2 V D (Kbar V) N hN
  clear * - hL hN0 hu hS Φ e hfr hθ hmul hcomm hnd m hm hact hw1 hw2 hw3 huniq xp hxp hcA hcH hg hlinF hbas
  have := A.isAb.comm
  let iso := (Scheme.ΓSpecIso (CommRingCat.of (Kbar V))).commRingCatIsoToRingEquiv
  let S : Subgroup (TFK (R := V) (Kbar V) ⟶ A.A) := (powMonoidHom N).ker
  have hcS : Nat.card S = N ^ (2 * A.g) := hcA
  have : Finite S := Nat.finite_of_card_ne_zero (hcS ▸ pow_ne_zero _ hN0)
  obtain ⟨x, hx⟩ : ∃ x : SecM A.A A.L N (TFK (R := V) (Kbar V)) → Raw D (Kbar V) N,
    ∀ v, U.ExpF (Kbar V) N (SecM.toSec A.A v) (x v) := ⟨_, fun v => hxp _⟩
  have hxe : ∀ t s, U.ExpF (Kbar V) N t s → x (SecM.ofSec A.A t) = s := fun t s h => (huniq _ _ _ _ (hx _) h).1 rfl
  have hsupp : ∀ β, U.Supp (Kbar V) N β ↔ ∃ v j, (x v β).f j ≠ 0 := fun β =>
    ⟨fun ⟨t, s, h, hj⟩ => ⟨SecM.ofSec A.A t, by rwa [hxe t s h]⟩, fun ⟨v, hv⟩ => ⟨_, _, hx v, hv⟩⟩
  refine (proportional_raw (D := D) (k := Γ((TFK (R := V) (Kbar V)).left, ⊤)) (A := S)
    (E := SecM A.A A.L N (TFK (R := V) (Kbar V))) hL.globalFns iso e Φ ?_ ?_ ?_ ?_ hN0 (fun g => ⟨m g, (hact g).1⟩)
    ?_ ?_ (n := N ^ D.P.g) ?_ x ?_ ?_ ?_ ?_ ?_ ?_ ?_ α mu u hu ((hsupp _).1 hS)).elim fun a ha => ?_
  · rw [hcS, mul_comm, pow_mul]; exact congrArg (· ^ 2) hfr
  · exact fun a b => hmul a b (a * b : S) rfl
  · exact fun a b => (hcomm a b).2
  · exact fun a h => Subtype.ext (hnd a h)
  · exact fun g g' h => hm (congrArg Subtype.val h)
  · rw [hcS, hcH, hg, ← pow_add]; exact le_of_eq (congrArg _ (by ring))
  · rw [← pow_add, add_comm, ← hg]; exact hfr.ge
  · intro c v v' β
    obtain ⟨c, rfl⟩ := iso.symm.surjective c
    choose s hs using fun β => exists_comb ((fst (TF (R := V) (Kbar V)) D.P.A).left.appTop.hom (iso.symm c))
      (x v β) (x v' β)
    have := hlinF _ _ (SecM.toSec A.A (iso.symm c • v + v' :)) _ _ s c (hx v) (hx v') (fun _ => rfl) hs
    rw [(huniq _ _ _ _ (hx _) this).1 rfl, iso.apply_symm_apply]
    exact hs β
  · exact fun v v' h => congrArg (SecM.ofSec A.A) ((huniq _ _ _ _ (hx v) (hx v')).2 h)
  · intro χ v
    obtain ⟨t', s', h, H⟩ := hw1 χ _ _ (hx v)
    exact ⟨SecM.ofSec A.A t', by rwa [hxe _ _ h]⟩
  · exact fun χ => (hw2 χ).imp fun ν h => (hsupp _).1 h
  · exact fun χ hχ v h h' => Subtype.ext (funext (hw3 χ ((hsupp _).2 hχ) _ _ (hx v) h h'))
  · exact fun β => (hbas β).imp fun b hb s => (hb s).exists
  · intro g
    obtain ⟨θ, hθ₁, hθ₂⟩ := hθ ⟨m g, (hact g).1⟩
    obtain ⟨w, hw, H⟩ := (hact g).2 θ hθ₁
    exact ⟨w, hw, fun v => H _ _ _ _ (hx _) (hx _) (hθ₂ v)⟩
  · refine ⟨a, fun t s h => ?_⟩
    rw [← hxe t s h]
    exact ha _

end GlobalTheory.UU.SchurComp

end
