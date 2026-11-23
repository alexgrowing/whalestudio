import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.QuoK

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem toSq_bijective_of_bot (a₀ b : IdF A) (h0 : ∀ T, a₀.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (j : ℕ) :
    Function.Bijective ((toSq a₀ b h0).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij (toSq a₀ b h0).hom (fun n => ⟨fun f f' h => ?_, fun y => ?_⟩) j
  · funext s
    have h1 := congrArg Subtype.val (congrFun h s)
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hb] at h2
    exact sub_eq_zero.1 h2
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a₀ b _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

end Abstract

section Concrete
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem ks_le_of_le {u s : ℕ} (hus : u ≤ s) (𝒱 : Set X.Opens) : KS q u 𝒱 ≤ KS q s 𝒱 := by
  rintro T ⟨⟨h1, h2⟩, hV⟩
  exact ⟨⟨le_bot_iff.1 (h1 ▸ T.pdPow_anti hus), h2⟩, hV⟩

theorem quoK_comm {u s : ℕ} (hus : u ≤ s) (𝒱 : Set X.Opens) (r : ℤ) (j : ℕ) (x : HdR q j) :
    ((incl (ks_le_of_le q hus 𝒱)).sq (incl_fil _ 0) (incl_fil _ r)).pull j (quoK q (KS q s 𝒱) r j x) =
      quoK q (KS q u 𝒱) r j x := by
  obtain ⟨z, hz, hx⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx (CH.modF (thA (smFun X q)))) j).1 x
  subst hx
  rfl

theorem quoK_bij_self {u : ℕ} (𝒱 : Set X.Opens) (j : ℕ) (h : Function.Bijective (resK q (KS q u 𝒱) j)) :
    Function.Bijective (quoK q (KS q u 𝒱) (u : ℤ) j) := by
  have hB := toSq_bijective_of_bot (sFil (KS q u 𝒱) 0) (sFil (KS q u 𝒱) (u : ℤ)) (fun T => T.obj.pdPow_zero)
    (fun T => by
      have h := T.property.1.1
      change T.obj.pdPow ((u : ℤ).toNat) = ⊥
      rw [Int.toNat_natCast]
      exact h) j
  exact hB.comp h

end Concrete

theorem quoK_bijective : KH.KIso → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (U : Cov q) (s u : ℕ), (∀ α, U.d α < u) → u ≤ s → ∀ (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ (j : ℕ),
    Function.Bijective (quoK q (KS q s 𝒱) (u : ℤ) j) := by
  intro hK K _ _ X q U s u hd hus 𝒱 h𝒱 j
  have h1 := quoK_bij_self q 𝒱 j (hK q U u hd 𝒱 h𝒱 j).1
  have h2 := GlobalTheory.T.filtered_cohomology_restriction_bijective (TF 1 s) 1 u (Or.inr ⟨s, hus, rfl⟩) 𝒱 (ks_le_of_le q hus 𝒱) 0 (u : ℤ) le_rfl j
  refine (Function.Bijective.of_comp_iff' h2 _).1 ?_
  have e : (((incl (ks_le_of_le q hus 𝒱)).sq (incl_fil _ 0) (incl_fil _ (u : ℤ))).pull j) ∘ (quoK q (KS q s 𝒱) (u : ℤ) j) =
      quoK q (KS q u 𝒱) (u : ℤ) j := funext (quoK_comm q hus 𝒱 (u : ℤ) j)
  exact (congrArg Function.Bijective e).mpr h1

end GlobalTheory.CompanionTheory.QuoK
