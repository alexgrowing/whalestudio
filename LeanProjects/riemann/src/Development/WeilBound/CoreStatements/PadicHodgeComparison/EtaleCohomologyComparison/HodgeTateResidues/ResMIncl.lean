import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.HT

open Pb

section Gen
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

def resM (r r' : ℤ) : CH.Mor (sq (thFil L r) (thFil L r')) (sq (sFil Q r) (sFil Q r')) (RingHom.id b.R) where
  G := Q.ι
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem resM_all (h : ∀ T, Q T) (r r' : ℤ) (n : ℕ) : Function.Bijective ((resM Q r r').pull n) := by
  have e1 : Q.ι.EssSurj := ⟨fun T => ⟨⟨T, h T⟩, ⟨Iso.refl _⟩⟩⟩
  have e2 : Q.ι.IsEquivalence := {}
  have : (resM Q r r').G.IsLeftAdjoint := inferInstanceAs Q.ι.IsLeftAdjoint
  exact CrystallineSemistableComparison.P.adj_mor _ (fun _ => Function.bijective_id) n

variable {Q} in
theorem resM_incl {Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) (n : ℕ) (x : CH.H (sq (thFil L r) (thFil L r')) n) :
    (resM Q' r r').pull n x = ((incl h).sq (incl_fil h r) (incl_fil h r')).pull n ((resM Q r r').pull n x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => ?_))
  change (z.1 (s ⋙ Q'.ι) : sqM _ _ _) = ((incl h).sq (incl_fil h r) (incl_fil h r')).τ _ (z.1 (s ⋙ Q'.ι))
  obtain ⟨y, hy, e⟩ := sq_surj _ _ (z.1 (s ⋙ Q'.ι))
  rw [← e]
  rfl

end Gen

section K
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def resH (Q : ObjectProperty (Thick (smFun X q))) (a n : ℕ) : Hdg q a n →ₗ[K] HQ Q (a : ℤ) ((a : ℤ) + 1) n :=
  (resM Q (a : ℤ) ((a : ℤ) + 1)).pull n

theorem res_bij (s : ℕ) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ) (hr : r' ≤ s) (n : ℕ) :
    Function.Bijective ((resM (TO q 1 s 𝒱) r r').pull n) := by
  let Q₀ : ObjectProperty (Thick (smFun X q)) :=
    St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ {⊤}
  have h0 : ∀ T, Q₀ T := fun T => ⟨trivial, ⊤, rfl, le_rfl⟩
  have h1 : TO q 1 s {⊤} ≤ Q₀ := fun T _ => h0 T
  have h2 : TO q 1 s 𝒱 ≤ TO q 1 s {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, le_rfl⟩
  have b0 := resM_all Q₀ h0 r r' n
  have b1 := refl (γ := dividedPowersBot K) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ 1 s (Or.inl ⟨rfl, rfl⟩) {⊤} h1 r r' hr n
  have b2 := (zar (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) 𝒱 {⊤} h2
    (fun W _ => by rw [h𝒱]; exact le_top) n).1 r r'
  have e : ⇑((resM (TO q 1 s 𝒱) r r').pull n) = ((incl h2).sq (incl_fil h2 r) (incl_fil h2 r')).pull n ∘
      ((incl h1).sq (incl_fil h1 r) (incl_fil h1 r')).pull n ∘ (resM Q₀ r r').pull n := funext fun x =>
    (resM_incl h2 r r' n x).trans (congrArg _ (resM_incl h1 r r' n x))
  rw [e]
  exact b2.comp (b1.comp b0)

theorem hdg_res (s : ℕ) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (a : ℕ) (ha : a < s) (n : ℕ) :
    Function.Bijective (resH q (TO q 1 s 𝒱) a n) := res_bij q s 𝒱 h𝒱 _ _ (by omega) n

end K

end CrystallineSemistableComparison.HT
