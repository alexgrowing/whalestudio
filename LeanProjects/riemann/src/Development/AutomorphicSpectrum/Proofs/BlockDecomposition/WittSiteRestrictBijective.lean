import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijective

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatZar

section Main
variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}

def resG (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ)
    (P Q : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (h : Q ≤ P) :
    CH.Mor (P.ι ⋙ Wc.OM l (B.schFn q) ρ m) (Q.ι ⋙ Wc.OM l (B.schFn q) ρ m) (RingHom.id (WittVector l k)) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

set_option maxHeartbeats 1600000 in
theorem resG_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤)
    (P : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (hP : P = stF q ρ m {⊤}) (h : stF q ρ m 𝒱 ≤ P) (j : ℕ) :
    Function.Bijective ((resG q ρ m P (stF q ρ m 𝒱) h).pull j) := by
  subst hP
  have z := (zar (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT
    (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inr rfl⟩) 𝒱 {⊤} h
    (fun W _ => by rw [hU]; exact le_top) j).2.2
  have c1 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m {⊤}) j
  have c2 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m 𝒱) j
  refine (Function.Bijective.of_comp_iff' c2 _).1 ?_
  have e : ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m 𝒱)).pull j) ∘ ⇑((resG q ρ m _ (stF q ρ m 𝒱) h).pull j) =
      ⇑((incl h).o.pull j) ∘ ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m {⊤})).pull j) := by
    funext x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  rw [e]
  exact z.comp c1

theorem resV_bij : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resV q ρ m 𝒱).pull j) := by
  intro l _ k _ _ _ O _ X q ρ m 𝒱 hU j
  exact resG_bij q ρ m 𝒱 hU (fl l (B.schFn q) ρ m)
    (GlobalTheory.CompanionTheory.FlatRes.st_top_eq (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT).symm
    (fun _ h => h.1) j

end Main

end GlobalTheory.CompanionTheory.FlatZar

end
