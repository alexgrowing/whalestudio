import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartFrames

theorem smor_Fr_frame : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) {V V' : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d) (c' : Chart γ' p q κ' V' d) (hc : c.Good) (hc' : c'.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T)) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D)
    (hQ' : ∀ T, Q' T → InU V' T) (hD' : Q' c'.D) (e : c.D ⟶ (m.mor p).functor.obj c'.D),
    (∀ i, e.φ (c.t i) = c'.t i) →
      (m.smor Q Q' h).Fr (c.frame hc Q hQ hD) (c'.frame hc' Q' hQ' hD') (ObjectProperty.homMk e) := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m V V' d c c' hc hc' Q Q' h hQ hD hQ' hD' e he i T s s'
  change (s'.hom.φ (e.φ (c.t i)) - s.hom.φ (e.φ (c.t i)) : T.obj.B) = s'.hom.φ (c'.t i) - s.hom.φ (c'.t i)
  rw [he]

end GlobalTheory.CompanionTheory.ChartFrames
