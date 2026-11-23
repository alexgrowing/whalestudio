import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedKillsToSome
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientReductionFirstChernClassTateTwist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIsFirstChernTorsionFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRetype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFirstChernThickeningMuBOfIsFirstChernDeRham
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullSqLePullToSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstChernPullback
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsEqOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedMorCupOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedTrans
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedMCup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullUnitClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem red_nm : ∀ {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u) →
    (∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X₁ q₁ κ₁) c₁) j),
    (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r).pull j ((B.omMor m σ₀ h₀).pull j x) =
      nmHM nm l s r n j ((redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).pull j x) := @GlobalTheory.CompanionTheory.RedNat.red_nm

theorem red_tr : ∀ {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂} (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2) →
    (∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X q κ₁) c₁) j),
    (redMor q s d₂ 𝒱 c₂ lam hc₂ r).pull j ((B.omMor m (RingHom.id Λ) h₀).pull j x) =
      trM (TS γ q l s 𝒱) r (l : A) n j ((redMor q s d₁ 𝒱 c₁ lam hc₁ r).pull j x) := @GlobalTheory.CompanionTheory.RedTrans.red_trans

theorem red_cup : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ),
    (∀ {i j k : ℕ} (h : i + j = k) x y, (redMor q s d 𝒱 c lam hc r).pull k ((CH.mulP (B.OA (nlFun δ l X q κ) c)).cup h x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).cup h ((redMor q s d 𝒱 c lam hc r).pull i x) ((redMor q s d 𝒱 c lam hc r).pull j y)) ∧
    (redMor q s d 𝒱 c lam hc r).pull 0 (CH.oneH (B.OA (nlFun δ l X q κ) c)) =
      redM (TS γ q l s 𝒱) r ((l : A) ^ n) 0 (CH.oneH (sP (TS γ q l s 𝒱)).A) := @GlobalTheory.CompanionTheory.RedCup.redMor_cup_one

theorem redM_cup : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) {i j k : ℕ} (h : i + j = k)
    (x : HO Q i) (y : HO Q j), redM Q r c k ((CH.mulP (sP Q).A).cup h x y) = (sqP (stdI Q r c)).cup h (redM Q r c i x) (redM Q r c j y) := @GlobalTheory.CompanionTheory.RedCup.redM_cup

theorem smor_cup : ∀ {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C}
    {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ), (∀ {i j k : ℕ} (h : i + j = k) x y,
      m.o.pull k ((CH.mulP Φ.A).cup h x y) = (CH.mulP Φ'.A).cup h (m.o.pull i x) (m.o.pull j y)) ∧
    m.o.pull 0 (CH.oneH Φ.A) = CH.oneH Φ'.A := @GlobalTheory.CompanionTheory.SiteCup.smor_cup

theorem red_fil : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r j : ℕ), ∀ x ∈ (B.pdS (nlFun δ l X q κ) c r).img j,
    toSome (TS γ q l s 𝒱) r ((l : A) ^ n) j ((redMor q s d 𝒱 c lam hc none).pull j x) = 0 := @GlobalTheory.CompanionTheory.RedFil.red_kills_toSome

theorem thickening_firstChern_existsUnique : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∃! z, IsFirstChernThickening (TS γ q l s {⊤}) D s z := @GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree.existsUnique_isFirstChernTorsionFree

theorem coefficientReduction_firstChernClass_tateTwist : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))
    (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∀ (x : CH.H (B.OM (nlFun δ l X q κ) c) 2) (z : HO (TS γ q l s {⊤}) 2),
    B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) D c (l * n) x → IsFirstChernThickening (TS γ q l s {⊤}) D s z →
    redM (TS γ q l s {⊤}) none ((l : A) ^ n) 2 z = (redMor q s d {⊤} c lam hc none).pull 2 x := @GlobalTheory.CompanionTheory.ReductionFirstChern.coefficientReduction_firstChernClass_tateTwist

theorem thickening_firstChern_pullback : ∀ {O O' R R' : Type} [CommRing O] [CommRing O'] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O')}
    {κ : O →+* R ⧸ I} {κ' : O' →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q' κ' σ) {p : ℕ}
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q₀ : ObjectProperty (Thick (nlFun γ' p X' q' κ'))) (hQ : Used Q₀)
    (h : ∀ T, St Q₀ {⊤} T → Q ((m.mor p).obj T)) (D : E.LineData X) (N : ℕ) (z : HO Q 2) (z' : HO (St Q₀ {⊤}) 2),
    sSup (𝒱D D) = ⊤ → IsFirstChernThickening Q D N z → IsFirstChernThickening (St Q₀ {⊤}) (D.pb m.u) N z' → (m.smor Q (St Q₀ {⊤}) h).o.pull 2 z = z' := @GlobalTheory.CompanionTheory.FirstChernPullback.firstChern_pullback

theorem deRham_firstChern_to_thickening : ∀ {K B' : Type} [Field K] [CharZero K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ) (D : E.LineData X) (c : HdR q 2), IsFirstChernDeRham q D c →
    IsFirstChernThickening (TS γ q 1 s {⊤}) D s (muB γ q 1 s {⊤} 2 c) := @GlobalTheory.CompanionTheory.FirstChernRationalLift.isFirstChernThickening_muB_of_isFirstChernDeRham

theorem trM_redM : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) (n j : ℕ) (z : HO Q j),
    trM Q r c n j (redM Q r (c ^ (n + 1)) j z) = redM Q r (c ^ n) j z := @GlobalTheory.CompanionTheory.RedTower.trM_redM

theorem nmHM_redM : ∀ {O A A' : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)}
    {σ : A →+* A'} (m : NMor γ q (κA O I) γ' q' (κA O I') σ) (l s : ℕ) (r : Option ℤ) (n j : ℕ) (z : HO (TS γ q l s {⊤}) j),
    nmHM m l s r n j (redM (TS γ q l s {⊤}) r ((l : A) ^ n) j z) = redM (TS γ' q' l s {⊤}) r ((l : A') ^ n) j (nmHO m l s j z) := @GlobalTheory.CompanionTheory.RedPull.nmHM_redM

end CrystallineSemistableComparison.Pb
