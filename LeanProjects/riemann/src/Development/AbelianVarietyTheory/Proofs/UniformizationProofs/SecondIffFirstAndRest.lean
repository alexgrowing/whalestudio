import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.ConstantUnitPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.PairingCompare

open GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing GlobalTheory.TorsionExt GlobalTheory.FieldBaseChange

def First : Prop :=
  LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ)

section Clause

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

def ClauseFirst (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x →
    QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ)

def ClauseSecond (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) (x x' : TFK (R := R) F ⟶ A.A),
    QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' →
    ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' (ζ : F) ↔ WeilIs A.A A.L (k : ℤ) x x' (constUnit R F ζ)

theorem weilQkIs_iff_operators (hG : GlobalFnsSt) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
    {p p' : QkPt D.toPre F k} {w : Frm D.toPre F k p.g.b} {w' : Frm D.toPre F k p'.g.b}
    (hw : w.IsGen) (hw' : w'.IsGen) {Φ Φ' : Fam D.toPre F k →ₗ[F] Fam D.toPre F k}
    (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) (hΦ' : ∀ s t, PhiRel D.toPre F k p' w' s t ↔ t = Φ' s)
    (ζ : F) : WeilQkIs D.toPre F k p p' ζ ↔ ∀ s, Φ (Φ' s) = ζ • Φ' (Φ s) := by
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ s) := fun s => (hΦ _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ' s) := fun s => (hΦ' _ _).2 rfl
  constructor
  · intro h s
    exact (isSmul_iff _ _ _).1 (h w w' hw hw' s _ _ _ _ (r' s) (r _) (r s) (r' _))
  · intro H v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
    obtain ⟨c, -, hc⟩ := TorsionImage.exists_smul_of_phiVal p w v hw hv
    obtain ⟨c', -, hc'⟩ := TorsionImage.exists_smul_of_phiVal p' w' v' hw' hv'
    have q : ∀ s t, PhiRel D.toPre F k p v s t → t = c • Φ s := fun s t h =>
      hc s _ t ((phiRel_iff hG p w hw _ _).1 (r s)) ((phiRel_iff hG p v hv _ _).1 h)
    have q' : ∀ s t, PhiRel D.toPre F k p' v' s t → t = c' • Φ' s := fun s t h =>
      hc' s _ t ((phiRel_iff hG p' w' hw' _ _).1 (r' s)) ((phiRel_iff hG p' v' hv' _ _).1 h)
    rw [isSmul_iff, q _ _ h₂, q' _ _ h₁, q' _ _ h₄, q _ _ h₃, map_smul, map_smul, H s,
      smul_comm c' ζ, smul_comm c ζ, smul_comm c c']

theorem injective_of_isExtension {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) : Function.Injective a := by
  obtain ⟨ℓ, hℓ⟩ := (Algebra.linearMap K F).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K F).injective)
  have h1 : ℓ 1 = 1 := by simpa using LinearMap.congr_fun hℓ 1
  obtain ⟨Λ, hΛ⟩ := h.coord ℓ
  have h2 : ∀ v, Λ (a v) = v := fun v => by
    have := hΛ 1 v
    rwa [one_smul, h1, one_smul] at this
  exact Function.LeftInverse.injective h2

variable {E F : Type} [Field F] [Algebra (FractionRing R) F] [Field E] [Algebra (FractionRing R) E] [Algebra E F]
  [IsScalarTower (FractionRing R) E F]

theorem weilQkIs_iff_of_algebra (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) {p p' : QkPt D.toPre E k}
    {q q' : QkPt D.toPre F k} (h : QkExt (algebraMap E F) p q) (h' : QkExt (algebraMap E F) p' q') (ζ : E) :
    WeilQkIs D.toPre E k p p' ζ ↔ WeilQkIs D.toPre F k q q' (algebraMap E F ζ) := by
  obtain ⟨w, hw⟩ : ∃ w : Frm D.toPre E k p.g.b, w.IsGen := exists_gen_of_local D.toPre.P.L D.toPre.P.isLB _ _
  obtain ⟨w', hw'⟩ : ∃ w : Frm D.toPre E k p'.g.b, w.IsGen := exists_gen_of_local D.toPre.P.L D.toPre.P.isLB _ _
  obtain ⟨v, hv, hwv⟩ := exists_phiVal_pull hG h hw
  obtain ⟨v', hv', hwv'⟩ := exists_phiVal_pull hG h' hw'
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R I D E k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG R I D E k hk p' w' hw'
  obtain ⟨Ψ, hΨ⟩ := phiFun_of_globalFns hG R I D F k hk q v hv
  obtain ⟨Ψ', hΨ'⟩ := phiFun_of_globalFns hG R I D F k hk q' v' hv'
  have c : ∀ s, Ψ (famPull D.toPre E F hG k s) = famPull D.toPre E F hG k (Φ s) := fun s =>
    phi_unique q v ((phiRel_iff hG q v hv _ _).1 ((hΨ _ _).2 rfl))
      (hwv _ _ ((phiRel_iff hG p w hw s _).1 ((hΦ s _).2 rfl)))
  have c' : ∀ s, Ψ' (famPull D.toPre E F hG k s) = famPull D.toPre E F hG k (Φ' s) := fun s =>
    phi_unique q' v' ((phiRel_iff hG q' v' hv' _ _).1 ((hΨ' _ _).2 rfl))
      (hwv' _ _ ((phiRel_iff hG p' w' hw' s _).1 ((hΦ' s _).2 rfl)))
  have hx := isExtension_famPull D.toPre E F hG hk
  rw [weilQkIs_iff_operators hG hw hw' hΦ hΦ', weilQkIs_iff_operators hG hv hv' hΨ hΨ']
  constructor
  · intro H s
    have e : Ψ ∘ₗ Ψ' = algebraMap E F ζ • (Ψ' ∘ₗ Ψ) := LinearMap.ext_on hx.span (by
      rintro _ ⟨t, rfl⟩
      rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, c', c, c, c', H, map_smulₛₗ])
    exact LinearMap.congr_fun e s
  · intro H s
    refine injective_of_isExtension hx ?_
    rw [map_smulₛₗ, ← c, ← c', ← c', ← c, H]

end Clause

def SecondOn (P : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G], Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I →
    ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
      (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], P R G → ∀ (U : Unif I D A G)
      (F : Type) [Field F] [Algebra (FractionRing R) F], ClauseSecond U F

end GlobalTheory.PairingCompare
