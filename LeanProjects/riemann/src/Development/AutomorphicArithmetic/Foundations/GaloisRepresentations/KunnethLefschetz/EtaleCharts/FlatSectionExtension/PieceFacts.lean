import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartNat

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem e1 {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (j : T ⟶ Y) (p : B.ι × Fin d) :
    tI B j p ≫ eP B j = (oT B j p).ι := by
  unfold tI eP
  rw [Sigma.ι_desc]

private theorem e2 {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (j : T ⟶ Y) (p : B.ι × Fin d) :
    tI B j p ≫ tauP B j = secOf B p.1 p.2 ((oT B j p).ι ≫ j) (oT_le B j p) := by
  unfold tI tauP
  rw [Sigma.ι_desc]

private theorem e3 {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i) (p : B.ι × Fin d) :
    tI B j p ≫ rhoP B j r hw = rhoC B j r hw p ≫ wI B p.1 := by
  unfold tI rhoP
  rw [Sigma.ι_desc]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.pieceFacts :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ (p : B.ι × Fin d) {V : Scheme.{0}} (a₁ : V ⟶ (oT B j p : Scheme.{0})), ∃ h : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p.1).C p.2, (a₁ ≫ tI B j p).appTop.hom ∘ v = uV B p.1 p.2 _ h ∧ (a₁ ≫ tI B j p) ≫ tauP B j = secOf B p.1 p.2 _ h ∧ (a₁ ≫ tI B j p) ≫ rhoP B j r hw = (a₁ ≫ rhoC B j r hw p) ≫ wI B p.1 := by
  intro K _ W Z Y q i π D d B T j r hw v hv p V a₁
  have ey : (a₁ ≫ tI B j p) ≫ eP B j ≫ j = a₁ ≫ (oT B j p).ι ≫ j := by
    rw [Category.assoc, ← Category.assoc (tI B j p), e1]
  have hle : ⊤ ≤ (a₁ ≫ (oT B j p).ι ≫ j) ⁻¹ᵁ (B.c p.1).C p.2 := by
    intro x _
    have := oT_le B j p (Set.mem_univ (a₁ x))
    simpa using this
  have key : ∀ (y' : V ⟶ Y) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c p.1).C p.2), y' = a₁ ≫ (oT B j p).ι ≫ j →
      (a₁ ≫ tI B j p).appTop.hom ∘ v = uV B p.1 p.2 y' h' ∧
        (a₁ ≫ tI B j p) ≫ tauP B j = secOf B p.1 p.2 y' h' := by
    rintro y' h' rfl
    obtain ⟨n1, n2⟩ := chartNat B p.1 p.2 a₁ ((oT B j p).ι ≫ j) (oT_le B j p) h'
    refine ⟨?_, ?_⟩
    · funext m
      rw [n1 m, ← hv p m]
      rw [Function.comp_apply, Scheme.Hom.comp_appTop]
      rfl
    · rw [n2, Category.assoc, e2]
  have h : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p.1).C p.2 := by
    rw [ey]; exact hle
  obtain ⟨k1, k2⟩ := key _ h ey
  exact ⟨h, k1, k2, by rw [Category.assoc, e3, Category.assoc]⟩
