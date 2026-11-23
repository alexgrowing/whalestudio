import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPairTest

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem over_of_isPull {T T' : Over (Spec (CommRingCat.of R))} {h : T'.left ⟶ T.left} {g : GtPt D T}
    {g' : GtPt D T'} (H : GtPt.IsPull h g g') : h ≫ T.hom = T'.hom := by
  rw [← Over.w g.b, ← Category.assoc, ← H.1, Over.w]

theorem generic_maps_eq (W : (Spec (CommRingCat.of R)).Opens) (χ : D.X) :
    (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ ptK (D.c χ) := by
  change (jK R ∣_ W) ≫ W.ι ≫ (D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ jK R ≫ (D.c χ).left
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

theorem ext_val {T : Over (Spec (CommRingCat.of R))} {g g' : GtPt D T} (hb : g.b = g'.b)
    (hs : ∀ χ y J, Geo.Tor.Good D.P.L y J → Geo.Tor.val (g.s χ) (𝟙 _) y J = Geo.Tor.val (g'.s χ) (𝟙 _) y J) :
    g = g' := by
  obtain ⟨b, s, h, _, _⟩ := g
  obtain ⟨b', s', h', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ =>
    GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ) (Geo.Tor.corr_of_val D.P.isLB (hs χ))
  rfl

theorem isAdd_unique {T : Over (Spec (CommRingCat.of R))} {g g' a a' : GtPt D T} (h : g.IsAdd g' a)
    (h' : g.IsAdd g' a') : a = a' :=
  ext_val (h.1.trans h'.1.symm) fun χ y J hJ => by
    have e := (Geo.Tor.val_corr hJ (h.2 χ) (𝟙 _)).trans (Geo.Tor.val_corr hJ (h'.2 χ) (𝟙 _)).symm
    exact mul_right_cancel ((Geo.Tor.val_mul hJ _ _ _).symm.trans (e.trans (Geo.Tor.val_mul hJ _ _ _)))

theorem isPull_unique {T T' : Over (Spec (CommRingCat.of R))} {h : T'.left ⟶ T.left} {g : GtPt D T}
    {a a' : GtPt D T'} (H : GtPt.IsPull h g a) (H' : GtPt.IsPull h g a') : a = a' :=
  ext_val (Over.OverMorphism.ext (H.1.trans H'.1.symm)) fun χ _ _ hJ =>
    (Geo.Tor.val_corr hJ (H.2 χ) (𝟙 _)).trans (Geo.Tor.val_corr hJ (H'.2 χ) (𝟙 _)).symm

theorem isIota_unique {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) {T : Over W.toScheme} {y : D.X}
    {a a' : GtPt D (overW W T)} (H : GtPt.IsIotaW ψW y a) (H' : GtPt.IsIotaW ψW y a') : a = a' :=
  ext_val (H.1.trans H'.1.symm) fun χ _ _ hJ =>
    (Geo.Tor.val_corr hJ (H.2 χ) (𝟙 _)).trans (Geo.Tor.val_corr hJ (H'.2 χ) (𝟙 _)).symm

theorem isNsmul_unique {T : Over (Spec (CommRingCat.of R))} {k : ℕ} {g a a' : GtPt D T} (h : GtPt.IsNsmul k g a)
    (h' : GtPt.IsNsmul k g a') : a = a' := by
  obtain ⟨u, u0, us, rfl⟩ := h
  obtain ⟨v, v0, vs, rfl⟩ := h'
  have : ∀ i, u i = v i := fun i => by
    induction i using Fin.induction with
    | zero => exact ext_val (u0.1.trans v0.1.symm) fun χ _ _ hJ =>
        (Geo.Tor.val_corr hJ (u0.2 χ) (𝟙 _)).trans (Geo.Tor.val_corr hJ (v0.2 χ) (𝟙 _)).symm
    | succ i ih => exact isAdd_unique (us i) (ih ▸ vs i)
  exact this _

section Empty

theorem corr_of_isEmpty {X Y : Scheme.{0}} [IsEmpty Y] (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) : LB.Gen.Corr L φ ε φ' ε' t t' :=
  fun _ _ _ _ _ => Units.ext (Subsingleton.elim _ _)

variable {T : Over (Spec (CommRingCat.of R))} [IsEmpty T.left]

theorem hom_eq {A : Over (Spec (CommRingCat.of R))} (a b : T ⟶ A) : a = b :=
  Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext _ _)

def emptyPt (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsEmpty T.left] : GtPt D T where
  b := DegPre.zeroT D T
  s := fun _ => ⟨fun _ => 1⟩
  isGen := fun _ _ _ => Units.ext (Subsingleton.elim _ _)
  s_zero := corr_of_isEmpty _ _ _ _ _ _ _
  mult := fun _ _ => corr_of_isEmpty _ _ _ _ _ _ _

theorem gtPt_eq (g g' : GtPt D T) : g = g' := by
  obtain ⟨b, s, _, _, _⟩ := g
  obtain ⟨b', s', _, _, _⟩ := g'
  obtain rfl : b = b' := hom_eq _ _
  obtain rfl : s = s' := funext fun χ => by
    have : (s χ).s = (s' χ).s := funext fun _ => Units.ext (Subsingleton.elim _ _)
    cases h : s χ; cases h' : s' χ
    rw [h, h'] at this
    congr
  rfl

end Empty

variable {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) [IsEmpty T.left]

instance : IsEmpty (overW W T).left := inferInstanceAs (IsEmpty T.left)

def emptyPair (y : D.X) : QkPtW D W ψW k T where
  y := y
  g := emptyPt D _
  eq := ⟨emptyPt D _, ⟨fun _ => emptyPt D _, ⟨hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩,
    fun _ => ⟨hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩, rfl⟩,
    ⟨hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩⟩

theorem equiv_iff_of_isEmpty (p p' : QkPtW D W ψW k T) :
    QkPtW.Equiv p p' ↔ ∃ z : D.X, p'.y = p.y + k • z :=
  ⟨fun ⟨z, hz, _⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, hz, emptyPt D _,
    ⟨hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩, hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩⟩

theorem not_equiv_over_empty {W : (Spec (CommRingCat.of InhTate.R)).Opens} (ψW : PsiOn InhTate.tatePre W) :
    ∃ (T : Over W.toScheme) (_ : IsEmpty T.left) (p p' : QkPtW InhTate.tatePre W ψW 2 T), ¬ QkPtW.Equiv p p' := by
  let T : Over W.toScheme := Over.mk (isInitialOfIsEmpty.to W.toScheme : (∅ : Scheme.{0}) ⟶ _)
  have hT : IsEmpty T.left := inferInstanceAs (IsEmpty (∅ : Scheme.{0}))
  refine ⟨T, hT, emptyPair ψW 2 T (0 : ℤ), emptyPair ψW 2 T (1 : ℤ), ?_⟩
  rintro ⟨z, hz, -⟩
  have key : ∀ w : ℤ, (1 : ℤ) ≠ (0 : ℤ) + 2 • w := fun w hw => by
    rw [two_nsmul] at hw
    omega
  exact key z hz

end GlobalTheory.TorsionPairTest
