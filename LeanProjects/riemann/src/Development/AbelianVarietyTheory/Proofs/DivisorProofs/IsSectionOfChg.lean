import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCompactForm
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor

namespace GlobalTheory.DetLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}

section Generic

variable {S X : Scheme.{0}} {F : Type} [Field F]

def FrameCover (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) (p q : ℕ) : Prop :=
  ∀ z ∈ V, ∃ (W : X.Opens) (hW : IsAffineOpen W) (j : F →+* Γ(X, W))
    (v : Fin p → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G))
    (w : Fin q → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G)),
    z ∈ W ∧ IsFrame t π s V χ j (show Sp Γ(X, W) ⟶ X from hW.fromSpec) v w

def IsChg (t : SAB H S) (π : X ⟶ S) {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R')
    (x : Sp R ⟶ X) (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G))
    (x' : Sp R' ⟶ X) (v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)) (w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G))
    (M : Matrix (Fin p) (Fin p) R') (N : Matrix (Fin q) (Fin q) R') : Prop :=
  x' = spMap g ≫ x ∧
    (∀ i, FramedFlatCoordinates.IsCombination (x' ≫ π) (M i) (fun k => spMap (Chart.dualMapR g) ≫ (v k).left) (v' i)) ∧
    ∀ i, FramedFlatCoordinates.IsCombination (x' ≫ π) (N i) (fun k => spMap (Chart.dualMapR g) ≫ (w k).left) (w' i)

def locPt (Y : Scheme.{0}) (y : Y) : Sp (Y.presheaf.stalk y) ⟶ Y := Y.fromSpecStalk y

def genPt (Y : Scheme.{0}) [IsIntegral Y] : Sp Y.functionField ⟶ Y := Y.fromSpecStalk (genericPoint Y)

def UnitAtPt (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) {p q : ℕ}
    {Y : Scheme.{0}} [IsIntegral Y] (io : Y ⟶ X) (v₀ : Fin p → (epsAt ((genPt Y ≫ io) ≫ π) ⟶ t.G))
    (w₀ : Fin q → (epsAt ((genPt Y ≫ io) ≫ π) ⟶ t.G)) (δ : Y.functionField) (y : Y) : Prop :=
  ∃ (j : F →+* Y.presheaf.stalk y) (v : Fin p → (epsAt ((locPt Y y ≫ io) ≫ π) ⟶ t.G))
    (w : Fin q → (epsAt ((locPt Y y ≫ io) ≫ π) ⟶ t.G)) (M : Matrix (Fin p) (Fin p) Y.functionField)
    (N : Matrix (Fin q) (Fin q) Y.functionField) (u : (Y.presheaf.stalk y)ˣ),
    IsFrame t π s V χ j (locPt Y y ≫ io) v w ∧
    IsChg t π (algebraMap (Y.presheaf.stalk y) Y.functionField) (locPt Y y ≫ io) v w (genPt Y ≫ io) v₀ w₀ M N ∧
    N.det * algebraMap (Y.presheaf.stalk y) Y.functionField u = M.det * δ

end Generic

variable {D : Datum H} {l : Level H}

theorem comp_chi (c : Coeff l) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) :
    j.comp (HermitianCompactForm.chi c τ) = FramedFlatCoordinates.chr c τ j := rfl

theorem comp_chi_bar (c : Coeff l) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) :
    j.comp ((HermitianCompactForm.chi c τ).comp (H.bar : 𝓞 E →+* 𝓞 E)) = FramedFlatCoordinates.chr c (conjEmb τ) j := by
  refine RingHom.ext fun a => congrArg j (Subtype.ext ?_)
  change τ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (τ (a : E))
  rw [H.bar_eq]
  exact IsCMField.complexEmbedding_complexConj E τ _

section Laws

variable {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R']

theorem exists_pull (g : R →+* R') {j : c.F →+* R} {x : Sp R ⟶ X} {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)}
    {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)} (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) {x' : Sp R' ⟶ X}
    (hx : x' = spMap g ≫ x) :
    ∃ (v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)) (w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)),
      IsFrame t π s V (HermitianCompactForm.chi c τ) (g.comp j) x' v' w' ∧
      (∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left) ∧
      ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : x' ≫ π = spMap g ≫ x ≫ π := by rw [hx, Category.assoc]
  rw [comp_chi_bar] at h4
  obtain ⟨v', a, a'⟩ := DetExtendZero.exists_basis (FlatRow.eigStable t c) g e (τ := τ) h3
  obtain ⟨w', b, b'⟩ := DetExtendZero.exists_basis (FlatRow.eigStable t c) g e (τ := conjEmb τ) h4
  refine ⟨v', w', ⟨?_, ?_, a, by rw [comp_chi_bar]; exact b⟩, a', b'⟩
  · rw [hx, Category.assoc, h1, DetExtendZero.spMap_comp]
  · rintro _ ⟨z, rfl⟩
    rw [hx, Scheme.Hom.comp_apply]
    exact h2 ⟨_, rfl⟩

theorem exists_chg (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'} {x : Sp R ⟶ X}
    {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)} {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)} {x' : Sp R' ⟶ X}
    {v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)} {w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') (hx : x' = spMap g ≫ x) :
    j' = g.comp j ∧ ∃ M N, IsChg t π g x v w x' v' w' M N := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hx
  have hj : j' = g.comp j := by
    have := h'.1.symm.trans h₁.1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  subst hj
  choose M hM using fun i => (h₁.2.2.1.2 _ (h'.2.2.1.1 i)).exists
  choose N hN using fun i => (h₁.2.2.2.2 _ (h'.2.2.2.1 i)).exists
  refine ⟨rfl, Matrix.of M, Matrix.of N, hx, fun i => ?_, fun i => ?_⟩
  · simp only [← a]; exact hM i
  · simp only [← b]; exact hN i

theorem sec_chg {σ : Rule t π p q} (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) {g : R →+* R'} {j : c.F →+* R}
    {j' : c.F →+* R'} {x : Sp R ⟶ X} {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)} {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)}
    {x' : Sp R' ⟶ X} {v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)} {w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') {M N}
    (hc : IsChg t π g x v w x' v' w' M N) : N.det * g (σ R x v w) = M.det * σ R' x' v' w' := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hc.1
  obtain rfl := (exists_chg g h h' hc.1).1
  rw [← hσ.1 R R' g (Chart.dualMapR g) j _ x x' v w v₁ w₁ (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) h h₁ hc.1 a b]
  refine hσ.2 R' _ x' v₁ w₁ v' w' M N h₁ h' (fun i => ?_) fun i => ?_
  · have := hc.2.1 i
    simp only [← a] at this
    exact this
  · have := hc.2.2 i
    simp only [← b] at this
    exact this

theorem isSection_of_chg {σ : Rule t π p q}
    (hσ : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (j : c.F →+* R) (j' : c.F →+* R') x v w x' v' w' M N,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w' → IsChg t π g x v w x' v' w' M N →
      N.det * g (σ R x v w) = M.det * σ R' x' v' w') : IsSection t π s V (HermitianCompactForm.chi c τ) σ := by
  refine ⟨fun R R' _ _ g gε j j' x x' v w v' w' h1 h2 h h' hx a b => ?_, fun R _ j x v w v' w' M N h h' a b => ?_⟩
  · obtain rfl : gε = Chart.dualMapR g := by
      refine RingHom.ext fun z => ?_
      have e : z = algebraMap R _ z.fst + algebraMap R _ z.snd * DualNumber.eps := by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [e, map_add, map_mul, h1, h1, h2]
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    have := hσ R R' g j j' x v w x' v' w' 1 1 h h' ⟨hx, fun i => ?_, fun i => ?_⟩
    · simpa using this.symm
    · simp only [← a]; exact DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
    · simp only [← b]; exact DetExtendZero.comb_one (fun k => (h'.2.2.2.1 k).1) i
  · refine hσ R R (RingHom.id R) j j x v w x v' w' M N h h'
      ⟨by rw [DetExtendZero.spMap_id, Category.id_comp], fun i => ?_, fun i => ?_⟩
    · simp only [DetExtendZero.dual_id, Category.id_comp]; exact a i
    · simp only [DetExtendZero.dual_id, Category.id_comp]; exact b i

end Laws

section Concrete

variable (Xo : Moduli D l) (c : Coeff l)

abbrev FrU (U : Set (Xo.XF c)) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Xo.XF c)
    (v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) (w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) : Prop :=
  IsFrame Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) j x v w

abbrev RuleU : Type 1 := Rule Xo.univ.t (toX Xo c) D.p D.q

abbrev SecU (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) : Prop :=
  IsSection Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ

abbrev NzU (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) : Prop :=
  NowhereZero Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ

variable {Xo c} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

abbrev FrY (V : Set (gen Y)) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ gen Y)
    (v : Fin D.p → (epsAt (x ≫ genι Y) ⟶ Y.t.G)) (w : Fin D.q → (epsAt (x ≫ genι Y) ⟶ Y.t.G)) : Prop :=
  IsFrame Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) j x v w

abbrev RuleY : Type 1 := Rule Y.t (genι Y) D.p D.q

abbrev SecY (V : Set (gen Y)) (τ : E →+* ℂ) (σ : RuleY Y) : Prop :=
  IsSection Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) σ

abbrev NzY (V : Set (gen Y)) (τ : E →+* ℂ) (σ : RuleY Y) : Prop :=
  NowhereZero Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) σ

variable {Y}

def Match (τ : E →+* ℂ) {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Y.X} (f : EigFrame Y φ x)
    (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G)) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → (v i).left = f.v τ k) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → (w i).left = f.v (conjEmb τ) k

def PerData (c : Coeff l) (e : c.F →+* ℂ) (Di : Datum H) {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (P : Di.La →+ (Fin g → ℂ)) (W : Pad.Letter D → Fin g → ℂ) (Q : Di.La →+ (Pad.Letter D → ℂ)) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) ∧ Submodule.span ℝ (Set.range P) = ⊤ ∧
    (∀ a b, (herm Hm (P a) (P b)).im = Di.EF a b) ∧ LinearIndependent ℂ W ∧ (∀ v, P v = ∑ z, Q v z • W z) ∧
    ∀ (a : 𝓞 E) v (z : Pad.Letter D), Q (a • v) z = Formalism.L2.PjFree.relab c e z.1 (a : E) * Q v z

def MatchVec (τ : E →+* ℂ) {g : ℕ} (W : Pad.Letter D → Fin g → ℂ) (V : Fin D.p → Fin g → ℂ)
    (W₀ : Fin D.q → Fin g → ℂ) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → V i = W ⟨τ, k⟩) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → W₀ i = W ⟨conjEmb τ, k⟩

end Concrete

end GlobalTheory.DetLine
