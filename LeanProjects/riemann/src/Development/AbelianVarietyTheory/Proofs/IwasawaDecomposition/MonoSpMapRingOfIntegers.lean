import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsEigenBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FlagTan

namespace GlobalTheory.ShFam

instance mono_spMap_ringOfIntegers (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) :=
  have := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 K)) (S := K)
  inferInstance

namespace Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

section Move

variable {A B T : Type} [CommRing A] [Algebra c.F A] [CommRing B] [Algebra c.F B] [CommRing T] [Algebra c.F T]

theorem ptF_fst (P : FrPt Xo c A) : GlobalTheory.AllWt.ptF P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _

theorem ptF_snd (P : FrPt Xo c A) : GlobalTheory.AllWt.ptF P ≫ pullback.snd _ _ = spMap (algebraMap c.F A) :=
  pullback.lift_snd _ _ _

theorem ptF_map {φ : A →ₐ[c.F] B} {P : FrPt Xo c A} {Q : FrPt Xo c B} (h : Q.x = spMap φ.toRingHom ≫ P.x) :
    GlobalTheory.AllWt.ptF Q = spMap φ.toRingHom ≫ GlobalTheory.AllWt.ptF P := by
  apply pullback.hom_ext
  · rw [Category.assoc, ptF_fst, ptF_fst, h]
  · rw [Category.assoc, ptF_snd, ptF_snd, sp_comp]
    exact congrArg spMap φ.comp_algebraMap.symm

def chi (ex : Ix Dw → ℤ) (t : Ix Dw → Aˣ) : Aˣ := ∏ i, t i ^ ex i

def umap (φ : A →ₐ[c.F] B) (t : Ix Dw → Aˣ) : Ix Dw → Bˣ := fun i => Units.map (φ : A →* B) (t i)

theorem chi_mul (ex : Ix Dw → ℤ) (t u : Ix Dw → Aˣ) : chi ex (t * u) = chi ex t * chi ex u := by
  simp [chi, mul_zpow, Finset.prod_mul_distrib]

theorem chi_one (ex : Ix Dw → ℤ) : chi ex (1 : Ix Dw → Aˣ) = 1 := by simp [chi]

theorem chi_umap (ex : Ix Dw → ℤ) (φ : A →ₐ[c.F] B) (t : Ix Dw → Aˣ) :
    (chi ex (umap φ t) : B) = φ (chi ex t : Aˣ) := by
  simp only [chi, umap, ← map_zpow, ← map_prod]
  rfl

theorem frBor_one (P : FrPt Xo c A) : FrBor 1 P P :=
  ((frBor_calculus E H Dw l Xo c A P P P).1 1).2 ⟨fun _ => 1, fun _ _ _ h => Matrix.one_apply_ne h.ne,
    fun _ _ => Matrix.one_apply_eq _, (frChg_refl_and_comp E H Dw l Xo c A P P P).1⟩

theorem frBor_unique {t u : Ix Dw → Aˣ} {P Q : FrPt Xo c A} (h : FrBor t P Q) (h' : FrBor u P Q) : t = u := by
  obtain ⟨g, -, g2, g3⟩ := ((frBor_calculus E H Dw l Xo c A P Q Q).1 t).1 h
  obtain ⟨g', -, g2', g3'⟩ := ((frBor_calculus E H Dw l Xo c A P Q Q).1 u).1 h'
  obtain ⟨e1, e2⟩ := (frChg_exists_unique E H Dw l Xo c A P Q).2 _ _ _ _ g3 g3'
  funext i
  rcases i with _ | ⟨τ, i⟩
  · exact Units.ext e2
  · exact Units.ext (by rw [← g2, ← g2', e1])

theorem frBor_map {φ : A →ₐ[c.F] B} {t : Ix Dw → Aˣ} {P Q : FrPt Xo c A} {P' Q' : FrPt Xo c B} (h : FrBor t P Q)
    (hP : FrMap φ P P') (hQ : FrMap φ Q Q') : FrBor (umap φ t) P' Q' := by
  obtain ⟨g, g1, g2, g3⟩ := ((frBor_calculus E H Dw l Xo c A P Q Q).1 t).1 h
  refine ((frBor_calculus E H Dw l Xo c B P' Q' Q').1 _).2 ⟨_, fun τ i j hij => ?_, fun τ i => ?_,
    (frMap_iff_frChg g3 hP).1 hQ⟩
  · simp [g1 τ i j hij]
  · simp [g2, umap]

theorem isUnit_diag {n : ℕ} {g : Matrix (Fin n) (Fin n) A} (h : ∀ i j, i < j → g i j = 0) (hg : IsUnit g.det)
    (i : Fin n) : IsUnit (g i i) := by
  rw [Matrix.det_of_lowerTriangular g fun i j hij => h i j hij] at hg
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => g i i) (Finset.mem_univ i)) hg

theorem exists_frBor {P Q : FrPt Xo c A} (hx : Q.x = P.x) (g : ∀ τ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)
    (h : ∀ τ i j, i < j → g τ i j = 0) (hc : ∀ τ i, IsCombAt P.x (P.u τ) (g τ i) (Q.u τ i)) :
    ∃ t, FrBor t P Q ∧ ∀ τ i, (t (some ⟨τ, i⟩) : A) = g τ i i := by
  obtain ⟨g', a, hg', hc'⟩ := (frChg_exists_unique E H Dw l Xo c A P Q).1 hx
  obtain rfl : g = g' := by
    funext τ i
    exact (P.basis τ _ (hx ▸ Q.tan τ i) (Q.eig τ i)).unique (hc τ i) (hc'.2.1 τ i)
  refine ⟨fun i => match i with
    | none => a
    | some x => (isUnit_diag (h x.1) (hg' x.1) x.2).unit, ?_, fun _ _ => rfl⟩
  exact ((frBor_calculus E H Dw l Xo c A P Q Q).1 _).2 ⟨g, h, fun _ _ => rfl, hc'⟩

def BM (φ : A →ₐ[c.F] B) (t : Ix Dw → Bˣ) (P : FrPt Xo c A) (Q : FrPt Xo c B) : Prop :=
  ∃ P', FrMap φ P P' ∧ FrBor t P' Q

theorem BM.of_frMap {φ : A →ₐ[c.F] B} {P : FrPt Xo c A} {Q : FrPt Xo c B} (h : FrMap φ P Q) : BM φ 1 P Q :=
  ⟨Q, h, frBor_one Q⟩

theorem BM.of_frBor {t : Ix Dw → Aˣ} {P Q : FrPt Xo c A} (h : FrBor t P Q) : BM (AlgHom.id _ _) t P Q :=
  ⟨P, frMap_id P, h⟩

theorem BM.x_eq {φ : A →ₐ[c.F] B} {t : Ix Dw → Bˣ} {P : FrPt Xo c A} {Q : FrPt Xo c B} (h : BM φ t P Q) :
    Q.x = spMap φ.toRingHom ≫ P.x := by
  obtain ⟨P', h1, h2⟩ := h
  exact h2.1.trans h1.1

theorem BM.comp {φ : A →ₐ[c.F] B} {ψ : B →ₐ[c.F] T} {χ : A →ₐ[c.F] T} {t : Ix Dw → Bˣ} {u : Ix Dw → Tˣ}
    {P : FrPt Xo c A} {Q : FrPt Xo c B} {R : FrPt Xo c T} (h : BM φ t P Q) (h' : BM ψ u Q R)
    (e : ∀ a, ψ (φ a) = χ a) : BM χ (u * umap ψ t) P R := by
  obtain ⟨P', h1, h2⟩ := h
  obtain ⟨Q', k1, k2⟩ := h'
  obtain ⟨P'', hP⟩ := exists_frMap ψ P'
  exact ⟨P'', frMap_comp h1 hP e, (frBor_calculus E H Dw l Xo c T P'' Q' R).2.2.1 _ _ (frBor_map h2 hP k1) k2⟩

theorem BM.unique {φ : A →ₐ[c.F] B} {t u : Ix Dw → Bˣ} {P : FrPt Xo c A} {Q : FrPt Xo c B} (h : BM φ t P Q)
    (h' : BM φ u P Q) : t = u := by
  obtain ⟨P', h1, h2⟩ := h
  obtain ⟨P'', k1, k2⟩ := h'
  obtain rfl := frMap_unique h1 k1
  exact frBor_unique h2 k2

theorem BM.cancel {φ : A →ₐ[c.F] B} {ψ : B →ₐ[c.F] T} {χ : A →ₐ[c.F] T} {u : Ix Dw → Tˣ}
    {P : FrPt Xo c A} {Q : FrPt Xo c B} {R : FrPt Xo c T} (h : FrMap φ P Q) (h' : BM χ u P R)
    (e : ∀ a, ψ (φ a) = χ a) : BM ψ u Q R := by
  obtain ⟨P', h1, h2⟩ := h'
  exact ⟨P', frMap_of_comp h h1 e, h2⟩

theorem BM.descend {φ : A →ₐ[c.F] B} (hφ : Function.Injective φ) {t u : Ix Dw → Bˣ} {P P₂ : FrPt Xo c A}
    {Q : FrPt Xo c B} (hx : P₂.x = P.x) (h : BM φ t P Q) (h' : BM φ u P₂ Q) :
    ∃ v, FrBor v P P₂ ∧ t = u * umap φ v := by
  obtain ⟨g, a, -, hc⟩ := (frChg_exists_unique E H Dw l Xo c A P P₂).1 hx
  obtain ⟨P', h1, h2⟩ := id h
  obtain ⟨P₂', k1, k2⟩ := id h'
  have b := (frBor_calculus E H Dw l Xo c B P' Q P₂').2.2.1 _ _ h2 ((frBor_calculus E H Dw l Xo c B P₂' Q Q).2.2.2 _ k2)
  obtain ⟨g', g1, -, g3⟩ := ((frBor_calculus E H Dw l Xo c B P' P₂' P₂').1 _).1 b
  obtain ⟨e1, -⟩ := (frChg_exists_unique E H Dw l Xo c B P' P₂').2 _ _ _ _ g3 ((frMap_iff_frChg hc h1).1 k1)
  obtain ⟨v, hv, -⟩ := exists_frBor hx g (fun τ i j hij => hφ (by
    have := g1 τ i j hij
    rw [e1] at this
    rw [map_zero]; exact this)) hc.2.1
  exact ⟨v, hv, h.unique ((BM.of_frBor hv).comp h' fun _ => rfl)⟩

theorem BM.evR [IsLocalRing A] [IsLocalRing B] {φ : A →ₐ[c.F] B} {t : Ix Dw → Bˣ} {P : FrPt Xo c A} {Q : FrPt Xo c B}
    (h : BM φ t P Q) {ex : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c ex) :
    evR Xo c f Q = chi ex t * φ (evR Xo c f P) := by
  obtain ⟨P', h1, h2⟩ := h
  rw [evR_frBor hf h2, evR_frMap hf.1 h1]
  rfl

end Move

section Dict

variable {S T : Type} [CommRing S] [CommRing T]

attribute [local instance] Over.cartesianMonoidalCategory in
open GlobalTheory.Exist.FlagBaseChange MonObj in

theorem sab_dict {X X' : Scheme.{0}} {t' : SAB H X'} {t : SAB H X} {f : X' ⟶ X} (m : SABMap t' t f) {x' : Sp S ⟶ X'}
    {x : Sp S ⟶ X} (hx : x' ≫ f = x) :
    (∀ v : Sp (DualNumber S) ⟶ t.G.left, v ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x →
      ∃ w, w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ∧ w ≫ m.φ = v) ∧
    (∀ w : Sp (DualNumber S) ⟶ t'.G.left, w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' →
      (IsTanAtG t x (w ≫ m.φ) ↔ IsTanAtG t' x' w) ∧ ∀ χ : 𝓞 E → S,
        (∀ a, (w ≫ m.φ) ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ w ≫ m.φ) ↔
          ∀ a, w ≫ (t'.act.act a).left = spMap (epsMul (χ a)) ≫ w) ∧
    ∀ (n : ℕ) (w : Fin n → (Sp (DualNumber S) ⟶ t'.G.left)) (a : Fin n → S) (w' : Sp (DualNumber S) ⟶ t'.G.left),
      (∀ i, w i ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') →
      w' ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' →
      (IsCombAtG t x (fun i => w i ≫ m.φ) a (w' ≫ m.φ) ↔ IsCombAtG t' x' w a w') := by
  obtain ⟨B, hB, h1, h2, h3⟩ := exists_tangentEquiv m.cart t'.act.act t.act.act m.act x' x hx
  refine ⟨fun v hv => ?_, fun w hw => ⟨?_, fun χ => ?_⟩, fun n w a w' hw hw' => ?_⟩
  · obtain ⟨w, e⟩ := B.surjective (Over.homMk v hv)
    exact ⟨w.left, Over.w w, (hB w).symm.trans (congrArg (fun u => u.left) e)⟩
  · have := h1 (Over.homMk w hw)
    unfold TanAt at this
    rw [hB] at this
    have e := Over.w (B (Over.homMk w hw))
    rw [hB] at e
    exact (and_iff_right e).trans (this.trans (and_iff_right hw).symm)
  · have := h2 χ (Over.homMk w hw)
    unfold EigAt at this
    simp only [Over.comp_left, hB] at this
    exact this
  · have := h3 n (fun i => Over.homMk (w i) (hw i)) a (Over.homMk w' hw')
    unfold CombAt at this
    simp only [hB, Over.OverMorphism.ext_iff] at this
    unfold IsCombAtG
    simp only [eq_comm (b := w'), eq_comm (b := w' ≫ m.φ)]
    exact this

variable {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)

def TanRel (xF : Sp S ⟶ Xo.XF c) (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (v : Sp (DualNumber S) ⟶ Z.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber S) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ xF ∧
    w ≫ Z.m0.toSABMap.φ = u ∧ w ≫ Z.m.φ = v

variable {Z} {xF : Sp S ⟶ Xo.XF c} {x₀ : Sp S ⟶ Xo.X} {x : Sp S ⟶ Z.X}

theorem TanRel.map (ψ : S →+* T) {u v} (h : TanRel Z xF u v) :
    TanRel Z (spMap ψ ≫ xF) (spMap (dualMap ψ) ≫ u) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨w, h1, rfl, rfl⟩ := h
  refine ⟨spMap (dualMap ψ) ≫ w, ?_, Category.assoc _ _ _, Category.assoc _ _ _⟩
  rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
  congr 2
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_tanRel_right (h₀ : xF ≫ pullback.fst _ _ = x₀) {u} (hu : IsTanAt x₀ u) : ∃ v, TanRel Z xF u v := by
  obtain ⟨w, h1, h2⟩ := (sab_dict Z.m0.toSABMap h₀).1 u hu.1
  exact ⟨_, w, h1, h2, rfl⟩

theorem exists_tanRel_left (hx : xF ≫ Z.j = x) {v} (hv : IsTanAtG Z.t x v) : ∃ u, TanRel Z xF u v := by
  obtain ⟨w, h1, h2⟩ := (sab_dict Z.m hx).1 v hv.1
  exact ⟨_, w, h1, rfl, h2⟩

theorem TanRel.tan_iff (h₀ : xF ≫ pullback.fst _ _ = x₀) (hx : xF ≫ Z.j = x) {u v} (h : TanRel Z xF u v) :
    IsTanAt x₀ u ↔ IsTanAtG Z.t x v := by
  obtain ⟨w, h1, rfl, rfl⟩ := h
  exact ((sab_dict Z.m0.toSABMap h₀).2.1 w h1).1.trans ((sab_dict Z.m hx).2.1 w h1).1.symm

theorem TanRel.eig_iff {u v} (h : TanRel Z xF u v) (χ : 𝓞 E → S) :
    (∀ a, u ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (χ a)) ≫ u) ↔
      ∀ a, v ≫ (Z.t.act.act a).left = spMap (epsMul (χ a)) ≫ v := by
  obtain ⟨w, h1, rfl, rfl⟩ := h
  exact (((sab_dict Z.m0.toSABMap rfl).2.1 w h1).2 χ).trans (((sab_dict Z.m rfl).2.1 w h1).2 χ).symm

theorem TanRel.comb_iff (h₀ : xF ≫ pullback.fst _ _ = x₀) (hx : xF ≫ Z.j = x) {n : ℕ} {u v u' v'}
    (h : ∀ i : Fin n, TanRel Z xF (u i) (v i)) (h' : TanRel Z xF u' v') (a : Fin n → S) :
    IsCombAt x₀ u a u' ↔ IsCombAtG Z.t x v a v' := by
  choose w h1 h2 h3 using h
  obtain ⟨w', k1, rfl, rfl⟩ := h'
  obtain rfl : u = _ := (funext h2).symm
  obtain rfl : v = _ := (funext h3).symm
  exact ((sab_dict Z.m0.toSABMap h₀).2.2 n w a w' h1 k1).trans ((sab_dict Z.m hx).2.2 n w a w' h1 k1).symm

variable [Algebra c.F S] [Algebra c.F T]

def Comparison₂ (P : FrPt Xo c S) {φ : c.F →+* S} {x : Sp S ⟶ Z.X} (g : EigFrame Z φ x) : Prop :=
  φ = algebraMap c.F S ∧ GlobalTheory.AllWt.ptF P ≫ Z.j = x ∧ ∀ τ i, TanRel Z (GlobalTheory.AllWt.ptF P) (P.u τ i) (g.v τ i)

theorem exists_tie_frame (P : FrPt Xo c S) (hx : GlobalTheory.AllWt.ptF P ≫ Z.j = x) :
    ∃ g : EigFrame Z (algebraMap c.F S) x, Comparison₂ P g := by
  choose v hv using fun τ i => exists_tanRel_right (Z := Z) (ptF_fst P) (P.tan τ i)
  refine ⟨⟨v, fun τ i => ((hv τ i).tan_iff (ptF_fst P) hx).1 (P.tan τ i), fun τ i => ((hv τ i).eig_iff _).1 (P.eig τ i),
    fun τ w hw he => ?_⟩, rfl, hx, hv⟩
  obtain ⟨u, hu⟩ := exists_tanRel_left hx hw
  exact (existsUnique_congr fun a => TanRel.comb_iff (ptF_fst P) hx (hv τ) hu a).1
    (P.basis τ u ((hu.tan_iff (ptF_fst P) hx).2 hw) ((hu.eig_iff _).2 he))

theorem exists_tie_point [IsLocalRing S] (hF : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (hx : xF ≫ Z.j = x)
    {φ : c.F →+* S} (hφ : φ = algebraMap c.F S) (g : EigFrame Z φ x) :
    ∃ P : FrPt Xo c S, GlobalTheory.AllWt.ptF P = xF ∧ Comparison₂ P g := by
  subst hφ
  obtain ⟨P, hP⟩ := exists_frPt (c := c) (xF ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hF, sp_comp]; rfl)
  have e : GlobalTheory.AllWt.ptF P = xF := pullback.hom_ext ((ptF_fst P).trans hP) ((ptF_snd P).trans hF.symm)
  subst e
  choose u hu using fun τ i => exists_tanRel_left hx (g.tan τ i)
  refine ⟨⟨P.x, P.x_over, u, fun τ i => ((hu τ i).tan_iff (ptF_fst P) hx).2 (g.tan τ i),
    fun τ i => ((hu τ i).eig_iff _).2 (g.eig τ i), fun τ w hw he => ?_, P.s, P.gen⟩, rfl, rfl, hx, hu⟩
  obtain ⟨v, hv⟩ := exists_tanRel_right (Z := Z) (ptF_fst P) hw
  exact (existsUnique_congr fun a => TanRel.comb_iff (ptF_fst P) hx (hu τ) hv a).2
    (g.basis τ v ((hv.tan_iff (ptF_fst P) hx).1 hw) ((hv.eig_iff _).1 he))

theorem Comparison₂.tri_of_bm {P : FrPt Xo c S} {Q : FrPt Xo c T} {φ : c.F →+* S} {φ' : c.F →+* T} {x' : Sp T ⟶ Z.X}
    {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} (hf : Comparison₂ P f) (hg : Comparison₂ Q g) {ψ : S →ₐ[c.F] T} {t : Ix Dw → Tˣ}
    (h : BM ψ t P Q) : f.Tri ψ.toRingHom g fun τ i => t (some ⟨τ, i⟩) := by
  have e := ptF_map h.x_eq
  obtain ⟨P', h1, h2⟩ := h
  refine ⟨by rw [← hg.2.1, e, Category.assoc, hf.2.1], by rw [hg.1, hf.1]; exact ψ.comp_algebraMap.symm, fun τ i => ?_⟩
  obtain ⟨cf, c1, c2, c3⟩ := h2.2.1 τ i
  refine ⟨cf, c1, c2, (TanRel.comb_iff ((ptF_fst Q).trans h2.1) hg.2.1 (fun k => ?_) (hg.2.2 τ i) cf).1 c3⟩
  rw [e, h1.2.1]
  exact (hf.2.2 τ k).map _

theorem Comparison₂.comb {P : FrPt Xo c S} {P' Q : FrPt Xo c T} {φ : c.F →+* S} {φ' : c.F →+* T} {x' : Sp T ⟶ Z.X}
    {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} (hf : Comparison₂ P f) (hg : Comparison₂ Q g) {ψ : S →ₐ[c.F] T} (hP : FrMap ψ P P')
    (hx : Q.x = P'.x) (τ : E →+* ℂ) {v : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Z.t.G.left)}
    {M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {N : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T}
    (hM : ∀ i, IsCombAtG Z.t x (f.v τ) (M i) (v i))
    (hN : ∀ i, IsCombAtG Z.t x' (fun k => spMap (dualMap ψ.toRingHom) ≫ v k) (N i) (g.v τ i)) (i : Fin (Dw.mult τ)) :
    IsCombAt P'.x (P'.u τ) ((N * M.map ψ) i) (Q.u τ i) := by
  have e := ptF_map (hx.trans hP.1)
  have ex : x' = spMap ψ.toRingHom ≫ x := by rw [← hg.2.1, e, Category.assoc, hf.2.1]
  refine (TanRel.comb_iff (v := fun k => spMap (dualMap ψ.toRingHom) ≫ f.v τ k) ((ptF_fst Q).trans hx) hg.2.1
    (fun k => ?_) (hg.2.2 τ i) _).2 ?_
  · rw [e, hP.2.1]
    exact (hf.2.2 τ k).map _
  · subst ex
    have := GlobalTheory.TangentLinear.isCombAtG_mulVec _ (fun k => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ.toRingHom (f.tan τ k)) _
      (M.map ψ).transpose (N i) _ (fun k => GlobalTheory.EigenReduction.isCombAtG_map Z.t ψ.toRingHom (hM k)) (hN i)
    rwa [Matrix.mulVec_transpose] at this

theorem Comparison₂.bm_of_tri {P : FrPt Xo c S} {Q : FrPt Xo c T} {φ : c.F →+* S} {φ' : c.F →+* T} {x' : Sp T ⟶ Z.X}
    {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} (hf : Comparison₂ P f) (hg : Comparison₂ Q g) {ψ : S →ₐ[c.F] T}
    (hx : Q.x = spMap ψ.toRingHom ≫ P.x) {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Tˣ} (h : f.Tri ψ.toRingHom g t) :
    ∃ u, BM ψ u P Q ∧ ∀ τ i, u (some ⟨τ, i⟩) = t τ i := by
  obtain ⟨P', hP⟩ := exists_frMap ψ P
  choose cf c1 c2 c3 using h.2.2
  have hx' := hx.trans hP.1.symm
  have e := ptF_map hx
  obtain ⟨u, hu, hu'⟩ := exists_frBor hx' cf c2 fun τ i =>
    (TanRel.comb_iff ((ptF_fst Q).trans hx') hg.2.1 (fun k => by
      rw [e, hP.2.1]
      exact (hf.2.2 τ k).map _) (hg.2.2 τ i) _).2 (c3 τ i)
  exact ⟨u, ⟨P', hP, hu⟩, fun τ i => Units.ext ((hu' τ i).trans (c1 τ i))⟩

end Dict

end Descent

end GlobalTheory.ShFam
