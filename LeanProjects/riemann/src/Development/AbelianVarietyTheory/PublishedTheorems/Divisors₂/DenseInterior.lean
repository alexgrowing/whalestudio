import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.LogKS

attribute [local instance] Over.cartesianMonoidalCategory

def IsField {Z : Scheme.{0}} (W₀ : Z.Opens) (d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)) : Prop :=
  (∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f') ∧
    (∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = f * d W f' + f' * d W f) ∧
    ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG Z h f) = resG Z h (d W f)

theorem isField_zero {Z : Scheme.{0}} (W₀ : Z.Opens) : IsField W₀ (fun _ _ => 0) :=
  ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ => by simp⟩

def chart {X : Scheme.{0}} (U : X.affineOpens) : Sp Γ(X, U.1) ⟶ X := U.2.fromSpec

def logDer {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Sp K) (I : X.IdealSheafData) (U : X.affineOpens) :
    Submodule Γ(X, U.1) (Derivation ℤ Γ(X, U.1) Γ(X, U.1)) where
  carrier := {D | (∀ a, D (constFn s U.1 a) = 0) ∧ ∀ f ∈ I.ideal U, D f ∈ I.ideal U}
  zero_mem' := ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  add_mem' := fun {D D'} h h' =>
    ⟨fun a => by simp [h.1 a, h'.1 a], fun f hf => add_mem (h.2 f hf) (h'.2 f hf)⟩
  smul_mem' := fun r D h =>
    ⟨fun a => by simp [h.1 a], fun f hf => Ideal.mul_mem_left _ r (h.2 f hf)⟩

def balanced {O R : Type} [CommRing R] {n : ℕ} (bar : O → O) (A : O → Matrix (Fin n) (Fin n) R) :
    Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := {Θ | Θᵀ = Θ ∧ ∀ a, (A a)ᵀ * Θ = Θ * A (bar a)}
  zero_mem' := ⟨by simp, fun a => by simp⟩
  add_mem' := fun {Θ Θ'} h h' =>
    ⟨by rw [Matrix.transpose_add, h.1, h'.1], fun a => by rw [Matrix.mul_add, Matrix.add_mul, h.2, h'.2]⟩
  smul_mem' := fun r Θ h =>
    ⟨by rw [Matrix.transpose_smul, h.1], fun a => by rw [Matrix.mul_smul, Matrix.smul_mul, h.2]⟩

theorem mem_balanced_diagonal {O R : Type} [CommRing R] {n : ℕ} (bar : O → O) (χ : Fin n → O → R)
    (Θ : Matrix (Fin n) (Fin n) R) :
    Θ ∈ balanced bar (fun a => Matrix.diagonal fun i => χ i a) ↔
      Θᵀ = Θ ∧ ∀ a i k, (χ i a - χ k (bar a)) * Θ i k = 0 := by
  refine and_congr_right fun _ => forall_congr' fun a => ?_
  rw [Matrix.diagonal_transpose, ← Matrix.ext_iff]
  refine forall₂_congr fun i k => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, sub_mul, sub_eq_zero, mul_comm (Θ i k)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def IsTranslate {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : Sp S ⟶ t.G.left)
    (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  ∃ g' v' : tEpsG (g ≫ t.G.hom) ⟶ t.G, g'.left = spMap (algebraMap S (DualNumber S)) ≫ g ∧
    v'.left = spMap (dualMap φ) ≫ v ∧ (g' * v').left = w

theorem existsUnique_isTranslate {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {x : Sp R ⟶ X}
    {g : Sp S ⟶ t.G.left} (hg : g ≫ t.G.hom = spMap φ ≫ x) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : IsTanAtG t x v) : ∃! w, IsTranslate t φ g v w := by
  have e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have h2 : (spMap (dualMap φ) ≫ v) ≫ t.G.hom = (tEpsG (g ≫ t.G.hom)).hom := by
    show _ = spMap (algebraMap S (DualNumber S)) ≫ g ≫ t.G.hom
    rw [Category.assoc, hv.1, hg, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  refine ⟨_, ⟨Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g) (Category.assoc _ _ _),
    Over.homMk (spMap (dualMap φ) ≫ v) h2, rfl, rfl, rfl⟩, ?_⟩
  rintro w ⟨g', v', h₁, h₂, rfl⟩
  congr 2
  · exact Over.OverMorphism.ext h₁
  · exact Over.OverMorphism.ext h₂

def IsKS (V : X.Opens) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) : Prop :=
  ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι)
    (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)),
    ⨆ i, W i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V) ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧
    (∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)),
      d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r)) ∧
    ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O))
      (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left)
      (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)),
      g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) →
      valR g₀ O (d i O f - d i' O f) =
        ∑ a, ∑ b, φ (Θ a b) *
          ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) *
          (valR (w a) O f).snd

theorem isKS_zero (V : X.Opens) (U : X.affineOpens) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) : IsKS t V U v (fun _ => 0) 0 := by
  refine ⟨t.PP.L.ι, fun i => t.G.hom ⁻¹ᵁ (U.1 ⊓ V) ⊓ t.PP.L.U i, id, fun _ _ _ => 0, ?_, fun _ => inf_le_right,
    fun _ => isField_zero _, fun _ _ _ => (map_zero _).symm, fun i i' O _ f S _ φ g₀ w _ h _ => ?_⟩
  · rw [← inf_iSup_eq, t.PP.isLB.cover, inf_top_eq]
  · simp [valR, h]

def HasLogKS {K : Type} [CommRing K] (s : X ⟶ Sp K) (V : X.Opens) : Prop :=
  ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(X, U.1)),
    (∀ i, IsTanAtG t (chart U) (v i)) →
    (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) →
    (∀ a i, IsCombAtG t (chart U) v (A a i) (v i ≫ (t.act.act a).left)) →
    ∃ e : logDer s (Scheme.IdealSheafData.vanishingIdeal V.compl) U ≃ₗ[Γ(X, U.1)] balanced H.bar A,
      ∀ (D : logDer s (Scheme.IdealSheafData.vanishingIdeal V.compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)),
        IsKS t V U v D.1 Θ ↔ Θ = (e D).1

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F))

theorem isIso_fst : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  infer_instance

instance isOpenImmersion_j : IsOpenImmersion Y.j := by
  have := isIso_fst Y
  have := Y.jQ_open
  unfold Model.j
  infer_instance

def interior : Y.X.Opens := Y.j.opensRange

def boundary : Y.X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (interior Y).compl

theorem coe_interior : (interior Y : Set Y.X) = abLocus Y.t.G := by
  have := isIso_fst Y
  have hs : Function.Surjective (pullback.fst Y.s (spMap (RingHom.id c.F))) :=
    (pullback.fst Y.s (spMap (RingHom.id c.F))).surjective
  rw [← Set.image_preimage_eq (abLocus Y.t.G) hs, Y.ab_gen, ← Set.range_comp]
  rfl

theorem dense_interior : Dense (interior Y : Set Y.X) := by
  have := isIso_fst Y
  have hs : Function.Surjective (pullback.fst Y.s (spMap (RingHom.id c.F))) :=
    (pullback.fst Y.s (spMap (RingHom.id c.F))).surjective
  exact hs.denseRange.comp Y.jQ_dense (pullback.fst Y.s (spMap (RingHom.id c.F))).continuous

end GlobalTheory.LogKS

namespace GlobalTheory.Published

open GlobalTheory.LogKS

def ToroidalCompactification : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
      ∃ Y : Model Xo c (RingHom.id c.F),
        SmoothOfRelativeDimension Dw.dim Y.s ∧ ReciprocityTheory.AnForm.R.FinalTheorems.Snc (boundary Y) ∧
          HasLogKS Y.t Y.s (interior Y)

end GlobalTheory.Published
