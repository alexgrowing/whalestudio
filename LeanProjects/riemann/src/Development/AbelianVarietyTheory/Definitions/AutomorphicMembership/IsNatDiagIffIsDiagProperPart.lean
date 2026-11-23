import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenImmersionGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

namespace Mdl

theorem isFrame_chart_bc (Z : Mdl Y i₀) (a : Fin Z.m) {k : Type} [CommRing k] (φ : Γ(Z.X, (Z.U a).1) →+* k) :
    IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ) :=
  isFrame_bc E H Dw _ _ _ _ _ _ _ φ _ _ (Z.frame a)

theorem comp_alg_eq (Z : Mdl Y i₀) {a a' : Fin Z.m} {k : Type} [Field k] {φ : Γ(Z.X, (Z.U a).1) →+* k}
    {φ' : Γ(Z.X, (Z.U a').1) →+* k} (h : spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a') :
    φ.comp (Z.alg a) = φ'.comp (Z.alg a') := by
  have e : spMap (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) =
      spMap (φ'.comp ((Z.alg a').comp (Z.i.c.V W).subtype)) := by
    have := congrArg (· ≫ Z.s) h
    simp only [Category.assoc, Z.alg_s] at this
    simpa only [spMap, CommRingCat.ofHom_comp, Spec.map_comp] using this
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  exact IsLocalization.ringHom_ext (nonZeroDivisors (Z.i.c.V W)) e'

theorem flagAt_of_properLE (Z : Mdl Y i₀) {ty ty' : (E →+* ℂ) → Finset ℕ} (h : ProperLE Dw ty' ty) {k : Type} [Field k]
    {w : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} (hw : Pre.FlagAt { Z.toPre with ty := ty } w u) :
    Pre.FlagAt { Z.toPre with ty := ty' } w u := by
  obtain ⟨a, φ, rfl, hu, hs⟩ := hw
  refine ⟨a, φ, rfl, hu, SameFlag.of_properLE ?_ hu h hs⟩
  rw [Category.assoc]
  exact Z.isFrame_chart_bc a φ

def withType (Z : Mdl Y i₀) (ty : (E →+* ℂ) → Finset ℕ) (h₁ : ProperLE Dw ty Z.ty) (h₂ : ProperLE Dw Z.ty ty) :
    Mdl Y i₀ :=
  { Z with
    ty := ty
    glue := fun k _ a a' φ φ' h => by
      refine SameFlag.of_properLE (Z.isFrame_chart_bc a φ) ?_ h₁ (Z.glue k a a' φ φ' h)
      have h' : spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' := h
      have := Z.isFrame_chart_bc a' φ'
      rwa [← Z.comp_alg_eq h', ← Category.assoc, ← h', Category.assoc] at this
    bij := fun k _ f y hy u hu => by
      obtain ⟨w, hw, uniq⟩ := Z.bij k f y hy u hu
      exact ⟨w, ⟨hw.1, Z.flagAt_of_properLE h₁ hw.2⟩, fun w' hw' => uniq w' ⟨hw'.1, Z.flagAt_of_properLE h₂ hw'.2⟩⟩ }

theorem flagAt_withType (Z : Mdl Y i₀) {ty : (E →+* ℂ) → Finset ℕ} (h₁ : ProperLE Dw ty Z.ty) (h₂ : ProperLE Dw Z.ty ty)
    {k : Type} [Field k] {w : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} : (Z.withType ty h₁ h₂).FlagAt w u ↔ Z.FlagAt w u :=
  ⟨fun h => Z.flagAt_of_properLE h₂ h, fun h => Z.flagAt_of_properLE h₁ h⟩

def properPart (Z : Mdl Y i₀) : Mdl Y i₀ :=
  Z.withType (fun σ => (Z.ty σ).filter fun k => 0 < k ∧ k < Dw.mult σ) (.of_subset fun _ => Finset.filter_subset _ _)
    fun _ _ hk h₀ h₁ => Finset.mem_filter.2 ⟨hk, h₀, h₁⟩

def addTop (Z : Mdl Y i₀) (σ : E →+* ℂ) : Mdl Y i₀ :=
  open Classical in
  Z.withType (fun τ => if τ = σ then insert (Dw.mult τ) (Z.ty τ) else Z.ty τ)
    (fun τ k hk _ h₁ => by
      dsimp only at hk
      split_ifs at hk
      · exact (Finset.mem_insert.1 hk).resolve_left h₁.ne
      · exact hk)
    (.of_subset fun τ => by
      split_ifs
      · exact Finset.subset_insert _ _
      · exact subset_rfl)

end Mdl

theorem natImg_withType_right {Z₁ Z₂ : Mdl Y i₀} {ty : (E →+* ℂ) → Finset ℕ} (h₁ : ProperLE Dw ty Z₂.ty)
    (h₂ : ProperLE Dw Z₂.ty ty) {k : Type} [Field k] {w₁ : Sp k ⟶ Z₁.X} {w₂ : Sp k ⟶ Z₂.X} :
    NatImg Z₁ (Z₂.withType ty h₁ h₂) w₁ w₂ ↔ NatImg Z₁ Z₂ w₁ w₂ :=
  ⟨fun ⟨τ, mu, u, a, b, c, d⟩ => ⟨τ, mu, u, a, b, c, (Z₂.flagAt_withType h₁ h₂).1 d⟩,
    fun ⟨τ, mu, u, a, b, c, d⟩ => ⟨τ, mu, u, a, b, c, (Z₂.flagAt_withType h₁ h₂).2 d⟩⟩

theorem natImg_withType_left {Z₁ Z₂ : Mdl Y i₀} {ty : (E →+* ℂ) → Finset ℕ} (h₁ : ProperLE Dw ty Z₁.ty)
    (h₂ : ProperLE Dw Z₁.ty ty) {k : Type} [Field k] {w₁ : Sp k ⟶ Z₁.X} {w₂ : Sp k ⟶ Z₂.X} :
    NatImg (Z₁.withType ty h₁ h₂) Z₂ w₁ w₂ ↔ NatImg Z₁ Z₂ w₁ w₂ :=
  ⟨fun ⟨τ, mu, u, a, b, c, d⟩ => ⟨τ, mu, u, a, b, (Z₁.flagAt_withType h₁ h₂).1 c, d⟩,
    fun ⟨τ, mu, u, a, b, c, d⟩ => ⟨τ, mu, u, a, b, (Z₁.flagAt_withType h₁ h₂).2 c, d⟩⟩

theorem isNatMap_withType_right {Z₁ Z₂ : Mdl Y i₀} {ty : (E →+* ℂ) → Finset ℕ} (h₁ : ProperLE Dw ty Z₂.ty)
    (h₂ : ProperLE Dw Z₂.ty ty) {f : Z₁.X ⟶ Z₂.X} : IsNatMap Z₁ (Z₂.withType ty h₁ h₂) f ↔ IsNatMap Z₁ Z₂ f :=
  ⟨fun h => ⟨⟨h.1.1, h.1.2.1, fun σ k hk a b => h.1.2.2 σ k (h₂ σ k hk a b) a b⟩,
      fun k _ w hw => (natImg_withType_right h₁ h₂).1 (h.2 k w hw)⟩,
    fun h => ⟨⟨h.1.1, h.1.2.1, fun σ k hk a b => h.1.2.2 σ k (h₁ σ k hk a b) a b⟩,
      fun k _ w hw => (natImg_withType_right h₁ h₂).2 (h.2 k w hw)⟩⟩

theorem isNatMap_withType_left {Z₁ Z₂ : Mdl Y i₀} {ty : (E →+* ℂ) → Finset ℕ} (h₁ : ProperLE Dw ty Z₁.ty)
    (h₂ : ProperLE Dw Z₁.ty ty) {f : Z₁.X ⟶ Z₂.X} : IsNatMap (Z₁.withType ty h₁ h₂) Z₂ f ↔ IsNatMap Z₁ Z₂ f :=
  ⟨fun h => ⟨⟨h.1.1, h.1.2.1, fun σ k hk a b => h₁ σ k (h.1.2.2 σ k hk a b) a b⟩,
      fun k _ w hw => (natImg_withType_left h₁ h₂).1 (h.2 k w hw)⟩,
    fun h => ⟨⟨h.1.1, h.1.2.1, fun σ k hk a b => h₂ σ k (h.1.2.2 σ k hk a b) a b⟩,
      fun k _ w hw => (natImg_withType_left h₁ h₂).2 (h.2 k w hw)⟩⟩

theorem isNatMap_id_withType (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {ty ty' : (E →+* ℂ) → Finset ℕ}
    (h₁ : ProperLE Dw ty Z.ty) (h₂ : ProperLE Dw Z.ty ty) (h₁' : ProperLE Dw ty' Z.ty) (h₂' : ProperLE Dw Z.ty ty') :
    IsNatMap (Z.withType ty h₁ h₂) (Z.withType ty' h₁' h₂') (𝟙 Z.X) :=
  (isNatMap_withType_left (Z₁ := Z) h₁ h₂).2 ((isNatMap_withType_right (Z₁ := Z) h₁' h₂').2 (Inhab.isMap_id hp hW Z).isNatMap)

example (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (σ σ' : E →+* ℂ) :
    IsNatMap (Z.addTop σ) (Z.addTop σ') (𝟙 Z.X) := isNatMap_id_withType hp hW Z _ _ _ _

example (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) : Nonempty (Bases Y i₀) := Inhab.nonempty_bases hp.ne_zero hW Y i₀

end GlobalTheory.LocM
