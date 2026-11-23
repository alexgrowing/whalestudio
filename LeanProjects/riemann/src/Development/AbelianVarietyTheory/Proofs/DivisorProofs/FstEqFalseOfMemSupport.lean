import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrViaNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsEigenBasis
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CovHt.Link.drVia_isometry_invariant

private theorem spMap_comp_ {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem spMap_id_ (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  show Spec.map (𝟙 (CommRingCat.of A)) = _
  exact Spec.map_id _

private theorem dualMap_id_ (A : Type) [CommRing A] : dualMap (RingHom.id A) = RingHom.id _ := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

section Field

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

private theorem spMap_symm_cancel (σ : C ≃+* C) {Y : Scheme.{0}} (y : Sp C ⟶ Y) :
    spMap σ.symm.toRingHom ≫ spMap σ.toRingHom ≫ y = y := by
  rw [← Category.assoc, ← spMap_comp_, RingEquiv.symm_toRingHom_comp_toRingHom, spMap_id_, Category.id_comp]

private theorem spMap_dualMap_symm_cancel (σ : C ≃+* C) {Y : Scheme.{0}} (y : Sp (DualNumber C) ⟶ Y) :
    spMap (dualMap σ.symm.toRingHom) ≫ spMap (dualMap σ.toRingHom) ≫ y = y := by
  rw [← Category.assoc, ← spMap_comp_, ← dualMap_comp, RingEquiv.symm_toRingHom_comp_toRingHom, dualMap_id_,
    spMap_id_, Category.id_comp]

private def restrO (σ : C ≃+* C) (hσ : ∀ z, ‖σ z‖ = ‖z‖) : ↥(intO C) ≃+* ↥(intO C) where
  toFun a := ⟨σ (a : C), show ‖σ (a : C)‖ ≤ 1 by rw [hσ]; exact a.2⟩
  invFun a := ⟨σ.symm (a : C), show ‖σ.symm (a : C)‖ ≤ 1 by rw [← hσ, RingEquiv.apply_symm_apply]; exact a.2⟩
  left_inv a := Subtype.ext (σ.symm_apply_apply (a : C))
  right_inv a := Subtype.ext (σ.apply_symm_apply (a : C))
  map_mul' a b := Subtype.ext (map_mul σ (a : C) (b : C))
  map_add' a b := Subtype.ext (map_add σ (a : C) (b : C))

private theorem subtype_comp_restrO (σ : C ≃+* C) (hσ : ∀ z, ‖σ z‖ = ‖z‖) :
    (intO C).subtype.comp (restrO σ hσ).toRingHom = σ.toRingHom.comp (intO C).subtype :=
  RingHom.ext fun _ => rfl

end Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

private theorem mem_lat_transport (σ : C ≃+* C) (hσ : ∀ z, ‖σ z‖ = ‖z‖) (p : ℕ) (x : Sp C ⟶ X)
    (v : Sp (DualNumber C) ⟶ t.G.left) (hv : v ∈ lat t p x false) :
    spMap (dualMap σ.toRingHom) ≫ v ∈ lat t p (spMap σ.toRingHom ≫ x) false := by
  have hx : ∀ xO : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO = x →
      spMap (intO C).subtype ≫ spMap (restrO σ hσ).toRingHom ≫ xO = spMap σ.toRingHom ≫ x := by
    intro xO hxO
    rw [← hxO, ← Category.assoc, ← Category.assoc, ← spMap_comp_, ← spMap_comp_, subtype_comp_restrO]
  have hd : ∀ vO : Sp (DualNumber ↥(intO C)) ⟶ t.G.left,
      spMap (dualMap (intO C).subtype) ≫ spMap (dualMap (restrO σ hσ).toRingHom) ≫ vO =
        spMap (dualMap σ.toRingHom) ≫ spMap (dualMap (intO C).subtype) ≫ vO := by
    intro vO
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp_, ← spMap_comp_, ← dualMap_comp, ← dualMap_comp,
      subtype_comp_restrO]
  obtain ⟨xO, hxO, vO, hvO, rfl⟩ := hv
  exact ⟨_, hx xO hxO, _, GlobalTheory.FactorDepth.isTanAtG_map t _ hvO, hd vO⟩

private theorem grNorm_transport (σ : C ≃+* C) (hσ : ∀ z, ‖σ z‖ = ‖z‖) (x : Sp C ⟶ X)
    (Λ Λ' : Set (Sp (DualNumber C) ⟶ t.G.left))
    (h1 : ∀ v ∈ Λ, spMap (dualMap σ.toRingHom) ≫ v ∈ Λ')
    (h2 : ∀ v ∈ Λ', spMap (dualMap σ.symm.toRingHom) ≫ v ∈ Λ) {m : ℕ}
    (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m) :
    grNorm t (spMap σ.toRingHom ≫ x) Λ' (fun j => spMap (dualMap σ.toRingHom) ≫ u j) i = grNorm t x Λ u i := by
  unfold grNorm
  congr 1
  ext r
  constructor
  · rintro ⟨cf, hi, hz, ⟨w, hw, hc⟩, rfl⟩
    have hc' := GlobalTheory.EigenReduction.isCombAtG_map t σ.symm.toRingHom hc
    simp only [spMap_symm_cancel, spMap_dualMap_symm_cancel] at hc'
    refine ⟨fun j => σ.symm (cf j), ?_, fun k hk => ?_, ⟨_, h2 w hw, hc'⟩, ?_⟩
    · simpa using hi
    · simp [hz k hk]
    · rw [← hσ (σ.symm (cf i)), RingEquiv.apply_symm_apply]
  · rintro ⟨cf, hi, hz, ⟨w, hw, hc⟩, rfl⟩
    refine ⟨fun j => σ (cf j), ?_, fun k hk => ?_, ⟨_, h1 w hw, GlobalTheory.EigenReduction.isCombAtG_map t σ.toRingHom hc⟩, ?_⟩
    · simpa using hi
    · simp [hz k hk]
    · simp only [hσ]

private theorem lnStep_transport {Dw : Datum H} (σ : C ≃+* C) (hσ : ∀ z, ‖σ z‖ = ‖z‖) (x : Sp C ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ)
    (s : ((E →+* ℂ) × ℕ) ⊕ ℕ) :
    lnStep t (spMap σ.toRingHom ≫ x) (fun τ i => spMap (dualMap σ.toRingHom) ≫ u τ i) p false s = lnStep t x u p false s := by
  have key : ∀ {m : ℕ} (w : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m),
      grNorm t (spMap σ.toRingHom ≫ x) (lat t p (spMap σ.toRingHom ≫ x) false)
        (fun j => spMap (dualMap σ.toRingHom) ≫ w j) i = grNorm t x (lat t p x false) w i := by
    intro m w i
    refine grNorm_transport t σ hσ x _ _ (fun v hv => mem_lat_transport t σ hσ p x v hv) (fun v hv => ?_) w i
    have hσ' : ∀ z, ‖σ.symm z‖ = ‖z‖ := fun z => by rw [← hσ, RingEquiv.apply_symm_apply]
    have := mem_lat_transport t σ.symm hσ' p _ v hv
    rwa [spMap_symm_cancel] at this
  rcases s with ⟨τ, k⟩ | k
  · simp only [lnStep]
    split_ifs <;> simp only [key]
  · simp only [lnStep]
    split_ifs
    · rw [key]
    · rfl

private theorem lnStep_transport_comp {Dw : Datum H} (σ : C ≃+* C) (hσ : ∀ z, ‖σ z‖ = ‖z‖) {R : Type} [CommRing R]
    (ψ : R →+* C) (x : Sp R ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ t.G.left)) (p : ℕ)
    (s : ((E →+* ℂ) × ℕ) ⊕ ℕ) :
    lnStep t (spMap (σ.toRingHom.comp ψ) ≫ x) (fun τ i => spMap (dualMap (σ.toRingHom.comp ψ)) ≫ u τ i) p false s =
      lnStep t (spMap ψ ≫ x) (fun τ i => spMap (dualMap ψ) ≫ u τ i) p false s := by
  rw [← lnStep_transport t σ hσ (spMap ψ ≫ x) (fun τ i => spMap (dualMap ψ) ≫ u τ i) p s]
  simp only [spMap_comp_, dualMap_comp, Category.assoc]

private theorem fst_eq_false_of_mem_support {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} (la : AllWt.Weight S.Dw)
    (a : Sym D.host.E) (ha : a ∈ (drSym la).support) (p : ℕ) : a.1 p = false := by
  classical
  rw [drSym] at ha
  obtain ⟨z, -, hz⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum ha)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hz)]

section Via

open GlobalTheory.Toroidal Formalism.L2.Geo

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

private def drViaAny (la : AllWt.Weight S.Dw) (p : ℕ) {K : Type} [Field K] (y : Sp K ⟶ (Φ.C k).Y.X)
    {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] (φ : K →+* L) (f : (Φ.C k).Y.Fn) : ℝ :=
  ‖φ (GlobalTheory.TrueGeo.valAt y (f * ((∏ z : Letter S.Dw, (((Φ.C k).gr_spec (below y)).choose_spec.choose_spec.choose z.1 z.2) ^
      expo S.Dw (drSym la) z : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn)))‖ *
    Real.exp ((drSym la).sum fun a n => (n : ℝ) * lnStep s.T.Z.t
      (spMap (φ.comp (Scheme.stalkClosedPointTo y).hom) ≫ stalkPt (Φ.C k).Y (below y) ≫ (Φ.C k).π ≫ genι s.T.Z)
      (fun τ i => spMap (dualMap (φ.comp (Scheme.stalkClosedPointTo y).hom)) ≫
        ((Φ.C k).gr_spec (below y)).choose_spec.choose.v τ i) p (a.1 p) a.2.2)

private theorem drVia_eq_drViaAny (la : AllWt.Weight S.Dw) (p : ℕ) [Fact p.Prime] {K : Type} [Field K]
    (y : Sp K ⟶ (Φ.C k).Y.X) (φ : K →+* ℂ_[p]) (f : (Φ.C k).Y.Fn) :
    drVia Φ k la p y φ f = drViaAny Φ k la p y φ f := rfl

private theorem drViaAny_isometry (la : AllWt.Weight S.Dw) (p : ℕ) {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
    (σ : L ≃+* L) (hσ : ∀ z, ‖σ z‖ = ‖z‖) (x : Sp L ⟶ (Φ.C k).Y.X) (f : (Φ.C k).Y.Fn) :
    drViaAny Φ k la p x σ.toRingHom f = drAt Φ k la p x f := by
  have h1 : ∀ z, ‖σ.toRingHom z‖ = ‖z‖ := hσ
  refine congrArg₂ (fun a b : ℝ => a * Real.exp b) (h1 _) (Finsupp.sum_congr fun a ha => ?_)
  rw [fst_eq_false_of_mem_support la a ha p]
  exact congrArg (fun r : ℝ => (drSym la a : ℝ) * r)
    (lnStep_transport_comp s.T.Z.t σ hσ (Scheme.stalkClosedPointTo x).hom
      (stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z)
      (((Φ.C k).gr_spec (below x)).choose_spec.choose.v) p a.2.2)

end Via

theorem _root_.GlobalTheory.T.drVia_isometry_invariant : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] ≃+* ℂ_[p]), (∀ z, ‖σ z‖ = ‖z‖) → ∀ (x : Sp ℂ_[p] ⟶ (Φ.C k).Y.X) (f : (Φ.C k).Y.Fn), drVia Φ k la p x σ.toRingHom f = drAt Φ k la p x f :=
  fun _ _ _ _ _ _ _ Φ k la p _ σ hσ x f =>
    (drVia_eq_drViaAny Φ k la p x σ.toRingHom f).trans (drViaAny_isometry Φ k la p σ hσ x f)

end GlobalTheory.CovHt.Link.drVia_isometry_invariant
