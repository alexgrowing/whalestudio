import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarOfInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VB GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.OrthFilt

namespace GlobalTheory.BaseIso

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}}

def Same (p : X ⟶ Sp k) (σ : k →+* ℂ) (p' : X ⟶ Sp k') (σ' : k' →+* ℂ) : Prop :=
  (∀ y : Sp ℂ ⟶ X, y ≫ p = spMap σ ↔ y ≫ p' = spMap σ') ∧
  ∀ (U : X.Opens) (D : ℕ) (x : Fin D → Γ(X, U)),
    (MvPolynomial.eval₂Hom (algX p U) x).Etale ↔ (MvPolynomial.eval₂Hom (algX p' U) x).Etale

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

instance isIso_spMap (φ : k ≃+* k') : IsIso (spMap φ.toRingHom) :=
  inferInstanceAs (IsIso (Spec.map φ.toCommRingCatIso.hom))

theorem etale_iff (φ : k ≃+* k') {A : Type} [CommRing A] (f : k' →+* A) {D : ℕ} (x : Fin D → A) :
    (MvPolynomial.eval₂Hom (f.comp φ.toRingHom) x).Etale ↔ (MvPolynomial.eval₂Hom f x).Etale := by
  have e : MvPolynomial.eval₂Hom (f.comp φ.toRingHom) x =
      (MvPolynomial.eval₂Hom f x).comp (MvPolynomial.mapEquiv (Fin D) φ).toRingHom :=
    MvPolynomial.ringHom_ext (fun a => by simp) fun a => by simp
  rw [e]
  exact RingHom.Etale.respectsIso.cancel_left_isIso (MvPolynomial.mapEquiv (Fin D) φ).toCommRingCatIso.hom
    (CommRingCat.ofHom (MvPolynomial.eval₂Hom f x))

theorem same (φ : k ≃+* k') {p : X ⟶ Sp k} {p' : X ⟶ Sp k'} (w : p' ≫ spMap φ.toRingHom = p) (σ : k →+* ℂ) :
    Same p σ p' (σ.comp φ.symm.toRingHom) := by
  refine ⟨fun y => ?_, fun U D x => ?_⟩
  · have e : spMap σ = spMap (σ.comp φ.symm.toRingHom) ≫ spMap φ.toRingHom := by
      rw [← spMap_comp]
      congr 1
      ext a
      simp
    rw [← w, e, ← Category.assoc, cancel_mono]
  · have e : algX p U = (algX p' U).comp φ.toRingHom := by
      have := TopForm.appLE_comp_algX (φ := 𝟙 X) ((Category.id_comp p).trans w.symm) (le_refl U)
      rw [← this]
      ext a
      have e₁ : (𝟙 X : X ⟶ X).appLE U U (le_refl U) = 𝟙 _ := (Category.id_comp _).trans (X.presheaf.map_id _)
      rw [e₁]
      rfl
    rw [e, etale_iff]

namespace Same

variable {p : X ⟶ Sp k} {σ : k →+* ℂ} {p' : X ⟶ Sp k'} {σ' : k' →+* ℂ} (S : Same p σ p' σ')

include S in

theorem symm : Same p' σ' p σ := ⟨fun y => (S.1 y).symm, fun U D x => (S.2 U D x).symm⟩

def pt : CxPts p σ ≃ₜ CxPts p' σ' where
  toFun y := ⟨y.1, (S.1 _).1 y.2⟩
  invFun y := ⟨y.1, (S.1 _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def chart {D : ℕ} (c : AlgChart p' σ' D) : AlgChart p σ D where
  e := S.pt.transOpenPartialHomeomorph c.e
  U := c.U
  affine := c.affine
  x := c.x
  etale := (S.2 _ _ _).2 c.etale
  source_subset y hy := c.source_subset (a := S.pt y) hy
  apply_eq y hy := c.apply_eq (S.pt y) hy
  holo := c.holo

theorem chart_surjective (D : ℕ) : Function.Surjective (S.chart (D := D)) := fun c => ⟨S.symm.chart c, rfl⟩

theorem cInfAt {f : CxPts p' σ' → ℝ} {y : CxPts p σ} (h : CInfAt f (S.pt y)) : CInfAt (fun z => f (S.pt z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  exact ⟨W, ι, inferInstance, g, F, O, h₁, h₂, h₃, h₄, S.pt.continuous.continuousAt.eventually h₅⟩

theorem vInfAt {f : CxPts p' σ' → ℂ} {y : CxPts p σ} (h : VInfAt f (S.pt y)) : VInfAt (fun z => f (S.pt z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  exact ⟨W, ι, inferInstance, g, F, O, h₁, h₂, h₃, h₄, S.pt.continuous.continuousAt.eventually h₅⟩

def wt {B : LB X} (ψ : Weight p' σ' B) : Weight p σ B :=
  ⟨ψ.isLB, fun i y => ψ.φ i (S.pt y), fun i j y => ψ.trans i j (S.pt y)⟩

def met {E : X.Modules} {r : ℕ} (h : Met p' σ' E r) : Met p σ E r :=
  ⟨h.isVB, fun c y => h.G c (S.pt y), fun c y => h.posDef c (S.pt y), fun c c' y => h.trans c c' (S.pt y)⟩

def measIso : Measure (CxPts p' σ') ≃o Measure (CxPts p σ) :=
  Equiv.toOrderIso ⟨Measure.map S.pt.symm, Measure.map S.pt,
    fun μ => S.pt.symm.toMeasurableEquiv.map_symm_map (μ := μ), fun μ => S.pt.symm.toMeasurableEquiv.map_map_symm (ν := μ)⟩
    (fun _ _ h => Measure.map_mono h S.pt.symm.measurable) (fun _ _ h => Measure.map_mono h S.pt.measurable)

variable {B : LB X} (ψ : Weight p' σ' B) (D : ℕ)

theorem chernPart_wt (ε : ℤˣ) : (S.wt ψ).chernPart D ε = (ψ.chernPart D ε).map S.pt.symm := by
  refine Eq.trans ?_ (S.measIso.map_iSup _).symm
  refine ((S.chart_surjective D).iSup_comp _).symm.trans (iSup_congr fun c => ?_)
  have h : AEMeasurable c.e.symm ((volume.restrict c.e.target).withDensity
      ((fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens ψ y)) ∘ c.e.symm)) :=
    (c.e.continuousOn_symm.aemeasurable c.e.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  exact (AEMeasurable.map_map_of_aemeasurable S.pt.symm.measurable.aemeasurable h).symm

theorem chernIntegrableOn_wt {T : Set (CxPts p σ)} {f : CxPts p σ → ℝ}
    (h : ψ.ChernIntegrableOn D (S.pt.symm ⁻¹' T) (f ∘ S.pt.symm)) : (S.wt ψ).ChernIntegrableOn D T f := by
  unfold Weight.ChernIntegrableOn
  rw [chernPart_wt, chernPart_wt]
  exact ⟨(integrableOn_map_equiv S.pt.symm.toMeasurableEquiv).2 h.1,
    (integrableOn_map_equiv S.pt.symm.toMeasurableEquiv).2 h.2⟩

theorem chernInt_wt (T : Set (CxPts p σ)) (f : CxPts p σ → ℝ) :
    (S.wt ψ).chernInt D T f = ψ.chernInt D (S.pt.symm ⁻¹' T) (f ∘ S.pt.symm) := by
  unfold Weight.chernInt
  rw [chernPart_wt, chernPart_wt]
  exact congrArg₂ (· - ·) (setIntegral_map_equiv S.pt.symm.toMeasurableEquiv _ _)
    (setIntegral_map_equiv S.pt.symm.toMeasurableEquiv _ _)

end Same

section Global

variable (φ : k ≃+* k') {p : X ⟶ Sp k} {p' : X ⟶ Sp k'} (w : p' ≫ spMap φ.toRingHom = p)

def embEquiv : (k →+* ℂ) ≃ (k' →+* ℂ) where
  toFun σ := σ.comp φ.symm.toRingHom
  invFun σ := σ.comp φ.toRingHom
  left_inv σ := by ext a; simp
  right_inv σ := by ext a; simp

def lb (L : HermLB p') : HermLB p where
  B := L.B
  isLB := L.isLB
  φ σ := (same φ w σ).wt (L.φ _)
  cInf σ i y hy := (same φ w σ).cInfAt (L.cInf _ i ((same φ w σ).pt y) hy)
  conj σ σ' i y y' h hy := L.conj _ _ i ((same φ w σ).pt y) ((same φ w σ').pt y') h hy

def vm {E : X.Modules} {r : ℕ} (h : VMetric p' E r) : VMetric p E r where
  isVB := h.isVB
  met σ := (same φ w σ).met (h.met _)
  conj σ σ' c y y' e := h.conj _ _ c ((same φ w σ).pt y) ((same φ w σ').pt y') e

theorem isCInf_vm {E : X.Modules} {r : ℕ} {h : VMetric p' E r} (H : h.IsCInf) : (vm φ w h).IsCInf :=
  fun σ c y hy a b => (same φ w σ).vInfAt (H _ c ((same φ w σ).pt y) hy a b)

theorem lb_comb {ι : Type} [Fintype ι] (L : ι → HermLB p') (n : ι → ℤ) :
    comb (fun i => lb φ w (L i)) n = lb φ w (comb L n) := by
  unfold comb
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    rfl

section Sub

variable [IsIntegral X] (L M : HermLB p') {r : M.B.ι → X.functionFieldˣ} (hr : IsRatSec M.B r)

theorem archIntegrable_lb {e : ℕ} (h : L.ArchIntegrable M e hr) : (lb φ w L).ArchIntegrable (lb φ w M) e hr :=
  fun σ => (same φ w σ).chernIntegrableOn_wt _ _ (h _)

theorem archInt_lb (e : ℕ) : (lb φ w L).archInt (lb φ w M) e hr = L.archInt M e hr :=
  (finsum_congr fun σ => (same φ w σ).chernInt_wt _ _ _ _).trans (finsum_comp_equiv (embEquiv φ)
    (f := fun σ => (L.φ σ).chernInt e (offSupp p' σ (M.div hr)) (logNorm (M.φ σ) r)))

theorem curveDeg_lb [IsLocallyNoetherian X] : (lb φ w M).curveDeg hr = M.curveDeg hr :=
  congrArg (_ - ·) ((finsum_congr fun σ => finsum_comp_equiv (same φ w σ).pt.toEquiv
    (f := fun y => logNorm (M.φ _) r y)).trans (finsum_comp_equiv (embEquiv φ)
      (f := fun σ => ∑ᶠ y : CxPts p' σ, logNorm (M.φ σ) r y)))

end Sub

include w in

theorem comp_base (i : Y ⟶ X) : (i ≫ p') ≫ spMap φ.toRingHom = i ≫ p := by rw [Category.assoc, w]

theorem isArithHeight_lb {L : HermLB p'} {h : X → ℝ} (H : L.IsArithHeight h) : (lb φ w L).IsArithHeight h where
  vertical := H.vertical
  point Z i _ _ _ hc hd r hr := (H.point Z i hc hd r hr).trans (curveDeg_lb φ (comp_base φ w i) (L.restr i) hr).symm
  recursion Z i _ _ _ hc e he hd m r hr :=
    have h₀ := H.recursion Z i hc e he hd m r hr
    ⟨archIntegrable_lb φ (comp_base φ w i) (L.restr i) ((L.restr i).pow m) hr h₀.1,
      h₀.2.trans (congrArg (_ - ·) (archInt_lb φ (comp_base φ w i) (L.restr i) ((L.restr i).pow m) hr e).symm)⟩

include w in

theorem isArithVar {d : ℕ} (h : IsArithVar p' d) : IsArithVar p d := by
  have := h.isDomain
  have := h.finite
  refine AlterationOrder.isArithVar_of_int φ.toMulEquiv.isDomain
    (Module.Finite.equiv φ.symm.toAddEquiv.toIntLinearEquiv) ?_
  rw [AlterationOrder.hom_ext_int (p ≫ _) (p' ≫ spMap (Int.castRingHom k'))]
  exact AlterationOrder.isArithVar_int h

theorem fam_vm {E : X.Modules} {r : ℕ} {h : VMetric p' E r} (H : h.IsCInf) (F : FlagSp E r) :
    F.fam (isCInf_vm φ w H) (VMetric.det (isCInf_vm φ w H)) =
      fun o => lb φ (comp_base φ w F.π) (F.fam H (VMetric.det H) o) := by
  funext o
  cases o with
  | none => rfl
  | some i => rfl

end Global

theorem exists_sameMet (k k' : Type) [CommRing k] [CommRing k'] (φ : k ≃+* k') (X : Scheme.{0}) (p : X ⟶ Sp k') (d : ℕ)
    (hp : IsArithVar p d) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) :
    IsArithVar (p ≫ spMap φ.toRingHom) d ∧ ∃ (h₀ : VMetric (p ≫ spMap φ.toRingHom) E r) (H₀ : h₀.IsCInf),
      SameMet φ h h₀ ∧ ∀ (F : FlagSp E r) (z : X) (e : ℕ) (a : ℝ),
        F.IsVal H (VMetric.det H) z e a → F.IsVal H₀ (VMetric.det H₀) z e a := by
  refine ⟨isArithVar φ rfl hp, vm φ rfl h, isCInf_vm φ rfl H, fun σ y₀ y e c _ => ?_, ?_⟩
  · obtain rfl : y = (same φ rfl σ).pt y₀ := Subtype.ext e
    rfl
  · rintro F z e a ⟨y, Φ, h₁, h₂, h₃⟩
    refine ⟨y, Φ, h₁, ⟨fun n => ?_, h₂.2⟩, h₃⟩
    obtain ⟨g, hg, e⟩ := h₂.1 n
    rw [fam_vm φ rfl H, lb_comb]
    exact ⟨g, isArithHeight_lb φ _ hg, e⟩

end GlobalTheory.BaseIso

end
