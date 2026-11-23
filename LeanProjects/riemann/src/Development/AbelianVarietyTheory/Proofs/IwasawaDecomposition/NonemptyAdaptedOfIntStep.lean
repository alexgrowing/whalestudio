import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.AdaptedOfStep

theorem eq_zero_of_dense {X : Scheme.{0}} [IsReduced X] {D : Set X} (hD : Dense D) {U : X.Opens} (f : Γ(X, U))
    (h : ∀ (K : Type) [Field K] (w : Sp K ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ U), w (IsLocalRing.closedPoint K) ∈ D →
      ev w U hw f = 0) : f = 0 := by
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen f).isOpen
    (((X.basicOpen f).ne_bot_iff_nonempty).1 hne)
  let w : Sp (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hr : ∀ p, w p = x := fun p => Scheme.fromSpecResidueField_apply x p
  have hb : ⊤ ≤ w ⁻¹ᵁ X.basicOpen f := fun p _ => show w p ∈ X.basicOpen f by rw [hr]; exact hx
  have hw : ⊤ ≤ w ⁻¹ᵁ U := le_preimage_mono (X.basicOpen_le f) hb
  have h0 := h _ w hw ((hr _).symm ▸ hxD)
  have hu : IsUnit (resG X (X.basicOpen_le f) f) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace f
  have := hu.map (ev w _ hb)
  rw [ev_res w _ hb hw, h0] at this
  exact not_isUnit_zero this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

theorem isAffineOpen_inf (g : Geo M π) {U U' : X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') :
    IsAffineOpen (U ⊓ U') := by
  have := projProper _ _ _ g.proj
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from (π ≫ M.s)]
    infer_instance⟩
  exact hU.inf hU'

variable {U U' : X.Opens} {hU : IsAffineOpen U} {hU' : IsAffineOpen U'} {m m' : ℕ}
  {b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)}
  {b' : Module.Basis (Fin k ⊕ Fin m') Γ(X, U') (TanM (tau hU' ≫ π) M.t.G)}

theorem crd_basAt {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (w : Sp S ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ U)
    (hw' : ⊤ ≤ w ⁻¹ᵁ U') {z : Sp S' ⟶ X} (e : spMap φ ≫ w = z) (hz : ⊤ ≤ z ⁻¹ᵁ U) (hz' : ⊤ ≤ z ⁻¹ᵁ U')
    (i : Fin k ⊕ Fin m') (j : Fin m) :
    crd b z hz (basAt b' z hz' i) j = φ (crd b w hw (basAt b' w hw' i) j) := by
  have e' : spMap φ ≫ w ≫ π = z ≫ π := by rw [← e, Category.assoc]
  rw [← tanPull_basAt b' φ w hw' e hz' e']
  exact basAt_repr b φ w hw e hz e' _ _

theorem crd_inl_field (hb : IntOn A σ k hU b) (hb' : IntOn A σ k hU' b') (K : Type) [Field K] (w : Sp K ⟶ X)
    (hw : ⊤ ≤ w ⁻¹ᵁ U) (hw' : ⊤ ≤ w ⁻¹ᵁ U') (hD : w (IsLocalRing.closedPoint K) ∈ π ⁻¹' Set.range M.j)
    (i : Fin k) (j : Fin m) : crd b w hw (basAt b' w hw' (.inl i)) j = 0 := by
  rw [← A.cover] at hD
  obtain ⟨a, φ, e⟩ := A.ch.exists_fac w hD
  obtain ⟨u, hu⟩ := A.exists_up_fr e
  have hf : A.FlagAt w (up u) := hu ▸ A.flagAt_fr e
  have h1 : basAt b' w hw' (.inl i) ∈ initSpan K (fun i : Fin k => basAt b' w hw' (.inl i)) k :=
    Submodule.subset_span ⟨i, i.2, rfl⟩
  rw [← hb' K w hw' u hf k le_rfl, hb K w hw u hf k le_rfl] at h1
  obtain ⟨cf, -, h2⟩ := mem_initSpan.1 h1
  rw [← h2]
  simp [crd]

theorem crd_inl (g : Geo M π) (hb : IntOn A σ k hU b) (hb' : IntOn A σ k hU' b') {S : Type} [CommRing S]
    (z : Sp S ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ U) (hz' : ⊤ ≤ z ⁻¹ᵁ U') (i : Fin k) (j : Fin m) :
    crd b z hz (basAt b' z hz' (.inl i)) j = 0 := by
  have hI := isAffineOpen_inf g hU hU'
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => have := (g.normal x).1; inferInstance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have h0 : crd b (tau hI) (tau_le hI inf_le_left) (basAt b' (tau hI) (tau_le hI inf_le_right) (.inl i)) j = 0 :=
    eq_zero_of_dense g.dense _ fun K _ w hw hD =>
      (crd_basAt _ (tau hI) _ _ (spMap_ev w hI hw) (le_preimage_mono inf_le_left hw)
        (le_preimage_mono inf_le_right hw) _ _).symm.trans (crd_inl_field hb hb' K w _ _ hD i j)
  rw [crd_basAt _ (tau hI) (tau_le hI inf_le_left) (tau_le hI inf_le_right)
    (spMap_ev z hI (le_preimage_inf hz hz')), h0, map_zero]

variable (b b') in

def trans (g : Geo M π) : Matrix (Fin m) (Fin m') Γ(X, U ⊓ U') := fun j i =>
  crd b (tau (isAffineOpen_inf g hU hU')) (tau_le _ inf_le_left)
    (basAt b' (tau (isAffineOpen_inf g hU hU')) (tau_le _ inf_le_right) (.inr i)) j

theorem trans_map (g : Geo M π) {S : Type} [CommRing S] (z : Sp S ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ U) (hz' : ⊤ ≤ z ⁻¹ᵁ U')
    (j : Fin m) (i : Fin m') : (trans b b' g).map (ev z _ (le_preimage_inf hz hz')) j i =
      crd b z hz (basAt b' z hz' (.inr i)) j :=
  (crd_basAt _ (tau (isAffineOpen_inf g hU hU')) _ _ (spMap_ev z _ (le_preimage_inf hz hz')) hz hz' _ _).symm

theorem trans_mulVec (g : Geo M π) (hb : IntOn A σ k hU b) (hb' : IntOn A σ k hU' b') {S : Type} [CommRing S]
    (z : Sp S ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ U) (hz' : ⊤ ≤ z ⁻¹ᵁ U') (v : TanM (z ≫ π) M.t.G) :
    ((trans b b' g).map (ev z _ (le_preimage_inf hz hz'))).mulVec (crd b' z hz' v) = crd b z hz v := by
  funext j
  have h0 := fun i => crd_inl g hb hb' z hz hz' i j
  conv_rhs => rw [← (basAt b' z hz').sum_repr v]
  simp only [Matrix.mulVec, dotProduct, trans_map g z hz hz']
  simp only [crd] at h0 ⊢
  rw [Fintype.sum_sum_type]
  simp only [map_add, map_sum, map_smul, Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    h0, mul_zero, Finset.sum_const_zero, zero_add]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem nonempty_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ), Geo M π → IntStep A σ k → Nonempty (Adapted A σ k) := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ k g h
  choose U hU m b hx hb using h
  refine ⟨⟨⟨X, U, hU, fun x => ⟨x, hx x⟩, m, fun α β => trans (b α) (b β) g, fun α S _ z hz => ?_,
    fun α β γ S _ z h₁ h₂ h₃ => ?_⟩, b, hb, fun α β S _ z h₁ h₂ v => trans_mulVec g (hb α) (hb β) z h₁ h₂ v⟩⟩
  · ext j i
    rw [trans_map g z hz hz]
    simp [crd, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  · ext j i
    rw [trans_map g z h₁ h₃, ← trans_mulVec g (hb α) (hb β) z h₁ h₂, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun q _ => by rw [trans_map g z h₂ h₃]

end GlobalTheory.DRFlag.AdaptedOfStep
