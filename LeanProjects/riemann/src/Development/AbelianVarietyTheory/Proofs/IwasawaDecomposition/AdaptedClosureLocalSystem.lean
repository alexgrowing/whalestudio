import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp
  tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.StepLift

theorem initSpan_map {K N N' : Type} [CommRing K] [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] {m : ℕ}
    (L : N →ₗ[K] N') (v : Fin m → N) (j : ℕ) : initSpan K (fun i => L (v i)) j = (initSpan K v j).map L := by
  rw [initSpan, initSpan, Submodule.map_span, Set.image_image]

theorem initSpan_of_le {K N : Type} [CommRing K] [AddCommGroup N] [Module K N] {m : ℕ}
    (v : Fin m → N) {j : ℕ} (hj : m ≤ j) : initSpan K v j = Submodule.span K (Set.range v) := by
  rw [initSpan, ← Set.image_univ]
  congr 2
  exact Set.eq_univ_of_forall fun i => i.2.trans_le hj

theorem exists_isUnit_repr {R N : Type} [CommRing R] [IsLocalRing R] [AddCommGroup N] [Module R N] {k m : ℕ} {κ : Type}
    (b : Module.Basis (Fin k ⊕ Fin m) R N) (c : Module.Basis κ R N) (q : κ)
    (h : ∀ i, c.repr (b (.inl i)) q = 0) : ∃ j, IsUnit (b.repr (c q) (.inr j)) := by
  by_contra! hn
  have h1 : c.repr (c q) q ∈ IsLocalRing.maximalIdeal R := by
    rw [← b.sum_repr (c q), map_sum, Finsupp.finset_sum_apply]
    refine Ideal.sum_mem _ fun x _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rcases x with i | j
    · rw [h i, mul_zero]; exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _ (hn j)
  rw [c.repr_self, Finsupp.single_eq_same] at h1
  exact h1 isUnit_one

theorem repr_eq_zero_of_mem {K N : Type} [CommRing K] [AddCommGroup N] [Module K N] {κ : Type} {d : ℕ}
    (c : Module.Basis κ K N) (e : Fin d ↪ κ) {k : ℕ} (hk : k < d) {v : N}
    (hv : v ∈ initSpan K (fun j => c (e j)) k) : c.repr v (e ⟨k, hk⟩) = 0 := by
  have : initSpan K (fun j => c (e j)) k ≤ LinearMap.ker (c.coord (e ⟨k, hk⟩)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hne : e j ≠ e ⟨k, hk⟩ := fun h => by
      obtain rfl := e.injective h
      exact lt_irrefl k hj
    simp [Finsupp.single_eq_of_ne hne.symm]
  exact this hv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem flagAt_of_initSpan_eq {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
    {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty}
    {K : Type} [Field K] {w : Sp K ⟶ X} {x : Sp K ⟶ M.X} (hx : w ≫ π = x) {u u' : TVecs Dw M.t x}
    (h : A.FlagAt w (up u)) (hli : ∀ σ, LinearIndependent K (u' σ))
    (hs : ∀ σ j, initSpan K (u' σ) j = initSpan K (u σ) j) : A.FlagAt w (up u') := by
  subst hx
  obtain ⟨a, φ, e, -⟩ := id h
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  obtain ⟨hf, hs'⟩ := (A.flagAt_iff e h₀ u).1 h
  refine (A.flagAt_iff e h₀ u').2 ⟨(isFrame_up_iff _ _).2 fun σ => ⟨hli σ, ?_⟩, fun σ j hj => (hs σ j).trans (hs' σ j hj)⟩
  rw [← initSpan_of_le _ le_rfl, hs, initSpan_of_le _ le_rfl]
  exact ((isFrame_up_iff _ _).1 hf σ).2

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_int_frame {Z : Mdl Y i₀} (hZ : HasDR Z) {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (φ : R →+* K)
    (z : Sp R ⟶ Z.X) {w : Sp K ⟶ Z.X} (e : spMap φ ≫ z = w) (e' : spMap φ ≫ z ≫ Z.π = w ≫ Z.π)
    (hw : Set.range w ⊆ Z.opn) {u : TVecs Dw (Y Z.i).t (w ≫ Z.π)} (hu : Z.FlagAt w (up u)) :
    ∃ T : TVecs Dw (Y Z.i).t (z ≫ Z.π),
      (∀ σ, ∃ (n : ℕ) (c : Module.Basis (Fin n) R (TanM (z ≫ Z.π) (Y Z.i).t.G)) (q : Fin (Dw.mult σ) ↪ Fin n),
        ∀ j, c (q j) = T σ j) ∧
      ∀ σ j, initSpan K (fun i => tanPull φ e' (T σ i)) j = initSpan K (u σ) j := by
  obtain ⟨U, hU, fr, hx, h1, h2⟩ := hZ.2 (z (IsLocalRing.closedPoint R))
  have hz : ⊤ ≤ z ⁻¹ᵁ U := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ U)).1 hx).ge
  have ht : ∀ σ j, IsTanAtG (Y Z.i).t (tau hU ≫ Z.π) (fr σ j) := fun σ j => by
    obtain ⟨n, v, q, hq, hv, -⟩ := h1 σ
    rw [← hq]; exact hv _
  have ez : spMap (ev z U hz) ≫ tau hU ≫ Z.π = z ≫ Z.π := by rw [← Category.assoc, tau, spMap_ev]
  refine ⟨fun σ j => tanPull (ev z U hz) ez (tanOf (ht σ j)), fun σ => ?_, fun σ j => ?_⟩
  · obtain ⟨n, v, q, hq, hv, hb⟩ := h1 σ
    have h3 : ∀ s : TanM (tau hU ≫ Z.π) (Y Z.i).t.G, ∃! a : Fin n → Γ(Z.X, U), s = ∑ i, a i • tanOf (x := tau hU ≫ Z.π) (hv i) :=
      fun s => (existsUnique_congr fun a => isComb_iff (fun i => tanOf (x := tau hU ≫ Z.π) (hv i)) a s).1 (hb _ (isTan_tv s))
    let b : Module.Basis (Fin n) Γ(Z.X, U) (TanM (tau hU ≫ Z.π) (Y Z.i).t.G) :=
      Module.Basis.mk (v := fun i => tanOf (x := tau hU ≫ Z.π) (hv i)) (Fintype.linearIndependent_iff.2 fun a ha => congrFun
        ((h3 0).unique ha.symm (by simp : (0 : TanM (tau hU ≫ Z.π) (Y Z.i).t.G) =
          ∑ i, (0 : Fin n → Γ(Z.X, U)) i • tanOf (x := tau hU ≫ Z.π) (hv i)))) fun s _ => by
        obtain ⟨a, rfl, -⟩ := h3 s
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨n, basPull _ ez b, q, fun j => ?_⟩
    rw [basPull_apply, Module.Basis.mk_apply]
    exact congrArg _ (tan_ext (hq j))
  · have ew : spMap (φ.comp (ev z U hz)) ≫ hU.fromSpec = w := by
      rw [← spMap_comp', Category.assoc, spMap_ev, e]
    have h4 := h2 K (φ.comp (ev z U hz)) (ew ▸ hw)
    rw [ew, ← Vecs.bc_bc] at h4
    let T : TVecs Dw (Y Z.i).t (w ≫ Z.π) := fun σ i => tanPull φ e' (tanPull (ev z U hz) ez (tanOf (ht σ i)))
    have h6 : up T = (fr.bc (ev z U hz)).bc φ := rfl
    rw [← h6, ← atlasOf_flagAt] at h4
    have h5 : ∀ j ∈ Z.ty σ, initSpan K (T σ) j = initSpan K (u σ) j := fun j hj =>
      Atlas.FlagAt.initSpan_eq h4 ((atlasOf_flagAt Z w _).2 hu) σ hj
    show initSpan K (T σ) j = _
    rw [hZ.1] at h5
    rcases le_total j (Dw.mult σ) with hj | hj
    · exact h5 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    · rw [initSpan_of_le _ hj, initSpan_of_le _ hj, ← initSpan_of_le _ le_rfl, ← initSpan_of_le _ le_rfl]
      exact h5 _ (Finset.mem_range.2 (Nat.lt_succ_self _))

theorem locMaps_closure {i : Idx H p} {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ}
    {A : Atlas (Y i) π ty} {σ : E →+* ℂ} {k r : ℕ} (D : Adapted A σ k) (hk : k < Dw.mult σ) {Sb : D.C.Sub A.ch r}
    (Cl : Sb.Closure (π ≫ (Y i).s)) {ty' : (E →+* ℂ) → Finset ℕ} {A' : Atlas (Y i) (Cl.f ≫ π) ty'} {Z : Mdl Y i₀}
    {g : Z.X ⟶ X} (hS : StepRel D hk Cl.L A') (hZ : HasDR Z) (hg : MapsTo Z A g) : LocMaps Z A' := by
  intro K _ w hw
  obtain ⟨τ, mu, u, htr, hwτ, hu, hA⟩ := hg K w hw
  obtain ⟨u, rfl⟩ := Atlas.FlagAt.exists_up (A := atlasOf Z) hu
  obtain ⟨y, hy, hA'⟩ := hA.exists_point A'
  have e₁ : (w ≫ Z.π) ≫ τ = (y ≫ Cl.f) ≫ π := by rw [Category.assoc, ← hwτ, ← hy, Category.assoc]
  let u₁ : TVecs Dw (Y i).t ((y ≫ Cl.f) ≫ π) := fun σ j => pushE mu _ e₁ (u σ j)
  have hA₁ : A'.FlagAt y (up u₁) := hA'
  have hyf : y ≫ Cl.f = w ≫ g :=
    Atlas.FlagAt.point_eq ((hS K y u₁).1 hA₁).1 hA (by rw [← hy, Category.assoc])
  refine ⟨y, ⟨τ, mu, _, htr, hy.trans hwτ, hu, hA'⟩, fun R _ _ _ _ _ _ z ez => ?_⟩
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have e₂ : (z ≫ Z.π) ≫ τ = (z ≫ g) ≫ π := by
    have := projProper _ _ _ (Y i).proj
    have : (Y i).X.IsSeparated := ⟨by
      rw [← terminal.comp_from (Y i).s]
      infer_instance⟩
    have : IsDominant (spMap (algebraMap R K)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
    refine ext_of_isDominant (spMap (algebraMap R K)) ?_
    simp only [Category.assoc] at hwτ ⊢
    rw [reassoc_of% ez, reassoc_of% ez, hwτ]
  have e₃ : spMap (algebraMap R K) ≫ z ≫ Z.π = w ≫ Z.π := by rw [reassoc_of% ez]
  have e₄ : spMap (algebraMap R K) ≫ z ≫ g = y ≫ Cl.f := by rw [reassoc_of% ez, hyf]
  have e₅ : spMap (algebraMap R K) ≫ (z ≫ g) ≫ π = (y ≫ Cl.f) ≫ π := by rw [← Category.assoc, e₄]
  obtain ⟨T, hT, hs⟩ := exists_int_frame hZ (algebraMap R K) z ez e₃ hw hu
  let T₁ : TVecs Dw (Y i).t ((z ≫ g) ≫ π) := fun σ j => pushE mu _ e₂ (T σ j)
  let T₂ : TVecs Dw (Y i).t ((y ≫ Cl.f) ≫ π) := fun σ j => tanPull (algebraMap R K) e₅ (T₁ σ j)
  have hT₁ : ∀ σ, ∃ (n : ℕ) (c : Module.Basis (Fin n) R (TanM ((z ≫ g) ≫ π) (Y i).t.G)) (q : Fin (Dw.mult σ) ↪ Fin n),
      (∀ j, c (q j) = T₁ σ j) ∧ T₂ σ = fun j => basPull (algebraMap R K) e₅ c (q j) := fun σ => by
    obtain ⟨n, c, q, hq⟩ := hT σ
    have : ∀ j, c.map (pushE mu _ e₂) (q j) = T₁ σ j := fun j => by rw [Module.Basis.map_apply, hq]
    exact ⟨n, _, q, this, funext fun j => by rw [basPull_apply, this]⟩
  have hA₂ : A'.FlagAt y (up T₂) := by
    refine flagAt_of_initSpan_eq (Category.assoc _ _ _).symm hA₁ (fun σ => ?_) fun σ j => ?_
    · obtain ⟨n, c, q, -, h⟩ := hT₁ σ
      rw [h]
      exact (basPull _ e₅ c).linearIndependent.comp _ q.injective
    · have : T₂ σ = fun j => (pushE mu _ e₁).toLinearMap (tanPull (algebraMap R K) e₃ (T σ j)) :=
        funext fun j => tan_ext (Category.assoc _ _ _).symm
      rw [this, initSpan_map, hs]
      exact (initSpan_map (pushE mu _ e₁).toLinearMap _ _).symm
  obtain ⟨hA₃, hc⟩ := (hS K y T₂).1 hA₂
  obtain ⟨α, hα⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing (U := D.C.B)
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (D.C.cover x)) (z ≫ g)
  have hα' : ⊤ ≤ (y ≫ Cl.f) ⁻¹ᵁ D.C.B α := e₄ ▸ le_preimage_comp _ hα
  refine Cl.lift R K (z ≫ g) α hα (crd (D.b α) (z ≫ g) hα (T₁ σ ⟨k, hk⟩)) ?_ y e₄.symm fun h => ?_
  · obtain ⟨n, c, q, hq, h⟩ := hT₁ σ
    rw [← hq]
    refine exists_isUnit_repr _ c _ fun j => hinj ?_
    rw [← basPull_repr _ e₅, map_zero, tanPull_basAt _ _ _ _ e₄ hα']
    refine repr_eq_zero_of_mem _ q hk ?_
    rw [← h, D.int α K _ hα' T₂ hA₃ k le_rfl]
    exact Submodule.subset_span ⟨j, j.2, rfl⟩
  · have := hc α h
    convert this using 1
    exact funext fun j => (basAt_repr _ _ _ hα e₄ h e₅ _ _).symm

end GlobalTheory.DRFlag.StepLift

theorem GlobalTheory.DRFlag.locMaps_closure_of_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ (Y i).s)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y i) (Cl.f ≫ π) ty') (Z : Mdl Y i₀) (g : Z.X ⟶ X), StepRel D hk Cl.L A' → HasDR Z → MapsTo Z A g → LocMaps Z A' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D hk _ Cl _ _ _ _ => GlobalTheory.DRFlag.StepLift.locMaps_closure D hk Cl
