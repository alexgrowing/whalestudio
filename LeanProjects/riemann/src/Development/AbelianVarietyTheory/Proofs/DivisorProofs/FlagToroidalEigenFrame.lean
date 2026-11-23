import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsLowInv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

theorem germ_stalkClosedPointTo_appLE' {Y : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y)
    (U : Y.Opens) (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]

theorem appLE_ι_topIso_hom {Y Z : Scheme.{0}} (U : Y.Opens) (g : Z ⟶ U) (h : ⊤ ≤ (g ≫ U.ι) ⁻¹ᵁ U) (a : Γ(U, ⊤)) :
    ((g ≫ U.ι).appLE U ⊤ h).hom (U.topIso.hom.hom a) = g.appTop.hom a := by
  have e : U.topIso.hom ≫ (g ≫ U.ι).appLE U ⊤ h = g.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ (by simp) le_top, ← Category.assoc]
    have : U.topIso.hom ≫ U.ι.appLE U ⊤ (by simp) = 𝟙 _ := by
      simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appLE]
      exact (Y.presheaf.map_comp _ _).symm.trans (Y.presheaf.map_id _)
    rw [this, Category.id_comp, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  exact congrArg (fun q => q.hom a) e

theorem appTop_topIso_inv {X : Scheme.{0}} {W : X.Opens} {K : Type} [CommRing K] [IsLocalRing K]
    (p : Spec (.of K) ⟶ W.toScheme) (s : Γ(X, W)) (hy : (p ≫ W.ι) (IsLocalRing.closedPoint K) ∈ W) :
    (Scheme.ΓSpecIso (.of K)).hom (p.appTop (W.topIso.inv s)) =
      (Scheme.stalkClosedPointTo (R := .of K) (p ≫ W.ι)).hom (X.presheaf.germ W _ hy s) := by
  have e1 := appLE_ι_topIso_hom W p (Scheme.preimage_eq_top_of_closedPoint_mem (p ≫ W.ι) hy).ge (W.topIso.inv s)
  have e2 := congrArg (fun φ => φ.hom s) (germ_stalkClosedPointTo_appLE' (R := CommRingCat.of K) (p ≫ W.ι) W hy)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  congr 1
  refine e1.symm.trans ?_
  congr 1
  exact congrArg (fun φ => φ.hom s) W.topIso.inv_hom_id

section Mat

variable {R S : Type} [CommRing R] [CommRing S] {m : ℕ}

theorem exists_low_of_inCell {K : Type} [Field K] {M M' : Matrix (Fin m) (Fin m) K} {w : Equiv.Perm (Fin m)}
    {a : Above m → K} (h : InCell M w a) (h' : InCell M' w a) :
    ∃ T : Matrix (Fin m) (Fin m) K, (∀ i j, i < j → T i j = 0) ∧ (∀ i, T i i ≠ 0) ∧ M = T * M' := by
  obtain ⟨L, hL, e⟩ := h
  obtain ⟨L', hL', e'⟩ := h'
  have hb : L.BlockTriangular OrderDual.toDual := fun i j hij => hL.1 i j (OrderDual.toDual_lt_toDual.1 hij)
  have hb' : L'.BlockTriangular OrderDual.toDual := fun i j hij => hL'.1 i j (OrderDual.toDual_lt_toDual.1 hij)
  have hd' : L'.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular L' hb']
    exact Finset.prod_ne_zero_iff.2 fun i _ => (hL'.2 i).ne_zero
  have hd : L.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular L hb]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (hL.2 i).ne_zero
  letI := Matrix.invertibleOfIsUnitDet L' (isUnit_iff_ne_zero.2 hd')
  have hbT : (L * L'⁻¹).BlockTriangular OrderDual.toDual :=
    hb.mul (Matrix.blockTriangular_inv_of_blockTriangular hb')
  refine ⟨L * L'⁻¹, fun i j hij => hbT (OrderDual.toDual_lt_toDual.2 hij), fun i => ?_, ?_⟩
  · have hdT : (L * L'⁻¹).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero hd (inv_ne_zero hd')
    rw [Matrix.det_of_lowerTriangular _ hbT] at hdT
    exact Finset.prod_ne_zero_iff.1 hdT i (Finset.mem_univ i)
  · have hs : M.submatrix id w = (L * L'⁻¹ * M').submatrix id w := by
      rw [e, show (L * L'⁻¹ * M').submatrix id w = L * L'⁻¹ * M'.submatrix id w from rfl, e', Matrix.mul_assoc,
        ← Matrix.mul_assoc L'⁻¹, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd'), Matrix.one_mul]
    have := congrArg (fun N => N.submatrix id w.symm) hs
    simpa using this

end Mat

section Tri

open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem tri_of_comb {R K : Type} [CommRing R] [CommRing K] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f : EigFrame Z φ x) (ψ : R →+* K) {φ' : c.F →+* K} {x' : Sp K ⟶ Z.X} (hφ : ψ.comp φ = φ')
    (hx : spMap ψ ≫ x = x') (h : EigFrame Z φ' x')
    (T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (hT : ∀ τ i j, i < j → T τ i j = 0)
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (ht : ∀ τ i, T τ i i = t τ i)
    (hh : ∀ τ i, h.vec τ i = ∑ j, T τ i j • res ψ hx (f.vec τ j)) : f.Tri ψ h t := by
  subst hφ hx
  exact ⟨rfl, rfl, fun τ i => ⟨T τ i, ht τ i, fun k hk => hT τ i k hk,
    (GlobalTheory.LieMet.isComb_iff (fun k => res ψ rfl (f.vec τ k)) (T τ i) (h.vec τ i)).2 (hh τ i)⟩⟩

theorem tri_bc {R S T : Type} [CommRing R] [CommRing S] [CommRing T] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f : EigFrame Z φ x) (ψ : R →+* S) {φ' : c.F →+* S} {x' : Sp S ⟶ Z.X} (hφ : ψ.comp φ = φ')
    (hx : spMap ψ ≫ x = x') (g : EigFrame Z φ' x') (hg : ∀ τ i, g.vec τ i = res ψ hx (f.vec τ i))
    (χ : S →+* T) {ω : R →+* T} (hω : χ.comp ψ = ω) {φ'' : c.F →+* T} {x'' : Sp T ⟶ Z.X}
    {k : EigFrame Z φ'' x''} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Tˣ} (h : f.Tri ω k t) : g.Tri χ k t := by
  subst hφ hx hω
  refine ⟨by rw [h.1, ← Category.assoc, spMap_comp_spMap], h.2.1, fun τ i => ?_⟩
  have e : (fun j => spMap (dualMap (χ.comp ψ)) ≫ f.v τ j) = fun j => spMap (dualMap χ) ≫ g.v τ j :=
    funext fun j => by
      have e₁ : g.v τ j = spMap (dualMap ψ) ≫ f.v τ j :=
        congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) (hg τ j)
      rw [e₁, ← Category.assoc, spMap_comp_spMap]
      congr 2
      exact RingHom.ext fun a => by ext <;> simp [dualMap]
  rw [← e]
  exact h.2.2 τ i

end Tri

section Pt

open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

theorem point_data (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)))
    (u : Coord Dw → Γ(C.Y.X, cellOpen C hV f₀ w)) (hu : IsCoord C hV f₀ w u)
    (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ (cellOpen C hV f₀ w).toScheme) (x : Sp Ω ⟶ gen Z)
    (hx : (p ≫ (cellOpen C hV f₀ w).ι) ≫ C.π = x) :
    ∃ (ω : Γ(gen Z, V) →+* Ω) (hω : spMap ω ≫ hV.fromSpec ≫ genι Z = x ≫ genι Z) (φΩ : c.F →+* Ω)
      (M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω),
      spMap ω ≫ hV.fromSpec = x ∧ x ≫ genStr Z = spMap φΩ ∧
      (∀ τ, InCell (M τ) (w τ)
        (fun p' => (Scheme.ΓSpecIso (.of Ω)).hom (p.appTop (coordTop C hV f₀ w u ⟨τ, p'⟩)))) ∧
      (∃ g : EigFrame Z φΩ (x ≫ genι Z), ∀ τ i, g.vec τ i = ∑ k, M τ i k • res ω hω (f₀.vec τ k)) ∧
      ∀ (g : EigFrame Z φΩ (x ≫ genι Z)) (T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω)
        (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Ωˣ), (∀ τ i j, i < j → T τ i j = 0) → (∀ τ i, T τ i i = t τ i) →
        (∀ τ i, g.vec τ i = ∑ j, T τ i j • ∑ k, M τ j k • res ω hω (f₀.vec τ k)) →
        C.Carries (p ≫ (cellOpen C hV f₀ w).ι) g := by
  have hyW : (p ≫ (cellOpen C hV f₀ w).ι) (IsLocalRing.closedPoint Ω) ∈ cellOpen C hV f₀ w := by
    exact (p (IsLocalRing.closedPoint Ω)).2
  obtain ⟨U, ⟨a, hUa⟩, hyU⟩ := TopologicalSpace.Opens.mem_sSup.1 hyW
  have hUW : U ≤ cellOpen C hV f₀ w := le_sSup ⟨a, hUa⟩
  have hco := hu U a hUa hUW
  obtain ⟨hU, hUV, hg, φ, fr, t₀, hxU, A, hstr, hTri, hvec, hcell⟩ := hUa
  set P := p ≫ (cellOpen C hV f₀ w).ι with hP
  set y := P (IsLocalRing.closedPoint Ω) with hy
  let ψ : C.Y.X.presheaf.stalk y →+* Ω := (Scheme.stalkClosedPointTo (R := .of Ω) P).hom
  let gm : Γ(C.Y.X, U) →+* C.Y.X.presheaf.stalk y := (C.Y.X.presheaf.germ U y hyU).hom
  let θ : Γ(C.Y.X, U) →+* Ω := ψ.comp gm
  let ρ : Γ(gen Z, V) →+* Γ(C.Y.X, U) := (C.π.appLE V U hUV).hom
  have hP' : spMap ψ ≫ C.Y.X.fromSpecStalk y = P := GlobalTheory.FlagBundle.spMap_stalkClosedPointTo P
  have hθ : spMap θ ≫ (show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) = P := by
    rw [← spMap_comp_spMap, Category.assoc, GlobalTheory.ShFam.Spread.spMap_germ hU hyU]
    exact hP'
  have hρ : spMap ρ ≫ (show Sp Γ(gen Z, V) ⟶ gen Z from hV.fromSpec) =
      (show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π :=
    IsAffineOpen.SpecMap_appLE_fromSpec C.π hV hU hUV
  have hωx : spMap (θ.comp ρ) ≫ hV.fromSpec = x := by
    rw [← spMap_comp_spMap, Category.assoc, hρ, ← Category.assoc, hθ, hx]
  have hω : spMap (θ.comp ρ) ≫ hV.fromSpec ≫ genι Z = x ≫ genι Z := by
    rw [← Category.assoc, hωx]
  have hxθ : spMap θ ≫ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z = x ≫ genι Z := by
    rw [← hx, ← hθ]
    simp only [Category.assoc]
  have hφx : x ≫ genStr Z = spMap (θ.comp φ) := by
    rw [← spMap_comp_spMap, ← hstr, ← hx, ← hθ]
    simp only [Category.assoc]
  have key : ∀ τ j, res θ hxθ (fr.vec τ j) = ∑ k, (A τ).map θ j k • res (θ.comp ρ) hω (f₀.vec τ k) := by
    intro τ j
    rw [hvec τ j, res_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [res_res ρ hxU θ hxθ rfl hω]
    rfl
  refine ⟨θ.comp ρ, hω, θ.comp φ, fun τ => (A τ).map θ, hωx, hφx, fun τ => ?_, ?_, ?_⟩
  · have hα : (fun p' => (Scheme.ΓSpecIso (.of Ω)).hom (p.appTop (coordTop C hV f₀ w u ⟨τ, p'⟩))) =
        fun p' => θ (a τ p') := by
      funext p'
      rw [coordTop, appTop_topIso_inv p (u ⟨τ, p'⟩) hyW, ← hco τ p']
      show _ = ψ (gm _)
      exact congrArg ψ (C.Y.X.presheaf.germ_res_apply (homOfLE hUW) y hyU _).symm
    rw [hα]
    exact (hcell τ).map θ
  · obtain ⟨g, hgv⟩ := GlobalTheory.ShFam.Spread.exists_bc fr θ rfl hxθ
    exact ⟨g, fun τ i => (hgv τ i).trans (key τ i)⟩
  · intro g T t hT ht hgT
    have hxS : spMap gm ≫ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z =
        stalkPt C.Y y ≫ C.π ≫ genι Z := by
      rw [Category.assoc, ← Category.assoc, GlobalTheory.ShFam.Spread.spMap_germ hU hyU]
      rfl
    have hxψ : spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z = x ≫ genι Z := by
      show spMap ψ ≫ C.Y.X.fromSpecStalk y ≫ C.π ≫ genι Z = _
      rw [← hx, ← hP']
      simp only [Category.assoc]
    obtain ⟨fS, hfS⟩ := GlobalTheory.ShFam.Spread.exists_bc fr gm rfl hxS
    refine ⟨y, ψ, gm.comp φ, fS, t₀, t, hP'.symm, ?_, ?_⟩
    · exact tri_bc fr gm rfl hxS fS hfS _ (RingHom.ext fun a => GlobalTheory.Cartier.algebraMap_germ hyU a) hTri
    · refine tri_of_comb fS ψ rfl hxψ g T hT t ht fun τ i => (hgT τ i).trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hfS, res_res gm hxS ψ hxψ rfl hxθ, key]

end Pt

section Main

open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem eq_of_cellMap_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (k : U.Comp) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (u : Cell.Coord Dw → Γ((Φ.C k).Y.X, Cell.cellOpen (Φ.C k) hV f₀ w)), Cell.IsCoord (Φ.C k) hV f₀ w u → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p q : Spec (.of Ω) ⟶ (Cell.cellOpen (Φ.C k) hV f₀ w).toScheme), p ≫ Cell.cellMap (Φ.C k) hV f₀ w = q ≫ Cell.cellMap (Φ.C k) hV f₀ w → (∀ i, p.appTop (Cell.coordTop (Φ.C k) hV f₀ w u i) = q.appTop (Cell.coordTop (Φ.C k) hV f₀ w u i)) → p = q := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k V hV φV f₀ w u hu Ω _ _ p q hpq hc
  have hx : (q ≫ (cellOpen (Φ.C k) hV f₀ w).ι) ≫ (Φ.C k).π = (p ≫ (cellOpen (Φ.C k) hV f₀ w).ι) ≫ (Φ.C k).π := by
    simp only [Category.assoc, ← cellMap_ι]
    rw [← Category.assoc, ← hpq, Category.assoc]
  obtain ⟨ω, hω, φΩ, M, hωx, hφ, hM, ⟨g, hg⟩, hcar⟩ := point_data (Φ.C k) hV f₀ w u hu Ω p _ rfl
  obtain ⟨ω', hω', φΩ', M', hωx', hφ', hM', -, hcar'⟩ := point_data (Φ.C k) hV f₀ w u hu Ω q _ hx
  have e1 : ω = ω' := by
    have h1 : spMap ω = spMap ω' := (cancel_mono hV.fromSpec).1 (hωx.trans hωx'.symm)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst e1
  have e2 : φΩ = φΩ' := congrArg CommRingCat.Hom.hom (Spec.map_injective (hφ.symm.trans hφ'))
  subst e2
  have hM'' : ∀ τ, InCell (M' τ) (w τ)
      (fun p' => (Scheme.ΓSpecIso (.of Ω)).hom (p.appTop (coordTop (Φ.C k) hV f₀ w u ⟨τ, p'⟩))) := fun τ => by
    simpa only [hc] using hM' τ
  choose T hT0 hTd hTM using fun τ => exists_low_of_inCell (hM τ) (hM'' τ)
  have hq : (Φ.C k).Carries (q ≫ (cellOpen (Φ.C k) hV f₀ w).ι) g := by
    refine hcar' g T (fun τ i => Units.mk0 _ (hTd τ i)) hT0 (fun τ i => rfl) fun τ i => ?_
    rw [hg, hTM τ]
    simp only [Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hp : (Φ.C k).Carries (p ≫ (cellOpen (Φ.C k) hV f₀ w).ι) g := by
    refine hcar g (fun τ => 1) (fun _ _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
      (fun τ i => by simp) fun τ i => ?_
    rw [hg]
    simp [Matrix.one_apply]
  obtain ⟨r, -, huniq⟩ := Φ.lifts Ω φΩ ((p ≫ (cellOpen (Φ.C k) hV f₀ w).ι) ≫ (Φ.C k).π) hφ g
  have h2 := (huniq ⟨k, q ≫ (cellOpen (Φ.C k) hV f₀ w).ι⟩ ⟨hx, hq⟩).trans
    (huniq ⟨k, p ≫ (cellOpen (Φ.C k) hV f₀ w).ι⟩ ⟨rfl, hp⟩).symm
  have h3 : q ≫ (cellOpen (Φ.C k) hV f₀ w).ι = p ≫ (cellOpen (Φ.C k) hV f₀ w).ι :=
    eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  exact ((cancel_mono _).1 h3).symm

end Main

end GlobalTheory.ShFam.Cell
