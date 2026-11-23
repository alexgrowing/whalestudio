import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBasisNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.Spread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open GlobalTheory.LieMet (tan_ext)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_germs {X : Scheme.{0}} (y : X) {W : X.Opens} (hW : y ∈ W) {κ : Type} [Finite κ]
    (a : κ → X.presheaf.stalk y) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (hy : y ∈ U) (s : κ → Γ(X, U)), U ≤ W ∧
      ∀ i, X.presheaf.germ U y hy (s i) = a i := by
  choose V hV s hs using fun i => X.presheaf.exists_germ_eq (a i)
  have ho : IsOpen ((W : Set X) ∩ ⋂ i, (V i : Set X)) :=
    W.isOpen.inter (isOpen_iInter_of_finite fun i => (V i).isOpen)
  obtain ⟨U, hU, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⟨_, ho⟩) (x := y)
    ⟨hW, Set.mem_iInter.2 hV⟩
  have hl : ∀ i, U ≤ V i := fun i z hz => Set.mem_iInter.1 (hle hz).2 i
  exact ⟨U, hU, hy, fun i => X.presheaf.map (homOfLE (hl i)).op (s i), fun z hz => (hle hz).1,
    fun i => (X.presheaf.germ_res_apply (homOfLE (hl i)) y hy (s i)).trans (hs i)⟩

theorem spMap_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U) :
    spMap (X.presheaf.germ U y hy).hom ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec) =
      (show Sp (X.presheaf.stalk y) ⟶ X from X.fromSpecStalk y) :=
  hU.fromSpecStalk_eq_fromSpecStalk hy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem exists_bc {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* S) {φ' : c.F →+* S}
    {x' : Sp S ⟶ Z.X} (hφ : ψ.comp φ = φ') (hx : spMap ψ ≫ x = x') :
    ∃ g : EigFrame Z φ' x', ∀ τ i, g.vec τ i = res ψ hx (f.vec τ i) := by
  subst hφ hx
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z R S φ x f ψ
  exact ⟨g, fun τ i => tan_ext (hg τ i)⟩

theorem exists_coord {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ A B : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, B * A = 1 ∧ ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k := by
  choose A hA _ using fun i => f.existsUnique_sum τ (g.vec τ i) (g.act_vec τ i)
  choose B hB _ using fun i => g.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)
  refine ⟨Matrix.of A, Matrix.of B, Matrix.ext fun i => congrFun ?_, hA⟩
  refine (f.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)).unique ?_ ?_
  · refine (hB i).trans ?_
    simp only [show ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k from hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    exact Finset.sum_comm
  · simp only [Matrix.one_apply, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      zero_smul R]

theorem exists_change {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (A B : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (h : ∀ τ, B τ * A τ = 1) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.vec τ i = ∑ k, A τ i k • f.vec τ k := by
  have hs : ∀ τ (a : Fin (Dw.mult τ) → R), ∑ i, a i • ∑ k, A τ i k • f.vec τ k =
      ∑ k, (Matrix.vecMul a (A τ)) k • f.vec τ k := fun τ a => by
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  refine ⟨EigFrame.ofVec (fun τ i => ∑ k, A τ i k • f.vec τ k) (fun τ i a => ?_) fun τ w hw => ?_,
    fun τ i => tan_ext rfl⟩
  · simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · obtain ⟨a, ha, hu⟩ := f.existsUnique_sum τ w hw
    refine ⟨Matrix.vecMul a (B τ), ?_, fun b hb => ?_⟩
    · show w = _
      rw [hs, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
      exact ha
    · rw [← hu _ (hb.trans (hs τ b)), Matrix.vecMul_vecMul, mul_eq_one_comm.1 (h τ), Matrix.vecMul_one]

theorem tri_of_bc {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* S) {φ' : c.F →+* S}
    {x' : Sp S ⟶ Z.X} (hφ : ψ.comp φ = φ') (hx : spMap ψ ≫ x = x') (g : EigFrame Z φ' x')
    (hg : ∀ τ i, g.vec τ i = res ψ hx (f.vec τ i)) (χ : S →+* T) {ω : R →+* T} (hω : χ.comp ψ = ω)
    {φ'' : c.F →+* T} {x'' : Sp T ⟶ Z.X} {k : EigFrame Z φ'' x''} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Tˣ}
    (h : g.Tri χ k t) : f.Tri ω k t := by
  subst hφ hx hω
  refine ⟨by rw [h.1, ← Category.assoc, spMap_comp_spMap], h.2.1, fun τ i => ?_⟩
  have e : (fun j => spMap (dualMap (χ.comp ψ)) ≫ f.v τ j) = fun j => spMap (dualMap χ) ≫ g.v τ j := funext fun j => by
    have e₁ : g.v τ j = spMap (dualMap ψ) ≫ f.v τ j := congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) (hg τ j)
    rw [e₁, ← Category.assoc, spMap_comp_spMap]
    congr 2
    exact RingHom.ext fun a => by ext <;> simp [dualMap]
  rw [e]
  exact h.2.2 τ i

theorem exists_frame_nhds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (y : C.Y.X) (V : C.Y.X.Opens), y ∈ V → ∃ (U : C.Y.X.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (φ : c.F →+* Γ(C.Y.X, U)) (fr : EigFrame Z φ (((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), U ≤ V ∧ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genStr Z = spMap φ ∧ fr.Tri (fnOf U (gen_mem hy)) C.f0 t ∧ ∀ y' ∈ U, ∀ τ i, (C.gr τ i).IsEqn y' (t τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C y V hV
  obtain ⟨φ₁, f, t, hT, ht⟩ := C.gr_spec y
  obtain ⟨U₀, hU₀, φ₀, f₀, hy₀, hs₀, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (C.π y)
  let j := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField
  let gm₀ : Γ(gen Z, U₀) →+* C.Y.X.presheaf.stalk y :=
    (C.Y.X.presheaf.germ (C.π ⁻¹ᵁ U₀) y hy₀).hom.comp (C.π.app U₀).hom
  have hgm : ∀ (U : C.Y.X.Opens) (hy : y ∈ U) (h : U ≤ C.π ⁻¹ᵁ U₀),
      (C.Y.X.presheaf.germ U y hy).hom.comp (C.π.appLE U₀ U h).hom = gm₀ := fun U hy h =>
    RingHom.ext fun a => C.Y.X.presheaf.germ_res_apply (homOfLE h) y hy _
  have hρ : ∀ (U : C.Y.X.Opens) (hU : IsAffineOpen U) (h : U ≤ C.π ⁻¹ᵁ U₀),
      spMap (C.π.appLE U₀ U h).hom ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) =
        (show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π := fun U hU h =>
    IsAffineOpen.SpecMap_appLE_fromSpec C.π hU₀ hU h
  have hx₀ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) = stalkPt C.Y y ≫ C.π := by
    obtain ⟨U, hU, hy, h⟩ := exists_isAffineOpen_mem_and_subset (X := C.Y.X) (U := C.π ⁻¹ᵁ U₀) (x := y) hy₀
    rw [← hgm U hy h, ← spMap_comp_spMap, Category.assoc, hρ U hU h, ← Category.assoc, spMap_germ]
    rfl
  have hs₀' : (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genStr Z = spMap φ₀ := hs₀
  have hφ₀ : gm₀.comp φ₀ = φ₁ := by
    letI := (constF e C.Y).toAlgebra
    have hgen : spMap j ≫ stalkPt C.Y y = genericPt C.Y :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.Y.X).specializes trivial)
    have h1 : spMap (j.comp (gm₀.comp φ₀)) = spMap (constF e C.Y) := by
      rw [← spMap_comp_spMap, ← spMap_comp_spMap, ← hs₀', ← Category.assoc (spMap gm₀), hx₀, ← Category.assoc,
        ← Category.assoc, hgen]
      exact (congrArg (· ≫ genStr Z) C.y0_x.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) Z.jQ_over).trans (ptF_snd C.y0)))
    have h2 : j.comp (gm₀.comp φ₀) = constF e C.Y := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    exact RingHom.ext fun r => IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField
      ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hT.2.1 r))
  have hx₁ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      stalkPt C.Y y ≫ C.π ≫ genι Z := by rw [← Category.assoc, hx₀, Category.assoc]
  obtain ⟨g, hg⟩ := exists_bc f₀ gm₀ hφ₀ hx₁
  choose A B hAB hA using exists_coord g f
  choose N hN hN' using fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => (ht p.1 p.2).exists_nhds
  have ho : IsOpen ((V ⊓ C.π ⁻¹ᵁ U₀ : C.Y.X.Opens) ∩ ⋂ p, (N p : Set C.Y.X)) :=
    (V ⊓ C.π ⁻¹ᵁ U₀).isOpen.inter (isOpen_iInter_of_finite fun p => (N p).isOpen)
  obtain ⟨U, hU, hy, s, hle, hs⟩ := exists_affine_germs y (W := ⟨_, ho⟩) ⟨⟨hV, hy₀⟩, Set.mem_iInter.2 hN⟩
    (fun p : Bool × (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)) =>
      (cond p.1 (A p.2.1) (B p.2.1)) p.2.2.1 p.2.2.2)
  have h₀ : U ≤ C.π ⁻¹ᵁ U₀ := fun z hz => (hle hz).1.2
  let gm : Γ(C.Y.X, U) →+* C.Y.X.presheaf.stalk y := (C.Y.X.presheaf.germ U y hy).hom
  let ρ : Γ(gen Z, U₀) →+* Γ(C.Y.X, U) := (C.π.appLE U₀ U h₀).hom
  let A' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(C.Y.X, U) :=
    fun τ => Matrix.of fun i k => s (true, ⟨τ, i, k⟩)
  let B' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(C.Y.X, U) :=
    fun τ => Matrix.of fun i k => s (false, ⟨τ, i, k⟩)
  have hA' : ∀ τ i k, gm (A' τ i k) = A τ i k := fun τ i k => hs (true, ⟨τ, i, k⟩)
  have hB' : ∀ τ i k, gm (B' τ i k) = B τ i k := fun τ i k => hs (false, ⟨τ, i, k⟩)
  have hAB' : ∀ τ, B' τ * A' τ = 1 := fun τ => Matrix.ext fun i k => germ_injective_of_isIntegral C.Y.X y hy (by
    show gm _ = gm _
    have := congrFun (congrFun (hAB τ) i) k
    simp only [Matrix.mul_apply, map_sum, map_mul, hA', hB', Matrix.one_apply] at this ⊢
    rw [this]
    split_ifs <;> simp)
  have hx₂ : spMap ρ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z := by rw [← Category.assoc, hρ U hU h₀]
  have hx₃ : spMap gm ≫ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z =
      stalkPt C.Y y ≫ C.π ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, spMap_germ]
    rfl
  obtain ⟨g', hg'⟩ := exists_bc f₀ ρ rfl hx₂
  obtain ⟨fr, hfr⟩ := exists_change g' A' B' hAB'
  refine ⟨U, hU, hy, ρ.comp φ₀, fr, t, fun z hz => (hle hz).1.1, ?_, ?_,
    fun y' hy' τ i => hN' ⟨τ, i⟩ y' (Set.mem_iInter.1 (hle hy').2 ⟨τ, i⟩)⟩
  · rw [← hρ U hU h₀, Category.assoc, hs₀']
    exact spMap_comp_spMap φ₀ ρ
  · refine tri_of_bc fr gm (by rw [← RingHom.comp_assoc, hgm U hy h₀, hφ₀]) hx₃ f (fun τ i => ?_) j
      (RingHom.ext fun a => algebraMap_germ hy a) hT
    rw [hfr, res_sum, hA]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA', hg, hg', res_res ρ hx₂ gm hx₃ (hgm U hy h₀) hx₁]

end GlobalTheory.ShFam.Spread
