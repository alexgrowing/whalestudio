import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.ValCoord

open GlobalTheory.ShFam.Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ρ : A →+* B) {x' : Sp B ⟶ Z.X} (hx : spMap ρ ≫ x = x') :
    ∃ g : EigFrame Z (ρ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ρ) ≫ fr.v τ i := by
  subst hx
  exact EigFrame.exists_baseChange E H Dw l Xo c O β Z A B φ x fr ρ

theorem spMap_dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ρ : A →+* B) (χ : B →+* C) :
    spMap (dualMap χ) ≫ spMap (dualMap ρ) = spMap (dualMap (χ.comp ρ)) := by
  rw [sp_comp]
  congr 1
  ext z <;> simp [dualMap]

theorem tri_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {φ : c.F →+* A} {x : Sp A ⟶ Z.X}
    {fr : EigFrame Z φ x} {ρ : A →+* B} {x₀ : Sp B ⟶ Z.X} (hx₀ : spMap ρ ≫ x = x₀) {g₀ : EigFrame Z (ρ.comp φ) x₀}
    (hg : ∀ τ i, g₀.v τ i = spMap (dualMap ρ) ≫ fr.v τ i) {χ : B →+* C} {φ' : c.F →+* C} {x' : Sp C ⟶ Z.X}
    {g : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Cˣ} (h : fr.Tri (χ.comp ρ) g t) : g₀.Tri χ g t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, ← hx₀, ← Category.assoc, sp_comp]
  · rw [h2]; rfl
  · obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
    refine ⟨cf, c1, c2, ?_⟩
    have e : (fun k => spMap (dualMap χ) ≫ g₀.v τ k) = fun k => spMap (dualMap (χ.comp ρ)) ≫ fr.v τ k :=
      funext fun k => by rw [hg, ← Category.assoc, spMap_dualMap_comp]
    rw [e]
    exact c3

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem core {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) {ex : Ix Dw → ℤ} (hex : ex none = 0)
    {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) {n : Letter Dw → ℤ} (hn : ∀ z, n z = -ex (some z))
    {p : Sp k ⟶ Y.Y.X} (hp : p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ) {y : Y.Y.X} {ψ : Y.Y.X.presheaf.stalk y →+* k}
    {φ₁ : c.F →+* Y.Y.X.presheaf.stalk y} {fr : EigFrame Z φ₁ (stalkPt Y.Y y ≫ Y.π ≫ genι Z)}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ} {t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ}
    (h1 : p = spMap ψ ≫ stalkPt Y.Y y)
    (h2 : fr.Tri (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) Y.f0 t)
    (h3 : fr.Tri ψ (frameOf Z P) t') :
    ∃ (y₀ : Y.Y.X) (ψ₀ : Y.Y.X.presheaf.stalk y₀ →+* k) (ρ : Y.Y.X.presheaf.stalk y →+* Y.Y.X.presheaf.stalk y₀)
      (g₀ : EigFrame Z (ρ.comp φ₁) (stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z)) (r : Y.Y.X.presheaf.stalk y₀),
      p = spMap ψ₀ ≫ stalkPt Y.Y y₀ ∧
      g₀.Tri (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) Y.f0 t ∧ g₀.Tri ψ₀ (frameOf Z P) t' ∧
      ψ = ψ₀.comp ρ ∧
      algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField =
        (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField).comp ρ ∧
      algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField r =
        Y.val f * ((∏ z : Letter Dw, t z.1 z.2 ^ n z : Y.Y.Fnˣ) : Y.Y.Fn) ∧
      evR Xo c f P = ψ₀ r * ((∏ z : Letter Dw, t' z.1 z.2 ^ (-n z) : kˣ) : k) := by
  classical
  obtain ⟨y₀, ψ₀, hp₀, hsp, hopen⟩ : ∃ (y₀ : Y.Y.X) (ψ₀ : Y.Y.X.presheaf.stalk y₀ →+* k),
      spMap ψ₀ ≫ stalkPt Y.Y y₀ = p ∧ y₀ ⤳ y ∧ Y.π y₀ ∈ Set.range Z.jQ := by
    refine ⟨_, (Scheme.stalkClosedPointTo (R := .of k) p).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk p, ?_, ?_⟩
    · have : p (IsLocalRing.closedPoint k) ∈ Set.range (Y.Y.X.fromSpecStalk y) := by
        rw [h1]
        exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecStalk] at this
    · have := congrArg (fun q : Sp k ⟶ gen Z => q (IsLocalRing.closedPoint (CommRingCat.of k))) hp
      simp only [Scheme.Hom.comp_apply] at this
      exact ⟨_, this.symm⟩
  haveI : ∀ z : Y.Y.X, Mono (stalkPt Y.Y z) := fun z => inferInstanceAs (Mono (Y.Y.X.fromSpecStalk z))
  let ρ := (Y.Y.X.presheaf.stalkSpecializes hsp).hom
  have hρ : spMap ρ ≫ stalkPt Y.Y y = stalkPt Y.Y y₀ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hψ : ψ = ψ₀.comp ρ := by
    apply sp_inj
    apply (cancel_mono (stalkPt Y.Y y)).1
    rw [← h1, ← sp_comp, Category.assoc, hρ, hp₀]
  have hgen : ∀ z : Y.Y.X,
      spMap (algebraMap (Y.Y.X.presheaf.stalk z) Y.Y.X.functionField) ≫ stalkPt Y.Y z = genericPt Y.Y :=
    fun z => Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y.Y.X).specializes trivial)
  have hι : algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField =
      (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField).comp ρ := by
    apply sp_inj
    apply (cancel_mono (stalkPt Y.Y y)).1
    rw [hgen, ← sp_comp, Category.assoc, hρ, hgen]
  have hx₀ : spMap ρ ≫ (stalkPt Y.Y y ≫ Y.π ≫ genι Z) = stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨g₀, hg₀⟩ := exists_bc fr ρ hx₀
  have T1 : g₀.Tri (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) Y.f0 t :=
    tri_bc hx₀ hg₀ (by rw [← hι]; exact h2)
  have T2 : g₀.Tri ψ₀ (frameOf Z P) t' := tri_bc hx₀ hg₀ (by rw [← hψ]; exact h3)

  letI : Algebra c.F (Y.Y.X.presheaf.stalk y₀) := (ρ.comp φ₁).toAlgebra
  letI : Algebra c.F Y.Y.X.functionField := (constF e Y.Y).toAlgebra
  haveI := Z.jQ_open
  have hr : Set.range (stalkPt Y.Y y₀ ≫ Y.π) ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    have h1 : stalkPt Y.Y y₀ q ⤳ y₀ := by
      have : stalkPt Y.Y y₀ q ∈ Set.range (Y.Y.X.fromSpecStalk y₀) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact (h1.map Y.π.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hopen
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = stalkPt Y.Y y₀ ≫ Y.π := IsOpenImmersion.lift_fac _ _ _
  have hpt0 : GlobalTheory.AllWt.ptF Y.y0 = spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, hgen]
    exact Y.y0_x
  have hc : constF e Y.Y = (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField).comp (ρ.comp φ₁) := by
    rw [h2.2.1, hι]; rfl
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (Y.Y.X.presheaf.stalk y₀)) := by
    obtain ⟨φ₂, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have k1 : spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ spMap φ₂.hom =
        spMap (constF e Y.Y) := by
      have h0 : GlobalTheory.AllWt.ptF Y.y0 ≫ pullback.snd _ _ = spMap (constF e Y.Y) := pullback.lift_snd _ _ _
      rw [← h0, hpt0, Category.assoc, ← h]
      rfl
    rw [sp_comp] at k1
    have k2 := sp_inj k1
    have k3 : φ₂.hom = ρ.comp φ₁ := RingHom.ext fun r =>
      IsFractionRing.injective (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField
        ((RingHom.congr_fun k2 r).trans (RingHom.congr_fun hc r))
    rw [← h]
    exact congrArg spMap k3
  have hxj : xF ≫ Z.j = stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z := by
    show xF ≫ Z.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, hxF, Category.assoc]
  obtain ⟨P', hP', htie⟩ := exists_tie_point (Z := Z) hs hxj rfl g₀
  have tie0 : Comparison₂ Y.y0 Y.f0 := ⟨rfl, by
    show _ ≫ Z.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, Y.y0_x, Category.assoc], Y.flagComponentFramedPoint_frame⟩
  let ι₀ : Y.Y.X.presheaf.stalk y₀ →ₐ[c.F] Y.Y.X.functionField :=
    { algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField with
      commutes' := fun r => (RingHom.congr_fun hc r).symm }
  have hx1 : Y.y0.x = spMap ι₀.toRingHom ≫ P'.x := by
    rw [← ptF_fst Y.y0, ← ptF_fst P', hpt0, hP', Category.assoc]
  obtain ⟨u, hu, hu'⟩ := Comparison₂.bm_of_tri htie tie0 (ψ := ι₀) hx1 T1
  have e1 := BM.evR hu hf
  have hcP : algebraMap c.F k = ψ₀.comp (ρ.comp φ₁) := by
    rw [h3.2.1, hψ]; rfl
  let ψa : Y.Y.X.presheaf.stalk y₀ →ₐ[c.F] k :=
    { ψ₀ with commutes' := fun r => (RingHom.congr_fun hcP r).symm }
  have hptP : GlobalTheory.AllWt.ptF P = spMap ψ₀ ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← hp, ← hp₀, Category.assoc]
  have hx2 : P.x = spMap ψa.toRingHom ≫ P'.x := by
    rw [← ptF_fst P, ← ptF_fst P', hptP, hP', Category.assoc]
  obtain ⟨v, hv, hv'⟩ := Comparison₂.bm_of_tri htie (tie_frameOf Z P) (ψ := ψa) hx2 T2
  have e2 := BM.evR hv hf

  have hchi : ∀ {A : Type} [CommRing A] [Algebra c.F A] (w : Ix Dw → Aˣ)
      (s : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Aˣ), (∀ τ i, w (some ⟨τ, i⟩) = s τ i) →
      GlobalTheory.ShFam.Descent.chi ex w = ∏ z : Letter Dw, s z.1 z.2 ^ ex (some z) := by
    intro A _ _ w s hw
    simp only [GlobalTheory.ShFam.Descent.chi, Fintype.prod_option, hex, zpow_zero, one_mul]
    exact Finset.prod_congr rfl fun z _ => by rw [← hw z.1 z.2]
  have E1 : Y.val f = ((∏ z : Letter Dw, t z.1 z.2 ^ ex (some z) : Y.Y.Fnˣ) : Y.Y.Fn) *
      algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField (evR Xo c f P') := by
    rw [← hchi u t hu']
    exact e1
  have E2 : evR Xo c f P = ((∏ z : Letter Dw, t' z.1 z.2 ^ ex (some z) : kˣ) : k) * ψ₀ (evR Xo c f P') := by
    rw [← hchi v t' hv']
    exact e2
  refine ⟨y₀, ψ₀, ρ, g₀, evR Xo c f P', hp₀.symm, T1, T2, hψ, hι, ?_, ?_⟩
  · have pn : (∏ z : Letter Dw, t z.1 z.2 ^ n z) = (∏ z : Letter Dw, t z.1 z.2 ^ ex (some z))⁻¹ := by
      simp only [hn, zpow_neg, Finset.prod_inv_distrib]
    rw [E1, pn, mul_right_comm, Units.mul_inv, one_mul]
  · simp only [hn, neg_neg]
    rw [E2, mul_comm]

theorem coordAt_val_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (k : Type) [Field k] [Algebra c.F k] (P : FrPt Xo c k) (ex : Ix Dw → ℤ), ex none = 0 → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c ex, ∀ a : k, CoordAt Y P (fun z => -ex (some z)) (Y.val f) a ↔ Carried Y P ∧ a = evR Xo c f P := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y k _ _ P ex hex f hf a
  constructor
  · intro h
    refine ⟨h.carried, ?_⟩
    obtain ⟨p, hp, y, ψ, φ₁, fr, t, t', r₀, h1, h2, h3, h4, h5⟩ := h
    obtain ⟨y₀, ψ₀, ρ, g₀, r, -, -, -, hψ, hι, hr, hev⟩ :=
      core Y P hex hf (n := fun z => -ex (some z)) (fun _ => rfl) hp h1 h2 h3
    have hρ : ρ r₀ = r := IsFractionRing.injective (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField (by
      rw [← RingHom.comp_apply, ← hι, h4, hr])
    rw [h5, hev, hψ, RingHom.comp_apply, hρ]
  · rintro ⟨⟨p, hp, y, ψ, φ₁, fr, t, t', h1, h2, h3⟩, rfl⟩
    obtain ⟨y₀, ψ₀, ρ, g₀, r, hp₀, T1, T2, -, -, hr, hev⟩ :=
      core Y P hex hf (n := fun z => -ex (some z)) (fun _ => rfl) hp h1 h2 h3
    exact ⟨p, hp, y₀, ψ₀, _, g₀, t, t', r, hp₀, T1, T2, hr, hev⟩

end GlobalTheory.ShFam.ValCoord
