import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.ChartValue

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => by ext <;> simp [dualMap]

theorem exists_evR_eq_of_tri {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.F R] (xF : Sp R ⟶ Xo.XF c)
    (hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) {x : Sp R ⟶ Z.X} (hx : xF ≫ Z.jQ ≫ pullback.fst _ _ = x)
    (f : EigFrame Z (algebraMap c.F R) x) {ex : Ix Dw → ℤ} (hex : ex none = 0) {g : Rul Xo c}
    (hg : g ∈ GlobalTheory.AllWt.secZ Xo c ex) :
    ∃ a : R, ∀ (K : Type) [CommRing K] [IsLocalRing K] [Algebra c.F K] (ψ : R →ₐ[c.F] K)
      (v0 : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber K) ⟶ Z.t.G.left))
      (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (y0 : FrPt Xo c K),
      (∀ τ i, ∃ cf : Fin (Dw.mult τ) → K, cf i = t τ i ∧ (∀ k, i < k → cf k = 0) ∧
        IsCombAtG Z.t (spMap ψ.toRingHom ≫ x) (fun k => spMap (dualMap ψ.toRingHom) ≫ f.v τ k) cf (v0 τ i)) →
      GlobalTheory.AllWt.ptF y0 = spMap ψ.toRingHom ≫ xF →
      (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
        w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 ∧
          w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = v0 τ i) →
      evR Xo c g y0 = ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : Kˣ) : K) * ψ a := by
  obtain ⟨y, w, hyx, hw⟩ := exists_frPt_of_eigFrame xF hs hx f
  refine ⟨evR Xo c g y, fun K _ _ _ ψ v0 t y0 hT hy hu => ?_⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap ψ y
  have h0 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = y0.x := pullback.lift_fst _ _ _
  have h1 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = z.x := by rw [hz.1, hyx, hy, Category.assoc]
  have h2 : GlobalTheory.AllWt.ptF y0 ≫ Z.jQ ≫ pullback.fst _ _ = spMap ψ.toRingHom ≫ x := by rw [hy, ← hx, Category.assoc]
  obtain ⟨g0, a, -, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c K z y0).1 (h0.symm.trans h1)
  choose cf hcf1 hcf2 hcf3 using hT
  have hcomb : ∀ τ i, IsCombAt z.x (z.u τ) (cf τ i) (y0.u τ i) := fun τ i => by
    obtain ⟨w0, a1, a2, a3⟩ := hu τ i
    have hv : ∀ k, (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.oF.t.G.hom =
        spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 := fun k => by
      rw [Category.assoc, (hw τ k).1, hy, ← Category.assoc, ← Category.assoc, OpenReg.spMap_comp, OpenReg.spMap_comp,
        GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]
    have e1 : z.u τ = fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m0.toSABMap.φ := funext fun k => by
      rw [hz.2.1, Category.assoc, (hw τ k).2.1]
    have e2 : (fun k => spMap (dualMap ψ.toRingHom) ≫ f.v τ k) =
        fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m.φ := funext fun k => by
      rw [Category.assoc, (hw τ k).2.2]
    have b := hcf3 τ i
    rw [e2, ← a3] at b
    rw [e1, ← a2]
    exact (comb_iff Z.m0.toSABMap h1 hv _ a1).2 ((comb_iff Z.m h2 hv _ a1).1 b)
  let T : Ix Dw → Kˣ := fun k => k.elim a fun k => t k.1 k.2
  have hb : FrBor T z y0 := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c K).2.2.2 T z y0).2
    ⟨fun τ => Matrix.of (cf τ), fun τ i => hcf1 τ i, fun τ i j hij => hcf2 τ i j hij, hc.1, hcomb, hc.2.2⟩
  rw [GlobalTheory.FlagTan.evR_frBor hg hb, GlobalTheory.FlagTan.evR_frMap hg.1 hz, Fintype.prod_option, hex, zpow_zero,
    _root_.one_mul]
  rfl

theorem exists_value_local {A R K L : Type} [CommRing A] [CommRing R] [IsLocalRing R] [Field K] [CommRing L] [IsLocalRing L]
    [Algebra c.F K] [Algebra c.F L] (j : A →+* R) (ι : R →+* K) (hι : Function.Injective ι) (ψ : R →+* L) [IsLocalHom ψ]
    (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) {x' : Sp K ⟶ Z.X}
    (f0 : EigFrame Z (algebraMap c.F K) x') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (hT : fr.Tri (ι.comp j) f0 t)
    (y0 : FrPt Xo c K) (hy0 : GlobalTheory.AllWt.ptF y0 ≫ Z.jQ = spMap (ι.comp j) ≫ x)
    (hu0 : ∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 ∧
        w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = f0.v τ i)
    (hσ : (ψ.comp j).comp φ = algebraMap c.F L) (y : FrPt Xo c L)
    (hy : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (ψ.comp j) ≫ x)
    (hu : ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ GlobalTheory.AllWt.ptF y ∧
        w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (ψ.comp j)) ≫ fr.v τ i)
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c ex) :
    ∃ a : R, evR Xo c g y0 = ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : Kˣ) : K) * ι a ∧
      evR Xo c g y = ψ a := by
  letI : Algebra c.F R := (j.comp φ).toAlgebra
  haveI := Z.jQ_open
  obtain ⟨f, hf⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z A R φ _ fr j
  let ι' : R →ₐ[c.F] K := { ι with commutes' := fun r => (RingHom.congr_fun hT.2.1 r).symm }
  let ψ' : R →ₐ[c.F] L := { ψ with commutes' := fun r => RingHom.congr_fun hσ r }
  have hr : Set.range (spMap j ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have h1 : p ⤳ spMap ψ (IsLocalRing.closedPoint L) := by
      have : spMap ψ (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint R := IsLocalRing.comap_closedPoint ψ
      rw [this]
      exact IsLocalRing.specializes_closedPoint p
    refine (h1.map (spMap j ≫ x).continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range
      ⟨GlobalTheory.AllWt.ptF y (IsLocalRing.closedPoint L), ?_⟩
    have h2 : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap ψ ≫ spMap j ≫ x := by rw [hy, ← Category.assoc, OpenReg.spMap_comp]
    exact congrArg (fun m : Sp L ⟶ gen Z => m (IsLocalRing.closedPoint L)) h2
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = spMap j ≫ x := IsOpenImmersion.lift_fac _ _ _
  have hpt0 : GlobalTheory.AllWt.ptF y0 = spMap ι ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, OpenReg.spMap_comp, hy0]
  have hpt : GlobalTheory.AllWt.ptF y = spMap ψ ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, OpenReg.spMap_comp, hy]
  have hs : xF ≫ pullback.snd _ _ = spMap (j.comp φ) := by
    obtain ⟨φ₁, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have h1 : spMap ι ≫ spMap φ₁.hom = spMap (algebraMap c.F K) := by
      have h0 : GlobalTheory.AllWt.ptF y0 ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := pullback.lift_snd _ _ _
      rw [← h0, hpt0, Category.assoc, ← h]
      rfl
    rw [OpenReg.spMap_comp] at h1
    have h2 : ι.comp φ₁.hom = algebraMap c.F K := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : φ₁.hom = j.comp φ := RingHom.ext fun r =>
      hι ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hT.2.1 r))
    rw [← h, ← h3]
    rfl
  obtain ⟨a, ha⟩ := exists_evR_eq_of_tri xF hs (by rw [← Category.assoc, hxF, Category.assoc]) f hex hg
  have e0 : ∀ {M : Type} [CommRing M] (χ : R →+* M) (τ : E →+* ℂ),
      (fun k => spMap (dualMap χ) ≫ f.v τ k) = fun k => spMap (dualMap (χ.comp j)) ≫ fr.v τ k := fun χ τ =>
    funext fun k => by rw [hf, ← Category.assoc, OpenReg.spMap_comp, dualMap_comp']
  refine ⟨a, ha K ι' f0.v t y0 (fun τ i => ?_) hpt0 hu0, ?_⟩
  · obtain ⟨cf, h1, h2, h3⟩ := hT.2.2 τ i
    refine ⟨cf, h1, h2, ?_⟩
    have e1 : x' = spMap ι ≫ spMap j ≫ x ≫ genι Z := by rw [hT.1, ← Category.assoc (spMap ι), OpenReg.spMap_comp]
    subst e1
    rw [← e0 ι τ] at h3
    exact h3
  · have := ha L ψ' (fun τ i => spMap (dualMap (ψ.comp j)) ≫ fr.v τ i) 1 y (fun τ i => ?_) hpt hu
    · exact this.trans (by simp; rfl)
    · refine ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩
      obtain ⟨f', hf'⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z R L _ _ f ψ
      have h := isCombAtG_single Z.t _ (fun k => hf' τ k ▸ f'.tan τ k) i
      rw [← congrFun (e0 ψ τ) i]
      exact h

theorem value_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (U : C.Y.X.Opens) (hU : IsAffineOpen U) (hg : genericPoint C.Y.X ∈ U) (φ : c.F →+* Γ(C.Y.X, U)) (fr : EigFrame Z φ (((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (ex : Ix Dw → ℤ) (g : Rul Xo c) (σ : c.F →+* ℂ) (ψ : Γ(C.Y.X, U) →+* ℂ) (y : FrPt Xo c (CAt σ)) (a b : Γ(C.Y.X, U)), fr.Tri (fnOf U hg) C.f0 t → ex none = 0 → g ∈ GlobalTheory.AllWt.secZ Xo c ex → ψ.comp φ = σ → Matches fr ψ y → fnOf U hg a = C.val g * ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : C.Y.Fnˣ)⁻¹ : C.Y.Fnˣ) * fnOf U hg b → ψ a = toC (evR Xo c g y) * ψ b := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C U hU hg φ fr t ex g σ ψ y a b hT hex hsec hσ hM hab
  letI := (constF e C.Y).toAlgebra
  have hinj : Function.Injective (fnOf U hg) := fnOf_injective U hg
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let R := Localization.AtPrime (RingHom.ker ψ)
  have u1 : ∀ s : (RingHom.ker ψ).primeCompl, IsUnit (fnOf U hg s) := fun s =>
    IsUnit.mk0 _ fun h => s.2 (by rw [(injective_iff_map_eq_zero _).1 hinj _ h]; exact zero_mem _)
  let ψ₀ : Γ(C.Y.X, U) →+* CAt σ := ψ
  have u2 : ∀ s : (RingHom.ker ψ).primeCompl, IsUnit (ψ₀ s) := fun s => IsUnit.mk0 (G₀ := ℂ) _ s.2
  let ι : R →+* C.Y.Fn := IsLocalization.lift u1
  let χ : R →+* CAt σ := IsLocalization.lift u2
  have e1 : ι.comp (algebraMap _ R) = fnOf U hg := IsLocalization.lift_comp u1
  have e2 : χ.comp (algebraMap _ R) = ψ₀ := IsLocalization.lift_comp u2
  haveI : IsDomain Γ(C.Y.X, U) := hinj.isDomain _
  have hι : Function.Injective ι := (IsLocalization.lift_injective_iff u1).2 fun p q =>
    (IsLocalization.injective R (RingHom.ker ψ).primeCompl_le_nonZeroDivisors).eq_iff.trans hinj.eq_iff.symm
  haveI : IsLocalHom χ := ⟨fun r hr => by
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (RingHom.ker ψ).primeCompl r
    have h1 : χ r * ψ₀ s = ψ₀ p := by
      rw [← e2]; simpa using congrArg χ h
    have h2 : p ∈ (RingHom.ker ψ).primeCompl := IsUnit.ne_zero (M₀ := ℂ) (show IsUnit (ψ₀ p) from h1 ▸ hr.mul (u2 s))
    have h3 := IsLocalization.map_units R (⟨p, h2⟩ : (RingHom.ker ψ).primeCompl)
    exact isUnit_of_mul_isUnit_left (h ▸ h3)⟩
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hgen : genericPt C.Y = spMap (fnOf U hg) ≫ (show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) :=
    (hU.fromSpecStalk_eq_fromSpecStalk hg).symm
  obtain ⟨a₀, h1, h2⟩ := exists_value_local (algebraMap _ R) ι hι χ φ _ fr C.f0 t (e1 ▸ hT) C.y0
    (by rw [e1, ← Category.assoc, ← hgen]; exact C.y0_x) C.flagComponentFramedPoint_frame (by rw [e2]; exact hσ) y
    (by rw [e2]; exact hM.1) (by rw [e2]; exact hM.2) hex hsec
  have h3 : algebraMap _ R a = a₀ * algebraMap _ R b := hι (by
    rw [map_mul]
    refine (RingHom.congr_fun e1 a).trans (hab.trans ?_)
    rw [show ι (algebraMap _ R b) = fnOf U hg b from RingHom.congr_fun e1 b, show C.val g = _ from h1,
      mul_right_comm _ (ι a₀), Units.mul_inv, _root_.one_mul])
  have h4 := congrArg χ h3
  rw [map_mul, ← h2] at h4
  exact (RingHom.congr_fun e2 a).symm.trans (h4.trans (congrArg (evR Xo c g y * ·) (RingHom.congr_fun e2 b)))

end GlobalTheory.ShFam.ChartValue
