import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTermWeightZeroSectionLevelOneFormalSumStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRigidifiedIsoAgreeAbelianFibresStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermMemConvLaurent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.ArcSectionValue

theorem valR_res_const_res {A K : Type} [CommRing A] [CommRing K] {Z : Scheme.{0}} (p : Z ⟶ Sp K) (f : K →+* A)
    (q : Sp A ⟶ Z) (hq : q ≫ p = spMap f) {U U' V : Z.Opens} (h : V ≤ U) (h' : V ≤ U') (hV : ⊤ ≤ q ⁻¹ᵁ V)
    (a : Γ(Z, U)) (r : K) (b : Γ(Z, U')) :
    valR q V (resG Z h a * constFn p V r * resG Z h' b) = valR q U a * f r * valR q U' b := by
  rw [← HolHom.valR_res q h a hV, ← HolHom.valR_res q h' b hV, ← valR_const p f q hq V hV]
  simp only [HolHom.valR_eq _ V hV, map_mul]

theorem germ_identity {Γ : Germs} {w : ℂ} {Z Z' : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (φ : Z ⟶ Z') {xF : Sp ℂ⸨X⸩ ⟶ Z}
    (hx : spMap (Γ.R w).val.toRingHom ≫ x = xF) {U₀ U₁ : Z.Opens} {U : Z'.Opens} (h₀ : ⊤ ≤ x ⁻¹ᵁ U₀)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ U₁) (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) {a₀ : Γ(Z, U₀)} {a₁ : Γ(Z, U₁)} {s : Γ(Z', U)} {ρ : ℂ⸨X⸩}
    (e : valR xF U₀ a₀ * valR (xF ≫ φ) U s = valR xF U₁ a₁ * ρ) :
    ((valR x U₀ a₀ : Γ.R w) : ℂ⸨X⸩) * (valR (x ≫ φ) U s : Γ.R w) = (valR x U₁ a₁ : Γ.R w) * ρ := by
  subst hx
  rwa [Category.assoc, HolHom.valR_spMap _ _ _ h₀, HolHom.valR_spMap _ _ _ h₁, HolHom.valR_spMap _ _ _ h] at e

theorem ev_identity {Γ : Germs} {w : ℂ} {Z Z' : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (φ : Z ⟶ Z')
    {U₀ U₁ : Z.Opens} {U : Z'.Opens} (h₀ : ⊤ ≤ x ⁻¹ᵁ U₀)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ U₁) (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) {a₀ : Γ(Z, U₀)} {a₁ : Γ(Z, U₁)} {s : Γ(Z', U)} {T T' : ℝ}
    (hw : T < w.im) (hw' : T' < w.im) (ρ : Conv.halfRing T) (F : Conv.halfRing T') {t : Γ.R w}
    (e : ((valR x U₀ a₀ : Γ.R w) : ℂ⸨X⸩) * (valR (x ≫ φ) U s : Γ.R w) = (valR x U₁ a₁ : Γ.R w) * (ρ * F * t)) :
    valAt' (spMap (Γ.ev w).toRingHom ≫ x) U₀ a₀ * valAt' ((spMap (Γ.ev w).toRingHom ≫ x) ≫ φ) U s =
      valAt' (spMap (Γ.ev w).toRingHom ≫ x) U₁ a₁ * (Conv.ev T w hw ρ * Conv.ev T' w hw' F * Γ.ev w t) := by
  have e' : valR x U₀ a₀ * valR (x ≫ φ) U s = valR x U₁ a₁ *
      (Subalgebra.inclusion (Γ.le T w hw) ρ * Subalgebra.inclusion (Γ.le T' w hw') F * t) := Subtype.ext e
  have e'' := congrArg (Γ.ev w) e'
  rw [map_mul, map_mul, map_mul, map_mul, Γ.ev_eq, Γ.ev_eq] at e''
  rw [HolHom.valAt'_eq_valR, HolHom.valAt'_eq_valR, HolHom.valAt'_eq_valR, Category.assoc,
    HolHom.valR_spMap _ _ _ h₀, HolHom.valR_spMap _ _ _ h₁, HolHom.valR_spMap _ _ _ h]
  exact e''

theorem mem_convLaurent_of_germ {Γ : Germs} {w : ℂ} {x₀ y x₁ t : Γ.R w} {ρ F : ℂ⸨X⸩}
    (e : (x₀ : ℂ⸨X⸩) * y = x₁ * (ρ * F * t)) (h₁ : IsUnit x₁) (ht : IsUnit t) (hF : F ≠ 0)
    (hF' : F ∈ Conv.convLaurent) : ρ ∈ Conv.convLaurent := by
  have u₁ : (x₁ : ℂ⸨X⸩) ≠ 0 := (h₁.map (Γ.R w).val).ne_zero
  have u₀ : (t : ℂ⸨X⸩) ≠ 0 := (ht.map (Γ.R w).val).ne_zero
  have : ρ = x₀ * y / (x₁ * F * t) := by
    rw [e]
    field_simp
  rw [this]
  exact div_mem (mul_mem (germ_mem_convLaurent Γ w _) (germ_mem_convLaurent Γ w _))
    (mul_mem (mul_mem (germ_mem_convLaurent Γ w _) hF') (germ_mem_convLaurent Γ w _))

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} [Algebra (FractionRing ℂ) ℂ] {bF : c.F →+* ℂ} {a : ArcIn D l β ℂ (bF.comp β)}
  {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}

theorem isProper_gen (C : Chain W Λ) : IsProper (pullback.snd W.t.G.hom gen) := by
  haveI := Y.oF.proper
  have h1 : IsPullback (pullback.fst W.t.G.hom gen ≫ W.m.φ) (pullback.snd W.t.G.hom gen) Y.t.G.hom (gen ≫ χ) :=
    (IsPullback.of_hasPullback W.t.G.hom gen).paste_horiz W.m.cart.1
  have h2 : IsPullback (pullback.fst Y.oF.t.G.hom C.yF ≫ Y.m.φ) (pullback.snd Y.oF.t.G.hom C.yF) Y.t.G.hom
      (C.yF ≫ Y.j) := (IsPullback.of_hasPullback Y.oF.t.G.hom C.yF).paste_horiz Y.m.cart.1
  rw [C.yF_j] at h2
  rw [← h1.isoIsPullback_hom_snd _ _ h2]
  infer_instance

theorem valR_section_model (hL : Out.Laws) (hL2 : Out.Laws2) (C : Chain W Λ) {σ : Out.H0 W.P.U.LG.L 1}
    {f : Λ.A.V → ℂ⸨X⸩} (hf : C.Ξ.Vals σ f) {w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)}
    (hw₂ : IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) {U : Y.X.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U)
    {s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)} {r : PowerSeries ℂ} (hp : PullHyp W σ w₂ U s r)
    (v : Λ.A.V) (j : Y.t.PP.L.ι) (hj : ⊤ ≤ (C.ΦY.x v).left ⁻¹ᵁ Y.t.PP.L.U j) :
    valR (C.ΦY.x v).left _ (s j) = (r : ℂ⸨X⸩) * f v * C.ΦY.τ v j := by
  obtain ⟨k₁, hk₁⟩ := exists_chart_local (A := ℂ⟦X⟧) (C.Ξ.x v).left W.P.U.LG.isLB
  obtain ⟨w', k₂, hw', hk, hUk, hval⟩ := exists_rigIso_of_eq (A := ℂ⸨X⸩) W.m.cm W.P.bundle Y.t.PP w₂ hw₂ k₁
  obtain ⟨hx, hτ⟩ := C.isGen v
  obtain ⟨hxY, hrel⟩ := C.rel₂.2 v
  have hk₁' : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ W.P.U.LG.L.U k₁ := hx ▸ FormalValue.top_le_comp hk₁ _
  have hj' : ⊤ ≤ ((C.ΦW.x v).left ≫ W.m.φ) ⁻¹ᵁ Y.t.PP.L.U j := hxY ▸ hj
  have hd₁ := (le_div_iff (C.ΦW.x v).left W.m.φ Y.t.PP.L W.P.U.LG.L j k₁).2 ⟨hj', hk₁'⟩
  have hd₂ := (le_div_iff (C.ΦW.x v).left W.m.φ Y.t.PP.L W.t.PP.L j k₂).2 ⟨hj', hUk ▸ hk₁'⟩
  have hw := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Y.t W.t χ W.m).2 w' C.w₂ hw' C.rig₂ _ gen (C.ΦW.x v) (isProper_gen C) j k₂ hd₂
  have hover : (C.ΦW.x v).left ≫ W.t.G.hom = gen := Over.w (C.ΦW.x v)
  have h₁ : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ (W.m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) := by
    have : ⊤ ≤ ((C.ΦW.x v).left ≫ W.m.φ ≫ Y.t.G.hom) ⁻¹ᵁ U := by
      rw [W.m.cart.1.w, reassoc_of% hover]
      exact FormalValue.top_le_comp hU _
    exact fun z hz => ⟨this hz, hj' hz⟩
  have h₃ : ⊤ ≤ (C.Ξ.x v).left ⁻¹ᵁ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k₁) :=
    fun z hz => Set.mem_iInter.2 fun _ => hk₁ hz
  have h₃' : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k₁) :=
    hx ▸ FormalValue.top_le_comp h₃ _
  let V : W.t.G.left.Opens := W.m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j) ⊓
    ((LB.div (Y.t.PP.L.pull W.m.φ) W.P.U.LG.L).U (fun _ => j, k₁) ⊓
      LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k₁))
  have hV : ⊤ ≤ (C.ΦW.x v).left ⁻¹ᵁ V := fun z hz => ⟨h₁ hz, hd₁ hz, h₃' hz⟩
  have key := ((HolHom.valR_appLE _ _ _ _ _ _ hV).symm.trans (congrArg (valR (C.ΦW.x v).left V)
    (hp j k₁ V inf_le_left (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)))).trans
    (valR_res_const_res _ _ _ hover _ _ hV _ _ _)
  have hσ : valR (C.ΦW.x v).left _ (σ.f (fun _ => k₁)) = f v * C.ΦW.τ v k₂ := by
    rw [hτ k₁ k₂ hk hk₁, ← pow_one (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ _), ← hf v k₁ hk₁, hx]
    exact HolHom.valR_spMap _ _ _ h₃ _
  rw [← hxY, hrel j k₂ hd₂, ← hw, ← hval]
  refine key.trans ?_
  refine (congrArg (_ * ·) hσ).trans ?_
  change _ * (r : ℂ⸨X⸩) * _ = _
  ring

theorem valR_section_generic (hL : Out.Laws) (hL2 : Out.Laws2) (C : Chain W Λ) {σ : Out.H0 W.P.U.LG.L 1}
    {f : Λ.A.V → ℂ⸨X⸩} (hf : C.Ξ.Vals σ f) {w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)}
    {w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)}
    {w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)}
    (hw₂ : IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) (hw₁ : IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁)
    (hw₀ : IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀) {U : Y.X.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U)
    {s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)} {r : PowerSeries ℂ} (hp : PullHyp W σ w₂ U s r)
    (v : Λ.A.V) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι)
    (h₁ : ⊤ ≤ (C.ΦF.x v).left ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))
    (h₀ : ⊤ ≤ (C.ΦF.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) :
    valR (C.ΦF.x v).left _ (w₀.s (fun _ => j₀, k)).val * valR ((C.ΦF.x v).left ≫ Y.m.φ) _ (s j) =
      valR (C.ΦF.x v).left _ (w₁.s (fun _ => j, k)).val * ((r : ℂ⸨X⸩) * f v * C.Φ.τ v j₀) := by
  haveI := Y.oF.proper
  obtain ⟨hx₁, hr₁⟩ := C.rel₁.2 v
  have e₁ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Y.t Y.oF.t _ Y.m).2 w₁ C.w₁ hw₁ C.rig₁ _ C.yF (C.ΦF.x v) inferInstance j k h₁
  have e₀ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Xo.univ.t Y.oF.t _ Y.m0.toSABMap).2 w₀ C.w₀ hw₀ C.rig₀ _ C.yF (C.ΦF.x v)
    inferInstance j₀ k h₀
  have hj := ((le_div_iff _ _ _ _ _ _).1 h₁).1
  have e₂ := valR_section_model hL hL2 C hf hw₂ hU hp v j (hx₁ ▸ hj)
  have e₃ := hr₁ j k h₁
  have e₄ := (C.rel₀.2 v).2 j₀ k h₀
  have aux : ∀ {x₀ x₀' x₁ x₁' y ρ t t₀ t₁ : ℂ⸨X⸩}, x₁ = x₁' → x₀ = x₀' → y = ρ * t₁ → t₁ = x₁' * t → t₀ = x₀' * t →
      x₀ * y = x₁ * (ρ * t₀) := by
    rintro _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl
    ring
  exact aux e₁ e₀ ((congrArg (valR · _ (s j)) hx₁).trans e₂) e₃ e₄

variable (hL : Out.Laws) (hL2 : Out.Laws2) (C : Chain W Λ) {σ : Out.H0 W.P.U.LG.L 1}
  {f : Λ.A.V → ℂ⸨X⸩} (hf : C.Ξ.Vals σ f) {w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)}
  {w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)}
  {w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)}
  (hw₂ : IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂) (hw₁ : IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁)
  (hw₀ : IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀) {U : Y.X.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U)
  {s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)} {r : PowerSeries ℂ} (hp : PullHyp W σ w₂ U s r)
  {Γ : Germs} (Ψ : SpecPts C.Φ Γ) {w : ℂ} (hw : Ψ.T < w.im) (v : Λ.A.V) (xg : Sp (Γ.R w) ⟶ Y.oF.t.G.left)
  (e₀ : xg ≫ Y.m0.toSABMap.φ = (Ψ.xt w hw v).left) (eg : spMap (Γ.R w).val.toRingHom ≫ xg = (C.ΦF.x v).left)
  (hxU : ⊤ ≤ (xg ≫ Y.oF.t.G.hom) ⁻¹ᵁ (Y.j ⁻¹ᵁ U))

omit [StarRing (𝓞 E)] in
include hxU in

theorem le_section_dom {j : Y.t.PP.L.ι} (hj : ⊤ ≤ (xg ≫ Y.m.φ) ⁻¹ᵁ Y.t.PP.L.U j) :
    ⊤ ≤ (xg ≫ Y.m.φ) ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j) := by
  have : ⊤ ≤ (xg ≫ Y.m.φ ≫ Y.t.G.hom) ⁻¹ᵁ U := by
    rw [Y.m.cart.1.w]
    exact hxU
  exact fun z hz => ⟨this hz, hj hz⟩

include hL hL2 hf hw₂ hw₁ hw₀ hU hp e₀ eg hxU

theorem valR_section_germ (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι)
    (h₁ : ⊤ ≤ xg ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))
    (h₀ : ⊤ ≤ xg ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) :
    ((valR xg _ (w₀.s (fun _ => j₀, k)).val : Γ.R w) : ℂ⸨X⸩) * (valR (xg ≫ Y.m.φ) _ (s j) : Γ.R w) =
      (valR xg _ (w₁.s (fun _ => j, k)).val : Γ.R w) * ((r : ℂ⸨X⸩) * f v * Ψ.τt w v j₀) := by
  have hs := le_section_dom xg hxU ((le_div_iff _ _ _ _ _ _).1 h₁).1
  have hj₀ := ((le_div_iff _ _ _ _ _ _).1 h₀).1
  rw [e₀] at hj₀
  have h₁' := FormalValue.top_le_comp h₁ (spMap (Γ.R w).val.toRingHom)
  have h₀' := FormalValue.top_le_comp h₀ (spMap (Γ.R w).val.toRingHom)
  rw [eg] at h₁' h₀'
  rw [Ψ.τt_gen w hw v j₀ hj₀]
  exact germ_identity xg Y.m.φ eg h₀ h₁ hs (valR_section_generic hL hL2 C hf hw₂ hw₁ hw₀ hU hp v j k j₀ h₁' h₀')

theorem factor_mem_convLaurent (hv : f v ≠ 0) (hv' : f v ∈ Conv.convLaurent) : (r : ℂ⸨X⸩) ∈ Conv.convLaurent := by
  have := isLocalRing_germ Γ w
  obtain ⟨j, hj⟩ := exists_chart_local (xg ≫ Y.m.φ) Y.t.PP.isLB
  obtain ⟨k, hk⟩ := exists_chart_local xg Y.oF.t.PP.isLB
  obtain ⟨j₀, hj₀⟩ := exists_chart_local (xg ≫ Y.m0.toSABMap.φ) Xo.univ.t.PP.isLB
  have h₁ := (le_div_iff _ _ _ _ _ _).2 ⟨hj, hk⟩
  have h₀ := (le_div_iff _ _ _ _ _ _).2 ⟨hj₀, hk⟩
  have e := valR_section_germ hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg e₀ eg hxU j k j₀ h₁ h₀
  rw [e₀] at hj₀
  exact mem_convLaurent_of_germ e (FormalValue.isUnit_valR xg _ h₁ _) ((Ψ.τt_frm w hw v).1 j₀ hj₀) hv hv'

theorem valAt_section {T₀ T₂ : ℝ} (hw0 : T₀ < w.im) (hw2 : T₂ < w.im) (hF : f v ∈ Conv.halfRing T₀)
    (hr : (r : ℂ⸨X⸩) ∈ Conv.halfRing T₂) {S : ℂ} (hS : Conv.ev T₀ w hw0 ⟨_, hF⟩ = S) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι)
    (x : Sp ℂ ⟶ Y.oF.t.G.left) (hx : x = spMap (Γ.ev w).toRingHom ≫ xg)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))
    (h₀ : ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) :
    valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) =
      valAt' x _ (w₁.s (fun _ => j, k)).val *
        (Conv.ev T₂ w hw2 ⟨_, hr⟩ * S * Ψ.fr w j₀ v) := by
  subst hx hS
  have h₁' := le_of_ev Γ w xg h₁
  have h₀' := le_of_ev Γ w xg h₀
  exact ev_identity xg Y.m.φ h₀' h₁' (le_section_dom xg hxU ((le_div_iff _ _ _ _ _ _).1 h₁').1) hw2 hw0 ⟨_, hr⟩ ⟨_, hF⟩
    (valR_section_germ hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg e₀ eg hxU j k j₀ h₁' h₀')

end Generic

theorem section_value : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), AnFin Λ.A → ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → θ ≠ 0 → Λ.u.IsFn th θ → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → ⊤ ≤ χ ⁻¹ᵁ U → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ (v : Λ.A.V) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (rw * Λ.A.Sum 1 0 θ w v * Ψ.fr w j₀ v) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ th σ fam θ w₂ w₁ w₀ U s r _ hth hθ hθ0 hfn hw₂ hw₁ hw₀
    hU hp
  have hf := GlobalTheory.T.constantTermWeightZero_section_levelOne_formalSum hL hL2 E H D l Xo c O β Y _ a χ W Λ C.Ξ th σ fam θ hth hθ hfn
  refine Λ.A.exists_isConvLine.elim fun T₀ hT₀ => ?_
  have hF : ∀ v, Λ.A.FSum 1 0 θ v ∈ Conv.halfRing T₀ := fun v _ hw => (AnArc.hasSum_coeff_FSum hT₀ hθ hw v).summable
  have hUF : ⊤ ≤ C.yF ⁻¹ᵁ (Y.j ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, C.yF_j]
    exact FormalValue.top_le_comp hU _
  refine (exists_germ_lift Y bF C.yF_over C.ΦF (fun v => (C.rel₀.2 v).1) Ψ _ hUF).elim fun T₁ hlift => ?_
  have hr : (r : ℂ⸨X⸩) ∈ Conv.convLaurent :=
    (exists_fsum_ne_zero Λ.A hθ0).elim fun v hv =>
      (hlift (((T₁ + 1 : ℝ) : ℂ) * Complex.I) (by simp)).elim fun hw hl => (hl v).elim fun xg h =>
        factor_mem_convLaurent hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg h.1 h.2.1 h.2.2.1 hv
          (Conv.halfRing_le_convLaurent T₀ (hF v))
  refine (Conv.mem_convLaurent_iff_halfRing.1 hr).elim fun T₂ hT₂ => ⟨max T₀ (max T₁ T₂), fun w hw' => ?_⟩
  have hw0 := (max_lt_iff.1 hw').1
  have hw1 := (max_lt_iff.1 (max_lt_iff.1 hw').2).1
  have hw2 := (max_lt_iff.1 (max_lt_iff.1 hw').2).2
  refine ⟨Conv.ev T₂ w hw2 ⟨_, hT₂⟩, Conv.sumsAt_ev hw2 hT₂, fun v x j k j₀ hx₁ hx₂ h₁ h₀ => ?_⟩
  exact (hlift w hw1).elim fun hw hl => (hl v).elim fun xg h =>
    valAt_section hL hL2 C hf hw₂ hw₁ hw₀ hU hp Ψ hw v xg h.1 h.2.1 h.2.2.1 hw0 hw2 (hF v) hT₂
      (Conv.ev_eq_of_hasSum hw0 ⟨_, hF v⟩ (AnArc.hasSum_coeff_FSum hT₀ hθ hw0 v)) j k j₀ x (h.2.2.2 x hx₁ hx₂) h₁ h₀

end GlobalTheory.ArcSectionValue
