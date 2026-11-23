import Development.WeilBound.CoreStatements.SesquilinearFractions.HermFormSelfEqRe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

open GlobalTheory.CompanionTheory.Ar.Fl.lie_norm_square_of_family

theorem lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  intro E _ _ _ H D R _ ω C T h L ψ σ κ r n a u hF hκ hr hu
  obtain ⟨hlin, -, -, hlam⟩ := hF
  obtain ⟨P', φ, v', uC, Hm, χ, w, ⟨hg', hpb, hLB⟩, hvo, hAH, hdw, hrr⟩ := hr
  have laws := abelianSchemeLaws_all.1
  obtain ⟨Q, ψQ, hQg, hQpb, hQLB⟩ := exists_isPolFibre laws.polBaseChange σ T.pol
  obtain ⟨rig0, hrig0⟩ := P'.rigid
  obtain ⟨u0, Hm0, χ0, -, hAH0, -, -, d20, hend0, -⟩ := thetaUnifAV_all P' rig0 hrig0
  obtain ⟨rigT, hrigT⟩ := Q.rigid
  obtain ⟨uT, HmT, χT, -, hAHT, -, -, d2T, -, -⟩ := thetaUnifAV_all Q rigT hrigT
  have := T.t.comm
  have := C.P.isAb.comm
  have hψm : ∀ b, IsMonHom (ψ b) := fun b => (hlin b).isMonHom
  choose f hfm hfc using fun b : L => @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hQpb (ψ b) (hψm b)
  choose e hem hec using fun c : OK H =>
    @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hpb (C.act.act c) (C.act.hom c)
  choose F hFl using fun b : L => @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ uT u0 (f b) (hfm b)
  choose G hGl using fun c : OK H => hend0 (e c) (hem c)
  obtain ⟨K, hK⟩ := @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ u0 uC (𝟙 P'.A) inferInstance
  have hv'T : IsTangent v' := IsVecOver.isTangent hpb hvo (C.basis.1 0)
  have hd0 : u0.IsDiff (K w) v' := by
    simpa using HodgeUniq.isDiff_comp u0 uC d20 (𝟙 P'.A) K hK hv'T hdw
  have hKH : ∀ z z', hermForm Hm0 (K z) (K z') = hermForm Hm z z' :=
    (_root_.GlobalTheory.T.weilEq_iff_hermForm_eq_complex thetaUnifAV_all laws P' P' P' P' uC uC u0 uC Hm0 Hm χ0 χ hAH0 hAH (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
      K K LinearMap.id LinearMap.id hK hK (fun z => by simp) (fun z => by simp)).1 (fun _ _ _ _ _ _ _ => Iff.rfl)
  have hkey : ∀ b b' : L, ∀ z z', hermForm HmT (F b z) (F b' z') = hermForm Hm0 (G (h b b') z) z' := by
    intro b b' z z'
    have W0 := (PairingFibre.lamEq_weilEq_over_ring laws R C.P C.P T.pol C.P (ψ b) (ψ b') (C.act.act (h b b'))
      (𝟙 _) (hψm b) (hψm b') (C.act.hom _) inferInstance ℂ σ).1 (hlam b b')
    have W1 := (PairingFibre.weilEq_iff hpb hpb hQpb hpb T.t.PP.isLB C.P.isLB Q.isLB P'.isLB (LBIso.symm hQLB)
      (LBIso.symm hLB) (hfc b) (hfc b') (hec (h b b'))
      (show (𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ = φ ≫ (𝟙 C.P.A : C.P.A ⟶ C.P.A).left by simp) (𝟙 (Sp ℂ))).2 (by rw [Category.id_comp]; exact W0)
    have := (_root_.GlobalTheory.T.weilEq_iff_hermForm_eq_complex thetaUnifAV_all laws P' P' Q P' u0 u0 uT u0 HmT Hm0 χT χ0 hAHT hAH0 (f b) (f b')
      (e (h b b')) (𝟙 _) (F b) (F b') (G (h b b')) LinearMap.id (hFl b) (hFl b') (hGl _) (fun z => by simp)).1 W1 z z'
    simpa using this
  have hg1 : P'.g = 1 := hg'.trans C.dim
  choose c hc using fun x : OK H => CurveAdjoint.exists_scalar hg1 (G x)
  have pa : ∀ (b : OK H) (p : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A),
      Geo.Tor.pushHom hpb _ (p ≫ e b) = Geo.Tor.pushHom hpb _ p ≫ C.act.act b := fun b p =>
    Over.OverMorphism.ext (by
      show (p.left ≫ _) ≫ _ = (p.left ≫ _) ≫ _
      rw [Category.assoc, hec, Category.assoc])
  have inj : ∀ p q : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A, Geo.Tor.pushHom hpb _ p = Geo.Tor.pushHom hpb _ q → p = q :=
    fun p q e' => SymBaseChange.pushPt_injective hpb e'
  have sc : ∀ (b : OK H) (s : ℂ) (Gs : (Fin P'.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z, Gs z = s • z) →
      (∀ z, u0.ex (G b z) = u0.ex (Gs z)) → c b = s := fun b s Gs hG hh => by
    have e' := congrFun ((hc b 1).symm.trans ((LinearMap.congr_fun (CurveAdjoint.linear_eq_of_ex u0 _ _ hh) 1).trans
      (hG 1))) ⟨0, by omega⟩
    simpa using e'
  let j : OK H →+* ℂ := RingHom.mk'
    { toFun := c
      map_one' := sc 1 1 LinearMap.id (fun z => by simp) fun z => inj _ _ (by
        rw [hGl, pa, C.act.one, Category.comp_id, LinearMap.id_apply])
      map_mul' := fun b b' => sc _ _ (G b' ∘ₗ G b) (fun z => by
        rw [LinearMap.comp_apply, hc, hc, smul_smul, mul_comm]) fun z => inj _ _ (by
          rw [LinearMap.comp_apply, hGl, hGl, hGl, pa, pa, pa, C.act.mul, Category.assoc]) }
    fun b b' => sc _ _ (G b + G b') (fun z => by
      rw [LinearMap.add_apply, hc, hc, ← add_smul]; rfl) fun z => inj _ _ (by
        rw [LinearMap.add_apply, u0.ex_add, map_mul, hGl, hGl, hGl, pa, pa, pa, C.act.add, Hom.mul_def, Hom.mul_def,
          ← Category.assoc, comp_lift])
  have hj : ∀ x, j x = c x := fun _ => rfl

  have heig : C.v ≫ C.act.act (wK H) = CMCurveTest.scaleVec ω C.v := by
    obtain ⟨u_, hu_, hprod⟩ := C.eig
    rw [hprod]
    apply Over.OverMorphism.ext
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]
    exact hu_ 0
  have hover : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (v' ≫ e (wK H)) := by
    show (v' ≫ e _).left ≫ φ = _
    rw [Over.comp_left, Category.assoc, hec, ← Category.assoc, hvo, Over.comp_left, Category.assoc]
  have hsc : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (CMCurveTest.scaleVec (σ ω) v') := by
    rw [heig]; exact CMCurveTest.isVecOver_scaleVec hvo ω
  have hvv : v' ≫ e (wK H) = CMCurveTest.scaleVec (σ ω) v' :=
    (existsUnique_isVecOver hpb.1 (C.v ≫ C.act.act (wK H))).unique hover hsc
  have hGw : G (wK H) (K w) = σ ω • K w := by
    haveI := hem (wK H)
    have h1 := HodgeUniq.isDiff_comp u0 u0 d20 (e (wK H)) (G (wK H)) (hGl _) hv'T hd0
    have h2 := CMCurveTest.isDiff_scaleVec u0 hd0 (σ ω)
    rw [← hvv] at h2
    exact HodgeUnique.eq_of_isDiff u0 (isTangent_comp hv'T (e (wK H))) h1 h2
  have hjk : K w ≠ 0 → ∀ x, c x = κ x := by
    intro hne x
    have hw : c (wK H) = σ ω := by
      have e' : (c (wK H) - σ ω) • K w = 0 := by rw [sub_smul, ← hc, hGw, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_right hne)
    obtain ⟨⟨m, k⟩, hx, -⟩ := existsUnique_coord H x
    rw [← hj, hx]
    simp only [map_add, map_mul, map_intCast]
    rw [hj, hw, hκ]
  refine ⟨Q, ψQ, fun k => v' ≫ f (a k), uT, HmT, χT, fun k => F (a k) (K w), hQpb, hQLB, hAHT,
    fun k => ⟨?_, ?_⟩, fun k k' => ?_⟩
  · rw [Over.comp_left, Category.assoc, hfc, ← Category.assoc, hvo, hu k, Category.assoc]
    rfl
  · haveI := hfm (a k)
    exact HodgeUniq.isDiff_comp uT u0 d2T (f (a k)) (F (a k)) (hFl _) hv'T hd0
  · simp only [Matrix.of_apply]
    rw [hkey, hc, hermForm_smul_left, hKH]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, hermForm Hm w w = t := ⟨_, hermForm_self_eq_re hAH.1 w⟩
    rw [ht] at hrr ⊢
    simp only [Complex.ofReal_re] at hrr
    by_cases hne : K w = 0
    · have h0 : (t : ℂ) = 0 := by rw [← ht, ← hKH, hne]; simp [hermForm]
      have h0' : t = 0 := by exact_mod_cast h0
      rw [hrr, h0']
      simp
    · rw [hjk hne, hrr]
      push_cast
      ring

end PositivityTheory.Xgf
