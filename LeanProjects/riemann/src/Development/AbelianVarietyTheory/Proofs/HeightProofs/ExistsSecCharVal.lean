import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LiftDatumAlternatingFormSignEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiFun

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CharRead

set_option maxHeartbeats 1000000 in

theorem exists_sec_char_val (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → FnAlgClosed Xo c → ∀ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, (∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1) → (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1) → (∀ h : GA D V, ∃ a : c.F, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V (h))) : ℂˣ)) → ∃ f ∈ sec Xo c 0 0, (∀ m : ℕ, (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V (h))) ^ m = 1) → f ^ m = 1) ∧ (∀ y : FrPt Xo c (CAt σ), ∃ a : c.F, evR Xo c f y = algebraMap c.F (CAt σ) a) ∧ ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → rdU U f (dict h).1 (dict h).2 = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
  intro hio hpos hA hgood hW hD hdom hcl xi h1 h2 h3
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h γ h' γ', MarkBy U V rfl dict io F ik φ h γ → MarkBy U V rfl dict io F ik φ h' γ' →
      ik (dict h).1 = ik (dict h').1 → xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) =
        xi (Matrix.GeneralLinearGroup.det (finHom V (γ' * h'))) := by
    intro h γ h' γ' hm hm' hi
    refine xi_eq_of_index F V io hio.emb _ _ hi _ _ _ _ (SetLike.ext' (hm.2.1.trans (Set.image_id _)))
      (SetLike.ext' (hm'.2.1.trans (Set.image_id _))) (φ _) (φ _) _ ?_ (htr _) (htr _) hm.2.2 hm'.2.2 xi h1 h2
    rw [← (hW (dict h).1).2]
    exact neg_ne_zero.2 (U.X _).ξ0_ne
  have hv : ∀ i : Fin F.n, ∃ a : c.F, (∃ u : GA D V, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ)) ∧
      ∀ h γ, MarkBy U V rfl dict io F ik φ h γ → ik (dict h).1 = i →
        σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
    intro i
    by_cases hex : ∃ h γ, MarkBy U V rfl dict io F ik φ h γ ∧ ik (dict h).1 = i
    · obtain ⟨h, γ, hm, hi⟩ := hex
      obtain ⟨a, ha⟩ := h3 (γ * h)
      exact ⟨a, ⟨_, ha⟩, fun h' γ' hm' hi' => by rw [ha, key h γ h' γ' hm hm' (hi.trans hi'.symm)]⟩
    · obtain ⟨a, ha⟩ := h3 1
      exact ⟨a, ⟨_, ha⟩, fun h γ hm hi => absurd ⟨h, γ, hm, hi⟩ hex⟩
  choose v hv1 hv2 using hv
  obtain ⟨f, hf, hf1, hf2⟩ := GlobalTheory.T.exists_weightZero_section_of_periodSpace_function D.host.E H Dw l Xo c σ g _ F hpos hgood
    ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat _ H l c σ hgood).2.2.2 Dw g e) hA hcl v
  refine ⟨f, hf, fun m hm => hf1 m fun i => σ.injective ?_, fun y => ?_, fun h γ hm => ?_⟩
  · obtain ⟨u, hu⟩ := hv1 i
    rw [map_pow, map_one, hu, ← Units.val_pow_eq_pow_val, hm u, Units.val_one]
  · obtain ⟨i, P, hP, hx⟩ := F.onto y.x y.x_over
    exact ⟨v i, hf2 y i P hP hx.symm⟩
  · obtain ⟨Pm, -, hP, hx, -⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hdom h⟩
    rw [← hv2 _ h γ hm rfl, ← hf2 _ _ Pm hP hx]
    exact dif_pos (hdom h)

theorem evR_ne_zero_of_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (f f' : Rul Xo c) (m : ℕ) (hm : 0 < m)
    (hf : f ^ m = 1) (k : Type) [Field k] [Algebra c.F k] (y : FrPt Xo c k) (h : evR Xo c f' y ≠ 0) :
    evR Xo c f y ≠ 0 := by
  unfold evR evalAt at h ⊢
  split_ifs at h ⊢ with hy
  · intro h0
    have h1 := congrArg (· ^ m) h0
    simp only [zero_pow hm.ne'] at h1
    rw [← map_pow, ← Pi.pow_apply, ← Pi.pow_apply, hf] at h1
    simp at h1
  · exact h

variable {D : D7}

theorem normOne_det (V : HSp D) (h : GA D V) : NormOne (D := D) (Matrix.GeneralLinearGroup.det (finHom V h)) := by
  have h1 := GlobalTheory.RecDict.det_finHom_norm V h
  have h2 : ∀ z : AfE D, barF D z = sigR (Af D.host.F) D.sp.cm.sig z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  unfold NormOne
  rw [h2, Matrix.GeneralLinearGroup.val_det_apply]
  exact h1

theorem det_rat (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ a : D.host.E, ((Matrix.GeneralLinearGroup.det (finHom V γ) : (AfE D)ˣ) : AfE D) = 1 ⊗ₜ a := by
  obtain ⟨γ', h⟩ := exists_isRat_of_mem_GQ V hγ
  refine ⟨γ'.1.det, ?_⟩
  unfold IsRat at h
  have : (finHom V γ).1 = ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom.comp
      (incA D)).mapMatrix γ'.1 := by
    unfold finHom
    rw [MonoidHom.comp_apply, h]
    rfl
  change (finHom V γ).1.det = _
  rw [this, ← RingHom.map_det]
  rfl

theorem FO_le_of_pins (Q : Par D) (h : Q.Pins) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have := h.2.2.1 (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at this
  have e : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := this
  rw [e]
  exact (Q.eO.symm y : Q.c.F).2

theorem iotaOK_of_latIsom (Q : Par D) (h : Q.Pins) (j : ℕ) (hj : InR D j) (V : HSp D) (hV : V = D.sp.W j)
    (ι : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (h1 : LatEmb V ι) (h2 : LatIsom V (Q.Dw j).EF ι) :
    IotaOK (Q.Dw j) V ι := by
  subst hV
  obtain ⟨ε, hε⟩ := h2
  let s : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (D.sp.W j).V := (D.sp.W j).frame.equivFun.symm
  have hs : ε = 1 := by
    refine sign_eq_one D Q.H (Q.Dw j) j hj h.1.2.1 h.1.2.2.1 (h.2.2.2 j hj).1 (h.2.2.2 j hj).2.1
      ((s.toLinearMap.restrictScalars (𝓞 D.host.E)) ∘ₗ ι) ε (s.injective.comp h1.1) ?_ hε
    have e1 : Set.range ((s.toLinearMap.restrictScalars (𝓞 D.host.E)) ∘ₗ ι) =
        s.toLinearMap '' (latG (D.sp.W j) 1 : Set _) := by
      rw [← h1.2, LinearMap.coe_range, ← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, (GlobalTheory.T.adelicElementLattice_full_and_completion D _ 1).2.1, Submodule.map_top, LinearEquiv.range]
  subst hs
  exact ⟨h.1.2.1, h.1.2.2.1, h1, fun x y => by simpa using hε x y⟩

set_option maxHeartbeats 1000000 in

theorem exists_fun_xiAt : ∀ (D : D7) (J : CoreJ D), LawsJ J → ∀ j, InR D j → ∀ (p : ℕ) (I : Ideal (𝓞 D.host.E)) (d : DeltaDat (J.Q.Xo j) J.Q.c 0) (xi : (AfE D)ˣ →* ℂˣ), CoverOK d p I → FnAlgClosed d.Xo₂ d.c₂ → XiOK D p xi → ∃ f : Rul d.Xo₂ d.c₂, CoverOK ({ d with cδ := f } : DeltaDat (J.Q.Xo j) J.Q.c 0) p I ∧ RootOK ({ d with cδ := f } : DeltaDat (J.Q.Xo j) J.Q.c 0) ∧ XiAt J j ({ d with cδ := f } : DeltaDat (J.Q.Xo j) J.Q.c 0) xi := by
  intro D J hJ j hj p I d xi hd hcl hxi
  obtain ⟨hp, hI, hlev, hA, hnab⟩ := hd
  have hg := J.toCore.good_σ₀
  have hpin := hJ.pins
  obtain ⟨hr, -, -, -, -, -, -, hemb, hisom, -⟩ := hJ.adPin j hj _ hg
  have hio := iotaOK_of_latIsom J.Q hpin j hj _ (hJ.spaceW j hj _ hg) _ hemb hisom
  have hpq := (exists_iotaOK D J.Q hpin j hj).2
  have hpos : 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q := by omega
  have hσ : d.c₂.F.val.toRingHom = J.σ₀.comp (d.eF.symm : d.c₂.F →+* J.Q.c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ (J.σ₀.comp (d.eF.symm : d.c₂.F →+* J.Q.c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨hr', hW⟩ := hJ.modelW j hj _ hg
  have hU := hJ.unf j hj _ hg
  let k₀ := (J.dict j J.σ₀ 1).1
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D J.Q.H (J.Q.Dw j) d.l₂ d.Xo₂ d.c₂ _ _ D.R.r hr _ hio hpos hA hg₂).2.2
    (J.x₀ j J.σ₀) (fun τ hτ => by
      have h1 := hJ.familyUniformisationBasePointOrthogonal j hj _ hg k₀ τ (((hU.2.1 k₀).2 τ).2 hτ)
      rwa [(hW k₀).1, (hU.2.1 k₀).1] at h1)
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D (J.V j J.σ₀) d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  have hM : d.l₂.M = D.host.g 0 * D.host.g 1 * p := by rw [hlev.2.1, hpin.2.1.1, hp]
  obtain ⟨m, hm, hxm⟩ := hxi.fin
  obtain ⟨f, hf, hfm, hfv, hfx⟩ := exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => hxi.tame _ (normOne_det _ u) (by
      rw [← hM]; unfold CongOne; rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu))
    (fun γ hγ => by
      obtain ⟨a, ha⟩ := det_rat _ γ hγ
      exact hxi.rat _ a ha (normOne_det _ γ))
    (fun h => ⟨⟨_, d.hF.symm ▸ FO_le_of_pins J.Q hpin (hxi.val _ (normOne_det _ h))⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m fun h => hxm _ (normOne_det _ h)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨hp, hI, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hA, hnab⟩, ⟨⟨m, hm, hfm'⟩, ?_⟩, ?_⟩
  · exact evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · change ∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F,
      evR d.Xo₂ d.c₂ f y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a
    rw [hσ]
    exact hfv
  · refine ⟨hr, fun _ => C.unf un, fun _ => dict, 1, ⟨1, one_pos, one_pow 1⟩, fun _ => ⟨hP.unf, hP.modelW,
      g, e, F, ik, φ, th, hth, ?_, fun h γ hmk => ?_⟩⟩
    · rw [← hCι, ← hCx]
      exact hdl
    · rw [one_mul]
      rw [← hCι] at hmk
      exact hfx h γ hmk

end GlobalTheory.XiFun
