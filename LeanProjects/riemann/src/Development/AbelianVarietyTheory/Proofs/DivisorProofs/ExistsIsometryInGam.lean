import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPsiTieOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSixth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSimInducing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves

noncomputable section

namespace GlobalTheory.CoverDatum

section Ratio

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Matrix
open GlobalTheory.ShortMove GlobalTheory.ShortMoveIso GlobalTheory.TwistTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
  (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
  (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
  (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
  (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)

set_option maxHeartbeats 1000000 in

theorem value_ratio_complex (hσ : σ = c.F.val.toRingHom) (hA : l.A = 1) (hpq : 1 ≤ Dw.p + Dw.q)
    (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k)) (hD : DictLat U V rfl dict io e F ik φ th x₀)
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀)
    (f : Rul Xo c) (hf : f ∈ sec Xo c 0 0) (c0 : ℂ) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (N : ℕ) (hN : 0 < N) (hc0 : c0 ^ N = 1)
    (hxN : ∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1)
    (hval : ∀ h γ : GA D V, MarkBy U V rfl dict io F ik φ h γ → rdU U f (dict h).1 (dict h).2 =
      c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ))
    (hxi : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (s : Sim Dw) (ρ : Xo.X ≅ Xo.X) (hρ : Xo.LevAut s ρ) (κ : GA D V) (hκ : latGHat V κ = latGHat V 1)
    (hκ' : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s.f l.M a)) + l.M • w)
    (z z' : FrPt Xo c (CAt σ)) (hz : z'.x = z.x ≫ ρ.hom) :
    toC (evR Xo c f z') = ((xi (Matrix.GeneralLinearGroup.det (finHom V κ)) : ℂˣ) : ℂ) * toC (evR Xo c f z) := by
  subst hσ
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  have hc0' : c0 ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hc0; exact zero_ne_one hc0
  have hty := (GlobalTheory.Relab.relab_good _ H l c _ hσ).2.2.2 Dw g e
  have hfree : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x →
      evR Xo c f y' = evR Xo c f y := fun K _ _ _ y y' h => by
    obtain ⟨z, z', hz, -, hz'⟩ := GlobalTheory.Frames.exists_complex_framed_pair _ _ _ _ Xo c K y y'
    have := hz' f hf 1 (by
      rw [map_one, one_mul]
      exact GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf (by simpa using hz (𝟙 _) (by simpa using h)))
    rwa [map_one, one_mul] at this
  have val₀ : ∀ h : GA D V, ∃ hx : (dict h).2 ∈ (U.X (dict h).1).dom, toC (evR Xo c f (U.un _ ⟨_, hx⟩)) =
      c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ) : ℂ) := by
    intro h
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    have hv := hval h γ ⟨hγ, hΛ, hm⟩
    rw [map_mul, map_mul, map_mul, hxi γ hγ, one_mul] at hv
    obtain ⟨hx, ex⟩ := rdU_eq U f _ _ (hv ▸ mul_ne_zero hc0' (Units.ne_zero _))
    exact ⟨hx, ex.symm.trans hv⟩
  choose hdom val₀ using val₀
  have hroot : ∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt c.F.val.toRingHom), evR Xo c f y ^ N = 1 := ⟨N, hN, fun y => by
    obtain ⟨h, hh⟩ := exists_dict_over V U dict io e F ik φ th x₀ hσ hA hpq hU hW hD hι hth hx₀ hdom y
    rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf hh]
    change toC (evR Xo c f _) ^ N = (1 : ℂ)
    rw [val₀, mul_pow, hc0, ← Units.val_pow_eq_pow_val, hxN, Units.val_one, one_mul]⟩
  have val : ∀ (h : GA D V) (i : Fin F.n) P (y : FrPt Xo c (CAt c.F.val.toRingHom)), i = ik (dict h).1 →
      IsPeriod (F.Di i) (fun j => relab c c.F.val.toRingHom (e j).1) P → y.x = F.u i P →
        toC (evR Xo c f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ) : ℂ) := by
    rintro h _ P y rfl hP hy
    obtain ⟨P₀, -, hP₀, hy₀, -⟩ := hD.1.2 (dict h).1 ⟨_, hdom h⟩
    rw [← val₀, GlobalTheory.FiniteOrderConst.const_on_period_space _ H Dw l Xo c _ f hf hfree hroot g _ F hty _ P P₀ y _ hP hP₀
      hy hy₀]
  have pt : ∀ y : FrPt Xo c (CAt c.F.val.toRingHom), ∃ k P,
      IsPeriod (F.Di (ik k)) (fun j => relab c c.F.val.toRingHom (e j).1) P ∧ y.x = F.u (ik k) P := by
    intro y
    obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y
    obtain ⟨P, -, hP, hy, -⟩ := hD.1.2 k x
    exact ⟨k, P, hP, ht.1.trans hy⟩
  have hA' : ∀ {i i' : Fin F.n} (gam : (F.Di i).La ≃ₗ[𝓞 D.host.E] (F.Di i').La) a,
      ∃ x, gam (F.t i a) = F.t i' a + l.A • x := fun gam a =>
    ⟨gam (F.t _ a) - F.t _ a, by rw [hA, one_smul, add_sub_cancel]⟩
  obtain ⟨k, P, hP, hyP⟩ := pt z
  obtain ⟨k', P', hP', hyP'⟩ := pt z'
  obtain ⟨h, hh⟩ := GlobalTheory.ShortMove.exists_marked_of_component D V H Dw l Xo _ g _ F hty _ rfl (U.X k) (ik k) (φ k) io
    (hW k) (hD.1.1 k) hι.emb hι.isom
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, -⟩ := hD.2 h
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, -⟩ := hD.2 (h * κ)
  obtain ⟨δ₁, hδu₁, hδf₁, -⟩ := GlobalTheory.MarkCoset.rational_matrix V γ₁ hγ₁
  obtain ⟨δ₂, hδu₂, hδf₂, -⟩ := GlobalTheory.MarkCoset.rational_matrix V γ₂ hγ₂
  obtain ⟨g₁, e₁, t₁, -⟩ := marked_isometry_half V l io (U.X k) (U.X (dict h).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    LinearMap.id h γ₁ 1 (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ₁ hδu₁ hδf₁ rfl (fun a _ => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) hh
    (by rw [mul_one]; exact ⟨hΛ₁, hm₁⟩)
  obtain ⟨g₂, e₂, t₂, -⟩ := marked_isometry_half V l io (U.X k) (U.X (dict (h * κ)).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    (s.f l.M) h γ₂ κ (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ₂ hδu₂ hδf₂ hκ hκ' hh
    (by rw [mul_assoc]; exact ⟨hΛ₂, hm₂⟩)
  obtain ⟨g₃, e₃, t₃⟩ := GlobalTheory.LevStab.exists_isometry_of_levAut F hρ hP hP' (hyP ▸ hz.symm.trans hyP')
  have i₁ : ik k = ik (dict h).1 := GlobalTheory.Dict.index_eq_of_marked_isometry F hpq hσ hty _ _ g₁ e₁ t₁ (hA' g₁)
  have i₂ : ik k' = ik (dict (h * κ)).1 := by
    refine GlobalTheory.Dict.index_eq_of_marked_isometry F hpq hσ hty _ _ (g₃.symm.trans g₂) (fun a b => ?_)
      (fun a ha => ?_) (hA' _)
    · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e₂, ← e₃, g₃.apply_symm_apply, g₃.apply_symm_apply]
    · obtain ⟨x, hx⟩ := t₂ a ha
      obtain ⟨z, hz⟩ := exists_eq_nsmul l (t₃ a) (sub_mem
        (GlobalTheory.LevStab.map_mem_smul_top _ g₃.toLinearMap (GlobalTheory.LevStab.map_mem_smul_top _ _
          (GlobalTheory.LevStab.map_mem_smul_top _ _ ha))) (GlobalTheory.LevStab.map_mem_smul_top _ _ ha))
      refine ⟨x - g₂ (g₃.symm z), ?_⟩
      have : F.t (ik k') a = g₃ (F.t (ik k) (s.f l.M a)) - l.M • z := by rw [← hz, sub_sub_cancel]
      rw [LinearEquiv.trans_apply, this, map_sub, map_sub, g₃.symm_apply_apply, hx, map_nsmul, map_nsmul, smul_sub,
        add_sub_assoc]
  rw [val _ _ P z i₁ hP hyP, val _ _ P' z' i₂ hP' hyP', map_mul, map_mul, map_mul, Units.val_mul]
  ring

end Ratio

section Value

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
open GlobalTheory.GeoLevel GlobalTheory.DatumInverseCharacter GlobalTheory.PinnedClassSum Formalism.L2.Host
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isometry_inGam {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev)
    (hA : d.l₂.A = 1) (hpq : 1 ≤ Dw.p + Dw.q) (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) :
    ∃ s : Sim Dw, (∀ n, s.ν n = 1) ∧ s.InGam l d.l₂ ∧
      ∀ a, (Submodule.Quotient.mk (s.f d.l₂.M a) : LaI Xo c d) = k (Submodule.Quotient.mk a) := by
  obtain ⟨hdv, hM, hp, hI, -⟩ := hd
  obtain ⟨g, hg, hk⟩ := GlobalTheory.CoverCharacter.exists_sim_inducing Dw hpq l d.l₂ d.pd d.I hdv hM hp hI hA k
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_ne_zero fun e => by rw [hM, e] at hM₂; omega
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  have hmap : ∀ f : Dw.La →ₗ[𝓞 E] Dw.La, (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) ≤ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La).comap f :=
    fun f a ha => GlobalTheory.LevStab.map_mem_smul_top _ f ha
  let σ : LevQ Dw d.l₂ ≃ₗ[𝓞 E] LevQ Dw d.l₂ := LinearEquiv.ofLinear (Submodule.mapQ _ _ (g.f d.l₂.M) (hmap _))
    (Submodule.mapQ _ _ g' (hmap _))
    (LinearMap.ext fun q => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact (Submodule.Quotient.eq _).2 (mem_of_modN Dw (natCast_mem_Mb _) (hg' a).2))
    (LinearMap.ext fun q => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact (Submodule.Quotient.eq _).2 (mem_of_modN Dw (natCast_mem_Mb _) (hg' a).1))
  obtain ⟨s, hν, hs, -⟩ := GlobalTheory.LevelIsometry.exists_isometry_inducing E H Dw d.l₂ σ
  have hs' : ∀ a, s.f d.l₂.M a - g.f d.l₂.M a ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := fun a =>
    (Submodule.Quotient.eq _).1 (hs a)
  have hA1 : l.A = 1 := Nat.dvd_one.1 (hA ▸ hdv.2.2)
  refine ⟨s, hν, ⟨by rw [hν, sub_self]; exact dvd_zero _, fun a => ?_, fun a => ⟨s.f l.A a - a, by rw [hA1, one_smul]⟩⟩,
    fun a => ?_⟩
  · have h1 := mem_of_modN Dw (natCast_mem_Mb l) (s.tower l.M d.pd hM0 hpd a)
    have h2 := mem_of_modN Dw (natCast_mem_Mb l) (g.tower l.M d.pd hM0 hpd a)
    rw [← hM] at h1 h2
    have h3 := add_mem (add_mem (sub_mem (Submodule.smul_mono_left hdv.2.1 (hs' a)) h1) h2) (hg.2.1 a)
    convert h3 using 1
    abel
  · rw [← hk, Submodule.Quotient.eq]
    exact Submodule.smul_mono_left (hI.le.trans Ideal.mul_le_right) (hs' a)

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

set_option maxHeartbeats 1000000 in

theorem psi_value (V : HSp D) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ}
    (d : DeltaDat Xo c n) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hpq : 1 ≤ Dw.p + Dw.q) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hd : d.IsLev) (hA₂ : d.l₂.A = 1) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (N : ℕ) (hN : 0 < N)
    (hxN : ∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1)
    (hrat : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1) (U₂ : _) (dict₂ : _) (c0 : ℂ) (hc0 : c0 ^ N = 1)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0)
    (ψ : (LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) →* c.Fˣ) (hψ : d.PsiTie ψ)
    (k : LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) (s : Sim Dw) (hs : s.InGam l d.l₂)
    (hk : ∀ a, (Submodule.Quotient.mk (s.f d.l₂.M a) : LaI Xo c d) = k (Submodule.Quotient.mk a))
    (u : GA D V) (hu : L2.Pj.gLat V u = latHat V)
    (hlift : ∀ a, ∃ w ∈ latGHat V 1,
      (finHom V u).1.mulVec (finVec V (io a)) = finVec V (io (s.f d.l₂.M a)) + d.l₂.M • w) :
    (((ψ k : c.Fˣ) : c.F) : ℂ) = (xi (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) := by
  subst hr
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, hsec, hne⟩ := hd
  have hc0' : c0 ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hc0; exact zero_ne_one hc0
  obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 1
  have hv := hval 1 γ ⟨hγ, hΛ, hm⟩
  obtain ⟨hx, -⟩ := GlobalTheory.ShortMove.rdU_eq U₂ d.cδ _ _ (hv ▸ mul_ne_zero hc0' (Units.ne_zero _))
  let z := U₂.un _ ⟨_, hx⟩
  obtain ⟨ρ, hρ⟩ := GlobalTheory.LevelActionLaws.exists_levAut hpq d.Xo₂ s hs.1
  obtain ⟨hρs, ν, -⟩ := id hρ
  obtain ⟨z', hz'⟩ := (GlobalTheory.exists_unique_frMove _ H Dw d.l₂ d.Xo₂ d.c₂ ρ.hom ν hρs _ z).1
  have h1 := value_ratio_complex V U₂ dict₂ io e₀ F ik φ th x₀ (RingHom.ext fun _ => rfl) hA₂ hpq hU hW hD hι hth
    (fun k τ hτ => by
      rw [(hW k).1, (hU.2.1 k).1]
      exact hx₀ τ (((hU.2.1 k).2 τ).1 hτ)) d.cδ hsec c0 xi N hN hc0 hxN hval hrat s ρ hρ u
    (by unfold latGHat; rw [hu, GlobalTheory.TwistTie.gLat_one]) (fun b _ => hlift b) z z' hz'.1
  have h2 : toC (evR d.Xo₂ d.c₂ d.cδ z') = (((ψ k : c.Fˣ) : c.F) : ℂ) * toC (evR d.Xo₂ d.c₂ d.cδ z) ∧
      toC (evR d.Xo₂ d.c₂ d.cδ z) ≠ 0 := by
    letI : Field (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))) := inferInstanceAs (Field ℂ)
    haveI : IsAlgClosed (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))) := inferInstanceAs (IsAlgClosed ℂ)
    exact ⟨hψ k s ρ hs (fun a => ⟨s.f d.l₂.A a - a, by rw [hA₂, one_smul]⟩) hρ hk _ z z' hz'.1, hne _ z⟩
  exact mul_right_cancel₀ h2.2 (h2.1.symm.trans h1)

end Value

section Move

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
open GlobalTheory.GeoLevel GlobalTheory.DatumInverseCharacter GlobalTheory.PinnedClassSum Formalism.L2.Host
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

set_option maxHeartbeats 1000000 in

theorem exists_move (S V : HSp D) (βS : GL (Fin S.rank) (EAf D)) (β : GL (Fin V.rank) (EAf D))
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) (e : AE D)
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}
    (d : DeltaDat Xo c n) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hpq : 1 ≤ Dw.p + Dw.q) (hd : d.IsLev) (hA₂ : d.l₂.A = 1)
    (hint : ∀ x : Fin S.rank → Dw.La, IsIntM (uMat S V βS β e fun b => io (x b)))
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) {χ : (AE D)ˣ →* Circle} {ξ : HChar D.host.E} (hχ : ChrEq χ ξ)
    (hxi : ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x →
      ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((χ x : Circle) : ℂ))
    (ht : ∀ P, ξ.TameAt P) (Q : Finset (Pl D.host.E)) (ch : ∀ P : Pl D.host.E, (kP P)ˣ →* ℂˣ)
    (hres : ∀ P ∈ Q, IsRes ξ P (ch P)) (hQ : ∀ P ∈ Q, d.I ≤ P.asIdeal)
    (hram : ∀ P, ¬ ξ.UnrAt P → P ∈ Q ∨ ∃ P' ∈ Q, Lev.IsConjPl P' P)
    (ψ : (LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) →* c.Fˣ)
    (hψ : ∀ (k : LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) (s : Sim Dw), s.InGam l d.l₂ →
      (∀ a, (Submodule.Quotient.mk (s.f d.l₂.M a) : LaI Xo c d) = k (Submodule.Quotient.mk a)) →
      ∀ u : GA D V, L2.Pj.gLat V u = latHat V → (∀ a, ∃ w ∈ latGHat V 1,
        (finHom V u).1.mulVec (finVec V (io a)) = finVec V (io (s.f d.l₂.M a)) + d.l₂.M • w) →
      (((ψ k : c.Fˣ) : c.F) : ℂ) = (xi (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ))
    (k : LaI Xo c d ≃ₗ[𝓞 D.host.E] LaI Xo c d) :
    ∃ (f : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (y : ∀ P : Pl D.host.E, GL (Fin V.rank) (kP P)),
      (∀ x, (Submodule.Quotient.mk (f x) : LaI Xo c d) = k (Submodule.Quotient.mk x)) ∧
      (∀ x x', (d.pd : ℤ) ∣ Dw.EF (f x) (f x') - Dw.EF x x') ∧
      (∀ P ∈ Q, ∀ x : Fin S.rank → Dw.La, redM P (uMat S V βS β e fun b => io (x b)) =
        redM P (uMat S V βS β e fun b => io (f (x b))) * (y P).val) ∧
      (((ψ k : c.Fˣ) : c.F) : ℂ) = ∏ P ∈ Q, ((ch P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ) := by
  obtain ⟨s, hν, hs, hk⟩ := exists_isometry_inGam d hd hA₂ hpq k
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hQ' : ∀ P ∈ Q, d.l₂.Mb ≤ P.asIdeal := fun P hP => (hd.2.2.2.1.le.trans Ideal.mul_le_right).trans (hQ P hP)
  obtain ⟨u, hu₀, hu, hus⟩ := GlobalTheory.ClassSumRule.exists_finite_of_isometry hι s hν
  obtain ⟨y, hy, hdet⟩ := exists_int_matrix hβ hu
  refine ⟨s.f d.l₂.M, fun P => Formalism.UG.bc (resS D.host.F P) y, hk, fun x x' => ?_, fun P hP x => ?_, ?_⟩
  · have := s.mult _ hM₂ x x'
    rw [hν, one_mul] at this
    exact (Int.natCast_dvd_natCast.2 (Dvd.intro_left _ hd.2.1.symm)).trans this
  · exact GlobalTheory.AdjMove.redM_uMat_move D S V βS β e _ io hint u y hy d.l₂.M P (hQ' P hP (natCast_mem_Mb d.l₂)) _ x fun b => by
      rw [← GlobalTheory.ClassSumRule.latGHat_one_eq hι.emb]
      exact hus _ hM₂ _
  · have hres' : ∀ P : Q, ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc (resS D.host.F P.1) y) : (kP P.1)ˣ) : kP P.1) =
        resS D.host.F P.1 y.1.det := fun P => ((resS D.host.F P.1).map_det _).symm
    obtain ⟨z, hz, hval⟩ := exists_root_value d.l₂ hu₀ hχ ht Q ch hres hQ' hram _ hdet _ hres'
    rw [hψ k s hs hk u hu (hus _ hM₂), hxi u z hz, hval, ← Finset.prod_coe_sort Q]

end Move

end GlobalTheory.CoverDatum
