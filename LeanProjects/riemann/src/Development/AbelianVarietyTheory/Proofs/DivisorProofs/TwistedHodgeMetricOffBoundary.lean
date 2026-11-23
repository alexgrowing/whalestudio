import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.HodgeCarry

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi MonoidalCategory CartesianMonoidalCategory MonObj

theorem exp_zsmul {V Q : Type} [AddCommGroup V] [Group Q] (e : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (n : ℤ) (z : V) : e (n • z) = e z ^ n := by
  let F : V →+ Additive Q := AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) (fun z w => by rw [he]; rfl)
  have := congrArg Additive.toMul (F.map_zsmul n z)
  simpa [F] using this

theorem compare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    (hsm : Smooth G.hom) {f₁ f₂ : S' ⟶ S} {π₁ π₂ : G'.left ⟶ G.left} (h₁ : IsGrpPullback G' G f₁ π₁)
    (h₂ : IsGrpPullback G' G f₂ π₂) (x : Sp ℂ ⟶ S') {y₁ y₂ : Sp ℂ ⟶ S} (hy₁ : x ≫ f₁ = y₁) (hy₂ : x ≫ f₂ = y₂)
    {g : ℕ} {L₁ L₂ : Type} [AddCommGroup L₁] [AddCommGroup L₂] (P₁ : L₁ →+ (Fin g → ℂ)) (P₂ : L₂ →+ (Fin g → ℂ))
    (iP₁ : Function.Injective P₁) (iP₂ : Function.Injective P₂) (dP₁ : DiscreteTopology P₁.range)
    (dP₂ : DiscreteTopology P₂.range) (e₁ : (Fin g → ℂ) → (Over.mk y₁ ⟶ G)) (e₂ : (Fin g → ℂ) → (Over.mk y₂ ⟶ G))
    (ha₁ : ∀ z w, e₁ (z + w) = e₁ z * e₁ w) (ha₂ : ∀ z w, e₂ (z + w) = e₂ z * e₂ w)
    (hk₁ : ∀ z, e₁ z = 1 ↔ z ∈ P₁.range) (hk₂ : ∀ z, e₂ z = 1 ↔ z ∈ P₂.range)
    (hol₁ : IsHolTo Set.univ fun z => (e₁ z).left) (hol₂ : IsHolTo Set.univ fun z => (e₂ z).left)
    (hd₁ : (∀ w, ∃! v : epsPt y₁ ⟶ G, IsDerivAt0 (fun z => (e₁ z).left) w v.left) ∧
      ∀ v : epsPt y₁ ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₁ 0).left →
        ∃! w, IsDerivAt0 (fun z => (e₁ z).left) w v.left)
    (hd₂ : (∀ w, ∃! v : epsPt y₂ ⟶ G, IsDerivAt0 (fun z => (e₂ z).left) w v.left) ∧
      ∀ v : epsPt y₂ ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₂ 0).left →
        ∃! w, IsDerivAt0 (fun z => (e₂ z).left) w v.left) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : L₁ ≃ₗ[ℤ] L₂) (lift : (Fin g → ℂ) → (Over.mk x ⟶ G')),
      (∀ z, (lift z).left ≫ π₁ = (e₁ z).left ∧ (lift z).left ≫ π₂ = (e₂ (h z)).left) ∧
      (∀ a, P₂ (gam a) = h (P₁ a)) ∧
      ∀ (w : Sp (DualNumber ℂ) ⟶ G'.left) (z : Fin g → ℂ), w ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
        IsDerivAt0 (fun z => (e₁ z).left) z (w ≫ π₁) → IsDerivAt0 (fun z => (e₂ z).left) (h z) (w ≫ π₂) := by
  subst hy₁ hy₂
  obtain ⟨E₁, hE₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h₁ (Over.mk x) (x ≫ f₁) rfl
  obtain ⟨E₂, hE₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h₂ (Over.mk x) (x ≫ f₂) rfl
  have Q₁ : IsPullback (pullback.fst G'.hom x ≫ π₁) (pullback.snd G'.hom x) G.hom (x ≫ f₁) :=
    (IsPullback.of_hasPullback G'.hom x).paste_horiz h₁.1
  have Q₂ : IsPullback (pullback.fst G'.hom x ≫ π₂) (pullback.snd G'.hom x) G.hom (x ≫ f₂) :=
    (IsPullback.of_hasPullback G'.hom x).paste_horiz h₂.1
  have kfib : ∀ p : Over.mk (x ≫ f₁) ⟶ G, fibPt G p ≫ Q₁.isoPullback.inv =
      pullback.lift (E₁.symm p).left (𝟙 _) (by rw [Over.w (E₁.symm p), Category.id_comp]; rfl) := by
    intro p
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc, pullback.lift_fst, ← hE₁,
        MulEquiv.apply_symm_apply]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
      exact pullback.lift_snd _ _ _
  let ψ : pullback G.hom (x ≫ f₁) ⟶ pullback G.hom (x ≫ f₂) := Q₁.isoPullback.inv ≫ Q₂.isoPullback.hom
  let ψp : (Over.mk (x ≫ f₁) ⟶ G) →* (Over.mk (x ≫ f₂) ⟶ G) := E₂.toMonoidHom.comp E₁.symm.toMonoidHom
  have hψs : ψ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [ψ, Category.assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_inv_snd]
  have hψp : ∀ p, fibPt G p ≫ ψ = fibPt G (ψp p) := by
    intro p
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc, kfib,
        ← Category.assoc, pullback.lift_fst]
      show _ = (fibPt G (E₂ (E₁.symm p))) ≫ pullback.fst _ _
      rw [show fibPt G (E₂ (E₁.symm p)) ≫ pullback.fst _ _ = (E₂ (E₁.symm p)).left from pullback.lift_fst _ _ _, hE₂]
    · rw [Category.assoc, hψs]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres S S G G (x ≫ f₁) (x ≫ f₂) g g e₁ e₂ ψ ψp hsm ha₁ ha₂ hol₁ hol₂ hd₂
    (by
      have h0 : (fun z => e₂ z = 1) = fun z => z ∈ P₂.range := funext fun z => propext (hk₂ z)
      show DiscreteTopology (Subtype fun z => e₂ z = 1)
      rw [h0]; exact dP₂) hψs hψp
  let φ : pullback G.hom (x ≫ f₂) ⟶ pullback G.hom (x ≫ f₁) := Q₂.isoPullback.inv ≫ Q₁.isoPullback.hom
  let φp : (Over.mk (x ≫ f₂) ⟶ G) →* (Over.mk (x ≫ f₁) ⟶ G) := E₁.toMonoidHom.comp E₂.symm.toMonoidHom
  have kfib₂ : ∀ p : Over.mk (x ≫ f₂) ⟶ G, fibPt G p ≫ Q₂.isoPullback.inv =
      pullback.lift (E₂.symm p).left (𝟙 _) (by rw [Over.w (E₂.symm p), Category.id_comp]; rfl) := by
    intro p
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc, pullback.lift_fst, ← hE₂,
        MulEquiv.apply_symm_apply]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
      exact pullback.lift_snd _ _ _
  have hφs : φ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [φ, Category.assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_inv_snd]
  have hφp : ∀ p, fibPt G p ≫ φ = fibPt G (φp p) := by
    intro p
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc, kfib₂,
        ← Category.assoc, pullback.lift_fst]
      show _ = (fibPt G (E₁ (E₂.symm p))) ≫ pullback.fst _ _
      rw [show fibPt G (E₁ (E₂.symm p)) ≫ pullback.fst _ _ = (E₁ (E₂.symm p)).left from pullback.lift_fst _ _ _, hE₁]
    · rw [Category.assoc, hφs]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  obtain ⟨f', hf', -⟩ := GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres S S G G (x ≫ f₂) (x ≫ f₁) g g e₂ e₁ φ φp hsm ha₂ ha₁ hol₂ hol₁ hd₁
    (by
      have h0 : (fun z => e₁ z = 1) = fun z => z ∈ P₁.range := funext fun z => propext (hk₁ z)
      show DiscreteTopology (Subtype fun z => e₁ z = 1)
      rw [h0]; exact dP₁) hφs hφp
  have hPz : ∀ {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)) (a : ℤ) (v : L) (i : Fin g),
      P (a • v) i = (fun (_ : Fin g) (a : ℤ) => (a : ℂ)) i a * P v i := fun P a v i => by
    simp [map_zsmul, zsmul_eq_mul]
  obtain ⟨h, gam, hh1, hh2, -⟩ := GlobalTheory.ExpUniqFamily.algebraic (O := ℤ) (fun _ a => (a : ℂ)) P₁ P₂
    (hPz P₁) (hPz P₂) iP₁ iP₂ dP₁ dP₂ (fun z => E₁.symm (e₁ z)) (fun z => E₂.symm (e₂ z))
    (fun z w => by rw [ha₁, map_mul]) (fun z w => by rw [ha₂, map_mul])
    (fun z => by rw [← hk₁]; exact map_eq_one_iff _ E₁.symm.injective)
    (fun z => by rw [← hk₂]; exact map_eq_one_iff _ E₂.symm.injective)
    (fun a q => q ^ a)
    (fun a z => by
      rw [show (fun k => (a : ℂ) * z k) = a • z from funext fun k => by simp [zsmul_eq_mul], exp_zsmul _ ha₁, map_zpow])
    (fun a z => by
      rw [show (fun k => (a : ℂ) * z k) = a • z from funext fun k => by simp [zsmul_eq_mul], exp_zsmul _ ha₂, map_zpow])
    f f' (fun z => by
      rw [hf z]
      show E₂.symm (E₂ (E₁.symm (e₁ z))) = _
      rw [MulEquiv.symm_apply_apply])
    (fun z => by
      rw [hf' z]
      show E₁.symm (E₁ (E₂.symm (e₂ z))) = _
      rw [MulEquiv.symm_apply_apply])
  have hE : ∀ z, e₂ (h z) = ψp (e₁ z) := fun z => by
    have := congrArg E₂ (hh1 z)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  refine ⟨h, gam, fun z => E₁.symm (e₁ z), fun z => ⟨?_, ?_⟩, hh2, fun w z hw hd => ?_⟩
  · rw [← hE₁, MulEquiv.apply_symm_apply]
  · rw [← hE₂, hE]; rfl
  · let w₁ : Sp (DualNumber ℂ) ⟶ pullback G.hom (x ≫ f₁) := pullback.lift (w ≫ π₁)
      (spMap (algebraMap ℂ (DualNumber ℂ))) (by rw [Category.assoc, h₁.1.w, ← Category.assoc, hw, Category.assoc])
    have hfst : ∀ z, fibPt G (e₁ z) ≫ pullback.fst _ _ = (e₁ z).left := fun z => pullback.lift_fst _ _ _
    have d1 : IsDerivAt0 (fun z => fibPt G (e₁ z)) z w₁ := by
      refine GlobalTheory.FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback G.hom (x ≫ f₁))
        (fun z => pullback.lift_snd _ _ _) ?_ (pullback.lift_snd _ _ _) ?_
      · exact (congrArg (IsHolTo Set.univ) (funext hfst)).mpr hol₁
      · refine (congrArg (fun F => IsDerivAt0 F z (w₁ ≫ pullback.fst G.hom (x ≫ f₁))) (funext hfst)).mpr ?_
        rw [show w₁ ≫ pullback.fst G.hom (x ≫ f₁) = w ≫ π₁ from pullback.lift_fst _ _ _]
        exact hd
    have d2 := GlobalTheory.FibreDeriv.isDerivAt0_comp d1 (ψ ≫ pullback.fst G.hom (x ≫ f₂))
    have e1 : ∀ z, fibPt G (e₁ z) ≫ ψ ≫ pullback.fst G.hom (x ≫ f₂) = (e₂ (h z)).left := fun z => by
      rw [← Category.assoc, hψp, ← hE]; exact pullback.lift_fst _ _ _
    have e2 : w₁ ≫ ψ ≫ pullback.fst G.hom (x ≫ f₂) = w ≫ π₂ := by
      have : w₁ ≫ Q₁.isoPullback.inv = pullback.lift w (spMap (algebraMap ℂ (DualNumber ℂ))) hw := by
        rw [Iso.comp_inv_eq]
        apply pullback.hom_ext
        · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
        · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]
      simp only [ψ, Category.assoc, IsPullback.isoPullback_hom_fst]
      rw [← Category.assoc, this, ← Category.assoc, pullback.lift_fst]
    simp only [e1, e2] at d2
    exact (GlobalTheory.ExpChain.isDerivAt0_comp_linear (fun z => (e₂ z).left) hol₂ h.toLinearMap z _).1 d2

end GlobalTheory.ShFam.HodgeCarry

namespace GlobalTheory.ShFam.HodgeCarry

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie

attribute [local instance] Over.cartesianMonoidalCategory

theorem weil_along {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    {f : S' ⟶ S} {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull π)) (x : Sp ℂ ⟶ S') {y : Sp ℂ ⟶ S} (hy : x ≫ f = y)
    (n : ℤ) (p q : Over.mk x ⟶ G') (p₀ q₀ : Over.mk y ⟶ G) (u : (Γ(Sp ℂ, ⊤))ˣ) (hp : p₀.left = p.left ≫ π)
    (hq : q₀.left = q.left ≫ π) : Out.WeilIs G' L' n p q u ↔ Out.WeilIs G L n p₀ q₀ u := by
  subst hy
  exact GlobalTheory.weilIs_grpPullback_of_comm _ _ G G' f π L L' hL hL' h hw (Over.mk x) n p q p₀ q₀ u hp hq

section Good

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem lieEquiv_push (y : FrPt Xo c (CAt σ)) {x : Sp (CAt σ) ⟶ Z.X}
    (hx : GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ ≫ genι Z = x) (v : TanM (GlobalTheory.AllWt.ptF (S := CAt σ) y) Z.oF.t.G) :
    lieEquiv Z y hx (pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF (S := CAt σ) y) (ptF_fst y) v) =
      pushE Z.m (GlobalTheory.AllWt.ptF (S := CAt σ) y) hx v := by
  rw [lieEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem cxFrame_vec (y : FrPt Xo c (CAt σ)) (τ : E →+* ℂ) (j : Fin (Dw.mult τ)) :
    (cxFrame Z y).vec τ j = lieEquiv Z y (Category.assoc _ _ _).symm (tanOf (t := Xo.univ.t) (y.tan τ j)) :=
  tan_ext rfl

theorem unitary_push (T : Tw Z) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {U : Formalism.L2.PjFree.Unf Xo c σ r}
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) {a : ℝ} (ha0 : 0 < a)
    (ha : ∀ k (τ : (U.X k).Ψ), (τ.1 (-(U.X k).ξ0)).im = a) {k k₁ : U.Comp} {x : (U.X k).dom}
    {x₁ : (U.X k₁).dom} (hx : IsOrth (U.X k) x.1) (hx₁ : IsOrth (U.X k₁) x₁.1)
    (e : (cxPt Z (U.un k₁ x₁)).1 = (cxPt Z (U.un k x)).1 ≫ T.g.hom)
    {g' : EigFrame Z σ ((cxPt Z (U.un k₁ x₁)).1 ≫ genι Z)} (hg : T.Push (cxFrame Z (U.un k x)) g')
    (τ : E →+* ℂ) :
    ((cxFrame Z (U.un k₁ x₁)).co g' τ)ᴴ * (cxFrame Z (U.un k₁ x₁)).co g' τ = 1 := by
  classical
  have hjQ := Z.jQ_open
  have hptF : GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k₁ x₁) = GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x) ≫ T.r.hom := by
    refine (cancel_mono Z.jQ).1 ?_
    have e' : GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k₁ x₁) ≫ Z.jQ = (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x) ≫ Z.jQ) ≫ T.g.hom := e
    rw [e', Category.assoc, T.jQ_g, Category.assoc]
  have p := W.period k x
  have p₁ := W.period k₁ x₁
  obtain ⟨hux, hv⟩ := W.lie k x
  obtain ⟨hux₁, hv₁⟩ := W.lie k₁ x₁
  have hy₁ : GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x) ≫ pullback.fst _ _ = W.F.u (W.ik k) (W.Pm k x) := (ptF_fst (U.un k x)).trans hux
  have hy₂ : (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x) ≫ T.r.hom) ≫ pullback.fst _ _ = W.F.u (W.ik k₁) (W.Pm k₁ x₁) := by
    rw [← hptF]; exact (ptF_fst (U.un k₁ x₁)).trans hux₁
  obtain ⟨h, gam, lift, hlift, hgam, hder⟩ := compare Xo.univ.t.semi.smooth Z.m0.cart (T.ν.cart.comp Z.m0.cart)
    (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x)) hy₁ ((Category.assoc _ _ _).symm.trans hy₂)
    (W.Pm k x) (W.Pm k₁ x₁) p.2.1 p₁.2.1 p.2.2.1 p₁.2.2.1 (W.F.ex _ _) (W.F.ex _ _) (W.F.ex_add _ _ p)
    (W.F.ex_add _ _ p₁) (W.F.ex_ker _ _ p) (W.F.ex_ker _ _ p₁) (GlobalTheory.ExpChain.isHolTo_ex W.F _ _ p)
    (GlobalTheory.ExpChain.isHolTo_ex W.F _ _ p₁) (W.F.ex_diff _ _ p) (W.F.ex_diff _ _ p₁)

  have hEF : ∀ u v, (W.F.Di (W.ik k₁)).EF (gam u) (gam v) = (W.F.Di (W.ik k)).EF u v := by
    intro u v
    refine GlobalTheory.ExpUniqFamily.int_eq_of_exp _ _ fun n hn => ?_
    let c₀ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero
      (-(2 * Real.pi * Complex.I) * ((W.F.Di (W.ik k)).EF u v : ℂ) / n))
    let c₁ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero
      (-(2 * Real.pi * Complex.I) * ((W.F.Di (W.ik k₁)).EF (gam u) (gam v) : ℂ) / n))
    have w0 := W.F.ex_weil _ _ p n u v c₀ hn rfl
    have w1 := W.F.ex_weil _ _ p₁ n (gam u) (gam v) c₁ hn rfl
    have wl := (weil_along Z.m0.cart Xo.univ.t.PP.isLB Z.oF.t.PP.isLB (Z.m0.lin.imp fun _ h => h.1) _ hy₁ n
      (lift ((n : ℂ)⁻¹ • W.Pm k x u)) (lift ((n : ℂ)⁻¹ • W.Pm k x v)) _ _ _
      (hlift _).1.symm (hlift _).1.symm).2 w0
    let pν : (Fin W.g → ℂ) → (Over.mk (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x) ≫ T.r.hom) ⟶ Z.oF.t.G) := fun z =>
      Over.homMk ((lift z).left ≫ T.ν.cm.F) (by
        show ((lift z).left ≫ T.ν.cm.F) ≫ Z.oF.t.G.hom = GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x) ≫ T.r.hom
        rw [Category.assoc, T.ν.cart.1.w, ← Category.assoc, Over.w (lift z)]; rfl)
    have wν := (weil_along T.ν.cart Z.oF.t.PP.isLB Z.oF.t.PP.isLB (T.ν.lin.imp fun _ h => h.1) _ rfl n
      (lift ((n : ℂ)⁻¹ • W.Pm k x u)) (lift ((n : ℂ)⁻¹ • W.Pm k x v)) (pν _) (pν _) _ rfl rfl).1 wl
    have hpt : ∀ b, (W.F.ex _ (W.Pm k₁ x₁) ((n : ℂ)⁻¹ • W.Pm k₁ x₁ (gam b))).left =
        (pν ((n : ℂ)⁻¹ • W.Pm k x b)).left ≫ Z.m0.cm.F := fun b => by
      rw [hgam, ← map_smul]
      exact ((hlift _).2).symm.trans (Category.assoc _ _ _).symm
    have w2 := (weil_along Z.m0.cart Xo.univ.t.PP.isLB Z.oF.t.PP.isLB (Z.m0.lin.imp fun _ h => h.1) _ hy₂ n
      (pν _) (pν _) _ _ _ (hpt u) (hpt v)).1 wν
    have := GlobalTheory.weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n _ _ _ _ w2 w1
    exact (congrArg Units.val this).symm

  set A := LinearMap.toMatrix' h.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  set Hm : Matrix (Fin W.g) (Fin W.g) ℂ := ((2 * a : ℝ) : ℂ) • 1 with hHm
  have key : Aᵀ * (Hm * A.map (starRingEnd ℂ)) = Hm := GlobalTheory.UnitDet.eq_of_im_hermForm_eq _ p.2.2.2.1 _ _ (by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [← GlobalTheory.UnitDet.hermForm_mulVec, hAv, hAv, ← hgam, ← hgam, im_hermForm_orth hσ hU W ha hx₁, hEF,
      im_hermForm_orth hσ hU W ha hx])

  have hcol : ∀ b : Fin (Dw.mult τ), A *ᵥ (Pi.single (W.e.symm ⟨T.emb τ, T.ix b⟩) 1 : Fin W.g → ℂ) =
      ∑ j, (cxFrame Z (U.un k₁ x₁)).co g' τ j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    intro b
    obtain ⟨w, hwt, hw0, hwm⟩ := EigFrame.ofFrPt_v (S := CAt σ) Z (U.un k x) (Category.assoc _ _ _).symm (T.emb τ) (T.ix b)
    have d1 : IsDerivAt0 (fun z => (W.F.ex _ (W.Pm k x) z).left) (Pi.single (W.e.symm ⟨T.emb τ, T.ix b⟩) 1)
        (w ≫ Z.m0.cm.F) := by
      have := hv (T.emb τ) (T.ix b)
      rw [← hw0] at this
      exact this
    have d2 := hder w _ hwt.1 d1

    have hwt' : IsTanAtG Z.oF.t (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k₁ x₁)) (w ≫ T.ν.cm.F) := by
      rw [hptF]
      refine ⟨by rw [Category.assoc, T.ν.cart.1.w, ← Category.assoc, hwt.1, Category.assoc], ?_⟩
      rw [← Category.assoc, hwt.2]
      exact (grpPull_one T.ν.cart (Over.mk (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k x)))).symm
    let v0 : TanM (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k₁ x₁)) Z.oF.t.G := tanOf hwt'
    let L := lieEquiv Z (U.un k₁ x₁) (x := (cxPt Z (U.un k₁ x₁)).1 ≫ genι Z) (Category.assoc _ _ _).symm
    have hL : L (pushE Z.m0.toSABMap _ (ptF_fst (U.un k₁ x₁)) v0) =
        pushE Z.m _ (Category.assoc _ _ _).symm v0 := lieEquiv_push _ _ v0
    have hg' : pushE Z.m _ (Category.assoc _ _ _).symm v0 = g'.vec τ b := tan_ext (by
      show (w ≫ T.ν.cm.F) ≫ Z.m.cm.F = g'.v τ b
      rw [hg.2.2 τ b, Category.assoc, ← T.m_mu, ← Category.assoc]
      exact congrArg (· ≫ T.mu.cm.F) hwm)
    have hsum : pushE Z.m0.toSABMap _ (ptF_fst (U.un k₁ x₁)) v0 =
        ∑ j, (show CAt σ from (cxFrame Z (U.un k₁ x₁)).co g' τ j b) • tanOf (t := Xo.univ.t) ((U.un k₁ x₁).tan τ j) := by
      apply L.injective
      rw [hL, hg', (cxFrame Z (U.un k₁ x₁)).vec_eq g' τ b, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, cxFrame_vec]
      rfl
    have hcomb : IsCombAt (U.un k₁ x₁).x ((U.un k₁ x₁).u τ) (fun j => (cxFrame Z (U.un k₁ x₁)).co g' τ j b)
        (w ≫ T.ν.cm.F ≫ Z.m0.cm.F) := by
      have := (isComb_iff (t := Xo.univ.t) (fun j => tanOf ((U.un k₁ x₁).tan τ j)) _ _).2 hsum
      rw [← Category.assoc]; exact this
    have d3 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p₁ _ ((U.un k₁ x₁).u τ)
      (fun j => (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) (hv₁ τ) _ _).1 (hux₁ ▸ hcomb)
    rw [hAv]
    exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p₁).2.2 _
      ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p₁).1 _ _ d2)).unique d2 d3
  have h7 : (((2 * a : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
  have hi' : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨T.emb τ, T.ix j⟩ = W.e.symm ⟨T.emb τ, T.ix j'⟩ ↔ j = j' :=
    fun j j' => by simp
  have k1 : (of fun b b' : Fin (Dw.mult τ) => hermForm Hm (A *ᵥ (Pi.single (W.e.symm ⟨T.emb τ, T.ix b'⟩) 1))
      (A *ᵥ (Pi.single (W.e.symm ⟨T.emb τ, T.ix b⟩) 1))) =
      ((2 * a : ℝ) : ℂ) • (((cxFrame Z (U.un k₁ x₁)).co g' τ)ᴴ * (cxFrame Z (U.un k₁ x₁)).co g' τ) := by
    ext b b'
    rw [of_apply, hcol, hcol]
    simp [hHm, hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, mul_apply, mul_comm]
  have k2 : (of fun b b' : Fin (Dw.mult τ) => hermForm Hm (A *ᵥ (Pi.single (W.e.symm ⟨T.emb τ, T.ix b'⟩) 1))
      (A *ᵥ (Pi.single (W.e.symm ⟨T.emb τ, T.ix b⟩) 1))) = ((2 * a : ℝ) : ℂ) • 1 := by
    ext b b'
    rw [of_apply, GlobalTheory.UnitDet.hermForm_mulVec, key]
    simp [hHm, hermForm, Pi.single_apply, hi', one_apply, eq_comm]
  exact smul_right_injective _ h7 (k1.symm.trans k2)

theorem unitary_at (T : Tw Z) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {U : Formalism.L2.PjFree.Unf Xo c σ r}
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) {a : ℝ} (ha0 : 0 < a)
    (ha : ∀ k (τ : (U.X k).Ψ), (τ.1 (-(U.X k).ξ0)).im = a) {k k₁ : U.Comp} {x : (U.X k).dom}
    {x₁ : (U.X k₁).dom} (hx : IsOrth (U.X k) x.1) (hx₁ : IsOrth (U.X k₁) x₁.1) {y y₁ : CxPts (genStr Z) σ}
    (hy : (cxPt Z (U.un k x)).1 = y.1) (hy₁ : (cxPt Z (U.un k₁ x₁)).1 = y₁.1) (e : y₁.1 = y.1 ≫ T.g.hom)
    {f₀ : EigFrame Z σ (y.1 ≫ genι Z)} {f₁ : EigFrame Z σ (y₁.1 ≫ genι Z)}
    (hf₀ : ∀ τ i, (cxFrame Z (U.un k x)).v τ i = f₀.v τ i) (hf₁ : ∀ τ i, (cxFrame Z (U.un k₁ x₁)).v τ i = f₁.v τ i)
    {g' : EigFrame Z σ (y₁.1 ≫ genι Z)} (hg : T.Push f₀ g') (τ : E →+* ℂ) :
    (f₁.co g' τ)ᴴ * f₁.co g' τ = 1 := by
  obtain rfl : cxPt Z (U.un k x) = y := Subtype.ext hy
  obtain rfl : cxPt Z (U.un k₁ x₁) = y₁ := Subtype.ext hy₁
  have c1 : f₁.co g' τ = (cxFrame Z (U.un k₁ x₁)).co g' τ := EigFrame.co_eq fun i => by
    have : f₁.v τ = (cxFrame Z (U.un k₁ x₁)).v τ := funext fun i => (hf₁ τ i).symm
    rw [this]; exact (cxFrame Z (U.un k₁ x₁)).co_spec g' τ i
  rw [c1]
  exact unitary_push T hσ hU W ha0 ha hx hx₁ e ⟨hg.1, hg.2.1, fun τ i => by rw [hg.2.2, hf₀]⟩ τ

end Good

section FinalTheorems

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem hodgeFrame_good {σ : κ.c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb κ.c σ) {y : CxPts (genStr s.T.Z) σ}
    {f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)} (hf : IsHodgeFrame s.U y f) :
    ∃ (k : (s.U σ).Comp) (x : ((s.U σ).X k).dom), IsOrth ((s.U σ).X k) x.1 ∧
      (cxPt s.T.Z ((s.U σ).un k x)).1 = y.1 ∧ ∀ τ i, (cxFrame s.T.Z ((s.U σ).un k x)).v τ i = f.v τ i := by
  obtain ⟨ψ, σ', k, x, hψ, h2, h3, h4, h5, h6⟩ := hf
  rcases hψ with rfl | rfl
  · obtain rfl : σ' = σ := h2
    refine ⟨k, x, h4, by rw [h5, show spMap (RingHom.id ℂ) = 𝟙 _ from Spec.map_id _, Category.id_comp],
      fun τ i => by rw [h6, spMap_dualMap_id, Category.id_comp]⟩
  · exact (not_good_conj κ.c (σ := σ) hσ (h2 ▸ h3)).elim

theorem metAt_good (T : Tw s.T.Z) (x x' : ToroidalCompactificationData s) {σ : κ.c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb κ.c σ)
    (y : CxPts (genStr s.T.Z) σ) (hy : ¬ LiesIn y (genBd s.T.Z)) : T.MetAt y (x.hodge σ) (x'.hodge σ) := by
  classical
  have hy' : ¬ LiesIn (T.pt y) (genBd s.T.Z) := fun h => hy ((T.mem_genBd _).1 h)
  obtain ⟨f₀, hf₀⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hy
  obtain ⟨f₁, hf₁⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hy'
  obtain ⟨k, x₀, h4, hy0, hv0⟩ := hodgeFrame_good hσ hf₀
  obtain ⟨k₁, x₁, g4, hy1, hv1⟩ := hodgeFrame_good hσ hf₁
  obtain ⟨W⟩ := nonempty_unfWit_of_isUnf _ _ _ _ _ _ σ _ _ (s.unf σ hσ).1
  intro f f' hp τ
  obtain ⟨g', hg'⟩ := T.exists_push f₀ rfl (T.pt_ι y)
  have hun := unitary_at T hσ (s.unf σ hσ).1 W (xiR_pos D) (s.im_neg_xi σ) h4 g4 hy0 hy1 rfl hv0 hv1 hg' τ
  rw [x.hodge_gram hf₁ f' τ, x'.hodge_gram hf₀ f (T.emb τ), ← f₁.co_mul g' f' τ, hg'.co hp τ, conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc (f₁.co g' τ)ᴴ, hun, Matrix.one_mul, Matrix.submatrix_smul]
  congr 1
  rw [conjTranspose_submatrix, ← Matrix.submatrix_mul_equiv _ _ _ (finCongr (T.mult_emb τ)) _]
  rfl

end FinalTheorems

end GlobalTheory.ShFam.HodgeCarry

open GlobalTheory.ShFam.HodgeCarry in

theorem GlobalTheory.ShFam.GalCarry.hodge_metAt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ)
    (T : Tw s.T.Z) (x x' : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (y : GlobalTheory.CxPts (genStr s.T.Z) σ),
    ¬ LiesIn y (genBd s.T.Z) → T.MetAt y (x.hodge σ) (x'.hodge σ) := by
  intro D A N j S κ s T x x' σ y hy
  by_cases hσ : GoodEmb κ.c σ
  · exact metAt_good T x x' hσ y hy
  have h1 : GoodEmb κ.c ((starRingEnd ℂ).comp σ) := by
    simpa only [goodOf, if_neg hσ] using goodEmb_goodOf κ.c σ
  let yc : CxPts (genStr s.T.Z) ((starRingEnd ℂ).comp σ) :=
    ⟨spMap (starRingEnd ℂ) ≫ y.1, by rw [Category.assoc, y.2, ← Spec.map_comp]; rfl⟩
  have hyc : ¬ LiesIn yc (genBd s.T.Z) := fun h => hy ((liesIn_iff_of_comp rfl _).1 h)
  have good := metAt_good T x x' h1 yc hyc
  intro f f' hp τ
  obtain ⟨fc, hfc⟩ := f.exists_isMap (starRingEnd ℂ) (φ' := (starRingEnd ℂ).comp σ) (x' := yc.1 ≫ genι s.T.Z) rfl
    (Category.assoc _ _ _)
  have epc : (T.pt yc).1 = spMap (starRingEnd ℂ) ≫ (T.pt y).1 := Category.assoc _ _ _
  obtain ⟨fc', hfc'⟩ := f'.exists_isMap (starRingEnd ℂ) (φ' := (starRingEnd ℂ).comp σ)
    (x' := (T.pt yc).1 ≫ genι s.T.Z) rfl (by rw [epc, Category.assoc])
  have e1 := good fc fc' (hp.map hfc hfc' rfl (T.pt_ι yc)) τ
  have c1 := GlobalTheory.ShFam.ConjMet.hodge_conj (σ := σ) (σ' := (starRingEnd ℂ).comp σ) (y := T.pt y) (y' := T.pt yc) (g := f') (g' := fc') x rfl epc hfc' τ
  have c2 := GlobalTheory.ShFam.ConjMet.hodge_conj (σ := σ) (σ' := (starRingEnd ℂ).comp σ) (y := y) (y' := yc) (g := f) (g' := fc) x' rfl rfl hfc (T.emb τ)
  rw [c1, c2] at e1
  exact Matrix.map_injective (starRingEnd ℂ).injective (e1.trans (Matrix.submatrix_map _ _ _ _))
