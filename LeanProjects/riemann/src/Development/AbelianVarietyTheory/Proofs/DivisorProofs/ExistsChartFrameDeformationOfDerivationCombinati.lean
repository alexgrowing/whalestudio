import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentVectorsLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomDualNumberSndEqZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem GlobalTheory.HorFrame.exists_deform_of_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁) (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ {ι : Type} [Fintype ι] (d : ι → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → ∀ (Mx : ι → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →+* K) (hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K), X.F.ChartFr k _ hk Q → ∀ (θ : Γ(M.X, W₁) →+* DualNumber K) (m : ι → K), (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * ψ (d a s).snd) → ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (∑ a, m a • (ψ ∘ Mx a)) ∧ spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hk₁ _ Q₀ hQ₀ ι _ d hd Mx hMx K _ _ ψ hk Q hQ θ m hθ1 hθ2
  haveI := c.fin
  have hinj : ∀ {A B : Type} [CommRing A] [CommRing B] (f g : A →+* B), spMap f = spMap g → f = g := by
    intro A B _ _ f g h
    have := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom this
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hjs : ∀ {T : Type} [CommRing T] [Algebra c.F T] (P : FrPt Xo c T),
      frX P ≫ Y.j ≫ Y.s = spMap (algebraMap c.F T) := by
    intro T _ _ P
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, frX_snd,
      hid, Category.comp_id]
  have e1 : frX Q ≫ Y.j = spMap ψ ≫ frX Q₀ ≫ Y.j := by
    rw [hQ.over, hQ₀.over]; simp only [Category.assoc]
  have hψα : ψ.comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F K := by
    have h2 := congrArg (· ≫ Y.s) e1
    simp only [Category.assoc] at h2
    rw [hjs Q, hjs Q₀, spMap_comp'] at h2
    exact (hinj _ _ h2).symm

  let ψA : Γ(M.X, W₁) →ₐ[c.F] K := ⟨ψ, fun r => RingHom.congr_fun hψα r⟩
  have hfrX : frX Q = spMap ψ ≫ frX Q₀ := by
    refine xF_ext (Y := Y) (frX_snd Q) ?_ (by rw [e1, Category.assoc])
    rw [Category.assoc, frX_snd, spMap_comp', hψα]
  have hQx : Q.x = spMap ψ ≫ Q₀.x := by
    rw [← frX_fst, hfrX, Category.assoc, frX_fst]
  have hFQ : FrMap ψA Q₀ Q := by
    obtain ⟨Q', hQ'⟩ := exists_frMap ψA Q₀
    have hc := hQ₀.frMap hQ' (z' := (spMap ψ ≫ tau hW₁) ≫ toFlag M) (by simp only [Category.assoc]) hk
    rwa [hc.unique hQ] at hQ'

  have hdu : ∀ φ : Γ(M.X, W₁) →+* DualNumber K, (∀ s, (φ s).fst = ψ s) →
      φ.comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F (DualNumber K) := by
    intro φ hφ
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · rw [RingHom.comp_apply, hφ, ← RingHom.comp_apply, hψα]; simp [TrivSqZeroExt.algebraMap_eq_inl']
    · rw [GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero c.F (φ.comp (algebraMap c.F _)) a]; simp [TrivSqZeroExt.algebraMap_eq_inl']
  let θA : Γ(M.X, W₁) →ₐ[c.F] DualNumber K := ⟨θ, fun r => RingHom.congr_fun (hdu θ hθ1) r⟩
  obtain ⟨w, hw⟩ := exists_frMap θA Q₀
  have hwc : X.F.ChartFr k (spMap θ ≫ tau hW₁ ≫ toFlag M) (le_preimage_comp _ hk₁) w :=
    hQ₀.frMap hw rfl _
  have hwpt : spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := FlagCover.eq_ptY hwc.lies
  have hwx : w.x = spMap θ ≫ Q₀.x := by
    rw [← frX_fst, ← frX_frMap hw, Category.assoc, frX_fst]
  have hred : (GlobalTheory.FlagTan.red c K).toRingHom.comp θ = ψ := RingHom.ext fun s => hθ1 s
  have hdef : IsDef Q w := by
    obtain ⟨Q', hQ'⟩ := exists_frMap (GlobalTheory.FlagTan.red c K) w
    have hc := hwc.frMap hQ' (z' := (spMap ψ ≫ tau hW₁) ≫ toFlag M)
      (by rw [← Category.assoc, spMap_comp', hred]; simp only [Category.assoc]) hk
    show FrMap _ w Q
    rwa [hc.unique hQ] at hQ'

  have hθc1 : ∀ a s, (((dualMap ψ).comp (d a)) s).fst = ψ s := by
    intro a s; simp [dualMap, hd]
  have hTan : ∀ φ : Γ(M.X, W₁) →+* DualNumber K, (∀ s, (φ s).fst = ψ s) →
      GlobalTheory.FlagTan.IsTanX Q (spMap φ ≫ Q₀.x) := by
    intro φ hφ
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, Q₀.x_over]
      unfold sOf
      rw [spMap_comp', ← RingHom.comp_assoc, hdu φ hφ]
    · rw [← Category.assoc, spMap_comp', hQx]
      have : (GlobalTheory.FlagTan.red c K).toRingHom.comp φ = ψ := RingHom.ext fun s => hφ s
      rw [this]
  have hKSa : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) Q (spMap ((dualMap ψ).comp (d a)) ≫ Q₀.x) (ψ ∘ Mx a) := by
    intro a
    have := hMx a K ψA Q hFQ
    rwa [← Category.assoc, spMap_comp'] at this
  refine ⟨w, hdef, ?_, hwpt⟩
  rw [hwx]
  refine GlobalTheory.T.kodaira_spencer_tangent_vectors_lift (hKS K Q) (x := fun a => spMap ((dualMap ψ).comp (d a)) ≫ Q₀.x)
    (fun a => hTan _ (hθc1 a)) hKSa (hTan θ hθ1) m ?_
  intro O f h' hc
  exact GlobalTheory.T.evalRingPoint_dualNumber_snd_linear_derivation Q₀.x ψ (fun a => (dualMap ψ).comp (d a)) θ m hθc1 hθ1
    (fun s => by rw [hθ2 s]; simp [dualMap]) O f h' hc
