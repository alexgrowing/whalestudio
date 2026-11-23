import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomAddEpsMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationChartPointReductionEqSpecialFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeformationChartPointSpecMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentOfFibrePullbackTangentAtChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCombinationTangentVectorsAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationPointsDifferEpsAllOpensStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundlesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

namespace GlobalTheory.CechKS

theorem chartPt_sub : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (V : X.Opens) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) (J₀ : Type) (W₀ : J₀ → t.G.left.Opens) (j : J₀ → t.PP.L.ι) (d : J₀ → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hcov : ⨆ i, W₀ i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V)) (hWj : ∀ i, W₀ i ≤ t.PP.L.U (j i)) (hfield : ∀ i, LogKS.IsField (W₀ i) (d i)) (hlift : ∀ i (h : W₀ i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W₀ i) ((t.G.hom.appLE U.1 (W₀ i) h).hom r) = (t.G.hom.appLE U.1 (W₀ i) h).hom (D r)) (hdiff : ∀ (i i' : J₀) (O : t.G.left.Opens), O ≤ W₀ i ⊓ W₀ i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ LogKS.chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, LogKS.IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (d i O f - d i' O f) = ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (hy1 : ∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (m : A.left ⟶ t.G.left) (m' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (u : Fin n → (epsR K ⟶ A)) (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hm : IsGrpPullback A t.G x0 m) (hm' : IsGrpPullback A' t.G y1 m') (him : i ≫ m' = m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (M : LB A.left) (wg : LB.Iso (t.PP.L.pull m) M) (hwg : wg.IsGen) (i₁ i₂ : J₀) (Ω₁ Ω₂ : t.G.left.affineOpens) (hΩ₁ : Ω₁.1 ≤ W₀ i₁) (hΩ₂ : Ω₂.1 ≤ W₀ i₂) (p₁ p₂ : M.ι) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (O : A'.left.Opens) (f : Γ(A'.left, O)) (w : Fin n → (Sp (DualNumber B) ⟶ A.left)) (hx : x ≫ A.hom = spMap (baseMap K B)) (hxW : ⊤ ≤ x ⁻¹ᵁ ((m ⁻¹ᵁ Ω₁.1 ⊓ M.U p₁) ⊓ (m ⁻¹ᵁ Ω₂.1 ⊓ M.U p₂))) (hxO : ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O)) (hw : ∀ a, IsTransl (baseMap K B) x (u a) (w a)) (l₁ l₂ : Sp B ⟶ A'.left) (h₁ : IsChartPt A' m m' Ω₁.1 (d i₁ Ω₁.1) u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) (wg.s (p₁, fun _ => j i₁)) x l₁) (h₂ : IsChartPt A' m m' Ω₂.1 (d i₂ Ω₂.1) u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) (wg.s (p₂, fun _ => j i₂)) x l₂), valR l₁ O f - valR l₂ O f = algebraMap (DualNumber K) B DualNumber.eps * ∑ a, ∑ b, baseMap K B ((Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) a b) * ((valR (w b) _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val) * (valR (w a) (i ⁻¹ᵁ O) ((i.app O).hom f)).snd := by
  intro E _ _ _ H X t V U n v D Θ hv J₀ W₀ j d hcov hWj hfield hlift hdiff K _ x0 hU y1 hU' hy1 A _ A' _ m m' i u
    hi hm hm' him hu M wg hwg i₁ i₂ Ω₁ Ω₂ hΩ₁ hΩ₂ p₁ p₂ B _ _ x O f w hx hxW hxO hw l₁ l₂ h₁ h₂
  have hW₀ : ∀ k, W₀ k ≤ t.G.hom ⁻¹ᵁ U.1 := fun k p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov ▸ (le_iSup W₀ k) hp
    exact this.1
  have := t.semi.separated
  have hut : ∀ a, IsTangent (u a) := GlobalTheory.T.isTangent_of_fibre_pullback_tangent_at_chart t U v hv x0 hU A m u hm hu
  let Ω : t.G.left.affineOpens :=
    ⟨Ω₁.1 ⊓ Ω₂.1, GlobalTheory.T.isAffineOpen_inf_of_separated_over_affineOpen t.G.hom U Ω₁ Ω₂ (hΩ₁.trans (hW₀ _)) (hΩ₂.trans (hW₀ _))⟩
  have e₁ : Ω.1 ≤ Ω₁.1 := inf_le_left
  have e₂ : Ω.1 ≤ Ω₂.1 := inf_le_right
  have hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1) := fun p hp => ⟨(hxW hp).1.1, (hxW hp).2.1⟩
  obtain ⟨l₁', k₁⟩ := GlobalTheory.CechKS.exists_isChartPt t U v D hv (W₀ i₁) (hW₀ i₁) (d i₁) (hfield i₁) (hlift i₁ (hW₀ i₁)) x0 hU y1 hU' hy1
    A A' m m' u hm hm' hu Ω (e₁.trans hΩ₁) (Matrix.of fun a b => ev x0 U.1 hU (Θ a b))
    (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) (wg.s (p₁, fun _ => j i₁)) B x hx hxΩ
  obtain ⟨l₂', k₂⟩ := GlobalTheory.CechKS.exists_isChartPt t U v D hv (W₀ i₂) (hW₀ i₂) (d i₂) (hfield i₂) (hlift i₂ (hW₀ i₂)) x0 hU y1 hU' hy1
    A A' m m' u hm hm' hu Ω (e₂.trans hΩ₂) (Matrix.of fun a b => ev x0 U.1 hU (Θ a b))
    (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) (wg.s (p₂, fun _ => j i₂)) B x hx hxΩ
  obtain rfl : l₁' = l₁ := (k₁.of_le (hfield i₁) e₁ hΩ₁ hx hxΩ hut).unique hm'.1 h₁
  obtain rfl : l₂' = l₂ := (k₂.of_le (hfield i₂) e₂ hΩ₂ hx hxΩ hut).unique hm'.1 h₂
  have hwt : ∀ a, transl (baseMap K B) x (u a) = w a := fun a => (isTransl_transl _ x hx (u a)).unique (hw a)
  have hwx := fun a => (hw a).red (hut a)
  have := isAffineHom_of_field x0
  have : IsAffineHom m := MorphismProperty.of_isPullback (P := @IsAffineHom) hm.1.flip inferInstance
  obtain ⟨S, hS, hSx, hSv⟩ := GlobalTheory.T.exists_linearCombination_tangentVectors_affineOpen A.hom ⟨m ⁻¹ᵁ Ω.1, Ω.2.preimage m⟩ (baseMap K B) x hx hxΩ w
    (fun a => (hw a).w) hwx (fun a => ∑ b, baseMap K B ((Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) a b) *
      ((valR (w b) _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val))
  have hx₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) :=
    fun p hp => ⟨(hxW hp).1.2, Set.mem_iInter.2 fun _ => hWj i₁ (hΩ₁ (hxW hp).1.1)⟩
  have hx₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) :=
    fun p hp => ⟨(hxW hp).2.2, Set.mem_iInter.2 fun _ => hWj i₂ (hΩ₂ (hxW hp).2.1)⟩
  have hlog : ∀ b, (valR (w b) _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val =
      (valR (w b ≫ m) _ (t.PP.L.g (j i₁) (j i₂)).val).snd * valR (x ≫ m) _ (t.PP.L.g (j i₁) (j i₂))⁻¹.val +
      (dlogAt (baseMap K B) x (u b) (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) (wg.s (p₁, fun _ => j i₁)) -
        dlogAt (baseMap K B) x (u b) (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) (wg.s (p₂, fun _ => j i₂))) := by
    intro b
    unfold dlogAt
    rw [hwt]
    exact GlobalTheory.T.logDerivative_transitionUnits_isoLineBundles m t.PP.L M wg hwg (j i₁) (j i₂) p₁ p₂ x (w b) (hwx b) hx₁ hx₂
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := hxΩ
  have hbase : (x ≫ m) ≫ t.G.hom = spMap ((baseMap K B).comp (ev x0 U.1 hU)) ≫ LogKS.chart U := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hx, GlobalTheory.Cris.spMap_comp (ev x0 U.1 hU), Category.assoc]
    exact congrArg _ (GlobalTheory.FlagMod.spMap_ev x0 U.2 hU).symm
  rw [GlobalTheory.T.firstOrderDeformation_points_differ_eps_allOpens hi.1.w hm'.1 him U hU' Ω ((e₁.trans hΩ₁).trans (hW₀ _)) x hxΩ S hS hSx l₁' l₂' k₁.1 k₂.1 k₁.2.1 k₂.2.1
    (fun f => ⟨_, k₂.2.2 f⟩) ?_ O hxO f, hSv _ hxO]
  · simp only [Finset.sum_mul]
  · intro f
    have hd := hdiff i₁ i₂ Ω.1 (le_inf (e₁.trans hΩ₁) (e₂.trans hΩ₂)) f B _ (x ≫ m) (fun a => w a ≫ m) hbase hxm
      (fun a => GlobalTheory.T.isTranslateOfTangentVector_fibre_to_groupScheme t x0 A m hm _ (v a) (u a) (hu a) _ x hx (w a) (hw a))
    rw [valR_eq_ev _ _ hxm, map_sub, ← valR_eq_ev, ← valR_eq_ev] at hd
    rw [k₁.2.2, k₂.2.2, valR_comp_app S, hSv _ hxΩ]
    unfold chartVal
    simp only [← valR_comp_app, hwt, hlog]
    rw [add_sub_add_left_eq_sub, ← mul_sub, add_sub_add_comm, hd, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
    rw [← Finset.sum_mul, ← sub_mul, ← add_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine congrArg (· * _) (Finset.sum_congr rfl fun b _ => ?_)
    simp only [Matrix.of_apply, RingHom.comp_apply]
    ring

theorem isCechKS_of_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ a, IsTanAtG t (LogKS.chart U) (v a)) → LogKS.IsKS t V U v D Θ → ∀ (K : Type) [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1), ⊤ ≤ x0 ⁻¹ᵁ V → ∀ (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1), (∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ι : A.left ⟶ t.G.left) (ι' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (u : Fin n → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A t.G x0 ι → IsGrpPullback A' t.G y1 ι' → i ≫ ι' = ι → (∀ a, (u a).left ≫ ι = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) → ∀ (M : LB A.left), ⨆ k, M.U k = ⊤ → LBIso (t.PP.L.pull ι) M → GlobalTheory.CechKS.IsCechKS A A' i M u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) := by
  intro E _ _ _ H X t V U n v D Θ hv hKS K _ x0 hU hV y1 hU' hy1 A _ A' _ ι ι' i u hi hι hι' hιι' hu M hM hiso
  obtain ⟨J₀, W₀, j, d, hcov, hWj, hfield, hlift, hdiff⟩ := hKS
  obtain ⟨wg, hwg⟩ := hiso
  have hW₀ : ∀ k, W₀ k ≤ t.G.hom ⁻¹ᵁ U.1 := fun k p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov ▸ (le_iSup W₀ k) hp
    exact this.1
  let θ : Matrix (Fin n) (Fin n) K := Matrix.of fun a b => ev x0 U.1 hU (Θ a b)
  let lam : ∀ (_ : Σ k : J₀, {Ω : t.G.left.affineOpens // Ω.1 ≤ W₀ k} × M.ι) (B : Type) [CommRing B]
      [Algebra (DualNumber K) B], (Sp B ⟶ A.left) → (Sp B ⟶ A'.left) :=
    fun k B _ _ x => chartPt A' i ι ι' k.2.1.1.1 (d k.1 k.2.1.1.1) u θ
      (M.U k.2.2 ⊓ (t.PP.L.pull ι).U (fun _ => j k.1)) (wg.s (k.2.2, fun _ => j k.1)) x
  have hex : ∀ (k : Σ k : J₀, {Ω : t.G.left.affineOpens // Ω.1 ≤ W₀ k} × M.ι) (B : Type) [CommRing B]
      [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left), x ≫ A.hom = spMap (baseMap K B) →
      ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) →
      IsChartPt A' ι ι' k.2.1.1.1 (d k.1 k.2.1.1.1) u θ (M.U k.2.2 ⊓ (t.PP.L.pull ι).U (fun _ => j k.1))
        (wg.s (k.2.2, fun _ => j k.1)) x (lam k B x) := by
    intro k B _ _ x hx hxΩ
    exact isChartPt_chartPt _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.CechKS.exists_isChartPt t U v D hv (W₀ k.1) (hW₀ k.1) (d k.1)
      (hfield k.1) (hlift k.1 (hW₀ k.1)) x0 hU y1 hU' hy1 A A' ι ι' u hι hι' hu k.2.1.1 k.2.1.2 θ _ _ B x hx hxΩ)
  refine ⟨Σ k : J₀, {Ω : t.G.left.affineOpens // Ω.1 ≤ W₀ k} × M.ι, fun k => ι ⁻¹ᵁ k.2.1.1.1 ⊓ M.U k.2.2,
    fun k => k.2.2, lam, ?_, fun k => inf_le_right, ?_, ?_⟩
  · refine eq_top_iff.2 fun a _ => ?_
    have h1 : (ι ≫ t.G.hom).base a ∈ U.1 ⊓ V := by
      rw [hι.1.w]
      exact ⟨hU (Set.mem_univ (A.hom.base a)), hV (Set.mem_univ (A.hom.base a))⟩
    have h2 : ι.base a ∈ ⨆ k, W₀ k := by
      rw [hcov]
      exact h1
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    obtain ⟨Ω, hΩB, haΩ, hΩk⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 t.G.left.isBasis_affineOpens hk
    have h3 : a ∈ ⨆ p, M.U p := by
      rw [hM]
      trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 h3
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, ⟨⟨Ω, hΩB⟩, hΩk⟩, p⟩, haΩ, hp⟩
  · intro k B _ _ x hx hxW
    have hxΩ : ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) := fun p hp => (hxW hp).1
    have hP := hex k B x hx hxΩ
    refine ⟨hP.1, GlobalTheory.T.deformationChartPoint_reduction_eq_specialFibre hi hι'.1 hιι' hx hxΩ hP, fun B' _ _ ρ => ?_⟩
    have hx' : (spMap (ρ : B →+* B') ≫ x) ≫ A.hom = spMap (baseMap K B') := by
      rw [Category.assoc, hx]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, AlgHom.comp_algebraMap]
    have hxΩ' : ⊤ ≤ (spMap (ρ : B →+* B') ≫ x) ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) :=
      fun p _ => hxΩ (Set.mem_univ ((spMap (ρ : B →+* B')).base p))
    have hxWo : ⊤ ≤ x ⁻¹ᵁ (M.U k.2.2 ⊓ (t.PP.L.pull ι).U (fun _ => j k.1)) :=
      fun p hp => ⟨(hxW hp).2, Set.mem_iInter.2 fun _ => hWj k.1 (k.2.1.2 (hxW hp).1)⟩
    exact (GlobalTheory.T.isDeformationChartPoint_spec_map hx hxΩ hxWo (GlobalTheory.T.isTangent_of_fibre_pullback_tangent_at_chart t U v hv x0 hU A ι u hι hu) hP B' ρ).unique hι'.1 (hex k B' _ hx' hxΩ')
  · intro k k' B _ _ x O f w hx hxW hxO hw
    have h₁ : ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) := fun p hp => (hxW hp).1.1
    have h₂ : ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k'.2.1.1.1) := fun p hp => (hxW hp).2.1
    exact chartPt_sub t V U v D Θ hv J₀ W₀ j d hcov hWj hfield hlift hdiff x0 hU y1 hU' hy1 A A' ι ι' i u hi hι
      hι' hιι' hu M wg hwg k.1 k'.1 k.2.1.1 k'.2.1.1 k.2.1.2 k'.2.1.2 k.2.2 k'.2.2 B x O f w hx hxW hxO hw _ _
      (hex k B x hx h₁) (hex k' B x hx h₂)

end GlobalTheory.CechKS
