import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

noncomputable section

namespace UpperTheory.FrameMove

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.LieMet MonObj GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {S : Type} [CommRing S] {x : Sp S ⟶ X}
  {f : X' ⟶ X} {φ : t'.G.left ⟶ t.G.left} (m : IsGrpPullback t'.G t.G f φ) (x' : Sp S ⟶ X') (hx : x' ≫ f = x)

include m hx in
private theorem tan_push {v : Sp (DualNumber S) ⟶ t'.G.left} (hv : IsTanAtG t' x' v) : IsTanAtG t x (v ≫ φ) := by
  subst hx
  exact ⟨by rw [Category.assoc, m.1.w, ← Category.assoc, hv.1, Category.assoc],
    by rw [← Category.assoc, hv.2]; exact (grpPull_one m (Over.mk x')).symm⟩

private def pL : TanM x' t'.G →ₗ[S] TanM x t.G where
  toFun v := tanOf (tan_push m x' hx (isTan_tv v))
  map_add' v w := tan_ext (by
    subst hx
    have e : (overAt x' (DualNumber S)).hom ≫ f = (overAt (x' ≫ f) (DualNumber S)).hom := Category.assoc _ _ _
    have key : ∀ (g : Sp (DualNumber S) ⟶ X) (e : (overAt x' (DualNumber S)).hom ≫ f = g) (a b : Over.mk g ⟶ t.G),
        a.left = (tv v).left ≫ φ → b.left = (tv w).left ≫ φ → (a * b).left = (tv v * tv w).left ≫ φ := by
      rintro _ rfl a b ha hb
      exact m.2 _ _ _ a b ha hb
    exact (key _ e _ _ rfl rfl).symm)
  map_smul' a v := tan_ext (Category.assoc _ _ _)

private theorem pL_bijective : Function.Bijective (pL m x' hx) := by
  refine ⟨fun v w h => tan_ext (m.1.hom_ext (congrArg (fun z => (tv z).left) h)
    ((isTan_tv v).1.trans (isTan_tv w).1.symm)), fun w => ?_⟩
  subst hx
  have hw : (tv w).left ≫ t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ x') ≫ f :=
    (isTan_tv w).1.trans (Category.assoc _ _ _).symm
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 (Sp S) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]))
  refine ⟨tanOf (v := m.1.lift _ _ hw) ⟨m.1.lift_snd _ _ _, m.1.hom_ext ?_ ?_⟩,
    tan_ext (m.1.lift_fst _ _ _)⟩
  · rw [Category.assoc, m.1.lift_fst, (isTan_tv w).2]
    exact grpPull_one m (Over.mk x')
  · rw [Category.assoc, m.1.lift_snd, ← Category.assoc, e, Category.id_comp]
    exact (Over.w (1 : Over.mk x' ⟶ t'.G)).symm

private def pE : TanM x' t'.G ≃ₗ[S] TanM x t.G := LinearEquiv.ofBijective _ (pL_bijective m x' hx)

include m hx

private theorem tan_lift {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x w) :
    ∃ v, IsTanAtG t' x' v ∧ v ≫ φ = w := by
  obtain ⟨v, hv⟩ := (pE m x' hx).surjective (tanOf hw)
  exact ⟨_, isTan_tv v, congrArg (fun z => (tv z).left) hv⟩

private theorem comb_iff' {n : ℕ} {u : Fin n → (Sp (DualNumber S) ⟶ t'.G.left)} (hu : ∀ i, IsTanAtG t' x' (u i))
    {w : Sp (DualNumber S) ⟶ t'.G.left} (hw : IsTanAtG t' x' w) (cf : Fin n → S) :
    IsCombAtG t x (fun i => u i ≫ φ) cf (w ≫ φ) ↔ IsCombAtG t' x' u cf w := by
  refine (GlobalTheory.LieMet.isComb_iff (fun i => pE m x' hx (tanOf (hu i))) cf (pE m x' hx (tanOf hw))).trans
    (Iff.trans ?_ (GlobalTheory.LieMet.isComb_iff (fun i => tanOf (hu i)) cf (tanOf hw)).symm)
  simp only [← map_smul, ← map_sum, EmbeddingLike.apply_eq_iff_eq]

private theorem eig_iff' (ha : ∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left)
    {w : Sp (DualNumber S) ⟶ t'.G.left} (hw : IsTanAtG t' x' w) (a : 𝓞 E) (s : S) :
    (w ≫ φ) ≫ (t.act.act a).left = spMap (epsMul s) ≫ w ≫ φ ↔ w ≫ (t'.act.act a).left = spMap (epsMul s) ≫ w := by
  refine Iff.trans (eig_iff (pE m x' hx (tanOf hw)) a s) (Iff.trans ?_ (eig_iff (tanOf hw) a s).symm)
  have : pE m x' hx (actR t'.act a (tanOf hw)) = actR t.act a (pE m x' hx (tanOf hw)) := tan_ext (by
    show (w ≫ (t'.act.act a).left) ≫ φ = (w ≫ φ) ≫ (t.act.act a).left
    rw [Category.assoc, Category.assoc, ha])
  rw [← this, ← map_smul, EmbeddingLike.apply_eq_iff_eq]

private theorem frame_iff (ha : ∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left)
    {l l' : Level H} {c : Coeff l} {c' : Coeff l'} {g' : c'.F →+* S} {g : c.F →+* S}
    (hf : ∀ τ a, g (embK c τ a) = g' (embK c' τ a)) {u : Vecs Dw t' S} (hu : ∀ τ i, IsTanAtG t' x' (u τ i)) :
    LocM.IsFrame (Dw := Dw) t g x (fun τ i => u τ i ≫ φ) ↔ LocM.IsFrame t' g' x' u := by
  constructor
  · intro h
    refine ⟨fun τ i => ⟨hu τ i, fun a => ?_⟩, fun τ w hw he => ?_⟩
    · rw [← eig_iff' m x' hx ha (hu τ i), ← hf]
      exact (h.1 τ i).2 a
    · refine (existsUnique_congr fun cf => comb_iff' m x' hx (hu τ) hw cf).1
        (h.2 τ _ (tan_push m x' hx hw) fun a => ?_)
      rw [eig_iff' m x' hx ha hw, hf]
      exact he a
  · intro h
    refine ⟨fun τ i => ⟨tan_push m x' hx (hu τ i), fun a => ?_⟩, fun τ w hw he => ?_⟩
    · rw [eig_iff' m x' hx ha (hu τ i), hf]
      exact (h.1 τ i).2 a
    · obtain ⟨v, hv, rfl⟩ := tan_lift m x' hx hw
      refine (existsUnique_congr fun cf => comb_iff' m x' hx (hu τ) hv cf).2 (h.2 τ _ hv fun a => ?_)
      rw [← eig_iff' m x' hx ha hv, ← hf]
      exact he a

end UpperTheory.FrameMove

namespace UpperTheory.FrameMove

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private theorem exists_gen {U S X₀ X₁ : Scheme.{0}} {t₀ : SAB H X₀} {t₁ : SAB H X₁} {s₀ : SAB H U} {s₁ : SAB H S}
    {g : X₀ ⟶ X₁} {y : U ⟶ X₀} {a : S ⟶ X₁} {j : U ⟶ S} (μ : SABMap t₀ t₁ g) (n₀ : SABMap s₀ t₀ y)
    (n₁ : SABMap s₁ t₁ a) (h : y ≫ g = j ≫ a) :
    ∃ ψ : s₀.G.left ⟶ s₁.G.left, IsGrpPullback s₀.G s₁.G j ψ ∧ ψ ≫ n₁.φ = n₀.φ ≫ μ.φ ∧
      ∀ b, (s₀.act.act b).left ≫ ψ = ψ ≫ (s₁.act.act b).left := by
  have hc : IsGrpPullback s₀.G t₁.G (y ≫ g) (n₀.φ ≫ μ.φ) := IsGrpPullback.comp n₀.cart μ.cart
  have hw : (n₀.φ ≫ μ.φ) ≫ t₁.G.hom = (s₀.G.hom ≫ j) ≫ a := by
    rw [hc.1.w, h, Category.assoc]
  have h1 : n₁.cart.1.lift _ _ hw ≫ n₁.φ = n₀.φ ≫ μ.φ := n₁.cart.1.lift_fst _ _ _
  have h2 : n₁.cart.1.lift _ _ hw ≫ s₁.G.hom = s₀.G.hom ≫ j := n₁.cart.1.lift_snd _ _ _
  generalize n₁.cart.1.lift _ _ hw = ψ at h1 h2
  refine ⟨ψ, IsGrpPullback.cancel (φ := n₁.φ) n₁.cart (hc.congr h h1.symm) h2, h1, fun b => ?_⟩
  have a₀ : (s₀.act.act b).left ≫ n₀.φ = n₀.φ ≫ (t₀.act.act b).left := n₀.act b
  have a₁ : (s₁.act.act b).left ≫ n₁.φ = n₁.φ ≫ (t₁.act.act b).left := n₁.act b
  have a₂ : (t₀.act.act b).left ≫ μ.φ = μ.φ ≫ (t₁.act.act b).left := μ.act b
  refine n₁.cart.1.hom_ext ?_ ?_
  · show (_ ≫ ψ) ≫ n₁.φ = (ψ ≫ _) ≫ n₁.φ
    rw [Category.assoc, h1, Category.assoc, a₁, reassoc_of% h1, reassoc_of% a₀, a₂]
  · rw [Category.assoc, h2, Category.assoc, Over.w, h2, ← Category.assoc, Over.w]

end UpperTheory.FrameMove

open UpperTheory.FrameMove GlobalTheory.Published.SemiAbelianHomExtension in
theorem UpperTheory.abelian_scheme_maps_valuation :
    GlobalTheory.Published.SemiAbelianHomExtension → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l₁ l₂ : Level H} {c₁ : Coeff l₁} {c₂ : Coeff l₂} {X₀ X₁ X₂ : Scheme.{0}} {t₀ : SAB H X₀} {t₁ : SAB H X₁} {t₂ : SAB H X₂} {g₁ : X₀ ⟶ X₁} {g₂ : X₀ ⟶ X₂} (μ₁ : SABMap t₀ t₁ g₁) (μ₂ : SABMap t₀ t₂ g₂) (K : Type) [Field K] (R : ValuationSubring K), IsDiscreteValuationRing R → ∀ (y : Sp K ⟶ X₀) (a₁ : Sp R ⟶ X₁) (a₂ : Sp R ⟶ X₂), y ≫ g₁ = spMap R.subtype ≫ a₁ → y ≫ g₂ = spMap R.subtype ≫ a₂ → ∀ (φ₁ : c₁.F →+* R) (φ₂ : c₂.F →+* R), (∀ τ a, φ₁ (embK c₁ τ a) = φ₂ (embK c₂ τ a)) → ∀ f₂ : Vecs Dw t₂ R, LocM.IsFrame t₂ φ₂ a₂ f₂ → ∃ (f₁ : Vecs Dw t₁ R) (v : Vecs Dw t₀ K), LocM.IsFrame t₁ φ₁ a₁ f₁ ∧ ∀ τ i, IsTanAtG t₀ y (v τ i) ∧ v τ i ≫ μ₁.φ = f₁.bc R.subtype τ i ∧ v τ i ≫ μ₂.φ = f₂.bc R.subtype τ i := by
  intro hE E _ _ _ H Dw l₁ l₂ c₁ c₂ X₀ X₁ X₂ t₀ t₁ t₂ g₁ g₂ μ₁ μ₂ K _ R hR y a₁ a₂ h₁ h₂ φ₁ φ₂ hφ f₂ hf₂
  obtain ⟨s₀, ⟨n₀⟩⟩ := exists_sab y t₀
  obtain ⟨s₁, ⟨n₁⟩⟩ := exists_sab a₁ t₁
  obtain ⟨s₂, ⟨n₂⟩⟩ := exists_sab a₂ t₂
  obtain ⟨ψ₁, p₁, q₁, r₁⟩ := exists_gen μ₁ n₀ n₁ h₁
  obtain ⟨ψ₂, p₂, q₂, r₂⟩ := exists_gen μ₂ n₀ n₂ h₂
  have : IsOpenImmersion (spMap R.subtype) := isOpenImmersion_generic_dvr R K
  have : IsDominant (spMap R.subtype) := isDominant_generic_dvr R K
  obtain ⟨e, ⟨he, he'⟩, -⟩ := hE.existsUnique_iso_of_extensions (isNormalScheme_dvr R) s₂.semi s₁.semi p₂ p₁
  obtain ⟨_, _⟩ := quasiCompact_and_dominant (isNormalScheme_dvr R) (spMap R.subtype)
  obtain ⟨_, -⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ s₂.semi
  obtain ⟨-, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ s₁.semi
  have hact : ∀ b, s₂.act.act b ≫ e.hom = e.hom ≫ s₁.act.act b :=
    act_comp_of_isPullback p₂.1 s₂.act s₁.act s₀.act s₀.act r₂ r₁ (𝟙 _) (fun b => by simp) e.hom
      (by rw [he']; exact Category.id_comp _)
  have pe : IsGrpPullback s₂.G t₁.G (𝟙 _ ≫ a₁) (e.hom.left ≫ n₁.φ) :=
    IsGrpPullback.comp (isGrpPullback_of_iso e) n₁.cart
  have ae : ∀ b, (s₂.act.act b).left ≫ e.hom.left ≫ n₁.φ = (e.hom.left ≫ n₁.φ) ≫ (t₁.act.act b).left := fun b => by
    have a₁ : (s₁.act.act b).left ≫ n₁.φ = n₁.φ ≫ (t₁.act.act b).left := n₁.act b
    rw [← Category.assoc, ← Over.comp_left, hact, Over.comp_left, Category.assoc, Category.assoc, a₁]
  have pn : IsGrpPullback s₂.G t₂.G a₂ n₂.φ := n₂.cart
  have pn₀ : IsGrpPullback s₀.G t₀.G y n₀.φ := n₀.cart
  choose u hu hu' using fun τ i => tan_lift pn (𝟙 _) (Category.id_comp a₂) (hf₂.1 τ i).1
  obtain rfl : (fun τ i => u τ i ≫ n₂.φ) = f₂ := funext fun τ => funext fun i => hu' τ i
  have hF : LocM.IsFrame (Dw := Dw) s₂ φ₂ (𝟙 _) u :=
    (frame_iff pn (𝟙 _) (Category.id_comp a₂) n₂.act (fun _ _ => rfl) hu).1 hf₂
  choose w hw hw' using fun τ i => tan_lift p₂ (𝟙 _) (Category.id_comp _)
    (LieMet.isTan_map R.subtype (Category.comp_id _) (hu τ i))
  refine ⟨fun τ i => u τ i ≫ e.hom.left ≫ n₁.φ, fun τ i => w τ i ≫ n₀.φ,
    (frame_iff pe (𝟙 _) (by simp) ae hφ hu).2 hF, fun τ i =>
      ⟨tan_push pn₀ (𝟙 _) (Category.id_comp y) (hw τ i), ?_, ?_⟩⟩
  · rw [Vecs.bc, Category.assoc, ← q₁, ← he', Category.assoc, reassoc_of% hw' τ i]
  · rw [Vecs.bc, Category.assoc, ← q₂, reassoc_of% hw' τ i]
