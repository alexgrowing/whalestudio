import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleOfFieldExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section

namespace GlobalTheory.RosatiDescent

theorem exists_gen_of_rosatiAdj {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    {f g : A ⟶ A} (h : RosatiAdj A L f g) : ∃ t : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := h (default : PrimeSpectrum k)
  obtain rfl : U = ⊤ := eq_top_iff.2 fun x _ => by
    rwa [Subsingleton.elim (α := PrimeSpectrum k) x default]
  have e : rosatiφ A f g = fun i => (A ⊗ A).left.topIso.inv ≫ ((A ⊗ A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ A f g i :=
    funext fun i => ((A ⊗ A).left.topIso.inv_hom_id_assoc _).symm
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ _ ht _⟩

theorem rosatiAdj_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)} {A : Over (Sp K)}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A₀) {Φ : A.left ⟶ A₀.left}
    (h : IsGrpPullback A A₀ (spMap i) Φ) {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hw : LBIso L (L₀.pull Φ)) {f g : A ⟶ A} {f₀ g₀ : A₀ ⟶ A₀} (hf : f.left ≫ Φ = Φ ≫ f₀.left)
    (hg : g.left ≫ Φ = Φ ≫ g₀.left) (hr : RosatiAdj A L f g) : RosatiAdj A₀ L₀ f₀ g₀ := by
  have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
  let U₂ := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have u₁ : U₂.left ≫ (fst A₀ A₀).left = (fst A A).left ≫ Φ := TripleDescent.lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd A₀ A₀).left = (snd A A).left ≫ Φ := TripleDescent.lift_left_snd _ _
  have P₂ : IsPullback U₂.left (A ⊗ A).hom (A₀ ⊗ A₀).hom (spMap i) :=
    TripleDescent.isPullback_tensor h.1 h.1 _ u₁ u₂
  have v₁ : (fst A A ≫ f).left ≫ Φ = U₂.left ≫ (fst A₀ A₀ ≫ f₀).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, ← u₁, Category.assoc]
  have v₂ : (snd A A ≫ g).left ≫ Φ = U₂.left ≫ (snd A₀ A₀ ≫ g₀).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, ← u₂, Category.assoc]
  have hψ : ∀ k, rosatiφ A f g k ≫ Φ = U₂.left ≫ rosatiφ A₀ f₀ g₀ k := fun k => by
    fin_cases k
    exacts [ArcPull.mul_push h U₂.left v₁ u₂.symm, v₁, u₂.symm, ArcPull.mul_push h U₂.left u₁.symm v₂, u₁.symm, v₂]
  obtain ⟨t, ht⟩ := exists_gen_of_rosatiAdj hr
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hL₀ hL t ht
  obtain ⟨u, hu⟩ := (lb_gen_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom _ _ A₂.smooth A₂.proper A₂.geomConnected P₂).1
    (LB.LinComb L₀ (rosatiφ A₀ f₀ g₀) rosatiε) (DVR.linComb_isLB _ hL₀ _ _)
    (gen_chartPull (chartPullOut L₀ _ _ U₂.left _ hψ) c hc)
  exact fun s => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ _ hu _⟩

end GlobalTheory.RosatiDescent

theorem GlobalTheory.polOAct_descend_of_generators : ∀ (O : Type) [CommRing O] [StarRing O] (J : Type) (gen : J → O), Subring.closure (Set.range gen) = ⊤ → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → LBIso P.L (P₀.L.pull Φ) → ∀ (oa : P.OAct O) (a₀ : J → (P₀.A ⟶ P₀.A)), (∀ j, (oa.act (gen j)).left ≫ Φ = Φ ≫ (a₀ j).left) → ∃ oa₀ : P₀.OAct O, ∀ c, (oa.act c).left ≫ Φ = Φ ≫ (oa₀.act c).left := by
  intro O _ _ J gen hgen K₀ K _ _ i P₀ P Φ h hw oa a₀ ha
  have := P₀.isAb.comm
  have := P.isAb.comm
  obtain ⟨r, -, hr⟩ := oAct_descend_of_generators O J gen K₀ K i P₀.A P.A Φ (ofRingAct oa.toRingAct) a₀ hgen h ha
  exact ⟨⟨r.toRingAct, fun a => RosatiDescent.rosatiAdj_descend i P₀.isAb h P₀.isLB P.isLB hw (hr a) (hr (star a))
    (oa.rosati a)⟩, hr⟩
