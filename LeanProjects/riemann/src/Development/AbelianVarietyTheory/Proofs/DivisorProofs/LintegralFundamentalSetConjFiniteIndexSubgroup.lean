import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SubgroupUnfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsIsom (G : Matrix (Fin r) (Fin r) E) (h : GL (Fin r) E) : Prop :=
  ∀ v w, herm G ((h : Matrix (Fin r) (Fin r) E).mulVec v) ((h : Matrix (Fin r) (Fin r) E).mulVec w) =
    herm G v w

theorem isIsom_inv {G : Matrix (Fin r) (Fin r) E} {h : GL (Fin r) E} (hh : IsIsom G h) :
    IsIsom G h⁻¹ := by
  intro v w
  have e : ∀ u : Fin r → E,
      (h : Matrix (Fin r) (Fin r) E).mulVec (((h⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← hh, e, e]

theorem isIsom_mul {G : Matrix (Fin r) (Fin r) E} {a b : GL (Fin r) E} (ha : IsIsom G a)
    (hb : IsIsom G b) : IsIsom G (a * b) := by
  intro v w
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]

theorem isIsom_of_mem (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : IsIsom X.Gm γ :=
  (X.Γ_stab γ hγ).1

theorem gram_lact_iso (X : Data E r) {h : GL (Fin r) E} (hh : IsIsom X.Gm h) (x : Frame X.Ψ r)
    (τ : X.Ψ) : gram τ.1 X.Gm (mat (lact h x) τ) = gram τ.1 X.Gm (mat x τ) := by
  have e1 : mat (lact h x) τ = (h : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  rw [e1]
  exact GlobalTheory.FrameDom.gram_mul X.Gm X.Gm _ hh τ.1 (mat x τ)

theorem dom_lact_iso (X : Data E r) {h : GL (Fin r) E} (hh : IsIsom X.Gm h) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : lact h x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact h x) τ = (h : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [e1, Matrix.det_mul]
    exact mul_ne_zero (GlobalTheory.FrameDom.det_map_ne τ.1 h) (hx τ).1
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [gram_lact_iso X hh]

theorem isOrth_lact_iso (X : Data E r) {h : GL (Fin r) E} (hh : IsIsom X.Gm h) {x : Frame X.Ψ r}
    (ho : IsOrth X x) : IsOrth X (lact h x) := fun τ => by
  rw [gram_lact_iso X hh]; exact ho τ

theorem muF_lact_iso (X : Data E r) {h : GL (Fin r) E} (hh : IsIsom X.Gm h) (x0 : Frame X.Ψ r) :
    muF X (lact h x0) = muF X x0 := by
  have h1 : OmF X (lact h x0) = OmF X x0 := by
    ext z
    show cpt X (lact h x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom
    rw [GlobalTheory.Unfold.cpt_lact]
    refine ⟨fun hz => ?_, dom_lact_iso X hh⟩
    have := dom_lact_iso X (isIsom_inv hh) hz
    rwa [FundSetPf.lact_inv] at this
  have h2 : densF X (lact h x0) = densF X x0 := by
    funext z
    simp only [densF, dmin, GlobalTheory.Unfold.cpt_lact, gram_lact_iso X hh]
  simp only [muF, h1, h2]

end GlobalTheory.SubgroupUnfold

namespace GlobalTheory.SubgroupUnfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem tsum_indicator_satFrames (Y : Data E r) {x0' : Frame Y.Ψ r} {FF' : Set (V (nd Y))}
    (hF' : IsFundSet Y x0' FF') (δ : GL (Fin r) E) (Γ : Subgroup (GL (Fin r) E))
    (hsub : Y.Γ.map (MulAut.conj δ).toMonoidHom ≤ Γ)
    (hidx : (Y.Γ.map (MulAut.conj δ).toMonoidHom).relIndex Γ ≠ 0) (x : Frame Y.Ψ r)
    (hx : ∀ g ∈ Γ, ∃ γ' ∈ Y.Γ, lact (γ'⁻¹ * (δ⁻¹ * g)) x ∈ GlobalTheory.Unfold.satFrames Y x0' FF') :
    ∑' γ : Γ, (GlobalTheory.Unfold.satFrames Y x0' FF').indicator (1 : Frame Y.Ψ r → ℝ≥0∞)
        (lact (δ⁻¹ * (γ : GL (Fin r) E)) x) =
      ((Y.Γ.map (MulAut.conj δ).toMonoidHom).relIndex Γ : ℝ≥0∞) := by
  classical
  set S := GlobalTheory.Unfold.satFrames Y x0' FF' with hSdef
  set H := Y.Γ.map (MulAut.conj δ).toMonoidHom with hHdef
  have hmem : ∀ γ' ∈ Y.Γ, δ * γ' * δ⁻¹ ∈ Γ := fun γ' hγ' =>
    hsub ⟨γ', hγ', by simp [MulAut.conj_apply]⟩
  let A : Set Γ := {γ | lact (δ⁻¹ * (γ : GL (Fin r) E)) x ∈ S}
  let f : A → Γ ⧸ H.subgroupOf Γ := fun a => QuotientGroup.mk (a.1⁻¹)
  have inj : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [f] at hab
    rw [QuotientGroup.eq, inv_inv, Subgroup.mem_subgroupOf, Subgroup.mem_map] at hab
    obtain ⟨γ', hγ', he⟩ := hab
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at he
    have he' : (a : GL (Fin r) E) = δ * γ' * δ⁻¹ * b := mul_inv_eq_iff_eq_mul.mp he.symm
    have e : lact (δ⁻¹ * (a : GL (Fin r) E)) x = lact γ' (lact (δ⁻¹ * (b : GL (Fin r) E)) x) := by
      rw [← FundSetPf.lact_mul, he']
      congr 1
      group
    have h1 : lact (1 : GL (Fin r) E)⁻¹ (lact (δ⁻¹ * (a : GL (Fin r) E)) x) ∈ S := by
      rw [inv_one, FundSetPf.lact_one]; exact ha
    have h2 : lact γ'⁻¹ (lact (δ⁻¹ * (a : GL (Fin r) E)) x) ∈ S := by
      rw [e, FundSetPf.lact_inv]; exact hb
    have h3 := GlobalTheory.Unfold.unique_translate Y hF' Y.Γ.one_mem hγ' h1 h2
    subst h3
    have : a = b := Subtype.ext (by rw [he']; group)
    subst this
    rfl
  have surj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨γ', hγ', hm⟩ := hx ((g⁻¹ : Γ) : GL (Fin r) E) (g⁻¹).2
      let c : Γ := ⟨δ * γ'⁻¹ * δ⁻¹, hmem _ (Y.Γ.inv_mem hγ')⟩
      refine ⟨⟨c * g⁻¹, ?_⟩, ?_⟩
      · show lact (δ⁻¹ * ((c * g⁻¹ : Γ) : GL (Fin r) E)) x ∈ S
        have e : δ⁻¹ * ((c * g⁻¹ : Γ) : GL (Fin r) E) = γ'⁻¹ * (δ⁻¹ * ((g⁻¹ : Γ) : GL (Fin r) E)) := by
          simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]; exact hm
      · simp only [f]
        rw [QuotientGroup.eq, inv_inv, inv_mul_cancel_right, Subgroup.mem_subgroupOf, Subgroup.mem_map]
        exact ⟨γ'⁻¹, Y.Γ.inv_mem hγ', by simp [c, MulAut.conj_apply]⟩
  have hA : ∀ γ : Γ, S.indicator (1 : Frame Y.Ψ r → ℝ≥0∞) (lact (δ⁻¹ * (γ : GL (Fin r) E)) x) =
      A.indicator (fun _ => (1 : ℝ≥0∞)) γ := by
    intro γ
    by_cases h : γ ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show _ ∈ S from h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show _ ∉ S from h)]
  rw [tsum_congr hA, ← tsum_subtype A (fun _ => (1 : ℝ≥0∞))]
  have e2 := (Equiv.ofBijective f ⟨inj, surj⟩).tsum_eq (fun _ => (1 : ℝ≥0∞))
  rw [e2]
  have hc : Nat.card (Γ ⧸ H.subgroupOf Γ) ≠ 0 := by
    rwa [← Subgroup.index_eq_card]
  haveI : Finite (Γ ⧸ H.subgroupOf Γ) := Nat.finite_of_card_ne_zero hc
  haveI := Fintype.ofFinite (Γ ⧸ H.subgroupOf Γ)
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_eq_nat_card, Subgroup.relIndex, Subgroup.index_eq_card]

theorem ae_mem_orbit_satFrames (Y : Data E r) {x0' : Frame Y.Ψ r} (ho' : IsOrth Y x0')
    {FF' : Set (V (nd Y))} (hF' : IsFundSet Y x0' FF') {x1 : Frame Y.Ψ r} (ho1 : IsOrth Y x1)
    {h : GL (Fin r) E} (hh : IsIsom Y.Gm h) :
    ∀ᵐ z ∂muF Y x1, ∃ γ' ∈ Y.Γ, lact (γ'⁻¹ * h) (cpt Y x1 z) ∈ GlobalTheory.Unfold.satFrames Y x0' FF' := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  set S := GlobalTheory.Unfold.satFrames Y x0' FF' with hSdef
  have hS : MeasurableSet S := GlobalTheory.Unfold.measurableSet_satFrames Y ho' hF'.1 hF'.2.1
  set G' : Set (Frame Y.Ψ r) := ⋃ γ' : Y.Γ, (fun x => lact (γ'.1)⁻¹ x) ⁻¹' S with hG'def
  have hG' : MeasurableSet G' :=
    MeasurableSet.iUnion fun γ' => (GlobalTheory.Unfold.continuous_lact Y _).measurable hS
  have hmemG : ∀ y, y ∈ G' ↔ ∃ γ' ∈ Y.Γ, lact γ'⁻¹ y ∈ S := by
    intro y
    simp only [G', Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨γ', hy⟩; exact ⟨γ'.1, γ'.2, hy⟩
    · rintro ⟨γ', hγ', hy⟩; exact ⟨⟨γ', hγ'⟩, hy⟩
  set D : Set (Frame Y.Ψ r) := (fun x => lact h x) ⁻¹' G'ᶜ with hDdef
  have hD : MeasurableSet D := (GlobalTheory.Unfold.continuous_lact Y h).measurable hG'.compl
  have hGB : ∀ y, ∀ b ∈ Bor Y.Ψ r, rmul y b ∈ G' ↔ y ∈ G' := by
    intro y b hb
    simp only [hmemG, FundSetPf.lact_rmul, hSdef, GlobalTheory.Unfold.rmul_mem_satFrames_iff Y x0' FF' _ hb]
  have hDB : ∀ x ∈ Y.dom, ∀ b ∈ Bor Y.Ψ r,
      D.indicator (1 : Frame Y.Ψ r → ℝ≥0∞) (rmul x b) = D.indicator 1 x := by
    intro x _ b hb
    have hiff : rmul x b ∈ D ↔ x ∈ D := by
      simp only [D, Set.mem_preimage, Set.mem_compl_iff, FundSetPf.lact_rmul, hGB _ b hb]
    by_cases hx : x ∈ D
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hiff.1 h'))]
  have hmeasD : Measurable (D.indicator (1 : Frame Y.Ψ r → ℝ≥0∞)) := measurable_const.indicator hD
  have ho2 : IsOrth Y (lact h⁻¹ x0') := isOrth_lact_iso Y (isIsom_inv hh) ho'
  have key : ∫⁻ z, D.indicator (1 : Frame Y.Ψ r → ℝ≥0∞) (cpt Y x1 z) ∂muF Y x1 = 0 := by
    rw [GlobalTheory.FrameMeasureClosed.measInv_holds r Y x1 (lact h⁻¹ x0') ho1 ho2 _ hmeasD hDB,
      muF_lact_iso Y (isIsom_inv hh)]
    refine (lintegral_eq_zero_iff (f := fun z => D.indicator (1 : Frame Y.Ψ r → ℝ≥0∞)
      (cpt Y (lact h⁻¹ x0') z)) (hmeasD.comp (FundSetPf.cont_cpt Y _).measurable)).2 ?_
    filter_upwards [hF'.2.2.2] with z hz
    obtain ⟨z', hz', γ, hγ, b, hb, he⟩ := hz
    show D.indicator (1 : Frame Y.Ψ r → ℝ≥0∞) (cpt Y (lact h⁻¹ x0') z) = 0
    apply Set.indicator_of_notMem
    simp only [D, Set.mem_preimage, Set.mem_compl_iff, not_not, GlobalTheory.Unfold.cpt_lact,
      ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one, hmemG]
    exact ⟨γ, hγ, z', hz', b, hb, by rw [he, FundSetPf.lact_inv]⟩
  have hae := (lintegral_eq_zero_iff (f := fun z => D.indicator (1 : Frame Y.Ψ r → ℝ≥0∞)
    (cpt Y x1 z)) (hmeasD.comp (FundSetPf.cont_cpt Y x1).measurable)).1 key
  filter_upwards [hae] with z hz
  have hz' : D.indicator (1 : Frame Y.Ψ r → ℝ≥0∞) (cpt Y x1 z) = 0 := hz
  have hnot : cpt Y x1 z ∉ D := fun hm => by
    rw [Set.indicator_of_mem hm] at hz'; exact one_ne_zero hz'
  simp only [D, Set.mem_preimage, Set.mem_compl_iff, not_not, hmemG] at hnot
  obtain ⟨γ', hγ', hm⟩ := hnot
  exact ⟨γ', hγ', by rw [FundSetPf.lact_mul]; exact hm⟩

end GlobalTheory.SubgroupUnfold

namespace GlobalTheory.SubgroupUnfold

theorem lintegral_fundSet_conj_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (δ : GL (Fin r) E) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))) (Φ : Frame X.Ψ r → ℝ≥0∞), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ v w, herm X.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X.Gm v w) → X'.Γ.map (MulAut.conj δ).toMonoidHom ≤ X.Γ → (X'.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → ∫⁻ z in FF', Φ (lact δ (hΨ ▸ cpt X' x0' z)) ∂(muF X' x0') = ((X'.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ : ℝ≥0∞) * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  intro E _ _ _ r X X' hΨ δ x0 x0' FF FF' Φ hG hp hδ hsub hidx ho ho' hF hF' hΦm hΦΓ hΦB
  cases X'
  dsimp only at hΨ hG hp
  subst hΨ hG hp
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hδ' : IsIsom X.Gm δ := hδ
  have hS : MeasurableSet (GlobalTheory.Unfold.satFrames X x0' FF') :=
    GlobalTheory.Unfold.measurableSet_satFrames _ ho' hF'.1 hF'.2.1
  let ψ : Frame X.Ψ r → ℝ≥0∞ := fun x =>
    Φ x * (GlobalTheory.Unfold.satFrames X x0' FF').indicator 1 (lact δ⁻¹ x)
  have hψm : Measurable ψ :=
    hΦm.mul ((measurable_const.indicator hS).comp (GlobalTheory.Unfold.continuous_lact X δ⁻¹).measurable)
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    simp only [ψ, hΦB b hb x hx, FundSetPf.lact_rmul]
    congr 1
    by_cases hm : lact δ⁻¹ x ∈ GlobalTheory.Unfold.satFrames X x0' FF'
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem
        ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0' FF' _ hb).2 hm)]; rfl
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem
        (fun h => hm ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0' FF' _ hb).1 h))]
  have ho'X : IsOrth X x0' := ho'
  have hFF'm : @MeasurableSet (V (nd X)) _ FF' := hF'.1

  have stepA : ∫⁻ z in FF', Φ (lact δ (cpt X x0' z)) ∂muF X x0' =
      ∫⁻ z, ψ (cpt X (lact δ x0') z) ∂muF X (lact δ x0') := by
    rw [muF_lact_iso X hδ' x0', ← lintegral_indicator hFF'm]
    refine lintegral_congr fun z => ?_
    simp only [ψ, GlobalTheory.Unfold.cpt_lact, FundSetPf.lact_inv]
    by_cases hz : z ∈ FF'
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem
        ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho'X FF' z).2 hz)]
      simp
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem
        (fun h => hz ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho'X FF' z).1 h))]
      simp
  have stepB := GlobalTheory.FrameMeasureClosed.measInv_holds r X x0 (lact δ x0') ho
    (isOrth_lact_iso X hδ' ho'X) ψ hψm hψB
  have stepC := GlobalTheory.Unfold.lintegral_unfold GlobalTheory.FrameMeasureClosed.measInv_holds r X x0 ho FF hF
    ψ hψm hψB
  have hgood : ∀ᵐ z ∂muF X x0, ∀ g : X.Γ, ∃ γ' ∈ _, lact (γ'⁻¹ * (δ⁻¹ * (g : GL (Fin r) E)))
      (cpt X x0 z) ∈ GlobalTheory.Unfold.satFrames _ x0' FF' :=
    ae_all_iff.2 fun g => ae_mem_orbit_satFrames _ ho' hF' ho
      (isIsom_mul (isIsom_inv hδ') (isIsom_of_mem X g.2))
  change ∫⁻ z in FF', Φ (lact δ (cpt X x0' z)) ∂muF X x0' = _
  rw [stepA, ← stepB, stepC, mul_comm, ← lintegral_mul_const' _ _ (ENNReal.natCast_ne_top _)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem hF.1, ae_restrict_of_ae hgood] with z hz hg
  have hx : cpt X x0 z ∈ X.dom := hF.2.1 hz
  have e : ∀ γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) = Φ (cpt X x0 z) *
      (GlobalTheory.Unfold.satFrames X x0' FF').indicator 1 (lact (δ⁻¹ * γ.1) (cpt X x0 z)) := by
    intro γ
    simp only [ψ, hΦΓ γ.1 γ.2 _ hx, FundSetPf.lact_mul]
  rw [tsum_congr e, ENNReal.tsum_mul_left]
  congr 1
  exact tsum_indicator_satFrames _ hF' δ X.Γ hsub hidx _ (fun g hg' => hg ⟨g, hg'⟩)

end GlobalTheory.SubgroupUnfold
