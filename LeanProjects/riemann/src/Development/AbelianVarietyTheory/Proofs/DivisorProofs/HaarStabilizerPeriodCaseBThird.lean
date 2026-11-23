import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoundedHeightReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarNonarchimedean
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeSmallSerInt

open GlobalTheory.ConeSmallSer GlobalTheory.ConeSmallCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem stabLn_mul {x : Fin n → E} {p q : UA σ J} (hp : StabLn x p) (hq : StabLn x q) : StabLn x (p * q) := by
  obtain ⟨l, hl⟩ := hp
  obtain ⟨m, hm⟩ := hq
  refine ⟨l * m, ?_⟩
  have e : mat (p * q) = mat p * mat q := rfl
  rw [e, ← Matrix.mulVec_mulVec, hm, Matrix.mulVec_smul, hl, smul_smul, Units.val_mul, mul_comm]

theorem stabLn_inv {x : Fin n → E} {p : UA σ J} (hp : StabLn x p) : StabLn x p⁻¹ := by
  obtain ⟨l, h⟩ := hp
  refine ⟨l⁻¹, ?_⟩
  have key : mat p⁻¹ *ᵥ (mat p *ᵥ incV F x) = incV F x := by
    rw [Matrix.mulVec_mulVec, GlobalTheory.ConeSmallCTReps.mat_inv_mul, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_smul] at key
  calc mat p⁻¹ *ᵥ incV F x = (l⁻¹).1 • (l.1 • mat p⁻¹ *ᵥ incV F x) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = (l⁻¹).1 • incV F x := by rw [key]

theorem norm_partSum_le {x : Fin n → E} {T S : Set (UA σ J)} (hT : IsReps T x) (hS : S ⊆ T) {f : UA σ J → ℂ}
    (hinv : ∀ p ∈ ratU σ J, StabLn x p → ∀ h, f (p * h) = f h) {b : T → ℝ} (hb : Summable b)
    {γ g : UA σ J} (hγ : γ ∈ ratU σ J) (hbd : ∀ t : T, ‖f (t.1 * (γ * g))‖ ≤ b t) :
    ‖partSum f S g‖ ≤ ∑' t, b t := by
  have hr : ∀ t : S, t.1 * γ⁻¹ ∈ ratU σ J := fun t => mul_mem (hT.1 (hS t.2)) (inv_mem hγ)
  choose r hrT hrs using fun t : S => (hT.2 _ (hr t)).exists
  let ρ : S → T := fun t => ⟨r t, hrT t⟩
  have hinj : Function.Injective ρ := by
    intro t₁ t₂ h
    have h' : r t₁ = r t₂ := congrArg Subtype.val h
    have h1 : StabLn x (t₁.1 * γ⁻¹ * (r t₁)⁻¹) := hrs t₁
    have h2 : StabLn x (t₂.1 * γ⁻¹ * (r t₂)⁻¹) := hrs t₂
    have h3 := stabLn_mul h1 (stabLn_inv h2)
    have e : t₁.1 * γ⁻¹ * (r t₁)⁻¹ * (t₂.1 * γ⁻¹ * (r t₂)⁻¹)⁻¹ = t₁.1 * t₂.1⁻¹ := by rw [h']; group
    rw [e] at h3
    refine Subtype.ext ((hT.2 t₁.1 (hT.1 (hS t₁.2))).unique ⟨hS t₁.2, 1, ?_⟩ ⟨hS t₂.2, h3⟩)
    rw [mul_inv_cancel]
    simp [mat]
  have hle : ∀ t : S, ‖f (t.1 * g)‖ ≤ b (ρ t) := fun t => by
    have e : t.1 * g = (t.1 * γ⁻¹ * (r t)⁻¹) * (r t * (γ * g)) := by group
    rw [e, hinv _ (mul_mem (hr t) (inv_mem (hT.1 (hrT t)))) (hrs t)]
    exact hbd (ρ t)
  have hs : Summable (b ∘ ρ) := hb.comp_injective hinj
  refine (tsum_of_norm_bounded hs.hasSum hle).trans ?_
  exact hs.tsum_le_tsum_of_inj ρ hinj (fun c _ => (norm_nonneg _).trans (hbd c)) (fun _ => le_rfl) hb

theorem countable_ratU' : Countable (ratU σ J) := by
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  haveI : Countable (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :=
    (MonoidHom.rangeRestrict_surjective _).countable
  refine Function.Injective.countable (f := fun x : ratU σ J => (⟨x.1.1, x.2⟩ :
    (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range)) ?_
  intro x y h
  exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))

theorem isCompact_ht_le (c : ℝ≥0) : IsCompact {g : UA σ J | ht g ≤ c} := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
    exact isClosed_eq (((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA))) continuous_const
  exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_heightGL_le F c)

theorem ctInt_partSum {d d₁ : ℕ} {W : Spc F E d} (H' : Plane E d d₁) (R : ℝ≥0)
    (hR : ∀ u ∈ unip σ W H', ∃ γ ∈ ratU σ W.J ⊓ unip σ W H', ht (γ * u) ≤ R)
    {T S : Set (UA σ W.J)} (hT : IsReps T H'.x) (hS : S ⊆ T) {f : UA σ W.J → ℂ} (hf : Measurable f)
    (hinv : ∀ p ∈ ratU σ W.J, StabLn H'.x p → ∀ h, f (p * h) = f h) (hL : LocUnifSum f T) :
    GlobalTheory.ThK.CTAdd.CTInt H' (partSum f S) := by
  intro μ 𝓕 _ _ h1 h
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ W.J
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI := countable_ratU' (σ := σ) (J := W.J)
  haveI : Countable S := Function.Injective.countable (f := fun t : S => (⟨t.1, hT.1 (hS t.2)⟩ : ratU σ W.J))
    fun x y h => Subtype.ext (congrArg (fun z : ratU σ W.J => z.1) h)
  obtain ⟨b, hb, hbd⟩ := hL _ (isCompact_ht_le (σ := σ) (J := W.J) (R * ht h))
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  have hm : Measurable fun u : unip σ W H' => partSum f S (u.1 * h) :=
    Measurable.tsum fun t : S => hf.comp
      ((continuous_const.mul (continuous_id.mul continuous_const)).measurable.comp measurable_subtype_coe)
  refine Integrable.mono' (integrable_const (∑' t, b t)) hm.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  obtain ⟨γ, hγ, hγR⟩ := hR u.1 u.2
  refine norm_partSum_le hT hS hinv hb hγ.1 fun t => hbd t _ ?_
  rw [← mul_assoc]
  exact (heightGL_mul_le F (γ * u.1).1 h.1).trans (mul_le_mul_left hγR _)

theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (μ : Measure X) (_ : IsFiniteMeasure μ) : SFinite μ :=
  inferInstance

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.ConeMeasV GlobalTheory.ConeMeasSmall in

theorem measurable_coneI : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ z : ℂ,
      Measurable (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z) := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' _ e' hE K μK μ hKs _ _ X om om' om₁ om₁' hT hT₁ Φ' hΦ z
  obtain ⟨K₀, μK₀, μ₀, hK₀, hK₀c, -, -⟩ :=
    GlobalTheory.StabHaar.stabEx hK.base F E σ B (b + 2) G.V' G.q (b + 2 - G.q) hT.base hT.geo.hV'
  have hKK : K = K₀ := by
    ext g; rw [hKs g, hK₀ g]
  subst hKK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK₀c
  haveI : IsFiniteMeasure μK := inferInstance
  haveI : SFinite μK := sfinite_of_finite μK inferInstance
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hS₁ := IsUWeilPair.isUSplitting hT₁.weil'
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin b × Fin (a + b))
  have hΦA := polData_le_schA hM hΦ.1
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V'.J
  obtain ⟨u1, u2, u3, u4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G₁.V'.J
  obtain ⟨w1, w2, w3, w4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.W.J
  obtain ⟨v1, v2⟩ := idele_top (F := F) (E := E)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G₁.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : TopologicalSpace.MetrizableSpace (UA σ G.V'.J) := metrizable_group _ t1 t4 t3
  haveI : TopologicalSpace.MetrizableSpace (UA σ G₁.V'.J) := metrizable_group _ u1 u4 u3
  haveI : TopologicalSpace.MetrizableSpace (UA σ G.W.J) := metrizable_group _ w1 w4 w3
  haveI := hM₁.haar
  haveI : SigmaCompactSpace (UA σ G₁.V'.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite (G₁.M'.μ.restrict G₁.M'.dom) := sfinite_restrict _ (Measure.IsHaarMeasure.sigmaFinite _) _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eq⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := eq.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := eq.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  have hν : Continuous fun l : (AE F E)ˣ => ((X.ν l : Circle) : ℂ) := by
    have h1 : Continuous fun l : (AE F E)ˣ => X.α l / X.β l :=
      hT.chars.heckeα.1.div' hT.chars.heckeβ.1
    have h2 : Continuous (X.α / X.β) := h1.congr fun l => (MonoidHom.div_apply _ _ _).symm
    exact continuous_subtype_val.comp h2
  have ha : Continuous fun l : (AE F E)ˣ => ((absE F E l : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (a + (b + 2)) → AE F E))
  have hco : Continuous G.M'.co.e := IsModuleTopology.continuous_of_linearMap G.M'.co.e.toLinearMap
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hsh : Continuous (shiftB σ H H') := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (hcA.comp Units.continuous_val).mul continuous_const
  let u : UA σ G₁.V'.J → UA σ G.V'.J × UA σ G.W.J → (AE F E)ˣ → ℂ := fun g k l =>
    l₀ (om₁' (g, 1) (e' (schr B.ψ (G.M'.co.e (shiftB σ H H' l)) (om' k Φ'))))
  have hmem : ∀ k l, e' (schr B.ψ (G.M'.co.e (shiftB σ H H' l)) (om' k Φ')) ∈ schA F _ := fun k l =>
    hE.maps _ (GlobalTheory.ConeMeasV.schr_mem_schA hψ _ (hS.pres _ _ hΦA))
  have hadm : ∀ g, (l₀ ∘ₗ om₁' (g, 1)) ∘ₗ e' ∈ (adeleClass F).adm _ := fun g =>
    comp_ev_mem_adm hM hM₁ hE (hS₁.adm _ _ hl₀)
  have cg : ∀ k l, Continuous fun g => u g k l := fun k l =>
    (hS₁.cont _ hl₀ _ (hmem k l)).comp (continuous_id.prodMk continuous_const)
  have ck : ∀ g l, Continuous fun k => u g k l := fun g l =>
    hS.cont _ (comp_schr_mem_adm hψ (G.M'.co.e (shiftB σ H H' l)) (hadm g)) _ hΦA
  have cl : ∀ g k, Continuous (u g k) := fun g k =>
    (continuous_schr hψ (hadm g) (hS.pres k _ hΦA)).comp (hco.comp hsh)
  have m1 : ∀ g, Measurable (Function.uncurry (u g)) := fun g =>
    measurable_uncurry_of_continuous_of_measurable (ck g) fun k => (cl g k).measurable
  have m2 : Measurable (Function.uncurry fun g (p : (UA σ G.V'.J × UA σ G.W.J) × (AE F E)ˣ) => u g p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable (fun p => cg p.1 p.2) m1
  have m3 : Measurable fun x : ((UA σ G.W.J × K) × (AE F E)ˣ) × UA σ G₁.V'.J => u x.2 (x.1.1.2.1, x.1.1.1) x.1.2 :=
    m2.comp (measurable_snd.prodMk (((measurable_subtype_coe.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk (measurable_snd.comp measurable_fst)))
  have m4 := (m3.stronglyMeasurable.integral_prod_right' (ν := G₁.M'.μ.restrict G₁.M'.dom)).measurable
  have m5 : Measurable fun p : (UA σ G.W.J × K) × (AE F E)ˣ =>
      G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2) (om' (p.1.2.1, p.1.1) Φ'))) 1 := by
    refine cast (congrArg Measurable (funext fun p => ?_)) m4
    refine congrArg (integral (G₁.M'.μ.restrict G₁.M'.dom)) (funext fun g => ?_)
    exact (hl₀eq _ (hS₁.pres _ _ (hmem _ _)))
  have m6 := (m5.mul (hν.measurable.comp measurable_snd)).mul ((ha.measurable.pow_const z).comp measurable_snd)
  have m7 := m6.stronglyMeasurable.integral_prod_right' (ν := μ)
  exact (m7.integral_prod_right' (ν := μK)).measurable

theorem ctInt_mid : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
      GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T →
      GlobalTheory.ThK.CTAdd.CTInt H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.midSet H'.x T)) := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ
  refine ⟨0, fun T hR s _ hL => ?_⟩
  obtain ⟨R, hR'⟩ := GlobalTheory.UnipCompact.exists_bounded_translate F E σ B _ _ G.W G₁.W H' _ _ _ _ hT.base hT.geo.hW hC.hH'
  exact ctInt_partSum H' R hR' hR (fun t ht => ht.1)
    (measurable_coneI hK F E σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ _)
    (fun p hp hs h => GlobalTheory.T.seesaw_evaluation_haar_nonarchimedean hK F E σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ _ p hp hs h)
    hL

end GlobalTheory.ConeSmallSerInt

end
