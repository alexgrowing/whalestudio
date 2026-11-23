import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihilaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLiftStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSFull

theorem eq_lieComb {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ} {cf : Fin n → R}
    {v : Fin n → (epsR R ⟶ A)} {w : epsR R ⟶ A} (h : IsLieComb cf v w) : w = GlobalTheory.FlagTan.lieComb cf v := by
  obtain ⟨u, hu, rfl⟩ := h
  unfold GlobalTheory.FlagTan.lieComb
  congr 2
  funext i
  exact Over.OverMorphism.ext (hu i)

theorem eq_one_of_isLieComb_zero {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {v : Fin n → (epsR R ⟶ A)} (hv : ∀ i, IsTangent (v i)) {w : epsR R ⟶ A}
    (h : IsLieComb (fun _ => (0 : R)) v w) : w = 1 := by
  rw [eq_lieComb h]
  unfold GlobalTheory.FlagTan.lieComb
  simp [GlobalTheory.GrpTangent.epsScale_zero_comp (hv _)]

theorem isKSValue_one_sum {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} {h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i} {J : Type} (s : Finset J)
    (c : J → K) (F : J → HdR A) (hF : ∀ k, IsKSValue h (F k) 1) : IsKSValue h (∑ k ∈ s, c k • F k) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, ⟨0, zero_mem _, fun _ => (LinearMap.zero_apply _).trans (by simp)⟩, isLieImage_one_iff.2 (zero_mem _)⟩
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    have := ((hF k).smul (c k)).add ih
    rwa [MonObj.comp_one, _root_.mul_one] at this

theorem isKSValue_one_of_rows {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (HdR A))
    (hiso : ∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) (hlag : ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A)
    (hperf : LinearMap.IsPerfPair ψ) (halt : ψ.IsAlt)
    (hsym : ∀ f g k k', IsFilLift h f k → IsFilLift h g k' → ψ f k' + ψ k g = 0)
    {Ι : Type} [Fintype Ι] {m : Ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A)
    (hl : ∀ k, IsLieImage (hb k) (ub k.1 k.2)) (hspan : Submodule.span K (Set.range hb) ⊔ Fil A = ⊤)
    (P : Ι → Prop) (cj : Ι → Ι) (hcj : ∀ σ, P σ → ¬ P (cj σ))
    (h0 : ∀ k : (Σ σ, Fin (m σ)), ¬ P k.1 → GlobalTheory.FlagTan.IsKSRow h ψ hb k 1)
    (h1 : ∀ k : (Σ σ, Fin (m σ)), P k.1 → ∃ cf w, IsLieComb cf (ub (cj k.1)) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb k w) :
    ∀ f ∈ Fil A, IsKSValue h f 1 := by
  classical

  have what₂ : ∀ k : (Σ σ, Fin (m σ)), ∃ f ∈ Fil A, (∀ k', ψ f (hb k') = if k' = k then 1 else 0) ∧
      ∃ kf, IsFilLift h f kf ∧ (¬ P k.1 → kf ∈ Fil A) ∧
        (P k.1 → ∃ cf : Fin (m (cj k.1)) → K, kf - ∑ b, cf b • hb ⟨cj k.1, b⟩ ∈ Fil A) := fun k => by
    by_cases hk : P k.1
    · obtain ⟨cf, w, hc, f, hf, hd, kf, hkf, hw⟩ := h1 k hk
      refine ⟨f, hf, fun k' => (hd k').trans (ite_congr rfl (fun _ => rfl) (fun _ => rfl)), kf, hkf,
        fun h' => absurd hk h', fun _ => ⟨cf, ?_⟩⟩
      have e := GlobalTheory.FlagTan.isLieImage_lieComb cf (fun b => hl ⟨cj k.1, b⟩)
      rw [← eq_lieComb hc] at e
      exact hw.sub_mem e
    · obtain ⟨f, hf, hd, kf, hkf, hw⟩ := h0 k hk
      exact ⟨f, hf, fun k' => (hd k').trans (ite_congr rfl (fun _ => rfl) (fun _ => rfl)), kf, hkf,
        fun _ => isLieImage_one_iff.1 hw, fun h' => absurd h' hk⟩
  choose F hF hδ kf hkf hk0 hk1 using what₂

  have zero : ∀ d ∈ Fil A, (∀ k, ψ d (hb k) = 0) → d = 0 := fun d hd h0 => by
    have hker : Submodule.span K (Set.range hb) ⊔ Fil A ≤ LinearMap.ker (ψ d) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso d hd g hg
      rintro _ ⟨k, rfl⟩
      exact h0 k
    have e : ψ d = 0 := LinearMap.ext fun x => hker (hspan ▸ Submodule.mem_top)
    exact hperf.bijective_left.1 (e.trans (map_zero ψ).symm)

  have span : ∀ g ∈ Fil A, g = ∑ k, ψ g (hb k) • F k := fun g hg => by
    refine (sub_eq_zero.1 (zero _ (sub_mem hg (sum_mem fun k _ => Submodule.smul_mem _ _ (hF k))) fun k' => ?_))
    have e : ∑ k, (ψ (ψ g (hb k) • F k)) (hb k') = ψ g (hb k') := by
      rw [Finset.sum_eq_single k' (fun b _ hb' => by
        rw [map_smul, LinearMap.smul_apply, hδ, if_neg (Ne.symm hb'), smul_zero]) (by simp)]
      rw [map_smul, LinearMap.smul_apply, hδ, if_pos rfl, smul_eq_mul, _root_.mul_one]
    rw [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, e, sub_self]

  have key : ∀ k k', ψ (kf k) (F k') = 0 := fun k k' => by
    by_cases hk : P k.1
    · by_cases hk' : P k'.1
      · obtain ⟨cf, hcf⟩ := hk1 k hk
        have e1 := hiso _ hcf _ (hF k')
        rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1
        rw [e1, map_sum, LinearMap.sum_apply]
        refine Finset.sum_eq_zero fun b _ => ?_
        have hne : (⟨cj k.1, b⟩ : Σ σ, Fin (m σ)) ≠ k' := fun e => hcj _ hk (by subst e; exact hk')
        rw [map_smul, LinearMap.smul_apply, ← LinearMap.IsAlt.neg halt (F k') _, hδ, if_neg hne, neg_zero,
          smul_zero]
      · have e1 := hsym _ _ _ _ (hkf k) (hkf k')
        rw [hiso _ (hF k) _ (hk0 k' hk'), zero_add] at e1
        exact e1
    · exact hiso _ (hk0 k hk) _ (hF k')
  have hone : ∀ k, IsKSValue h (F k) 1 := fun k =>
    ⟨kf k, hkf k, isLieImage_one_iff.2 (hlag _ fun g hg => by
      rw [span g hg, map_sum]
      exact Finset.sum_eq_zero fun k' _ => by rw [map_smul, key, smul_zero])⟩
  intro f hf
  rw [span f hf]
  exact isKSValue_one_sum _ _ _ hone

end GlobalTheory.KSFull

namespace GlobalTheory.KSFull

theorem conj_embK' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  show conjEmb τ ((H.bar z : 𝓞 E) : E) = τ (z : E)
  rw [H.bar_eq]
  simp [conjEmb, IsCMField.complexEmbedding_complexConj]

theorem ksFull : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧ ∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1 := by
  intro PP E _ _ _ H Dw l Xo c K _ _ y x' _ _ hKS
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hKS
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, hπ, hπ', e, ?_⟩
  have P := PP.p5
  have hU := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  haveI : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc i π', e, ha z]
    · rw [Category.assoc, Category.assoc, Over.w, h.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ₀, hpol₀, hiso, hperf, hlag⟩ := GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating P Xo hπ
  obtain rfl : ψ = ψ₀ := IsPolForm.unique P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hpol hpol₀
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P Xo hπ a ha hpol
  have hK := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme P h hA' gA'
  obtain ⟨ub₀, hu₀, ht₀, he₀, hbasis₀⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  obtain rfl : ub = ub₀ := by
    funext σ k
    apply ReciprocityTheory.ChartRestriction.G.PullbackSections.push_inj hπ
    apply Over.OverMorphism.ext
    change (ub σ k).left ≫ π = (ub₀ σ k).left ≫ π
    rw [hu, hu₀]
  have hl' : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), IsLieImage (hb k) (ub k.1 k.2) := fun k => hl k.1 k.2
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P y hπ ub hu hb hl'
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hl' k).push (a.act z)
    rw [he₀] at h1
    exact h1.sub_mem ((hl' k).smul _)
  have hsym := GlobalTheory.T.tangent_group_pullback_epsilon_lift PP E H Dw l Xo K y.x x' A A' π π' i h ψ hπ hπ' e hpol
  refine isKSValue_one_of_rows h ψ hiso hlag hperf hpol.isAlt hsym ub hb hl' hspan
    (fun σ => σ ∈ GlobalTheory.FlagTan.psiSet H) conjEmb
    (fun σ hσ => ((GlobalTheory.FlagTan.isHalf_psiSet H) σ).1 hσ) ?_ ?_
  ·
    have key : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, j⟩ 1 := fun τ j => by
      obtain ⟨w, hw, hr⟩ := hM τ j
      rwa [eq_one_of_isLieComb_zero (fun b => ht₀ τ.1 b) hw] at hr
    rintro ⟨σ, j⟩ hσ
    have hτ : conjEmb σ ∈ GlobalTheory.FlagTan.psiSet H := by
      rw [(GlobalTheory.FlagTan.isHalf_psiSet H) (conjEmb σ), GlobalTheory.AllWt.conjEmb_conjEmb]
      exact hσ
    suffices ∀ σ' (_ : conjEmb (conjEmb σ) = σ') (j' : Fin (Dw.mult σ')),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨σ', j'⟩ 1 from this σ (GlobalTheory.AllWt.conjEmb_conjEmb σ) j
    intro σ' e'
    subst e'
    exact key ⟨conjEmb σ, hτ⟩
  ·
    rintro ⟨σ, j⟩ -
    exact GlobalTheory.KSExist.ksRow_exists_lieComb h a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift h a a' hc z hw)
      χ ub hb hspan hind heig hbasis₀ (conjEmb σ) σ
      (fun z => by
        simp only [χ, RingHom.comp_apply]
        rw [← conj_embK' c (conjEmb σ) z, GlobalTheory.AllWt.conjEmb_conjEmb]) j

end GlobalTheory.KSFull
