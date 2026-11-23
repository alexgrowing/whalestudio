import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicSectionContinuousLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianContinuousCoordsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix Filter Topology MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped ContDiff
open scoped CategoryTheory.Obj MonObj

namespace GlobalTheory.RiemannConst

theorem isHolTo_comp_clm {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] {Z : Scheme.{0}} {W : Set E} {a : E → (Sp ℂ ⟶ Z)} (h : IsHolTo W a) (φ : E' →L[ℂ] E) :
    IsHolTo (φ ⁻¹' W) fun v => a (φ v) := fun U f =>
  ⟨(h U f).1.preimage φ.continuous, (h U f).2.comp φ.differentiable.differentiableOn fun _ hw => hw⟩

theorem exists_pair {X : Scheme.{0}} (A : Over X) {m g : ℕ} {B : Set (Fin m → ℂ)}
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B)
    {ε : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ A.left)} (hε : IsHolTo (B ×ˢ Set.univ) ε)
    (hy : ∀ b ∈ B, ∀ z, ε (b, z) ≫ A.hom = y b) :
    ∃ c : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ (A ⊗ A).left),
      IsHolTo (B ×ˢ Set.univ) c ∧ ∀ b ∈ B, ∀ z w, c (b, z, w) ≫ (fst A A).left = ε (b, z) ∧
        c (b, z, w) ≫ (snd A A).left = ε (b, w) := by
  let φ₁ : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) →L[ℂ] (Fin m → ℂ) × (Fin g → ℂ) :=
    (ContinuousLinearMap.id ℂ _).prodMap (ContinuousLinearMap.fst ℂ _ _)
  let φ₂ : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) →L[ℂ] (Fin m → ℂ) × (Fin g → ℂ) :=
    (ContinuousLinearMap.id ℂ _).prodMap (ContinuousLinearMap.snd ℂ _ _)
  have h₁ := isHolTo_comp_clm hε φ₁
  have h₂ := isHolTo_comp_clm hε φ₂
  have e₁ : φ₁ ⁻¹' (B ×ˢ Set.univ) = B ×ˢ Set.univ := by ext q; simp [φ₁]
  have e₂ : φ₂ ⁻¹' (B ×ˢ Set.univ) = B ×ˢ Set.univ := by ext q; simp [φ₂]
  rw [e₁] at h₁
  rw [e₂] at h₂
  obtain ⟨c, hc, H⟩ := HolTorsion.exists_isHolTo_lift (IsPullback.of_hasPullback A.hom A.hom) h₁ h₂
    (fun w hw => (hy w.1 hw.1 _).trans (hy w.1 hw.1 _).symm) (b₀ := (b₀, 0, 0)) ⟨hb₀, trivial⟩
  exact ⟨c, hc, fun b hb z w => H (b, z, w) ⟨hb, trivial⟩⟩

theorem eventually_im_form_eq : ∀ (X : Scheme.{0}) (P : PPAS X) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (d : ∀ b, P.RiemannData (y b)) (ε : (Fin m → ℂ) × (Fin P.g → ℂ) → (Sp ℂ ⟶ P.A.left)) (T : (Fin m → ℂ) → ((Fin P.g → ℂ) ≃L[ℂ] (Fin P.g → ℂ))) (l l' : (Fin m → ℂ) → (Fin P.g → ℂ)), IsOpen B → b₀ ∈ B → IsHolTo (B ×ˢ Set.univ) ε → (∀ b ∈ B, ∀ z, ε (b, z) = ((d b).u.ex (T b z)).left ≫ (d b).φ) → ContinuousOn l B → ContinuousOn l' B → (∀ b ∈ B, T b (l b) ∈ (d b).u.Λ ∧ T b (l' b) ∈ (d b).u.Λ) → ∀ᶠ b in nhds b₀, (HermFrame.form (d b).H (T b (l b)) (T b (l' b))).im = (HermFrame.form (d b₀).H (T b₀ (l b₀)) (T b₀ (l' b₀))).im := by
  intro X P m B y b₀ d ε T l l' hB hb₀ hε hT hl hl' hΛ
  obtain ⟨M, hM, eM⟩ := CechPic.cls_surj P.c
  obtain ⟨c, hc, hce⟩ := exists_pair P.A (y := y) hb₀ hε fun b hb z => by
    rw [hT b hb, Category.assoc, (d b).isPull.1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _
  let x : (Fin m → ℂ) → (Fin P.g → ℂ) × (Fin P.g → ℂ) → (Sp ℂ ⟶ (P.A ⊗ P.A).left) := fun b q =>
    c (b, (T b).symm q.1, (T b).symm q.2)
  have hx : ∀ b : B, ∀ q, x b q ≫ (fst P.A P.A).left = ((d b).u.ex q.1).left ≫ (d b).φ ∧
      x b q ≫ (snd P.A P.A).left = ((d b).u.ex q.2).left ≫ (d b).φ := fun b q => by
    have := hce b b.2 ((T b).symm q.1) ((T b).symm q.2)
    rwa [hT b b.2, hT b b.2, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply] at this
  choose F hFc hF0 hFg hFp using fun b : B => GlobalTheory.T.product_abelian_continuous_coords X P (y b) (d b) M hM eM (x b) (hx b)
  have hper : ∀ (b : B) (z w : Fin P.g → ℂ) (k : (d b).u.Λ),
      x b (z + k, w) = x b (z, w) ∧ x b (z, w + k) = x b (z, w) := fun b z w k => by
    have e (z) : (d b).u.ex (z + k) = (d b).u.ex z := by
      rw [(d b).u.ex_add, ((d b).u.ker k).2 k.2, _root_.mul_one]
    refine ⟨Limits.pullback.hom_ext ?_ ?_, Limits.pullback.hom_ext ?_ ?_⟩
    · exact (hx b _).1.trans ((congrArg (·.left ≫ (d b).φ) (e z)).trans (hx b (z, w)).1.symm)
    · exact (hx b _).2.trans (hx b (z, w)).2.symm
    · exact (hx b _).1.trans (hx b (z, w)).1.symm
    · exact (hx b _).2.trans ((congrArg (·.left ≫ (d b).φ) (e w)).trans (hx b (z, w)).2.symm)
  let p : B × ℝ × ℝ → (Fin P.g → ℂ) × (Fin P.g → ℂ) := fun q =>
    ((q.2.1 : ℂ) • T q.1 (l q.1), (q.2.2 : ℂ) • T q.1 (l' q.1))
  let r : B × ℝ × ℝ → (Fin m → ℂ) × (Fin P.g → ℂ) × (Fin P.g → ℂ) := fun q =>
    (q.1, (q.2.1 : ℂ) • l q.1, (q.2.2 : ℂ) • l' q.1)
  have hr : Continuous r := by
    have k₁ : Continuous fun b : B => l b := hl.domRestrict
    have k₂ : Continuous fun b : B => l' b := hl'.domRestrict
    exact (continuous_subtype_val.comp continuous_fst).prodMk
      (((Complex.continuous_ofReal.comp continuous_snd.fst).smul (k₁.comp continuous_fst)).prodMk
        ((Complex.continuous_ofReal.comp continuous_snd.snd).smul (k₂.comp continuous_fst)))
  have hxr (q : B × ℝ × ℝ) : x q.1 (p q) = c (r q) := by
    simp only [x, p, r, map_smul, ContinuousLinearEquiv.symm_apply_apply]
  have hp (b : B) : Continuous fun v : ℝ × ℝ => p (b, v) := by
    simp only [p]; fun_prop
  have p₁ (b : B) (s t : ℝ) : p (b, s + 1, t) = ((p (b, s, t)).1 + T b (l b), (p (b, s, t)).2) := by
    simp [p, add_smul]
  have p₂ (b : B) (s t : ℝ) : p (b, s, t + 1) = ((p (b, s, t)).1, (p (b, s, t)).2 + T b (l' b)) := by
    simp [p, add_smul]
  have key := GlobalTheory.T.periodic_section_continuous_limit B ⟨b₀, hb₀⟩ M.ι (fun i => {q | ⊤ ≤ x q.1 (p q) ⁻¹ᵁ M.U i})
    (fun i q => F q.1 i (p q))
    (fun q => Real.pi * HermFrame.form (d q.1).H (p q).2 (T q.1 (l q.1)))
    (fun q => Real.pi * HermFrame.form (d q.1).H (p q).1 (T q.1 (l' q.1)))
    (fun i => ?_) (fun q => ?_) (fun i b s t => ?_) (fun i q hq => hF0 q.1 i _ hq)
    (fun i b => (hFc b i).comp (hp b).continuousOn fun v hv => hv) (fun i j => ?_) (fun b => ?_)
    (fun i b s t hq => ?_)
  · rw [← hB.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨b₀, hb₀⟩, eventually_map]
    filter_upwards [key] with b hb
    have e (b : B) := congrArg Complex.im (HermFrame.conj_form (d b).isAH.1 (T b (l b)) (T b (l' b)))
    have e₀ := e ⟨b₀, hb₀⟩
    have e₁ := e b
    have := congrArg Complex.im hb
    simp [p, HermFrame.form] at this e₀ e₁
    simp only [HermFrame.form]
    rw [← e₀, ← e₁] at this
    apply mul_left_cancel₀ Real.pi_ne_zero
    linarith
  · convert (hc (M.U i) 0).1.preimage hr using 1
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hxr]
    exact ⟨fun h => ⟨⟨q.1.2, trivial⟩, h⟩, fun h => h.2⟩
  · have h : x q.1 (p q) (default : PrimeSpectrum ℂ) ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  · simp only [Set.mem_ofPred_eq, p₁, p₂]
    exact ⟨by rw [(hper b _ _ ⟨_, (hΛ b b.2).1⟩).1], by rw [(hper b _ _ ⟨_, (hΛ b b.2).2⟩).2]⟩
  · have hm : ∀ q ∈ {q : B × ℝ × ℝ | ⊤ ≤ x q.1 (p q) ⁻¹ᵁ M.U i} ∩ {q | ⊤ ≤ x q.1 (p q) ⁻¹ᵁ M.U j},
        ⊤ ≤ x q.1 (p q) ⁻¹ᵁ (M.U i ⊓ M.U j) := fun q hq => by
      rw [Scheme.Hom.preimage_inf]
      exact le_inf hq.1 hq.2
    refine ((hc (M.U i ⊓ M.U j) (M.g i j).val).2.continuousOn.comp hr.continuousOn
      fun q hq => ⟨⟨q.1.2, trivial⟩, hxr q ▸ hm q hq⟩).congr fun q hq => ?_
    simp only [Function.comp_apply]
    rw [hFg q.1 i j _ (hm q hq), mul_div_cancel_right₀ _ (hF0 q.1 j _ hq.2), hxr]
  · have k (w : Fin P.g → ℂ) : Continuous fun v => (Real.pi : ℂ) * HermFrame.form (d b).H v w :=
      continuous_const.mul (continuous_id.dotProduct continuous_const)
    have k₁ := (k (T b (l b))).comp (hp b).snd
    have k₂ := (k (T b (l' b))).comp (hp b).fst
    exact ⟨by simpa only [Function.comp_def] using k₁, by simpa only [Function.comp_def] using k₂⟩
  · simp only [p₁, p₂]
    exact ⟨(hFp b ⟨_, (hΛ b b.2).1⟩ i _ _ hq).1, (hFp b ⟨_, (hΛ b b.2).2⟩ i _ _ hq).2⟩

end GlobalTheory.RiemannConst
