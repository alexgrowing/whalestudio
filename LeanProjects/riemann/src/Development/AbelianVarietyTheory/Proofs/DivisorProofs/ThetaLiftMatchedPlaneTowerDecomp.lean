import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTwoLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentQuotientUnitVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneRestrictedSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicUnfoldingRationalLeviStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.DescB.LevRatInv
open GlobalTheory.LeviLine
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_of_cartan {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : E →+* ℂ) {θ : Matrix (Fin n) (Fin n) ℂ}
    (h : IsCartan (Complex.I • J.map e) θ) : J.det ≠ 0 := by
  intro hd
  have h0 : (J.map e).det = 0 := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, map_zero]
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hx : star z ≠ 0 := fun h' => hz0 (by simpa using congrArg star h')
  have := h.2.2 (star z) hx
  rw [star_star, Matrix.smul_mulVec, hz, smul_zero, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem isLevi_mul_one {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {γ h₁ : UA σ Y₁.J}
    {m m' : UA σ Y.J} (h : IsLevi (W₁ := Y₁) H 1 γ m) (h' : IsLevi (W₁ := Y₁) H 1 h₁ m') :
    IsLevi (W₁ := Y₁) H 1 (γ * h₁) (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (γ * h₁) = mat γ * mat h₁ := rfl
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h1', Matrix.mulVec_smul, h1, smul_smul, Units.val_one, one_mul]
  · rw [e, ← Matrix.mulVec_mulVec, h2', Matrix.mulVec_smul, h2, smul_smul, inv_one, Units.val_one, map_one, one_mul]
  · rw [e, e1, Matrix.mul_assoc, h3', ← Matrix.mul_assoc, h3, Matrix.mul_assoc]

theorem isLevi_conj {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {γ : UA σ Y₁.J}
    {m₀ m : UA σ Y.J} {t : (AE F E)ˣ} (h₀ : IsLevi (W₁ := Y₁) H 1 γ m₀) (h : IsLevi (W₁ := Y₁) H t 1 m) :
    IsLevi (W₁ := Y₁) H t 1 (m₀ * m * m₀⁻¹) := by
  obtain ⟨a1, a2, a3⟩ := h₀
  obtain ⟨b1, b2, b3⟩ := h
  have e : mat (m₀ * m * m₀⁻¹) = mat m₀ * mat m * mat m₀⁻¹ := rfl
  have inv1 : mat m₀⁻¹ * mat m₀ = 1 := GlobalTheory.UnipCT.mat_inv_mul' m₀
  have inv2 : mat γ * mat γ⁻¹ = 1 := by
    show (γ.1 * γ.1⁻¹ : GL _ _).1 = 1
    simp
  have c1 : mat m₀⁻¹ *ᵥ incV F H.x = incV F H.x := by
    have := congrArg (mat m₀⁻¹ *ᵥ ·) a1
    simp only [Matrix.mulVec_mulVec, inv1, Matrix.one_mulVec, Units.val_one, one_smul] at this
    exact this.symm
  have c2 : mat m₀⁻¹ *ᵥ incV F H.y = incV F H.y := by
    have := congrArg (mat m₀⁻¹ *ᵥ ·) a2
    simp only [Matrix.mulVec_mulVec, inv1, Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul] at this
    exact this.symm
  have c3 : mat m₀⁻¹ * incM F H.ι = incM F H.ι * mat γ⁻¹ := by
    have := congrArg (fun M => mat m₀⁻¹ * M * mat γ⁻¹) a3
    simp only [← Matrix.mul_assoc, inv1, Matrix.one_mul] at this
    rw [Matrix.mul_assoc (mat m₀⁻¹ * incM F H.ι), inv2, Matrix.mul_one] at this
    exact this.symm
  have a1' : mat m₀ *ᵥ incV F H.x = incV F H.x := by simpa using a1
  have a2' : mat m₀ *ᵥ incV F H.y = incV F H.y := by simpa using a2
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c1, b1, Matrix.mulVec_smul, a1']
  · rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c2, b2, Matrix.mulVec_smul, a2']
  · have b3' : mat m * incM F H.ι = incM F H.ι := by simpa [mat] using b3
    have e1 : mat (1 : UA σ Y₁.J) = 1 := rfl
    rw [e, e1, Matrix.mul_one, Matrix.mul_assoc, c3, ← Matrix.mul_assoc (mat m₀ * mat m), Matrix.mul_assoc (mat m₀), b3', a3,
      Matrix.mul_assoc, inv2, Matrix.mul_one]

theorem fa_inv {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {χa χb : Chr F E} {za zb : ℝ}
    (hz : za < zb)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m ∧ 1 < (absE F E t : ℝ))
    (hdom : ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1)
    {f fa fb : UA σ Y.J → ℂ} (hf : ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x)
    (hs : SplitZ Y₁ H χa χb za zb f fa fb) {γ : UA σ Y₁.J} {m₀ : UA σ Y.J} (hm₀ : m₀ ∈ ratU σ Y.J)
    (hL : IsLevi (W₁ := Y₁) H 1 γ m₀) : ∀ x, fa (m₀ * x) = fa x := by
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := hdom
  have hsum : ∀ x, fa (m₀ * x) + fb (m₀ * x) = fa x + fb x := fun x => by
    have e1 := hs.1 μ 𝓕 hμ h𝓕 h1 (m₀ * x)
    have e2 := hs.1 μ 𝓕 hμ h𝓕 h1 x
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
    exact GlobalTheory.T.parabolic_unfolding_rational_levi F E σ n n₁ Y Y₁ H f hf γ m₀ hm₀ hL μ 𝓕 hμ h𝓕 h1 x
  set T : UA σ Y.J → ℂ := fun x => fa (m₀ * x) - fa x with hT
  have hTa : HasLaw Y₁ H χa za T := by
    intro t m hm x
    have hc := isLevi_conj hL hm
    have e : m₀ * (m * x) = (m₀ * m * m₀⁻¹) * (m₀ * x) := by group
    simp only [hT]
    rw [e, hs.2.1 t _ hc, hs.2.1 t m hm]
    ring
  have hTb : HasLaw Y₁ H χb zb T := by
    have eT : ∀ x, T x = -(fb (m₀ * x) - fb x) := fun x => by
      simp only [hT]; linear_combination hsum x
    intro t m hm x
    have hc := isLevi_conj hL hm
    have e : m₀ * (m * x) = (m₀ * m * m₀⁻¹) * (m₀ * x) := by group
    rw [eT, eT, e, hs.2.2 t _ hc, hs.2.2 t m hm]
    ring
  have h0 := GlobalTheory.ThK.DescB.NextStep.eq_zero_of_two_laws hz hlevi hTa hTb
  intro x
  have := congrFun h0 x
  simp only [hT, Pi.zero_apply] at this
  exact sub_eq_zero.1 this

theorem gen_inv {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {χa χb : Chr F E} {za zb : ℝ}
    (hz : za < zb)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m ∧ 1 < (absE F E t : ℝ))
    (hdom : ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1)
    (hrat : ∀ γ ∈ ratU σ Y₁.J, ∃ m ∈ ratU σ Y.J, IsLevi (W₁ := Y₁) H 1 γ m)
    {f fa fb : UA σ Y.J → ℂ} (hf : ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x)
    (hs : SplitZ Y₁ H χa χb za zb f fa fb) (h : UA σ Y.J)
    (hex : ∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H 1 h₁ m)
    {g : UA σ Y₁.J → ℂ} (hg : ∀ h₁ m, IsLevi (W₁ := Y₁) H 1 h₁ m → g h₁ = fa (m * h)) :
    ∀ γ ∈ ratU σ Y₁.J, ∀ h₁, g (γ * h₁) = g h₁ := by
  intro γ hγ h₁
  obtain ⟨m₀, hm₀, hL⟩ := hrat γ hγ
  obtain ⟨m₁, hm₁⟩ := hex h₁
  rw [hg _ _ (isLevi_mul_one hL hm₁), hg _ _ hm₁, mul_assoc]
  exact fa_inv hz hlevi hdom hf hs hm₀ hL (m₁ * h)

theorem inv_span {n : ℕ} {Y : Spc F E n} (S : Set (UA σ Y.J → ℂ))
    (hS : ∀ f ∈ S, ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) :
    ∀ f ∈ Submodule.span ℂ S, ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => intro _ _ _; rfl
  | add x y _ _ hx hy => intro γ hγ z; simp only [Pi.add_apply]; rw [hx γ hγ z, hy γ hγ z]
  | smul r x _ hx => intro γ hγ z; simp only [Pi.smul_apply]; rw [hx γ hγ z]

theorem inv_alphaSpan {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {χa χb : Chr F E} {za zb : ℝ}
    (hz : za < zb)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m ∧ 1 < (absE F E t : ℝ))
    (hdom : ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1)
    (hrat : ∀ γ ∈ ratU σ Y₁.J, ∃ m ∈ ratU σ Y.J, IsLevi (W₁ := Y₁) H 1 γ m)
    (Kh : Set (UA σ Y.J)) (S : Submodule ℂ (UA σ Y.J → ℂ))
    (hS : ∀ f ∈ S, ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) :
    ∀ g ∈ alphaSpan Y₁ H χa χb za zb Kh S, ∀ γ ∈ ratU σ Y₁.J, ∀ x, g (γ * x) = g x := by
  refine inv_span _ ?_
  rintro g ⟨f, hf, fa, fb, hs, h, -, hex, hg⟩
  exact gen_inv hz hlevi hdom hrat (hS f hf) hs h hex hg

theorem plane_facts (B : Base F E) (hB : B.IsGood σ) {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁}
    (hsk : ∀ i j, σ (Y.J j i) = -Y.J i j) (hI : IsIsoPlane σ B H Y Y₁) :
    (∃ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m ∧ 1 < (absE F E t : ℝ)) ∧
    (∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1) ∧
    (∀ γ ∈ ratU σ Y₁.J, ∃ m ∈ ratU σ Y.J, IsLevi (W₁ := Y₁) H 1 γ m) := by
  have hcm := hB.cm
  refine ⟨GlobalTheory.ThK.DescB.NextStep.exists_levi_of hcm hsk hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2.1,
    GlobalTheory.T.unipotent_quotient_unit_volume F E σ B hB n n₁ Y Y₁ H hsk hI, ?_⟩
  have w : InfinitePlace F := Classical.arbitrary _
  exact GlobalTheory.T.isotropic_plane_restricted_skew F E σ (sigma_invol hcm) n n₁ Y Y₁ H hsk hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2.1 hI.2.2.2.2.2.1
    (det_ne_zero_of_cartan _ (hI.2.2.2.2.2.2.2 w))

theorem polData_of_polMatch (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a')
    (Rf : FinMaps F a a') {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} {Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ}
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, -, rfl, -, -⟩ := h
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (hi i).2.1, ?_, rfl⟩
  refine Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => ?_)
  by_contra hT
  exact hv ((hi i).2.2 v hT)

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ k, k + 1 + 1 ≤ G.p →
      ∀ f ∈ Lev B X a a' H' sp pl (thetaSpanV B G X om R Rf) k, ∀ fa fb : UA σ (sp k).J → ℂ,
        SplitZ (sp (k + 1)) (pl k) X.α X.β ((a' : ℝ) / 2) (zb a k) f fa fb →
      ∀ h ∈ finK σ (sp k) B.emb, (∀ h₁ : UA σ (sp (k + 1)).J, ∃ m : UA σ (sp k).J, IsLevi (W₁ := sp (k + 1)) (pl k) 1 h₁ m) →
      ∀ g : UA σ (sp (k + 1)).J → ℂ, (∀ h₁ m, IsLevi (W₁ := sp (k + 1)) (pl k) 1 h₁ m → g h₁ = fa (m * h)) →
      ∀ γ ∈ ratU σ (sp (k + 1)).J, ∀ h₁, g (γ * h₁) = g h₁ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso k hk f hf fa fb hs h _ hex g hg
  have hB := hM.triple.base
  have hcm := hB.cm
  have hσ : ∀ x, σ (σ x) = x := sigma_invol hcm
  have hsk := GlobalTheory.ThK.DescB.NextStep.skew_sp hσ B hM.triple.geo.hW.skew hH hiso
  have hzj : ∀ j, j + 1 ≤ G.p → (a' : ℝ) / 2 < zb a j := fun j hj => by
    have e := hM.triple.geo.eBig
    have hn : a' + 2 * (j + 1) < a := by omega
    have hr : ((a' + 2 * (j + 1) : ℕ) : ℝ) < a := by exact_mod_cast hn
    unfold zb
    push_cast at hr ⊢
    linarith
  have hlev : ∀ j, j ≤ k → ∀ f ∈ Lev B X a a' H' sp pl (thetaSpanV B G X om R Rf) j,
      ∀ γ ∈ ratU σ (sp j).J, ∀ x, f (γ * x) = f x := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [lev_zero]
      have hI0 := hiso 0 (by omega)
      have w : InfinitePlace F := Classical.arbitrary _
      refine inv_alphaSpan (χa := X.α) (χb := X.β) ?_
        (GlobalTheory.ThK.DescB.NextStep.exists_levi_of hcm hM.triple.geo.hW.skew hH.xx hH.yy hH.xy hH.orth)
        (GlobalTheory.T.triple_adapted_plane_theta_integral F E σ B a a' G X om om' hM.triple d₁ (sp 0) H' i₀ i₁ hH)
        (GlobalTheory.T.isotropic_plane_restricted_skew F E σ hσ _ _ G.W (sp 0) H' hM.triple.geo.hW.skew hH.xx hH.yy hH.xy hH.orth hH.gram
          (det_ne_zero_of_cartan _ (hI0.2.2.2.2.2.2.1 w))) _ _ ?_
      · have hlt := hM.triple.geo.lt
        have : (a' : ℝ) < a := by exact_mod_cast hlt
        linarith
      · refine inv_span _ ?_
        rintro f ⟨Φ, Φ', -, hm, rfl⟩
        exact (GlobalTheory.T.theta_lift_left_invariant hK F E σ B a a' G X om om' hM.triple d₁ (sp 0) H' i₀ i₁ hH).1 Φ
          (polData_of_polMatch B G X R Rf hm)
    | succ j ih =>
      intro hj
      rw [lev_succ]
      have hI := hiso j (by omega)
      obtain ⟨p1, p2, p3⟩ := plane_facts B hB (hsk j (by omega)) hI
      exact inv_alphaSpan (hzj j (by omega)) p1 p2 p3 _ _ (ih (by omega))
  obtain ⟨p1, p2, p3⟩ := plane_facts B hB (hsk k (by omega)) (hiso k (by omega))
  exact gen_inv (hzj k (by omega)) p1 p2 p3 (hlev k le_rfl f hf) hs h hex hg

end GlobalTheory.ThK.DescB.LevRatInv

end
