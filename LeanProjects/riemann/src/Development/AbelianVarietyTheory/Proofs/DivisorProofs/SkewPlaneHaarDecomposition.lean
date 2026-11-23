import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneUnipotentDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementIsometryStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.InducedLeft

open GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conj_mem_unip_of_isLevi {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {t : (AE F E)ˣ}
    {h₁ : UA σ W₁.J} {m : UA σ W.J} (hm : IsLevi (W₁ := W₁) H t h₁ m) {v : UA σ W.J} (hv : v ∈ unip σ W H) :
    m * v * m⁻¹ ∈ unip σ W H := by
  have hx : mat m *ᵥ incV F H.x = t.1 • incV F H.x := hm.1
  have hι : mat m * incM F H.ι = incM F H.ι * mat h₁ := hm.2.2
  have hmi : mat m⁻¹ * mat m = 1 := GlobalTheory.ThK.FlagPar.mat_inv_mul m
  have hhi : mat h₁ * mat h₁⁻¹ = 1 := by
    rw [← GlobalTheory.ThK.FlagPar.mat_mul, mul_inv_cancel, GlobalTheory.ThK.FlagPar.mat_one]
  have hxi : mat m⁻¹ *ᵥ incV F H.x = (t⁻¹).1 • incV F H.x := by
    calc mat m⁻¹ *ᵥ incV F H.x = ((t⁻¹).1 * t.1) • (mat m⁻¹ *ᵥ incV F H.x) := by rw [Units.inv_mul, one_smul]
      _ = (t⁻¹).1 • (mat m⁻¹ *ᵥ (t.1 • incV F H.x)) := by rw [mul_smul, Matrix.mulVec_smul]
      _ = (t⁻¹).1 • incV F H.x := by rw [← hx, Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
  have hιi : mat m⁻¹ * incM F H.ι = incM F H.ι * mat h₁⁻¹ := by
    calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * incM F H.ι * (mat h₁ * mat h₁⁻¹) := by rw [hhi, Matrix.mul_one]
      _ = mat m⁻¹ * (incM F H.ι * mat h₁) * mat h₁⁻¹ := by simp only [Matrix.mul_assoc]
      _ = mat m⁻¹ * (mat m * incM F H.ι) * mat h₁⁻¹ := by rw [hι]
      _ = incM F H.ι * mat h₁⁻¹ := by rw [← Matrix.mul_assoc (mat m⁻¹), hmi, Matrix.one_mul]
  have key : ∀ u : UA σ W.J, (mat u *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) →
      (mat (m * u * m⁻¹) *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat (m * u * m⁻¹) *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) := by
    rintro u ⟨h1, h2⟩
    have e : mat (m * u * m⁻¹) = mat m * mat u * mat m⁻¹ := rfl
    refine ⟨?_, fun z => ?_⟩
    · rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxi, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, hx,
        smul_smul, Units.inv_mul, one_smul]
    · obtain ⟨a, ha⟩ := h2 (mat h₁⁻¹ *ᵥ z)
      refine ⟨a * t.1, ?_⟩
      rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat m⁻¹), hιi,
        ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx, Matrix.mulVec_mulVec, hι,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z, hhi, Matrix.one_mulVec, smul_smul]
  induction hv using Subgroup.closure_induction with
  | mem u hu => exact Subgroup.subset_closure (key u hu)
  | one => simp
  | mul a b _ _ ha hb =>
    have : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
    rw [this]; exact mul_mem ha hb
  | inv a _ ha =>
    have : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem ha

theorem isLevi_mul_gen {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁}
    {l l' : (AE F E)ˣ} {g₀ g₀' : UA σ W₁.J} {h h' : UA σ W.J} (hL : IsLevi (W₁ := W₁) H l g₀ h)
    (hL' : IsLevi (W₁ := W₁) H l' g₀' h') : IsLevi (W₁ := W₁) H (l * l') (g₀ * g₀') (h * h') := by
  obtain ⟨hx, hy, hι⟩ := hL
  obtain ⟨hx', hy', hι'⟩ := hL'
  have hm : ∀ (A B : UA σ W.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  have hm₁ : ∀ (A B : UA σ W₁.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, ← Matrix.mulVec_mulVec, hx', Matrix.mulVec_smul, hx, smul_smul, Units.val_mul, mul_comm]
  · rw [hm, ← Matrix.mulVec_mulVec, hy', Matrix.mulVec_smul, hy, smul_smul, _root_.mul_inv_rev, Units.val_mul, map_mul]
  · rw [hm, hm₁, Matrix.mul_assoc, hι', ← Matrix.mul_assoc, hι, Matrix.mul_assoc]

end GlobalTheory.InducedLeft

namespace GlobalTheory.InducedLeft
open GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.CuspTransfer

theorem left_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' →
      ∀ (Kc : Set (GAd σ (c₀ • W.J.map σ))) (d : ℕ) (ψs : Fin d → GAd σ (c₀ • W₁.J.map σ) → ℂ) (a : Fin d → GAd σ (c₀ • W.J.map σ) → ℂ) (Ψ : GAd σ (c₀ • W.J.map σ) → ℂ),
      GlobalTheory.ThK.CuspTransfer.IsInd hσ W W₁ H hc₀ X' M χ Kc ψs a Ψ →
      (∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (ψs i)) →
      (∀ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))), ∀ g, Ψ (u * g) = Ψ g) ∧
      (∀ γ ∈ ratPts σ (c₀ • W.J.map σ), γ ∈ GlobalTheory.StdPar.levi σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r))) → ∀ g, Ψ (γ * g) = Ψ g) := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ hND M hMc hML hMr r Xf Yf hWf X' Y'
    hW' hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ K' hK' Kc d ψs a Ψ hInd hcusp
  have hdet : W₁.J.det ≠ 0 := by
    intro h0
    apply hND₁.2
    rw [Matrix.det_smul, show (W₁.J.map σ).det = σ W₁.J.det from (RingHom.map_det (σ : E →+* E) _).symm, h0, map_zero,
      mul_zero]
  have hHP : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, horth, hgram⟩
  obtain ⟨hmul, hcomm⟩ := GlobalTheory.LeviPlaneHom.levi_section_hom F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀
    hND₁ hND M hML
  set T := toGAd hσ W.J hc₀ with hT
  set T₁ := toGAd hσ W₁.J hc₀ with hT₁
  have hU : ∀ v : UA σ W.J, v ∈ unip σ W H → T v ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0} := fun v hv => by
    have := (GlobalTheory.ThK.GLTwo.IsHypPlane.mem_unip_iff hσ hHP hsk hdet hc₀ hW' (Nat.succ_pos r) hx0 v).1 hv
    simpa using this
  have hU' : ∀ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, T.symm u ∈ unip σ W H := fun u hu => by
    refine (GlobalTheory.ThK.GLTwo.IsHypPlane.mem_unip_iff hσ hHP hsk hdet hc₀ hW' (Nat.succ_pos r) hx0 _).2 ?_
    have h2 : toGAd hσ W.J hc₀ (T.symm u) = u := T.apply_symm_apply u
    rw [h2]
    simpa using hu
  have hemb : ∀ y, emb hσ W W₁ hc₀ M y = T (M (T₁.symm y)) := fun _ => rfl
  refine ⟨fun u hu g => ?_, fun γ hγr hγl g => ?_⟩
  · obtain ⟨u₀, hu₀, t, m, y, k, hk, hm, rfl⟩ := hInd.1 g
    obtain ⟨v, hv, w, hw, rfl⟩ := (GlobalTheory.T.skew_plane_unipotent_decomposition F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ hND M
      hMc hML hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' u).1 hu
    obtain ⟨v₀, rfl⟩ := T.surjective u₀
    obtain ⟨w', rfl⟩ := T₁.surjective w
    obtain ⟨y', rfl⟩ := T₁.surjective y
    have hv₀ : v₀ ∈ unip σ W H := by simpa using hU' _ hu₀
    have hnew : v * (M w' * v₀ * (M w')⁻¹) ∈ unip σ W H :=
      mul_mem hv (conj_mem_unip_of_isLevi (hML w') hv₀)
    have e : T v * T (M (T₁.symm (T₁ w'))) * (T v₀ * T m * emb hσ W W₁ hc₀ M (T₁ y') * k) =
        T (v * (M w' * v₀ * (M w')⁻¹)) * T m * emb hσ W W₁ hc₀ M (T₁ w' * T₁ y') * k := by
      have e1 : v * M w' * v₀ * m * M y' = v * (M w' * v₀ * (M w')⁻¹) * m * (M w' * M y') := by
        calc v * M w' * v₀ * m * M y' = v * M w' * v₀ * (M w')⁻¹ * (M w' * m) * M y' := by group
          _ = _ := by rw [← hcomm t m hm w']; group
      rw [hemb, hemb, ← map_mul T₁]
      simp only [MulEquiv.symm_apply_apply, hmul]
      calc T v * T (M w') * (T v₀ * T m * T (M y') * k) = T (v * M w' * v₀ * m * M y') * k := by
            simp only [map_mul, mul_assoc]
        _ = T (v * (M w' * v₀ * (M w')⁻¹) * m * (M w' * M y')) * k := by rw [e1]
        _ = _ := by simp only [map_mul, map_inv, mul_assoc]
    rw [e, hInd.2 _ (hU _ hnew) t m (T₁ w' * T₁ y') k hk hm, hInd.2 _ hu₀ t m (T₁ y') k hk hm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hcusp i).1.leftN (T₁ w') hw (T₁ y')]
  · obtain ⟨u₀, hu₀, t, m, y, k, hk, hm, rfl⟩ := hInd.1 g
    obtain ⟨s', mₛ, h₁, hms, hh₁l, rfl⟩ := GlobalTheory.T.hyperbolic_plane_orthogonal_split F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ hND
      M hML r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc S' γ hγl
    obtain ⟨⟨s, rfl⟩, hh₁r⟩ := GlobalTheory.T.hyperbolic_plane_complement_isometry F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ hND M hML _ hγr
      _ mₛ h₁ hms rfl
    obtain ⟨v₀, rfl⟩ := T.surjective u₀
    obtain ⟨y', rfl⟩ := T₁.surjective y
    have hv₀ : v₀ ∈ unip σ W H := by simpa using hU' _ hu₀
    have hnew : mₛ * M h₁ * v₀ * (mₛ * M h₁)⁻¹ ∈ unip σ W H := by
      have := conj_mem_unip_of_isLevi hms (conj_mem_unip_of_isLevi (hML h₁) hv₀)
      have e0 : mₛ * M h₁ * v₀ * (mₛ * M h₁)⁻¹ = mₛ * (M h₁ * v₀ * (M h₁)⁻¹) * mₛ⁻¹ := by group
      rw [e0]; exact this
    have hml := isLevi_mul_gen hms hm
    rw [mul_one] at hml
    have e : T mₛ * T (M h₁) * (T v₀ * T m * emb hσ W W₁ hc₀ M (T₁ y') * k) =
        T (mₛ * M h₁ * v₀ * (mₛ * M h₁)⁻¹) * T (mₛ * m) * emb hσ W W₁ hc₀ M (T₁ h₁ * T₁ y') * k := by
      have e1 : mₛ * M h₁ * v₀ * m * M y' = mₛ * M h₁ * v₀ * (mₛ * M h₁)⁻¹ * (mₛ * m) * (M h₁ * M y') := by
        calc mₛ * M h₁ * v₀ * m * M y' = mₛ * M h₁ * v₀ * (M h₁)⁻¹ * (M h₁ * m) * M y' := by group
          _ = _ := by rw [← hcomm t m hm h₁]; group
      rw [hemb, hemb, ← map_mul T₁]
      simp only [MulEquiv.symm_apply_apply, hmul]
      calc T mₛ * T (M h₁) * (T v₀ * T m * T (M y') * k) = T (mₛ * M h₁ * v₀ * m * M y') * k := by
            simp only [map_mul, mul_assoc]
        _ = T (mₛ * M h₁ * v₀ * (mₛ * M h₁)⁻¹ * (mₛ * m) * (M h₁ * M y')) * k := by rw [e1]
        _ = _ := by simp only [map_mul, map_inv, mul_assoc]
    have hrat : T₁ h₁ ∈ ratPts σ (c₀ • W₁.J.map σ) := (GlobalTheory.ThK.GLTwo.toGAd_mem_ratPts hσ W₁.J hc₀ h₁).2 hh₁r
    rw [e, hInd.2 _ (hU _ hnew) _ _ (T₁ h₁ * T₁ y') k hk hml, hInd.2 _ hu₀ t m (T₁ y') k hk hm, map_mul, hχ s, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hcusp i).1.leftM (T₁ h₁) hrat hh₁l (T₁ y')]

end GlobalTheory.InducedLeft
