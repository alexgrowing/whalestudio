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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.CuspTransfer

theorem continuous_of_closed_coords {G S B : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace S] [TopologicalSpace B] {Kc : Set G} (hK : IsCompact Kc) {e : S → B} (he : IsClosedEmbedding e)
    {c : G → B} (hc : Continuous c) {T : Set (G × S)} (hT : IsClosed T) (hec : ∀ q ∈ T, e q.2 = c q.1)
    {Φ : S × Kc → ℂ} (hΦ : Continuous Φ) {Ψ : G → ℂ} (hs : ∀ g, ∃ q ∈ T, ∃ k ∈ Kc, g = q.1 * k)
    (hΨ : ∀ q ∈ T, ∀ k : Kc, Ψ (q.1 * k) = Φ (q.2, k)) : Continuous Ψ := by
  haveI : CompactSpace Kc := isCompact_iff_compactSpace.1 hK
  refine continuous_iff_isClosed.2 fun C hC => ?_
  let D : Set ((G × Kc) × S) := {z | (z.1.1 * (z.1.2 : G)⁻¹, z.2) ∈ T ∧ Φ (z.2, z.1.2) ∈ C}
  have hD : IsClosed D := (hT.preimage (by fun_prop)).inter (hC.preimage (by fun_prop))
  have hD' : IsClosed (Prod.map id e '' D) := (IsClosedEmbedding.id.prodMap he).isClosedMap _ hD
  have hD'' : IsClosed ((fun z : G × Kc => (z, c (z.1 * (z.2 : G)⁻¹))) ⁻¹' (Prod.map id e '' D)) :=
    hD'.preimage (by fun_prop)
  convert isClosedMap_fst_of_compactSpace _ hD'' using 1
  ext g
  constructor
  · intro hg
    obtain ⟨q, hq, k, hk, rfl⟩ := hs g
    refine ⟨(q.1 * k, ⟨k, hk⟩), ⟨((q.1 * k, ⟨k, hk⟩), q.2), ⟨by simpa using hq, ?_⟩, ?_⟩, rfl⟩
    · rw [← hΨ q hq ⟨k, hk⟩]; exact hg
    · simp [hec q hq]
  · rintro ⟨⟨g', k⟩, ⟨⟨z, s⟩, ⟨h1, h2⟩, h3⟩, rfl⟩
    obtain rfl : z = (g', k) := congrArg Prod.fst h3
    have := hΨ _ h1 k
    simp only [inv_mul_cancel_right] at this
    change Ψ g' ∈ C
    rw [this]; exact h2

section Tri

variable {R : Type*} [CommRing R] {n m : ℕ} (x : Fin n → R) (ι : Matrix (Fin n) (Fin m) R)

def ActsOnFlag (g : Matrix (Fin n) (Fin n) R) (t : R) (h : Matrix (Fin m) (Fin m) R) : Prop :=
  g *ᵥ x = t • x ∧ ∀ z, ∃ a : R, g *ᵥ (ι *ᵥ z) = ι *ᵥ (h *ᵥ z) + a • x

variable {x ι} {g g' : Matrix (Fin n) (Fin n) R} {t t' : R} {h h' : Matrix (Fin m) (Fin m) R}

theorem ActsOnFlag.mul (H : ActsOnFlag x ι g t h) (H' : ActsOnFlag x ι g' t' h') :
    ActsOnFlag x ι (g * g') (t * t') (h * h') := by
  refine ⟨by rw [← Matrix.mulVec_mulVec, H'.1, Matrix.mulVec_smul, H.1, smul_smul, mul_comm], fun z => ?_⟩
  obtain ⟨a', ha'⟩ := H'.2 z
  obtain ⟨a, ha⟩ := H.2 (h' *ᵥ z)
  refine ⟨a + a' * t, ?_⟩
  rw [← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_smul, H.1, smul_smul, add_smul, add_assoc,
    Matrix.mulVec_mulVec z h h']

theorem ActsOnFlag.inv (H : ActsOnFlag x ι g t h) (hg : g' * g = 1) (ht : t' * t = 1) (hh : h * h' = 1) :
    ActsOnFlag x ι g' t' h' := by
  have h1 : g' *ᵥ x = t' • x := by
    have : g' *ᵥ (g *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]
    rw [H.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this, smul_smul, ht, one_smul]
  refine ⟨h1, fun z => ?_⟩
  obtain ⟨a, ha⟩ := H.2 (h' *ᵥ z)
  have := congrArg (g' *ᵥ ·) ha
  simp only [Matrix.mulVec_mulVec z h h', hh, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, h1] at this
  rw [Matrix.mulVec_mulVec _ g' g, hg, Matrix.one_mulVec, smul_smul] at this
  exact ⟨-(a * t'), by rw [this, neg_smul, add_neg_cancel_right]⟩

theorem ActsOnFlag.coords (H : ActsOnFlag x ι g t h) {l : Fin n → R} (hl : l ⬝ᵥ x = 1) {L : Matrix (Fin m) (Fin n) R}
    (hL : L * ι = 1) (hLx : L *ᵥ x = 0) : t = l ⬝ᵥ (g *ᵥ x) ∧ h = L * g * ι := by
  refine ⟨by rw [H.1, dotProduct_smul, hl, smul_eq_mul, mul_one], Matrix.ext_of_mulVec_single fun j => ?_⟩
  obtain ⟨a, ha⟩ := H.2 (Pi.single j 1)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hLx, smul_zero, add_zero,
    Matrix.mulVec_mulVec _ L, hL, Matrix.one_mulVec]

end Tri

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}

theorem exists_dual (hσ : ∀ x, σ (σ x) = x) (h : GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j)
    (hd : W₁.J.det ≠ 0) : ∃ (l : Fin n → AE F E) (L : Matrix (Fin n₁) (Fin n) (AE F E)),
      l ⬝ᵥ incV F H.x = 1 ∧ L * incM F H.ι = 1 ∧ L *ᵥ incV F H.x = 0 := by
  refine ⟨incV F (W.J *ᵥ fun i => σ (H.y i)), incM F ((W₁.J⁻¹)ᵀ * (W.J * H.ι.map σ)ᵀ), ?_, ?_, ?_⟩
  · have := congrArg (inclR (F := F) (AF F)) h.2.2.2.1
    rw [map_one, form, dotProduct_comm, RingHom.map_dotProduct] at this
    exact this
  · rw [incM, incM, ← Matrix.map_mul, Matrix.mul_assoc, ← Matrix.transpose_transpose H.ι, Matrix.transpose_transpose H.ι,
      show (W.J * H.ι.map σ)ᵀ * H.ι = W₁.Jᵀ from by
        rw [← h.2.2.2.2.2, Matrix.mul_assoc, Matrix.transpose_mul H.ιᵀ, Matrix.transpose_transpose],
      ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · have : (W.J * H.ι.map σ)ᵀ *ᵥ H.x = 0 := by
      funext j
      have h1 := GlobalTheory.LeviPlaneSection.form_skew hσ hsk H.x (H.ι *ᵥ Pi.single j 1)
      rw [(h.2.2.2.2.1 _).1, map_zero, neg_zero] at h1
      rw [Pi.zero_apply, ← h1, form, Matrix.mulVec_single_one]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.col_apply,
        mul_comm]
    rw [← GlobalTheory.UnipCocptForm.incV_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero]
    funext i
    exact map_zero _

theorem exists_levi_formula (hσ : ∀ x, σ (σ x) = x) (h : GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j)
    (hd : W₁.J.det ≠ 0) : ∃ A B C : Matrix (Fin n) (Fin n) (AE F E), ∀ t (m : UA σ W.J), IsLevi (W₁ := W₁) H t 1 m →
      mat m = t.1 • A + cA σ (t⁻¹).1 • B + C := by
  choose α β z hz using fun j : Fin n => GLTwo.IsHypPlane.decompA hσ h hsk hd (Pi.single j 1)
  refine ⟨Matrix.of fun i j => α j * incV F H.x i, Matrix.of fun i j => β j * incV F H.y i,
    Matrix.of fun i j => (incM F H.ι *ᵥ z j) i, fun t m hm => Matrix.ext fun i j => ?_⟩
  have := congrFun (congrArg (mat m *ᵥ ·) (hz j)) i
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hm.1, hm.2.1, hm.2.2, mat_one, Matrix.mul_one,
    Matrix.mulVec_single_one, Matrix.col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  simp only [this, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  ring

theorem mat_mul_inv {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem actsOnFlag_unip {u : UA σ W.J} (hu : u ∈ unip σ W H) : ActsOnFlag (incV F H.x) (incM F H.ι) (mat u) 1 1 := by
  induction hu using Subgroup.closure_induction with
  | mem u hu => exact ⟨by rw [one_smul]; exact hu.1, fun z => by rw [Matrix.one_mulVec]; exact hu.2 z⟩
  | one => exact ⟨by rw [mat_one, Matrix.one_mulVec, one_smul], fun z => ⟨0, by simp [mat_one]⟩⟩
  | mul a b _ _ ha hb => simpa only [mul_one, ← mat_mul] using ha.mul hb
  | inv a _ ha => exact ha.inv (mat_inv_mul a) (mul_one _) (mul_one _)

theorem actsOnFlag_levi {t : (AE F E)ˣ} {y : UA σ W₁.J} {m : UA σ W.J} (hm : IsLevi (W₁ := W₁) H t y m) :
    ActsOnFlag (incV F H.x) (incM F H.ι) (mat m) t.1 (mat y) :=
  ⟨hm.1, fun z => ⟨0, by rw [Matrix.mulVec_mulVec, hm.2.2, Matrix.mulVec_mulVec, zero_smul, add_zero]⟩⟩

theorem isLevi_inv {t : (AE F E)ˣ} {m : UA σ W.J} (hm : IsLevi (W₁ := W₁) H t 1 m) : IsLevi (W₁ := W₁) H t⁻¹ 1 m⁻¹ := by
  refine ⟨((actsOnFlag_levi hm).inv (h' := 1) (mat_inv_mul m) t.inv_mul (Matrix.mul_one _)).1, ?_, ?_⟩
  · have : mat m⁻¹ *ᵥ (mat m *ᵥ incV F H.y) = incV F H.y := by rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [hm.2.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this, smul_smul, ← map_mul, inv_inv, Units.mul_inv, map_one, one_smul]
  · have := hm.2.2
    rw [mat_one, Matrix.mul_one] at this ⊢
    conv_lhs => rw [← this, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

theorem continuous_of_isInd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
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
      (IsCompact Kc ∧ (1 : GAd σ (c₀ • W.J.map σ)) ∈ Kc ∧ ∀ k ∈ Kc, ∀ k' ∈ K', k * k' ∈ Kc) → (∀ i, ContinuousOn (a i) Kc) → Continuous Ψ := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hg c₀ hc₀ hJ₁ hJ M hMc hM _ r Xf Yf _ X' Y' hW hX _ _ S' χ _ hχ
    K₁ _ K' _ Kc d ψs a Ψ hI hψ hK ha
  have h : GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, horth, hg⟩
  have hd : W₁.J.det ≠ 0 := fun h0 => hJ₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  obtain ⟨l, L, hl, hL, hLx⟩ := exists_dual hσ h hsk hd
  obtain ⟨A, B, C, hABC⟩ := exists_levi_formula hσ h hsk hd
  have hs : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  let φ := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀
  let φ₁ := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀
  have hemb : Continuous (emb hσ W W₁ hc₀ M) :=
    (GLTwo.continuous_toGAd hσ W.J hc₀).1.comp (hMc.comp (GLTwo.continuous_toGAd hσ W₁.J hc₀).2)
  have hmat : Continuous fun g : GAd σ (c₀ • W.J.map σ) => mat (φ.symm g) := GlobalTheory.StdPar.continuous_mat
  have hmat' : Continuous fun g : GAd σ (c₀ • W.J.map σ) => mat (φ.symm g)⁻¹ := GlobalTheory.StdPar.continuous_mat.comp continuous_inv
  let τ : Matrix (Fin n) (Fin n) (AE F E) → AE F E := fun g => l ⬝ᵥ (g *ᵥ incV F H.x)
  have hτ : Continuous τ := continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  let μ : AE F E → AE F E → Matrix (Fin n) (Fin n) (AE F E) := fun s s' => s • A + cA σ s' • B + C
  have hμ : ∀ {f f' : GAd σ (c₀ • W.J.map σ) → AE F E}, Continuous f → Continuous f' → Continuous fun g => μ (f g) (f' g) :=
    fun h1 h2 => ((h1.smul continuous_const).add ((hs.comp h2).smul continuous_const)).add continuous_const
  let β : Matrix (Fin n) (Fin n) (AE F E) → Matrix (Fin n₁) (Fin n₁) (AE F E) := fun g => L * g * incM F H.ι
  have hβ : Continuous β := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have he := (Units.isClosedEmbedding_embedProduct (α := AE F E)).prodMap
    (((Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) (AE F E))).comp
      (isClosedEmbedding_matHom_GAd σ (c₀ • W.J.map σ))).prodMap
    ((Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n₁) (Fin n₁) (AE F E))).comp
      (isClosedEmbedding_matHom_GAd σ (c₀ • W₁.J.map σ))))
  refine continuous_of_closed_coords hK.1 he
    (c := fun g => ((τ (mat (φ.symm g)), MulOpposite.op (τ (mat (φ.symm g)⁻¹))),
      (μ (τ (mat (φ.symm g))) (τ (mat (φ.symm g)⁻¹)), MulOpposite.op (μ (τ (mat (φ.symm g)⁻¹)) (τ (mat (φ.symm g))))),
      (β (mat (φ.symm g)), MulOpposite.op (β (mat (φ.symm g)⁻¹)))))
    (((hτ.comp hmat).prodMk (MulOpposite.continuous_op.comp (hτ.comp hmat'))).prodMk
      (((hμ (hτ.comp hmat) (hτ.comp hmat')).prodMk (MulOpposite.continuous_op.comp (hμ (hτ.comp hmat') (hτ.comp hmat)))).prodMk
      ((hβ.comp hmat).prodMk (MulOpposite.continuous_op.comp (hβ.comp hmat')))))
    (T := {q | IsLevi (W₁ := W₁) H q.2.1 1 (φ.symm q.2.2.1) ∧
      q.1 * (emb hσ W W₁ hc₀ M q.2.2.2)⁻¹ * q.2.2.1⁻¹ ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}}) ?_ ?_
    (Φ := fun z => (χ z.1.1 : ℂ) * ∑ i, ψs i z.1.2.2 * a i z.2) ?_ ?_ ?_
  · have hm := hmat.comp (continuous_fst.comp (continuous_snd.comp (continuous_snd
      (X := GAd σ (c₀ • W.J.map σ)) (Y := (AE F E)ˣ × GAd σ (c₀ • W.J.map σ) × GAd σ (c₀ • W₁.J.map σ)))))
    have ht := continuous_fst.comp (continuous_snd
      (X := GAd σ (c₀ • W.J.map σ)) (Y := (AE F E)ˣ × GAd σ (c₀ • W.J.map σ) × GAd σ (c₀ • W₁.J.map σ)))
    refine IsClosed.inter (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)) ?_
    · exact isClosed_eq (hm.matrix_mulVec continuous_const) ((Units.continuous_val.comp ht).smul continuous_const)
    · exact isClosed_eq (hm.matrix_mulVec continuous_const) ((hs.comp (Units.continuous_coe_inv.comp ht)).smul continuous_const)
    · exact isClosed_eq (hm.matrix_mul continuous_const) continuous_const
    · exact (GlobalTheory.StdPar.isClosed_unip {0} hcm hJ hW).preimage ((continuous_fst.mul (hemb.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd))).inv).mul
        (continuous_fst.comp (continuous_snd.comp continuous_snd)).inv)
  · rintro ⟨p, t, m, y⟩ ⟨h1, h2⟩
    obtain ⟨u, hu⟩ := φ.surjective (p * (emb hσ W W₁ hc₀ M y)⁻¹ * m⁻¹)
    have hu' : u ∈ unip σ W H := (h.mem_unip_iff hσ hsk hd hc₀ hW (Nat.succ_pos r) hX u).2 (hu ▸ h2)
    have hp : φ.symm p = u * φ.symm m * M (φ₁.symm y) := φ.injective (by
      rw [map_mul, map_mul, hu, φ.apply_symm_apply, φ.apply_symm_apply, inv_mul_cancel_right]
      exact (inv_mul_cancel_right _ _).symm)
    have a1 : ActsOnFlag (incV F H.x) (incM F H.ι) (mat (φ.symm p)) t.1 (mat (φ₁.symm y)) := by
      simpa only [hp, mat_mul, one_mul, mul_one, Units.val_one, mat_one] using
        ((actsOnFlag_unip hu').mul (actsOnFlag_levi h1)).mul (actsOnFlag_levi (hM (φ₁.symm y)))
    have a2 := a1.inv (mat_inv_mul _) t.inv_mul (mat_mul_inv _)
    obtain ⟨e1, e2⟩ := a1.coords hl hL hLx
    obtain ⟨e3, e4⟩ := a2.coords hl hL hLx
    have e5 := hABC _ _ h1
    have e6 := hABC _ _ (isLevi_inv h1)
    rw [inv_inv] at e6
    simp only [τ, β, μ, ← e1, ← e2, ← e3, ← e4]
    exact Prod.ext rfl (Prod.ext (Prod.ext e5 (congrArg MulOpposite.op e6)) rfl)
  · exact (hχ.comp (continuous_fst.comp continuous_fst)).mul (continuous_finset_sum _ fun i _ =>
      ((hψ i).1.cont.comp (continuous_snd.comp (continuous_snd.comp continuous_fst))).mul
        ((ha i).restrict.comp continuous_snd))
  · intro g
    obtain ⟨u, hu, t, m, y, k, hk, hm, rfl⟩ := hI.1 g
    refine ⟨(u * φ m * emb hσ W W₁ hc₀ M y, t, φ m, y), ⟨?_, ?_⟩, k, hk, rfl⟩
    · simpa only [φ.symm_apply_apply] using hm
    · simpa only [mul_inv_cancel_right] using hu
  · rintro ⟨p, t, m, y⟩ ⟨h1, h2⟩ k
    have := hI.2 _ h2 t (φ.symm m) y k k.2 h1
    rwa [show GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (φ.symm m) = m from φ.apply_symm_apply m, inv_mul_cancel_right,
      inv_mul_cancel_right] at this

end GlobalTheory.ThK.CuspTransfer

end
