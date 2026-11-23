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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfClosedCoords

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.ThK.CuspTransfer

noncomputable section

namespace GlobalTheory.ThK.InducedCons

theorem exists_continuousOn_coords {G S B : Type*} [TopologicalSpace G] [TopologicalSpace S] [TopologicalSpace B] [Nonempty S]
    {e : S → B} (he : IsClosedEmbedding e) {c : G → B} (hc : Continuous c) {T : Set (G × S)} (hT : IsClosed T)
    (hec : ∀ q ∈ T, e q.2 = c q.1) :
    IsClosed {g | ∃ s, (g, s) ∈ T} ∧ ∃ s : G → S, ContinuousOn s {g | ∃ s, (g, s) ∈ T} ∧ ∀ q ∈ T, s q.1 = q.2 := by
  have hs : ∀ q ∈ T, Function.invFun e (c q.1) = q.2 := fun q hq => by
    rw [← hec q hq]; exact Function.leftInverse_invFun he.injective _
  refine ⟨?_, fun g => Function.invFun e (c g), ?_, hs⟩
  · have hD : IsClosed (Prod.map id e '' T) := (IsClosedEmbedding.id.prodMap he).isClosedMap _ hT
    convert hD.preimage (f := fun g : G => (g, c g)) (by fun_prop) using 1
    ext g
    constructor
    · rintro ⟨s, h⟩
      exact ⟨(g, s), h, Prod.ext rfl (hec _ h)⟩
    · rintro ⟨⟨g', s⟩, h, h'⟩
      obtain rfl : g' = g := congrArg Prod.fst h'
      exact ⟨s, h⟩
  · rw [he.isInducing.continuousOn_iff]
    refine hc.continuousOn.congr ?_
    rintro g ⟨s, h⟩
    exact (congrArg e (hs _ h)).trans (hec _ h)

theorem parDec_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M 1 1 1 ∧ IsClosed {g : GAd σ (c₀ • W.J.map σ) | ∃ t y, GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g} ∧
      ∃ (τ : GAd σ (c₀ • W.J.map σ) → (AE F E)ˣ) (η : GAd σ (c₀ • W.J.map σ) → GAd σ (c₀ • W₁.J.map σ)), ContinuousOn τ {g : GAd σ (c₀ • W.J.map σ) | ∃ t y, GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g} ∧
        ContinuousOn η {g : GAd σ (c₀ • W.J.map σ) | ∃ t y, GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g} ∧ ∀ t y g, GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g → τ g = t ∧ η g = y := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hg c₀ hc₀ hJ₁ hJ M hMc hM _ r Xf Yf _ X' Y' hW hX _ _
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
  have hemb : Continuous (CuspTransfer.emb hσ W W₁ hc₀ M) :=
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
  refine (exists_continuousOn_coords he
    (c := fun g => ((τ (mat (φ.symm g)), MulOpposite.op (τ (mat (φ.symm g)⁻¹))),
      (μ (τ (mat (φ.symm g))) (τ (mat (φ.symm g)⁻¹)), MulOpposite.op (μ (τ (mat (φ.symm g)⁻¹)) (τ (mat (φ.symm g))))),
      (β (mat (φ.symm g)), MulOpposite.op (β (mat (φ.symm g)⁻¹)))))
    (((hτ.comp hmat).prodMk (MulOpposite.continuous_op.comp (hτ.comp hmat'))).prodMk
      (((hμ (hτ.comp hmat) (hτ.comp hmat')).prodMk (MulOpposite.continuous_op.comp (hμ (hτ.comp hmat') (hτ.comp hmat)))).prodMk
      ((hβ.comp hmat).prodMk (MulOpposite.continuous_op.comp (hβ.comp hmat')))))
    (T := {q | IsLevi (W₁ := W₁) H q.2.1 1 (φ.symm q.2.2.1) ∧
      q.1 * (CuspTransfer.emb hσ W W₁ hc₀ M q.2.2.2)⁻¹ * q.2.2.1⁻¹ ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}}) ?_ ?_).elim fun hP hex => ?_
  rotate_right
  · obtain ⟨s, hsc, hsq⟩ := hex
    have key : ∀ t y g, IsParDec hσ W W₁ H hc₀ X' M t y g ↔ ∃ m, IsLevi (W₁ := W₁) H t 1 (φ.symm m) ∧
        g * (CuspTransfer.emb hσ W W₁ hc₀ M y)⁻¹ * m⁻¹ ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0} := by
      intro t y g
      constructor
      · rintro ⟨u, hu, m, hm, rfl⟩
        refine ⟨φ m, ?_, ?_⟩
        · simpa only [φ.symm_apply_apply] using hm
        · simpa only [φ, mul_inv_cancel_right] using hu
      · rintro ⟨m, h1, h2⟩
        refine ⟨_, h2, φ.symm m, h1, ?_⟩
        rw [show GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (φ.symm m) = m from φ.apply_symm_apply m, inv_mul_cancel_right,
          inv_mul_cancel_right]
    have hset : {g : GAd σ (c₀ • W.J.map σ) | ∃ t y, IsParDec hσ W W₁ H hc₀ X' M t y g} =
        {g | ∃ s : (AE F E)ˣ × GAd σ (c₀ • W.J.map σ) × GAd σ (c₀ • W₁.J.map σ), IsLevi (W₁ := W₁) H s.1 1 (φ.symm s.2.1) ∧
          g * (CuspTransfer.emb hσ W W₁ hc₀ M s.2.2)⁻¹ * s.2.1⁻¹ ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}} := by
      ext g
      constructor
      · rintro ⟨t, y, hp⟩
        obtain ⟨m, hm⟩ := (key t y g).1 hp
        exact ⟨(t, m, y), hm⟩
      · rintro ⟨⟨t, m, y⟩, hm⟩
        exact ⟨t, y, (key t y g).2 ⟨m, hm⟩⟩
    have h1 : IsLevi (W₁ := W₁) H 1 1 (1 : UA σ W.J) := by
      refine ⟨?_, ?_, ?_⟩ <;> simp [mat_one]
    have hM1 : M 1 = 1 := h.levi_unique hσ hsk hd (hM 1) h1
    rw [hset]
    refine ⟨⟨1, one_mem _, 1, h1, ?_⟩, hP, fun g => (s g).1, fun g => (s g).2.2, hsc.fst, hsc.snd.snd, fun t y g hp => ?_⟩
    · simp only [CuspTransfer.emb, map_one, hM1, mul_one]
    · obtain ⟨m, hm⟩ := (key t y g).1 hp
      have := hsq (g, t, m, y) hm
      exact ⟨congrArg Prod.fst this, congrArg (·.2.2) this⟩
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
    obtain ⟨u, hu⟩ := φ.surjective (p * (CuspTransfer.emb hσ W W₁ hc₀ M y)⁻¹ * m⁻¹)
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

end GlobalTheory.ThK.InducedCons

end
