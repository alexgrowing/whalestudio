import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeSpaceFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionFockDegreeFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeLeSpanInvariantVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingMulOfAdaptedPlaneStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.WtSplitB

open Module GlobalTheory.WtSplit

set_option maxHeartbeats 1000000 in
theorem lowPart_le_tw_sup_off_beta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      lowPartInf B G.M R.p ≤ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p) ⊔ offPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p) := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  classical
  have hB := hm.triple.base
  have hg := hm.triple.geo
  have hop : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin a × Fin (a + (b + 2))) →ₗ[ℂ] SInf F (Fin a × Fin (a + (b + 2))),
      ∀ f : SInf F (Fin a × Fin (a + (b + 2))), Acts (evI F) (om (1, k)) (⇑f) (⇑(A f)) :=
    fun k hk => GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om _ _ hB hg.hM hm.triple.weil k hk
  have hop' : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (a + (b + 2))),
      ∀ f : SInf F (Fin (b + 2) × Fin (a + (b + 2))), Acts (evI F) (om' (1, k)) (⇑f) (⇑(A f)) :=
    fun k hk => GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V' G.W G.M' om' _ _ hB hg.hM' hm.triple.weil' k hk
  have hdesc : ∀ k ∈ KInf σ G.W B.emb, ∃ T : R.Pi →ₗ[ℂ] R.Pi, ∀ f ∈ G.M.Pol B.ψ B.emb,
      ∀ f₁ : SInf F (Fin a × Fin (a + (b + 2))), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → R.p f₁ = T (R.p f) := by
    intro k hk
    obtain ⟨A, hA⟩ := hop k hk
    obtain ⟨A', hA'⟩ := hop' k hk
    have onto : ∀ x, ∃ f ∈ G.M.Pol B.ψ B.emb, R.p f = x := by
      intro x
      have : x ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hm.real.quot.onto]; trivial
      obtain ⟨f, hf, e⟩ := this
      exact ⟨f, hf, e⟩
    have onto' : ∀ x, ∃ f ∈ G.M'.Pol B.ψ B.emb, R.p' f = x := by
      intro x
      have : x ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [hm.real.quot'.onto]; trivial
      obtain ⟨f, hf, e⟩ := this
      exact ⟨f, hf, e⟩
    have key : ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) →
        ∀ f' ∈ G.M'.Pol B.ψ B.emb, R.p f = R.p' f' → R.p f₁ = R.p' (A' f') :=
      fun f hf f₁ h1 f' hf' he => hm.real.cpt k hk f hf f' hf' f₁ (A' f') h1 (hA' f') he
    have wd : ∀ f' ∈ G.M'.Pol B.ψ B.emb, ∀ g' ∈ G.M'.Pol B.ψ B.emb, R.p' f' = R.p' g' →
        R.p' (A' f') = R.p' (A' g') := by
      intro f' hf' g' hg' he
      obtain ⟨f, hf, hfx⟩ := onto (R.p' f')
      rw [← key f hf (A f) (hA f) f' hf' hfx, key f hf (A f) (hA f) g' hg' (hfx.trans he)]
    choose g hgP hgx using onto'
    refine ⟨{ toFun := fun x => R.p' (A' (g x)), map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro x y
      rw [← map_add, ← map_add]
      exact wd _ (hgP _) _ (add_mem (hgP x) (hgP y)) (by rw [hgx, map_add, hgx, hgx])
    · intro c x
      rw [RingHom.id_apply, ← map_smul, ← map_smul]
      exact wd _ (hgP _) _ (Submodule.smul_mem _ c (hgP x)) (by rw [hgx, map_smul, hgx])
    · intro f hf f₁ h1
      exact key f hf f₁ h1 _ (hgP _) (hgx _).symm
  choose! A hA using hop
  choose! T hT using hdesc
  set j₀ := lowDegInf B G.M R.p
  have hfin := GlobalTheory.T.fock_degree_space_finiteDimensional F E σ B _ _ G.V G.W G.M _ _ _ _ hB hg.hV hg.hW hg.hM j₀
  have hstab := GlobalTheory.T.weil_action_fock_degree_formula F E σ B _ _ G.V G.W G.M om _ _ _ _ _ _ hB hg.hV hg.hW hg.hM hm.triple.weil
  have hdiag := GlobalTheory.T.fock_degree_le_span_invariant_vectors F E σ B _ _ G.V G.W G.M om _ _ _ _ _ _ hB hg.hV hg.hW hg.hM hm.triple.weil
  have hcommG := GlobalTheory.T.levi_embedding_mul_of_adapted_plane F E σ B _ _ G.W G₁.W H' a (a + b + 1) _ _ _ _ hB hg.hW hm₁.triple.geo.hW hC.hH'
  have hV : lowPartInf B G.M R.p = (fockDeg G.M B.ψ B.emb j₀).map R.p := rfl
  haveI : FiniteDimensional ℂ (lowPartInf B G.M R.p) := by rw [hV]; infer_instance
  have hPol : ∀ f ∈ fockDeg G.M B.ψ B.emb j₀, f ∈ G.M.Pol B.ψ B.emb := fun f hf => fockDeg_le_pol _ _ _ _ hf
  let ι := {q : UA σ G.W.J × (AE F E)ˣ // q.1 ∈ KInf σ G.W B.emb ∧ IsLevi H' q.2 (1 : UA σ G₁.W.J) q.1}
  let lam : ι → ℂ := fun i => (X.β i.1.2 : ℂ) * (((absE F E i.1.2 : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)
  have hTp : ∀ i : ι, ∀ f ∈ fockDeg G.M B.ψ B.emb j₀, T i.1.1 (R.p f) = R.p (A i.1.1 f) := fun i f hf =>
    (hT i.1.1 i.2.1 f (hPol f hf) _ (hA i.1.1 i.2.1 f)).symm
  have main := le_span_sup_span (lowPartInf B G.M R.p) (fun i : ι => T i.1.1) lam ?_ ?_ ?_
  · refine main.trans (sup_le_sup (Submodule.span_mono ?_) (Submodule.span_mono ?_))
    · rintro x ⟨hx, hxe⟩
      refine ⟨hx, fun k hk t hL f hf f₁ h1 hfx => ?_⟩
      rw [hT k hk f hf f₁ h1, hfx]
      exact hxe ⟨(k, t), hk, hL⟩
    · rintro x ⟨hx, i, c, hc, hxe⟩
      refine ⟨hx, i.1.1, i.2.1, i.1.2, i.2.2, c, hc, fun f hf f₁ h1 hfx => ?_⟩
      rw [hT i.1.1 i.2.1 f hf f₁ h1, hfx]
      exact hxe
  · rintro i x ⟨f, hf, rfl⟩
    rw [hTp i f hf]
    exact ⟨_, hstab i.1.1 i.2.1 j₀ f hf _ (hA i.1.1 i.2.1 f), rfl⟩
  · rintro i i' x ⟨f, hf, rfl⟩
    have hf1 := hstab i'.1.1 i'.2.1 j₀ f hf _ (hA i'.1.1 i'.2.1 f)
    have hf2 := hstab i.1.1 i.2.1 j₀ f hf _ (hA i.1.1 i.2.1 f)
    show T i.1.1 (T i'.1.1 (R.p f)) = T i'.1.1 (T i.1.1 (R.p f))
    rw [hTp i' f hf, hTp i _ hf1, hTp i f hf, hTp i' _ hf2]
    congr 1
    exact acts_comm om (hcommG _ _ _ _ i.2.2 i'.2.2) (hA i'.1.1 i'.2.1 f) (hA i.1.1 i.2.1 _)
      (hA i.1.1 i.2.1 f) (hA i'.1.1 i'.2.1 _)
  · intro i
    rw [hV]
    refine (Submodule.map_mono (hdiag i.1.1 i.2.1 j₀)).trans ?_
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨f, ⟨hf, c, hc⟩, rfl⟩
    refine ⟨⟨f, hf, rfl⟩, c, ?_⟩
    show T i.1.1 (R.p f) = c • R.p f
    rw [hTp i f hf, hc _ (hA i.1.1 i.2.1 f), map_smul]

end GlobalTheory.WtSplitB
