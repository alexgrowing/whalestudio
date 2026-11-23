import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeSpaceFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionFockDegreeFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeLeSpanInvariantVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingMulOfAdaptedPlaneStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.WtSplit

open Module

theorem isSemisimple_of_iSup_eigenspace' {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : End ℂ V} (hf : ⨆ α, f.eigenspace α = ⊤) : f.IsSemisimple := by
  classical
  have hfin : Set.Finite {α : ℂ | f.HasEigenvalue α} := Module.End.finite_hasEigenvalue f
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := ∏ α ∈ hfin.toFinset, (Polynomial.X - Polynomial.C α))
    (Polynomial.separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h).squarefree ?_
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← hf]
  refine iSup_le fun α v hv => ?_
  by_cases hα : f.HasEigenvalue α
  · rw [LinearMap.mem_ker, ← Finset.prod_erase_mul _ _ (hfin.mem_toFinset.mpr hα), map_mul,
      End.mul_apply]
    have : Polynomial.aeval f (Polynomial.X - Polynomial.C α) v = 0 := by
      simp [End.mem_eigenspace_iff.mp hv]
    rw [this, map_zero]
  · rw [End.hasEigenvalue_iff, not_not] at hα
    rw [hα, Submodule.mem_bot] at hv
    rw [hv]; exact zero_mem _

theorem le_span_sup_span {P : Type} [AddCommGroup P] [Module ℂ P] (V : Submodule ℂ P) [FiniteDimensional ℂ V]
    {ι : Type} (A : ι → End ℂ P) (lam : ι → ℂ) (hmap : ∀ i, ∀ x ∈ V, A i x ∈ V)
    (hcomm : ∀ i j, ∀ x ∈ V, A i (A j x) = A j (A i x))
    (hss : ∀ i, V ≤ Submodule.span ℂ {x | x ∈ V ∧ ∃ c : ℂ, A i x = c • x}) :
    V ≤ Submodule.span ℂ {x | x ∈ V ∧ ∀ i, A i x = lam i • x} ⊔
      Submodule.span ℂ {x | x ∈ V ∧ ∃ i, ∃ c : ℂ, c ≠ lam i ∧ A i x = c • x} := by
  let B : ι → End ℂ V := fun i => (A i).restrict (hmap i)
  have hB : ∀ i (y : V), ((B i y : V) : P) = A i y := fun i y => rfl
  have hspan : ∀ i, ⨆ μ, (B i).eigenspace μ = ⊤ := by
    intro i
    rw [eq_top_iff]
    rintro y -
    have hy : (y : P) ∈ (⨆ μ, (B i).eigenspace μ).map V.subtype := by
      refine Submodule.span_le.2 ?_ (hss i y.2)
      rintro x ⟨hx, c, hc⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      refine Submodule.mem_iSup_of_mem c ?_
      rw [End.mem_eigenspace_iff]
      exact Subtype.ext hc
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    rwa [← this]
  have hsemi : ∀ i, (B i).IsSemisimple := fun i => isSemisimple_of_iSup_eigenspace' (hspan i)
  have hgen : ∀ i μ, (B i).maxGenEigenspace μ = (B i).eigenspace μ := fun i μ =>
    (hsemi i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have htop : ⨆ χ : ι → ℂ, ⨅ i, (B i).maxGenEigenspace (χ i) = ⊤ := by
    refine End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute B ?_ ?_
    · intro i j _
      refine LinearMap.ext fun y => Subtype.ext ?_
      exact hcomm i j y y.2
    · intro i
      simp_rw [hgen]
      exact hspan i
  intro x hx
  have hy : (⟨x, hx⟩ : V) ∈ (⨆ χ : ι → ℂ, ⨅ i, (B i).maxGenEigenspace (χ i)) := by rw [htop]; trivial
  have hle : (⨆ χ : ι → ℂ, ⨅ i, (B i).maxGenEigenspace (χ i)) ≤
      (Submodule.span ℂ {x | x ∈ V ∧ ∀ i, A i x = lam i • x} ⊔
        Submodule.span ℂ {x | x ∈ V ∧ ∃ i, ∃ c : ℂ, c ≠ lam i ∧ A i x = c • x}).comap V.subtype := by
    refine iSup_le fun χ z hz => ?_
    simp_rw [hgen] at hz
    have hz' : ∀ i, A i z = χ i • (z : P) := fun i => by
      have := (Submodule.mem_iInf _).1 hz i
      rw [End.mem_eigenspace_iff] at this
      exact congrArg Subtype.val this
    by_cases h : ∀ i, χ i = lam i
    · refine Submodule.mem_sup_left (Submodule.subset_span ⟨z.2, fun i => ?_⟩)
      show A i z = lam i • (z : P)
      rw [hz' i, h i]
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Submodule.mem_sup_right (Submodule.subset_span (show (z : P) ∈ _ from ⟨z.2, i, χ i, hi, hz' i⟩))
  exact hle hy

end GlobalTheory.WtSplit

namespace GlobalTheory.WtSplit

section Tens

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

noncomputable def archPt (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)

theorem evI_archPt (t : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (archPt t i) = t i := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) = t i
  exact RingEquiv.apply_symm_apply _ _

theorem at_archPt (t : κ → mixedEmbedding.mixedSpace F) : At (evI F) (archPt t) := by
  intro u' hu'
  have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
  funext i
  refine Prod.ext ?_ ?_
  · show u'.1 * (archPt t i).1 = 0
    rw [h0, zero_mul]
  · show u'.2 * (archPt t i).2 = 0
    simp [archPt]

theorem tens_injective {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0) (hR : ∀ f : SInf F κ, Rest (evI F) (⇑f) R)
    {f g : SInf F κ} (h : tens (evI F) (⇑f) R = tens (evI F) (⇑g) R) : f = g := by
  refine DFunLike.ext f g fun t => ?_
  have h1 := congrFun h (archPt t)
  have hR' : R (archPt t) = R 0 := by
    have := (hR f).1 0 (archPt t) (at_archPt t)
    rwa [zero_add] at this
  simp only [tens, evI_archPt, hR'] at h1
  exact mul_right_cancel₀ hR0 h1

end Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem acts_comm {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) {k k' : UA σ W.J} (hkk : k * k' = k' * k)
    {f f₁ f₂ g₁ g₂ : SInf F (Fin n × Fin d)} (h1 : Acts (evI F) (om (1, k')) (⇑f) (⇑f₁))
    (h2 : Acts (evI F) (om (1, k)) (⇑f₁) (⇑f₂)) (h3 : Acts (evI F) (om (1, k)) (⇑f) (⇑g₁))
    (h4 : Acts (evI F) (om (1, k')) (⇑g₁) (⇑g₂)) : f₂ = g₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz (F := F) (Fin n × Fin d)
  refine tens_injective hR0 hR ?_
  have e1 : tens (evI F) (⇑f₂) R = om (1, k * k') (tens (evI F) (⇑f) R) := by
    have : ((1 : UA σ Y.J), k * k') = (1, k) * (1, k') := by simp
    rw [this, map_mul, Module.End.mul_apply, h1 R (hR f), h2 R (hR f₁)]
  have e2 : tens (evI F) (⇑g₂) R = om (1, k' * k) (tens (evI F) (⇑f) R) := by
    have : ((1 : UA σ Y.J), k' * k) = (1, k') * (1, k) := by simp
    rw [this, map_mul, Module.End.mul_apply, h3 R (hR f), h4 R (hR g₁)]
  rw [e1, e2, hkk]

end GlobalTheory.WtSplit

namespace GlobalTheory.WtSplit

open Module

set_option maxHeartbeats 1000000 in
theorem lowPart_le_tw_sup_off : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      lowPartInf B G.M R.p ≤ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) ⊔ offPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  classical
  have hB := hm.triple.base
  have hg := hm.triple.geo

  have hop : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (om (1, k)) (⇑f) (⇑(A f)) :=
    fun k hk => GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om _ _ hB hg.hM hm.triple.weil k hk
  have hop' : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin a' × Fin (b + 2 + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (b + 2 + a')),
      ∀ f : SInf F (Fin a' × Fin (b + 2 + a')), Acts (evI F) (om' (1, k)) (⇑f) (⇑(A f)) :=
    fun k hk => GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V' G.W G.M' om' _ _ hB hg.hM' hm.triple.weil' k hk

  have hdesc : ∀ k ∈ KInf σ G.W B.emb, ∃ T : R.Pi →ₗ[ℂ] R.Pi, ∀ f ∈ G.M.Pol B.ψ B.emb,
      ∀ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → R.p f₁ = T (R.p f) := by
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
  have hcommG := GlobalTheory.T.levi_embedding_mul_of_adapted_plane F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ _ _ hB hg.hW hm₁.triple.geo.hW hC.hH'
  have hV : lowPartInf B G.M R.p = (fockDeg G.M B.ψ B.emb j₀).map R.p := rfl
  haveI : FiniteDimensional ℂ (lowPartInf B G.M R.p) := by rw [hV]; infer_instance
  have hPol : ∀ f ∈ fockDeg G.M B.ψ B.emb j₀, f ∈ G.M.Pol B.ψ B.emb := fun f hf => fockDeg_le_pol _ _ _ _ hf
  let ι := {q : UA σ G.W.J × (AE F E)ˣ // q.1 ∈ KInf σ G.W B.emb ∧ IsLevi H' q.2 (1 : UA σ G₁.W.J) q.1}
  let lam : ι → ℂ := fun i => (X.α i.1.2 : ℂ) * (((absE F E i.1.2 : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)
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

end GlobalTheory.WtSplit
