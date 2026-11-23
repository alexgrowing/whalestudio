import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartLeFixedPartImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedModelThetaRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeSpaceFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionPreservesLintegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedFockDegreeSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeOddMapLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPolynomialLinesInvarianceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LieGenStep

theorem exists_kFix_map_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    {R : RealMaps F a a'} {Rf : FinMaps F a a'} (h : IsMatched B G X om om' R Rf) (m : ℕ)
    (f : SInf F (Fin a × Fin (a + a'))) (hf : f ∈ fockDeg G.M B.ψ B.emb m) :
    ∃ f₀ ∈ fockDeg G.M B.ψ B.emb m, IsKFix B om f₀ ∧ R.p f₀ = R.p f := by
  classical
  have hT := h.triple
  have hψ : IsStd B.ψ := hT.base.std
  have hw := hT.weil
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evI F) := by
    intro u _
    simp [mat]
  have hex : ∀ k : UA σ G.V.J, ∃ A : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
      k ∈ KInf σ G.V B.emb → ∀ v : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (k, 1)) v (A v) := by
    intro k
    by_cases hk : k ∈ KInf σ G.V B.emb
    · obtain ⟨A, hA⟩ := GlobalTheory.FockCompactW.exists_op_of_UAt hψ hw (k, 1) hk.1 h1W
      exact ⟨A, fun _ => hA⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose A hA using hex
  set V : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) := fockDeg G.M B.ψ B.emb m with hVdef
  have hVfin : FiniteDimensional ℂ V :=
    GlobalTheory.T.fock_degree_space_finiteDimensional F E σ B a (a + a') G.V G.W G.M _ _ _ _ hT.base hT.geo.hV hT.geo.hW
      hT.geo.hM _
  have hVst : ∀ k ∈ KInf σ G.V B.emb, ∀ v ∈ V, A k v ∈ V := fun k hk v hv =>
    GlobalTheory.LowFixCover.fockDeg_stable_left hψ hw B.emb hk (A k) (hA k hk) _ hv
  let U : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) :=
    Submodule.span ℂ {z | ∃ k ∈ KInf σ G.V B.emb, ∃ v ∈ V, z = A k v - v}
  have hUV : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, v, hv, rfl⟩
    exact V.sub_mem (hVst k hk v hv) hv)
  have hU0 : U ≤ LinearMap.ker R.p := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, v, hv, rfl⟩
    show R.p (A k v - v) = 0
    rw [map_sub, h.real.quot.cpt k hk v (fockDeg_le_pol _ _ _ _ hv) _ (hA k hk v), sub_self])
  obtain ⟨u, hu, hfx⟩ := GlobalTheory.KFixedVanish.exists_fixed
    (Measure.addHaar : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) U V hVfin hUV
    ((fun k => A k) '' KInf σ G.V B.emb)
    (by
      rintro _ ⟨k, hk, rfl⟩ v hv
      exact Submodule.subset_span ⟨k, hk, v, hv, rfl⟩)
    (by
      rintro _ ⟨k, hk, rfl⟩ v
      exact GlobalTheory.T.weil_action_preserves_lintegral F E σ a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hw (k, 1) v (A k v) (hA k hk v) _
        inferInstance)
    f hf
  refine ⟨f - u, V.sub_mem hf (hUV hu), fun k hk => ?_, ?_⟩
  · have h' := hA k hk (f - u)
    rwa [hfx (A k) ⟨k, hk, rfl⟩] at h'
  · rw [map_sub, LinearMap.mem_ker.1 (hU0 hu), sub_zero]

theorem fixDeg_le_lowDegInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    {R : RealMaps F a a'} {Rf : FinMaps F a a'} (h : IsMatched B G X om om' R Rf) :
    fixDeg B G.M om ≤ lowDegInf B G.M R.p := by
  haveI := h.real.nontriv
  obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
  have hx' : x ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [h.real.quot.onto]; trivial
  obtain ⟨f, hf, rfl⟩ := hx'
  rw [pol_eq_iSup_fockDeg] at hf
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono G.M B.ψ B.emb).directed_le).1 hf
  have hne : {k | ∃ f ∈ fockDeg G.M B.ψ B.emb k, R.p f ≠ 0}.Nonempty := ⟨k, f, hk, hx⟩
  obtain ⟨g, hg, hpg⟩ := Nat.sInf_mem hne
  obtain ⟨g₀, hg₀, hfix, hpe⟩ := exists_kFix_map_eq h _ g hg
  refine Nat.sInf_le ⟨g₀, hg₀, ?_, hfix⟩
  rintro rfl
  exact hpg (by rw [← hpe, map_zero])

theorem map_fockDeg_add_two_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ j : ℕ, (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j + 2)).map R.p ≤
        (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j)).map R.p ⊔
          Submodule.span ℂ {x : R.Pi | ∃ γ ∈ Lines σ G.W, ∃ f ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j),
            ∃ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ x = R.p f₁} := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM j
  set T := (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j)).map R.p ⊔
    Submodule.span ℂ {x : R.Pi | ∃ γ ∈ Lines σ G.W, ∃ f ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j),
      ∃ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧
        x = R.p f₁} with hTdef
  have hodd := GlobalTheory.T.fock_degree_odd_map_le hKP F E σ B a a' G X om om' R Rf hM j
  have hpol := GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hM.triple
  have hpol' := GlobalTheory.T.theta_polynomial_lines_invariance hKP F E σ B a a' G X om om' hM.triple
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨f₀, hf₀, hfix, hpe⟩ := exists_kFix_map_eq hM _ f hf
  rw [← hpe]
  have hm : fixDeg B G.M om ≤ lowDegInf B G.M R.p + 2 * j + 1 := by
    have := fixDeg_le_lowDegInf hM
    omega
  have hf₀' : f₀ ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j + 1 + 1) := hf₀
  have hspan := GlobalTheory.T.fixed_fock_degree_span hKP F E σ B a a' G X om om' R Rf hM _ hm f₀ hf₀' hfix
  have hS : ({g | g ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j + 1) ∧ IsKFix B om g} ∪
      {f₁ | ∃ γ ∈ Lines σ G.W, ∃ g ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j + 1), IsKFix B om g ∧
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁}) ⊆ (T.comap R.p : Set _) := by
    rintro y (⟨hy, -⟩ | ⟨γ, hγ, g, hg, -, hd⟩)
    · exact Submodule.mem_sup_left (hodd (Submodule.mem_map_of_mem hy))
    · obtain ⟨g', hg', hpg'⟩ := hodd (Submodule.mem_map_of_mem hg)
      obtain ⟨g₁', -, hd₁, -⟩ := hpol.2.2.1 γ hγ g' (fockDeg_le_pol _ _ _ _ hg')
      have hx : R.p g ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [hM.real.quot'.onto]; trivial
      obtain ⟨f', hf', hpf'⟩ := hx
      obtain ⟨f₁', -, hd', -⟩ := hpol'.2.2.1 γ hγ f' hf'
      have e1 := hM.real.lie γ hγ g (fockDeg_le_pol _ _ _ _ hg) f' hf' y f₁' hd hd' hpf'.symm
      have e2 := hM.real.lie γ hγ g' (fockDeg_le_pol _ _ _ _ hg') f' hf' g₁' f₁' hd₁ hd' (hpg'.trans hpf'.symm)
      show R.p y ∈ T
      rw [e1, ← e2]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨γ, hγ, g', hg', g₁', hd₁, rfl⟩)
  exact Submodule.span_le.2 hS hspan

end GlobalTheory.LieGenStep

end
