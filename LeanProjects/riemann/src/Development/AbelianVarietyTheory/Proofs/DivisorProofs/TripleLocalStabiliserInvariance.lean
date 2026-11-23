import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleArchimedeanComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPlaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearStableRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCompactOrbitFiniteDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementActsByScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimKStableContinuousInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTripleStabilizerFixedStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Topology

open GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV

noncomputable section

namespace GlobalTheory.ThKAdm

section Comm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem commute_fin_inf {d : ℕ} {W : Spc F E d} {v : Pl F} {g k : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v))
    (hk : k ∈ UAt σ W (evI F)) : g * k = k * g := by
  set A := mat g - 1 with hAdef
  set B := mat k - 1 with hBdef
  have hA : GlobalTheory.LatVac.liftV v 1 • A = A := partFin_of_at hg
  have hB : realAd F 1 • B = B := partInf_of_at hk
  have h0 : realAd F 1 • A = 0 := by
    rw [← hA, smul_smul]
    have := GlobalTheory.LatVac.at_liftV v 1 (realAd F 1) (map_zero (evalV F v))
    rw [smul_eq_mul] at this
    rw [this, zero_smul]
  have h1 : A * B = 0 := by
    rw [← hB, Matrix.mul_smul, ← Matrix.smul_mul, h0, Matrix.zero_mul]
  have h2 : B * A = 0 := by
    rw [← hB, Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero]
  have e1 : mat g = A + 1 := by rw [hAdef, sub_add_cancel]
  have e2 : mat k = B + 1 := by rw [hBdef, sub_add_cancel]
  have key : mat g * mat k = mat k * mat g := by
    rw [e1, e2]
    simp only [add_mul, mul_add, one_mul, mul_one, h1, h2]
    abel
  apply Subtype.ext; apply Units.ext
  simpa [mat] using key

end Comm

theorem adm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)),
    (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v)) → IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) →
    (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) ∈ O ∧
      ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v) → g ∈ K) →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ s : Finset (GlobalTheory.ThK.Fn F a (a + a')), (↑s ⊆ (GlobalTheory.ThK.PolData B G.M : Set (GlobalTheory.ThK.Fn F a (a + a')))) ∧
      ∀ Ψ ∈ Submodule.span ℂ (Set.range fun g : GlobalTheory.ThK.UAtSub σ G.W (GlobalTheory.AdelicU.evFin F v) => om (1, g.1) Φ),
        (∀ k ∈ K, om (1, k) Ψ = Ψ) → ∃ Ψ₀ ∈ Submodule.span ℂ (s : Set (GlobalTheory.ThK.Fn F a (a + a'))), G.M.I om (Ψ - Ψ₀) = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT v K hKv hKc hKo Φ hΦ
  classical
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (a + a') G.W.J
  haveI := i1; haveI := i2; haveI := i3; haveI := i4
  set D := PolData B G.M with hD
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hKP.base
  have hWr : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have := hT.geo.eBig; have := hT.geo.lt; left; omega
  set SA := schA F (Fin a × Fin (a + a')) with hSA
  have hsch : D ≤ SA := GlobalTheory.ThKRatInv.polData_le_schA B G.M hT.geo.hM
  have pres : ∀ x, ∀ Ψ ∈ SA, om x Ψ ∈ SA := fun x Ψ h => hT.weil.isUSplitting.pres x Ψ h
  have lin : ∀ Φ₁ ∈ SA, ∀ Φ₂ ∈ SA, ∀ c : ℂ, G.M.I om (c • Φ₁ + Φ₂) = c • G.M.I om Φ₁ + G.M.I om Φ₂ :=
    fun Φ₁ h₁ Φ₂ h₂ c => funext fun h =>
      GlobalTheory.T.theta_integral_linear_stable_range (GlobalTheory.T.weil_convergence_of_kernel hKP) F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP hWr h Φ₁ h₁ Φ₂ h₂ c
  have I0 : G.M.I om 0 = 0 := by
    have := lin 0 (zero_mem _) 0 (zero_mem _) 1
    rw [smul_zero, zero_add, one_smul] at this
    simpa using this
  let Lin : SA →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun Ψ => G.M.I om Ψ.1
      map_add' := fun x y => by simpa using lin x.1 x.2 y.1 y.2 1
      map_smul' := fun c x => by simpa [I0] using lin x.1 x.2 0 (zero_mem _) c }
  set S := Submodule.span ℂ (Set.range fun g : UAtSub σ G.W (evFin F v) => om (1, g.1) Φ) with hS
  have hSD : S ≤ D := Submodule.span_le.2 (by
    rintro _ ⟨g, rfl⟩
    exact GlobalTheory.ThKPolFin.polData_stable hA B G.M hP v g.1 g.2 Φ hΦ)
  let P : Submodule ℂ (Fn F a (a + a')) :=
    { carrier := {Ψ | Ψ ∈ S ∧ ∀ k ∈ K, om (1, k) Ψ = Ψ}
      add_mem' := fun {x y} hx hy => ⟨S.add_mem hx.1 hy.1, fun k hk => by rw [map_add, hx.2 k hk, hy.2 k hk]⟩
      zero_mem' := ⟨S.zero_mem, fun k _ => map_zero _⟩
      smul_mem' := fun c x hx => ⟨S.smul_mem c hx.1, fun k hk => by rw [map_smul, hx.2 k hk]⟩ }
  have hPsch : P ≤ SA := fun Ψ h => hsch (hSD h.1)
  let LP : P →ₗ[ℂ] (UA σ G.W.J → ℂ) := Lin.comp (Submodule.inclusion hPsch)
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (G.M.I om '' (P : Set (Fn F a (a + a'))))) := by
    have hσ := GlobalTheory.SkewToHerm.sigma_invol σ hT.base.cm
    obtain ⟨y, hy⟩ := GlobalTheory.SkewToHerm.exists_sigma_ne σ hT.base.cm
    have hc : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    have hcc : σ (y - σ y) = -(y - σ y) := by rw [map_sub, hσ]; ring
    have cont := GlobalTheory.T.continuous_left_invariant_theta hKP F E σ B a a' G X om om' hT
    set Kc := Subgroup.closure (KInf σ G.W B.emb) with hKcdef
    have hKcInf : ∀ k ∈ Kc, k ∈ UAt σ G.W (evI F) := fun k hk =>
      (Subgroup.closure_le (K := UAtSub σ G.W (evI F))).2 (fun k' hk' => hk'.1) hk
    set T := Submodule.span ℂ (Set.range fun k : Kc => G.M.I om (om (1, k.1) Φ)) with hTdef
    have hTf : FiniteDimensional ℂ T := by
      have hbot : IsCompact (((⊥ : Subgroup (UA σ G.W.J)) : Set (UA σ G.W.J))) := by
        rw [Subgroup.coe_bot]; exact isCompact_singleton
      set S₀ := Submodule.span ℂ (Set.range fun k : Subgroup.closure (KInf σ G.W B.emb ∪
        ((⊥ : Subgroup (UA σ G.W.J)) : Set (UA σ G.W.J))) => om (1, (k : UA σ G.W.J)) Φ) with hS₀
      haveI : FiniteDimensional ℂ S₀ :=
        GlobalTheory.T.polynomial_data_compact_orbit_finite_dim hKP F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hP ⊥ hbot bot_le Φ hΦ
      let S' : Submodule ℂ SA := S₀.comap SA.subtype
      haveI : FiniteDimensional ℂ S' :=
        FiniteDimensional.of_injective (K := ℂ) (V₂ := S₀) ((SA.subtype.domRestrict S').codRestrict S₀ fun x => x.2)
          fun x y e => Subtype.ext (Subtype.ext (congrArg (fun z : S₀ => (z : Fn F a (a + a'))) e))
      refine Submodule.finiteDimensional_of_le (S₂ := S'.map Lin) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      have hk : k.1 ∈ Subgroup.closure (KInf σ G.W B.emb ∪ ((⊥ : Subgroup (UA σ G.W.J)) : Set (UA σ G.W.J))) :=
        Subgroup.closure_mono Set.subset_union_left k.2
      exact ⟨⟨om (1, k.1) Φ, pres _ _ (hsch hΦ)⟩, Submodule.subset_span ⟨⟨k.1, hk⟩, rfl⟩, rfl⟩
    have hTcont : ∀ t ∈ T, Continuous t := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        have e : G.M.I om (om (1, k.1) Φ) = fun x => G.M.I om Φ (x * k.1) :=
          funext fun x => GlobalTheory.ThetaFacCompl.I_transl _ _ _ _ _
        show Continuous (G.M.I om (om (1, k.1) Φ))
        rw [e]
        exact (cont Φ hΦ).1.comp (continuous_mul_right _)
      | zero => exact continuous_const
      | add x y _ _ hx hy => exact hx.add hy
      | smul c x _ hx => exact hx.const_smul c
    have hTst : ∀ k, ∀ t ∈ T, rt Kc k t ∈ T := by
      intro k t ht
      have hle : T.map (rt Kc k) ≤ T := by
        rw [hTdef, Submodule.map_span_le]
        rintro _ ⟨k', rfl⟩
        refine Submodule.subset_span ⟨k * k', ?_⟩
        funext x
        simp only [rt_apply, GlobalTheory.ThetaFacCompl.I_transl, Subgroup.coe_mul, mul_assoc]
      exact hle ⟨t, ht, rfl⟩
    obtain ⟨U, hU, hlev⟩ := GlobalTheory.T.inert_place_triple_stabilizer_fixed hKP F E σ B a a' G X om om' hT v K hKv hKo Φ hΦ
    have hIΦT : G.M.I om Φ ∈ T := Submodule.subset_span ⟨1, by
      show G.M.I om (om (1, 1) Φ) = G.M.I om Φ
      rw [← Prod.one_eq_mk, map_one, Module.End.one_apply]⟩
    have hAtype : G.M.I om '' (P : Set (Fn F a (a + a'))) ⊆ typeSet (rt Kc) ⊤ T := by
      rintro _ ⟨Ψ, hΨP, rfl⟩
      obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hΨP.1
      let L : T →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
        ∑ g ∈ c.support, c g • ((LinearMap.funLeft ℂ ℂ fun x : UA σ G.W.J => x * g.1) ∘ₗ T.subtype)
      have hL : ∀ t : T, ∀ x, L t x = ∑ g ∈ c.support, c g * (t : UA σ G.W.J → ℂ) (x * g.1) := by
        intro t x
        simp [L, LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]
      have Isum : ∀ s : Finset (UAtSub σ G.W (evFin F v)),
          G.M.I om (∑ g ∈ s, c g • om (1, g.1) Φ) = ∑ g ∈ s, c g • G.M.I om (om (1, g.1) Φ) := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · simpa using I0
        · intro g s hg ih
          rw [Finset.sum_insert hg, Finset.sum_insert hg,
            lin _ (pres _ _ (hsch hΦ)) _ (sum_mem fun g' _ => SA.smul_mem _ (pres _ _ (hsch hΦ))), ih]
      refine ⟨L, fun _ => Submodule.mem_top, fun k t t' htt => ?_, LinearMap.mem_range.2 ⟨⟨G.M.I om Φ, hIΦT⟩, ?_⟩⟩
      · funext x
        rw [hL, rt_apply, hL, htt]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [rt_apply, mul_assoc, mul_assoc, commute_fin_inf (mem_UAtSub.1 g.2) (hKcInf k.1 k.2)]
      · funext x
        rw [hL, ← hc, Finsupp.sum, Isum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ThetaFacCompl.I_transl]
    have hAmod : ∀ φ ∈ G.M.I om '' (P : Set (Fn F a (a + a'))),
        IsSmoothModerate σ ((y - σ y) • G.W.J.map σ) (fun x => φ ((toGAd hσ G.W.J hc).symm x)) := by
      rintro _ ⟨Ψ, hΨP, rfl⟩
      obtain ⟨K', -, hK'⟩ := GlobalTheory.T.exists_maximal_compact_invariant F E σ hσ B a a' G X om om' hKP hT _ hc hcc Ψ (hSD hΨP.1)
      exact hK'.mod
    have hAlev : ∀ φ ∈ G.M.I om '' (P : Set (Fn F a (a + a'))), ∀ k ∈ U, k ∈ finU σ G.W.J → ∀ x, φ (x * k) = φ x := by
      rintro _ ⟨Ψ, hΨP, rfl⟩ k hk hkf x
      rw [← GlobalTheory.ThetaFacCompl.I_transl, hlev Ψ hΨP.1 hΨP.2 k hk hkf]
    refine GlobalTheory.T.finite_dim_K_stable_continuous_invariant hKP F E σ hσ B _ _ _ G.W hT.base hT.geo.hW hT.geo.even _ hc hcc T hTf hTcont hTst U hU _
      hAtype hAmod hAlev (fun z hz => ?_)
    obtain ⟨m, b, hb⟩ := GlobalTheory.T.central_element_acts_by_scalar hKP F E σ hσ B a a' G X om om' hT _ hc hcc z hz
    refine ⟨m, b, fun φ hφ => ?_⟩
    obtain ⟨Ψ, hΨP, rfl⟩ := hφ
    exact hb Ψ (hSD hΨP.1)
  have hfinR : FiniteDimensional ℂ (LinearMap.range LP) :=
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (G.M.I om '' (P : Set (Fn F a (a + a'))))) (by
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨x.1, x.2, rfl⟩)
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional (LinearMap.range LP)).2 hfinR
  have hpre : ∀ y : t, ∃ x : P, LP x = y.1 := fun y =>
    LinearMap.mem_range.1 (ht ▸ Submodule.subset_span (Finset.mem_coe.2 y.2))
  choose pre hpre' using hpre
  refine ⟨Finset.univ.image fun y : t => (pre y : Fn F a (a + a')), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact hSD (pre y).2.1
  · intro Ψ hΨ hKΨ
    have hΨP : Ψ ∈ P := ⟨hΨ, hKΨ⟩
    have hmem : LP ⟨Ψ, hΨP⟩ ∈ (Submodule.span ℂ (Set.range pre)).map LP := by
      rw [Submodule.map_span, ← Set.range_comp]
      have e : Set.range (LP ∘ pre) = (t : Set (UA σ G.W.J → ℂ)) := by
        ext f
        constructor
        · rintro ⟨y, rfl⟩
          simp only [Function.comp_apply, hpre']
          exact y.2
        · intro hf
          exact ⟨⟨f, hf⟩, by simp only [Function.comp_apply, hpre']⟩
      rw [e, ht]
      exact LinearMap.mem_range_self _ _
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hmem
    refine ⟨x.1, ?_, ?_⟩
    · have h1 : x.1 ∈ (Submodule.span ℂ (Set.range pre)).map P.subtype := ⟨x, hx, rfl⟩
      rw [Submodule.map_span, ← Set.range_comp] at h1
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨y, rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨y, Finset.mem_univ _, rfl⟩)
    · have e1 : Ψ - x.1 = (-1 : ℂ) • x.1 + Ψ := by rw [neg_one_smul]; abel
      have e2 : G.M.I om x.1 = G.M.I om Ψ := hxe
      rw [e1, lin x.1 (hPsch x.2) Ψ (hPsch hΨP) (-1), e2, neg_one_smul, neg_add_cancel]

end GlobalTheory.ThKAdm

end
