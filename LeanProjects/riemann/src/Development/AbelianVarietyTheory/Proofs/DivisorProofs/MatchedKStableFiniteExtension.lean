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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeSpaceFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPolynomialTripleProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionFockDegreeFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactWeilL2InvariantStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.KStableCompl

theorem fockDeg_kStable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
      ∀ (j : ℕ), ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
        Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT j k hk f hf f₁ h
  exact GlobalTheory.KInfFockDeg.fockDeg_stable_kInf F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α) (a - G.p) G.p
    (a + a' - (G.p + G.q)) (G.p + G.q) hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil k hk j f hf f₁ h

theorem exists_kStable_compl_fockDeg : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
      ∀ (j : ℕ) (S : Submodule ℂ (SInf F (Fin a × Fin (a + a')))), S ≤ GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j →
        (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ S, ∀ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ S) →
        ∃ T : Submodule ℂ (SInf F (Fin a × Fin (a + a'))), T ≤ GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j ∧
          (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ T, ∀ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ T) ∧
          S ⊓ T = ⊥ ∧ S ⊔ T = GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j := by
  classical
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT j S hSU hS
  haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F (Fin a × Fin (a + a'))
  haveI : BorelSpace (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) := inferInstance
  haveI hU : FiniteDimensional ℂ (GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j) :=
    GlobalTheory.FockDegFin.fockDeg_finiteDimensional F E σ B a (a + a') G.V G.W G.M (a - G.p) G.p
      (a + a' - (G.p + G.q)) (G.p + G.q) hT.base hT.geo.hV hT.geo.hW hT.geo.hM j
  haveI hSfin : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSU
  let ι : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
  have hι : Function.Injective ι := SchwartzMap.injective_toLp 2 volume
  let K := S.map ι
  haveI : FiniteDimensional ℂ K := Module.Finite.map S ι
  have hE := (GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hT).2.2.2
  have hle := GlobalTheory.IndLine.fockDeg_le_pol G.M B.ψ B.emb j
  refine ⟨GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j ⊓ Kᗮ.comap ι, inf_le_left, ?_, ?_, ?_⟩
  · rintro k hk f ⟨hfU, hfK⟩ f₁ h1
    obtain ⟨A, hA⟩ := GlobalTheory.ArchLocalAct.exists_op_of_KInf F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α)
      hT.base hT.geo.hM hT.weil k hk
    have huniq : ∀ g ∈ GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j, ∀ g₁ : SInf F (Fin a × Fin (a + a')),
        Acts (evI F) (om (1, k)) g g₁ → g₁ = A g := by
      intro g hg g₁ hg₁
      obtain ⟨g₂, -, -, hu⟩ := hE k hk g (hle hg)
      rw [hu g₁ hg₁, hu (A g) (hA g)]
    have hnorm : ∀ g, ‖ι (A g)‖ = ‖ι g‖ := by
      intro g
      have e := GlobalTheory.T.compact_weil_l2_invariant F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α) hT.base hT.geo.hM hT.weil k hk g (A g) (hA g)
      show ‖(A g).toLp 2 volume‖ = ‖g.toLp 2 volume‖
      rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
        eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
      rw [e]
    have hinner : ∀ g h, inner ℂ (ι (A g)) (ι (A h)) = inner ℂ (ι g) (ι h) := by
      intro g h
      rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
      simp only [← map_add, ← map_sub, ← map_smul, hnorm]
    have hAS : ∀ s ∈ S, A s ∈ S := fun s hs => hS k hk s hs (A s) (hA s)
    let AS : S →ₗ[ℂ] S := A.restrict hAS
    have hinj : Function.Injective AS := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro s hs
      rw [LinearMap.mem_ker] at hs
      have h0 : A s = 0 := congrArg Subtype.val hs
      have : ‖ι s‖ = 0 := by rw [← hnorm, h0, map_zero, norm_zero]
      rw [norm_eq_zero, ← map_zero ι] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext (hι this))
    have hsurj : Function.Surjective AS := LinearMap.injective_iff_surjective.mp hinj
    rw [huniq f hfU f₁ h1]
    refine ⟨GlobalTheory.KInfFockDeg.fockDeg_stable_kInf F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α) (a - G.p) G.p
      (a + a' - (G.p + G.q)) (G.p + G.q) hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil k hk j f hfU (A f) (hA f), ?_⟩
    show ι (A f) ∈ Kᗮ
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨s', hs'⟩ := hsurj ⟨s, hs⟩
    have e : A s'.1 = s := congrArg Subtype.val hs'
    rw [← e, hinner]
    exact (Submodule.mem_orthogonal K (ι f)).1 hfK (ι s'.1) ⟨s'.1, s'.2, rfl⟩
  · rw [eq_bot_iff]
    rintro s ⟨hs, -, hsK⟩
    have h1 : ι s ∈ K := ⟨s, hs, rfl⟩
    have h2 : ι s = 0 := by
      have := (Submodule.mem_orthogonal K (ι s)).1 hsK (ι s) h1
      exact inner_self_eq_zero.1 this
    rw [← map_zero ι] at h2
    exact (Submodule.mem_bot ℂ).2 (hι h2)
  · refine le_antisymm (sup_le hSU inf_le_left) ?_
    intro u hu
    obtain ⟨s, hs, hse⟩ := (K.orthogonalProjection (ι u)).2
    have hmem : ι u - K.starProjection (ι u) ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal (ι u)
    have hu' : u = s + (u - s) := by abel
    rw [hu']
    refine Submodule.add_mem_sup hs ⟨Submodule.sub_mem _ hu (hSU hs), ?_⟩
    show ι (u - s) ∈ Kᗮ
    rw [map_sub, hse]
    exact hmem

theorem exists_kStable_compl : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ U₀ : Submodule ℂ R.Pi, FiniteDimensional ℂ U₀ → ∃ N : Submodule ℂ R.Pi,
        (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
          Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N) ∧
        lowPartInf B G.M R.p ⊓ N = ⊥ ∧ U₀ ≤ lowPartInf B G.M R.p ⊔ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM U₀ hU₀
  have hT := hM.triple
  have hA := fockDeg_kStable hKP F E σ B a a' G X om om' hT
  have hC := exists_kStable_compl_fockDeg hKP F E σ B a a' G X om om' hT
  have hE := (GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hT).2.2.2
  have hadd := GlobalTheory.T.matched_polynomial_triple_product hKP F E σ B a a' G X om om' R Rf hM
  have hV := (GlobalTheory.T.low_part_compact_stable hKP F E σ B a a' G X om om' R Rf hM).1
  have hle := GlobalTheory.IndLine.fockDeg_le_pol G.M B.ψ B.emb

  obtain ⟨j, hj⟩ : ∃ j, U₀ ≤ (GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j).map R.p := by
    have htop : (⨆ j, (GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j).map R.p) = ⊤ := by
      rw [← Submodule.map_iSup, ← GlobalTheory.IndLine.pol_eq_iSup_fockDeg]
      exact hM.real.quot.onto
    have hdir : Directed (· ≤ ·) (fun j => (GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j).map R.p) :=
      Monotone.directed_le fun i j hij => Submodule.map_mono (GlobalTheory.IndLine.fockDeg_mono G.M B.ψ B.emb hij)
    have hfg : U₀.FG := Module.Finite.iff_fg.mp hU₀
    have hc : IsCompactElement U₀ := (Submodule.fg_iff_compact U₀).mp hfg
    obtain ⟨x, ⟨j, rfl⟩, hx⟩ := (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ U₀).mp hc
      (Set.range fun j => (GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j).map R.p) (Set.range_nonempty _)
      hdir.directedOn_range (by simp only [sSup_range, htop, le_top])
    exact ⟨j, hx⟩
  let S := GlobalTheory.IndLine.fockDeg G.M B.ψ B.emb j ⊓ (lowPartInf B G.M R.p).comap R.p
  have hSst : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ S, ∀ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ S :=
    fun k hk f hf f₁ h1 => ⟨hA j k hk f hf.1 f₁ h1, hV k hk f (hle j hf.1) f₁ h1 hf.2⟩
  obtain ⟨T, hTle, hTst, hST, hST'⟩ := hC j S inf_le_left hSst
  have h00 : ∀ k, Acts (evI F) (om (1, k)) (0 : SInf F (Fin a × Fin (a + a'))) (0 : SInf F (Fin a × Fin (a + a'))) := by
    intro k r _
    have : tens (evI F) (⇑(0 : SInf F (Fin a × Fin (a + a')))) r = 0 := by
      funext x; simp [tens]
    rw [this, map_zero]
  refine ⟨T.map R.p, ?_, ?_, ?_⟩
  · rintro k hk f hf f₁ h1 ⟨t, ht, hpt⟩
    obtain ⟨t₁, -, ht₁, -⟩ := hE k hk t (hle j (hTle ht))
    have e := hadd k hk f hf t (hle j (hTle ht)) 0 (Submodule.zero_mem _) f₁ t₁ 0 h1 ht₁ (h00 k)
      (by rw [map_zero, add_zero, hpt])
    rw [map_zero, add_zero] at e
    rw [e]
    exact ⟨t₁, hTst k hk t ht t₁ ht₁, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxV, t, ht, rfl⟩
    have : t ∈ S ⊓ T := ⟨⟨hTle ht, hxV⟩, ht⟩
    rw [hST, Submodule.mem_bot] at this
    simp [this]
  · refine hj.trans ?_
    rw [← hST', Submodule.map_sup]
    exact sup_le_sup_right (Submodule.map_le_iff_le_comap.mpr inf_le_right) _

end GlobalTheory.KStableCompl
