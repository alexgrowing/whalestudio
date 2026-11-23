import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdNonnegReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixApplyInrInr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetIntOff

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisE

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem eisMeas : IdemEx → BumpEx → Major → FixW → FixTh → ThProd → MuCell → FibEx → RCell → TopX → AlgRich → SigLaw → OrbEx →
    EisMeas := by
  classical
  intro hIdem hBump hMaj hFixW hFixTh hThProd hMu hFib hR hTop hAlg hSig hOrb
  unfold EisMeas
  intro D n t B W d hn ψ χ θ μB μW ωB ωW hStg mu hmu M m b₀ hb₀ hrho
  have hStg' := hStg
  obtain ⟨big, hlt, hpos, hψ, hχ, hηW, hθ, hμB, hμW, hB, hW⟩ := hStg
  have hrk : B.rank = W.rank + 2 * t := d.rank_add.symm
  have hdet := hb₀.2
  let nb : hermA D t → G D t := fun b => GlobalTheory.CompanionTheory.JacobiMaps.nAt b.1 b.2
  have hnb : IsNMap nb := fun b => GlobalTheory.CompanionTheory.JacobiMaps.mat_nAt b.1 b.2
  obtain ⟨w, hw⟩ := GlobalTheory.CompanionTheory.EisE.exists_isW D t
  obtain ⟨S₁, hS₁⟩ := hMu D t mu hmu nb hnb w hw
  obtain ⟨S₂, hS₂⟩ := hFixW D n B ψ hψ χ hχ (resEta_parity hηW (by omega)) θ hθ μB hμB ωB hB
  obtain ⟨S₃, hS₃⟩ := hFixTh D W.rank t m ψ hψ χ hχ θ hθ b₀ hdet
  obtain ⟨S₄, hS₄⟩ := GlobalTheory.CompanionTheory.ColumnSplitting.YvInt.intOff_yv D W.rank t B b₀
  refine ⟨S₁ ∪ S₂ ∪ S₃ ∪ S₄, fun S hS e he => ?_⟩
  have h1S : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have h2S : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have h3S : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have h4S : S₄ ⊆ S := fun x hx => hS (by simp [hx])
  obtain ⟨he2, hcA⟩ := (hIdem D S).2 e he
  have hyS := hS₄ S h4S
  obtain ⟨hLC, hT2, hSC, hBor, hTG⟩ := GlobalTheory.CompanionTheory.MuC.hermS_facts D t e
  have hlam : (Measure.addHaar : Measure (hermS D t e)).IsAddHaarMeasure := inferInstance
  have kinv : ∀ (Φ : schwartzA θ B.rank n), Good S e (Φ : Mx D B.rank n → ℂ) →
      ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → Good S e (Ω 1) →
      ∀ u ∈ KOff D t S, ∀ g : G D t,
        Rsec M m ψ b₀ (fun g => ((ωB g) Φ).1 0) 1 Ω (g * u) = Rsec M m ψ b₀ (fun g => ((ωB g) Φ).1 0) 1 Ω g :=
    fun Φ hΦ Ω hΩ hΩg u hu g => GlobalTheory.CompanionTheory.EisE.rsec_inv M m ψ b₀ ωB Φ u
      (hS₂ S h2S e he Φ hΦ (M.emb u) (GlobalTheory.CompanionTheory.EmbK.emb_mem_KOff M S u hu)) (hS₃ S h3S e he Ω hΩ hΩg u hu) g
  rcases hS₁ S h1S e he Measure.addHaar hlam with hzero | ⟨c, hc, hcell⟩
  · refine ⟨0, GlobalTheory.CompanionTheory.EisE.isOrb_zero, fun Φ hΦ Ω hΩ hΩg _ => ?_⟩
    rw [integral_zero_measure]
    exact hzero _ (hrho Ω hΩ Φ) (kinv Φ hΦ Ω hΩ hΩg)
  · obtain ⟨μr, hμr'⟩ : ∃ μ : Measure (Mx D B.rank W.rank), ∃ 𝓕, IsCovolOne (ratMx D B.rank W.rank) μ 𝓕 :=
      GlobalTheory.Size.exists_isCovolOne W B
    obtain ⟨μt, hμt'⟩ : ∃ μ : Measure (Mx D B.rank t), ∃ 𝓕, IsCovolOne (ratMx D B.rank t) μ 𝓕 :=
      GlobalTheory.Size.exists_isCovolOne (GlobalTheory.Size.posSp D t) B
    have hμtH : μt.IsAddHaarMeasure := by
      obtain ⟨_, h, -⟩ := hμt'
      exact h
    obtain ⟨fib, hfib⟩ := hFib D W.rank B (by omega) ψ hψ θ hθ μr hμr' m.lz ⟨m.𝓖, m.hz⟩ b₀ hdet
    obtain ⟨hsfin, -, hsL, -⟩ := hSig D W.rank t B b₀ S e he he2 fib μt hfib.fin hfib.supp hfib.inv hμtH
    obtain ⟨hXT2, hXLC, hXSC, hXBor, hPBor, hemb, -⟩ := hTop D B.rank W.rank t e
    have hRich := (hAlg D θ hθ B.rank W.rank t n hn S e he).1
    have := hsfin
    have := hXBor
    have := hPBor
    have key : ∀ (Φ : schwartzA θ B.rank n), Good S e (Φ : Mx D B.rank n → ℂ) →
        ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → Good S e (Ω 1) → ∀ Bd : ℝ, (∀ y, ‖Ω 1 y‖ ≤ Bd) →
        Integrable (fun z : XS D B.rank W.rank t e => GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn (Φ : Mx D B.rank n → ℂ) (Ω 1) z.1)
          (sig S he2 (fib.prod μt)) ∧
        Integrable (fun x : hermS D t e => ∫ z : XS D B.rank W.rank t e,
          GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn (Φ : Mx D B.rank n → ℂ) (Ω 1) z.1 * pch ψ x.1.1 (qv B b₀ z.1)
            ∂(sig S he2 (fib.prod μt))) Measure.addHaar ∧
        mu (Rsec M m ψ b₀ (fun g => ((ωB g) Φ).1 0) 1 Ω) = (c : ℂ) * ∫ x : hermS D t e, ∫ z : XS D B.rank W.rank t e,
          GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn (Φ : Mx D B.rank n → ℂ) (Ω 1) z.1 * pch ψ x.1.1 (qv B b₀ z.1)
            ∂(sig S he2 (fib.prod μt)) ∂Measure.addHaar := by
      intro Φ hΦ Ω hΩ hΩg Bd hBd
      obtain ⟨hIΦ, hRx⟩ := hR D n t B W d hn ψ χ θ μB μW ωB ωW hStg' M m b₀ hdet μr μt hμr' hμt' fib hfib Ω hΩ Φ nb hnb w hw
      have hΦc : Continuous (Φ : Mx D B.rank n → ℂ) :=
        (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ B.rank n Φ Φ.2).1
      have hΩc : Continuous (Ω 1) := hΩ.cont.comp (continuous_const.prodMk continuous_id)
      obtain ⟨hintX, hxid⟩ := GlobalTheory.CompanionTheory.EisE.cell_id he2 hcA hψ hsL hyS hΦc hΩc hΦ hΩg hBd hIΦ
      obtain ⟨hA1, hA2⟩ := hcell _ (hrho Ω hΩ Φ) (kinv Φ hΦ Ω hΩ hΩg)
      have hfun : (fun x : hermS D t e => Rsec M m ψ b₀ (fun g => ((ωB g) Φ).1 0) 1 Ω (w * nb x.1)) =
          fun x => ∫ z : XS D B.rank W.rank t e,
            GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn (Φ : Mx D B.rank n → ℂ) (Ω 1) z.1 * pch ψ x.1.1 (qv B b₀ z.1)
              ∂(sig S he2 (fib.prod μt)) := by
        funext x
        exact (hRx x.1).trans (hxid x)
      refine ⟨hintX, ?_, ?_⟩
      · rw [← hfun]; exact hA1
      · rw [hA2, hfun]
    have hpchc : ∀ x : hermS D t e, Continuous fun z : XS D B.rank W.rank t e => pch ψ x.1.1 (qv B b₀ z.1) :=
      fun x => (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection hψ B b₀ x.1).2.2.2.1.comp continuous_subtype_val
    have hyvc : Continuous fun z : Mx D B.rank W.rank × Mx D B.rank t => yv B b₀ z :=
      (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection hψ B b₀ (0 : hermA D t)).2.1
    have hI1 : ∀ f ∈ algA (a := B.rank) θ hn S e, ∀ x : hermS D t e,
        Integrable (fun z : XS D B.rank W.rank t e => f z * pch ψ x.1.1 (qv B b₀ z.1)) (sig S he2 (fib.prod μt)) := by
      intro f hf x
      obtain ⟨hfc, hfcs⟩ := hRich.cc f hf
      have h2 : HasCompactSupport (f * fun z : XS D B.rank W.rank t e => pch ψ x.1.1 (qv B b₀ z.1)) := hfcs.mul_right
      exact (hfc.mul (hpchc x)).integrable_of_hasCompactSupport h2
    have bump : ∀ C : Set (Mx D W.rank t), IsCompact C → (∀ x ∈ C, IntOff S x) →
        ∃ Ω, IsTh ψ χ θ b₀ m.μ Ω ∧ Good S e (Ω 1) ∧
          (∀ y, 0 ≤ (Ω 1 y).re ∧ (Ω 1 y).im = 0 ∧ ‖Ω 1 y‖ ≤ 1) ∧ ∀ y ∈ C, Ω 1 y = 1 := by
      intro C hC hCi
      obtain ⟨η, hη⟩ := hBump D θ hθ W.rank t S e he C hC hCi
      obtain ⟨Ω, hΩ, hΩ1⟩ := hThProd D W.rank t m ψ hψ b₀ hb₀ χ hχ hηW hpos θ hθ η (fun i => (hη i).1)
      have hΩ1' : Ω 1 = fun y => ∏ i, η i (y.submatrix (fun _ => i) id) := funext hΩ1
      refine ⟨Ω, hΩ, ?_, ?_, ?_⟩
      · rw [hΩ1']
        exact GlobalTheory.CompanionTheory.EisE.good_rows fun i => (hη i).2.2.1
      · intro y
        rw [hΩ1 y]
        have hre : ∀ i, 0 ≤ (η i (y.submatrix (fun _ => i) id)).re ∧ (η i (y.submatrix (fun _ => i) id)).im = 0 :=
          fun i => ⟨((hη i).2.2.2.1 _).1, ((hη i).2.2.2.1 _).2.2⟩
        have hnn := GlobalTheory.CompanionTheory.EisE.prod_nonneg_real Finset.univ _ hre
        refine ⟨hnn.1, hnn.2, ?_⟩
        rw [norm_prod]
        refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
        obtain ⟨h0, h1, h2⟩ := (hη i).2.2.2.1 (y.submatrix (fun _ => i) id)
        have h3 : η i (y.submatrix (fun _ => i) id) = ((η i (y.submatrix (fun _ => i) id)).re : ℂ) :=
          Complex.ext (by simp) (by simp [h2])
        rw [h3, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        exact h1
      · intro y hy
        rw [hΩ1 y]
        exact Finset.prod_eq_one fun i _ => (hη i).2.2.2.2 y hy
    have hint : ∀ f ∈ algA (a := B.rank) θ hn S e, Integrable (fun x : hermS D t e =>
        ∫ z : XS D B.rank W.rank t e, f z * pch ψ x.1.1 (qv B b₀ z.1) ∂(sig S he2 (fib.prod μt))) Measure.addHaar := by
      intro f hf
      unfold PositivityTheory.Rg.Rsw.Em.algA at hf
      induction hf using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨Φ, hΦm, hΦg, hΦcs, rfl⟩ := hg
        have hC : IsCompact ((fun X => e • yv B b₀ (GlobalTheory.CompanionTheory.EisE.cutc hn X)) '' tsupport Φ) :=
          hΦcs.isCompact.image ((continuous_const_smul e).comp (hyvc.comp (GlobalTheory.CompanionTheory.EisE.continuous_cutc hn)))
        have hCi : ∀ x ∈ (fun X => e • yv B b₀ (GlobalTheory.CompanionTheory.EisE.cutc hn X)) '' tsupport Φ, IntOff S x := by
          rintro _ ⟨X, -, rfl⟩
          exact GlobalTheory.CompanionTheory.EisE.intOff_smul he _
        obtain ⟨Ω, hΩ, hΩg, hΩnn, hΩC⟩ := bump _ hC hCi
        have hpt : ∀ z : XS D B.rank W.rank t e,
            Φ (jn hn z.1.1 z.1.2) = GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn Φ (Ω 1) z.1 := by
          intro z
          by_cases h0 : Φ (jn hn z.1.1 z.1.2) = 0
          · simp [GlobalTheory.CompanionTheory.EisE.xiP, h0]
          · have hio : IntOff S (jn hn z.1.1 z.1.2) := by
              by_contra hn'
              exact h0 (by rw [hΦg (jn hn z.1.1 z.1.2), if_neg hn'])
            obtain ⟨hi1, hi2⟩ := (GlobalTheory.CompanionTheory.EisE.intOff_jn hn z.1.1 z.1.2).1 hio
            have hiy := hyS z.1 hi1 hi2
            have hmem : e • yv B b₀ z.1 ∈ (fun X => e • yv B b₀ (GlobalTheory.CompanionTheory.EisE.cutc hn X)) '' tsupport Φ :=
              ⟨jn hn z.1.1 z.1.2, subset_tsupport _ h0, by simp only [GlobalTheory.CompanionTheory.EisE.cutc_jn]⟩
            have h1 : Ω 1 (yv B b₀ z.1) = 1 := by
              rw [hΩg (yv B b₀ z.1), if_pos hiy]
              exact hΩC _ hmem
            simp [GlobalTheory.CompanionTheory.EisE.xiP, h1]
        refine (key ⟨Φ, hΦm⟩ hΦg Ω hΩ hΩg 1 (fun y => (hΩnn y).2.2)).2.1.congr
          (Filter.Eventually.of_forall fun x => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hpt z]
      | zero => simp
      | add g g' hg hg' ih ih' =>
        refine (ih.add ih').congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply, add_mul]
        rw [integral_add (hI1 g hg x) (hI1 g' hg' x)]
      | smul a g hg ih =>
        refine (ih.const_mul a).congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [integral_const_mul]
    obtain ⟨ν₀, hν₀, hν₀eq⟩ := hOrb D n W.rank t hn B hrk ψ hψ θ hθ b₀ hdet S e he he2 fib μt hfib.fin hfib.supp
      hfib.inv hμtH Measure.addHaar hlam hint
    refine ⟨c.toNNReal • Measure.map Subtype.val ν₀, GlobalTheory.CompanionTheory.EisE.isOrb_smul hν₀ _, ?_⟩
    intro Φ hΦ Ω hΩ hΩg hΩcs
    have hΩc : Continuous (Ω 1) := hΩ.cont.comp (continuous_const.prodMk continuous_id)
    obtain ⟨Bd, hBd⟩ := hΩc.bounded_above_of_compact_support hΩcs
    have hBd0 : 0 ≤ Bd := (norm_nonneg _).trans (hBd 0)
    obtain ⟨k1, k2, k3⟩ := key Φ hΦ Ω hΩ hΩg Bd hBd
    obtain ⟨Φ₀, hΦ₀m, hΦ₀g, hΦ₀nn, happ⟩ := hMaj D θ hθ B.rank n S e he (Φ : Mx D B.rank n → ℂ) Φ.2 hΦ
    have hC₀ : IsCompact ((fun y : Mx D W.rank t => e • y) '' tsupport (Ω 1)) :=
      hΩcs.isCompact.image (continuous_const_smul e)
    obtain ⟨Ω₀, hΩ₀, hΩ₀g, hΩ₀nn, hΩ₀C⟩ := bump _ hC₀ (by
      rintro _ ⟨y, -, rfl⟩
      exact GlobalTheory.CompanionTheory.EisE.intOff_smul he y)
    have hdom : ∀ y, ‖Ω 1 y‖ ≤ Bd * (Ω₀ 1 y).re := by
      intro y
      by_cases h0 : Ω 1 y = 0
      · rw [h0, norm_zero]
        exact mul_nonneg hBd0 (hΩ₀nn y).1
      · have hio : IntOff S y := by
          by_contra hn'
          exact h0 (by rw [hΩg y, if_neg hn'])
        have h1 : Ω₀ 1 y = 1 := by
          rw [hΩ₀g y, if_pos hio]
          exact hΩ₀C _ ⟨y, subset_tsupport _ h0, rfl⟩
        rw [h1, Complex.one_re, mul_one]
        exact hBd y
    obtain ⟨j1, j2, -⟩ := key ⟨Φ₀, hΦ₀m⟩ hΦ₀g Ω₀ hΩ₀ hΩ₀g 1 (fun y => (hΩ₀nn y).2.2)
    have hΦc : Continuous (Φ : Mx D B.rank n → ℂ) :=
      (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ B.rank n Φ Φ.2).1
    have hΦ₀c : Continuous Φ₀ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ B.rank n Φ₀ hΦ₀m).1
    have hΩ₀c : Continuous (Ω₀ 1) := hΩ₀.cont.comp (continuous_const.prodMk continuous_id)
    have hf₀nn : ∀ z : XS D B.rank W.rank t e, 0 ≤ (GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn Φ₀ (Ω₀ 1) z.1).re ∧
        (GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn Φ₀ (Ω₀ 1) z.1).im = 0 := by
      intro z
      obtain ⟨a1, a2⟩ := hΦ₀nn (jn hn z.1.1 z.1.2)
      obtain ⟨b1, b2, -⟩ := hΩ₀nn (yv B b₀ z.1)
      constructor
      · simp only [GlobalTheory.CompanionTheory.EisE.xiP, Complex.mul_re, Complex.conj_re, Complex.conj_im, a2, zero_mul, sub_zero]
        exact mul_nonneg a1 b1
      · simp [GlobalTheory.CompanionTheory.EisE.xiP, Complex.mul_im, a2, b2]
    have happrox : ∀ ε : ℝ, 0 < ε → ∃ f₁ : XS D B.rank W.rank t e → ℂ, Continuous f₁ ∧ HasCompactSupport f₁ ∧
        ∀ z, ‖GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn (Φ : Mx D B.rank n → ℂ) (Ω 1) z.1 - f₁ z‖ ≤
          ε * (GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn Φ₀ (Ω₀ 1) z.1).re := by
      intro ε hε
      obtain ⟨Φ₁, hΦ₁m, hΦ₁g, hΦ₁cs, hΦ₁⟩ := happ (ε / (Bd + 1)) (div_pos hε (by linarith))
      have hΦ₁c : Continuous Φ₁ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ B.rank n Φ₁ hΦ₁m).1
      have hgen : (fun z : XS D B.rank W.rank t e => Φ₁ (jn hn z.1.1 z.1.2)) ∈ algA (a := B.rank) θ hn S e :=
        Submodule.subset_span ⟨Φ₁, hΦ₁m, hΦ₁g, hΦ₁cs, rfl⟩
      refine ⟨fun z => GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn Φ₁ (Ω 1) z.1,
        (GlobalTheory.CompanionTheory.EisE.continuous_xiP hψ hΦ₁c hΩc).comp continuous_subtype_val, ?_, ?_⟩
      · have h2 : HasCompactSupport ((fun z : XS D B.rank W.rank t e => Φ₁ (jn hn z.1.1 z.1.2)) *
            fun z => (starRingEnd ℂ) (Ω 1 (yv B b₀ z.1))) := (hRich.cc _ hgen).2.mul_right
        exact h2
      · intro z
        have hxr : (GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn Φ₀ (Ω₀ 1) z.1).re =
            (Φ₀ (jn hn z.1.1 z.1.2)).re * (Ω₀ 1 (yv B b₀ z.1)).re := by
          simp only [GlobalTheory.CompanionTheory.EisE.xiP, Complex.mul_re, Complex.conj_re, Complex.conj_im,
            (hΦ₀nn (jn hn z.1.1 z.1.2)).2, zero_mul, sub_zero]
        have hdiff : GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn (Φ : Mx D B.rank n → ℂ) (Ω 1) z.1 -
            GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn Φ₁ (Ω 1) z.1 =
              ((Φ : Mx D B.rank n → ℂ) (jn hn z.1.1 z.1.2) - Φ₁ (jn hn z.1.1 z.1.2)) *
                (starRingEnd ℂ) (Ω 1 (yv B b₀ z.1)) := by
          simp only [GlobalTheory.CompanionTheory.EisE.xiP]
          ring
        rw [hxr, hdiff, norm_mul, Complex.norm_conj]
        have e1 := hΦ₁ (jn hn z.1.1 z.1.2)
        have e2 := hdom (yv B b₀ z.1)
        have a0 := (hΦ₀nn (jn hn z.1.1 z.1.2)).1
        have b0 := (hΩ₀nn (yv B b₀ z.1)).1
        have hk : ε / (Bd + 1) * Bd ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
        calc ‖(Φ : Mx D B.rank n → ℂ) (jn hn z.1.1 z.1.2) - Φ₁ (jn hn z.1.1 z.1.2)‖ * ‖Ω 1 (yv B b₀ z.1)‖
            ≤ (ε / (Bd + 1) * (Φ₀ (jn hn z.1.1 z.1.2)).re) * (Bd * (Ω₀ 1 (yv B b₀ z.1)).re) :=
              mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (div_nonneg hε.le (by linarith)) a0)
          _ = (ε / (Bd + 1) * Bd) * ((Φ₀ (jn hn z.1.1 z.1.2)).re * (Ω₀ 1 (yv B b₀ z.1)).re) := by ring
          _ ≤ ε * ((Φ₀ (jn hn z.1.1 z.1.2)).re * (Ω₀ 1 (yv B b₀ z.1)).re) :=
              mul_le_mul_of_nonneg_right hk (mul_nonneg a0 b0)
    have hmain := hν₀eq (fun z => GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn (Φ : Mx D B.rank n → ℂ) (Ω 1) z.1)
      (fun z => GlobalTheory.CompanionTheory.EisE.xiP B b₀ hn Φ₀ (Ω₀ 1) z.1)
      ((GlobalTheory.CompanionTheory.EisE.continuous_xiP hψ hΦc hΩc).comp continuous_subtype_val)
      ((GlobalTheory.CompanionTheory.EisE.continuous_xiP hψ hΦ₀c hΩ₀c).comp continuous_subtype_val)
      hf₀nn k1 j1 k2 j2 happrox
    rw [k3, hmain, integral_smul_nnreal_measure, hemb.integral_map]
    simp only [NNReal.smul_def, Real.coe_toNNReal c hc.le, Complex.real_smul]
    rfl

end GlobalTheory.CompanionTheory.EisE

end
