import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproB
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproCa
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproCb
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open scoped ContDiff ComplexConjugate InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

instance scUN (N : ℕ) : SecondCountableTopology (UN N) :=
  (Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ Matrix.unitaryGroup (Fin N) ℂ)).secondCountableTopology

theorem one_mem_GLs' : (1 : Mat N) ∈ GLs N := by simp [GLs]

theorem local_repro (hK : KerEx) (hM : MultAlg) (hB : Bridge.BridgeSt) (W : Submodule ℂ (Kinf E N → ℂ))
    (hW : FiniteDimensional ℂ W) (R : ℝ) (v : InfinitePlace E) [MeasurableSpace (G N)] [BorelSpace (G N)]
    (μ0 : Measure (G N)) [μ0.IsHaarMeasure] :
    ∃ a : G N → ℂ, Continuous a ∧ HasCompactSupport a ∧ ∀ φ : Sm E N,
      (∀ g, (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W) →
      PositivityTheory.Rg.BcB.SpectralAccumulation.InfBdd R (Submodule.span ℂ {φ}) →
      ∃ s : ℂ, 1 / 2 ≤ ‖s‖ ∧ ∀ g : GA E N, ∫ t, a t * φ.1 (g * infP N (Pi.mulSingle v t)) ∂μ0 = s * φ.1 g := by
  obtain ⟨g, T, hT, hg, hval⟩ := exists_bump N R
  obtain ⟨c0, hc0⟩ := hK N
  obtain ⟨k, hk⟩ := (hc0 μ0 (Mv W hW v)).1 [] g T hg
  have hmult : IsMult μ0 (Mv W hW v) k (fun χ => coshT g (cas χ)) T :=
    ⟨1, fun _ => 1, fun _ => [], fun _ => g, fun _ => k, fun _ => ⟨hg, hk⟩, fun y _ => by simp,
      fun χ => by simp [zVal]⟩
  have hact := (hM N μ0 (Mv W hW v) k k _ _ T T hmult hmult).2.2.2
  have : CompleteSpace (Mv W hW v).V := FiniteDimensional.complete ℂ _
  set b : G N → (Mv W hW v).V := fun y =>
    (InnerProductSpace.toDual ℂ (Mv W hW v).V).symm ((evL W hW v 1).comp (k y.val)) with hbdef
  have hb : ∀ y w, ⟪b y, w⟫_ℂ = toFun W v (k y.val w) 1 := fun y w => by
    rw [hbdef, InnerProductSpace.toDual_symm_apply]; rfl
  have hbc : Continuous b :=
    (InnerProductSpace.toDual ℂ (Mv W hW v).V).symm.continuous.comp
      ((ContinuousLinearMap.compL ℂ _ _ ℂ (evL W hW v 1)).continuous.comp (mult_continuous hmult))
  set c : G N → UN N → ℂ := fun y u => conj (toFun W v (b y) u) with hcdef
  have hcc : Continuous (Function.uncurry c) :=
    Complex.continuous_conj.comp ((continuous_toFun₂ W hW v).comp ((hbc.comp continuous_fst).prodMk continuous_snd))
  set Kc := tsupport fun y : G N => k y.val with hKcdef
  have hKc : IsCompact Kc := mult_hasCompactSupport hmult
  have hk0 : ∀ y, y ∉ Kc → k y.val = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (f := fun y : G N => k y.val) hy
  have hcK : ∀ y u, y ∉ Kc → c y u = 0 := by
    intro y u hy
    have hb0 : b y = 0 := by simp [hbdef, hk0 y hy]
    have ht : toFun W v (b y) = 0 := by rw [hb0]; exact (toFun W v).map_zero
    simp [hcdef, ht]
  set ι : UN N → G N := fun u => Unitary.toUnits u with hιdef
  have hι : Continuous ι := continuous_toUnitsU N
  set Ku : Subgroup (G N) := (Unitary.toUnits (R := Mat N)).range with hKudef
  have hKu : IsCompact (Ku : Set (G N)) := by
    have : (Ku : Set (G N)) = Set.range ι := by ext x; simp [Ku, ι]
    rw [this]; exact isCompact_range hι
  have hιK : ∀ u, ι u ∈ Ku := fun u => ⟨u, rfl⟩
  obtain ⟨ha1, ha2⟩ := avg_cont_supp (nuN N) Ku hKu ι hι hιK c hcc Kc hKc hcK
  refine ⟨_, ha1, ha2, ?_⟩
  intro φ hφ hR
  obtain ⟨χ, hχb, hχ⟩ := exists_chi hB R v φ hR
  refine ⟨coshT g (cas χ), hval χ hχb, fun g0 => ?_⟩
  set F := sec W hW v φ.1 φ.2 hφ g0 with hFdef
  have hF := sec_mem_CE W hW v φ.1 φ.2 hφ g0
  have hE := sec_isEig W hW v φ.1 φ.2 hφ g0 χ (hχ g0)
  have h1 := hact χ F hF hE 1 one_mem_GLs'
  set h : G N → ℂ := fun t => φ.1 (g0 * infP N (Pi.mulSingle v t)) with hhdef
  have hh : Continuous h := continuous_along_infP v g0 φ.1 φ.2
  have hFc : Continuous fun y : G N => F y.val :=
    hF.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs
  have hint : Integrable (fun y : G N => k y.val (F (1 * y.val))) μ0 := by
    simp only [one_mul]
    refine Continuous.integrable_of_hasCompactSupport ((mult_continuous hmult).clm_apply hFc) ?_
    exact HasCompactSupport.intro hKc fun y hy => by simp [hk0 y hy]
  have h2 := congrArg (evL W hW v 1) h1
  simp only [PositivityTheory.RgBcC.act] at h2
  rw [← ContinuousLinearMap.integral_comp_comm _ hint] at h2
  have hL : ∀ y : G N, evL W hW v 1 (k y.val (F (1 * y.val))) = ∫ u, c y u * h (y * ι u) ∂nuN N := by
    intro y
    rw [one_mul, evL_apply, ← hb]
    refine (inner_eq W v (b y) (F y.val)).trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
    simp only [hcdef, hhdef]
    rw [toFun_sec W hW v φ.1 φ.2 hφ g0 (val_mem_GLs y) u]
    congr 1
    rw [show y.val * u.1 = (y * ι u).val from rfl, along_val]
  have hRHS : evL W hW v 1 (coshT g (cas χ) • F 1) = coshT g (cas χ) * φ.1 g0 := by
    rw [map_smul, evL_apply, toFun_sec W hW v φ.1 φ.2 hφ g0 one_mem_GLs' 1, smul_eq_mul]
    congr 1
    simpa using along_one' v g0 φ.1
  simp_rw [hL] at h2
  rw [hRHS] at h2
  rw [← h2, swap_right μ0 (nuN N) Ku hKu ι hι hιK c hcc Kc hKc hcK h hh]

end PositivityTheory.Rg.BcB.CG.ReproL
