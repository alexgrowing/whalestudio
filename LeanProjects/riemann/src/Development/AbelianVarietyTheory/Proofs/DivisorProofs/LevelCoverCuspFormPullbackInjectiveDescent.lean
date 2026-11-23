import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NvalNonnegIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormIffLevelCoverPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonLevelCoverPullbackProbabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionConstantOnFibresDescendsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntValuationPrimeBack
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticeRationalSpanInclusionsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevRingDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem pull_zero (d : DeltaDat Xo c 0) : Pull d 0 0 := by
  intro k _ _ _ _ _ y₂ y _
  exact (evalAt_zero _ _ y₂).trans (evalAt_zero _ _ y).symm

theorem pull_add {d : DeltaDat Xo c 0} {f f' : Rul Xo c} {g g' : Rul d.Xo₂ d.c₂} (h : Pull d f g)
    (h' : Pull d f' g') : Pull d (f + f') (g + g') := by
  intro k _ _ _ _ hk y₂ y hy
  unfold evR
  rw [evalAt_add, evalAt_add]
  exact congrArg₂ (· + ·) (h k hk y₂ y hy) (h' k hk y₂ y hy)

theorem pull_smul {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (t : c.F) (h : Pull d f g) :
    Pull d (t • f) ((d.eF t : d.c₂.F) • g) := by
  intro k _ _ _ _ hk y₂ y hy
  unfold evR
  rw [evalAt_smul, evalAt_smul, hk t]
  exact congrArg _ (h k hk y₂ y hy)

theorem pull_sum {d : DeltaDat Xo c 0} {m : ℕ} (t : Fin m → c.F) (f : Fin m → Rul Xo c)
    (g : Fin m → Rul d.Xo₂ d.c₂) (h : ∀ i, Pull d (f i) (g i)) :
    Pull d (∑ i, t i • f i) (∑ i, (d.eF (t i) : d.c₂.F) • g i) := by
  classical
  suffices H : ∀ s : Finset (Fin m), Pull d (∑ i ∈ s, t i • f i) (∑ i ∈ s, (d.eF (t i) : d.c₂.F) • g i) from H _
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using pull_zero d
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact pull_add (pull_smul _ (h i)) ih

theorem fibConst_zero (d : DeltaDat Xo c 0) : FibConst d 0 := (pull_zero d).fibConst

theorem fibConst_add {d : DeltaDat Xo c 0} {g g' : Rul d.Xo₂ d.c₂} (h : FibConst d g) (h' : FibConst d g') :
    FibConst d (g + g') := by
  intro k _ _ _ _ hk y₂ y₂' y h₁ h₂
  unfold evR
  rw [evalAt_add, evalAt_add]
  exact congrArg₂ (· + ·) (h k hk y₂ y₂' y h₁ h₂) (h' k hk y₂ y₂' y h₁ h₂)

theorem fibConst_smul {d : DeltaDat Xo c 0} {g : Rul d.Xo₂ d.c₂} (t : d.c₂.F) (h : FibConst d g) :
    FibConst d (t • g) := by
  intro k _ _ _ _ hk y₂ y₂' y h₁ h₂
  unfold evR
  rw [evalAt_smul, evalAt_smul]
  exact congrArg _ (h k hk y₂ y₂' y h₁ h₂)

theorem rulBC_zero {c' : Coeff l} (hle : c.F ≤ c'.F) : rulBC hle (0 : Rul Xo c) = 0 := by
  funext p y
  letI := resAlg hle p.R
  exact evalAt_zero _ _ _

end GlobalTheory.LevRingDesc

namespace GlobalTheory.LevRingDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}

set_option maxHeartbeats 1000000 in

theorem exists_pullMap {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hU : ∀ f ∈ sec Xo c' a n, ∃! g, g ∈ sec d.Xo₂ d.c₂ a n ∧ Pull d f g)
    (hc : ∀ f : cuspW Xo c U (wtZ a n), ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d (rulBC hle (f : Rul Xo c)) g →
      g ∈ cuspW d.Xo₂ d.c₂ U₂ (wtZ a n)) :
    ∃ π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n),
      ∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂) := by
  have hlin := GlobalTheory.FieldBC.rulBC_sec_val_linear _ H Dw l Xo c c' hle
  have hsec' : ∀ f : cuspW Xo c U (wtZ a n), rulBC hle (f : Rul Xo c) ∈ sec Xo c' a n := fun f =>
    (hlin.1 a n _ (cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U) a n).le f.2))).1
  choose P hPs hPp using fun f : cuspW Xo c U (wtZ a n) => (hU _ (hsec' f)).exists
  have hadd : ∀ f f' : cuspW Xo c U (wtZ a n), rulBC hle ((f + f' : cuspW Xo c U (wtZ a n)) : Rul Xo c) =
      rulBC hle (f : Rul Xo c) + rulBC hle (f' : Rul Xo c) := fun f f' => by
    simpa using hlin.2 1 f f'
  have hsmul : ∀ (t : c.F) (f : cuspW Xo c U (wtZ a n)), rulBC hle ((t • f : cuspW Xo c U (wtZ a n)) : Rul Xo c) =
      incF c c' hle t • rulBC hle (f : Rul Xo c) := fun t f => by
    simpa [rulBC_zero] using hlin.2 t f 0
  have hPadd : ∀ f f', P (f + f') = P f + P f' := fun f f' =>
    (hU _ (hsec' (f + f'))).unique ⟨hPs _, hPp _⟩
      ⟨add_mem (hPs f) (hPs f'), by rw [hadd]; exact pull_add (hPp f) (hPp f')⟩
  have hPsmul : ∀ (t : c.F) f, P (t • f) = (d.eF (incF c c' hle t) : d.c₂.F) • P f := fun t f =>
    (hU _ (hsec' (t • f))).unique ⟨hPs _, hPp _⟩
      ⟨Submodule.smul_mem _ _ (hPs f), by rw [hsmul]; exact pull_smul _ (hPp f)⟩
  exact ⟨{ toFun := fun f => ⟨P f, hc f _ (hPs f) (hPp f)⟩
           map_add' := fun f f' => Subtype.ext (hPadd f f')
           map_smul' := fun t f => Subtype.ext (hPsmul t f) }, fun f => hPp f⟩

end GlobalTheory.LevRingDesc

namespace GlobalTheory.LevRingDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}

set_option maxHeartbeats 1000000 in

theorem span_integral_descent {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hgal : letI : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra;
      IsGalois c.F d.c₂.F)
    (π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n))
    (hπ : ∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂))
    (hlat : ∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n))
    (hint : ∀ F ∈ sec Xo c' a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d F g → (IntAt d.Xo₂ d.c₂ g ↔ IntAt Xo c' F))
    (C : Submodule c.F (cuspW Xo c U (wtZ a n))) (δ : 𝓞 d.c₂.F) (hδ : δ ∈ differentIdeal ℤ (𝓞 d.c₂.F))
    (g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n)) (hgL : g ∈ latW U₂ (wtZ a n))
    (hgC : g ∈ Submodule.span d.c₂.F (π '' (C : Set (cuspW Xo c U (wtZ a n))))) :
    δ • g ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := by
  have hlin := GlobalTheory.FieldBC.rulBC_sec_val_linear _ H Dw l Xo c c' hle
  have hsecC : ∀ f : cuspW Xo c U (wtZ a n), (f : Rul Xo c) ∈ sec Xo c a n := fun f =>
    cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U) a n).le f.2)
  have hsec₂ : ∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (g : Rul d.Xo₂ d.c₂) ∈ sec d.Xo₂ d.c₂ a n := fun g =>
    cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U₂) a n).le g.2)
  obtain ⟨m, μ, x, hx⟩ := Submodule.mem_span_set'.1 hgC
  choose b hbC hb using fun i => (x i).2
  have hrul : ∀ v : Fin m → c'.F, (∑ i, v i • rulBC hle (b i : Rul Xo c)) ∈ sec Xo c' a n := fun v =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hlin.1 a n _ (hsecC (b i))).1
  let Φ : (Fin m → d.c₂.F) →ₗ[𝓞 d.c₂.F] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n) :=
    { toFun := fun v => ∑ i, v i • π (b i)
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun t v => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_assoc t (v i) (π (b i)) }
  have hΦ : ∀ v, Φ v = ∑ i, v i • π (b i) := fun v => rfl
  have hpullS : ∀ v : Fin m → d.c₂.F,
      Pull d (∑ i, d.eF.symm (v i) • rulBC hle (b i : Rul Xo c)) (Φ v : Rul d.Xo₂ d.c₂) := by
    intro v
    have := pull_sum (fun i => d.eF.symm (v i)) (fun i => rulBC hle (b i : Rul Xo c))
      (fun i => (π (b i) : Rul d.Xo₂ d.c₂)) (fun i => hπ (b i))
    rw [hΦ, Submodule.coe_sum]
    simpa only [Submodule.coe_smul, AlgEquiv.apply_symm_apply] using this
  let M : Submodule (𝓞 d.c₂.F) (Fin m → d.c₂.F) := (latW U₂ (wtZ a n)).comap Φ
  have hmemM : ∀ v, v ∈ M ↔ IntAt Xo c' (∑ i, d.eF.symm (v i) • rulBC hle (b i : Rul Xo c)) := fun v =>
    hint _ (hrul _) _ (hsec₂ _) (hpullS v)
  letI alg : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra
  haveI : IsGalois c.F d.c₂.F := hgal
  have hstab : ∀ s : d.c₂.F ≃ₐ[c.F] d.c₂.F, ∀ v ∈ M, (fun i => s (v i)) ∈ M := by
    intro s v hv
    rw [hmemM] at hv ⊢
    let s' : c'.F ≃+* c'.F := (d.eF.toRingEquiv.trans s.toRingEquiv).trans d.eF.symm.toRingEquiv
    have hs' : ∀ y : c.F, s' (incF c c' hle y) = incF c c' hle y := by
      intro y
      have h0 : s (d.eF (incF c c' hle y)) = d.eF (incF c c' hle y) := s.commutes y
      show d.eF.symm (s (d.eF (incF c c' hle y))) = incF c c' hle y
      rw [h0, AlgEquiv.symm_apply_apply]
    have e : ∀ i, s' (d.eF.symm (v i)) = d.eF.symm (s (v i)) := fun i => by
      show d.eF.symm (s (d.eF (d.eF.symm (v i)))) = _
      rw [AlgEquiv.apply_symm_apply]
    have := GlobalTheory.GalSup.intAt_galois _ H Dw l Xo c c' hle a n s' hs' m (fun i => d.eF.symm (v i))
      (fun i => (b i : Rul Xo c)) (fun i => hsecC (b i)) hv
    simpa only [e] using this
  have hT := (GlobalTheory.T.galois_stable_lattice_rational_span_inclusions c.F d.c₂.F d.c₂.F m M hstab).2
  have hΦμ : Φ μ = g := by
    rw [hΦ, ← hx]
    exact Finset.sum_congr rfl fun i _ => by rw [hb i]
  have hμM : μ ∈ M := by
    show Φ μ ∈ latW U₂ (wtZ a n)
    rw [hΦμ]
    exact hgL
  have hπs : ∀ y : Fin m → c.F, π (∑ i, y i • b i) = Φ (fun i => algebraMap c.F d.c₂.F (y i)) := by
    intro y
    rw [map_sum, hΦ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    rfl
  have h2 := hT (Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hδ) (Submodule.subset_span ⟨μ, hμM, rfl⟩))
  have h3 : Submodule.span (𝓞 d.c₂.F) ((fun (y : Fin m → c.F) i => algebraMap d.c₂.F d.c₂.F (algebraMap c.F d.c₂.F (y i))) ''
      {y | (fun i => algebraMap c.F d.c₂.F (y i)) ∈ M}) ≤
      (Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)})).comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    refine Submodule.subset_span ⟨∑ i, y i • b i, ⟨C.sum_mem fun i _ => C.smul_mem _ (hbC i), ?_⟩, hπs y⟩
    rw [← hlat, hπs]
    exact hy
  have h4 := h3 h2
  rw [Submodule.mem_comap, map_smul] at h4
  have h5 : δ • Φ μ ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := h4
  rwa [hΦμ] at h5

end GlobalTheory.LevRingDesc

namespace GlobalTheory.LevRingDesc

set_option maxHeartbeats 2000000 in

theorem levRing_descent : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → (letI : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra; IsGalois c.F d.c₂.F) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∃ π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂)) ∧ (∀ (m : ℕ) (b : Fin m → cuspW Xo c U (wtZ a n)), LinearIndependent c.F b → LinearIndependent d.c₂.F (fun k => π (b k))) ∧ (∀ (σ₂ : d.c₂.F →+* ℂ) (f : cuspW Xo c U (wtZ a n)), normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ (π f) = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))) f) ∧ (∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n)) ∧ (∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (Set.range π) ↔ FibConst d (g : Rul d.Xo₂ d.c₂)) ∧ ∀ (C : Submodule c.F (cuspW Xo c U (wtZ a n))), ∀ δ ∈ differentIdeal ℤ (𝓞 d.c₂.F), ∀ g ∈ latW U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (π '' (C : Set (cuspW Xo c U (wtZ a n)))) → δ • g ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := by
  intro D j H Dw l Xo c c' hle U dict d U₂ dict₂ hL hL₂ hlev hgal a n hdom hev
  have hpq : Dw.q < Dw.p := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.sigW] at hp hq
    omega
  have h1 : 1 ≤ Dw.p + Dw.q := by omega
  have hB : (Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d := Or.inl ⟨by omega, hL.levA⟩
  obtain ⟨hL', hN'⟩ := GlobalTheory.LawsFieldChange.laws_fieldChange D j H Dw l Xo c c' hle U dict hL
  obtain ⟨hU, hinj⟩ := GlobalTheory.CoverSec.section_pullback_existsUnique _ H Dw l Xo c' d h1 hlev hB a n
  have hlin := GlobalTheory.FieldBC.rulBC_sec_val_linear _ H Dw l Xo c c' hle
  have hsecC : ∀ f : cuspW Xo c U (wtZ a n), (f : Rul Xo c) ∈ sec Xo c a n := fun f =>
    cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U) a n).le f.2)
  have hsec' : ∀ f : cuspW Xo c U (wtZ a n), rulBC hle (f : Rul Xo c) ∈ sec Xo c' a n := fun f =>
    (hlin.1 a n _ (hsecC f)).1
  have hsec₂ : ∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (g : Rul d.Xo₂ d.c₂) ∈ sec d.Xo₂ d.c₂ a n := fun g =>
    cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U₂) a n).le g.2)
  have hcusp := GlobalTheory.T.cuspForm_iff_levelCover_pullback D j H Dw l Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) d U₂ dict₂ hL'
    hL₂ hlev a n hdom hev
  have hint := GlobalTheory.CoverInt.pull_intAt_iff _ H Dw l Xo c' d h1 hlev hB a n
  obtain ⟨π, hπ⟩ := exists_pullMap hle U d U₂ a n hU fun f g hg hp => by
    rw [cuspW_wtZ]
    obtain ⟨h, -⟩ := hN' a n hdom f
    have hc : rulBC hle (f : Rul Xo c) ∈ cusp Xo c' (unfBC hle U) a n := by rwa [← cuspW_wtZ]
    exact (hcusp _ (hsec' f) _ hg hp).2 hc
  have hlat : ∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n) := fun f =>
    (hint _ (hsec' f) _ (hsec₂ _) (hπ f)).trans (GlobalTheory.IntCoefExt.intAt_rulBC_iff _ H Dw l Xo c c' hle a n _ (hsecC f))
  refine ⟨π, hπ, ?_, ?_, hlat, ?_, fun C δ hδ g hgL hgC =>
    span_integral_descent hle U d U₂ a n hgal π hπ hlat hint C δ hδ g hgL hgC⟩
  · intro m b hb
    have hv : LinearIndependent c.F (fun k => (b k : Rul Xo c)) :=
      hb.map' (cuspW Xo c U (wtZ a n)).subtype (Submodule.ker_subtype _)
    have hv' := GlobalTheory.CuspFieldChange.linearIndependent_rulBC hle (fun k => hsecC (b k)) hv
    rw [Fintype.linearIndependent_iff] at hv' ⊢
    intro t ht i
    have hp := pull_sum (fun k => d.eF.symm (t k)) (fun k => rulBC hle (b k : Rul Xo c))
      (fun k => (π (b k) : Rul d.Xo₂ d.c₂)) (fun k => hπ (b k))
    have h0 : (∑ k, (d.eF (d.eF.symm (t k)) : d.c₂.F) • (π (b k) : Rul d.Xo₂ d.c₂)) = 0 := by
      simp only [AlgEquiv.apply_symm_apply]
      have := congrArg Subtype.val ht
      simpa only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero] using this
    rw [h0] at hp
    have := hv' _ (hinj _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hsec' (b k))) hp) i
    simpa using this
  · intro σ₂ f
    obtain ⟨h, hn⟩ := hN' a n hdom f
    rw [GlobalTheory.T.peterssonNorm_eq_of_levelCover_pullback D j H Dw l Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) d U₂ dict₂ hL' hL₂ hlev
      a n hdom hev ⟨_, h⟩ (π f) (hπ f) σ₂, hn]
    rfl
  · intro g
    constructor
    · intro hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, rfl⟩ := hx
        exact (hπ f).fibConst
      | zero => exact fibConst_zero d
      | add x y _ _ hx hy => exact fibConst_add hx hy
      | smul t x _ hx => exact fibConst_smul t hx
    · intro hF
      obtain ⟨f', hf', hp⟩ := GlobalTheory.T.section_constant_on_fibres_descends _ H Dw l Xo c' d h1 hlev a n _ (hsec₂ g) hF
      have hc' : f' ∈ cusp Xo c' (unfBC hle U) a n := (hcusp _ hf' _ (hsec₂ g) hp).1 (by rw [← cuspW_wtZ]; exact g.2)
      rw [GlobalTheory.CuspFieldChange.cusp_unfBC_eq_span hle U a n] at hc'
      have key : ∀ x ∈ Submodule.span c'.F (rulBC hle '' (cusp Xo c U a n : Set (Rul Xo c))),
          ∃ g' ∈ Submodule.span d.c₂.F (Set.range π), Pull d x (g' : Rul d.Xo₂ d.c₂) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨f0, hf0, rfl⟩ := hx
          have hf0' : f0 ∈ cuspW Xo c U (wtZ a n) := by rw [cuspW_wtZ]; exact hf0
          exact ⟨π ⟨f0, hf0'⟩, Submodule.subset_span ⟨_, rfl⟩, hπ ⟨f0, hf0'⟩⟩
        | zero => exact ⟨0, zero_mem _, pull_zero d⟩
        | add x y _ _ hx hy =>
          obtain ⟨g1, hg1, p1⟩ := hx
          obtain ⟨g2, hg2, p2⟩ := hy
          exact ⟨g1 + g2, add_mem hg1 hg2, pull_add p1 p2⟩
        | smul t x _ hx =>
          obtain ⟨g1, hg1, p1⟩ := hx
          exact ⟨d.eF t • g1, Submodule.smul_mem _ _ hg1, pull_smul t p1⟩
      obtain ⟨g', hg', hp'⟩ := key f' hc'
      have e : g = g' := Subtype.ext ((hU f' hf').unique ⟨hsec₂ g, hp⟩ ⟨hsec₂ g', hp'⟩)
      rw [e]
      exact hg'

end GlobalTheory.LevRingDesc
