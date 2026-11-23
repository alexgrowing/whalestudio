import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem intC_one_of_bump : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (s : kˣ)
    (hψ1 : ∀ y ∈ GlobalTheory.SplitWeil.cball s, ψ y = 1) (w : τ.V ⊗[ℂ] σ.V) (F : XS τ σ)
    (h1 : ∀ d : Fin (t + 1) → k, (∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → evX F (dEmb k i t d) = w)
    (h0 : ∀ d : Fin (t + 1) → k, (¬ ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → evX F (dEmb k i t d) = 0),
  ∃ c : ℂ, c ≠ 0 ∧ intC ψ F 1 = c • w := by
  intro k _ _ _ _ i t ψ τ σ s hψ1 w F h1 h0
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  let A : Set (Fin (t + 1) → k) := Set.pi Set.univ fun _ => GlobalTheory.SplitWeil.cball s
  have hAc : IsCompact A := isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s
  have hAo : IsOpen A := isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_cball s
  have hne : A.Nonempty := ⟨0, fun _ _ => by simp [GlobalTheory.SplitWeil.cball]⟩
  have hmem : ∀ d, d ∈ A ↔ ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s :=
    fun d => ⟨fun h j => h j (Set.mem_univ j), fun h j _ => h j⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by
    unfold muD
    infer_instance
  have hpos : 0 < muD k (t + 1) A := hAo.measure_pos _ hne
  have htop : muD k (t + 1) A < ⊤ := hAc.measure_lt_top
  refine ⟨(((muD k (t + 1) A).toReal : ℝ) : ℂ), ?_, ?_⟩
  · exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hpos.ne' htop.ne).ne'
  · have e : (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) •
        evX F (dEmb k i t d * (1 : Mir k ((i + 1) + t + 1)))) = A.indicator fun _ => w := by
      funext d
      have e1 : dEmb k i t d * (1 : Mir k ((i + 1) + t + 1)) = dEmb k i t d := mul_one _
      rw [e1]
      by_cases hd : d ∈ A
      · rw [Set.indicator_of_mem hd, h1 d ((hmem d).1 hd), hψ1 _ ((hmem d).1 hd _)]
        simp
      · rw [Set.indicator_of_notMem hd, h0 d (fun h => hd ((hmem d).2 h)), smul_zero]
    show @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) _ = _
    rw [e]
    exact GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator _ A w

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
