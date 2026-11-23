import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PRSPole

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem bnd (hJS : GlobalTheory.Published.JacquetShalikaBound) {m : ℕ} (π : CuspSub E m) (hπ : IsNormalised π)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (α : Off E S → Fin m → ℂˣ) (hα : SatOff (CG.mk π) S α) :
    ∀ w a, ‖(α w a : ℂ)‖ ≤ Real.sqrt (nq w) := by
  intro w a
  have hu : (CG.mk π).IsUnitary :=
    (CG.isUnitary_mk π).2 (GlobalTheory.Published.CuspFormsBoundedGL.isUnitary GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL hπ)
  have h := (hJS E m (CG.mk π) hu w.1 _ (hα w) (α w a)
    (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
  show ‖((α w a : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
  rw [Real.sqrt_eq_rpow]
  exact h.le

end PRSPole

open Classical in
theorem rspole_of : GlobalTheory.Published.JacquetShalikaBound → jumpWindows.G1 → jumpWindows.StandardCharacterExists → W0 → E2 → M1 → KIR → KSec → CornerEmbedding → KLt1 → KLt2 → LastRowCutoff → KEq1 → KEq2 → ORT → KY → RSPole := by
  intro hJS _hG1 hG10 hW0 hE2 hM1 hKIR hKSec hK5e hKLt1 hKLt2 hK11 hKEq1 hKEq2 hORT hKY E _ _ _ m k π π' u hk
    hkm hπ hπ'
  obtain ⟨ψ, hψ, hcond⟩ := hG10 E
  have hm : 1 ≤ m := hk.trans hkm
  obtain ⟨S₁, hS₁⟩ := hKSec E k hk ψ hψ hcond π' hπ'
  obtain ⟨S₂, hS₂⟩ := hKIR E m hm ψ hψ hcond π hπ
  refine ⟨S₁ ∪ S₂, fun S hS α β hα hβ => ?_⟩
  have hS1 : S₁ ⊆ S := Finset.union_subset_left hS
  have hS2 : S₂ ⊆ S := Finset.union_subset_right hS
  obtain ⟨hCond, hsec⟩ := hS₁ S hS1
  obtain ⟨φ₀', hφ₀', h', φ', hφ'e, hsec⟩ := hsec β hβ
  have hαb := PRSPole.bnd hJS π hπ S α hα
  have hβb := PRSPole.bnd hJS π' hπ' S β hβ
  let μ : Measure (GA E k) := Measure.haar
  obtain ⟨⟨b, hb⟩, -⟩ := hW0 E k μ hk
  rcases hkm.lt_or_eq with hlt | heq
  · obtain ⟨ι, hι⟩ := ((hK5e E m k hkm).1 (Ad E))
    obtain ⟨U, hU, hUd⟩ := hKLt1 E m k hk hlt ψ hψ S hCond ι hι α β u φ' hsec
    obtain ⟨φ, -, hprep⟩ := hS₂ S hS2 α hα (m ^ 3) k hlt U hU ⊤ isClosed_univ (fun _ _ _ => trivial)
      (fun _ _ => trivial)
    have hdat := hUd (m ^ 3) (Nat.one_le_pow _ _ hm) φ hprep
    have hgrow := hKLt2 E m k hk hlt ψ hψ S hCond ι hι α β φ' hsec U φ hprep
    obtain ⟨Z, hZd, hZe, hZ1⟩ := hE2 E k μ hk b hb _ _ hgrow
    obtain ⟨ZS, σ₀, hZSd, hZS0, hZSe⟩ := hM1 E k μ hk b hb ψ hψ S m α β u _ _ hkm hαb hβb hdat
    refine ⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun _ => hZ1 ?_⟩
    · rw [hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]
    · simp
  · subst heq
    obtain ⟨U, hU, hUd⟩ := hKEq1 E k hk ψ hψ S hCond α β u φ' hsec
    let φ'' : XB E k := if π = π' then 0 else φ'
    obtain ⟨Y, hYc, hYi, hYm, hYz⟩ := hKY E k μ hk b hb φ''
    have hforms : ∀ x : XB E k, (∃ φ ∈ π.V, (x : GA E k → ℂ) = φ.1) → x ∈ Y := by
      rintro x ⟨φ₁, hφ₁, hx⟩
      have hx' : ∀ g, x g = φ₁.1 g := congrFun hx
      refine (hYm x).2 ⟨fun t g => by rw [hx', hx']; exact hπ φ₁ hφ₁ t g, fun h => ?_⟩
      by_cases he : π = π'
      · have e0 : φ'' = 0 := if_pos he
        rw [e0]
        simp
      · have e1 : φ'' = φ' := if_neg he
        have hO := hORT E k μ hk b hb π π' hπ hπ' he φ₁ hφ₁ φ₀' hφ₀' h h'
        rw [e1]
        simp only [hx', hφ'e]
        exact hO
    obtain ⟨φ, hφY, hprep⟩ := hS₂ S hS2 α hα (k + 1) (k - 1) (by omega) U hU Y hYc hYi hforms
    obtain ⟨η, s, hcut⟩ := hK11 E k hk ψ hψ S hCond U hU φ hprep.smooth hprep.lev
    have hdat := hUd φ hprep η s hcut
    have hcen := ((hYm φ).1 hφY).1
    have hgrow := hKEq2 E k hk ψ hψ S β φ' hsec U φ η s hcut hprep.inv hcen
    obtain ⟨Z, hZd, hZe, hZ1⟩ := hE2 E k μ hk b hb _ _ hgrow
    obtain ⟨ZS, σ₀, hZSd, hZS0, hZSe⟩ := hM1 E k μ hk b hb ψ hψ S k α β u _ _ le_rfl hαb hβb hdat
    refine ⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun hne => hZ1 ?_⟩
    · rw [hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]
    · have hne' : π ≠ π' := fun e => hne (by rw [e])
      have e1 : φ'' = φ' := if_neg hne'
      have hz := hYz φ hφY ψ S U η s hcut
      rw [e1] at hz
      exact hz

end PositivityTheory.AdelicQuotientData

end
