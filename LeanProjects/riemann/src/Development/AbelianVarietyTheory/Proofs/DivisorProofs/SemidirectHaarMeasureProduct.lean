import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv
namespace GlobalTheory.ModulusCoord

theorem map_haar_eq_smul_of_coords : ∀ (Q L A C : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [T2Space L] [MeasurableSpace L] [BorelSpace L]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C] [LocallyCompactSpace C]
    [SecondCountableTopology C] [T2Space C] [MeasurableSpace C] [BorelSpace C]
    (Φ : L × (A × C) ≃ₜ Q),
    (∀ q' : Q, ∃ (l' : L) (f : L → A) (g : L × A → C), Continuous f ∧ Continuous g ∧
      ∀ l a c, Φ (l, (a, c)) * q' = Φ (l * l', (a + f l, c + g (l, a)))) →
    ∀ (α : Q →* Q) (sA : A →+ A) (sC : C →+ C) (kA kC : ℝ≥0), Continuous α → Continuous sA → Continuous sC →
    (∀ l a c, α (Φ (l, (a, c))) = Φ (l, (sA a, sC c))) →
    (∀ ν : Measure A, ν.IsAddHaarMeasure → ν.map sA = kA • ν) →
    (∀ ν : Measure C, ν.IsAddHaarMeasure → ν.map sC = kC • ν) →
    ∀ μ : Measure Q, μ.IsHaarMeasure → μ.map α = (kA * kC) • μ := by
  intro Q L A C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Φ hT α sA sC kA kC hα hsA hsC hαΦ hA hC μ hμ
  set ρ : Measure L := (Measure.haar : Measure L).inv with hρ
  set νA : Measure A := Measure.addHaar with hνA
  set νC : Measure C := Measure.addHaar with hνC
  set P : Measure (L × (A × C)) := ρ.prod (νA.prod νC) with hP
  have hΦm : Measurable Φ := Φ.continuous.measurable
  set ν₀ : Measure Q := P.map Φ with hν₀
  have hright : ν₀.IsMulRightInvariant := by
    constructor
    intro q'
    obtain ⟨l', f, g, hf, hg, hfg⟩ := hT q'
    let T : L × (A × C) → L × (A × C) :=
      fun p => (p.1 * l', (p.2.1 + f p.1, p.2.2 + g (p.1, p.2.1)))
    have hTΦ : (· * q') ∘ Φ = Φ ∘ T := by funext p; exact hfg p.1 p.2.1 p.2.2
    have hTmp : MeasurePreserving T P P := by
      refine MeasurePreserving.skew_product (μa := ρ) (μb := ρ) (μc := νA.prod νC) (μd := νA.prod νC)
        (f := fun l : L => l * l')
        (g := fun l (x : A × C) => (x.1 + f l, x.2 + g (l, x.1))) ?_ ?_ ?_
      · exact measurePreserving_mul_right ρ l'
      · exact (by fun_prop : Continuous fun p : L × (A × C) =>
          (p.2.1 + f p.1, p.2.2 + g (p.1, p.2.1))).measurable
      · filter_upwards with l
        exact (MeasurePreserving.skew_product (μa := νA) (μc := νC) (g := fun (a : A) (c : C) => c + g (l, a))
          (measurePreserving_add_right νA (f l))
          (by exact (by fun_prop : Continuous fun p : A × C => p.2 + g (l, p.1)).measurable)
          (ae_of_all _ fun a => map_add_right_eq_self νC (g (l, a)))).map_eq
    rw [hν₀, Measure.map_map (measurable_mul_const q') hΦm, hTΦ,
      ← Measure.map_map hΦm hTmp.measurable, hTmp.map_eq]
  have hfin : IsFiniteMeasureOnCompacts ν₀ := Measure.IsFiniteMeasureOnCompacts.map P Φ
  have hpos : ν₀.IsOpenPosMeasure := Φ.continuous.isOpenPosMeasure_map Φ.surjective
  haveI : ν₀.inv.IsHaarMeasure := by constructor
  have hα_map : ν₀.map α = (kA * kC) • ν₀ := by
    have hcomp : α ∘ Φ = Φ ∘ Prod.map id (Prod.map sA sC) := by
      funext p; exact hαΦ p.1 p.2.1 p.2.2
    rw [hν₀, Measure.map_map hα.measurable hΦm, hcomp,
      ← Measure.map_map hΦm (measurable_id.prodMap (hsA.measurable.prodMap hsC.measurable)), hP,
      ← Measure.map_prod_map _ _ measurable_id (hsA.measurable.prodMap hsC.measurable),
      ← Measure.map_prod_map _ _ hsA.measurable hsC.measurable, hA νA inferInstance,
      hC νC inferInstance, Measure.map_id, Measure.prod_smul_right, Measure.prod_smul_left,
      smul_smul, Measure.prod_smul_right, Measure.map_smul, mul_comm]
  have hinv : (ν₀.inv).map α = (kA * kC) • ν₀.inv := by
    have hc : α ∘ (fun q => q⁻¹) = (fun q => q⁻¹) ∘ α := by funext q; simp [map_inv]
    rw [Measure.inv, Measure.map_map hα.measurable measurable_inv, hc,
      ← Measure.map_map measurable_inv hα.measurable, hα_map, Measure.map_smul]
  rw [Measure.isMulLeftInvariant_eq_smul μ ν₀.inv, Measure.map_smul, hinv, smul_smul, mul_comm,
    ← smul_smul]

end GlobalTheory.ModulusCoord
