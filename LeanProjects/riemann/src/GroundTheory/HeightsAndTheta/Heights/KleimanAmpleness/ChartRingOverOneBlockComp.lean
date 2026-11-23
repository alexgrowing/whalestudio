import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneMemSecOverZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

section Points

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem exists_locIn_of_eq {A B : Subalgebra F Ω} (hAB : A = B) (p : Ideal A) (hp : p.IsPrime) :
    ∃ q : Ideal B, q.IsPrime ∧ IndefiniteRowSideFullHecke.Kleiman2.locIn A p = IndefiniteRowSideFullHecke.Kleiman2.locIn B q := by
  subst hAB
  exact ⟨p, hp, rfl⟩

theorem chartRingOver_oneBlock_comp {κ κ' : Type} (σ : κ' ≃ κ) (v : κ → Ω) (c : Unit → κ') :
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) c =
      chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) (fun u => σ (c u)) := by
  rw [SectionsOverLocalization.chartRingOver_oneBlock_eq, SectionsOverLocalization.chartRingOver_oneBlock_eq]
  congr 1
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩

variable (F) in

theorem modelPts_oneBlock_comp {κ κ' : Type} (σ : κ' ≃ κ) (v : κ → Ω) :
    IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) =
      IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) := by
  ext z
  constructor
  · rintro ⟨c, hc, p, hp, rfl⟩
    obtain ⟨q, hq, he⟩ := exists_locIn_of_eq (chartRingOver_oneBlock_comp σ v c) p hp
    exact ⟨fun u => σ (c u), fun u => hc u, q, hq, he⟩
  · rintro ⟨c, hc, p, hp, rfl⟩
    have hc' : ∀ u, IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ) ⟨u, σ.symm (c u)⟩ ≠ 0 := fun u => by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.oneBlock] using hc u
    have hch : chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) c =
        chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) (fun u => σ.symm (c u)) := by
      rw [chartRingOver_oneBlock_comp σ v]
      simp
    obtain ⟨q, hq, he⟩ := exists_locIn_of_eq hch p hp
    exact ⟨fun u => σ.symm (c u), hc', q, hq, he⟩

variable (F) in

theorem modelPts_eq_of_base {N : ℕ} {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (k₀ : K)
    (e : ι k₀ ≃ Fin (N + 1)) {K' : Type} {ι' : K' → Type} (y' : (Σ k, ι' k) → Ω) (k₀' : K')
    (e' : ι' k₀' ≃ Fin (N + 1)) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀)
    (hy' : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀')
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm) :
    IndefiniteRowSideFullHecke.Kleiman2.modelPts F y = IndefiniteRowSideFullHecke.Kleiman2.modelPts F y' := by
  rw [hy.2, hy'.2, ← modelPts_oneBlock_comp F e.symm, hx, modelPts_oneBlock_comp F e'.symm]

end Points

theorem veryAmple_change (hGen : ModelChangeGen.Statement) (F : Type) [Field F] (Ω : Type) [Field Ω]
    [Algebra F Ω] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1))
    (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (hy' : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀')
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm)
    (β : K → ℤ) (β' : K' → ℤ)
    (hs : ∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
      secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) :
    IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y' β' := by
  have h0 : secOver F y β = secOver F y' β' := by simpa using hs 0
  have hpts := modelPts_eq_of_base F y k₀ e y' k₀' e' hy hy' hx
  unfold IndefiniteRowSideFullHecke.Kleiman2.VeryAmple IndefiniteRowSideFullHecke.Kleiman2.SameModel
  rw [hpts]
  constructor
  · rintro ⟨n, x', hmem, hgen, hsame⟩
    refine ⟨n, x', fun j => h0 ▸ hmem j, ?_, hsame⟩
    exact (hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs n x' hmem).1 hgen
  · rintro ⟨n, x', hmem, hgen, hsame⟩
    have hmem' : ∀ j, x' j ∈ secOver F y β := fun j => h0 ▸ hmem j
    exact ⟨n, x', hmem', (hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs n x' hmem').2 hgen, hsame⟩

theorem VeryAmpleModel.proof (hVA : VeryAmpleEq.Statement) (hGen : ModelChangeGen.Statement) :
    VeryAmpleModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hxe hmod Q β hQ
  subst hxe
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (Q.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen Q n g := hg
  have hmod' := GraphModel.full F N Ω _ Q n (r + 1) g hx hgen
  have hsec := realises_graph Q n g hgen
  rw [hVA F N Ω _ Q n (r + 1) g hgen]
  exact (veryAmple_change hGen F Ω N K ι y k₀ e (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock
    (Equiv.refl _) hmod hmod' rfl β (graphDeg n) (fun c => (hQ c).symm.trans (hsec c))).symm

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
