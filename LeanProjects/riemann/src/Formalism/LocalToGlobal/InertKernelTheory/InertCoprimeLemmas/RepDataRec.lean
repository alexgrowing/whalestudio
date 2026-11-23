import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb

noncomputable section

namespace Formalism.L2.KerInert.RepRec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

theorem intOff_mono {S S' : Finset ℕ} (hSS : S ⊆ S') {r : ℂ} (h : IntOff S r) : IntOff S' r :=
  ⟨h.1, fun q _ lam hq => h.2 q lam (fun hm => hq (hSS hm))⟩

theorem intOff_natCast (S : Finset ℕ) (n : ℕ) : IntOff S (n : ℂ) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact IntOff.zero
  | succ m ih => rw [Nat.cast_succ]; exact IntOff.add ih IntOff.one

theorem dataRec_iff {p : ℕ} [hp : Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (D : D7) (cl : ℕ)
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) :
    DataRec X D cl Ξ ↔ ClAway p cl ∧ XiAway X D Ξ := by
  constructor
  · rintro ⟨S, ⟨hcl, hS⟩, hpS, hΞ⟩
    exact ⟨⟨hcl, fun hd => hpS (hS p hp.out hd)⟩, ⟨S, hpS, hΞ⟩⟩
  · rintro ⟨⟨hcl, hnd⟩, S₀, hp0, hΞ⟩
    refine ⟨S₀ ∪ cl.primeFactors,
      ⟨hcl, fun q hq hd => Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hq, hd, hcl.ne'⟩)⟩, ?_,
      fun j La La' y => intOff_mono Finset.subset_union_left (hΞ j La La' y)⟩
    rw [Finset.mem_union, not_or]
    exact ⟨hp0, fun h => hnd (Nat.dvd_of_mem_primeFactors h)⟩

theorem dataRec_movD {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (D : D7) (cl : ℕ)
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (G : ∀ j, X.Lt j → X.Lt (j + 1) → (Formalism.L2.Col.Sp D.host.E ((X.Pj j).m + 1) ≃ₗ[D.host.E] Formalism.L2.Col.Sp D.host.E ((X.Pj j).m + 1))) (G' : ∀ j, X.Lt j → X.Lt (j + 1) → (Formalism.L2.Col.Sp D.host.E ((X.Pj (j + 1)).m + 1) ≃ₗ[D.host.E] Formalism.L2.Col.Sp D.host.E ((X.Pj (j + 1)).m + 1))) (h : DataRec X D cl Ξ) :
    DataRec X D cl (fun j La La' => Formalism.L2.PairingIndexBounds.F.movD (Ξ j La La') (G j La La') (G' j La La')) := by
  obtain ⟨S, hS, hpS, hΞ⟩ := h
  exact ⟨S, hS, hpS, fun j La La' x => Formalism.L2.KerInert.RepComb.intOff_movD _ _ _ (hΞ j La La') x⟩

theorem combAt_of_dataRec {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) [IsFractionRing X.G.O X.G.Kf]
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hAlg : B.AlgT χ)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (hD : DataRec X D cl Ξ)
    (hA : ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
      TaylorLogMetric.admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    Rep.CombAt X hfin D large₂ Lg'
      (fun j La La' => Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')))
      B.tor (B.eNat χ) lam := by
  obtain ⟨S, hS, hpS, hΞ⟩ := hD
  exact Formalism.L2.KerInert.RepComb.combine_at_final_level X hfin D B χ SS cl lam S hcc hδ hAlg hS.1 hS hpS large₂ Lg' Ξ hΞ hA

end Formalism.L2.KerInert.RepRec
