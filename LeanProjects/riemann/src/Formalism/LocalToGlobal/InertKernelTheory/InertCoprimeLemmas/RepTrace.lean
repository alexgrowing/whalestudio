import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FrLocB
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx

noncomputable section

namespace Formalism.L2.KerInert.RepFrame

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem trace_tau_sum (D : D7) : TraceTau D := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.sum_tau_trace D

section Rank

variable (D : D7)

theorem exists_nat_integral {N N' : ℕ} (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, IsIntegral ℤ ((n : D.host.E) * B i j) := by
  classical
  choose k hk hkB using fun x : Fin N' × Fin N => Formalism.L2.KerInert.FrLocB.nat_mult (D := D) (B x.1 x.2)
  refine ⟨∏ x, k x, Finset.prod_pos fun x _ => hk x, fun i j => ?_⟩
  have h := Finset.mul_prod_erase Finset.univ k (Finset.mem_univ (i, j))
  have he : ((∏ x, k x : ℕ) : D.host.E) * B i j =
      ((∏ x ∈ Finset.univ.erase (i, j), k x : ℕ) : D.host.E) * ((k (i, j) : D.host.E) * B i j) := by
    rw [← h, Nat.cast_mul]; ring
  rw [he]
  have hi : IsIntegral ℤ ((∏ x ∈ Finset.univ.erase (i, j), k x : ℕ) : D.host.E) := by
    have := isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := ((∏ x ∈ Finset.univ.erase (i, j), k x : ℕ) : ℤ))
    simpa using this
  exact hi.mul (hkB (i, j))

variable {D}

theorem mem_span_of_locBasis {p : ℕ} [hp : Fact p.Prime] {N N' r : ℕ}
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hb : LocBasis D p Y b) {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ Y) :
    y ∈ Submodule.span D.host.K (Set.range b) := by
  obtain ⟨s, hs, c, hc⟩ := hb.2.2 y hy
  have hs0 : (s : D.host.K) ≠ 0 := by
    exact_mod_cast Formalism.L2.KerInert.FrLocB.ne_zero_of_coprime p hs
  have h1 : (s : D.host.K) • y ∈ Submodule.span D.host.K (Set.range b) := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, hc]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Formalism.L2.KerInert.IntegralOrthonormalChange.smul_eq_K D _ (c i : D.host.K).2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h2 := Submodule.smul_mem _ (s : D.host.K)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at h2

theorem span_top_of_locBasis {p : ℕ} [Fact p.Prime] {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : LocBasis D p (YYl D L L') b) :
    ⊤ ≤ Submodule.span D.host.K (Set.range b) := by
  obtain ⟨M, hM, hlow⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.YY_lower D L L' hL hL'
  intro B _
  obtain ⟨n, hn, hnB⟩ := exists_nat_integral D B
  have hA : ∀ i j, IsIntegral ℤ (((n : D.host.E) • B) i j) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hnB i j
  have h1 := mem_span_of_locBasis hb (hlow _ hA)
  rw [Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.K,
    ← Int.cast_smul_eq_zsmul D.host.K, smul_smul] at h1
  have hMn : ((M : D.host.K) * (n : D.host.K)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hM) (by exact_mod_cast hn.ne')
  have h2 := Submodule.smul_mem _ ((M : D.host.K) * (n : D.host.K))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hMn, one_smul] at h2

theorem rank_of_locBasis {p : ℕ} [Fact p.Prime] {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : LocBasis D p (YYl D L L') b) :
    r = Fintype.card (D.what₂.Tau × Fin N' × Fin N) := by
  have hbas := Module.Basis.mk hb.1 (span_top_of_locBasis L L' hL hL' hb)
  have h1 := Module.finrank_eq_card_basis hbas
  rw [Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin] at h1
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Formalism.L2.Ker.cardTau D]
  rw [Fintype.card_fin] at h1
  rw [← h1]; ring

end Rank

variable {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem rankTie_of (hadm : ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → Formalism.MainNotions.TaylorLogMetric.admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    RankTie X hfin D large₂ Lg' :=
  fun j L0 hL0 La' hLa' _ b hb =>
    rank_of_locBasis _ _ (hadm j L0 hL0 La' hLa').2.2.1 (hadm j L0 hL0 La' hLa').2.2.2 b hb

section Witness

variable (D : D7)

end Witness

end Formalism.L2.KerInert.RepFrame

set_option pp.fullNames true
