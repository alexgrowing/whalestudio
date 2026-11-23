import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfEqv

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_αβ_core (Bs : FramepfBas W T) (hT : IsCrys PD T.ρ) (π' Eπ : LetA O n) (h' M : ℕ)
    (c : ZMod n) (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hEΔ : Eπ ∈ W.AΔ)
    (eb : Fin Bs.r → LcQ W T π' c) (P R S : Fin Bs.r → Fin Bs.r → LetA O n) (hS : ∀ m k, S m k ∈ W.AΔ)
    (lam : O) (hRP : ∀ m k, ∑ j, R m j * P j k =
      (if m = k then algebraMap O (LetA O n) lam * letE c else 0) + π' ^ M * Eπ ^ (4 * h') * S m k)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c)
    (hΨ : ∀ e j, Ψ (e ⊗ₜ eb j) = e • ∑ m, R m j • W.φD T (Bs.b m))
    (hΦ : ∀ a : Fin Bs.r → LetA O n, Φ (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * P j k) ⊗ₜ eb j)
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) : Ψ (Φ y) - lam • y ∈ JP W T π' Eπ h' M c := by
  obtain ⟨h1, hΔ, hl⟩ := (mem_LamPS W T Eπ h' c y).1 hy
  obtain ⟨a, haΔ, hac, ha⟩ := framepf_phi_coordΔ Bs hT c (framepf_φspan_le (c - 1) h1)
    (fun δ hδ => by rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ, hΔ δ hδ])
    (by rw [smul_comm, hl])
  refine ⟨∑ m, (∑ k, a k * S m k) • W.φD T (Bs.b m), framepf_mem_Pc Bs c _
    (fun m => Subalgebra.sum_mem _ fun k _ => W.AΔ.mul_mem (haΔ k) (hS m k)) (fun m => ?_), ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hac]
  show (π' ^ M * Eπ ^ (3 * h')) • (∑ m, (∑ k, a k * S m k) • W.φD T (Bs.b m)) = _
  rw [← sub_eq_zero]
  apply gradNPf_tf W T (Eπ ^ h') (by rw [map_pow]; exact huE.pow _)
  have h2 : Eπ ^ h' • Ψ (Φ y) = ∑ m, (∑ j, (∑ k, a k * P j k) * R m j) • W.φD T (Bs.b m) := by
    rw [← algebraMap_smul W.EE, ← map_smul, ← map_smul, algebraMap_smul, ha, hΦ, map_sum]
    simp only [hΨ, algebraMap_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_smul.symm
  have h3 : ∀ m, ∑ j, (∑ k, a k * P j k) * R m j =
      algebraMap O (LetA O n) lam * a m + π' ^ M * Eπ ^ (4 * h') * ∑ k, a k * S m k := by
    intro m
    have : ∑ j, (∑ k, a k * P j k) * R m j = ∑ k, a k * ∑ j, R m j * P j k := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    simp only [hRP, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · rw [mul_left_comm, mul_comm (a m), hac]
    · exact Finset.sum_congr rfl fun k _ => by ring
  have h4 : Eπ ^ h' • (lam • y) = ∑ m, (algebraMap O (LetA O n) lam * a m) • W.φD T (Bs.b m) := by
    rw [smul_comm, ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [mul_smul, algebraMap_smul]
  rw [smul_sub, smul_sub, h2, h4, smul_smul, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [h3, smul_smul, ← sub_smul, ← sub_smul]
  convert zero_smul (LetA O n) (W.φD T (Bs.b m)) using 2
  ring

end Local

end Formalism.MainNotions.N.Ln34

end
