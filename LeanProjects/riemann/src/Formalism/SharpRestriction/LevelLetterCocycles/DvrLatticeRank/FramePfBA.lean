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

theorem framepf_βα_core (Bs : FramepfBas W T) (π' Eπ : LetA O n) (h' M : ℕ)
    (c : ZMod n) (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (eb : Module.Basis (Fin Bs.r) O (LcQ W T π' c)) (P R S : Fin Bs.r → Fin Bs.r → LetA O n)
    (hS : ∀ m k, S m k ∈ W.AΔ) (lam : O) (hPR : ∀ j k, ∑ m, P j m * R m k =
      (if j = k then algebraMap O (LetA O n) lam * letE c else 0) + π' ^ M * Eπ ^ (4 * h') * S j k)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c)
    (hΨ : ∀ e j, Ψ (e ⊗ₜ eb j) = e • ∑ m, R m j • W.φD T (Bs.b m))
    (hΦ : ∀ a : Fin Bs.r → LetA O n, Φ (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * P j k) ⊗ₜ eb j)
    (x : LA W T π' c) (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    Φ (Ψ x) - lam • x ∈ JLA W T π' Eπ h' M c := by
  choose a haΔ ha using (framepf_mem_toLA π' c eb _).1 hx
  have hee : (letE c : LetA O n) * letE c = letE c := Formalism.MainNotions.LiftingTheory.wmap_letE_idem c
  have hx' : algebraMap (LetA O n) W.EE (Eπ ^ h') • x =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a k) ⊗ₜ[O] eb k := by
    rw [← framepf_smulLA_alg, ← (Algebra.TensorProduct.basis W.EE eb).sum_repr (smulLA W T π' c _ x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hm : ∀ j, ∑ k, a k * S j k ∈ W.AΔ := fun j =>
    Subalgebra.sum_mem _ fun k _ => W.AΔ.mul_mem (haΔ k) (hS j k)
  refine ⟨∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * ∑ k, a k * S j k) ⊗ₜ[O] eb j,
    ⟨∑ j, (⟨_, hm j⟩ : ↥W.AΔ) ⊗ₜ ⟨eb j, trivial⟩, by rw [map_sum]; rfl⟩, ?_⟩
  obtain ⟨Λ, hΛ⟩ : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact huE.pow _
  have hcan : ∀ z z' : LA W T π' c, algebraMap (LetA O n) W.EE (Eπ ^ h') • z =
      algebraMap (LetA O n) W.EE (Eπ ^ h') • z' → z = z' := by
    intro z z' h
    have := congrArg (fun w => ((Λ⁻¹ : W.EEˣ) : W.EE) • w) h
    simpa only [← hΛ, smul_smul, Units.inv_mul, one_smul] using this
  apply hcan
  have h1 : Ψ (algebraMap (LetA O n) W.EE (Eπ ^ h') • x) =
      ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) • W.φD T (Bs.b m) := by
    rw [hx', map_sum]
    simp only [hΨ, algebraMap_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_smul.symm
  have h3 : ∀ j, ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) * P j m =
      algebraMap O (LetA O n) lam * ((letE c : LetA O n) * a j) +
        Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h') * ((letE c : LetA O n) * ∑ k, a k * S j k)) := by
    intro j
    have : ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) * P j m =
        ∑ k, (letE c : LetA O n) * a k * ∑ m, P j m * R m k := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    simp only [hPR, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · linear_combination (algebraMap O (LetA O n) lam * a j) * hee
    · exact Finset.sum_congr rfl fun k _ => by ring
  rw [smul_sub, ← map_smul Φ, ← map_smul Ψ, h1, hΦ, smul_comm _ lam x, hx', framepf_smulLA_alg,
    Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h3, ← algebraMap_smul W.EE lam, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  simp only [TensorProduct.smul_tmul', smul_eq_mul]
  rw [← TensorProduct.sub_tmul, ← map_mul, ← map_mul, ← map_mul, ← map_sub, add_sub_cancel_left]

end Local

end Formalism.MainNotions.N.Ln34

end
