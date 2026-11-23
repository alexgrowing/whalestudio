import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAlpha
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPhi

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

theorem framepf_smulLA_eq (π' : LetA O n) (c : ZMod n) (a : LetA O n) (z : W.EE ⊗[O] LcQ W T π' c) :
    smulLA W T π' c a z = algebraMap (LetA O n) W.EE a • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e ℓ => rw [framepf_smulLA_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

variable (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

include hπ0 hΔπ γ0 in
theorem framepf_φA_ι_mem (g : PowerSeries O) : W.φA (framepf_ι π' (c - 1) g) ∈ W.AΔ := by
  intro δ hδ
  rw [← LocWach.φA_γA, framepf_ι_Δ π' hπ0 hΔπ γ0 _ g δ hδ]

theorem framepf_φD_vec (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    W.φD T (framepf_vec Bs π' (c - 1) H k) =
      ∑ m, W.φA (framepf_ι π' (c - 1) (H m k)) • W.φD T (Bs.b m) := by
  unfold framepf_vec
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => framepf_φD_smul _ _

def framepf_ebar (j : Fin Bs.r) : LcQ W T π' c :=
  (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu).symm (Pi.single j 1)

theorem framepf_hh_ebar (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (j : Fin Bs.r) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H (framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j) =
      framepf_vec Bs π' (c - 1) H j := by
  unfold framepf_hh framepf_ebar
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    Fintype.linearCombination_apply_single, one_smul]

theorem framepf_sum_ebar (ℓ : LcQ W T π' c) :
    ∑ k, framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu ℓ k • framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu k = ℓ := by
  unfold framepf_ebar
  simp_rw [← LinearEquiv.map_smul, ← map_sum]
  rw [LinearEquiv.symm_apply_eq]
  conv_rhs => rw [← Finset.univ_sum_single (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu ℓ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext m
  by_cases h : m = k
  · subst h; simp
  · simp [h]

def framepf_Ψβ (βφ : Module.Basis (Fin Bs.r) W.EE (W.DD T)) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) :
    W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c :=
  βφ.constr W.EE fun k => ∑ j, algebraMap (LetA O n) W.EE (W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
    framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j

variable (βφ : Module.Basis (Fin Bs.r) W.EE (W.DD T)) (hβφ : ∀ k, βφ k = W.φD T (Bs.b k))

include hβφ in
theorem framepf_Ψβ_sum (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (a : Fin Bs.r → LetA O n) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
        framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := by
  have e1 : ∀ k, framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F (a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (a k * W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
        framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := by
    intro k
    rw [← algebraMap_smul W.EE (a k), LinearMap.map_smul, ← hβφ k]
    unfold framepf_Ψβ
    rw [Module.Basis.constr_basis, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]
  rw [map_sum, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← TensorProduct.sum_tmul, ← map_sum]

include hπ0 hΔπ γ0 hβφ in

theorem framepf_Ψβ_Pc (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (p : W.DD T) (hp : p ∈ PcS W T c) :
    ∃ t, framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F p = toLA W T π' c ⊤ t := by
  obtain ⟨a, haΔ, hac, hap⟩ := framepf_Pc_coord Bs hT c p hp
  have hmem : ∀ j, ∑ k, a k * W.φA (framepf_ι π' (c - 1) (F j k)) ∈ W.AΔ := fun j =>
    Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (haΔ k) (framepf_φA_ι_mem π' c hπ0 hΔπ γ0 _)
  refine ⟨∑ j, (⟨_, hmem j⟩ : ↥W.AΔ) ⊗ₜ (⟨framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j, trivial⟩ :
    ↥(⊤ : Submodule O (LcQ W T π' c))), ?_⟩
  rw [hap, framepf_Ψβ_sum Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [framepf_toLA_tmul]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, hac k]

variable (Eπ : LetA O n) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hEΔ : ∀ δ ∈ W.DelF, W.γA δ Eπ = Eπ) (h' M : ℕ)

include hπ0 hΔπ γ0 hβφ hEΔ in

theorem framepf_Ψβ_Lam (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F y ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [mem_LamPS] at hy
  obtain ⟨h1, hΔ, hl⟩ := hy
  have hP : Eπ ^ h' • y ∈ PcS W T c := by
    unfold PcS
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(Submodule.restrictScalars_mem _ _ _).2 h1, ?_⟩, ?_⟩
    · rw [mem_DelS]
      intro δ hδ
      rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ, hΔ δ hδ]
    · rw [mem_letS, smul_smul, mul_comm, ← smul_smul, hl]
  obtain ⟨t, ht⟩ := framepf_Ψβ_Pc Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ hT F _ hP
  refine Submodule.mem_comap.2 ⟨t, ?_⟩
  rw [← ht, framepf_smulLA_eq, ← LinearMap.map_smul, algebraMap_smul]

include hπ0 hΔπ γ0 hβφ in

theorem framepf_Ψβ_J (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (y : W.DD T) (hy : y ∈ JP W T π' Eπ h' M c) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F y ∈ JLA W T π' Eπ h' M c := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨t, ht⟩ := framepf_Ψβ_Pc Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ hT F p hp
  refine Submodule.mem_map.2 ⟨_, ⟨t, rfl⟩, ?_⟩
  rw [framepf_smulLA_eq, ← ht, ← LinearMap.map_smul, algebraMap_smul]
  rfl

include hπ0 in
theorem framepf_ι_X_pow_mul (k : ℕ) (g : PowerSeries O) :
    framepf_ι π' (c - 1) (PowerSeries.X ^ k * g) = π' ^ k * framepf_ι π' (c - 1) g := by
  induction k with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ', mul_assoc, framepf_ι_mul π' (c - 1) (hπ0 _), ih, framepf_ι_X π' (c - 1) (hπ0 _),
      pow_succ']
    have := framepf_letE_ι π' (c - 1) hπ0 g
    calc letE (c - 1) * π' * (π' ^ k * framepf_ι π' (c - 1) g)
        = π' * π' ^ k * (letE (c - 1) * framepf_ι π' (c - 1) g) := by ring
      _ = π' * π' ^ k * framepf_ι π' (c - 1) g := by rw [this]

include hπ0 in

theorem framepf_φA_ι_entry (M : ℕ) (lam : O) (K : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (j k : Fin Bs.r) :
    W.φA (framepf_ι π' (c - 1) ((PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K) j k)) =
      (if j = k then algebraMap O (LetA O n) lam * letE c else 0) +
        W.φA π' ^ M * W.φA (framepf_ι π' (c - 1) (K j k)) := by
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    framepf_ι_add π' (c - 1) (hπ0 _), map_add, framepf_ι_X_pow_mul π' c hπ0, map_mul, map_pow]
  congr 1
  by_cases h : j = k
  · subst h
    rw [Matrix.one_apply_eq, mul_one, framepf_ι_C π' (c - 1) (hπ0 _), map_mul,
      Formalism.MainNotions.LiftingTheory.wmap_φA_letE, AlgHom.commutes, if_pos rfl, mul_comm]
  · rw [Matrix.one_apply_ne h, mul_zero, framepf_ι_zero π' (c - 1) hπ0, map_zero, if_neg h]

include hπ0 in
theorem framepf_φA_ι_matmul (F H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (j k : Fin Bs.r) :
    ∑ m, W.φA (framepf_ι π' (c - 1) (F j m)) * W.φA (framepf_ι π' (c - 1) (H m k)) =
      W.φA (framepf_ι π' (c - 1) ((F * H) j k)) := by
  rw [Matrix.mul_apply, framepf_ι_sum π' (c - 1) hπ0, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [framepf_ι_mul π' (c - 1) (hπ0 _), map_mul]

end Local

end Formalism.MainNotions.N.Ln34

end
