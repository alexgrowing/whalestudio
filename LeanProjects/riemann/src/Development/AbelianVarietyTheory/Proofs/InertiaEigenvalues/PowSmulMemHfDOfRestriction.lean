import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCorestrictionCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSmulCocycleEqCoboundary
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory

open TensorProduct

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V)

theorem corHf_actVB_tmul (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := by
  simp [actVB]

noncomputable def corHfRepVB : Representation LL G (V ⊗[Qp] B) where
  toFun g := actVB PD ρ g
  map_one' := by
    ext v b
    simp [corHf_actVB_tmul]
  map_mul' g h := by
    ext v b
    simp [corHf_actVB_tmul]

def corHfRepO (O : Type) [CommRing O] [Algebra O LL] [Module O V] [IsScalarTower O LL V] :
    Representation O G V where
  toFun g := (ρ g).restrictScalars O
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul LL V]

theorem index_smul_mem_HfD [CharZero LL] (L : Lattice (O := O) ρ) (hρ : ∀ g, Continuous (ρ g))
    (hρ' : ∀ x, Continuous fun g => ρ g x) (H : Subgroup G) [H.Normal] [H.FiniteIndex]
    (hH : IsOpen (H : Set G)) (Z f₀ : G → V) (hZ : ContinuousOn Z H)
    (hc : ∀ g ∈ H, ∀ h ∈ H, Z (g * h) = Z g + ρ g (Z h))
    (hX : ∃ X : V ⊗[Qp] B, ∀ h ∈ H, Z h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h X - X)
    (h₀ : ∀ g h, f₀ (g * h) - (f₀ g + ρ g (f₀ h)) ∈ L.T) (hZf : ∀ h ∈ H, Z h - f₀ h ∈ L.T) :
    (fun g => H.index • (Submodule.Quotient.mk (f₀ g) : V ⧸ L.T)) ∈ HfD PD L := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨F, hF, hFc, ⟨x, hx⟩, hY⟩ := exists_corestriction_cocycle O G V (corHfRepO ρ O) H hH hρ hρ'
    Z hZ hc
  obtain ⟨x', hx'⟩ := hY L.T L.stable f₀ 0 h₀ (by simpa using hZf)
  obtain ⟨X, hX⟩ := hX
  have hmul : ∀ a b y, actVB PD ρ a (actVB PD ρ b y) = actVB PD ρ (a * b) y := by
    intro a b y
    exact (LinearMap.congr_fun ((corHfRepVB PD ρ).map_mul a b) y).symm
  have h1 : ∀ g (v : V), actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
    intro g v
    rw [corHf_actVB_tmul, map_one]
  obtain ⟨y, hy⟩ := index_smul_cocycle_eq_coboundary LL G (V ⊗[Qp] B) (corHfRepVB PD ρ) H
    (fun g => F g ⊗ₜ[Qp] (1 : B))
    (by
      intro g h
      change _ = _ + actVB PD ρ g _
      rw [h1, hFc, add_tmul]
      rfl)
    ⟨(∑ q : G ⧸ H, actVB PD ρ q.out X) + x ⊗ₜ[Qp] (1 : B), by
      intro h hh
      change _ = actVB PD ρ h _ - _
      rw [hx h hh, finsum_eq_sum_of_fintype, add_tmul, sum_tmul, map_add, map_sum, h1, sub_tmul]
      have : ∀ q : G ⧸ H, (corHfRepO ρ O q.out (Z (q.out⁻¹ * h * q.out))) ⊗ₜ[Qp] (1 : B) =
          actVB PD ρ h (actVB PD ρ q.out X) - actVB PD ρ q.out X := by
        intro q
        change (ρ q.out _) ⊗ₜ[Qp] (1 : B) = _
        rw [← h1, hX _ (Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out), map_sub, hmul, hmul]
        congr 3
        group
      rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_sub_distrib]
      change _ + (ρ h x ⊗ₜ[Qp] (1 : B) - _) = _
      abel⟩
  have hn : (H.index : LL) ≠ 0 := Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hFf : F ∈ finiteCocycles PD ρ := by
    refine ⟨⟨hF, hFc⟩, (H.index : LL)⁻¹ • y, fun g => ?_⟩
    have := hy g
    change _ = actVB PD ρ g y - y at this
    rw [map_smul, ← smul_sub, ← this, ← Nat.cast_smul_eq_nsmul LL, inv_smul_smul₀ hn]
  have e : (fun g => H.index • (Submodule.Quotient.mk (f₀ g) : V ⧸ L.T)) =
      LinearMap.compLeft L.T.mkQ G F -
        (LinearMap.pi fun g => actD L g - LinearMap.id) (Submodule.Quotient.mk x') := by
    funext g
    have := (Submodule.Quotient.mk_eq_zero L.T).mpr (hx' g)
    change L.T.mkQ _ = 0 at this
    rw [map_sub, map_sub, map_sub, map_nsmul] at this
    change H.index • L.T.mkQ (f₀ g) = L.T.mkQ (F g) - (L.T.mkQ (corHfRepO ρ O g x') - L.T.mkQ x')
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  rw [e]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨F, hFf, rfl⟩)
    (Submodule.mem_sup_right ⟨_, rfl⟩)

end General

theorem corHf_exists_mul_eq_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (n k : ℕ) (hn : n ≠ 0) (hk : padicValNat l n ≤ k) : ∃ u : O, u * (n : O) = ((l ^ k : ℕ) : O) := by
  have hn' : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have : (n : ℤ_[l]) ∣ (l : ℤ_[l]) ^ k := by
    obtain ⟨m, hm⟩ : l ^ padicValNat l n ∣ n := pow_padicValNat_dvd
    have hlm : ¬ l ∣ m := by
      rintro ⟨c, rfl⟩
      apply pow_succ_padicValNat_not_dvd (p := l) hn
      exact ⟨c, by rw [pow_succ, mul_assoc]; exact hm⟩
    have hu : IsUnit (m : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      exact PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlm)
    have e : (n : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l n * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hm
    rw [e, hu.mul_right_dvd]
    exact pow_dvd_pow _ hk
  obtain ⟨c, hc⟩ := this
  refine ⟨algebraMap ℤ_[l] O c, ?_⟩
  have := congrArg (algebraMap ℤ_[l] O) hc
  simp only [map_pow, map_natCast, map_mul] at this
  rw [Nat.cast_pow, this, mul_comm]

theorem corHf_nsmul_mem {O G M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Submodule O (G → M)) (f : G → M) (n m : ℕ) (h : ∃ u : O, u * (n : O) = (m : O))
    (hf : (fun g => n • f g) ∈ S) : (fun g => m • f g) ∈ S := by
  obtain ⟨u, hu⟩ := h
  convert S.smul_mem u hf using 1
  funext g
  rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, smul_smul, hu]

set_option synthInstance.maxHeartbeats 400000 in

theorem pow_smul_mem_HfD_of_restriction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (H : Subgroup ↥(GK K)) [H.Normal] [H.FiniteIndex], IsOpen (H : Set ↥(GK K)) → ∀ (Z f₀ : ↥(GK K) → V.V), ContinuousOn Z H → (∀ g ∈ H, ∀ h ∈ H, Z (g * h) = Z g + V.ρ g (Z h)) → (∃ X : TensorProduct ℚ_[l] V.V P.R.B, ∀ h ∈ H, Z h ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) V.ρ h X - X) → (∀ g h, f₀ (g * h) - (f₀ g + V.ρ g (f₀ h)) ∈ V.L.T) → (∀ h ∈ H, Z h - f₀ h ∈ V.L.T) → ∀ k : ℕ, padicValNat l H.index ≤ k → (fun g => (l ^ k : ℕ) • (Submodule.Quotient.mk (f₀ g) : V.V ⧸ V.L.T)) ∈ HfD (P.PD K) V.L := by
  intro l _ P K LL V H _ _ hH Z f₀ hZ hc hX h₀ hZf k hk
  haveI : IsTopologicalAddGroup V.V := IsModuleTopology.topologicalAddGroup ↥LL.1 V.V
  haveI : ContinuousSMul ↥LL.1 V.V := IsModuleTopology.toContinuousSMul ↥LL.1 V.V
  exact corHf_nsmul_mem _ _ H.index _
    (corHf_exists_mul_eq_pow l _ _ k Subgroup.FiniteIndex.index_ne_zero hk)
    (index_smul_mem_HfD (P.PD K) V.ρ V.L
      (fun g => IsModuleTopology.continuous_of_linearMap (V.ρ g)) V.cont H hH Z f₀ hZ hc hX h₀ hZf)

end GlobalTheory
