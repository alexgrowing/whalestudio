import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetZ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem pow_wToC (σ : ℂ_[p] →+* ℂ_[p]) (hσ : ∀ w : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p (sigW p w))
    (k : ℕ) (w : FormalGroupSystem.WW p) : (σ ^ k) (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p ((sigW p)^[k] w) := by
  have h : Function.Semiconj (Formalism.L2.G.Pend.wToC p) (sigW p) σ := fun w => (hσ w).symm
  rw [RingHom.coe_pow]
  exact (h.iterate_right k w).symm

theorem comb {κ ι ρ : Type} [Fintype ρ] (S : Finset ι) (a : ι → ℂ_[p]) (b : ι → ρ → ℂ_[p])
    (L : ρ → MvPowerSeries κ ℂ_[p]) (r : ρ) (h : ∀ r', ∑ i ∈ S, a i * b i r' = if r' = r then 1 else 0) :
    ∑ i ∈ S, C (a i) * ∑ r', C (b i r') * L r' = L r := by
  simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, h]
  simp

theorem sum_even {M : Type} [AddCommMonoid M] {n' : ℕ} (he : Even n') (g : ℕ → M) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s), g s.val = ∑ i ∈ Finset.range (n' / 2), g (2 * i) := by
  obtain ⟨m, rfl⟩ := he
  refine Finset.sum_bij' (fun s _ => s.val / 2) (fun i hi => ⟨2 * i, by simp at hi; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp [IsOddPos] at hs ⊢; omega
  · intro i hi; simp [IsOddPos]
  · intro s hs; simp [IsOddPos] at hs; ext; simp; omega
  · intro i hi; simp
  · intro s hs; simp [IsOddPos] at hs; congr 1; omega

theorem sum_odd {M : Type} [AddCommMonoid M] {n' : ℕ} (he : Even n') (g : ℕ → M) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s), g s.val = ∑ i ∈ Finset.range (n' / 2), g (2 * i + 1) := by
  obtain ⟨m, rfl⟩ := he
  have hm : (m + m) / 2 = m := by omega
  refine Finset.sum_bij' (fun s _ => s.val / 2) (fun i hi => ⟨2 * i + 1, by rw [Finset.mem_range, hm] at hi; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro s hs; have := s.isLt; rw [Finset.mem_range, hm]; omega
  · intro i hi; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩; show (2 * i + 1) % 2 = 1; omega
  · intro s hs; have h2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2; ext; show 2 * (s.val / 2) + 1 = s.val; omega
  · intro i hi; show (2 * i + 1) / 2 = i; omega
  · intro s hs; have h2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2; congr 1; omega

end GlobalTheory.OnePlace.Ident

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem eq_subst_subst {n' : ℕ} [NeZero n'] (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p])
    (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (ht0 : ∀ s, constantCoeff (t s) = 0)
    (hx0 : ∀ r, constantCoeff (x r) = 0) (hxt : ∀ s, subst x (t s) = X s) (f : MvPowerSeries (ZMod n') ℂ_[p]) :
    f = subst x (subst t f) := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ht0) (hasSubst_of_constantCoeff_zero hx0),
    show (fun s => subst x (t s)) = X from funext hxt, subst_self]
  rfl

theorem subst_sum_C_mul {κ τ ι : Type} (x : κ → MvPowerSeries τ ℂ_[p]) (hx : HasSubst x) (S : Finset ι)
    (c : ι → ℂ_[p]) (f : ι → MvPowerSeries κ ℂ_[p]) :
    subst x (∑ i ∈ S, C (c i) * f i) = ∑ i ∈ S, C (c i) * subst x (f i) := by
  rw [← coe_substAlgHom hx]
  simp only [map_sum, map_mul, coe_substAlgHom, subst_C]

theorem subst_lg {κ τ : Type} [Finite κ] (x : κ → MvPowerSeries τ ℂ_[p]) (hx0 : ∀ r, constantCoeff (x r) = 0) (k : κ) :
    subst x (GlobalTheory.ThBe0.lg (l := p) k) = PowerSeries.subst (x k) (Formalism.MainNotions.GL3Theta.logF p) := by
  have hx := hasSubst_of_constantCoeff_zero hx0
  rw [GlobalTheory.ThBe0.lg, GlobalTheory.BeProps.subst_psubst hx (constantCoeff_X k), subst_X hx]

theorem hasSubst_jetZ (n' r0 r1 : ℕ) [NeZero n'] : HasSubst (jetZ p n' r0 r1) :=
  hasSubst_of_constantCoeff_zero fun z => by
    rw [jetZ, ← GlobalTheory.BiextInhab.bridge]
    exact GlobalTheory.BeProps.constantCoeff_laAt _ _

theorem hasSubst_copy {n' r0 r1 : ℕ} [NeZero n'] (a : Fin r0) (b : Fin r1) :
    HasSubst (fun u : ZMod n' => (X (u, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem subst_jetZ_lin {n' r0 r1 : ℕ} [NeZero n'] (S : Finset (Fin n')) (c : Fin n' → ℂ_[p]) (a : Fin r0) (b : Fin r1) :
    subst (jetZ p n' r0 r1) (∑ s ∈ S, C (c s) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p])) =
      subst (fun u : ZMod n' => (X (u, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
        (∑ s ∈ S, C (c s) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n')) := by
  rw [subst_sum_C_mul _ (hasSubst_jetZ n' r0 r1), subst_sum_C_mul _ (hasSubst_copy a b)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [subst_X (hasSubst_jetZ n' r0 r1), jetZ, ← GlobalTheory.BiextInhab.bridge]
  rfl

end GlobalTheory.OnePlace.Ident

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

theorem zOm_even (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[p])
    (k : ℕ) (hk : k < n') (he : Even k) :
    GlobalTheory.ThBe0.zOm σ (d := n') om om' ((k : ℕ) : ZMod n') =
      ∑ r, C ((σ ^ k) (om r)) * GlobalTheory.ThBe0.lg (l := p) (Sum.inl r : ρ ⊕ ρ) := by
  have hv : ((k : ℕ) : ZMod n').val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [GlobalTheory.ThBe0.zOm, hv, if_pos he]

theorem zOm_odd (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[p])
    (k : ℕ) (hk : k < n') (he : ¬ Even k) :
    GlobalTheory.ThBe0.zOm σ (d := n') om om' ((k : ℕ) : ZMod n') =
      ∑ r, C ((σ ^ k) (om' r)) * GlobalTheory.ThBe0.lg (l := p) (Sum.inr r : ρ ⊕ ρ) := by
  have hv : ((k : ℕ) : ZMod n').val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [GlobalTheory.ThBe0.zOm, hv, if_neg he]

theorem coordZ_jetZ : ∀ {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), (∀ w : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p (sigW p w)) → ∀ {n' : ℕ} [NeZero n'], Even n' → ∀ (B : OmBasis p n'), GlobalTheory.ThBe0.DualOm σ n' (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) → ∀ (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), (∀ s, MvPowerSeries.constantCoeff (t s) = 0) → (∀ r, MvPowerSeries.constantCoeff (x r) = 0) → (∀ s, MvPowerSeries.subst t (GlobalTheory.ThStr.laS p n' s) = GlobalTheory.ThBe0.zOm σ (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) s) → (∀ s, MvPowerSeries.subst x (t s) = MvPowerSeries.X s) → ∀ (r0 r1 : ℕ) (i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1), MvPowerSeries.subst (jetZ p n' r0 r1) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 i)) = PowerSeries.subst (xiE x i) (Formalism.MainNotions.GL3Theta.logF p) := by
  intro p _ σ hσ n' _ he B hD t x ht0 hx0 ht hxt r0 r1 i
  have hx : HasSubst x := hasSubst_of_constantCoeff_zero hx0
  have key : ∀ s : ZMod n', GlobalTheory.ThStr.laS p n' s = subst x (GlobalTheory.ThBe0.zOm σ (fun r => Formalism.L2.G.Pend.wToC p (B.om r))
      (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) s) := fun s => by
    rw [← ht s]; exact eq_subst_subst t x ht0 hx0 hxt _
  rcases i with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · have hm : MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 (Sum.inl (r, a, b))) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
          C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r))) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p]) := by
      simp only [coordZ, map_sum, map_mul, map_C, map_X, one_mul, Algebra.algebraMap_self, RingHom.id_apply, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap,
        pow_wToC σ hσ]
    rw [hm, subst_jetZ_lin]
    have hin : ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
        C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r))) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') =
        PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p) := by
      have e1 : ∀ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
          GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') = ∑ r', C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r'))) *
            PowerSeries.subst (x (Sum.inl r')) (Formalism.MainNotions.GL3Theta.logF p) := by
        intro s hs
        have hs2 : ¬ s.val % 2 = 1 := (Finset.mem_filter.mp hs).2
        rw [key, zOm_even p σ _ _ s.val s.isLt (Nat.even_iff.mpr (by omega)), subst_sum_C_mul _ hx]
        simp only [subst_lg x hx0]
      rw [Finset.sum_congr rfl fun s hs => by rw [e1 s hs]]
      refine comb _ _ _ _ r fun r' => ?_
      rw [sum_even he (fun k => (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r')))]
      have hk : ∀ k : ℕ, (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r')) =
          (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r') * Formalism.L2.G.Pend.wToC p (B.omS r)) := fun k => by
        rw [map_mul, mul_comm]
      simp only [hk]
      rw [hD.dual r' r]
      by_cases h : r' = r <;> simp [h]
    rw [hin, GlobalTheory.BeProps.subst_psubst (hasSubst_copy a b) (hx0 _)]
    rfl
  · have hm : MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 (Sum.inr (r, a, b))) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
          C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r))) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p]) := by
      simp only [coordZ, map_sum, map_mul, map_C, map_X, one_mul, Algebra.algebraMap_self, RingHom.id_apply, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap,
        pow_wToC σ hσ]
    rw [hm, subst_jetZ_lin]
    have hin : ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
        C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r))) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') =
        PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p) := by
      have e1 : ∀ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
          GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') = ∑ r', C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r'))) *
            PowerSeries.subst (x (Sum.inr r')) (Formalism.MainNotions.GL3Theta.logF p) := by
        intro s hs
        have hs2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2
        rw [key, zOm_odd p σ _ _ s.val s.isLt (Nat.not_even_iff.mpr hs2), subst_sum_C_mul _ hx]
        simp only [subst_lg x hx0]
      rw [Finset.sum_congr rfl fun s hs => by rw [e1 s hs]]
      refine comb _ _ _ _ r fun r' => ?_
      rw [sum_odd he (fun k => (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r')))]
      have hk : ∀ k : ℕ, (σ ^ (2 * k + 1)) (Formalism.L2.G.Pend.wToC p (B.om r)) * (σ ^ (2 * k + 1)) (Formalism.L2.G.Pend.wToC p (B.omS r')) =
          σ ((σ ^ (2 * k)) (Formalism.L2.G.Pend.wToC p (B.om r) * Formalism.L2.G.Pend.wToC p (B.omS r'))) := fun k => by
        rw [← map_mul, pow_succ']; rfl
      simp only [hk]
      rw [← map_sum, hD.dual r r']
      by_cases h : r = r' <;> simp [h, eq_comm]
    rw [hin, GlobalTheory.BeProps.subst_psubst (hasSubst_copy a b) (hx0 _)]
    rfl

end GlobalTheory.OnePlace.Ident
