import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem sum_coef_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0)
    (r₀ : R) (a : Fin N) (b : Fin N') (i : Fin r) (s : ZMod (nP D p)) :
    ∑ k, (if s.val % 2 = 0 then fOf D p σ om R g ((r₀, k), a, b) i * σ^[s.val] (oms k)
      else fOf' D p σ oms R g ((r₀, k), a, b) i * σ^[s.val] (om k)) = g (OrbitPlaces.orbMap D p r₀ s) a b i := by
  by_cases hs : s.val % 2 = 0
  · simp only [hs, if_true, fOf, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_true]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (om k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (oms k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp only [ht, if_true]
        have h := hdual t s (by rw [ht, hs])
        rw [if_neg hts] at h
        calc ∑ k, σ^[t.val] (om k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (oms k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[t.val] (om k) * σ^[s.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
      · simp [ht]
    · intro h; exact absurd (Finset.mem_univ s) h
  · simp only [hs, if_false, fOf', Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_false]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (om k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp [ht]
      · simp only [ht, if_false]
        have h := hdual s t (by omega)
        rw [if_neg (Ne.symm hts)] at h
        calc ∑ k, σ^[t.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (om k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h

theorem hypZ_term (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {n : Type} (f f' : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension p) (i : n)
    (e : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1) :
    MvPowerSeries.C (f e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
      MvPowerSeries.C (f' e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2 =
    ∑ s : ZMod (nP D p), MvPowerSeries.C (((if s.val % 2 = 0 then f e i * σ^[s.val] (oms e.1.2)
      else f' e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) := by
  unfold linEv linOd
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s.val % 2 = 0
  · simp [hs, map_mul, mul_assoc]
  · simp [hs, map_mul, mul_assoc]

theorem bijective_orbMap (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hR : OrbitPlaces.IsReps D p R) :
    Function.Bijective (fun y : R × ZMod (nP D p) => OrbitPlaces.orbMap D p y.1 y.2) := by
  constructor
  · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ h
    simp only at h
    have hr : (r₁ : OrbitPlaces.Pl D) = r₂ := by
      obtain ⟨r0, _, hu⟩ := hR (OrbitPlaces.orbMap D p r₁ s₁)
      have e1 := hu r₁ ⟨r₁.2, s₁.val, rfl⟩
      have e2 := hu r₂ ⟨r₂.2, s₂.val, h.symm⟩
      rw [e1, e2]
    have hr' : r₁ = r₂ := Subtype.ext hr
    subst hr'
    have hs : s₁ = s₂ := ZMod.val_injective _ (posPl_inj D p r₁ _ _ (ZMod.val_lt s₁) (ZMod.val_lt s₂) h)
    rw [hs]
  · intro z
    obtain ⟨r0, ⟨hr0, e, he⟩, _⟩ := hR z
    refine ⟨(⟨r0, hr0⟩, (e : ZMod (nP D p))), ?_⟩
    show posPl D p r0 (e : ZMod (nP D p)).val = z
    rw [ZMod.val_natCast, posPl_mod, he]

end GlobalTheory.KerStd.HypCoord

namespace GlobalTheory.KerStd.HypCoord

theorem hypZ_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hR : OrbitPlaces.IsReps D p R)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) (i : Fin r) :
    hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i =
      ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j := by
  set F : (R × Fin (nP D p / 2)) × Fin N × Fin N' → ZMod (nP D p) → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    fun e s => MvPowerSeries.C (((if s.val % 2 = 0 then fOf D p σ om R g e i * σ^[s.val] (oms e.1.2)
      else fOf' D p σ oms R g e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) *
        MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) with hF
  have hB : Function.Bijective (fun y : (R × ZMod (nP D p)) × Fin N × Fin N' => ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) :
      OrbitPlaces.Pl D × Fin N × Fin N')) :=
    (bijective_orbMap D p R hR).prodMap Function.bijective_id
  let eqv : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2) ≃
      ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p) :=
    { toFun := fun y => (((y.1.1.1, y.2), y.1.2), y.1.1.2)
      invFun := fun x => (((x.1.1.1, x.2), x.1.2), x.1.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold hypZ
  calc ∑ e, (MvPowerSeries.C (fOf D p σ om R g e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
        MvPowerSeries.C (fOf' D p σ oms R g e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2)
      = ∑ e, ∑ s, F e s := Finset.sum_congr rfl fun e _ => hypZ_term D p σ om oms R _ _ i e
    _ = ∑ x : ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p), F x.1 x.2 := (Fintype.sum_prod_type' F).symm
    _ = ∑ y : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2), F ((y.1.1.1, y.2), y.1.2) y.1.1.2 :=
        (Fintype.sum_equiv eqv _ _ fun _ => rfl).symm
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N', ∑ k, F ((y.1.1, k), y.2) y.1.2 :=
        Fintype.sum_prod_type' (fun (y : (R × ZMod (nP D p)) × Fin N × Fin N') (k : Fin (nP D p / 2)) => F ((y.1.1, k), y.2) y.1.2)
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N',
          MvPowerSeries.C ((g (OrbitPlaces.orbMap D p y.1.1 y.1.2) y.2.1 y.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) *
            MvPowerSeries.X ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) : OrbitPlaces.Pl D × Fin N × Fin N') := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← sum_coef_fOf D p σ om oms R g hdual y.1.1 y.2.1 y.2.2 i y.1.2, hF]
        simp only [← Finset.sum_mul, ← map_sum]
        congr 2
        push_cast
        rfl
    _ = _ := hB.sum_comp (fun j : OrbitPlaces.Pl D × Fin N × Fin N' =>
          MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j)

theorem linForm_hypZ : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (κ : Type) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p) (Λ : κ → Fin r → ℂ_[p]) (T : κ → OrbitPlaces.Pl D × Fin N × Fin N' → ℂ_[p]), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 → ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) → (∀ q z a b, ∑ i, Λ q i * ((g z a b i : MaximalUnramifiedExtension p) : ℂ_[p]) = T q (z, a, b)) → ∀ q, ∑ i, MvPowerSeries.C (Λ q i) * hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i = ∑ j, MvPowerSeries.C (T q j) * MvPowerSeries.X j := by
  intro D p _ σ om oms R N N' r κ g Λ T _ hR hdual hT q
  simp only [hypZ_fOf D p σ om oms R g hR hdual, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hT q j.1 j.2.1 j.2.2, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc]

end GlobalTheory.KerStd.HypCoord
