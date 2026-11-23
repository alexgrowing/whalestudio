import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocLanglands
open scoped Pointwise

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local notation "NK₁[" k ", " m "]" =>
  ((unipB k (Fin m) : Set (GL (Fin m) k)) * (KOne k (Fin m) : Set (GL (Fin m) k)))

section Ring

variable {m : ℕ}

theorem unipB_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {x : GL (Fin m) R}
    (hx : x ∈ unipB R (Fin m)) : Matrix.GeneralLinearGroup.map f x ∈ unipB S (Fin m) := by
  rw [mem_unipB] at hx ⊢
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · show f ((x : Matrix (Fin m) (Fin m) R) a b) = 0
    rw [hx.1 a b hab, map_zero]
  · show f ((x : Matrix (Fin m) (Fin m) R) a a) = 1
    rw [hx.2 a, map_one]

theorem unipB_of_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f)
    {x : GL (Fin m) R} (hx : Matrix.GeneralLinearGroup.map f x ∈ unipB S (Fin m)) : x ∈ unipB R (Fin m) := by
  rw [mem_unipB] at hx ⊢
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have h0 : f ((x : Matrix (Fin m) (Fin m) R) a b) = 0 := hx.1 a b hab
    exact (map_eq_zero_iff f hf).1 h0
  · have h1 : f ((x : Matrix (Fin m) (Fin m) R) a a) = f 1 := by rw [map_one]; exact hx.2 a
    exact hf h1

end Ring

section Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem mem_unipotentKOne_mul_left {u x : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) :
    u * x ∈ NK₁[k, m] ↔ x ∈ NK₁[k, m] := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 h
    refine Set.mem_mul.2 ⟨u⁻¹ * a, (unipB k (Fin m)).mul_mem ((unipB k (Fin m)).inv_mem hu) ha, b, hb, ?_⟩
    rw [mul_assoc, e, inv_mul_cancel_left]
  · intro h
    obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 h
    refine Set.mem_mul.2 ⟨u * a, (unipB k (Fin m)).mul_mem hu ha, b, hb, ?_⟩
    rw [mul_assoc, e]

theorem isOpen_unipotentKOne : IsOpen NK₁[k, m] :=
  (GlobalTheory.StepData.isOpen_KOne (k := k) (n := Fin m)).mul_left

theorem isClosed_unipotentKOne : IsClosed NK₁[k, m] := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rw [Set.mem_compl_iff] at hx
  have hU : IsOpen ((fun y : GL (Fin m) k => x⁻¹ * y) ⁻¹' (KOne k (Fin m) : Set (GL (Fin m) k))) :=
    (GlobalTheory.StepData.isOpen_KOne (k := k) (n := Fin m)).preimage (continuous_const.mul continuous_id)
  have hx1 : x ∈ (fun y : GL (Fin m) k => x⁻¹ * y) ⁻¹' (KOne k (Fin m) : Set (GL (Fin m) k)) := by
    show x⁻¹ * x ∈ KOne k (Fin m)
    rw [inv_mul_cancel]
    exact (KOne k (Fin m)).one_mem
  refine Filter.mem_of_superset (hU.mem_nhds hx1) ?_
  intro y hy
  rw [Set.mem_compl_iff]
  intro hyS
  have hy' : x⁻¹ * y ∈ KOne k (Fin m) := hy
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 hyS
  apply hx
  refine Set.mem_mul.2 ⟨a, ha, b * (x⁻¹ * y)⁻¹, (KOne k (Fin m)).mul_mem hb ((KOne k (Fin m)).inv_mem hy'), ?_⟩
  rw [← mul_assoc, e, mul_inv_rev, inv_inv, mul_inv_cancel_left]

theorem isLocallyConstant_indicator_one {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    (hU' : IsClosed U) : IsLocallyConstant (U.indicator (1 : X → ℂ)) := by
  intro s
  change IsOpen (U.indicator (fun _ => (1 : ℂ)) ⁻¹' s)
  have h := Set.indicator_const_preimage U s (1 : ℂ)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h <;> rw [h]
  · exact isOpen_univ
  · exact hU
  · exact hU'.isOpen_compl
  · exact isOpen_empty

theorem isTestFun_indicator_unipotentKOne : IsTestFun (Set.indicator NK₁[k, m] (1 : GL (Fin m) k → ℂ)) := by
  classical
  refine ⟨fun u hu x => ?_, isLocallyConstant_indicator_one isOpen_unipotentKOne isClosed_unipotentKOne,
    (KO k (Fin m) : Set (GL (Fin m) k)), GlobalTheory.SplitFlip.isCompact_KO, fun x hx => ?_⟩
  · simp only [Set.indicator_apply, mem_unipotentKOne_mul_left hu, Pi.one_apply]
  · obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 (Set.mem_of_indicator_ne_zero hx)
    exact ⟨a, ha, b, GlobalTheory.StepData.KOne_le_KO hb, e.symm⟩

end Gen

section Loc

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]

theorem exists_unip_lift {m : ℕ} {u : Gn g m} (hu : u ∈ unipB (ZMod g) (Fin m)) :
    ∃ v : GL (Fin m) ℤ_[g], v ∈ unipB ℤ_[g] (Fin m) ∧ red g m v = u := by
  classical
  rw [mem_unipB] at hu
  let M : Matrix (Fin m) (Fin m) ℤ_[g] := fun a b =>
    if b < a then 0 else if a = b then 1 else (ZMod.cast ((u : Matrix (Fin m) (Fin m) (ZMod g)) a b) : ℤ_[g])
  have hM : M.BlockTriangular id := fun a b hab => by
    have hab' : b < a := hab
    simp only [M]; rw [if_pos hab']
  have hdiag : ∀ a, M a a = 1 := fun a => by simp [M]
  have hd : IsUnit M.det := by
    rw [Matrix.det_of_isUpperTriangular hM]
    simp [hdiag]
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det M).2 hd
  refine ⟨v, ?_, ?_⟩
  · rw [mem_unipB, hv]
    exact ⟨fun a b hab => by simp only [M]; rw [if_pos hab], hdiag⟩
  · refine Units.ext (Matrix.ext fun a b => ?_)
    show PadicInt.toZMod ((v : Matrix (Fin m) (Fin m) ℤ_[g]) a b) = (u : Matrix (Fin m) (Fin m) (ZMod g)) a b
    rw [hv]
    simp only [M]
    split_ifs with h1 h2
    · rw [map_zero, hu.1 a b h1]
    · rw [← h2, map_one, hu.2 a]
    · exact ZMod.ringHom_map_cast _ _

theorem card_filter_unip {m : ℕ} (c : Gn g m)
    [DecidablePred fun κ : Gn g m => c * κ⁻¹ ∈ unipB (ZMod g) (Fin m)] :
    (Finset.univ.filter fun κ : Gn g m => c * κ⁻¹ ∈ unipB (ZMod g) (Fin m)).card =
      Nat.card (unipB (ZMod g) (Fin m)) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun κ => ⟨c * (κ : Gn g m)⁻¹, κ.2⟩
      invFun := fun v => ⟨(v : Gn g m)⁻¹ * c, by rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]; exact v.2⟩
      left_inv := fun κ => Subtype.ext (by simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right])
      right_inv := fun v => Subtype.ext (by simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]) }

variable (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

def phi (m : ℕ) : GL (Fin m) ℤ_[g] →* GL (Fin m) (w.adicCompletion E) :=
  (Matrix.GeneralLinearGroup.map i.toRingHom).comp (inc g m)

theorem phi_apply {m : ℕ} (b : GL (Fin m) ℤ_[g]) :
    phi i m b = Matrix.GeneralLinearGroup.map i.toRingHom (inc g m b) := rfl

include hi

theorem mem_unipotentKOne_iff {m : ℕ} (b : GL (Fin m) ℤ_[g]) :
    phi i m b ∈ NK₁[w.adicCompletion E, m] ↔ red g m b ∈ unipB (ZMod g) (Fin m) := by
  constructor
  · intro h
    obtain ⟨a, ha, c, hc, e⟩ := Set.mem_mul.1 h
    obtain ⟨d, hd, rfl⟩ := DzIso.exists_of_mem_KOne i hi hc
    have e' : a * phi i m d = phi i m b := e
    have ha' : phi i m (b * d⁻¹) = a := by rw [map_mul, map_inv, ← e', mul_inv_cancel_right]
    have h1 : phi i m (b * d⁻¹) ∈ unipB (w.adicCompletion E) (Fin m) := by rw [ha']; exact ha
    have h2 : inc g m (b * d⁻¹) ∈ unipB ℚ_[g] (Fin m) :=
      unipB_of_map (x := inc g m (b * d⁻¹)) i.toRingHom i.injective h1
    have h3 : b * d⁻¹ ∈ unipB ℤ_[g] (Fin m) :=
      unipB_of_map (algebraMap ℤ_[g] ℚ_[g]) (fun x y hxy => PadicInt.ext hxy) h2
    have h4 : red g m (b * d⁻¹) ∈ unipB (ZMod g) (Fin m) := unipB_map (PadicInt.toZMod (p := g)) h3
    rwa [map_mul, map_inv, hd, inv_one, mul_one] at h4
  · intro h
    obtain ⟨v, hv, hvr⟩ := exists_unip_lift h
    have h1 : red g m (v⁻¹ * b) = 1 := by rw [map_mul, map_inv, hvr, inv_mul_cancel]
    refine Set.mem_mul.2 ⟨phi i m v, unipB_map i.toRingHom (unipB_map (algebraMap ℤ_[g] ℚ_[g]) hv),
      phi i m (v⁻¹ * b), DzIso.map_mem_KOne i hi _ h1, ?_⟩
    rw [← map_mul (phi i m), mul_inv_cancel_left]

theorem eq_of_red {m : ℕ} (F : GL (Fin m) (w.adicCompletion E) → ℂ)
    (h2 : ∀ x, ∀ k ∈ KOne (w.adicCompletion E) (Fin m), F (x * k) = F x) {a b : GL (Fin m) ℤ_[g]}
    (hab : red g m a = red g m b) : F (phi i m a) = F (phi i m b) := by
  have h0 : red g m (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
  have hk : phi i m (a⁻¹ * b) ∈ KOne (w.adicCompletion E) (Fin m) := DzIso.map_mem_KOne i hi _ h0
  rw [← h2 (phi i m a) _ hk, ← map_mul (phi i m), mul_inv_cancel_left]

theorem integral_eq {m : ℕ}
    (I : (GL (Fin m) (w.adicCompletion E) → ℂ) →ₗ[ℂ] ℂ) (hI : IsInvIntegral I) (F : GL (Fin m) (w.adicCompletion E) → ℂ)
    (h1 : ∀ u ∈ unipB (w.adicCompletion E) (Fin m), ∀ x, F (u * x) = F x)
    (h2 : ∀ x, ∀ k ∈ KOne (w.adicCompletion E) (Fin m), F (x * k) = F x)
    (h3 : ∀ x, F x ≠ 0 → ∃ u ∈ unipB (w.adicCompletion E) (Fin m), ∃ k ∈ KO (w.adicCompletion E) (Fin m), x = u * k)
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, GlobalTheory.GLp.red g m (s κ) = κ) :
    (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * I F =
      I (Set.indicator ((unipB (w.adicCompletion E) (Fin m) : Set _) * (KOne (w.adicCompletion E) (Fin m) : Set _)) 1) *
        ∑ κ : Gn g m, F (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m (s κ))) := by
  classical
  simp only [← phi_apply i]
  have hT := isTestFun_indicator_unipotentKOne (k := w.adicCompletion E) (m := m)
  have key : ∀ y, (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * F y =
      ∑ κ : Gn g m, F (phi i m (s κ)) * Set.indicator NK₁[w.adicCompletion E, m] 1 (y * (phi i m (s κ))⁻¹) := by
    intro y
    by_cases hmem : ∃ u ∈ unipB (w.adicCompletion E) (Fin m), ∃ c ∈ KO (w.adicCompletion E) (Fin m), y = u * c
    · obtain ⟨u, hu, c, hc, rfl⟩ := hmem
      obtain ⟨a, rfl⟩ := DzIso.exists_of_mem_KO i hi hc
      rw [← phi_apply i a]
      have hterm : ∀ κ : Gn g m, F (phi i m (s κ)) *
          Set.indicator NK₁[w.adicCompletion E, m] 1 (u * phi i m a * (phi i m (s κ))⁻¹) =
          if red g m a * κ⁻¹ ∈ unipB (ZMod g) (Fin m) then F (phi i m a) else 0 := by
        intro κ
        have e : u * phi i m a * (phi i m (s κ))⁻¹ = u * phi i m (a * (s κ)⁻¹) := by
          rw [mul_assoc, map_mul, map_inv]
        have hr : red g m (a * (s κ)⁻¹) = red g m a * κ⁻¹ := by rw [map_mul, map_inv, hs]
        rw [e]
        simp only [Set.indicator_apply, mem_unipotentKOne_mul_left hu, mem_unipotentKOne_iff i hi, hr, Pi.one_apply]
        split_ifs with hU
        · rw [mul_one]
          obtain ⟨v, hv, hvr⟩ := exists_unip_lift hU
          have hvN : phi i m v ∈ unipB (w.adicCompletion E) (Fin m) :=
            unipB_map i.toRingHom (unipB_map (algebraMap ℤ_[g] ℚ_[g]) hv)
          rw [← h1 _ hvN, ← map_mul (phi i m)]
          apply eq_of_red i hi F h2
          rw [map_mul, hvr, hs, inv_mul_cancel_right]
        · rw [mul_zero]
      rw [h1 u hu, Finset.sum_congr rfl fun κ _ => hterm κ, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, card_filter_unip, nsmul_eq_mul]
    · have hFy : F y = 0 := by
        by_contra hne
        exact hmem (h3 y hne)
      rw [hFy, mul_zero]
      refine (Finset.sum_eq_zero fun κ _ => ?_).symm
      have hn : y * (phi i m (s κ))⁻¹ ∉ NK₁[w.adicCompletion E, m] := by
        intro hS
        obtain ⟨a, ha, b, hb, e⟩ := Set.mem_mul.1 hS
        exact hmem ⟨a, ha, b * phi i m (s κ),
          (KO (w.adicCompletion E) (Fin m)).mul_mem (GlobalTheory.StepData.KOne_le_KO hb) (DzIso.map_inc_mem_KO i hi _),
          by rw [← mul_assoc, e, inv_mul_cancel_right]⟩
      rw [Set.indicator_apply, if_neg hn, mul_zero]
  have e2 : (fun y => (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * F y) =
      ∑ κ : Gn g m, F (phi i m (s κ)) •
        (fun y => Set.indicator NK₁[w.adicCompletion E, m] 1 (y * (phi i m (s κ))⁻¹)) := by
    funext y
    rw [key y, Finset.sum_apply]
    rfl
  have e1 : I (fun y => (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * F y) =
      (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * I F := by
    have : (fun y => (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * F y) = (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) • F := rfl
    rw [this, map_smul, smul_eq_mul]
  rw [← e1, congrArg I e2, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [map_smul, smul_eq_mul, hI _ hT, mul_comm]

end Loc

end DiscreteGroups.sglob.DzRed
