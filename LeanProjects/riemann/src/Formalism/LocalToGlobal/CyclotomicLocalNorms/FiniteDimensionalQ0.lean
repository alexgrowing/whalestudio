import Mathlib
import Formalism.LocalToGlobal.CyclotomicLocalNorms.NormLeOneIffIsIntegral
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups

variable {l : ℕ} [Fact l.Prime]

abbrev Q0 (l : ℕ) [Fact l.Prime] : IntermediateField ℚ_[l] (Om l) := ⊥

theorem finiteDimensional_Q0_alt : FiniteDimensional ℚ_[l] (Q0 l) := inferInstance

def ofGQ (g : GQ l) : Neutral.B1.GK l (Q0 l) :=
  { g.toRingEquiv with
    commutes' := fun r => by
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 r.2
      change g (r : Om l) = r
      rw [← ha]
      exact g.commutes a }

theorem ofGQ_apply (g : GQ l) (x : Om l) : ofGQ g x = g x := rfl

theorem qK_bot : LocalClassField.qK l (Q0 l) = l := by
  obtain ⟨f, hf, hq⟩ := LocalClassField.qK_eq_pow l (Q0 l) finiteDimensional_Q0_alt
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hle : LocalClassField.qK l (Q0 l) ≤ l := by
    have hs : Function.Surjective (fun n : Fin l =>
        (⟨((n : ℕ) : LocalClassField.kbar l), natCast_mem _ _⟩ : LocalClassField.resK l (Q0 l))) := by
      rintro ⟨c, hc⟩
      obtain ⟨x, hx, rfl⟩ := (LocalClassField.mem_resK_iff l (Q0 l) c).1 hc
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hx
      have ha1 : ‖a‖ ≤ 1 := by
        rw [← PadicAlgCl.norm_extends, show ((a : ℚ_[l]) : Om l) = (x : Om l) from ha]
        exact LocalClassField.mem_Obar_iff.1 x.2
      set A : ℤ_[l] := ⟨a, ha1⟩ with hA
      obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range A
      refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
      change ((n : ℕ) : LocalClassField.kbar l) = _
      rw [← map_natCast (IsLocalRing.residue (LocalClassField.Obar l)) n, eq_comm, LocalClassField.residue_eq_iff]
      have h2 : ‖A - (n : ℤ_[l])‖ < 1 := by
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PadicInt.not_isUnit_iff] at hmem
      have h3 : ((x : LocalClassField.Obar l) : Om l) - (((n : ℕ) : LocalClassField.Obar l) : Om l)
          = algebraMap ℚ_[l] (Om l) (a - (n : ℚ_[l])) := by
        rw [map_sub, ha, map_natCast]
        rfl
      rw [h3]
      have h4 := PadicAlgCl.norm_extends (p := l) (a - (n : ℚ_[l]))
      rw [show ((a - (n : ℚ_[l]) : ℚ_[l]) : Om l) = algebraMap ℚ_[l] (Om l) (a - (n : ℚ_[l])) from rfl] at h4
      rw [h4]
      rw [PadicInt.norm_def] at h2
      push_cast at h2
      exact h2
    have := Nat.card_le_card_of_surjective _ hs
    exact this.trans_eq ((Nat.card_eq_fintype_card (α := Fin l)).trans (Fintype.card_fin l))
  rw [hq] at hle ⊢
  have : f ≤ 1 := by
    by_contra hcon
    have h2 : l ^ 2 ≤ l ^ f := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  have hf1 : f = 1 := by omega
  rw [hf1, pow_one]

theorem Kur_eq : LocalClassField.MaximalUnramifiedExtension l (Q0 l) = MaximalUnramifiedExtension l := by
  rw [LocalClassField.Kur_eq finiteDimensional_Q0_alt, bot_sup_eq, MaximalUnramifiedExtension]
  congr 1
  ext x
  constructor
  · rintro ⟨m, hm, hx⟩
    exact ⟨m, Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l)), hm, hx⟩
  · rintro ⟨m, -, hm, hx⟩
    exact ⟨m, hm, hx⟩

variable (l) in

def FrobQ : GQ l := (LocalClassField.frobK l (Q0 l)).restrictScalars ℚ_[l]

theorem FrobQ_apply (x : Om l) : FrobQ l x = LocalClassField.frobK l (Q0 l) x := rfl

theorem FrobQ_pow_apply (i : ℕ) (x : Om l) : (FrobQ l ^ i) x = (LocalClassField.frobK l (Q0 l) ^ i) x := by
  induction i generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, FrobQ_apply]

theorem FrobQ_spec (x : Om l) (hx : ‖x‖ ≤ 1) : ‖FrobQ l x - x ^ l‖ < 1 := by
  have := LocalClassField.isFrob_frobK (finiteDimensional_Q0_alt (l := l)) x hx
  rwa [qK_bot] at this

theorem norm_GQ (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := LocalClassField.norm_GK l (Q0 l) (ofGQ g) x

section Fin

variable {F : IntermediateField ℚ_[l] (Om l)}

theorem norm_Kur {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : ∃ a : ℚ_[l], ‖x‖ = ‖a‖ := by
  rw [← Kur_eq] at hx
  obtain ⟨n, hn, hxn⟩ := (LocalClassField.mem_Kur_iff finiteDimensional_Q0_alt x).1 hx
  obtain ⟨y, hy, h⟩ := LocalClassField.norm_Kn l (Q0 l) finiteDimensional_Q0_alt hn hxn
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hy
  exact ⟨a, h.trans (PadicAlgCl.norm_extends l a)⟩

theorem norm_Kur_zpow {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) : ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  obtain ⟨a, ha⟩ := norm_Kur hx
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at ha
    exact h0 ha
  exact ⟨-a.valuation, ha.trans (Padic.norm_eq_zpow_neg_valuation ha0)⟩

theorem eq_Kn (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) :
    F = LocalClassField.Kn l (Q0 l) (Module.finrank ℚ_[l] F) := by
  refine LocalClassField.eq_Kn_of_norm l (Q0 l) finiteDimensional_Q0_alt bot_le Module.finrank_pos ?_ ?_
  · rw [IntermediateField.finrank_bot, mul_one]
  · intro x hx
    obtain ⟨a, ha⟩ := norm_Kur (hle hx)
    exact ⟨algebraMap ℚ_[l] (Om l) a, IntermediateField.algebraMap_mem _ a,
      ha.trans (PadicAlgCl.norm_extends l a).symm⟩

theorem map_mem (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (g : GQ l) {x : Om l}
    (hx : x ∈ F) : g x ∈ F := by
  rw [eq_Kn hF hle] at hx ⊢
  exact LocalClassField.map_mem_Kn l (Q0 l) _ (ofGQ g) hx

theorem normal_of_le_Kur (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) : Normal ℚ_[l] F := by
  rw [IntermediateField.normal_iff_forall_map_le']
  rintro g _ ⟨x, hx, rfl⟩
  exact map_mem hF hle g hx

theorem exists_GQ_of_algHom (τ : F →ₐ[ℚ_[l]] Om l) : ∃ g : GQ l, ∀ x : F, g x = τ x := by
  refine ⟨AlgEquiv.ofBijective (τ.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _), ?_⟩
  intro x
  exact τ.liftNormal_commutes (Om l) x

theorem exists_pow_of_GQ (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (g : GQ l) :
    ∃ i < Module.finrank ℚ_[l] F, ∀ x ∈ F, g x = (FrobQ l ^ i) x := by
  obtain ⟨i, hi, h⟩ := LocalClassField.IsFrobOn.exists_pow l (Q0 l) finiteDimensional_Q0_alt (Module.finrank_pos (R := ℚ_[l]) (M := F))
    ((LocalClassField.isFrob_frobK (finiteDimensional_Q0_alt (l := l))).isFrobOn _) (ofGQ g)
  refine ⟨i, hi, fun x hx => ?_⟩
  rw [FrobQ_pow_apply, ← h x (by rwa [← eq_Kn hF hle])]
  rfl

theorem pow_fixes_iff (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (i : ℕ) :
    (∀ x ∈ F, (FrobQ l ^ i) x = x) ↔ Module.finrank ℚ_[l] F ∣ i := by
  rw [← LocalClassField.IsFrobOn.pow_fixes_iff l (Q0 l) finiteDimensional_Q0_alt (Module.finrank_pos (R := ℚ_[l]) (M := F))
    ((LocalClassField.isFrob_frobK (finiteDimensional_Q0_alt (l := l))).isFrobOn _) i, ← eq_Kn hF hle]
  simp only [FrobQ_pow_apply]

theorem eq_FrobQ_of_congr (hF : FiniteDimensional ℚ_[l] F) (hle : F ≤ MaximalUnramifiedExtension l) (g : GQ l)
    (hg : ∀ x ∈ F, ‖x‖ ≤ 1 → ‖g x - x ^ l‖ < 1) {x : Om l} (hx : x ∈ F) : g x = FrobQ l x := by
  have h1 : LocalClassField.IsFrobOn l (Q0 l) (Module.finrank ℚ_[l] F) (ofGQ g) := by
    intro y hy hy1
    rw [← eq_Kn hF hle] at hy
    rw [qK_bot]
    exact hg y hy hy1
  exact LocalClassField.IsFrobOn.eqOn l (Q0 l) finiteDimensional_Q0_alt (Module.finrank_pos (R := ℚ_[l]) (M := F)) h1
    ((LocalClassField.isFrob_frobK (finiteDimensional_Q0_alt (l := l))).isFrobOn _) (by rwa [← eq_Kn hF hle])

end Fin

theorem mem_bot_of_FrobQ_fixed {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h : FrobQ l x = x) : x ∈ Q0 l := by
  rw [← Kur_eq] at hx
  exact LocalClassField.mem_of_frobK_fixed finiteDimensional_Q0_alt hx h

theorem eq_FrobQ_on_Kur (g : GQ l) (hg : ∀ x ∈ MaximalUnramifiedExtension l, ‖x‖ ≤ 1 → ‖g x - x ^ l‖ < 1) {x : Om l}
    (hx : x ∈ MaximalUnramifiedExtension l) : g x = FrobQ l x := by
  have hx' := hx
  rw [← Kur_eq] at hx'
  obtain ⟨n, hn, hxn⟩ := (LocalClassField.mem_Kur_iff finiteDimensional_Q0_alt x).1 hx'
  have hle : LocalClassField.Kn l (Q0 l) n ≤ MaximalUnramifiedExtension l := by
    rw [← Kur_eq]
    exact LocalClassField.Kn_le_Kur hn
  exact eq_FrobQ_of_congr (LocalClassField.finiteDimensional_Kn l (Q0 l) finiteDimensional_Q0_alt hn) hle g
    (fun y hy => hg y (hle hy)) hxn

theorem mem_bot_of_fixed (g : GQ l) (hg : ∀ x ∈ MaximalUnramifiedExtension l, ‖x‖ ≤ 1 → ‖g x - x ^ l‖ < 1) {x : Om l}
    (hx : x ∈ MaximalUnramifiedExtension l) (h : g x = x) : x ∈ Q0 l :=
  mem_bot_of_FrobQ_fixed hx ((eq_FrobQ_on_Kur g hg hx).symm.trans h)

end Formalism.L2.LocGap.Gal
