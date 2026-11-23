import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.InertiaLift

open ReciprocityTheory.DiscreteGroups.LocalClassField in

theorem unr_inf_le {l : ℕ} [Fact l.Prime] (F K'' : IntermediateField ℚ_[l] (Om l))
    (hF : FiniteDimensional ℚ_[l] F) (hK : FiniteDimensional ℚ_[l] K'') (hFK : F ≤ K'') :
    (F ⊔ MaximalUnramifiedExtension l) ⊓ K'' ≤ F ⊔ (K'' ⊓ MaximalUnramifiedExtension l) := by
  set N := (F ⊔ MaximalUnramifiedExtension l) ⊓ K'' with hNdef
  have hN : FiniteDimensional ℚ_[l] N :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_right : N ≤ K'')).toLinearMap
      (IntermediateField.inclusion (inf_le_right : N ≤ K'')).injective
  have hNur : N ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l F := by
    rw [Kur_eq hF]
    refine inf_le_left.trans (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) F)
    rintro x ⟨m, -, hm, hx⟩
    exact ⟨m, hm, hx⟩
  obtain ⟨n, hn, hNn⟩ := exists_le_Kn_of_le_Kur hF hN hNur
  have hFN : F ≤ N := le_inf le_sup_left hFK
  have hdvd : Module.finrank ℚ_[l] F ∣ Module.finrank ℚ_[l] N :=
    IntermediateField.finrank_dvd_of_le_right hFN
  have hpos : 0 < Module.finrank ℚ_[l] N := Module.finrank_pos
  have hFpos : 0 < Module.finrank ℚ_[l] F := Module.finrank_pos
  set d := Module.finrank ℚ_[l] N / Module.finrank ℚ_[l] F
  have hd : 0 < d := Nat.div_pos (Nat.le_of_dvd hpos hdvd) hFpos
  have hNeq : N = Kn l F d := eq_Kn_of_norm l F hF hFN hd (Nat.div_mul_cancel hdvd).symm
    (fun x hx => norm_Kn l F hF hn (hNn hx))
  rw [hNeq]
  refine UnramifiedExtensions.Kn_le F le_sup_left fun ζ hζ => (le_sup_right : K'' ⊓ MaximalUnramifiedExtension l ≤ _) ⟨?_, ?_⟩
  · have h1 : ζ ∈ N := by rw [hNeq]; exact mem_Kn_of_pow l F hζ
    exact h1.2
  · refine IntermediateField.subset_adjoin _ _ ⟨_, ?_, UnramifiedExtensions.not_dvd_qK_pow_sub_one F hF hd, hζ⟩
    have := one_lt_qK l F hF
    have : 1 < qK l F ^ d := Nat.one_lt_pow hd.ne' this
    omega

end GlobalTheory.InertiaLift

namespace GlobalTheory.InertiaLift

theorem exists_mul_of_fixes {l : ℕ} [Fact l.Prime] (M K'' : IntermediateField ℚ_[l] (Om l))
    (hK : FiniteDimensional ℚ_[l] K'')
    (hconj : ∀ s ∈ M.fixingSubgroup, ∀ k ∈ K''.fixingSubgroup, s⁻¹ * k * s ∈ K''.fixingSubgroup)
    (h : GQ l) (hh : ∀ x ∈ M ⊓ K'', h x = x) :
    ∃ i ∈ M.fixingSubgroup, i⁻¹ * h ∈ K''.fixingSubgroup := by
  let T : Subgroup (GQ l) :=
    { carrier := {g | ∃ s ∈ M.fixingSubgroup, s⁻¹ * g ∈ K''.fixingSubgroup}
      one_mem' := ⟨1, M.fixingSubgroup.one_mem, by simpa using K''.fixingSubgroup.one_mem⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨s₁, hs₁, hk₁⟩ ⟨s₂, hs₂, hk₂⟩
        refine ⟨s₁ * s₂, M.fixingSubgroup.mul_mem hs₁ hs₂, ?_⟩
        have e : (s₁ * s₂)⁻¹ * (g₁ * g₂) = (s₂⁻¹ * (s₁⁻¹ * g₁) * s₂) * (s₂⁻¹ * g₂) := by group
        rw [e]
        exact K''.fixingSubgroup.mul_mem (hconj s₂ hs₂ _ hk₁) hk₂
      inv_mem' := by
        rintro g ⟨s, hs, hk⟩
        refine ⟨s⁻¹, M.fixingSubgroup.inv_mem hs, ?_⟩
        have e : s⁻¹⁻¹ * g⁻¹ = (s⁻¹)⁻¹ * (s⁻¹ * g)⁻¹ * s⁻¹ := by group
        rw [e]
        exact hconj _ (M.fixingSubgroup.inv_mem hs) _ (K''.fixingSubgroup.inv_mem hk) }
  have hNT : K''.fixingSubgroup ≤ T := fun k hk => ⟨1, M.fixingSubgroup.one_mem, by simpa using hk⟩
  have hMT : M.fixingSubgroup ≤ T := fun s hs => ⟨s, hs, by simpa using K''.fixingSubgroup.one_mem⟩
  have hopen : IsOpen (T : Set (GQ l)) := Subgroup.isOpen_mono hNT (IntermediateField.fixingSubgroup_isOpen K'')
  let Tc : ClosedSubgroup (GQ l) := ⟨T, Subgroup.isClosed_of_isOpen T hopen⟩
  have hfix : IntermediateField.fixedField T ≤ M ⊓ K'' := by
    refine le_inf ?_ ?_
    · rw [← InfiniteGalois.fixedField_fixingSubgroup M]
      intro x hx s
      exact hx ⟨s.1, hMT s.2⟩
    · rw [← InfiniteGalois.fixedField_fixingSubgroup K'']
      intro x hx s
      exact hx ⟨s.1, hNT s.2⟩
  have hT : h ∈ (IntermediateField.fixedField (Tc : Subgroup (GQ l))).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hh x (hfix hx)
  rw [InfiniteGalois.fixingSubgroup_fixedField Tc] at hT
  exact hT

theorem inertia_of_fixes_Kur {l : ℕ} [Fact l.Prime] (i : GQ l) (hi : ∀ x ∈ MaximalUnramifiedExtension l, i x = x) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖i x - x‖ < 1 := by
  have hn : ∀ y : Om l, ‖i y‖ = ‖y‖ := fun y => (spectralNorm_eq_of_equiv i y).symm
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact lt_of_le_of_lt (ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [hn]; exact hlt) hlt)
  · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar x heq
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
    have h1 : i ζ = ζ := hi ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
    have h2 : i x - x = i (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
    rw [h2]
    exact lt_of_le_of_lt (ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [hn]; exact hxζ) hxζ)

theorem lift : ∀ (l : ℕ) [Fact l.Prime] (K' F K'' : FinExt l), (GK K').Normal → K''.1 = K'.1 ⊔ F.1 →
    ∀ h : GQ l, h ∈ GK F → (∀ x ∈ K0 K'', h x = x) →
      ∃ i : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)), i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (i : GQ l) ∈ GK F ∧
        (i : GQ l)⁻¹ * h ∈ GK K'' := by
  intro l _ K' F K'' hnorm hK'' h hF h0
  have hFK : F.1 ≤ K''.1 := hK'' ▸ le_sup_right
  have hfK : FiniteDimensional ℚ_[l] K''.1 := K''.2
  have hfF : FiniteDimensional ℚ_[l] F.1 := F.2

  have h1 : h ∈ (F.1 ⊔ (K''.1 ⊓ MaximalUnramifiedExtension l)).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hF, (IntermediateField.mem_fixingSubgroup_iff _ _).2 h0⟩
  have h2 : ∀ x ∈ (F.1 ⊔ MaximalUnramifiedExtension l) ⊓ K''.1, h x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 h1 x (unr_inf_le F.1 K''.1 hfF hfK hFK hx)
  have hconj : ∀ s ∈ (F.1 ⊔ MaximalUnramifiedExtension l).fixingSubgroup, ∀ k ∈ K''.1.fixingSubgroup,
      s⁻¹ * k * s ∈ K''.1.fixingSubgroup := by
    intro s hs k hk
    rw [IntermediateField.fixingSubgroup_sup] at hs
    rw [hK'', IntermediateField.fixingSubgroup_sup] at hk ⊢
    refine ⟨?_, F.1.fixingSubgroup.mul_mem (F.1.fixingSubgroup.mul_mem
      (F.1.fixingSubgroup.inv_mem hs.1) hk.2) hs.1⟩
    have := hnorm.conj_mem k hk.1 s⁻¹
    rw [inv_inv] at this
    exact this
  obtain ⟨i, hi, hik⟩ := exists_mul_of_fixes (F.1 ⊔ MaximalUnramifiedExtension l) K''.1 hfK hconj h h2
  rw [IntermediateField.fixingSubgroup_sup] at hi
  have hiQ : i ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact i.commutes y
  refine ⟨⟨i, hiQ⟩, Subgroup.subset_closure ?_, hi.1, hik⟩
  exact inertia_of_fixes_Kur i ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hi.2)

end GlobalTheory.InertiaLift
