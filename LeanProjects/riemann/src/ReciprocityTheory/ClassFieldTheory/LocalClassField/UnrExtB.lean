import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtA
import Lemmata.GeneralBFactUpperTerForm.Imports

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

namespace UnramifiedExtensions

variable {p}

theorem norm_sum_le_of_le {ι : Type} (s : Finset ι) (g : ι → PadicAlgCl p) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j ∈ s, ‖g j‖ ≤ C) : ‖∑ j ∈ s, g j‖ ≤ C := by
  first | exact Bl.general_b_fact_upper_ter_form.goal1 .. | (apply Bl.general_b_fact_upper_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_ter_form.goal1 <;> assumption)

theorem norm_sum_eq_one {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (b : ι → Obar p)
    (hb : ∀ j, (b j : PadicAlgCl p) ∈ K) (i : ι) (hi : b i = 1) :
    ‖∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ = 1 := by
  have hs : ∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p) = ((∑ j, b j * ω j : Obar p) : PadicAlgCl p) := by
    push_cast; rfl
  rw [hs]
  refine le_antisymm (norm_le_one _) (not_lt.1 fun hlt => ?_)
  have h0 := (res_eq_zero_iff _).2 hlt
  rw [map_sum] at h0
  let c : ι → resK p K := fun j => ⟨res (b j), (mem_resK_iff K _).2 ⟨b j, hb j, rfl⟩⟩
  have h1 : ∑ j, c j • IsLocalRing.residue (Obar p) (ω j) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, map_mul]
  have h2 := Fintype.linearIndependent_iff.1 hω c h1 i
  have h3 : res (b i) = 0 := congrArg Subtype.val h2
  rw [hi, map_one] at h3
  exact one_ne_zero h3

end UnramifiedExtensions

theorem norm_le_norm_sum {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (a : ι → K) (i : ι) :
    ‖(a i : PadicAlgCl p)‖ ≤ ‖∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ‖(a j : PadicAlgCl p)‖) ⟨i, Finset.mem_univ i⟩
  refine (hm i (Finset.mem_univ i)).trans ?_
  by_cases h0 : (a m : PadicAlgCl p) = 0
  · rw [h0, norm_zero]; exact norm_nonneg _
  have hpos : 0 < ‖(a m : PadicAlgCl p)‖ := norm_pos_iff.2 h0
  have hle : ∀ j, ‖(a j : PadicAlgCl p) / (a m : PadicAlgCl p)‖ ≤ 1 := by
    intro j
    rw [norm_div, div_le_one hpos]
    exact hm j (Finset.mem_univ j)
  let b : ι → Obar p := fun j => ⟨(a j : PadicAlgCl p) / (a m : PadicAlgCl p), mem_Obar_iff.2 (hle j)⟩
  have h1 := UnramifiedExtensions.norm_sum_eq_one (K := K) ω hω b (fun j => K.div_mem (a j).2 (a m).2) m
    (Subtype.ext (div_self h0))
  have h2 : ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p)
      = (a m : PadicAlgCl p) * ∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = (a m : PadicAlgCl p) * ((a j : PadicAlgCl p) / (a m : PadicAlgCl p) * (ω j : PadicAlgCl p))
    field_simp
  rw [h2, norm_mul, h1, mul_one]

namespace UnramifiedExtensions

variable {p} {K}

noncomputable def comb {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) {ι : Type} [Fintype ι]
    (ω : ι → Obar p) (hL : ∀ j, (ω j : PadicAlgCl p) ∈ L) : (ι → K) →ₗ[ℚ_[p]] L where
  toFun a := ⟨∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p),
    L.sum_mem fun j _ => L.mul_mem (hKL (a j).2) (hL j)⟩
  map_add' a b := by
    apply Subtype.ext
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply Subtype.ext
    simp [Algebra.smul_def, mul_assoc, Finset.mul_sum]

theorem comb_injective {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) {ι : Type} [Fintype ι]
    (ω : ι → Obar p) (hL : ∀ j, (ω j : PadicAlgCl p) ∈ L)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) :
    Function.Injective (comb hKL ω hL) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  funext i
  have h1 := norm_le_norm_sum p K ω hω a i
  have h2 : ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p) = 0 := congrArg Subtype.val ha
  rw [h2, norm_zero] at h1
  exact Subtype.ext (norm_le_zero_iff.1 h1)

noncomputable def resMod {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) :
    Submodule (resK p K) (kbar p) where
  carrier := (resK p L : Set (kbar p))
  add_mem' := fun ha hb => (resK p L).add_mem ha hb
  zero_mem' := (resK p L).zero_mem
  smul_mem' := fun c x hx => by
    rw [Subfield.smul_def, smul_eq_mul]
    exact (resK p L).mul_mem (resK_mono hKL c.2) hx

theorem exists_lifts {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ ∃ ω : Fin f → Obar p, (∀ j, (ω j : PadicAlgCl p) ∈ L) ∧
      LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i)) := by
  have hfL : Finite (resK p L) := finite_resK L hL
  have hfW : Finite (resMod hKL) := hfL
  have hMF : Module.Finite (resK p K) (resMod hKL) := Module.Finite.of_finite
  have hcard : Nat.card (resMod hKL) = Nat.card (resK p K) ^ Module.finrank (resK p K) (resMod hKL) :=
    Module.natCard_eq_pow_finrank
  have hnt : Nontrivial (resMod hKL) :=
    ⟨⟨⟨1, (resK p L).one_mem⟩, 0, fun h => one_ne_zero (congrArg Subtype.val h)⟩⟩
  refine ⟨Module.finrank (resK p K) (resMod hKL), Module.finrank_pos, hcard, ?_⟩
  let B := Module.finBasis (resK p K) (resMod hKL)
  have hex : ∀ i, ∃ x : Obar p, (x : PadicAlgCl p) ∈ L ∧ res x = (B i : kbar p) :=
    fun i => (mem_resK_iff L _).1 (B i).2
  choose ω h1 h2 using hex
  refine ⟨ω, h1, ?_⟩
  have h3 : (fun i => IsLocalRing.residue (Obar p) (ω i)) = (resMod hKL).subtype ∘ B := by
    funext i; exact h2 i
  rw [h3]
  exact B.linearIndependent.map' _ (Submodule.ker_subtype _)

theorem finrank_fun (hK : FiniteDimensional ℚ_[p] K) (f : ℕ) : Module.finrank ℚ_[p] (Fin f → K) = f * Module.finrank ℚ_[p] K := by
  rw [Module.finrank_pi_fintype]
  simp

end UnramifiedExtensions

theorem qK_le_pow_finrank (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ f * Module.finrank ℚ_[p] K ≤ Module.finrank ℚ_[p] L := by
  obtain ⟨f, hf, hq, ω, h1, h2⟩ := UnramifiedExtensions.exists_lifts hL hKL
  refine ⟨f, hf, hq, ?_⟩
  rw [← UnramifiedExtensions.finrank_fun hK]
  exact LinearMap.finrank_le_finrank_of_injective (UnramifiedExtensions.comb_injective hKL ω h1 h2)

theorem exists_norm_eq_of_qK (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hKL : K ≤ L) {f : ℕ} (hf : 0 < f) (hdeg : Module.finrank ℚ_[p] L = f * Module.finrank ℚ_[p] K)
    (h : qK p L = qK p K ^ f) {x : PadicAlgCl p} (hx : x ∈ L) : ∃ y ∈ K, ‖x‖ = ‖y‖ := by
  classical
  have hL : FiniteDimensional ℚ_[p] L := by
    apply Module.finite_of_finrank_pos
    rw [hdeg]
    exact Nat.mul_pos hf Module.finrank_pos
  obtain ⟨f', hf', hq, ω, h1, h2⟩ := UnramifiedExtensions.exists_lifts hL hKL
  have hff : f' = f := Nat.pow_right_injective (one_lt_qK p K hK) (hq.symm.trans h)
  subst hff
  have hsurj : Function.Surjective (UnramifiedExtensions.comb hKL ω h1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((UnramifiedExtensions.finrank_fun hK f').trans hdeg.symm)).1 (UnramifiedExtensions.comb_injective hKL ω h1 h2)
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  have hxa : x = ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p) := (congrArg Subtype.val ha).symm
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ‖(a j : PadicAlgCl p)‖)
    ⟨⟨0, hf⟩, Finset.mem_univ _⟩
  refine ⟨a m, (a m).2, le_antisymm ?_ ?_⟩
  · rw [hxa]
    refine UnramifiedExtensions.norm_sum_le_of_le _ _ (norm_nonneg _) fun j _ => ?_
    rw [norm_mul]
    calc ‖(a j : PadicAlgCl p)‖ * ‖(ω j : PadicAlgCl p)‖ ≤ ‖(a j : PadicAlgCl p)‖ * 1 :=
          mul_le_mul_of_nonneg_left (UnramifiedExtensions.norm_le_one _) (norm_nonneg _)
      _ ≤ ‖(a m : PadicAlgCl p)‖ := by rw [mul_one]; exact hm j (Finset.mem_univ j)
  · rw [hxa]
    exact norm_le_norm_sum p K ω h2 a m

end ReciprocityTheory.DiscreteGroups.LocalClassField
