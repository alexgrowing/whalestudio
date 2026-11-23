import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsEqFinsumConjClasses

open MulAction

namespace GlobalTheory.OrbitUnfold

section Restrict

variable {G Y Y' : Type} [Group G] [MulAction G Y] [MulAction G Y']

theorem out_mk_mem_orbit (x : Y) :
    Quotient.out (Quotient.mk (orbitRel G Y) x) ∈ orbit G x :=
  orbitRel_apply.mp (Quotient.mk_out (s := orbitRel G Y) x)

theorem injective_mk_comp_out (i : Y' → Y) (hi : Function.Injective i)
    (heq : ∀ (η : G) (y : Y'), i (η • y) = η • i y) :
    Function.Injective (fun o : orbitRel.Quotient G Y' =>
      (Quotient.mk (orbitRel G Y) (i (Quotient.out o)) : orbitRel.Quotient G Y)) := by
  intro o₁ o₂ h
  have h' : i (Quotient.out o₁) ∈ orbit G (i (Quotient.out o₂)) :=
    orbitRel_apply.mp (Quotient.exact h)
  obtain ⟨η, hη⟩ := h'
  simp only at hη
  rw [← heq] at hη
  have h2 := hi hη
  rw [← Quotient.out_eq o₁, ← Quotient.out_eq o₂]
  exact Quotient.sound (orbitRel_apply.mpr ⟨η, h2⟩)

theorem finsum_orbits_restrict (i : Y' → Y) (hi : Function.Injective i)
    (heq : ∀ (η : G) (y : Y'), i (η • y) = η • i y) (g : Y → ℂ) (g' : Y' → ℂ)
    (hgg : ∀ y, g' y = g (i y)) (hg : ∀ (η : G) (y : Y), g (η • y) = g y)
    (h0 : ∀ y, g y ≠ 0 → y ∈ Set.range i) :
    ∑ᶠ o : orbitRel.Quotient G Y, g (Quotient.out o) =
      ∑ᶠ o : orbitRel.Quotient G Y', g' (Quotient.out o) := by
  have hgo : ∀ x : Y, g (Quotient.out (Quotient.mk (orbitRel G Y) x)) = g x := by
    intro x
    obtain ⟨η, hη⟩ := out_mk_mem_orbit (G := G) x
    simp only at hη
    rw [← hη, hg]
  have hφ := injective_mk_comp_out i hi heq
  have hsupp : Function.support (fun o : orbitRel.Quotient G Y => g (Quotient.out o)) ⊆
      Set.range (fun o : orbitRel.Quotient G Y' =>
        (Quotient.mk (orbitRel G Y) (i (Quotient.out o)) : orbitRel.Quotient G Y)) := by
    intro o ho
    obtain ⟨y, hy⟩ := h0 _ ho
    refine ⟨Quotient.mk (orbitRel G Y') y, ?_⟩
    obtain ⟨η, hη⟩ := out_mk_mem_orbit (G := G) y
    simp only at hη
    show Quotient.mk (orbitRel G Y) (i (Quotient.out (Quotient.mk (orbitRel G Y') y))) = o
    rw [← hη, heq, hy]
    conv_rhs => rw [← Quotient.out_eq o]
    exact Quotient.sound (orbitRel_apply.mpr (mem_orbit _ _))
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ _
    (fun x hx => ⟨fun _ => hsupp hx, fun _ => trivial⟩), finsum_mem_range hφ]
  exact finsum_congr fun o => by rw [hgo, hgg]

end Restrict

section Stab

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

def finiteStabilizerSubMulAction (Γ Y : Type) [Group Γ] [MulAction Γ Y] : SubMulAction Γ Y where
  carrier := {y | (stabilizer Γ y : Set Γ).Finite}
  smul_mem' η y hy := by
    show (stabilizer Γ (η • y) : Set Γ).Finite
    rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.coe_map]
    exact Set.Finite.image _ hy

theorem mem_stabilizer_conj_iff (η x : Γ) (y : Y) :
    x ∈ stabilizer Γ y ↔ η * x * η⁻¹ ∈ stabilizer Γ (η • y) := by
  simp only [mem_stabilizer_iff, mul_smul, inv_smul_smul]
  exact (smul_left_cancel_iff η).symm

theorem natCard_stabilizer_inf_smul (K : Subgroup Γ) (η : Γ) (hK : ∀ x, x ∈ K ↔ η * x * η⁻¹ ∈ K)
    (y : Y) : Nat.card (stabilizer Γ (η • y) ⊓ K : Subgroup Γ) = Nat.card (stabilizer Γ y ⊓ K : Subgroup Γ) := by
  symm
  refine Nat.card_congr ((MulAut.conj η).toEquiv.subtypeEquiv fun x => ?_)
  simp only [Subgroup.mem_inf, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [mem_stabilizer_conj_iff η x y, hK x]

theorem natCard_stabilizer_smul (η : Γ) (y : Y) :
    Nat.card (stabilizer Γ (η • y)) = Nat.card (stabilizer Γ y) := by
  symm
  refine Nat.card_congr ((MulAut.conj η).toEquiv.subtypeEquiv fun x => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  exact mem_stabilizer_conj_iff η x y

theorem mem_iff_conj_mem (K : Subgroup Γ) {η : Γ} (hη : η ∈ K) (x : Γ) :
    x ∈ K ↔ η * x * η⁻¹ ∈ K := by
  constructor
  · intro h; exact K.mul_mem (K.mul_mem hη h) (K.inv_mem hη)
  · intro h
    have := K.mul_mem (K.mul_mem (K.inv_mem hη) h) hη
    simpa [mul_assoc] using this

theorem stabilizer_inf_centralizer_infinite (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (y : Y)
    (hs : (Function.support (F y)).Finite) (c : Γ) (hc : F y c ≠ 0)
    (hinf : (stabilizer Γ y : Set Γ).Infinite) :
    ((stabilizer Γ y ⊓ Subgroup.centralizer {c} : Subgroup Γ) : Set Γ).Infinite := by
  haveI : Infinite (stabilizer Γ y) := hinf.to_subtype
  haveI : Finite (Function.support (F y)) := hs.to_subtype
  let f : stabilizer Γ y → Function.support (F y) := fun η =>
    ⟨(η : Γ) * c * (η : Γ)⁻¹, by
      show F y _ ≠ 0
      have h1 : (η : Γ) • y = y := η.2
      have := hF η y c
      rw [h1] at this
      rw [this]; exact hc⟩
  obtain ⟨z, hz⟩ := Finite.exists_infinite_fiber f
  obtain ⟨⟨η₀, hη₀⟩⟩ : Nonempty ↑(f ⁻¹' {z}) := inferInstance
  refine Set.infinite_of_injective_forall_mem (α := ↑(f ⁻¹' {z}))
    (f := fun η => (η₀ : Γ)⁻¹ * ((η : stabilizer Γ y) : Γ)) ?_ ?_
  · intro a b hab
    have : ((a : stabilizer Γ y) : Γ) = ((b : stabilizer Γ y) : Γ) := mul_left_cancel hab
    exact Subtype.ext (Subtype.ext this)
  · intro ⟨η, hη⟩
    have E : (η : Γ) * c * (η : Γ)⁻¹ = (η₀ : Γ) * c * (η₀ : Γ)⁻¹ := by
      have h1 : f η = z := hη
      have h2 : f η₀ = z := hη₀
      have := congrArg Subtype.val (h1.trans h2.symm)
      exact this
    refine Subgroup.mem_inf.mpr ⟨(stabilizer Γ y).mul_mem ((stabilizer Γ y).inv_mem η₀.2) η.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h2 : (η₀ : Γ)⁻¹ * ((η : Γ) * h * (η : Γ)⁻¹) * η = (η₀ : Γ)⁻¹ * ((η₀ : Γ) * h * (η₀ : Γ)⁻¹) * η := by
      rw [E]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h2
    simp only [mul_assoc]
    exact h2.symm

end Stab

theorem finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  intro Γ Y _ _ F hF hs ho
  let S := finiteStabilizerSubMulAction Γ Y
  have hstabS : ∀ y : S, stabilizer Γ y = stabilizer Γ (y : Y) := fun y =>
    SubMulAction.stabilizer_of_subMul y
  have hF' : ∀ (η : Γ) (y : S) (γ : Γ), F ((η • y : S) : Y) (η * γ * η⁻¹) = F (y : Y) γ :=
    fun η y γ => hF η y γ
  have hst' : ∀ y : S, (stabilizer Γ y : Set Γ).Finite := fun y => by rw [hstabS]; exact y.2
  have hs' : ∀ y : S, (Function.support (fun γ => F (y : Y) γ)).Finite := fun y => hs y
  have ho' : {o : orbitRel.Quotient Γ S | ∃ γ, F ((Quotient.out o : S) : Y) γ ≠ 0}.Finite := by
    have hφ := injective_mk_comp_out (G := Γ) (Y := Y) (Y' := S) Subtype.val
      Subtype.val_injective (fun _ _ => rfl)
    refine (ho.preimage hφ.injOn).subset ?_
    rintro o ⟨γ, hγ⟩
    obtain ⟨η, hη⟩ := out_mk_mem_orbit (G := Γ) ((Quotient.out o : S) : Y)
    simp only at hη
    refine ⟨η * γ * η⁻¹, ?_⟩
    show F (Quotient.out (Quotient.mk (orbitRel Γ Y) ((Quotient.out o : S) : Y))) (η * γ * η⁻¹) ≠ 0
    rw [← hη, hF]; exact hγ
  have key := finsum_orbits_eq_finsum_conjClasses (fun (y : S) γ => F (y : Y) γ) hF' hst' hs' ho'
  refine Eq.trans ?_ (key.trans (finsum_congr fun c => ?_))
  · refine finsum_orbits_restrict (G := Γ) Subtype.val Subtype.val_injective (fun _ _ => rfl)
      (fun y => ((Nat.card (stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F y γ)
      (fun y : S => ((Nat.card (stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (y : Y) γ)
      (fun y => by simp only [hstabS]) (fun η y => ?_) (fun y hy => ?_)
    · simp only [natCard_stabilizer_smul]
      congr 1
      rw [← finsum_comp_equiv (MulAut.conj η).toEquiv]
      refine finsum_congr fun γ => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      exact hF η y γ
    · by_contra hn
      apply hy
      have hinf : ¬ (stabilizer Γ y : Set Γ).Finite := fun h => hn ⟨⟨y, h⟩, rfl⟩
      haveI : Infinite (stabilizer Γ y) := Set.Infinite.to_subtype hinf
      rw [Nat.card_eq_zero_of_infinite (α := stabilizer Γ y), Nat.cast_zero, inv_zero, zero_mul]
  · set c' := Quotient.out c
    refine (finsum_orbits_restrict (G := Subgroup.centralizer {c'}) (Y := Y) (Y' := S)
      Subtype.val Subtype.val_injective (fun _ _ => rfl)
      (fun y => ((Nat.card (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y c')
      (fun y : S => ((Nat.card (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
        F (y : Y) c')
      (fun y => by simp only [hstabS]) (fun η y => ?_) (fun y hy => ?_)).symm
    · have hc : (η : Γ) * c' * (η : Γ)⁻¹ = c' := by
        have := Subgroup.mem_centralizer_iff.mp η.2 c' (Set.mem_singleton _)
        rw [← this, mul_inv_cancel_right]
      have hFc := hF η y c'
      rw [hc] at hFc
      simp only [Subgroup.smul_def]
      rw [natCard_stabilizer_inf_smul _ (η : Γ) (mem_iff_conj_mem _ η.2) y, hFc]
    · by_contra hn
      apply hy
      have hinf : ¬ (stabilizer Γ y : Set Γ).Finite := fun h => hn ⟨⟨y, h⟩, rfl⟩
      by_cases hc : F y c' = 0
      · simp [hc]
      have hI := stabilizer_inf_centralizer_infinite F hF y (hs y) c' hc hinf
      have h0 : Nat.card (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) = 0 := by
        haveI : Infinite (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) := hI.to_subtype
        exact Nat.card_eq_zero_of_infinite
      rw [h0, Nat.cast_zero, inv_zero, zero_mul]

end GlobalTheory.OrbitUnfold
