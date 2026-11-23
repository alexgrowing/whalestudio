import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

private theorem sep_char {A : Type} [AddCommGroup A] (H : AddSubgroup A) {a : A} (ha : a ∉ H) :
    ∃ ψ : AddChar A Circle, (∀ u ∈ H, ψ u = 1) ∧ ψ a ≠ 1 := by
  have hne : (a : A ⧸ H) ≠ 0 := fun h => ha ((QuotientAddGroup.eq_zero_iff _).1 h)
  obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let e : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      rintro _ ⟨m, rfl⟩
      exact ⟨m, by simp⟩)
  have he : ∀ b, e b = 0 → b = 0 := by
    intro b
    induction b using QuotientAddGroup.induction_on with
    | H q =>
      intro h
      have h1 : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
      rw [AddCircle.coe_eq_zero_iff] at h1 ⊢
      obtain ⟨m, hm⟩ := h1
      refine ⟨m, ?_⟩
      have h2 : ((m : ℚ) : ℝ) = q := by simpa using hm
      have h3 : (m : ℚ) = q := by exact_mod_cast h2
      simpa using h3
  let f : A →+ AddCircle (1 : ℝ) := e.comp (AddMonoidHom.comp (χ : A ⧸ H →+ AddCircle (1 : ℚ)) (QuotientAddGroup.mk' H))
  let ψ : AddChar A Circle :=
    { toFun := fun x => AddCircle.toCircle (f x)
      map_zero_eq_one' := by rw [map_zero, AddCircle.toCircle_zero]
      map_add_eq_mul' := fun x y => by rw [map_add, AddCircle.toCircle_add] }
  refine ⟨ψ, fun u hu => ?_, fun h => ?_⟩
  · have h0 : f u = 0 := by
      have : QuotientAddGroup.mk' H u = 0 := (QuotientAddGroup.eq_zero_iff _).2 hu
      show e (χ (QuotientAddGroup.mk' H u)) = 0
      rw [this, map_zero, map_zero]
    show AddCircle.toCircle (f u) = 1
    rw [h0, AddCircle.toCircle_zero]
  · have h2 : AddCircle.toCircle (f a) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h
    exact hχ (he _ (AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero h2))

private theorem cont_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    (H : AddSubgroup A) (hH : IsOpen (H : Set A)) (ψ : AddChar A Circle) (h : ∀ u ∈ H, ψ u = 1) :
    Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => y - x) ⁻¹' (H : Set A), hH.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
  · simp [H.zero_mem]
  · intro y hy
    have h1 : ψ (y - x) = 1 := h _ hy
    have h2 : y = (y - x) + x := by abel
    rw [h2, AddChar.map_add_eq_mul, h1, one_mul]

theorem UpperTheory.exists_level_one_addChar_lifting_residue :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
        ∃ (ψ : AddChar k Circle) (φ : AddChar 𝓀[k] Circle), Lev1 ψ ∧ φ ≠ 1 ∧ ∀ y : 𝒪[k], ψ (y : k) = φ (IsLocalRing.residue 𝒪[k] y) := by
  intro k _ _ _ _
  let M : AddSubgroup k :=
    { carrier := {x | valuation k x < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => lt_of_le_of_lt ((valuation k).map_add a b) (max_lt ha hb)
      neg_mem' := fun {a} ha => by
        show valuation k (-a) < 1
        rw [Valuation.map_neg]; exact ha }
  have hMo : IsOpen (M : Set k) := by
    have h := IsValuativeTopology.isOpen_ball (R := k) (v := valuation k) 1
    convert h using 1
    ext x
    exact ((valuation k).restrict_lt_one_iff (x := x)).symm
  have h1M : (1 : k) ∉ M := by
    intro h
    have h' : valuation k (1 : k) < 1 := h
    simp at h'
  obtain ⟨ψ, hψM, hψ1⟩ := sep_char M h1M
  have hres : ∀ y z : 𝒪[k], IsLocalRing.residue 𝒪[k] y = IsLocalRing.residue 𝒪[k] z → ψ (y : k) = ψ (z : k) := by
    intro y z h
    have h0 : IsLocalRing.residue 𝒪[k] (y - z) = 0 := by rw [map_sub, h, sub_self]
    have h1 : ψ ((y - z : 𝒪[k]) : k) = 1 := hψM _ ((GlobalTheory.StepData.residue_eq_zero_iff_lt _).1 h0)
    have h2 : (y : k) = ((y - z : 𝒪[k]) : k) + (z : k) := by push_cast; abel
    rw [h2, AddChar.map_add_eq_mul, h1, one_mul]
  have hsurj := IsLocalRing.residue_surjective (R := 𝒪[k])
  let σ : 𝓀[k] → 𝒪[k] := Function.surjInv hsurj
  have hσ : ∀ c, IsLocalRing.residue 𝒪[k] (σ c) = c := Function.surjInv_eq hsurj
  let φ : AddChar 𝓀[k] Circle :=
    { toFun := fun c => ψ (σ c : k)
      map_zero_eq_one' := by
        have : ψ (σ 0 : k) = ψ ((0 : 𝒪[k]) : k) := hres _ _ (by rw [hσ, map_zero])
        rw [this]; simp
      map_add_eq_mul' := fun c d => by
        have : ψ (σ (c + d) : k) = ψ ((σ c + σ d : 𝒪[k]) : k) := hres _ _ (by rw [hσ, map_add, hσ, hσ])
        rw [this]; push_cast; rw [AddChar.map_add_eq_mul] }
  have hφ : ∀ y : 𝒪[k], ψ (y : k) = φ (IsLocalRing.residue 𝒪[k] y) := fun y =>
    hres _ _ (hσ _).symm
  refine ⟨ψ, φ, ⟨cont_char M hMo ψ hψM, hψM, 1, by simp, hψ1⟩, fun h => hψ1 ?_, hφ⟩
  have h2 := hφ 1
  rw [h] at h2
  simpa using h2
