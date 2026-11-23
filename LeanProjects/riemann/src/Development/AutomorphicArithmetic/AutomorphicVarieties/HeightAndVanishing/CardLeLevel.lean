import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem card_le_level (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N]
    (T : Finset (DirichletCharacter O N)) : T.card ≤ N := by
  classical
  have hli := linearIndependent_monoidHom (ZMod N) O
  let g : T → (ZMod N →* O) := fun χ => (χ.1 : MulChar (ZMod N) O).toMonoidHom
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply MulChar.ext'
    intro y
    have := DFunLike.congr_fun h y
    simpa [g] using this
  have hT := (hli.comp g hg).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card, Fintype.card_coe] at hT
  exact hT

theorem UpperTheory.V.HV.xCard :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N], (∀ T : Finset (DirichletCharacter O N), T.card ≤ N) ∧
      ∀ (M : ℕ), 0 < M → ∀ T : Finset (DirichletCharacter O N), (∀ ψ ∈ T, ψ.conductor ∣ M) → T.card ≤ M := by
  intro O _ _ N _
  refine ⟨card_le_level O N, ?_⟩
  intro M hM T hT
  classical
  set g := Nat.gcd M N with hgdef
  have hgN : g ∣ N := Nat.gcd_dvd_right M N
  have hgM : g ≤ M := Nat.le_of_dvd hM (Nat.gcd_dvd_left M N)
  haveI : NeZero g := ⟨(Nat.gcd_pos_of_pos_left N hM).ne'⟩
  have hex : ∀ ψ ∈ T, ∃ ψ₀ : DirichletCharacter O g, ψ = DirichletCharacter.changeLevel hgN ψ₀ := by
    intro ψ hψ
    obtain ⟨hc, χ₀, hχ₀⟩ := ψ.factorsThrough_conductor
    have hcg : ψ.conductor ∣ g := Nat.dvd_gcd (hT ψ hψ) hc
    refine ⟨DirichletCharacter.changeLevel hcg χ₀, ?_⟩
    rw [← DirichletCharacter.changeLevel_trans]
    exact hχ₀
  let f : DirichletCharacter O N → DirichletCharacter O g := fun ψ =>
    if h : ∃ ψ₀ : DirichletCharacter O g, ψ = DirichletCharacter.changeLevel hgN ψ₀ then h.choose else 1
  have hf : ∀ ψ ∈ T, ψ = DirichletCharacter.changeLevel hgN (f ψ) := by
    intro ψ hψ
    have h := hex ψ hψ
    simp only [f, dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn f T := by
    intro a ha b hb hab
    rw [hf a ha, hf b hb, hab]
  calc T.card = (T.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ g := card_le_level O g _
    _ ≤ M := hgM
