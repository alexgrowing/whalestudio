import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.U3

section Quot

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}

private theorem glift_map_map {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R']
    [IsCO O R'] [CommRing R''] [Algebra O R''] [IsCO O R''] (r : GLift O η Ψ R) (f : R →ₐ[O] R')
    (f' : R' →ₐ[O] R'') : (r.map f).map f' = r.map (f'.comp f) := GLift.ext rfl

private theorem univ_quot {P Q : GCond O η Ψ} (V : Univ P) (J : Ideal V.R)
    (hQP : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R), Q R r → P R r)
    (hJ : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (f : V.R →ₐ[O] R),
      Q R (V.r.map f) ↔ J ≤ RingHom.ker f)
    {R₀ : Type} [CommRing R₀] [Algebra O R₀] [IsCO O R₀] (r₀ : GLift O η Ψ R₀) (h₀ : Q R₀ r₀) :
    Nonempty (Univ Q) := by
  obtain ⟨f₀, hf₀, -⟩ := (V.rep R₀).2 r₀ (hQP _ _ h₀)
  have hle : J ≤ RingHom.ker f₀ := (hJ R₀ f₀).1 (hf₀ ▸ h₀)
  have hne : J ≠ ⊤ := fun h => RingHom.ker_ne_top f₀ (top_le_iff.1 (h ▸ hle))
  haveI : Nontrivial (V.R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsCO O (V.R ⧸ J) :=
    co_quot O V.R (V.R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  refine ⟨⟨V.R ⧸ J, V.r.map (Ideal.Quotient.mkₐ O J), fun R' _ _ _ => ⟨fun f => ?_, fun r' hr' => ?_⟩⟩⟩
  · rw [glift_map_map, hJ]
    intro y hy
    show f (Ideal.Quotient.mk J y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero]
  · obtain ⟨f, hf, hu⟩ := (V.rep R').2 r' (hQP _ _ hr')
    have hk : J ≤ RingHom.ker f := (hJ R' f).1 (hf ▸ hr')
    have hc : (Ideal.Quotient.liftₐ J f hk).comp (Ideal.Quotient.mkₐ O J) = f := AlgHom.ext fun _ => rfl
    refine ⟨Ideal.Quotient.liftₐ J f hk, ?_, fun g hg => ?_⟩
    · show (V.r.map _).map _ = r'
      rw [glift_map_map, hc, hf]
    · have hg' : g.comp (Ideal.Quotient.mkₐ O J) = f := hu _ ((glift_map_map V.r _ g).symm.trans hg)
      exact Ideal.Quotient.algHom_ext O (hg'.trans hc.symm)

private theorem univ_norm {P : GCond O η Ψ} (V : Univ P) (c g₁ : Γ)
    {R₀ : Type} [CommRing R₀] [Algebra O R₀] [IsCO O R₀] (r₀ : GLift O η Ψ R₀) (h₀ : NormCond c g₁ P R₀ r₀) :
    Nonempty (Univ (NormCond c g₁ P)) := by
  refine univ_quot V (Ideal.span ({x | ∃ a b, x = ((V.r.hom c).mat - 1) a b} ∪
    {zmat c g₁ V.r.hom 0 1, zmat c g₁ V.r.hom 1 0})) (fun _ _ _ _ _ h => h.2) (fun R _ _ _ f => ?_) r₀ h₀
  have hz : ∀ a b, zmat c g₁ (V.r.map f).hom a b = f (zmat c g₁ V.r.hom a b) := fun a b => by
    simp only [zmat, Matrix.sub_apply, map_sub]
    rfl
  have hc : ∀ a b, (((V.r.map f).hom c).mat - 1) a b = f (((V.r.hom c).mat - 1) a b) := fun a b => by
    simp only [Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite f, map_one, map_zero]
    rfl
  rw [Ideal.span_le]
  constructor
  · rintro ⟨hn, -⟩ x hx
    show f x = 0
    rcases hx with ⟨a, b, rfl⟩ | rfl | rfl
    · rw [← hc, hn.atc, sub_self, Matrix.zero_apply]
    · rw [← hz, hn.z12]
    · rw [← hz, hn.z21]
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, (V.rep R).1 f⟩
    · rw [← sub_eq_zero]
      ext a b
      rw [hc]
      exact h (Or.inl ⟨a, b, rfl⟩)
    · rw [hz]
      exact h (Or.inr (Or.inl rfl))
    · rw [hz]
      exact h (Or.inr (Or.inr rfl))

private theorem univ_box {H : Type} [Group H] [TopologicalSpace H] {N : Set Γ} {ι : H →* Γ} (hι : Continuous ι)
    (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R)
    (V : Univ (Kills (O := O) (η := η) (Ψ := Ψ) N))
    {R₀ : Type} [CommRing R₀] [Algebra O R₀] [IsCO O R₀] (r₀ : GLift O η Ψ R₀) (h₀ : BoxCond N ι hι U I R₀ r₀) :
    Nonempty (Univ (BoxCond N ι hι U I)) := by
  obtain ⟨φ, hφ, -⟩ := (U.rep V.R).2 (V.r.comap ι hι) trivial
  refine univ_quot V (I.map φ) (fun _ _ _ _ _ h => h.1) (fun R _ _ _ f => ?_) r₀ h₀
  have hf : U.r.map (f.comp φ) = (V.r.map f).comap ι hι := by
    rw [← glift_map_map, hφ]
    exact GLift.ext rfl
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · rintro ⟨-, f', hf', hI⟩
    obtain ⟨g, -, hu⟩ := (U.rep R).2 ((V.r.map f).comap ι hι) trivial
    have e : f' = f.comp φ := (hu f' hf').trans (hu _ hf).symm
    subst e
    exact fun y hy => hI hy
  · exact fun h => ⟨(V.rep R).1 f, f.comp φ, hf, fun y hy => h hy⟩

end Quot

end UpperTheory.V.U3

theorem UpperTheory.V.U3.exists_sRing :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
      {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} (hι : Continuous ι)
      (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R) (cc g₁ : Γ), Marks η Ψ cc g₁ → LocGood U I →
      (∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) → (∀ g ∈ N, r0 η Ψ g = 1) →
      Nonempty (Univ (Kills (O := O) (η := η) (Ψ := Ψ) N)) →
      Nonempty (Univ (BoxCond N ι hι U I)) ∧ Nonempty (SRing N hι U I cc g₁) := by
  intro O _ _ _ _ _ Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ hM hL hΨ hN ⟨V⟩
  obtain ⟨x, τ, _, w, φ, hx, hφ, -⟩ := hL.chart
  have h₀ : BoxCond N ι hι U I O (baseLift O η Ψ hΨ) := by
    refine ⟨hN, x, GLift.ext hx, fun y hy => ?_⟩
    have h1 : φ y = 0 := by
      rw [← hφ.ker] at hy
      exact hy
    have h2 := hφ.const y
    rw [h1, map_zero] at h2
    exact IsFractionRing.injective O (FractionRing O) (h2.symm.trans (map_zero _).symm)
  obtain ⟨B⟩ := univ_box hι U I V _ h₀
  exact ⟨⟨B⟩, univ_norm B cc g₁ (baseLift O η Ψ hΨ) ⟨baseRepGL3_normalised_of_psi_eq_one η Ψ g₁ hM.Ψc, h₀⟩⟩
