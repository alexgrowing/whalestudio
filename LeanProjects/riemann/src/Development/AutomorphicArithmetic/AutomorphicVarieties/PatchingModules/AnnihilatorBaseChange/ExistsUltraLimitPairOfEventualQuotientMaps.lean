import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.KjMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.UlimQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinCompl
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem const_bij {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (U : Ultrafilter ℕ)
    (m : Ideal R) (I : ℕ → Ideal R) (hc : IsAdicComplete m X)
    (hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)))
    (hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤) :
    Function.Bijective
      (ULim.mk (U : Filter ℕ) I (fun _ => X) ∘ₗ LinearMap.pi fun _ : ℕ => (LinearMap.id : X →ₗ[R] X)) := by
  have hb := ULim.const_bijective R ℕ U m X hc hf
  have key : ∀ p q : ℕ → X, ULim.mk (U : Filter ℕ) I (fun _ => X) p = ULim.mk (U : Filter ℕ) I (fun _ => X) q ↔
      ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) p =
        ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) q := by
    intro p q
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero, ← sub_eq_zero (a := ULim.mk _ _ _ p), ← map_sub,
      ULim.mk_eq_zero]
    simp only [hI]
  refine ⟨fun a b hab => hb.1 ((key (fun _ => a) (fun _ => b)).1 hab), fun x => ?_⟩
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
  obtain ⟨z, hz⟩ := hb.2 (ULim.mk _ _ _ p)
  exact ⟨z, (key (fun _ => z) p).2 hz⟩

private theorem comp_smul {R : Type} [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type)
    [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)]
    (ν : ℕ → ℕ) (hν : Tendsto ν F atTop) (hI : Antitone I) (f : R)
    (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))))
    (ψ : ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))))
    (h : ∀ᶠ N in F, ∀ z, ψ N (φ N z) = f • z)
    (Φ : ULim F I M →ₗ[R] ULim F I M') (Ψ : ULim F I M' →ₗ[R] ULim F I M)
    (hΦ : ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p')
    (hΨ : ∀ (p : ∀ N, M' N) (p' : ∀ N, M N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      ψ N (Submodule.Quotient.mk (p N))) → Ψ (ULim.mk F I M' p) = ULim.mk F I M p') (z : ULim F I M) :
    Ψ (Φ z) = f • z := by
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ z
  choose q hq using fun N => Submodule.Quotient.mk_surjective _ (φ N (Submodule.Quotient.mk (p N)))
  rw [hΦ p q (Eventually.of_forall hq), ← map_smul]
  refine hΨ q (f • p) (h.mono fun N hN => ?_)
  rw [hq, hN]
  rfl

theorem UpperTheory.V.Pa.Core.exists_ultraLimit_pair_of_eventual_quotient_maps :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (U : Filter ℕ) ≤ atTop → (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∃ (Φ : X →ₗ[R] ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M) (Ψ : ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M →ₗ[R] X), (∀ z, Φ (Ψ z) = f • z) ∧ ∀ z, Ψ (Φ z) = f • z := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hU hs hy h
  classical
  letI : Algebra Λ R := (s.comp MvPowerSeries.C).toAlgebra
  haveI : IsScalarTower Λ R X := IsScalarTower.of_algebraMap_smul fun a x => (hs a x).symm
  set m : Ideal R := (maximalIdeal Λ).map (s.comp MvPowerSeries.C) with hm
  set I : ℕ → Ideal R := fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ m ^ j with hIdef
  have hkj : ∀ j, (kjIdeal Λ σ 1 j).map s = I j := fun j => by rw [kjMap, pow_one]
  have h' : ∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ (I j • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I j • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I j • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I j • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro j
    rw [← hkj j]
    exact h j
  obtain ⟨ν, hν, hP⟩ := exists_diag _ hU _ h'
  have hanti : Antitone I := fun a b hab => sup_le_sup_left (Ideal.pow_le_pow_right hab) _
  have hex : ∀ N, ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro N
    by_cases hN : ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z
    · obtain ⟨φ, ψ, hh⟩ := hN
      exact ⟨φ, ψ, fun _ => hh⟩
    · exact ⟨0, 0, fun hh => absurd hh hN⟩
  choose φ ψ hφψ using hex
  have hgood := hP.mono fun N hN => hφψ N (hN _ le_rfl)
  obtain ⟨Φ, hΦ⟩ := ulimQuot R U I (fun _ => X) M ν φ hanti hν
  obtain ⟨Ψ, hΨ⟩ := ulimQuot R U I M (fun _ => X) ν ψ hanti hν
  have h1 := comp_smul U I (fun _ => X) M ν hν hanti f φ ψ (hgood.mono fun _ hN => hN.2) Φ Ψ hΦ hΨ
  have h2 := comp_smul U I M (fun _ => X) ν hν hanti f ψ φ (hgood.mono fun _ hN => hN.1) Ψ Φ hΨ hΦ
  have hc : IsAdicComplete m X :=
    (IsAdicComplete.map_algebraMap_iff (S := R) (maximalIdeal Λ) X).2 (AnnihilatorQuotientFinite.finCompl Λ X _)
  have hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)) := by
    intro j
    haveI : Finite (Λ ⧸ maximalIdeal Λ) := inferInstanceAs (Finite (ResidueField Λ))
    haveI : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
    haveI : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
      Submodule.finite_quotient_smul _ Module.Finite.fg_top
    have hle : (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X) ≤ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ := by
      refine Submodule.smul_le.2 fun a ha x _ => ?_
      rw [Submodule.restrictScalars_mem, hs]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [hm, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (s.comp MvPowerSeries.C) ha
    haveI : Finite (X ⧸ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ) :=
      Finite.of_surjective _ (Submodule.factor_surjective hle)
    exact Finite.of_equiv _ (Submodule.Quotient.restrictScalarsEquiv Λ _).toEquiv
  have hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤ := by
    intro j
    have h0 : (Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) • ⊤ : Submodule R X) = ⊥ := by
      rw [← Submodule.le_annihilator_iff, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_annihilator.2 fun x _ => hy a x
    show ((_ ⊔ _ : Ideal R) • ⊤ : Submodule R X) = _
    rw [Submodule.sup_smul, h0, bot_sup_eq]
  let e := LinearEquiv.ofBijective _ (const_bij U m I hc hf hI)
  refine ⟨Φ ∘ₗ e.toLinearMap, e.symm.toLinearMap ∘ₗ Ψ, fun z => ?_, fun z => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact h2 z
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, map_smul, LinearEquiv.symm_apply_apply]
