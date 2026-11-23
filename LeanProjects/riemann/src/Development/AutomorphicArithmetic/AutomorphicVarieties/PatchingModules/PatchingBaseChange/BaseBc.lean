import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaSuppBc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinOfHom
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem free_fin_transfer {S T N N' : Type} [CommRing S] [CommRing T] [AddCommGroup N] [AddCommGroup N']
    [Module S N] [Module T N'] [Module.Free S N] [Module.Finite S N] (τ : S ≃+* T) (e : N ≃+ N')
    (he : ∀ a z, e (a • z) = τ a • e z) : Module.Free T N' ∧ Module.Finite T N' := by
  letI : Module S N' := Module.compHom N' (τ : S →+* T)
  let e' : N ≃ₗ[S] N' := { e with map_smul' := he }
  haveI : Module.Free S N' := Module.Free.of_equiv e'
  haveI : Module.Finite S N' := Module.Finite.equiv e'
  refine ⟨Module.Free.of_basis ((Module.Free.chooseBasis S N').mapCoeffs τ (fun _ _ => rfl)), ?_⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := N')
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span S (s : Set N') := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ (hy trivial) (hz trivial)
  | smul a y _ hy => exact Submodule.smul_mem _ (τ a) (hy trivial)

private theorem fin_of_hom {S R M : Type} [CommRing S] [CommRing R] [AddCommGroup M] [Module S M] [Module R M]
    [Module.Finite S M] (f : S → R) (h : ∀ (a : S) (m : M), a • m = f a • m) : Module.Finite R M :=
  _root_.UpperTheory.Reformulated.B.Qh10.fin_of_hom f h

private theorem lamEmb_X (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (D : ℕ) (k : Fin D) :
    lamEmb O O' D (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (.inr k) := by
  simp [lamEmb]

theorem UpperTheory.V.Pa.BC.base_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) → ∃ b' : TWBase u' (J.map (Til.ι O O' B)) Unit D, Nonempty (BaseRel b b' τ) := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D b τ hr hu hτ
  haveI := b.free
  haveI := b.fin
  haveI : IsNoetherianRing (abelian₂ O Empty D) := inferInstance
  haveI : Module.Finite B b.M := fin_of_hom b.lam b.smul_lam
  obtain ⟨e, -, he⟩ := UpperTheory.V.Pa.BC.til_mod O O' (abelian₂ O Empty D) B b.lam b.M b.smul_lam
  let lam' : abelian₂ O' Unit D →ₐ[O'] Til O O' B := (Til.map O' b.lam).comp (τ.symm : abelian₂ O' Unit D →ₐ[O'] _)
  have hlam : ∀ a, lam' (τ a) = Til.map O' b.lam a := fun a => by simp [lam']
  letI mL : Module (abelian₂ O' Unit D) (Til O O' B ⊗[B] b.M) := Module.compHom _ (lam' : abelian₂ O' Unit D →+* Til O O' B)
  have hff := free_fin_transfer (T := abelian₂ O' Unit D) (N' := Til O O' B ⊗[B] b.M) τ.toRingEquiv e (fun a z => by
    rw [he, ← hlam]; rfl)
  refine ⟨{ wt := ⟨b.wt.v, b.wt.i, b.wt.γ, fun k => algebraMap O O' (b.wt.c k)⟩
            wt_res := ?_
            lam := lam'
            segmentWeightExponent := ?_
            M := Til O O' B ⊗[B] b.M
            smul_lam := fun _ _ => rfl
            free := hff.1
            fin := hff.2
            supp := ?_ }, ⟨⟨rfl, hlam, LinearEquiv.refl _ _⟩⟩⟩
  · intro k
    have h := congrArg (ResidueField.map (algebraMap O O')) (b.wt_res k)
    rw [map_mul, map_one, ResidueField.map_residue] at h
    dsimp only
    rw [hr.2.1]
    exact h
  · intro k
    dsimp only
    rw [← lamEmb_X O O' D k, ← hτ, hlam, Til.map_ι, b.segmentWeightExponent, map_sub, map_mul, map_one, Til.ι_algebraMap, ← hu.2]
    rfl
  · intro p hp
    have h1 := UpperTheory.V.AlgebraTools.mem_support_baseChange B (Til O O' B) b.M ⟨p, hp⟩
    rw [Module.mem_support_iff_of_finite, Module.mem_support_iff_of_finite] at h1
    rw [Ideal.map_le_iff_le_comap, ← b.supp _ (Ideal.comap_isPrime _ _)]
    exact h1
