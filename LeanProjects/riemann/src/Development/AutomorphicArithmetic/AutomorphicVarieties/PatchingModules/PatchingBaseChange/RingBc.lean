import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilCo
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ResidBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.FreeBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem lamEmb_X (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (D : ℕ) (k : Fin D) :
    lamEmb O O' D (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (.inr k) := by
  simp [lamEmb]

theorem UpperTheory.V.Pa.BC.ring_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (b' : TWBase u' (J.map (Til.ι O O' B)) Unit D) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) (G : Glob l L) (h : G.Hom G0) (q : ℕ) (ut : Fin q → Fin n → O) (N : ℕ) (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) (A : TWRing b h ut N), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → Nonempty (BaseRel b b' τ) → SinfRel l τ τS → ∃ A' : TWRing b' h (fun j i => algebraMap O O' (ut j i)) N, Nonempty (RingRel A A' τS) := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D b b' τ G h q ut N τS A hr _ ⟨hb⟩ hS
  obtain ⟨rN', hN⟩ := (resid_bc l G.frame O O' n A.rN).1
  obtain ⟨hco, hloc, -⟩ := til_co O O' A.R
  obtain ⟨-, p', hp⟩ := pair_bc l G.frame O O' n A.rN rN' hN A.R (Til O O' A.R) (Til.ι O O' A.R)
    (Til.ι_algebraMap O O' A.R) A.p
  obtain ⟨e', he'⟩ := free_bc O O' (Sinf O Empty D q n) A.R A.s A.M _ A.rk A.e A.e_smul
    (Sinf O' Unit D q n) τS.toRingEquiv _ (hS.del A.a)
  have hc : Glob.Compat h rN' r' := by
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [hN.1, hr.1, A.compat.1]
      rfl
    · funext v i
      rw [hN.2.1, hr.2.1, A.compat.2.1]
    · funext v i
      rw [hN.2.2, hr.2.2, A.compat.2.2]
      rfl
  refine ⟨{ rN := rN', compat := hc, R := Til O O' A.R, p := p'
            s := (Til.map O' A.s).comp τS.symm.toAlgHom
            s_w := fun k => ?_
            U := fun j i => Til.ι O O' A.R (A.U j i)
            U_res := fun j i => ?_
            M := Til O O' A.R ⊗[A.R] A.M
            a := A.a, le_a := A.le_a, rk := A.rk, e := e'
            e_smul := fun z m => ?_ },
    ⟨{ ρ := AlgEquiv.refl, maps := hp, s := fun z => ?_, U := fun _ _ => rfl, ν := AddEquiv.refl _
       ν_smul := fun _ _ => rfl }⟩⟩
  · rw [← lamEmb_X O O' D k, ← hS.C, hb.wt, ← hp.2]
    change Til.map O' A.s (τS.symm (τS _)) = _
    rw [AlgEquiv.symm_apply_apply, Til.map_ι, A.s_w, map_sub, map_mul, map_one, Til.ι_algebraMap]
    rfl
  · rw [← Til.ι_algebraMap, ← map_sub]
    exact fun hu => A.U_res j i (IsLocalHom.map_nonunit _ hu)
  · have := he' (τS.symm z) m
    rw [show τS.toRingEquiv (τS.symm z) = z from τS.apply_symm_apply z] at this
    exact this
  · change Til.map O' A.s (τS.symm (τS z)) = Til.map O' A.s z
    rw [AlgEquiv.symm_apply_apply]
