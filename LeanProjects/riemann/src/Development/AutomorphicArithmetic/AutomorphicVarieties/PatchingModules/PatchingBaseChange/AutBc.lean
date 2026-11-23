import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.BaseBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.RingBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.MapsBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.aut_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (T : TWGrp G0) (_A : TWAut u J Empty D T), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → ∃ A' : TWAut u' (J.map (Til.ι O O' B)) Unit D T, A'.b.lam (MvPowerSeries.X (.inl ())) = Til.s O O' B := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D T A hr hu
  obtain ⟨τ, hτ, hs⟩ := UpperTheory.V.Pa.BC.til_lam O O' D
  obtain ⟨τS, hS⟩ := UpperTheory.V.Pa.BC.sinf_iso l O O' D T.q n τ hτ
  obtain ⟨b', hb⟩ := UpperTheory.V.Pa.BC.base_bc l L G0 n O O' r r' B u u' J D A.b τ hr hu hτ
  have hA := fun N => UpperTheory.V.Pa.BC.ring_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) hr hu hb hS
  choose A' hA' using hA
  have hm := fun N => UpperTheory.V.Pa.BC.maps_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) (A' N) (T.Nq N) (T.ph N) (T.ta N) A.ex (A.m N) hr hu hb hS (hA' N)
  refine ⟨⟨b', fun j i => algebraMap O O' (A.ut j i), ?_, A', A.ex, fun N => (hm N).some⟩, ?_⟩
  · intro j i
    rw [hr.1 i, ← ResidueField.map_residue, A.ut_res]
    rfl
  · obtain ⟨hb⟩ := hb
    show b'.lam _ = _
    rw [← hs, hb.lam, Til.map_s]
