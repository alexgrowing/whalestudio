import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.TensTorsion
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.QuotientsEquivOfKerEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.GroupHomologyLongExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.ImageRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermCard

noncomputable section

open CategoryTheory

namespace UpperTheory.FiniteGenerationAndTorsion

open UpperTheory.V.KH

private theorem fgOfFin (N : Type) [AddCommGroup N] [i : Module ℤ N] (h : Module.Finite ℤ N) :
    AddGroup.FG N := by
  obtain rfl : i = AddCommGroup.toIntModule N := Subsingleton.elim _ _
  exact Module.Finite.iff_addGroup_fg.1 h

private theorem finOfFg (N : Type) [AddCommGroup N] [i : Module ℤ N] (h : AddGroup.FG N) :
    Module.Finite ℤ N := by
  obtain rfl : i = AddCommGroup.toIntModule N := Subsingleton.elim _ _
  exact Module.Finite.iff_addGroup_fg.2 h

private theorem fgStep {P N Q : Type} [AddCommGroup P] [AddCommGroup N] [AddCommGroup Q]
    (u : P →+ N) (v : N →+ Q) (h : Function.Exact u v) [Finite P] (hQ : AddGroup.FG Q) :
    AddGroup.FG N := by
  have : Module.Finite ℤ Q := Module.Finite.iff_addGroup_fg.2 hQ
  have : Module.Finite ℤ P := Module.Finite.of_finite
  have hr : LinearMap.range u.toIntLinearMap = LinearMap.ker v.toIntLinearMap := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (h x).symm
  have : IsNoetherian ℤ N := isNoetherian_of_range_eq_ker _ _ hr
  exact Module.Finite.iff_addGroup_fg.1 inferInstance

private theorem fgBase (G : Type) [Group G] (X Y : Type) [MulAction G X] (A : ℕ) (M : Rep ℤ G)
    (e : permRep G X ⟶ M) (D : (Y →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ)) (he : Function.Surjective e.hom)
    (hex : Function.Exact D e.hom) (ho : OrbLe G X A) :
    AddGroup.FG (groupHomology M 0) := by
  have := ho.1
  obtain ⟨φ⟩ := hZero G X M e (LinearMap.range D : Set (X →₀ ℤ)) he (fun f => by
    rw [Submodule.span_eq, LinearMap.mem_range]
    exact hex f)
  have hf := fgOfFin _ (inferInstance : Module.Finite ℤ ((MulAction.orbitRel.Quotient G X →₀ ℤ) ⧸
    Submodule.span ℤ (Finsupp.mapDomain
      (Quotient.mk (MulAction.orbitRel G X) : X → MulAction.orbitRel.Quotient G X) ''
        (LinearMap.range D : Set (X →₀ ℤ)))))
  exact AddGroup.fg_of_surjective (f := φ.symm.toAddMonoidHom) φ.symm.surjective

private theorem fg_homology_of_permutation_resolution (G : Type) [Group G] (A s : ℕ) (hs : 1 ≤ s) (m : ℕ) :
    ∀ (X : ℕ → Type) [∀ p, MulAction G (X p)]
      (d : ∀ p, permRep G (X (p + 1)) ⟶ permRep G (X p)) (M : Rep ℤ G) (e : permRep G (X 0) ⟶ M),
      Function.Surjective e.hom → Function.Exact (d 0).hom e.hom →
      (∀ p, p < m → Function.Exact (d (p + 1)).hom (d p).hom) →
      (∀ p, p ≤ m → OrbLe G (X p) A) → (∀ p, p ≤ m → StabLe G (X p) s) →
      AddGroup.FG (groupHomology M m) := by
  induction m with
  | zero =>
    intro X _ d M e he h0 _ ho _
    exact fgBase G (X 0) (X 1) A M e (d 0).hom.toLinearMap he h0 (ho 0 le_rfl)
  | succ m ih =>
    intro X _ d M e he h0 hx ho hst
    obtain ⟨K, p, i, hp, hi, hpi, hie⟩ := imageRep G _ _ _ (d 0) e h0
    have h1 : Function.Exact (d 1).hom p.hom := by
      intro y
      rw [← hx 0 (Nat.succ_pos m) y, ← hpi y]
      constructor
      · intro h; rw [h, map_zero]
      · intro h; exact hi (by rw [h, map_zero])
    have hK := ih (fun q => X (q + 1)) (fun q => d (q + 1)) K p hp h1
      (fun q hq => hx (q + 1) (by omega)) (fun q hq => ho (q + 1) (by omega))
      (fun q hq => hst (q + 1) (by omega))
    have hC := (permCard G s m A (X 0) (ho 0 (by omega)) (hst 0 (by omega)) hs).1
    obtain ⟨u, v, huv⟩ := (les G _ _ _ i e hi hie he m).2
    exact fgStep u v huv hK

theorem fgShift : FgShift := by
  intro G _ A s m X _ d M e hs he h0 hx ho hst
  exact finOfFg _ (fg_homology_of_permutation_resolution G A s hs m X d M e he h0 hx ho hst)

end UpperTheory.FiniteGenerationAndTorsion

end
