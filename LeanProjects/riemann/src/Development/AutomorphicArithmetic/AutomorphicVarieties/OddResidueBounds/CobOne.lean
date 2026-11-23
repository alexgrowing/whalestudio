import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FnOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ContinuousToTorsionBounded
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CocycleCoboundaryFiniteIndex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem coboundary_of_vanishing_on_finite_index {R Q M : Type} [CommRing R] [Group Q] [AddCommGroup M] [Module R M]
    (π : Representation R Q M) (H : Subgroup Q) (f : Q → M) (hf : ∀ g h, f (g * h) = f g + π g (f h))
    (h0 : ∀ u ∈ H, f u = 0) (hn : IsUnit (H.index : R)) (hn' : H.index ≠ 0) : ∃ m, ∀ g, f g = π g m - m :=
  _root_.UpperTheory.Reformulated.B.CocycleCoboundaryFiniteIndex.coboundary_of_vanishing_on_finite_index π H f hf h0 hn hn'

theorem UpperTheory.V.Odd.cobOne :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (z : Z1 (qzTw D e)), (∀ g ∈ galOf E (Fn E Ω l 1) Ω, z.1 (toGS Ω _ g) = 0) → (Submodule.Quotient.mk z : H1 (qzTw D e)) = 0 := by
  intro E Ω _ _ _ _ _ l hl D e z hz
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  have h0 := (fnCyc E Ω l 1).1
  rw [pow_one] at h0
  haveI : FiniteDimensional E (Fn E Ω l 1) := IsCyclotomicExtension.finiteDimensional {l} E _
  haveI : NumberField (Fn E Ω l 1) := NumberField.of_module_finite E _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure (Fn E Ω l 1) Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  have hi : (galOf E (Fn E Ω l 1) Ω).index ∣ l - 1 := by
    rw [(galEmbTop E (Fn E Ω l 1) Ω).2.2]
    exact (fnOne E Ω l).1
  have h2 := hl.out.two_le
  have hle := Nat.le_of_dvd (by omega) hi
  have hne : (galOf E (Fn E Ω l 1) Ω).index ≠ 0 := fun h => by
    rw [h, zero_dvd_iff] at hi
    omega
  have hu : IsUnit ((galOf E (Fn E Ω l 1) Ω).index : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff, hl.out.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hne) (by omega)
  obtain ⟨m, hm⟩ := coboundary_of_vanishing_on_finite_index ((qzTw D e).comp (toGS Ω _)) (galOf E (Fn E Ω l 1) Ω) (fun g => z.1 (toGS Ω _ g))
    (fun g h => by rw [map_mul]; exact z.2.2 _ _) hz hu hne
  rw [Submodule.Quotient.mk_eq_zero]
  refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
  obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω _ σ = g := QuotientGroup.mk_surjective g
  exact hm σ
