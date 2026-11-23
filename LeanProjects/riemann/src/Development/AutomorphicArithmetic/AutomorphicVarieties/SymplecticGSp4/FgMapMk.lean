import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WcompMulHomog

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem fg_map_mk {O A S : Type} [CommRing O] [IsNoetherianRing O] [CommRing A] [Algebra O A] [CommRing S]
    [Algebra O S] (f : A →ₐ[O] S) (I : Ideal A) (hI : ∀ a, f a = 0 ↔ a ∈ I) (P : Submodule O A) (T : Submodule O S)
    (hT : T.FG) (hP : ∀ a ∈ P, f a ∈ T) : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).FG := by
  have hIf : ∀ a ∈ I, f a = 0 := fun a ha => (hI a).mpr ha
  let g : A ⧸ I →ₐ[O] S := Ideal.Quotient.liftₐ I f hIf
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hI a).mp hy
  haveI : IsNoetherian O T := isNoetherian_of_fg_of_noetherian T hT
  have hle : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).map g.toLinearMap ≤ T := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hP a ha
  exact Submodule.fg_of_fg_map_injective g.toLinearMap hg (isNoetherian_submodule.mp inferInstance _ hle)

theorem UpperTheory.V.GradeZeroInterpolatingElement.m2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], D.Fin0 → M2 M.gr M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hF
  obtain ⟨h1, -, h3⟩ := kerA D hD M
  have hs := spanMono D hD M hF 0
  have hfin := hF M.S M.ru M.pt
  have hT : (Subalgebra.toSubmodule (Algebra.adjoin c.O (mono M.ru.hom 0))).FG :=
    Module.Finite.iff_fg.1 hfin
  refine fg_map_mk (M.SS.val.comp M.toSS) _ (fun a => ?_) _ _ hT (fun a ha => ?_)
  · rw [← h1 a]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · have h4 : (M.toSS a).1 ∈ M.sPart 0 := h3 0 a ha
    rw [hs] at h4
    exact Algebra.span_le_adjoin _ _ h4
