import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.NSideDecomp

theorem part_le_off' {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [IsLocalRing O] (T : Subalgebra O (Module.End K V)) {I J : Ideal T}
    (h : I ≠ J) : NCov.part T I ≤ NCov.off T J :=
  iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ J) => NCov.W T (NCov.pt ψ)) ψ
    (by rw [hψ]; exact h) le_rfl

theorem iV_eq_sum_Psi : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → ∀ y : D.what₂.MtL (D.what₂.muTw w) j, T.B.iV j w y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (D.nd.prMt i.1 (castMtInv D i.2 y)) := by
  classical
  intro D M T j w h1 h2 hw hstd y
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  rw [← sub_eq_zero]
  refine NCov.eq_zero_of_forall_mem_off hinj hS hsplit hint ((D.nd.locs j w).image (T.mx j w))
    (fun I hI => ?_) ?_
  · obtain ⟨i, hi, rfl⟩ := T.mx_all j w h1 h2 hw I hI
    exact Finset.mem_image_of_mem _ hi
  · intro I hI
    obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.1 hI
    rw [← Finset.add_sum_erase _ _ (Finset.mem_attach _ ⟨i0, hi0⟩), sub_add_eq_sub_sub]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun i hi => ?_)
    · have e := T.Psi_pr j w i0 hi0 (castMtInv D hi0 y)
      rw [castMt_castMtInv] at e
      rw [← neg_sub]
      exact Submodule.neg_mem _ e
    · have hne : T.mx j w i.1 ≠ T.mx j w i0 := by
        intro e
        have := T.mx_inj j w i.2 hi0 e
        exact (Finset.mem_erase.1 hi).1 (Subtype.ext this)
      exact part_le_off' _ hne ((T.Psi_range j w i.1 i.2 _).2 ⟨_, rfl⟩)

end GlobalTheory.NSideDecomp
