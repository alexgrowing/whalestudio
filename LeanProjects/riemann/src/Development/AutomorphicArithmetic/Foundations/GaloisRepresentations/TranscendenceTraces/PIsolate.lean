import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.isolate_of :
    Chart → IsolateSpec → Isolate := by
  intro hC hI Z S p _ z
  have hmem : p z ∈ (⊤ : S.Opens) := trivial
  obtain ⟨U, hU0, hzU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens) hmem
  have hU : IsAffineOpen U := hU0
  let u0 : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.isoSpec.inv ≫ Scheme.Opens.ι U
  obtain ⟨B, iB, iAB, v0, hfin, hpb⟩ := hC p Γ(S, U) u0
  haveI := hfin
  obtain ⟨y, hy⟩ : ∃ y : (U : Scheme), Scheme.Opens.ι U y = p z := ⟨⟨p z, hzU⟩, rfl⟩
  have ha : u0 (hU.isoSpec.hom y) = p z := by
    show (hU.isoSpec.hom ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U) y = p z
    rw [Iso.hom_inv_id_assoc, hy]
  obtain ⟨w0, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := u0) z _ ha.symm
  have hw : v0 (hpb.isoPullback.inv w0) = z := by
    rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hw1]
  obtain ⟨A', W, v, hEt, hW, hvW, hvv, hiso⟩ := hI Γ(S, U) B (hpb.isoPullback.inv w0)
  haveI := hEt
  refine ⟨⟨A'.U, A'.V, A'.u ≫ u0, A'.v ≫ v0, A'.r, A'.pb.paste_horiz hpb⟩, W, v, ?_, hW, hvW, ?_, hiso⟩
  · show Etale (A'.u ≫ u0)
    infer_instance
  · show (A'.v ≫ v0) v = z
    rw [Scheme.Hom.comp_apply, hvv, hw]
