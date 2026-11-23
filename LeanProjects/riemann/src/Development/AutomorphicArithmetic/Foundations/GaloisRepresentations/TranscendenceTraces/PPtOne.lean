import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma ring_eq {Ω B L : Type} [Field Ω] [IsAlgClosed Ω] [CommRing B] [Algebra Ω B] [Module.Finite Ω B] [Field L]
    (f f' : B →+* L) (h : f.comp (algebraMap Ω B) = f'.comp (algebraMap Ω B))
    (hk : RingHom.ker f = RingHom.ker f') : f = f' := by
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  haveI : IsDomain (B ⧸ RingHom.ker f) := Ideal.Quotient.isDomain _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := B ⧸ RingHom.ker f)
  ext b
  obtain ⟨c, hc⟩ := hb.2 (Ideal.Quotient.mk _ b)
  have hm : b - algebraMap Ω B c ∈ RingHom.ker f := by
    rw [← Ideal.Quotient.eq]
    rw [← hc]
    rfl
  have h1 : f b = f (algebraMap Ω B c) := by
    have := RingHom.mem_ker.mp hm
    rw [map_sub, sub_eq_zero] at this
    exact this
  have h2 : f' b = f' (algebraMap Ω B c) := by
    have := RingHom.mem_ker.mp (hk ▸ hm)
    rw [map_sub, sub_eq_zero] at this
    exact this
  rw [h1, h2]
  exact congrArg (fun g : Ω →+* L => g c) h

private lemma pt_spec {B L : Type} [CommRing B] [Field L] (f : CommRingCat.of B ⟶ CommRingCat.of L) :
    (pt (Spec.map f) : Spec (CommRingCat.of B)).asIdeal = RingHom.ker f.hom := by
  ext b
  change f.hom b ∈ (IsLocalRing.closedPoint L).asIdeal ↔ _
  simp [RingHom.mem_ker, IsLocalRing.closedPoint]

theorem UpperTheory.Gal.TranscendenceTraces.ptOne_of :
    Chart → PtOne := by
  intro hC V Ω _ _ r _ L _ a z z' hz hz' hp
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC r Ω (𝟙 _)
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  have hs : inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = r := by
    have := hpb.w
    rw [Category.comp_id] at this
    rw [← this, IsIso.inv_hom_id_assoc]
  obtain ⟨f, hf⟩ := Spec.map_surjective (z ≫ inv v)
  obtain ⟨f', hf'⟩ := Spec.map_surjective (z' ≫ inv v)
  have e1 : Spec.map f ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = a := by
    rw [hf, Category.assoc, hs, hz]
  have e2 : Spec.map f' ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = a := by
    rw [hf', Category.assoc, hs, hz']
  have e3 : CommRingCat.ofHom (algebraMap Ω B) ≫ f = CommRingCat.ofHom (algebraMap Ω B) ≫ f' := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, e1, e2]
  have e4 : pt (Spec.map f) = pt (Spec.map f') := by
    rw [hf, hf', pt_comp, pt_comp, hp]
  have e5 : RingHom.ker f.hom = RingHom.ker f'.hom := by
    rw [← pt_spec f, ← pt_spec f', e4]
  have e6 : f.hom = f'.hom := ring_eq f.hom f'.hom (congrArg CommRingCat.Hom.hom e3) e5
  have e7 : f = f' := CommRingCat.hom_ext e6
  have e8 : z ≫ inv v = z' ≫ inv v := by rw [← hf, ← hf', e7]
  exact (cancel_mono (inv v)).mp e8
