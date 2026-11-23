import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

private theorem spMap_inj' {R R' : Type} [CommRing R] [CommRing R'] {f g : R →+* R'} (h : spMap f = spMap g) : f = g := by
  have h' := Spec.map_injective h
  ext x
  exact congrArg (fun φ => CommRingCat.Hom.hom φ x) h'

private theorem spMap_algComp {V B C D : Type} [CommRing V] [CommRing B] [CommRing C] [CommRing D] [Algebra V B] [Algebra V C]
    [Algebra V D] (a : C →ₐ[V] D) (b : B →ₐ[V] C) :
    spMap (a.comp b).toRingHom = spMap a.toRingHom ≫ spMap b.toRingHom := by
  rw [spMap_comp']; rfl

private theorem pt_alg {V B Λ : Type} [CommRing V] [CommRing B] [Algebra V B] [CommRing Λ] [Algebra V Λ]
    (w : algPt V Λ ⟶ algPt V B) : ∃ ν : B →ₐ[V] Λ, w.left = spMap ν.toRingHom := by
  have e : Spec.map (CommRingCat.ofHom (Spec.preimage w.left).hom) = w.left := by
    simp
  have hw := Over.w w
  have key : (Spec.preimage w.left).hom.comp (algebraMap V B) = algebraMap V Λ := by
    apply spMap_inj'
    rw [← spMap_comp']
    change Spec.map (CommRingCat.ofHom (Spec.preimage w.left).hom) ≫ spMap (algebraMap V B) = spMap (algebraMap V Λ)
    rw [e]
    simpa using hw
  exact ⟨{ (Spec.preimage w.left).hom with commutes' := fun r => congrArg (fun φ => φ r) key }, e.symm⟩

private noncomputable def ptOf {V B Λ : Type} [CommRing V] [CommRing B] [Algebra V B] [CommRing Λ] [Algebra V Λ]
    (ν : B →ₐ[V] Λ) : algPt V Λ ⟶ algPt V B :=
  Over.homMk (spMap ν.toRingHom) (by
    show spMap ν.toRingHom ≫ spMap (algebraMap V B) = spMap (algebraMap V Λ)
    rw [spMap_comp']
    congr 1
    exact ν.comp_algebraMap)

private theorem surj_of_mono {κ B B' : Type} [Field κ] [CommRing B] [Algebra κ B] [CommRing B'] [Algebra κ B'] [Module.Finite κ B']
    (π : B →ₐ[κ] B') (h : Mono (spMap π.toRingHom)) : Function.Surjective π := by
  have hm : Mono (CommRingCat.ofHom π.toRingHom).op :=
    Functor.mono_of_mono_map Scheme.Spec (f := (CommRingCat.ofHom π.toRingHom).op) h
  have he : Epi (CommRingCat.ofHom π.toRingHom) := (op_mono_iff _).mp hm
  have hfin : π.toRingHom.Finite := by
    apply RingHom.Finite.of_comp_finite (f := algebraMap κ B)
    convert RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite κ B') using 1
    exact π.comp_algebraMap
  exact RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom π.toRingHom) hfin

end UpperTheory.Gal.crystallineComparison.Mod

private theorem exists_integer_mul_eq_of_valuation_le {V B Λ : Type} [CommRing V] [CommRing B] [Algebra V B] [CommRing Λ] [Algebra V Λ]
    {A : Over (Sp V)} (i : algPt V B ⟶ A) [Mono i] {φ ψ : B →ₐ[V] Λ}
    (h : spMap φ.toRingHom ≫ i.left = spMap ψ.toRingHom ≫ i.left) : φ = ψ := by
  haveI := Over.mono_left_of_mono i
  have h1 := Mod.spMap_inj' ((cancel_mono i.left).mp h)
  ext x
  exact RingHom.congr_fun h1 x

private theorem inSub_iff_exists_algHom_factor {V B Λ : Type} [CommRing V] [CommRing B] [Algebra V B] [CommRing Λ] [Algebra V Λ]
    {A : Over (Sp V)} (i : algPt V B ⟶ A) (g : algPt V Λ ⟶ A) :
    InSub i g ↔ ∃ ν : B →ₐ[V] Λ, g.left = spMap ν.toRingHom ≫ i.left := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨ν, hν⟩ := Mod.pt_alg y
    exact ⟨ν, by rw [← hy, Over.comp_left, hν]⟩
  · rintro ⟨ν, hν⟩
    exact ⟨Mod.ptOf ν, Over.OverMorphism.ext (by rw [Over.comp_left, hν]; rfl)⟩

theorem UpperTheory.Gal.crystallineComparison.Mod.infW_of :
    RingHomog → CotanOne → ChainRing → RepHomog → FrobRing → InfW := by
  intro hRH hCO hCR hRP hFR
  intro p f hp κ _ _ _ A _ P P' d d' hRA hSub hcard hd hRA' hle hTan Λ _ _ _ ε g hP'g hInf
  obtain ⟨B, _, _, hBfin, hBfree, hBrank, i, hi, hiP⟩ := hRA
  obtain ⟨B', _, _, hB'fin, _, _, i', hi', hiP'⟩ := hRA'
  obtain ⟨hcardB, ε₀, hInf0, htrans⟩ := hRP κ A P hSub B i hi hiP
  haveI : (RingHom.ker ε₀.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hq := hRH κ B ε₀ htrans
  rw [hBrank, hcardB, hcard] at hq
  have hq' : Module.finrank κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) = p ^ f :=
    (Nat.eq_of_mul_eq_mul_right hd (hq.trans (mul_comm _ _))).symm
  obtain ⟨j, hj⟩ : InSub i' i := (hiP' _ i).mpr (hle _ i ((hiP _ i).mp ⟨𝟙 _, Category.id_comp _⟩))
  obtain ⟨π, hπ⟩ := Mod.pt_alg j
  haveI : Mono j := mono_of_mono_fac hj
  haveI := Over.mono_left_of_mono j
  have hπs : Function.Surjective π := Mod.surj_of_mono π (by rw [← hπ]; infer_instance)
  haveI := Over.mono_left_of_mono i'
  have hiL : i.left = spMap π.toRingHom ≫ i'.left := by rw [← hj, Over.comp_left, hπ]
  obtain ⟨ν', hν'⟩ := (inSub_iff_exists_algHom_factor i' g).mp ((hiP' _ g).mpr hP'g)
  have hInf0' : Inf (ε₀.comp π) i' := by
    unfold Inf at hInf0 ⊢
    rw [Mod.spMap_algComp, Category.assoc, ← hiL]
    exact hInf0
  have hεν : ε.comp ν' = ε₀.comp π := by
    apply exists_integer_mul_eq_of_valuation_le i'
    unfold Inf at hInf hInf0'
    rw [Mod.spMap_algComp, Category.assoc, ← hν', hInf, ← hInf0', Mod.spMap_algComp, Category.assoc]
  obtain ⟨v₀, hv₀P, hv₀I, hv₀⟩ := hTan
  obtain ⟨m₀, hm₀⟩ := (inSub_iff_exists_algHom_factor i' v₀).mp ((hiP' _ v₀).mpr hv₀P)
  have hcot := hCO κ B' (ε₀.comp π) m₀ (by
    intro v hv
    have hvI : Inf (TrivSqZeroExt.fstHom κ κ κ) (Mod.ptOf v ≫ i') := by
      unfold Inf at hInf0' ⊢
      rw [Over.comp_left]
      change spMap _ ≫ spMap v.toRingHom ≫ i'.left = _
      rw [← Category.assoc, ← Mod.spMap_algComp, hv]
      exact hInf0'
    obtain ⟨c, hc⟩ := hv₀ _ ((hiP' _ _).mp ⟨Mod.ptOf v, rfl⟩) hvI
    rw [hm₀, Over.comp_left, ← Category.assoc, Mod.spMap_comp'] at hc
    have hr := Mod.spMap_inj' ((cancel_mono i'.left).mp hc)
    refine ⟨c, fun x => ?_⟩
    have hx := RingHom.congr_fun hr x
    change v x = (epsScale c) (m₀ x) at hx
    rw [hx]
    simp [epsScale])
  have hch := hCR κ B' B Λ π ε₀ (p ^ f) hπs hq' hcot ε ν' hεν
  have hfr := hFR p f hp κ A B' Λ i' hi' (ε₀.comp π) hInf0' ν' g hν'
  rw [hfr, ← hiP]
  refine Iff.trans ?_ hch
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨m, hm⟩ := Mod.pt_alg y
    have hνm : ν' = m.comp π := exists_integer_mul_eq_of_valuation_le i' (by
      rw [← hν', ← hy, Over.comp_left, hm, hiL, Mod.spMap_algComp, Category.assoc])
    intro x hx
    rw [hνm, AlgHom.comp_apply, hx, map_zero]
  · intro hk
    let e := Ideal.quotientKerAlgEquivOfSurjective hπs
    let m : B →ₐ[κ] Λ := (Ideal.Quotient.liftₐ (RingHom.ker π) ν' (fun a ha => hk a ha)).comp e.symm.toAlgHom
    have hm : m.comp π = ν' := by
      ext x
      have he : e.symm (π x) = Ideal.Quotient.mk (RingHom.ker π) x := by
        rw [AlgEquiv.symm_apply_eq]
        rfl
      change (Ideal.Quotient.liftₐ (RingHom.ker π) ν' (fun a ha => hk a ha)) (e.symm (π x)) = ν' x
      rw [he]
      rfl
    refine ⟨Mod.ptOf m, Over.OverMorphism.ext ?_⟩
    rw [Over.comp_left]
    change spMap m.toRingHom ≫ i.left = g.left
    rw [hν', hiL, ← Category.assoc, ← Mod.spMap_algComp, hm]
