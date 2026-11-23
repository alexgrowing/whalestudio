import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncIso

theorem mem_vanishingIdeal_ideal_iff {X : Scheme.{0}} (Z : Closeds X) (U : X.affineOpens) (s : Γ(X, U.1)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U ↔
      ∀ x ∈ (U.1 : Set X), x ∈ (Z : Set X) → x ∉ X.basicOpen s := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · rintro h x hxU hxZ hxs
    rw [← U.2.range_fromSpec] at hxU
    obtain ⟨p, rfl⟩ := hxU
    have hp : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := hxs
    rw [U.2.fromSpec_preimage_basicOpen] at hp
    exact hp (h p hxZ)
  · intro h p hpZ
    by_contra hs
    have hp : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
      rw [U.2.fromSpec_preimage_basicOpen]; exact hs
    have hpU : U.2.fromSpec p ∈ (U.1 : Set X) := by
      rw [← U.2.range_fromSpec]; exact ⟨p, rfl⟩
    exact h _ hpU hpZ hp

theorem rsp_ringEquiv {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (e : R ≃+* S)
    {n : ℕ} {x : Fin n → R} (h : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R n x) : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp S n (fun i => e (x i)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have hr : Set.range (fun i => e (x i)) = e '' Set.range x := by
    rw [← Set.range_comp]; rfl
  rw [hr, ← Ideal.map_span, h1]
  ext y
  rw [Ideal.mem_map_of_equiv, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩ hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hz ((isUnit_map_iff e z).1 hu)
  · intro hy
    refine ⟨e.symm y, (IsLocalRing.mem_maximalIdeal _).2 fun hu => hy ?_, e.apply_symm_apply y⟩
    simpa using (isUnit_map_iff e (e.symm y)).2 hu

theorem snc_vanishingIdeal_of_isIso {A B : Scheme.{0}} (f : A ⟶ B) [IsIso f] (Z : Closeds B) (Z' : Closeds A)
    (hZ : ∀ a : A, a ∈ Z' ↔ f a ∈ Z) (h : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z)) :
    ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z') := by
  intro a
  obtain ⟨hreg, U, hU, n, g, J, hrsp, hid⟩ := h (f a)
  let e : B.presheaf.stalk (f a) ≃+* A.presheaf.stalk a := (asIso (f.stalkMap a)).commRingCatIsoToRingEquiv
  have he : ∀ t, e t = f.stalkMap a t := fun _ => rfl
  let U' : A.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have hU' : a ∈ U'.1 := hU
  refine ⟨IsRegularLocalRing.of_ringEquiv e, U', hU', n, fun i => f.app U.1 (g i), J, ?_, ?_⟩
  · have hg : ∀ i, A.presheaf.germ U'.1 a hU' (f.app U.1 (g i)) = e (B.presheaf.germ U.1 (f a) hU (g i)) := by
      intro i
      rw [he, Scheme.Hom.germ_stalkMap_apply]
    simp only [hg]
    exact rsp_ringEquiv e hrsp
  · let φ : Γ(B, U.1) ≃+* Γ(A, U'.1) := (asIso (f.app U.1)).commRingCatIsoToRingEquiv
    have hφ : ∀ t, φ t = f.app U.1 t := fun _ => rfl
    ext t
    obtain ⟨s, rfl⟩ : ∃ s, φ s = t := φ.surjective t
    have key : φ s ∈ (Scheme.IdealSheafData.vanishingIdeal Z').ideal U' ↔
        s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U := by
      rw [mem_vanishingIdeal_ideal_iff, mem_vanishingIdeal_ideal_iff, hφ, ← Scheme.preimage_basicOpen]
      constructor
      · intro H b hbU hbZ hbs
        obtain ⟨a', rfl⟩ : ∃ a', f a' = b := ⟨(inv f) b, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
        exact H a' hbU ((hZ a').2 hbZ) hbs
      · intro H a' ha'U ha'Z ha's
        exact H (f a') ha'U ((hZ a').1 ha'Z) ha's
    rw [key, hid, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    have hp : (∏ i ∈ J, f.app U.1 (g i)) = φ (∏ i ∈ J, g i) := by
      rw [map_prod]; rfl
    rw [hp, map_dvd_iff]

end GlobalTheory.SncIso

namespace GlobalTheory.VarFlag

open GlobalTheory.Toroidal (gen genι genBd genBdIdeal mem_genBd)

theorem snc_genBdIdeal_of_snc_boundary {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} :
    ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.LogKS.boundary Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.Toroidal.genBdIdeal Y) := by
  intro h
  refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (genι Y) (GlobalTheory.LogKS.interior Y).compl (genBd Y) (fun a => ?_) h
  have hinj : Function.Injective (genι Y) := (genι Y).isOpenEmbedding.injective
  rw [mem_genBd]
  show a ∉ Set.range Y.jQ ↔ genι Y a ∉ Set.range Y.j
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Model.j, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, hinj ?_⟩
    rw [← hx, Model.j, Scheme.Hom.comp_apply]

end GlobalTheory.VarFlag
