import Development.EtaleCohomology.EtaleSheaves.LocallyConstantH0

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCBijPf

def TwGenNZAC : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (K : Type) [Field K] [IsAlgClosed K] (ζ : Prim q K) (c : ZMod q),
  c.val • twGen i (gam ζ) = 0 → c = 0

abbrev TwGenNZ : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (B : Type) [CommRing B] [Nontrivial B] (ζ : Prim q B) (c : ZMod q),
  c.val • twGen i (gam ζ) = 0 → c = 0

def LCSurj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B), Function.Surjective (m B ζ)

theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold Sec.res twGen ofRings.sec tw ofRings
  erw [← ModuleCat.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g.op).hom) (Finsupp.single ζ 1)) = _
  erw [Finsupp.mapDomain_single]
  rfl

theorem gam_map {q : ℕ} {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) :
    gam (ζ.map f) = (gam ζ).map (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  apply Subtype.ext
  change (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (f ζ.1) =
    (Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ζ.1)
  have := congrArg (fun φ => φ.hom ζ.1) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem twGenNZ_of (hAC : TwGenNZAC) : TwGenNZ := by
  intro q _ i B _ _ ζ c h
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  let _ : Field (B ⧸ M) := Ideal.Quotient.field M
  let f : B →+* AlgebraicClosure (B ⧸ M) := (algebraMap (B ⧸ M) (AlgebraicClosure (B ⧸ M))).comp (Ideal.Quotient.mk M)
  apply hAC q i (AlgebraicClosure (B ⧸ M)) (ζ.map f) c
  have h2 := congrArg (Sec.res (Spec.map (CommRingCat.ofHom f))) h
  have hs : ∀ x : Sec (tw q i) (Spec (CommRingCat.of B)), Sec.res (Spec.map (CommRingCat.ofHom f)) (c.val • x) =
      c.val • Sec.res (Spec.map (CommRingCat.ofHom f)) x := fun x => map_nsmul _ _ x
  have hz : Sec.res (Spec.map (CommRingCat.ofHom f)) (0 : Sec (tw q i) (Spec (CommRingCat.of B))) = 0 := map_zero _
  rw [hs, hz, twGen_res, ← gam_map] at h2
  exact h2

theorem lcInj (hT : TwGenNZ) (q : ℕ) [NeZero q] (i : ℤ) m (hm : IsLCMap q i m) (B : Type) [CommRing B]
    (ζ : Prim q B) : Function.Injective (m B ζ) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  by_contra hne
  obtain ⟨p, hp⟩ : ∃ p, φ p ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LocallyConstant.ext h)
  set c := φ p with hc
  let U : Set (PrimeSpectrum B) := φ ⁻¹' {c}
  have hU : IsClosed U := (φ.isLocallyConstant.isClopen_fiber c).isClosed
  let I := PrimeSpectrum.vanishingIdeal U
  let f := Ideal.Quotient.mk I
  have hrange : Set.range (PrimeSpectrum.comap f) = U := by
    rw [_root_.range_comap_of_surjective _ f Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.closure_eq]
  have hconst : lcMap f φ = LocallyConstant.const _ c := by
    ext x
    have : PrimeSpectrum.comap f x ∈ U := hrange ▸ ⟨x, rfl⟩
    exact this
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ I := h ▸ Submodule.mem_top
    have hpU : p ∈ U := rfl
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ((PrimeSpectrum.mem_vanishingIdeal _ _).1 h1 p hpU))
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have h1 := hm.1 B (B ⧸ I) f ζ φ
  rw [hφ, hconst, hm.2] at h1
  simp only [map_zero] at h1
  exact hp (hT q i (B ⧸ I) (ζ.map f) c h1.symm)

theorem LCBij_of (hT : TwGenNZAC) (hS : LCSurj) : LateralTheory.E.LocallyConstantH0.LCBij :=
  fun q _ i m hm B _ ζ => ⟨lcInj (twGenNZ_of hT) q i m hm B ζ, hS q i m hm B ζ⟩

end LateralTheory.E.LCBijPf
