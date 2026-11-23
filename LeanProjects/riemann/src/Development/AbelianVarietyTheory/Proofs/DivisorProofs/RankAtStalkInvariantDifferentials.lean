import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace GlobalTheory.WmodRank

theorem rankAtStalk_wmod : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] (d : ℕ),
    GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega A) d → ∀ p : PrimeSpectrum O,
      Module.rankAtStalk (R := O) (GlobalTheory.SqZeroPt.Wmod A) p = d := by
  intro O _ A _ d h p
  have hfr : ∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s := fun x => by
    obtain ⟨U, e, hx, he⟩ := h x
    exact ⟨U, d, e, hx, he⟩
  haveI : (GlobalTheory.LieVB.omega A).IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames hfr
  obtain ⟨hfin, hproj⟩ := GlobalTheory.FramesFGP.finite_projective_wmod O A hfr
  have hb : Function.Bijective (GlobalTheory.LieVB.cst O) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv
  obtain ⟨U, e, hx, he⟩ := h p
  have hU := isAffineOpen_top (Sp O)
  obtain ⟨f, hf, hpf⟩ := hU.exists_basicOpen_le (V := U) ⟨p, hx⟩ trivial
  obtain ⟨r, rfl⟩ := hb.2 f
  have hrp : r ∉ p.asIdeal := by
    have : p ∈ (Sp O).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv r) := hpf
    rw [AlgebraicGeometry.basicOpen_eq_of_affine] at this
    exact this
  set F := GlobalTheory.LieVB.omega A
  set f := GlobalTheory.LieVB.cst O r with hfdef
  let S := Γ(Sp O, (Sp O).basicOpen f)
  let M' := Γ(F, (Sp O).basicOpen f)
  let res : Γ(Sp O, ⊤) →+* S := ((Sp O).presheaf.map (homOfLE ((Sp O).basicOpen_le f)).op).hom
  letI : Algebra O S := (res.comp (GlobalTheory.LieVB.cst O)).toAlgebra
  letI : Module O M' := Module.compHom M' (algebraMap O S)
  haveI : IsScalarTower O S M' := .of_algebraMap_smul fun _ _ => rfl
  let l : GlobalTheory.SqZeroPt.Wmod A →ₗ[O] M' :=
    { toFun := GlobalTheory.QCoh.resBasicOpen F f
      map_add' := map_add _
      map_smul' := fun c w => (GlobalTheory.QCoh.resBasicOpen F f).map_smul (GlobalTheory.LieVB.cst O c) w }
  haveI hL := GlobalTheory.QCoh.isLocalizedModule_resBasicOpen F hU f
  haveI hS := hU.isLocalization_basicOpen f
  have hSO : IsLocalization (Submonoid.powers r) S := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      have := IsLocalization.map_units S (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
      simpa [RingHom.algebraMap_toAlgebra, hfdef, map_pow] using this
    · intro z
      obtain ⟨⟨a, ⟨s, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers f) z
      obtain ⟨a', rfl⟩ := hb.2 a
      refine ⟨⟨a', ⟨r ^ n, n, rfl⟩⟩, ?_⟩
      simpa [RingHom.algebraMap_toAlgebra, hfdef, map_pow] using hz
    · intro x y hxy
      have hxy' : algebraMap Γ(Sp O, ⊤) S (GlobalTheory.LieVB.cst O x) = algebraMap Γ(Sp O, ⊤) S (GlobalTheory.LieVB.cst O y) := hxy
      obtain ⟨⟨c, n, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers f) hxy'
      refine ⟨⟨r ^ n, n, rfl⟩, hb.1 ?_⟩
      simpa [hfdef, map_pow] using hc
  have hLO : IsLocalizedModule (Submonoid.powers r) l := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      have := IsLocalizedModule.map_units (GlobalTheory.QCoh.resBasicOpen F f) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
      rw [Module.End.isUnit_iff] at this ⊢
      have hfun : ⇑(algebraMap O (Module.End O M') (r ^ n)) =
          ⇑(algebraMap Γ(Sp O, ⊤) (Module.End Γ(Sp O, ⊤) M') (f ^ n)) := by
        funext m
        simp only [Module.algebraMap_end_apply]
        show res (GlobalTheory.LieVB.cst O (r ^ n)) • m = res (f ^ n) • m
        rw [map_pow]
      simpa only [hfun] using this
    · intro z
      obtain ⟨⟨a, ⟨s, n, rfl⟩⟩, hz⟩ := IsLocalizedModule.surj (Submonoid.powers f) (GlobalTheory.QCoh.resBasicOpen F f) z
      refine ⟨⟨a, ⟨r ^ n, n, rfl⟩⟩, ?_⟩
      show res (GlobalTheory.LieVB.cst O (r ^ n)) • z = GlobalTheory.QCoh.resBasicOpen F f a
      rw [map_pow]
      exact hz
    · intro x y hxy
      obtain ⟨⟨c, n, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := GlobalTheory.QCoh.resBasicOpen F f) hxy
      refine ⟨⟨r ^ n, n, rfl⟩, ?_⟩
      have hc' : f ^ n • (show Γ(F, ⊤) from x) = f ^ n • (show Γ(F, ⊤) from y) := hc
      rw [hfdef, ← map_pow] at hc'
      exact hc'
  have hbc : IsBaseChange S l := (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) S l).1 hLO
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap O S)) := by
    rw [PrimeSpectrum.localization_away_comap_range S r]
    exact hrp
  obtain ⟨q, rfl⟩ := hq
  let bas : Module.Basis (Fin d) S M' := he.basis hf
  haveI := Module.Free.of_basis bas
  haveI : Nontrivial S := q.nontrivial
  rw [← Module.rankAtStalk_isBaseChange hbc q, Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank S M' = d
  rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]

end GlobalTheory.WmodRank
