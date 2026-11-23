import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GSetup

theorem exists_uSetup_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ η ∈ genericPoints (Xo.XF c), ∀ B : ℕ, ∃ X₁ : USetup C, B ≤ X₁.S.N ∧ IsProjOver X₁.M.s ∧ ∀ w, X₁.uΩ w = η := by
  intro E _ _ _ H Dw hpq l Xo c C η hη B
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨A, _, φ, j, P, _, hφ, hjs, hjo, hjx⟩ :=
    exists_chart (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) η
  let ev : A →+* P.ResidueField := algebraMap A P.ResidueField
  let y : Sp P.ResidueField ⟶ Xo.XF c := spMap ev ≫ j
  have hy : ∀ w, y w = η := fun w => by
    have hp : spMap ev w = ⟨P, inferInstance⟩ := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ev w.asIdeal = P
      rw [Subsingleton.elim w (⊥ : PrimeSpectrum P.ResidueField)]
      exact Ideal.ker_algebraMap_residueField _
    show j (spMap ev w) = η
    rw [hp, hjx]
  haveI : CharZero P.ResidueField := (ev.comp φ).charZero_iff (ev.comp φ).injective |>.1 inferInstance
  obtain ⟨A₀, hS₀, hU₀⟩ := exists_fibre Xo c y
  have ho : Odd H.d := Nat.odd_iff.2 (by have := H.d_mod; omega)
  obtain ⟨k, j₁, hk, hBk, hj₁, big⟩ := exists_big_level A₀.g H.d H.d_prime.two_le B
  obtain ⟨Ω, _, f, A₁, ψ, ze, hf, hA₁, hze, ⟨lev⟩⟩ :=
    exists_level_finite P.ResidueField A₀ ((H.d ^ j₁ * (H.d ^ k) ^ 2) ^ 2) (Nat.one_le_iff_ne_zero.2 (by
      have := H.d_prime.pos; positivity))
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hU₁ : UOver Xo c A₁ (RingHom.id Ω) (spMap f ≫ y) := by
    refine (uOver_baseChange_iff hA₁.2.1 (LBIso.symm hA₁.2.2) (RingHom.id Ω)).2 ?_
    rw [RingHom.id_comp]
    simpa only [RingHom.comp_id] using hU₀.comp f
  have hS₁ : HypS A₁.A A₁.L := by
    have := A₀.isAb.comm
    have := A₁.isAb.comm
    exact SymBaseChange.hypS_baseChange _ _ _ _ _ ψ _ _ A₀.isLB A₁.isLB hA₁.2.1 (LBIso.symm hA₁.2.2) hS₀
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  let β : c.F →+* Ω := f.comp (ev.comp φ)
  obtain ⟨o₁, _, _, κ, ze₁, hded, hκ, hinj, hcomp, hze₁⟩ :=
    exists_base_root C.o c.F Ω β ze _ (Nat.one_le_iff_ne_zero.2 (by have := H.d_prime.pos; positivity)) hze
  have hft : Algebra.FiniteType ℤ o₁ := by
    letI := κ.toAlgebra
    haveI := C.ft
    haveI : Algebra.FiniteType C.o o₁ := hκ.finiteType
    exact Algebra.FiniteType.trans C.ft this
  haveI : ArithBase o₁ Ω := ⟨hded, hft, inferInstance, hinj⟩
  have hun : IsUnit (H.d : o₁) := by simpa using C.unit_d.map κ
  rw [← hze₁] at lev
  have hβ : β.EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.EssFiniteType.comp hφ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := A) (S := P.ResidueField)).2 inferInstance)) hf.finiteType.essFiniteType
  obtain ⟨R₀, hR₀, hfr, hR₀e⟩ := exists_fg_ratHull C.b (fun y => exists_int_mul_mem y) κ β hcomp hβ φ hφ (f.comp ev) rfl
  let u₀ : Sp (ratHull R₀) ⟶ Xo.XF c := spMap ((f.comp ev).codRestrict (ratHull R₀) hR₀e) ≫ j
  have hu₀ : spMap (ratHull R₀).val.toRingHom ≫ u₀ = spMap f ≫ y := by
    simp only [u₀, y, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨S, ρ, u, hN, hr, hg, hUS, hpt⟩ :=
    exists_thetaSys_uOver Xo c R₀ hR₀ hfr u₀ A₁ (hu₀ ▸ hU₁) hS₁ H.d k j₁ H.d_prime ho hk hj₁ hun ze₁ lev
  have hbig : S.Big := big j₁ le_rfl o₁ Ω S (hg.trans hA₁.1) hN hr
  have hp : spMap (ratHull S.R).val.toRingHom ≫ u = spMap f ≫ spMap ev ≫ j := hpt.trans hu₀
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  haveI := C.isPreimmersion_i
  haveI : SurjectiveOnStalks (spMap ev) :=
    (SurjectiveOnStalks.Spec_iff (φ := CommRingCat.ofHom ev)).2 (Ideal.surjectiveOnStalks_residueField P)
  have hi : C.i ≫ C.z = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap C.b := by
    simp only [UCompact.i, Category.assoc, pullback.condition]
    rw [← Category.assoc, C.iF_over]
  have hpz : (spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i) ≫ C.z = spMap ((algebraMap o₁ Ω).comp κ) := by
    rw [show (spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i) ≫ C.z =
      (spMap (ratHull S.R).val.toRingHom ≫ u) ≫ (C.i ≫ C.z) by simp only [Category.assoc], hp, hi]
    simp only [Category.assoc]
    rw [← Category.assoc j, hjs, hcomp]
    simp only [← Spec.map_comp]
    rfl
  have hst : ((spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
    rw [← Category.assoc, hp, Category.assoc, Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (finite_stalkMap_field f hf _)
      (RingHom.Finite.of_surjective _ (Scheme.Hom.stalkMap_surjective _ _))
  obtain ⟨Mdl, π, hMn, hπ, hMp⟩ := GlobalTheory.Poinc.exists_ratModel_normalization C.o o₁ Ω κ hκ C.Z C.z inferInstance
    inferInstance inferInstance _ hpz hst
  have hgen : ∀ w, (spMap (ratHull S.R).val.toRingHom ≫ u) w = η := fun w => by
    rw [hp]
    exact hy _
  have hsc : Mdl.s ≫ spMap κ = π ≫ C.z := by
    refine ext_of_isDominant Mdl.pt ?_
    rw [← Category.assoc, Mdl.pt_s, ← Category.assoc, hMp, hpz]
    exact (Spec.map_comp (CommRingCat.ofHom κ) (CommRingCat.ofHom (algebraMap o₁ Ω))).symm
  have hproj : IsProjOver Mdl.s := by
    haveI := hπ
    obtain ⟨h1, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB C.z).1 C.proj
    haveI : IsProper (Mdl.s ≫ spMap κ) := by rw [hsc]; infer_instance
    haveI : IsProper Mdl.s := IsProper.of_comp Mdl.s (spMap κ)
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, _, hL.pull_of_isFinite π⟩
  exact ⟨⟨o₁, Ω, S, ρ, hbig, u, hUS, fun w => (hgen w).symm ▸ hη, Mdl, GlobalTheory.IsNormalScheme.of_pred hMn, π, hπ, hMp⟩, hN ▸ hBk, hproj, hgen⟩

end GlobalTheory.UPoinc.GSetup
