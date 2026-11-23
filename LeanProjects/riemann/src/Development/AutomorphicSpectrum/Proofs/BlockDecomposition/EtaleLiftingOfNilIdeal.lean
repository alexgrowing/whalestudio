import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtNil

theorem isNilpotent_of_fg_of_le {B : Type} [CommRing B] {J J' : Ideal B}
    (hJ : ∀ x ∈ J, IsNilpotent x) (hfg : J'.FG) (hle : J' ≤ J) : IsNilpotent J' :=
  (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 fun x hx => mem_nilradical.2 (hJ x (hle hx))

theorem exists_lift {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallySmooth P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (g : E →ₐ[P] B ⧸ J) :
    ∃ h : E →ₐ[P] B, (Ideal.Quotient.mkₐ P J).comp h = g := by
  obtain ⟨n, π, hπ, hK⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  choose b hb using fun i => Ideal.Quotient.mk_surjective (g (π (MvPolynomial.X i)))
  let φ : MvPolynomial (Fin n) P →ₐ[P] B := MvPolynomial.aeval b
  have hφ : (Ideal.Quotient.mkₐ P J).comp φ = g.comp π :=
    MvPolynomial.algHom_ext fun i => by simp [φ, hb]
  have hφ' : ∀ p, Ideal.Quotient.mk J (φ p) = g (π p) := fun p => DFunLike.congr_fun hφ p
  let J' : Ideal B := (RingHom.ker π.toRingHom).map φ.toRingHom
  have hle : J' ≤ J := by
    refine Ideal.map_le_iff_le_comap.2 fun p hp => ?_
    have hp0 : π p = 0 := hp
    refine Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    change Ideal.Quotient.mk J (φ p) = 0
    rw [hφ', hp0, map_zero]
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ (hK.map _) hle
  have hkill : ∀ a ∈ RingHom.ker π, ((Ideal.Quotient.mkₐ P J').comp φ) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem φ.toRingHom ha)
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let g' : E →ₐ[P] B ⧸ J' :=
    (Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill).comp
      e.symm.toAlgHom
  have hg' : ∀ p, g' (π p) = Ideal.Quotient.mk J' (φ p) := fun p => by
    have : e.symm (π p) = Ideal.Quotient.mk (RingHom.ker π) p := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hπ p).symm
    change Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill
      (e.symm (π p)) = _
    rw [this]
    rfl
  refine ⟨Algebra.FormallySmooth.lift J' hnil g', AlgHom.ext fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hπ x
  have h1 := Algebra.FormallySmooth.mk_lift J' hnil g' (π p)
  rw [hg', Ideal.Quotient.eq] at h1
  change Ideal.Quotient.mk J (Algebra.FormallySmooth.lift J' hnil g' (π p)) = g (π p)
  rw [← hφ', Ideal.Quotient.eq]
  exact hle h1

theorem lift_unique {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallyUnramified P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (h₁ h₂ : E →ₐ[P] B)
    (H : ∀ x, Ideal.Quotient.mk J (h₁ x) = Ideal.Quotient.mk J (h₂ x)) : h₁ = h₂ := by
  obtain ⟨n, π, hπ, -⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  let d : Fin n → B := fun i => h₁ (π (MvPolynomial.X i)) - h₂ (π (MvPolynomial.X i))
  let J' : Ideal B := Ideal.span (Set.range d)
  have hfg : J'.FG := Submodule.fg_span (Set.finite_range d)
  have hle : J' ≤ J := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.Quotient.eq.1 (H _)
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ hfg hle
  have hc : (Ideal.Quotient.mkₐ P J').comp (h₁.comp π) =
      (Ideal.Quotient.mkₐ P J').comp (h₂.comp π) :=
    MvPolynomial.algHom_ext fun i =>
      Ideal.Quotient.eq.2 (Ideal.subset_span ⟨i, rfl⟩)
  refine Algebra.FormallyUnramified.ext J' hnil fun x => ?_
  obtain ⟨p, rfl⟩ := hπ x
  exact DFunLike.congr_fun hc p

end GlobalTheory.CompanionTheory.EtNil

theorem GlobalTheory.CompanionTheory.EtNil.etLift_of_nil : ∀ {B : Type} [CommRing B] (J : Ideal B),
    (∀ x ∈ J, IsNilpotent x) → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g hg
  letI := ψ.toAlgebra
  letI := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let gA : E →ₐ[P] B ⧸ J :=
    { g with commutes' := fun p => DFunLike.congr_fun hg p }
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.EtNil.exists_lift J hJ gA
  have hh' : ∀ x, Ideal.Quotient.mk J (h x) = g x := fun x => DFunLike.congr_fun hh x
  refine ⟨h.toRingHom, ⟨RingHom.ext fun p => h.commutes p, RingHom.ext hh'⟩, ?_⟩
  rintro h' ⟨h1, h2⟩
  let hA : E →ₐ[P] B := { h' with commutes' := fun p => DFunLike.congr_fun h1 p }
  have : hA = h := GlobalTheory.CompanionTheory.EtNil.lift_unique J hJ hA h fun x => by
    change Ideal.Quotient.mk J (h' x) = _
    rw [hh']
    exact DFunLike.congr_fun h2 x
  exact RingHom.ext fun x => DFunLike.congr_fun this x
