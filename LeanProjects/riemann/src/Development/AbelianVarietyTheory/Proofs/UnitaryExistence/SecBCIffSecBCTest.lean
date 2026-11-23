import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SectionBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.SecFieldCompare

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD HasBC map_trans evR_spec evR_not evR_test evR_of_map
  map_cancel hasBC_of exists_testRing_ext)
open GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests (IsBCTest SecBCTest SecBCAll)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def homRes {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (ψ : S →ₐ[c'.F] T) : S →ₐ[c.F] T :=
  { ψ.toRingHom with
    commutes' := fun a => by
      show ψ (algebraMap c.F S a) = algebraMap c.F T a
      rw [← hS a, ψ.commutes, hT a] }

theorem frMap_res_iff {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (ψ : S →ₐ[c'.F] T)
    (y : FrPt Xo c' S) (z : FrPt Xo c' T) :
    FrMap (homRes hle hS hT ψ) (y.res hle hS) (z.res hle hT) ↔ FrMap ψ y z := Iff.rfl

theorem fromT_of_res (hBC : HasBC Xo c) {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (hy : FromT (y.res hle h)) : FromT y := by
  obtain ⟨p, φ, y₀, hy₀⟩ := hy
  let : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  obtain ⟨q, α, hα, hlift, -⟩ := exists_testRing_ext (K' := c'.F) p
  obtain ⟨β, hβ⟩ := hlift S φ.toRingHom fun a => (φ.commutes a).trans (h a).symm
  let : Algebra c.F q.R := ((algebraMap c'.F q.R).comp (incF c c' hle)).toAlgebra
  have hq : AlgOver c c' hle q.R := fun _ => rfl
  let α' : p.R →ₐ[c.F] q.R := { α with commutes' := hα }
  obtain ⟨y₁, hy₁⟩ := hBC _ _ α' y₀
  have e : (homRes hle hq h β).comp α' = φ := AlgHom.ext hβ
  have h₂ : FrMap (homRes hle hq h β) y₁ (y.res hle h) := map_cancel hBC e hy₁ hy₀
  exact ⟨q, β, y₁.ext hle hq, (frMap_res_iff hle hq h β (y₁.ext hle hq) y).1 h₂⟩

theorem isBCTest_of_isBC (hWD : ValueWD Xo c) {m : ℕ} {f' : Rul Xo c'} {as : Fin m → c'.F} {fs : Fin m → Rul Xo c}
    (hf' : Natural c' f') (hfs : ∀ i, Natural c (fs i)) (h : IsBC hle f' as fs) : IsBCTest hle f' as fs := by
  intro p' _ hp y' p φ y hy
  rw [← evR_test hf' p' y', h p'.R hp y']
  exact Finset.sum_congr rfl fun i _ => congrArg _ (evR_of_map hWD (hfs i) hy)

theorem isBC_of_isBCTest (hWD : ValueWD Xo c) (hBC : HasBC Xo c) (hT : AllTest Xo c) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hfs : ∀ i, Natural c (fs i)) (h : IsBCTest hle f' as fs) :
    IsBC hle f' as fs := by
  intro S _ _ _ hS y
  by_cases hy : FromT y
  · obtain ⟨q, ψ, y', hy', hev⟩ := evR_spec hy
    let : Algebra c.F q.R := ((algebraMap c'.F q.R).comp (incF c c' hle)).toAlgebra
    have hq : AlgOver c c' hle q.R := fun _ => rfl
    have : IsReduced q.R := (Ideal.isRadical_iff_quotient_reduced _).1 q.rad
    obtain ⟨p, φ, y₀, hy₀⟩ := hT q.R (y'.res hle hq)
    have h₂ := map_trans _ _ hy₀ ((frMap_res_iff hle hq hS ψ y' y).2 hy')
    rw [hev, h q hq y' p φ y₀ hy₀, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ψ.commutes, evR_of_map hWD (hfs i) h₂]
    rfl
  · have hy' : ¬ FromT (y.res hle hS) := fun h' => hy (fromT_of_res hle hBC hS y h')
    rw [evR_not hy]
    exact (Finset.sum_eq_zero fun i _ => by rw [evR_not hy', mul_zero]).symm

theorem isBC_iff_isBCTest {m : ℕ} {f' : Rul Xo c'} {as : Fin m → c'.F} {fs : Fin m → Rul Xo c}
    (hf' : Natural c' f') (hfs : ∀ i, Natural c (fs i)) : IsBC hle f' as fs ↔ IsBCTest hle f' as fs :=
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c := evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  ⟨isBCTest_of_isBC hle hWD hf' hfs,
    isBC_of_isBCTest hle hWD (hasBC_of hS) (GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c) hfs⟩

variable (Xo)

theorem secBC_iff_secBCTest (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests.SecBC Xo hle a n ↔ SecBCTest Xo hle a n :=
  forall₂_congr fun _ hf' => exists₃_congr fun _ _ _ => and_congr_right fun hfs =>
    isBC_iff_isBCTest hle hf'.1 fun i => (hfs i).1

theorem secBC_iff_forall : Formalism.L2.Pj.SecBC Xo hle ↔ ∀ a n, GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests.SecBC Xo hle a n := Iff.rfl

theorem secBC_typings_equiv :
    (Formalism.L2.Pj.SecBC Xo hle ↔ ∀ a n, GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests.SecBC Xo hle a n) ∧
    (Formalism.L2.Pj.SecBC Xo hle ↔ SecBCAll Xo hle) ∧
    (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (f' : Rul Xo c') (as : Fin m → c'.F) (fs : Fin m → Rul Xo c),
      f' ∈ sec Xo c' a n → (∀ i, fs i ∈ sec Xo c a n) → (IsBC hle f' as fs ↔ IsBCTest hle f' as fs)) ∧
    (Formalism.L2.Pj.SecBC Xo hle ↔ ∀ a n, SecBCTest Xo hle a n) :=
  ⟨Iff.rfl, Iff.rfl, fun _ _ _ _ _ _ hf' hfs => isBC_iff_isBCTest hle hf'.1 fun i => (hfs i).1,
    forall₂_congr fun a n => secBC_iff_secBCTest Xo hle a n⟩

end GlobalTheory.SecFieldCompare
