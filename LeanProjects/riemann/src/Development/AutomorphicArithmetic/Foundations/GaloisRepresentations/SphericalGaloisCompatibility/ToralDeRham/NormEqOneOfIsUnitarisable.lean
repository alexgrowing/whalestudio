import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharactersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Holds7SizeAway
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfHasSupportSingleton
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.Window

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_absPow_ofReal (r : ℝ) (z : kˣ) : ‖((absPow k (r : ℂ) z : ℂˣ) : ℂ)‖ = nabs k z ^ r := by
  rw [val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (GlobalTheory.SmGL.nabs_pos' k z).le _)]

theorem len_eq_one {Δ : Segment k} {s : ℂ} {S : Multiset (IrrGL k)} (hS : Unlinked S)
    (hm : ∀ a, (Δ.term a).nu s ∈ S) : Δ.len = 1 := by
  by_contra hne
  have h2 : 2 ≤ Δ.len := by have := Δ.len_pos; omega
  refine hS _ (hm ⟨1, by omega⟩) _ (hm ⟨0, by omega⟩) ?_
  simp only [Segment.term, IrrGL.nu_nu]
  congr 1
  push_cast
  ring

theorem norm_eq_one_of_isUnitarisable {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (hu : IsUnitarisable (IrrGL.ofChar μ hμ).rep) (z : kˣ) : ‖((μ z : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : IsUnitarisable (detRep (Fin 1) μ) :=
    GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (equivRep (IrrRep.det (Fin 1) μ hμ)).symm hu
  have h := (isUnitarisable_ofChar_iff _).1 h1 (Matrix.GeneralLinearGroup.scalar (Fin 1) z)
  have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rwa [detChar_apply, h2] at h

theorem exponents_of_genericUnitary (hGU : GlobalTheory.Published.GenericUnitaryDualGL) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    [CharZero k] (x : IrrGL k) (hg : IsGeneric x.rep) (hu : IsUnitarisable x.rep) {n : ℕ}
    (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hx : HasSupport x.rep (chars ξ hξ))
    (hU : Unlinked (chars ξ hξ)) (j : Fin n) :
    ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ z, ‖((ξ j z : ℂˣ) : ℂ)‖ = ‖((absPow k (e : ℂ) z : ℂˣ) : ℂ)‖ := by
  obtain ⟨h, δ, Δ, s, hΔ, hδu, hs, hd, ⟨φ⟩⟩ := hGU.exists_prod x.2.rep.smooth x.2.rep.irr hu hg
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  have hsupp : HasSupport x.rep (∑ i, (Δ i).ms.map fun y => y.nu (s i)) :=
    GlobalTheory.LocGL.SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ
      (fun i => GlobalTheory.LocGL.SupportRing.hasSupport_nu (hΔ i).hasSupport (s i)) x.2.rep.irr
      (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have heq : chars ξ hξ = ∑ i, (Δ i).ms.map fun y => y.nu (s i) :=
    GlobalTheory.LocGL.SupportUnique.eq_of_hasSupport GlobalTheory.RecT.geometricLemma_holds hZ _ x rfl _ _ hx hsupp
  have hj : IrrGL.ofChar (ξ j) (hξ j) ∈ ∑ i, (Δ i).ms.map fun y => y.nu (s i) :=
    heq ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
  obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hj
  have hm : ∀ a, ((Δ i).term a).nu (s i) ∈ chars ξ hξ := fun a => heq ▸ Multiset.mem_sum.2
    ⟨i, Finset.mem_univ _, Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val a))⟩
  have hlen := len_eq_one hU hm
  have hfirst : (Δ i).first ∈ (Δ i).ms := by
    have h0 : (Δ i).term ⟨0, (Δ i).len_pos⟩ ∈ (Δ i).ms := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    have e0 : (Δ i).term ⟨0, (Δ i).len_pos⟩ = (Δ i).first := by simp [Segment.term]
    rwa [e0] at h0
  have hms : (Δ i).ms = {(Δ i).first} := by
    obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 (by simp [Segment.ms, hlen] : Multiset.card (Δ i).ms = 1)
    rw [hz] at hfirst ⊢
    rw [Multiset.mem_singleton.1 hfirst]
  have hδ : δ i = (Δ i).first := GlobalTheory.DZeroDegOne.eq_of_hasSupport_singleton (hms ▸ (hΔ i).hasSupport)
  obtain ⟨y, hy, hyc⟩ := Multiset.mem_map.1 hi
  rw [hms, Multiset.mem_singleton] at hy
  subst hy
  have hμ : IsSmoothChar (ξ j * absPow k ((-(s i) : ℝ) : ℂ)) := (hξ j).mul (isSmoothChar_absPow _)
  have hc : IrrGL.ofChar (ξ j * absPow k ((-(s i) : ℝ) : ℂ)) hμ = δ i := by
    rw [hδ, ← IrrGL.tw_ofChar _ _ (hξ j) (isSmoothChar_absPow _)]
    change (IrrGL.ofChar (ξ j) (hξ j)).nu _ = _
    rw [← hyc, IrrGL.nu_nu]
    push_cast
    simp
  have h1 := norm_eq_one_of_isUnitarisable hμ (hc ▸ hδu i)
  refine ⟨s i, hs i, fun z => ?_⟩
  have h2 := h1 z
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_absPow_ofReal] at h2
  rw [norm_absPow_ofReal]
  have hp : 0 < nabs k z := GlobalTheory.SmGL.nabs_pos' k z
  rw [Real.rpow_neg hp.le] at h2
  have hq : 0 < nabs k z ^ s i := Real.rpow_pos_of_pos hp _
  field_simp at h2
  exact h2

end GlobalTheory.RoadU.Window

open GlobalTheory.RoadU.Window in

theorem GlobalTheory.RoadU.window : UpperTheory.Gal.ToralGalois.Inq → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ wt : ℤ, IsWeight π wt → ∀ w : HeightOneSpectrum (𝓞 E), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → (∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖((ξ j x : ℂˣ) : ℂ)‖ = ‖((absPow (w.adicCompletion E) ((e - (wt : ℝ) / 2 : ℝ) : ℂ) x : ℂˣ) : ℂ)‖) := by
  intro hI E _ _ _ l n hn π χ _ wt hwt w σ hσ ξ hξ hS hU j
  set c : ℂ := (((wt : ℝ) / 2 : ℝ) : ℂ) with hc
  let ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j => ξ j * absPow (w.adicCompletion E) c
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (isSmoothChar_absPow _)
  have hT := GlobalTheory.T.supercuspidalSupport_twist_nu_characters (w.adicCompletion E) (algNorm σ) n ξ ξ' hξ hξ' c (fun _ => rfl)
  have hg : IsGeneric ((algNorm σ).nu c).rep := by
    refine GlobalTheory.GalCut.AwayMono.isGeneric_nu (GlobalTheory.GalCut.AwayMono.isGeneric_nu ?_ _) _
    exact (isGeneric_congr (IrrGL.equivOf σ.ρ σ.smooth σ.irred)).1
      (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w σ hσ)
  have hu := GlobalTheory.GalCut7.SizeAway.isUnitarisable E n hn π wt hwt w σ hσ
  obtain ⟨e, he, hx⟩ := exponents_of_genericUnitary hI.gen hI.zel _ hg hu ξ' hξ' (hT.1.1 hS) (hT.2.1 hU) j
  refine ⟨e, he, fun x => ?_⟩
  have h1 := hx x
  simp only [ξ', MonoidHom.mul_apply, Units.val_mul, norm_mul, hc, norm_absPow_ofReal] at h1
  rw [norm_absPow_ofReal]
  have hp : 0 < nabs (w.adicCompletion E) x := GlobalTheory.SmGL.nabs_pos' _ x
  rw [Real.rpow_sub hp, eq_div_iff (Real.rpow_pos_of_pos hp _).ne']
  exact h1

end

section

end
