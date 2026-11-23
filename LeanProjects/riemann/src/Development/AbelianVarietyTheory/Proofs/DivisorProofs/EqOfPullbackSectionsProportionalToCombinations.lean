import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

open TopologicalSpace

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem mem_nonzeroLocus_iff_comb {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} {Ψ : X ⟶ B₀} (hcov : ⨆ i, nonzeroLocus (b i) = ⊤)
    (hG : Generates a φ p c) (hP : Proport a b φ p Ψ c) {z : X} {q : N.ι} (hq : φ z ∈ N.U q) {k : H.ι}
    (hk : Ψ z ∈ H.U k) (i : Fin mB) :
    Ψ z ∈ nonzeroLocus (b i) ↔ IsUnit (comb a φ p c z q i) := by
  obtain ⟨j₀, hj₀⟩ := hG z q hq
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (Ψ z)))
  have u₀ := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i₀) Ψ z hk).1 hi₀
  have e₀ := hP z q k hq hk i₀ j₀
  have ub : IsUnit (gs Ψ z (H.U k) ((b j₀).f k)) := by
    have := u₀.mul hj₀
    rw [e₀] at this
    exact isUnit_of_mul_isUnit_left this
  have e := hP z q k hq hk j₀ i
  rw [GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i) Ψ z hk]
  constructor
  · intro h
    have := h.mul hj₀
    rw [← e] at this
    exact isUnit_of_mul_isUnit_right this
  · intro h
    have := ub.mul h
    rw [e] at this
    exact isUnit_of_mul_isUnit_left this

theorem gs_eval_eq {Rg : Type} [CommRing Rg] {fB : B₀ ⟶ Sp Rg} {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H}
    {φ : X ⟶ A₀} {p : X ⟶ T} {c : Fin mA → Fin mB → Γ(T, ⊤)} {Ψ₁ Ψ₂ : X ⟶ B₀}
    (hcov : ⨆ i, nonzeroLocus (b i) = ⊤) (hH : H.IsLB) (hN : N.IsLB) (hG : Generates a φ p c)
    (h₁ : Proport a b φ p Ψ₁ c) (h₂ : Proport a b φ p Ψ₂ c) (e : Ψ₁ ≫ fB = Ψ₂ ≫ fB) {i : Fin mB}
    {r : Fin mB → Γ(B₀, nonzeroLocus (b i))} (hr : ∀ j, GlobalTheory.AmpleSpan.IsRatio (b j) (b i) (r j)) (x : X)
    (m₁ : Ψ₁ x ∈ nonzeroLocus (b i)) (m₂ : Ψ₂ x ∈ nonzeroLocus (b i)) (P : MvPolynomial (Fin mB) Γ(Sp Rg, ⊤)) :
    gs Ψ₁ x _ (MvPolynomial.eval₂Hom (fB.appLE ⊤ (nonzeroLocus (b i)) le_top).hom r P) =
      gs Ψ₂ x _ (MvPolynomial.eval₂Hom (fB.appLE ⊤ (nonzeroLocus (b i)) le_top).hom r P) := by
  obtain ⟨q, hq⟩ := exists_chart hN (φ x)
  have key : ∀ Ψ : X ⟶ B₀, Proport a b φ p Ψ c → Ψ x ∈ nonzeroLocus (b i) → ∀ j,
      gs Ψ x _ (r j) * comb a φ p c x q i = comb a φ p c x q j := fun Ψ hP m j => by
    obtain ⟨k, hk⟩ := exists_chart hH (Ψ x)
    have ub := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i) Ψ x hk).1 m
    have e₁ := hP x q k hq hk j i
    rw [(hr j).gs Ψ x m hk] at e₁
    refine ub.mul_left_cancel ?_
    rw [← e₁]
    ring
  have uc : IsUnit (comb a φ p c x q i) := by
    obtain ⟨k, hk⟩ := exists_chart hH (Ψ₁ x)
    exact (mem_nonzeroLocus_iff_comb hcov hG h₁ hq hk i).1 m₁
  induction P using MvPolynomial.induction_on with
  | C a₀ =>
    rw [MvPolynomial.eval₂Hom_C, GlobalTheory.AmpleSpan.gs_const fB _ Ψ₁ x m₁, GlobalTheory.AmpleSpan.gs_const fB _ Ψ₂ x m₂, e]
  | add P Q hP hQ => rw [map_add, gs_add _ x _ m₁, gs_add _ x _ m₂, hP, hQ]
  | mul_X P j hP =>
    rw [map_mul, gs_mul _ x _ m₁, gs_mul _ x _ m₂, hP, MvPolynomial.eval₂Hom_X']
    exact congrArg _ (uc.mul_right_cancel ((key Ψ₁ h₁ m₁ j).trans (key Ψ₂ h₂ m₂ j).symm))

theorem eq_of_proport : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (Ψ₁ Ψ₂ : X ⟶ B₀), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → GlobalTheory.HomFixUniv.Generates a φ p c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₁ c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₂ c → Ψ₁ ≫ fB = Ψ₂ ≫ fB → Ψ₁ = Ψ₂ := by
  intro Rg _ A₀ B₀ X T fB N H mA mB a b φ p c Ψ₁ Ψ₂ hE hH hN hG h₁ h₂ e
  obtain ⟨hcov, hloc⟩ := hE
  have hW : ⨆ i, Ψ₁ ⁻¹ᵁ nonzeroLocus (b i) = ⊤ := by
    refine top_le_iff.1 fun x _ => Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (Ψ₁ x)))
    exact ⟨i, hi⟩
  let 𝒰 := X.openCoverOfIsOpenCover (fun i => Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)) hW
  refine 𝒰.hom_ext _ _ fun i => ?_
  obtain ⟨ha, r, hr, hs⟩ := hloc i
  have m₂ : ∀ x, Ψ₁ x ∈ nonzeroLocus (b i) → Ψ₂ x ∈ nonzeroLocus (b i) := fun x hx => by
    obtain ⟨q, hq⟩ := exists_chart hN (φ x)
    obtain ⟨k₁, hk₁⟩ := exists_chart hH (Ψ₁ x)
    obtain ⟨k₂, hk₂⟩ := exists_chart hH (Ψ₂ x)
    exact (mem_nonzeroLocus_iff_comb hcov hG h₂ hq hk₂ i).2 ((mem_nonzeroLocus_iff_comb hcov hG h₁ hq hk₁ i).1 hx)
  change (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι ≫ Ψ₁ = (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι ≫ Ψ₂
  have w₁ : ∀ w : (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).toScheme, Ψ₁ ((Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι w) ∈ nonzeroLocus (b i) :=
    fun w => w.2
  refine GlobalTheory.SecRingIso.hom_ext_affine ha (fun w => w₁ w) (fun w => m₂ _ (w₁ w)) fun f w => ?_
  obtain ⟨P, rfl⟩ := hs f
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_comp _ Ψ₁ w _ (w₁ w), ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_comp _ Ψ₂ w _ (m₂ _ (w₁ w))]
  exact congrArg _ (gs_eval_eq hcov hH hN hG h₁ h₂ e hr _ (w₁ w) (m₂ _ (w₁ w)) P)

end GlobalTheory.HomFixUniv
