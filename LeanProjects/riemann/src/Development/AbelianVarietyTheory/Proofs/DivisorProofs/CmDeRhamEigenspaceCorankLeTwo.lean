import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMultEigen

theorem diagonalizable_corank_le_two {V : Type*} {κ : Type} [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (S : Module.End ℂ V) (ν : κ → ℂ)
    (hS : ∀ k, S (b k) = ν k • b k) (k₁ k₂ : κ) (hν : ∀ k, ν k = 0 → k = k₁ ∨ k = k₂) :
    Module.rank ℂ (V ⧸ LinearMap.range S) ≤ 2 ∧ Disjoint (LinearMap.ker S) (LinearMap.range S) := by
  classical
  have hr : ∀ k x, b.repr (S x) k = ν k * b.repr x k := fun k x => by
    have : (b.coord k) ∘ₗ S = ν k • b.coord k := b.ext fun l => by
      by_cases h : l = k
      · subst h; simp [hS]
      · simp [hS, Finsupp.single_apply, h]
    simpa using LinearMap.congr_fun this x
  constructor
  · let q := (LinearMap.range S).mkQ
    have htop : Submodule.span ℂ (({q (b k₁), q (b k₂)} : Finset _) : Set (V ⧸ LinearMap.range S)) = ⊤ := by
      rw [eq_top_iff, ← (LinearMap.range S).range_mkQ, LinearMap.range_eq_map (Submodule.mkQ _), ← b.span_eq, Submodule.map_span,
        Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      by_cases h : ν k = 0
      · apply Submodule.subset_span
        rcases hν k h with rfl | rfl <;> simp [q]
      · have : (LinearMap.range S).mkQ (b k) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨(ν k)⁻¹ • b k, by rw [map_smul, hS, smul_smul, inv_mul_cancel₀ h, one_smul]⟩
        rw [this]
        exact Submodule.zero_mem _
    rw [← rank_top, ← htop]
    refine (rank_span_finset_le _).trans ?_
    exact_mod_cast Finset.card_le_two
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    rw [LinearMap.mem_ker] at hx
    apply b.repr.injective
    ext k
    have h := hr k (S y)
    rw [hx, hr] at h
    rw [hr]
    simp only [map_zero, Finsupp.zero_apply] at h ⊢
    rcases mul_eq_zero.1 h.symm with h | h
    · rw [h, zero_mul]
    · exact h

theorem exists_eigenbasis {V : Type*} [AddCommGroup V] [Module ℂ V] {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (full : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (P : Λ →+ V) (hspan : Submodule.span ℂ (Set.range P) = ⊤)
    (hdim : Module.finrank ℂ V = 2 * g) (T : Module.End ℂ V) (r : Fin g → ℝ)
    (hT : ∀ x : Λ, ∃ x' : Λ, (x' : Fin g → ℂ) = (fun j => (r j : ℂ) * (x : Fin g → ℂ) j) ∧ T (P x) = P x') :
    ∃ b : Module.Basis (Fin g × Bool) ℂ V, ∀ k, T (b k) = (r k.1 : ℂ) • b k := by
  classical
  haveI : IsZLattice ℝ Λ := ⟨full⟩
  letI : Module ℝ V := Module.compHom V (algebraMap ℝ ℂ)
  haveI : IsScalarTower ℝ ℂ V := ⟨fun a c v => by
    change (a • c) • v = (algebraMap ℝ ℂ a) • c • v
    rw [smul_smul, Algebra.smul_def]⟩
  let bZ := Module.Free.chooseBasis ℤ Λ
  let bR := bZ.ofZLatticeBasis ℝ Λ
  let Q : (Fin g → ℂ) →ₗ[ℝ] V := bR.constr ℝ fun k => P (bZ k)
  have hQ : ∀ x : Λ, Q x = P x := fun x => by
    have : (Q.toAddMonoidHom.toIntLinearMap ∘ₗ Λ.subtype) = P.toIntLinearMap := bZ.ext fun k => by
      have := bR.constr_basis ℝ (fun k => P (bZ k)) k
      simpa [bR, Q] using this
    exact LinearMap.congr_fun this x
  let M : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun w j => (r j : ℂ) * w j
      map_add' := fun w w' => by funext j; simp [mul_add]
      map_smul' := fun c w => by funext j; simp; ring }
  have hTQ : ∀ w, T (Q w) = Q (M w) := fun w => by
    have : (T.restrictScalars ℝ) ∘ₗ Q = Q ∘ₗ M := bR.ext fun k => by
      obtain ⟨x', h1, h2⟩ := hT (bZ k)
      have e : bR k = bZ k := by simp [bR]
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, e]
      rw [hQ, h2, ← hQ, h1]
      rfl
    exact LinearMap.congr_fun this w
  let v : Fin g × Bool → V := fun k => Q (Pi.single k.1 (if k.2 then Complex.I else 1))
  have hv : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← hQ]
    generalize (x : Fin g → ℂ) = w
    have hw : w = ∑ j, ((w j).re • (Pi.single j 1 : Fin g → ℂ) + (w j).im • (Pi.single j Complex.I : Fin g → ℂ)) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
    rw [hw, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_add, map_smul, map_smul]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(j, false), rfl⟩)
    · exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(j, true), rfl⟩)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank v hv (by rw [hdim]; simp [mul_comm]), fun k => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  have : M (Pi.single k.1 (if k.2 then Complex.I else 1)) =
      r k.1 • (Pi.single k.1 (if k.2 then Complex.I else 1) : Fin g → ℂ) := by
    funext l
    by_cases h : l = k.1
    · subst h; simp [M]
    · simp [M, Pi.single_apply, h]
  simp only [v]
  rw [hTQ, this, map_smul]
  rfl

theorem rank_coker_le_two : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X), IsCMType φ →
    ∀ (i : I) (b₀ : 𝓞 (FR E)), (∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i) →
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) := by
  intro hPC _ E _ _ _ I _ φ L 𝔠 X U _ i b₀ hsep
  obtain ⟨ε, hε⟩ := hPC
  obtain ⟨P, hspan, hdim, -, hend, -⟩ :=
    hε X.A (Module.finrank ℚ (FR E)) X.ab X.dim (X.diag U.c) (LB.isLB_pull (X.isLB _) _) U.u
  have hreal : ∀ j, (((φ j ((b₀ : FR E) : E)).re : ℝ) : ℂ) = φ j ((b₀ : FR E) : E) := fun j =>
    Complex.conj_eq_iff_re.1 ((b₀ : FR E).2 (φ j))
  let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun w j => φ (U.e j) ((b₀ : FR E) : E) * w j
      map_add' := fun w w' => by funext j; simp [mul_add]
      map_smul' := fun r w => by funext j; simp; ring }
  haveI := U.u.discrete
  obtain ⟨b, hb⟩ := exists_eigenbasis U.u.Λ U.u.full P hspan hdim (act (dp0 ℂ) (𝟙 _) X.rm b₀)
    (fun j => (φ (U.e j) ((b₀ : FR E) : E)).re) (fun x => by
      have hx : M x ∈ U.u.Λ := by
        rw [← U.u.ker]
        refine (U.act b₀ x).trans ?_
        rw [(U.u.ker x).2 x.2]
        haveI := X.rm.hom b₀
        exact MonObj.one_comp _
      refine ⟨⟨M x, hx⟩, ?_, ?_⟩
      · funext j
        rw [hreal]
        rfl
      · haveI := X.rm.hom b₀
        exact hend (X.rm.act b₀) M (U.act b₀) x ⟨M x, hx⟩ rfl)
  refine diagonalizable_corank_le_two b _ (fun k => φ (U.e k.1) ((b₀ : FR E) : E) - φ i ((b₀ : FR E) : E)) (fun k => ?_)
    (U.e.symm i, false) (U.e.symm i, true) (fun k hk => ?_)
  · rw [LinearMap.sub_apply, hb, hreal, sub_smul]
    rfl
  · obtain ⟨j, c⟩ := k
    have : j = U.e.symm i := by rw [← hsep _ (sub_eq_zero.1 hk)]; simp
    subst this
    cases c <;> simp

end GlobalTheory.RealMultEigen
