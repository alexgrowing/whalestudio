import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualEq
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PeriodLattice

theorem periods_unif : GlobalTheory.Published.PeriodComparison →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ P : E →+ HdR X.A, Submodule.span ℂ (Set.range P) = ⊤ ∧
      ∀ (a : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) a * w' j) = U.u.ex w' ≫ α) →
        ∀ x, push (dp0 ℂ) (𝟙 _) α (P x) = P (a * x) := by
  intro hPC E _ _ _ I _ φ L 𝔠 X U
  obtain ⟨ε, hε⟩ := hPC
  obtain ⟨P₀, hspan, -, -, hend, -⟩ :=
    hε X.A (Module.finrank ℚ (FR E)) X.ab X.dim (X.diag U.c) (LB.isLB_pull (X.isLB _) _) U.u
  let em : E →ₗ[ℚ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j => φ (U.e j) x
      map_add' := fun x x' => by funext j; simp
      map_smul' := fun q x => by funext j; simp [Rat.smul_def] }
  have hem : ∀ x j, em x j = φ (U.e j) x := fun _ _ => rfl
  have hdc : ∀ x, (fun j => GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (U.e j)) = em x := fun x => by
    funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, hem]
  let S : AddSubgroup E :=
    { carrier := {x | em x ∈ U.u.Λ}
      add_mem' := fun {a b} ha hb => by
        show em (a + b) ∈ U.u.Λ
        rw [map_add]; exact add_mem ha hb
      zero_mem' := by
        show em 0 ∈ U.u.Λ
        rw [map_zero]; exact zero_mem _
      neg_mem' := fun {a} ha => by
        show em (-a) ∈ U.u.Λ
        rw [map_neg]; exact neg_mem ha }
  have hemL : ∀ x ∈ S, em x ∈ U.u.Λ := fun x hx => hx
  let Q : S →+ HdR X.A :=
    { toFun := fun x => P₀ ⟨em x, hemL x x.2⟩
      map_zero' := by
        rw [show (⟨em ((0 : S) : E), hemL _ (0 : S).2⟩ : U.u.Λ) = 0 from
          Subtype.ext (by simp), map_zero]
      map_add' := fun x x' => by
        rw [← map_add]
        congr 1
        ext
        simp }
  have hsur : ∀ w ∈ U.u.Λ, ∃ x, em x = w := fun w hw => by
    obtain ⟨x, -, rfl⟩ := (U.lat w).1 hw
    exact ⟨x, (hdc x).symm⟩
  have hΛ : (U.u.Λ : Set (Fin (Module.finrank ℚ (FR E)) → ℂ)) = em '' (S : Set E) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, rfl⟩ := hsur w hw
      exact ⟨x, hw, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hemL x hx
  have hdim : Module.finrank ℚ E ≤ 2 * Module.finrank ℚ (FR E) := by
    rw [← Module.finrank_mul_finrank ℚ (FR E) E, Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]
  have full : ∀ x : E, ∃ n : ℕ, 0 < n ∧ n • x ∈ S :=
    exists_nsmul_mem S em hdim (hΛ ▸ U.u.full)
  obtain ⟨P, hP⟩ := exists_ext S full Q
  have hP1 : ∀ x (hx : x ∈ S), P x = P₀ ⟨em x, hemL x hx⟩ := fun x hx => by
    rw [hP x 1 one_pos (by rw [one_smul]; exact hx), Nat.cast_one, inv_one, one_smul]
    show P₀ _ = P₀ _
    congr 2
    simp
  refine ⟨P, ?_, ?_⟩
  · refine top_unique (hspan ▸ Submodule.span_mono ?_)
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    obtain ⟨x, rfl⟩ := hsur w hw
    exact ⟨x, hP1 x hw⟩
  · intro a α _ hα x
    obtain ⟨n, hn, hnx⟩ := full x
    obtain ⟨m, hm, hmx⟩ := full (a * x)
    have hpos : 0 < n * m := Nat.mul_pos hn hm
    have hNx : (n * m) • x ∈ S := by
      rw [mul_comm, mul_smul]; exact S.nsmul_mem hnx _
    have hNax : (n * m) • (a * x) ∈ S := by
      rw [mul_smul]; exact S.nsmul_mem hmx _
    let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j => φ (U.e j) a * w j
        map_add' := fun w w' => by funext j; simp [mul_add]
        map_smul' := fun r w => by funext j; simp; ring }
    rw [hP x _ hpos hNx, hP (a * x) _ hpos hNax, map_smul]
    congr 1
    exact hend α M (fun w => hα w) ⟨em ((n * m) • x), hemL _ hNx⟩ ⟨em ((n * m) • (a * x)), hemL _ hNax⟩
      (by funext j; simp only [hem, M, LinearMap.coe_mk, AddHom.coe_mk, map_nsmul, nsmul_eq_mul, map_mul]; ring)

end GlobalTheory.PeriodLattice
