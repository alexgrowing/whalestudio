import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AffineHilbertIdealSheafOfQuotientIdealTop
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.DualLatticeFamily

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.dotDual
  simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

noncomputable def dotB (Ω : Type) [Field Ω] (r : ℕ) : (Fin r → Ω) →ₗ[Ω] (Fin r → Ω) →ₗ[Ω] Ω :=
  LinearMap.mk₂ Ω (fun a b => a ⬝ᵥ b) (fun a a' b => add_dotProduct a a' b)
    (fun c a b => smul_dotProduct c a b) (fun a b b' => dotProduct_add a b b')
    (fun c a b => dotProduct_smul c a b)

theorem dotB_apply {Ω : Type} [Field Ω] {r : ℕ} (a b : Fin r → Ω) : dotB Ω r a b = a ⬝ᵥ b := rfl

theorem dotB_bij (Ω : Type) [Field Ω] (r : ℕ) : Function.Bijective (dotB Ω r).flip := by
  classical
  refine ⟨fun a b h => funext fun i => ?_, fun ψ => ⟨fun i => ψ (Pi.single i 1), ?_⟩⟩
  · have := LinearMap.congr_fun h (Pi.single i 1)
    simpa [dotB_apply] using this
  · refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : Fin r → Ω) = x • (Pi.single i 1 : Fin r → Ω) := by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rw [LinearMap.flip_apply, dotB_apply, single_dotProduct, hx, map_smul, smul_eq_mul]

theorem overlap {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {T : Type} (x : T → Ω) {r : ℕ}
    (i j : T) (hi : x i ≠ 0) (hj : x j ≠ 0) (Li Lj : AddSubgroup (Fin r → Ω))
    (hov : ∀ e ∈ Lj, ∃ m : ℕ, (x j / x i) ^ m • e ∈ Li) (hL : LocFree (chartRing O x j) r Lj)
    (w : Fin r → Ω) (hw : w ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual (chartRing O x i) Li) :
    ∃ m : ℕ, (x i / x j) ^ m • w ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual (chartRing O x j) Lj := by
  rw [mem_dotDual] at hw
  have hdiv : x i / x j ∈ chartRing O x j := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j i
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.Ar.Num.Reflexive.exists_uniform_denominator (chartRing O x j) r Lj hL
    (x i / x j) hdiv ((dotB Ω r).flip w) fun e he => by
      obtain ⟨m, hm⟩ := hov e he
      have h1 := hw _ hm
      rw [smul_dotProduct, smul_eq_mul] at h1
      obtain ⟨m', hm'⟩ : ∃ m' : ℕ, (x i / x j) ^ m' * ((x j / x i) ^ m * (e ⬝ᵥ w)) ∈ chartRing O x j :=
        ReciprocityTheory.ChartRestriction.G.Geo.exists_pow_mul_mem_chartRing x i j hi h1
      have hone : (x i / x j) ^ m * (x j / x i) ^ m = 1 := by
        rw [← mul_pow, div_mul_div_comm, _root_.mul_comm (x i), div_self (mul_ne_zero hj hi), one_pow]
      have h2 := mul_mem (pow_mem hdiv m) hm'
      have h3 : (x i / x j) ^ m * ((x i / x j) ^ m' * ((x j / x i) ^ m * (e ⬝ᵥ w))) =
          (x i / x j) ^ m' * (e ⬝ᵥ w) := by
        calc _ = (x i / x j) ^ m' * (e ⬝ᵥ w) * ((x i / x j) ^ m * (x j / x i) ^ m) := by ring
          _ = _ := by rw [hone, _root_.mul_one]
      rw [h3] at h2
      exact ⟨m', h2⟩
  refine ⟨m, (mem_dotDual _ _ _).2 fun l hl => ?_⟩
  rw [dotProduct_smul, smul_eq_mul]
  exact hm l hl

end PositivityTheory.Xgn.DualLatticeFamily

open PositivityTheory.Xgn.DualLatticeFamily in
theorem PositivityTheory.Xgn.dual_lattice_family : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) := by
  intro O _ Ω _ _ K _ J _ y r Γ hΓ hL
  refine ⟨⟨fun s _ a ha w hw => ?_, fun s t hs ht w hw => ?_⟩, fun c hc => ?_⟩
  · refine (mem_dotDual _ _ _).2 fun l hl => ?_
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha ((mem_dotDual _ _ _).1 hw l hl)
  · exact overlap (mseg y) s t hs ht (Γ s) (Γ t) (hΓ.2 t s ht hs) (hL t ht) w hw
  · exact (GlobalTheory.CompanionTheory.Ar.Num.DualLattice.locFree_dual _ (dotB Ω r) (dotB_bij Ω r) r (Γ c) _ (hL c hc)
      fun w => mem_dotDual _ _ w).1
