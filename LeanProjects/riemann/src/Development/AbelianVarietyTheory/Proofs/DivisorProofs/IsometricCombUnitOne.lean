import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.ArInt GlobalTheory.Cartier

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsIntegral X] [IsLocallyNoetherian X] in

theorem isometric_comb_unit_one (M : HermLB p) :
    (comb (fun _ : Unit => M) fun _ => 1).Isometric M := by
  have e : (fun _ : Unit => (1 : ℤ)) = Pi.single () 1 := by
    funext u
    simp
  rw [e]
  exact isometric_comb_single (fun _ : Unit => M) ()

theorem arMix_pair (HM : Published.ArMix) (hX : IsArithVar p 1) {L M : HermLB p}
    {Φ : MvPolynomial (Option Unit) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option Unit => o.elim L fun _ => M) 1 Φ) {h : X → ℝ} (H : M.IsArithHeight h)
    (r : L.B.ι → X.functionFieldˣ) (hr : IsRatSec L.B r) :
    M.ArchIntegrable L 1 hr ∧
      Φ (MvPolynomial.X none * MvPolynomial.X (some ())) =
        ∑ᶠ z, ((L.div hr).mult z : ℝ) * h z - M.archInt L 1 hr := by
  have e := isometric_comb_unit_one M
  obtain ⟨h₁, h₂⟩ := HM k X p 1 hX Unit L (fun _ => M) Φ hΦ (fun _ => 1) h
    (e.symm.isArithHeight hX H) r hr
  have hl : MvPolynomial.rename some (lin fun _ : Unit => (((1 : ℤ) : ℤ) : ℝ)) ^ 1 =
      (MvPolynomial.X (some ()) : MvPolynomial (Option Unit) ℝ) := by
    simp [lin]
  rw [hl] at h₂
  refine ⟨fun σ => ?_, ?_⟩
  · rw [← e.chernIntegrableOn_eq σ 1]
    exact h₁ σ
  · have a : (comb (fun _ : Unit => M) fun _ => 1).archInt L 1 hr = M.archInt L 1 hr :=
      finsum_congr fun σ => congrFun (congrFun (e.chernInt_eq σ 1) _) _
    rw [h₂, a]

theorem isInter_iff (HE : Published.ArExists) (HM : Published.ArMix) (hX : IsArithVar p 1) {L M : HermLB p}
    {Φ : MvPolynomial (Option Unit) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option Unit => o.elim L fun _ => M) 1 Φ) (a : ℝ) :
    L.IsInter M a ↔ a = Φ (MvPolynomial.X none * MvPolynomial.X (some ())) := by
  constructor
  · rintro ⟨h, H, ha⟩
    obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
    rw [(ha r hr).2, (arMix_pair HM hX hΦ H r hr).2]
  · rintro rfl
    obtain ⟨h, H⟩ := (HE k X p 1 hX).1 M
    exact ⟨h, H, fun r hr => arMix_pair HM hX hΦ H r hr⟩

theorem isInter_of_comb (HE : Published.ArExists) (HM : Published.ArMix) (HI : Published.ArIso) (hX : IsArithVar p 1)
    {ι : Type} [Fintype ι] {T : ι → HermLB p} {Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΨ : IsArFun T 1 Ψ)
    {u v : ι → ℤ} {L M : HermLB p} (hu : (comb T u).Isometric L) (hv : (comb T v).Isometric M) :
    L.IsInter M (Ψ (lin (fun i => (u i : ℝ)) * lin fun i => (v i : ℝ))) := by
  have hΦ := ((HI k X p 1 hX).2 ι T Ψ hΨ).2.2 (Option Unit) (fun o => o.elim L fun _ => M)
    (fun o => o.elim u fun _ => v) (by rintro (_ | _); exacts [hu, hv])
  refine (isInter_iff HE HM hX hΦ _).2 ?_
  simp

theorem lin_add_int {ι : Type} [Fintype ι] (u v : ι → ℤ) :
    (lin fun i => (((u + v) i : ℤ) : ℝ)) = (lin fun i => (u i : ℝ)) + lin fun i => (v i : ℝ) := by
  simp [lin, add_mul, Finset.sum_add_distrib]

end GlobalTheory.HermLB

namespace GlobalTheory

theorem isInter_calculus : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X]
    [IsLocallyNoetherian X], IsArithVar p 1 → ∀ (L L' M : HermLB p), (∃ a, L.IsInter M a) ∧
      (∀ a, L.IsInter M a → M.IsInter L a) ∧
      (∀ a a', L.IsInter M a → L'.IsInter M a' → (L.tens L').IsInter M (a + a')) ∧
      ∀ a x y z, L.IsInter M a → L.IsSelfInter x → M.IsSelfInter y → (L.tens M).IsSelfInter z →
        z = x + 2 * a + y := by
  intro hC k _ X p _ _ hX L L' M
  have HE := hC.arExists
  have HM := hC.arMix
  have HI := hC.arIso
  let T : Fin 3 → HermLB p := ![L, L', M]
  obtain ⟨Ψ, hΨ⟩ := ((HE k X p 1 hX).2 (Fin 3) T).1
  let e : Fin 3 → Fin 3 → ℤ := fun i => Pi.single i 1
  have c₀ : (comb T (e 0)).Isometric L := isometric_comb_single T 0
  have c₁ : (comb T (e 1)).Isometric L' := isometric_comb_single T 1
  have c₂ : (comb T (e 2)).Isometric M := isometric_comb_single T 2
  have l (i : Fin 3) : (lin fun j => ((e i j : ℤ) : ℝ)) = MvPolynomial.X i := lin_single i
  have s₀₁ : (comb T (e 0 + e 1)).Isometric (L.tens L') :=
    (isometric_comb_add T _ _).trans (c₀.tens c₁)
  have s₀₂ : (comb T (e 0 + e 2)).Isometric (L.tens M) :=
    (isometric_comb_add T _ _).trans (c₀.tens c₂)
  have I₀ := HermLB.isInter_of_comb HE HM HI hX hΨ c₀ c₂
  have I₀' := HermLB.isInter_of_comb HE HM HI hX hΨ c₂ c₀
  have I₁ := HermLB.isInter_of_comb HE HM HI hX hΨ c₁ c₂
  have I₀₁ := HermLB.isInter_of_comb HE HM HI hX hΨ s₀₁ c₂
  rw [l, l] at I₀ I₀' I₁
  rw [HermLB.lin_add_int, l, l, l] at I₀₁
  refine ⟨⟨_, I₀⟩, fun a ha => ?_, fun a a' ha ha' => ?_, fun a x y z ha hx hy hz => ?_⟩
  · rw [ha.unique hX I₀, mul_comm]
    exact I₀'
  · rw [ha.unique hX I₀, ha'.unique hX I₁, ← map_add, ← add_mul]
    exact I₀₁
  · have S₀ := c₀.isSelfInter hX (hΨ.1 (e 0))
    have S₂ := c₂.isSelfInter hX (hΨ.1 (e 2))
    have S := s₀₂.isSelfInter hX (hΨ.1 (e 0 + e 2))
    rw [l] at S₀ S₂
    rw [HermLB.lin_add_int, l, l] at S
    rw [hx.unique hX S₀, hy.unique hX S₂, hz.unique hX S, ha.unique hX I₀]
    have E : (MvPolynomial.X 0 + MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ) ^ (1 + 1) =
        MvPolynomial.X 0 ^ (1 + 1) + (MvPolynomial.X 0 * MvPolynomial.X 2 + MvPolynomial.X 0 * MvPolynomial.X 2) +
          MvPolynomial.X 2 ^ (1 + 1) := by ring
    rw [E, map_add, map_add, map_add]
    ring

end GlobalTheory
