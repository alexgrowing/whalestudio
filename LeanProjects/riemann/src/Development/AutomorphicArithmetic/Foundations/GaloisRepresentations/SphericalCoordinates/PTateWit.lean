import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

theorem tateWit_of : TateWit := by
  intro p _ D gb N S s o hX hL ρ D' t P x e hN hNp hU I hI
  classical
  obtain ⟨-, hper, hexp, hker, hact, hweil, heta⟩ := hU
  have hadd : ∀ z w, e (z + w) = e z * e w := hexp.1
  have hsurj : Function.Surjective e := hexp.2.1
  have hlin : ∀ (c : D.O) u, P (c • u) = ρ c *ᵥ P u := hper.1
  have hinj : Function.Injective P := hper.2.1
  haveI : Module.Free ℤ D.toG.La := D.freeLa
  have hlift : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ φ : D.La →+ D'.La, ∀ a, I.ev n a = e ((n : ℂ)⁻¹ • P (φ a)) :=
    fun n hn hnp => unifCls_lift e P hadd hsurj hker (I.ev n) (I.add n) hn
      (fun y => (I.onto n hn _).2 ⟨y, rfl⟩)
  have hroot : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ v : ℤ, IsCoprime v n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (v : ℂ) / n) :=
    fun n hn hnp => unifCls_root hn _ (I.ζ_prim n hn)
  let f : ℕ → D.La →+ D'.La := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hlift n hn.1 hn.2) else 0
  let nu : ℕ → ℤ := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hroot n hn.1 hn.2) else 0
  have hf : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) a, I.ev n a = e ((n : ℂ)⁻¹ • P (f n a)) := by
    intro n hn hnp a
    simp only [f, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hlift n hn hnp) a
  have hnu : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p), IsCoprime (nu n) n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) := by
    intro n hn hnp
    simp only [nu, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hroot n hn hnp)
  have heq : ∀ {n : ℕ}, 0 < n → ∀ v v' : D'.La,
      e ((n : ℂ)⁻¹ • P v) = e ((n : ℂ)⁻¹ • P v') ↔ ∃ w, v = v' + n • w :=
    fun hn v v' => unifCls_eq_iff e P hadd hker hinj hn v v'
  refine ⟨f, nu, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro n m hn hm hnm
    have hnp : n.Coprime p := (Nat.coprime_mul_iff_left.1 hnm).1
    refine ⟨?_, fun a => ?_⟩
    · have hz := I.ζ_pow n m hn hm
      have hz' := congrArg (fun u : ℂˣ => (u : ℂ)) hz
      simp only [Units.val_pow_eq_pow_val] at hz'
      rw [(hnu _ (Nat.mul_pos hn hm) hnm).2, (hnu n hn hnp).2, ← Complex.exp_nat_mul] at hz'
      have : (m : ℂ) * (-(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / ((n * m : ℕ) : ℂ)) =
          -(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / n := by
        have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
        push_cast; field_simp
      rw [this] at hz'
      exact (unifCls_exp_eq_iff hn _ _).1 hz'
    · have ht := I.tower n m hn hm a
      have e1 := hf _ (Nat.mul_pos hn hm) hnm a
      have e2 := hf n hn hnp a
      rw [e1, e2] at ht
      erw [unifCls_tower e P hadd hn hm] at ht
      exact (heq hn _ _).1 ht
  · intro n hn hnp
    refine ⟨(hnu n hn hnp).1, fun c a => ?_, fun a => ?_, fun a' => ?_, fun a a' => ?_⟩
    · have hl := I.lin n c a
      erw [hf n hn hnp (c • a), hf n hn hnp a] at hl
      have h3 := hact c ((n : ℂ)⁻¹ • P (f n a))
      rw [Matrix.mulVec_smul] at h3
      have h4 := hlin c (f n a)
      have h5 : e ((n : ℂ)⁻¹ • P (c • f n a)) = e ((n : ℂ)⁻¹ • P (f n a)) ≫ o.act.act c := by
        rw [h4]; exact h3
      exact (heq hn _ _).1 (hl.trans h5.symm)
    · have h1 := I.ker n hn a
      erw [hf n hn hnp a, unifCls_unit_iff e P hker hinj hn] at h1
      exact h1
    · obtain ⟨y, hy⟩ := (I.onto n hn (e ((n : ℂ)⁻¹ • P a'))).1 (unifCls_pow e P hadd hker hn a')
      rw [hf n hn hnp y] at hy
      obtain ⟨w, hw⟩ := (heq hn _ _).1 hy.symm
      exact ⟨y, w, hw⟩
    · have hiso := I.isom n hn a a'
      rw [hf n hn hnp a, hf n hn hnp a'] at hiso
      have hw := hweil n (f n a) (f n a')
        (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF (f n a) (f n a') : ℂ) / n)) (Complex.exp_ne_zero _))
        hn rfl
      have hu := GlobalTheory.T.weilPairing_complex_value_unique S o.A D.g o.ab hX _ hL x n _ _ _ _ hiso hw
      have hu' := congrArg (fun u : ℂˣ => (u : ℂ)) hu
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hu'
      rw [(hnu n hn hnp).2, ← Complex.exp_int_mul] at hu'
      have : ((2 * D.toG.EF a a' : ℤ) : ℂ) * (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) =
          -(2 * Real.pi * Complex.I) * ((nu n * (2 * D.toG.EF a a') : ℤ) : ℂ) / n := by
        push_cast; ring
      rw [this] at hu'
      exact (unifCls_exp_eq_iff hn _ _).1 hu'.symm
  · intro a
    have h3 : I.ev N a = e ((N : ℂ)⁻¹ • P (t a)) := (hI a).symm.trans (heta a)
    rw [hf N hN hNp a] at h3
    obtain ⟨w, hw⟩ := (heq hN _ _).1 h3
    exact ⟨w, hw⟩
  · intro n hn hnp a
    exact hf n hn hnp a

end UpperTheory.Gal.W2
