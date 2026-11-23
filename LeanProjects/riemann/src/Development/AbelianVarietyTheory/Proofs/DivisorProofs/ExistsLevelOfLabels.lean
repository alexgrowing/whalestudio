import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImHermFormPer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.LabelLevel

theorem perV_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (M N M' N' : Fin g → ℤ) :
    perV τ (M + M') (N + N') = perV τ M N + perV τ M' N' := by
  have h : ∀ a b : Fin g → ℤ, cv (a + b) = cv a + cv b := fun a b => funext fun i => by simp [cv]
  simp only [perV, h, Matrix.mulVec_add]
  abel

theorem perV_smul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (M N : Fin g → ℤ) :
    perV τ ((k : ℤ) • M) ((k : ℤ) • N) = (k : ℂ) • perV τ M N := by
  have h : ∀ a : Fin g → ℤ, cv ((k : ℤ) • a) = (k : ℂ) • cv a := fun a => funext fun i => by simp [cv]
  simp only [perV, h, Matrix.mulVec_smul, smul_add]

theorem prod_single {n k : ℕ} [NeZero k] (a : Fin n → ZMod k) :
    (List.ofFn fun i => (Multiplicative.ofAdd (Pi.single i 1 : Fin n → ZMod k)) ^ (a i).val).prod =
      Multiplicative.ofAdd a := by
  rw [List.prod_ofFn]
  simp only [← ofAdd_nsmul, ← ofAdd_sum]
  congr 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply, -ZMod.natCast_val, ZMod.natCast_zmod_val]

theorem exists_level_of_labels : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (k : ℕ), 0 < k → ∀ (ζ : ℂˣ), IsPrimitiveRoot ζ k → ∀ M Nn : (Fin (2 * g) → ZMod k) → Fin g → ℤ, ((∀ a a', ∃ M' N', M (a + a') = M a + M a' + (k : ℤ) • M' ∧ Nn (a + a') = Nn a + Nn a' + (k : ℤ) • N') ∧ (∀ a a' M' N', M a' = M a + (k : ℤ) • M' → Nn a' = Nn a + (k : ℤ) • N' → a = a') ∧ (∀ M₁ N₁, ∃ a M' N', M₁ = M a + (k : ℤ) • M' ∧ N₁ = Nn a + (k : ℤ) • N') ∧ ∀ i j, Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv (M (Pi.single i 1)) ⬝ᵥ cv (Nn (Pi.single j 1)) - cv (Nn (Pi.single i 1)) ⬝ᵥ cv (M (Pi.single j 1))) / k) = ((ζ ^ stdSymp g i j : ℂˣ) : ℂ)) → ∃ lev : Out.Level x.P k (unitOn ζ), ∀ a, (levelPoint lev hg a).left = (u.ex ((k : ℂ)⁻¹ • perV τ (M a) (Nn a))).left := by
  intro g x hg u τ a b c W hNF k hk ζ hζ M Nn ⟨hadd, _, _, hpair⟩
  subst hg
  obtain ⟨hs, hp, ha, hb, hc, hΛ, -, hfn, -⟩ := hNF
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have : NeZero k := ⟨hk.ne'⟩
  have hper : ∀ M' N', u.ex (perV τ M' N') = 1 := fun M' N' => (u.ker _).2 ((hΛ _).2 ⟨M', N', rfl⟩)
  let e : Multiplicative (Fin (2 * x.P.g) → ZMod k) →* (𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) :=
    MonoidHom.mk' (fun s => u.ex ((k : ℂ)⁻¹ • perV τ (M s.toAdd) (Nn s.toAdd))) (fun s t => by
      obtain ⟨M', N', h1, h2⟩ := hadd s.toAdd t.toAdd
      rw [toAdd_mul, h1, h2, perV_add, perV_add, perV_smul, smul_add, smul_add, inv_smul_smul₀ hk', u.ex_add,
        u.ex_add, hper, _root_.mul_one])
  let f : Multiplicative (Fin (2 * x.P.g) → ZMod k) →* (baseOver (Sp ℂ) ⟶ x.P.A) := e
  have hcv : ∀ M' N' : Fin x.P.g → ℤ, perV τ M' N' = GlobalTheory.KeyFam.per τ (Sum.elim N' M') := fun M' N' => by
    rw [perV, add_comm]; rfl
  obtain ⟨lev, hlev⟩ := GlobalTheory.Ex.FibIso.exists_level GlobalTheory.abelianSchemeLaws_all.1 x.P rfl hk' hζ
    (fun i => f (Multiplicative.ofAdd (Pi.single i 1)))
    (fun i => by
      rw [← map_pow, ← ofAdd_nsmul, ← f.map_one]
      congr 2
      funext j
      simp)
    (fun i j => by
      have h := GlobalTheory.WeilStd.weilIs_per x _ u τ a b c rfl hs hp ⟨ha, hb⟩ hc hΛ hfn k
        (Sum.elim (Nn (Pi.single i 1)) (M (Pi.single i 1))) (Sum.elim (Nn (Pi.single j 1)) (M (Pi.single j 1)))
        (ζ ^ stdSymp x.P.g i j) hk (by
          rw [← hpair i j]
          congr 2
          simp only [omegaStd, cv, dotProduct, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib]
          push_cast
          ring)
      rw [← hcv, ← hcv, show unitOn (ζ ^ stdSymp x.P.g i j) = unitOn ζ ^ stdSymp x.P.g i j from map_zpow _ _ _] at h
      exact h)
  refine ⟨lev, fun s => ?_⟩
  have h : levelPoint lev rfl s = f (Multiplicative.ofAdd s) := by
    rw [levelBasis_rfl] at hlev
    rw [levelPoint_rfl, Level.toPt, hlev, GlobalTheory.Ex.FibIso.linComb_map, prod_single]
  rw [h]
  rfl

end GlobalTheory.MBLow.LabelLevel

end
