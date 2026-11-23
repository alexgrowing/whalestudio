import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.InfType

theorem inf_eq_one {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {χ : Formalism.L2.Host.HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : Formalism.L2.Host.HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (Formalism.L2.Host.infDiag k) = 1
  unfold Formalism.L2.Host.infDiag
  rw [MonoidHom.finset_prod_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    starRingEnd ℂ z / ((‖starRingEnd ℂ z‖ : ℝ) : ℂ) = (z / ((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [Complex.norm_conj, inv_div, div_eq_div_iff h1 hz, ← sq, ← Complex.mul_conj', mul_comm]

theorem delAt_inf {D : D7} (C : CharFrame D) (l : ℕ) (k : D.host.Eˣ) : (C.delAt l).inf k = 1 := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  unfold CharFrame.delAt
  split_ifs
  · obtain ⟨n, hn, h⟩ := C.isDel'.fin
    exact inf_eq_one hn h k
  · obtain ⟨n, hn, h⟩ := C.isDel.fin
    exact inf_eq_one hn h k

theorem toricLam0_hasInfinityType_conjRatio (D : D7) (Z : LamDat D) (hZ : Z.Ok) (l : ℕ) (j a : Fin D.R.m) (s : ℕ)
    (hs : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1) :
    (∀ g, 1 ≤ Z.kap j a s g) ∧
      GlobalTheory.CMVal.HasInf (Z.lam0 l j a) (phi D.host) (fun g => (Z.kap j a s g : ℤ) + s) := by
  have he : ∀ g, ∃ z : ℤ, eExp D j g = z := fun g => (D.hc _).e_int j
  choose e he using he
  have hpos : ∀ g, 1 ≤ e g + Z.c a g - s := fun g => by
    have h := hZ.big j a g
    rw [he] at h
    have h' : (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 < e g + Z.c a g := by exact_mod_cast h
    omega
  have hk : ∀ g, (Z.kap j a s g : ℤ) = e g + Z.c a g - s := fun g => by
    unfold LamDat.kap
    rw [he, Int.floor_intCast]
    exact Int.toNat_of_nonneg (by have := hpos g; omega)
  refine ⟨fun g => by have := hk g; have := hpos g; omega, fun k => ?_⟩
  obtain ⟨n, hn, h1⟩ := (Z.C.isMu0 j).inf
  obtain ⟨n', hn', h2⟩ := (hZ.aux a).inf
  unfold LamDat.lam0
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, delAt_inf, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, h1 k, h2 k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hz : embPsi D.host g (k : D.host.E) ≠ 0 := by simp
  have hu : embPsi D.host g (k : D.host.E) / ((‖embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero hz (by exact_mod_cast norm_ne_zero_iff.2 hz)
  have e1 : n g = 2 * -(e g) := by
    have := hn g
    simp only [he] at this
    exact_mod_cast this
  have e2 : n' g = 2 * Z.c a g := by
    have := hn' g
    beta_reduce at this
    exact_mod_cast this
  have e3 : phi D.host g (k : D.host.E) = starRingEnd ℂ (embPsi D.host g (k : D.host.E)) := rfl
  rw [e3, conj_div_norm hz, inv_zpow', ← zpow_neg, ← zpow_add₀ hu, e1, e2]
  congr 1
  beta_reduce
  rw [hk]
  ring

end GlobalTheory.LamTie.InfType
