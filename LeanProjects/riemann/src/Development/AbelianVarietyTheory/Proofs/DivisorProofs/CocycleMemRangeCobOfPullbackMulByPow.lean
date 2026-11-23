import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulP

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem exists_injective_mulBy_pow_eq_comp_resOne (n : ℕ) : ∃ q : G.A 1 →ₐc[R] G.A (n + 1),
    Function.Injective q ∧ ∀ a, mulBy R _ (p ^ n) a = q (G.resOne n a) := by
  induction n with
  | zero =>
    refine ⟨BialgHom.id R _, Function.injective_id, fun a => ?_⟩
    rw [pow_zero, mulBy, pow_one]
    rfl
  | succ n ih =>
    obtain ⟨q, hq, hq'⟩ := ih
    refine ⟨(G.mulP (n + 1)).comp q, (Test.mulP_injective G (n + 1)).comp hq, fun a => ?_⟩
    rw [pow_succ', ← mulBy_mulBy, ← mulP_res, map_mulBy, hq']
    rfl

theorem mulBy_pow_zero_eq_id (n : ℕ) : mulBy R (G.A n) (p ^ 0) = BialgHom.id R _ := by
  rw [pow_zero, mulBy, pow_one]

theorem exists_cob_eq_mulBy_eq (c : G.cocycles) (B : G.funs)
    (hB : ∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) p) (c.1 n)) (h1 : B.1 1 = 0) :
    ∃ e : G.funs, G.cob e = c ∧ ∀ n, mulBy R _ p (e.1 n) = B.1 n := by
  have hlev : ∀ n, cobOne R _ (B.1 (n + 1)) = pullbackTwo (G.mulP n) (c.1 n) := by
    intro n
    rw [hB, ← mulP_comp_res, pullTwo_comp, (c.2 n).2]
  have hinv : ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ 1 := fun n =>
    G.transl_eq_of_cobOne_eq_pullTwo n _ _ (hlev n) (by rw [resOne_funs, h1])
  choose e he using fun n => G.exists_mulP_eq_of_transl_eq n (B.1 (n + 1)) (hinv n)
  have hres : ∀ n, G.res n (e (n + 1)) = e n := by
    intro n
    apply Test.mulP_injective G n
    rw [mulP_res, he n, ← B.2 (n + 1), ← he (n + 1), res_mulP]
  refine ⟨⟨e, hres⟩, Subtype.ext (funext fun n => ?_), fun n => ?_⟩
  · change cobOne R _ (e n) = c.1 n
    apply G.pullbackTwo_mulP_injective n
    rw [pullTwo_cobOne, he n, hlev n]
  · change mulBy R _ p (e n) = B.1 n
    rw [← res_mulP, he n, B.2 n]

theorem exists_cob_eq_mulBy_pow_eq [Fact p.Prime] (N : ℕ) : ∀ (c : G.cocycles) (B : G.funs),
    (∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c.1 n)) → B.1 N = 0 →
      ∃ e : G.funs, G.cob e = c ∧ ∀ n, mulBy R _ (p ^ N) (e.1 n) = B.1 n := by
  induction N with
  | zero =>
    intro c B hB _
    refine ⟨B, Subtype.ext (funext fun n => ?_), fun n => ?_⟩
    · change cobOne R _ (B.1 n) = c.1 n
      rw [hB n, mulBy_pow_zero_eq_id, pullTwo_id]
    · rw [mulBy_pow_zero_eq_id]
      rfl
  | succ N ih =>
    intro c B hB hN
    let c' : G.cocycles := cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c
    have hc' : ∀ n, c'.1 n = pullbackTwo (mulBy R (G.A n) p) (c.1 n) := fun n => by
      change pullbackTwo (Hom.app ((p : ℤ_[p]) • 𝟙 G) n) (c.1 n) = _
      rw [natCast_smul_id_app]
    have hB' : ∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c'.1 n) := fun n => by
      rw [hB n, hc' n, ← pullTwo_comp, pow_succ,
        show (mulBy R (G.A n) (p ^ N)).comp (mulBy R _ p) = mulBy R _ (p ^ N * p) from
          BialgHom.ext fun a => mulBy_mulBy _ _ a]
    obtain ⟨e', he', hm'⟩ := ih c' B hB' ((B.2 N).symm.trans (by rw [hN, map_zero]))
    have h1 : e'.1 1 = 0 := by
      obtain ⟨q, hq, hq'⟩ := G.exists_injective_mulBy_pow_eq_comp_resOne N
      apply hq
      rw [map_zero, ← G.resOne_funs e' N, ← hq', hm', hN]
    have hA : ∀ n, cobOne R _ (e'.1 n) = pullbackTwo (mulBy R (G.A n) p) (c.1 n) := fun n =>
      (congrArg (fun d : G.cocycles => d.1 n) he').trans (hc' n)
    obtain ⟨e, he, hm⟩ := G.exists_cob_eq_mulBy_eq c e' hA h1
    refine ⟨e, he, fun n => ?_⟩
    rw [pow_succ, ← mulBy_mulBy, hm, hm']

end PDivGroup

theorem cocycle_mem_range_cob_of_pullback_mulBy_pow :
    ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (G : PDivGroup p R) (N : ℕ) (c : G.cocycles)
      (B : ∀ n, G.A n), (∀ n, G.res n (B (n + 1)) = B n) →
      (∀ n, cobOne R (G.A n) (B n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c.1 n)) → B N = 0 →
        c ∈ LinearMap.range G.cob := by
  intro p _ R _ G N c B hB hc hN
  obtain ⟨e, he, -⟩ := G.exists_cob_eq_mulBy_pow_eq N c ⟨B, hB⟩ hc hN
  exact ⟨e, he⟩

end GlobalTheory
