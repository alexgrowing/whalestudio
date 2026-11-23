import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.GlueBase

open GlobalTheory.IdemSupport (cP)

section Alg

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem split_prime {e a t t' : A} (ht : t' * t = 1) {y f : M} (hy : e • y = y) :
    y = e • (y - a • f) + (a * (e * t')) • (t • f) := by
  have key : a * (e * t') * t = e * a := by linear_combination (a * e) * ht
  rw [smul_sub, hy, smul_smul, smul_smul, key, sub_add_cancel]

theorem mem_of_mul_sub (S : Subring A) {b h t : A} (hb : b ∈ S) (h1 : b * h ∈ S) (h2 : h - t ∈ S) : b * t ∈ S := by
  have hd := S.sub_mem h1 (S.mul_mem hb h2)
  rwa [mul_sub, sub_sub_cancel] at hd

theorem mem_of_sub (S : Subring A) {a b : A} (ha : a ∈ S) (h : a - b ∈ S) : b ∈ S := by
  have hd := S.sub_mem ha h
  rwa [sub_sub_cancel] at hd

theorem idem_smul_smul {e : A} (he : e * e = e) (x : M) : e • e • x = e • x := by
  rw [smul_smul, he]

end Alg

variable {D : D7}

theorem inc_inv_mul (u : D.what₂.Word) : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (Tu_ne_zero u), map_one]

theorem cjA_inc_inv (u : D.what₂.Word) : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by
  rw [cjA_inc]
  congr 1
  simp [Tu, star_inv₀]

theorem hA_idem {X : HSp D} {e : EAf D} {y : Fin X.rank → EAf D} (hy : cjA D e • y = y) (x : Fin X.rank → EAf D) :
    hA X x y = hA X (e • x) y := by
  conv_lhs => rw [← hy]
  rw [hA_smul_right, hA_smul_left, cjA_cjA]

theorem isBasePair_of_isGlueVec (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (X : HSp D) (L₀ : Lat X)
    (f : Fin X.rank → EAf D) (hL : Submodule.IsLattice D.host.E L₀) (hf : IsGlueVec X u L₀ f) :
    IsBasePair X u π L₀ fun w => idem w • f := by
  have ht : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := inc_inv_mul u
  unfold IsBasePair
  refine ⟨hL, fun w e he hT y => ?_, fun w e he hπw => ?_⟩
  ·
    obtain rfl := eq_idem he
    have hinv : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hT
    simp only [InCmp]
    constructor
    · rintro ⟨hy, hey⟩
      exact ⟨(mem_hat_dualL_iff hL y).2 fun x hx => hf.int x hx y hy, hey⟩
    · rintro ⟨hy, hey⟩
      obtain ⟨a, ha, hya⟩ := hf.dual y ((mem_hat_dualL_iff hL y).1 hy)
      refine ⟨?_, hey⟩
      rw [split_prime (a := a) (f := f) ht hey]
      exact add_mem_hat (smul_mem_hat (idem_mem w) hya) (smul_mem_hat ((OA D).mul_mem ha hinv) hf.mul_mem)
  ·
    obtain rfl := eq_idem he
    have hTw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← pi_mul_cO hπ]
      exact w.asIdeal.mul_mem_right _ hπw
    have hnot : idem w * inc D (Tu D u)⁻¹ ∉ OA D := fun h => (idem_mul_inv_mem_iff u w).1 h hTw
    have hff : hA X f f - inc D (Tu D u)⁻¹ ∈ OA D := hf.norm
    refine ⟨idem_smul_smul (idem_mul_self w) f, ?_, ?_, ?_⟩
    · show inc D (Tu D u) • (idem w • f) ∈ hat L₀
      rw [smul_smul, mul_comm, ← smul_smul]
      exact smul_mem_hat (idem_mem w) hf.mul_mem
    ·
      intro hmem
      apply hnot
      refine mem_of_mul_sub (OA D) (idem_mem w) ?_ hff
      rw [← hA_smul_left, ← cjA_hA]
      exact cjA_mem (hf.pair _ hmem)
    · intro y
      simp only [InCmp]
      constructor
      · rintro ⟨hy, hey⟩
        refine ⟨hey, fun x hx => hf.int x hx.1 y hy, ?_⟩
        rw [hA_smul_left]
        exact (OA D).mul_mem (idem_mem w) (hf.pair y hy)
      · rintro ⟨hey, hx, hfy⟩
        have hdual : ∀ x ∈ hat L₀, hA X x y ∈ OA D := by
          intro x hx'
          rw [hA_idem hey]
          exact hx _ ⟨smul_mem_hat (idem_mem w) hx', idem_smul_smul (idem_mul_self w) x⟩
        obtain ⟨a, ha, hya⟩ := hf.dual y hdual
        refine ⟨?_, hey⟩
        have h1 : cjA D a * idem w * hA X f f ∈ OA D := by
          have hp : hA X (idem w • f) (a • f) ∈ OA D := by
            refine mem_of_sub (OA D) hfy ?_
            rw [← hA_sub_right, hA_smul_left]
            exact (OA D).mul_mem (idem_mem w) (hf.pair _ hya)
          rwa [hA_smul_left, hA_smul_right, ← mul_assoc, mul_comm (idem w)] at hp
        have h2 : cjA D a * idem w * inc D (Tu D u)⁻¹ ∈ OA D :=
          mem_of_mul_sub (OA D) ((OA D).mul_mem (cjA_mem ha) (idem_mem w)) h1 hff
        have h3 : a * (cjA D (idem w) * inc D (Tu D u)⁻¹) ∈ OA D := by
          have hc := cjA_mem h2
          rwa [map_mul, map_mul, cjA_cjA, cjA_inc_inv, mul_assoc] at hc
        rw [split_prime (a := a) (f := f) ht hey]
        exact add_mem_hat (smul_mem_hat (cjA_mem (idem_mem w)) hya) (smul_mem_hat h3 hf.mul_mem)

end GlobalTheory.AdIsom.GlueBase
