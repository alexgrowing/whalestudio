import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceInfKerLeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.BadCount.Lift

open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ]

theorem isSplit_injective {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) : Function.Injective ι := by
  intro a b hab
  have := congrArg π hab
  rwa [h.1, h.1] at this

theorem inv_mul_mem_ker {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (γ : Γ) :
    (ι (π γ))⁻¹ * γ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, h.1, inv_mul_cancel]

theorem commute_single {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (x : MonoidAlgebra ℂ G)
    (r : Γ) (hr : r ∈ π.ker) (c : ℂ) :
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x) (MonoidAlgebra.single r c) := by
  refine MonoidAlgebra.induction_on (motive := fun x =>
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x) (MonoidAlgebra.single r c)) x ?_ ?_ ?_
  · intro m
    show _ * _ = _ * _
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, h.2 m r hr]
  · intro x y hx hy
    rw [map_add]
    exact hx.add_left hy
  · intro a x hx
    rw [map_smul]
    exact hx.smul_left a

theorem asAlgebraHom_map {V : Type} [AddCommGroup V] [Module ℂ V] (ι : G →* Γ)
    (ρ : Representation ℂ Γ V) (e : MonoidAlgebra ℂ G) :
    ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι e) =
      Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e := by
  refine MonoidAlgebra.induction_on (motive := fun e =>
    ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι e) =
      Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) e ?_ ?_ ?_
  · intro m
    simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]
  · intro x y hx hy
    rw [map_add, map_add, map_add, hx, hy]
  · intro a x hx
    rw [map_smul, map_smul, map_smul, hx]

variable [Fintype Γ]

def eR (π : Γ →* G) : MonoidAlgebra ℂ Γ :=
  ∑ r : π.ker, MonoidAlgebra.single (r : Γ) ((Nat.card π.ker : ℂ)⁻¹)

theorem coeff_map_mul_eR {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (x : MonoidAlgebra ℂ G)
    (γ : Γ) :
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x * eR π).coeff γ =
      x.coeff (π γ) * (Nat.card π.ker : ℂ)⁻¹ := by
  unfold eR
  rw [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  simp_rw [MonoidAlgebra.mul_single_apply]
  let r0 : π.ker := ⟨(ι (π γ))⁻¹ * γ, inv_mul_mem_ker h γ⟩
  have key : ∀ r : π.ker, (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x).coeff (γ * (r : Γ)⁻¹) =
      if r = r0 then x.coeff (π γ) else 0 := by
    intro r
    rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.coeff_mapDomain]
    split_ifs with hr
    · have : γ * (r : Γ)⁻¹ = ι (π γ) := by
        subst hr
        simp [r0]
      rw [this, Finsupp.mapDomain_apply (isSplit_injective h)]
    · apply Finsupp.mapDomain_notin_range
      rintro ⟨g, hg⟩
      apply hr
      have hr1 : π (r : Γ) = 1 := r.2
      have hg' : g = π γ := by
        have := congrArg π hg
        rwa [h.1, map_mul, map_inv, hr1, inv_one, mul_one] at this
      subst hg'
      apply Subtype.ext
      show (r : Γ) = (ι (π γ))⁻¹ * γ
      rw [hg]
      group
  simp_rw [key, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def comapEquiv {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G) :
    P × π.ker ≃ P.comap π where
  toFun x := ⟨ι x.1 * x.2, by
    have hr1 : π (x.2 : Γ) = 1 := x.2.2
    simp [Subgroup.mem_comap, h.1, hr1]⟩
  invFun γ := (⟨π γ, γ.2⟩, ⟨(ι (π γ))⁻¹ * γ, inv_mul_mem_ker h γ⟩)
  left_inv x := by
    have hr1 : π (x.2 : Γ) = 1 := x.2.2
    ext <;> simp [h.1, hr1]
  right_inv γ := by
    ext
    simp

theorem card_comap {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G) :
    Nat.card (P.comap π) = Nat.card P * Nat.card π.ker := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (comapEquiv h P)).symm

end GlobalTheory.BadCount.Lift

namespace GlobalTheory.BadCount.Lift

open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ]

theorem lvlIdem_comap [Fintype G] {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G)
    (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ) (hl : ∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) :
    Formalism.L2.DIV.lvlIdem (P.comap π) lamb =
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι (Formalism.L2.DIV.lvlIdem P lam) * eR π := by
  have hcard := card_comap h P
  simp only [Formalism.L2.DIV.lvlIdem, eR, map_sum, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single, Finset.sum_mul_sum, MonoidAlgebra.single_mul_single]
  rw [← Fintype.sum_prod_type' (f := fun (i : P) (j : π.ker) =>
    MonoidAlgebra.single (ι (i : G) * (j : Γ))
      ((Nat.card P : ℂ)⁻¹ * ((lam i⁻¹ : ℂˣ) : ℂ) * (Nat.card π.ker : ℂ)⁻¹))]
  refine (Fintype.sum_equiv (comapEquiv h P) _ _ (fun x => ?_)).symm
  have hr1 : π (x.2 : Γ) = 1 := x.2.2
  have hx : lamb ((comapEquiv h P) x)⁻¹ = lam x.1⁻¹ := by
    rw [hl]
    congr 1
    apply Subtype.ext
    simp [comapEquiv, h.1, hr1]
  simp only [hx, hcard, Nat.cast_mul, mul_inv]
  congr 1
  ring

end GlobalTheory.BadCount.Lift

open scoped Classical in

theorem GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit : ∀ (G Γ V : Type) [Group G] [Fintype G] [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G) (ι : G →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup G) (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ G) (b : Fin 2 → MonoidAlgebra ℂ G) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → (∀ k, b k * b k = b k) → (∀ k a, b k * a = a * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff 1 = (s k : ℂ) / (Nat.card P : ℂ)) → (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  intro G Γ V _ _ _ _ _ _ _ π ι h ρ P lam lamb hl H n e b s c hEmb hcard hidem hcent hsum hsupp hcoeff
  let ιA := MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι
  have hL := GlobalTheory.BadCount.Lift.lvlIdem_comap h P lam lamb hl
  have hR : (Nat.card π.ker : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hP : (Nat.card P : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hprod : ∀ k, ιA (b k) * Formalism.L2.DIV.lvlIdem (P.comap π) lamb =
      ιA (b k * Formalism.L2.DIV.lvlIdem P lam) * GlobalTheory.BadCount.Lift.eR π := by
    intro k
    rw [hL, map_mul, mul_assoc]
  have hco : ∀ k γ, (ιA (b k) * Formalism.L2.DIV.lvlIdem (P.comap π) lamb).coeff γ =
      (b k * Formalism.L2.DIV.lvlIdem P lam).coeff (π γ) * (Nat.card π.ker : ℂ)⁻¹ := by
    intro k γ
    rw [hprod]
    exact GlobalTheory.BadCount.Lift.coeff_map_mul_eR h _ γ
  have key := GlobalTheory.T.finrank_characterEigenspace_inf_ker_le Γ V ρ (P.comap π) lamb (fun k => (H k).comap π) n (ιA e) (fun k => ιA (b k)) s c
    hEmb hcard
    (fun k => by rw [← map_mul, hidem])
    (fun k => by
      rw [hL]
      refine Commute.mul_right ?_ ?_
      · exact Commute.map (show Commute (b k) (Formalism.L2.DIV.lvlIdem P lam) from hcent k _) ιA
      · unfold GlobalTheory.BadCount.Lift.eR
        refine Commute.sum_right _ _ _ (fun r _ => ?_)
        exact GlobalTheory.BadCount.Lift.commute_single h _ r r.2 _)
    (by rw [← map_one ιA, ← map_sub, hsum, map_sub, map_add, map_mul])
    (fun k γ hne => by
      rw [hco] at hne
      show π γ ∈ H k
      apply hsupp k
      intro h0
      apply hne
      rw [h0, zero_mul])
    (fun k => by
      rw [hco, map_one, hcoeff, GlobalTheory.BadCount.Lift.card_comap h P, Nat.cast_mul]
      field_simp)
  rwa [GlobalTheory.BadCount.Lift.asAlgebraHom_map] at key
