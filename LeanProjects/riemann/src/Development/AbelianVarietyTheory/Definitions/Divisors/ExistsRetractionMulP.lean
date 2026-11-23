import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

set_option autoImplicit false

noncomputable section

open Coalgebra

namespace GlobalTheory.HTPair

open GlobalTheory.PDiv

structure QuotTower {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) : Type 1 where

  B : ℕ → Type
  [commRing : ∀ m, CommRing (B m)]
  [hopf : ∀ m, HopfAlgebra O (B m)]
  [cocomm : ∀ m, IsCocomm O (B m)]
  [finite : ∀ m, Module.Finite O (B m)]
  [projective : ∀ m, Module.Projective O (B m)]

  j : ∀ m, B m →ₐc[O] G.A (m + 1)

  ρ : ∀ m, G.A (m + 1) →ₗ[O] B m

  r : ∀ m, B (m + 1) →ₐc[O] B m

  s : ∀ m, G.A m →ₐc[O] B m

  ρ_j : ∀ m b, ρ m (j m b) = b

  r_surjective : ∀ m, Function.Surjective (r m)

  j_r : ∀ m b, j m (r m b) = G.res (m + 1) (j (m + 1) b)

  j_s : ∀ m a, j m (s m a) = G.mulP m a

  tors_le : ∀ m, torsionIdeal O (G.A (m + 1)) p ≤ kerIdeal (j m)

attribute [instance] QuotTower.commRing QuotTower.hopf QuotTower.cocomm QuotTower.finite
  QuotTower.projective

def IsInv {O A : Type} [CommRing O] [CommRing A] [HopfAlgebra O A]
    (Q : Subgroup (WithConv (A →ₐ[O] O))) (a : A) : Prop :=
  ∀ x : WithConv (A →ₐ[O] O), ∀ q ∈ Q, (x * q).ofConv a = x.ofConv a

def ptIdeal {O A : Type} [CommRing O] [CommRing A] [HopfAlgebra O A]
    (Q : Subgroup (WithConv (A →ₐ[O] O))) : Ideal A :=
  ⨅ q : Q, RingHom.ker q.1.ofConv

theorem isInv_bot {O A : Type} [CommRing O] [CommRing A] [HopfAlgebra O A] (a : A) :
    IsInv (⊥ : Subgroup (WithConv (A →ₐ[O] O))) a := fun x q hq => by
  rw [Subgroup.mem_bot.1 hq, mul_one]

def QuotTower.trivial {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) : QuotTower G where
  B m := G.A (m + 1)
  j _ := BialgHom.id O _
  ρ _ := LinearMap.id
  r m := G.res (m + 1)
  s m := G.mulP m
  ρ_j _ _ := rfl
  r_surjective m := G.res_surjective (m + 1)
  j_r _ _ := rfl
  j_s _ _ := rfl
  tors_le m := by
    rw [kerIdeal_of_surjective (f := BialgHom.id O (G.A (m + 1))) Function.surjective_id,
      ← kerIdeal_of_surjective (f := BialgHom.id O (G.A (m + 1))) Function.surjective_id]
    have h := kerIdeal_comp_of_surjective (mulBy O (G.A (m + 1)) p)
      (f := BialgHom.id O (G.A (m + 1))) Function.surjective_id
    rw [kerIdeal_of_surjective (f := BialgHom.id O (G.A (m + 1))) Function.surjective_id]
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    have ha' : counit (R := O) a = 0 := ha
    change counit (R := O) (mulBy O (G.A (m + 1)) p a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha']

theorem exists_retraction_mulP {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (m : ℕ) :
    ∃ ρ : G.A (m + 1) →ₗ[O] G.A m, ∀ a, ρ (G.mulP m a) = a := by
  let f : G.A m →ₗ[O] G.A (m + 1) := (G.mulP m : G.A m →ₐ[O] G.A (m + 1)).toLinearMap
  have hs : Function.Surjective f.dualMap := fun φ => by
    obtain ⟨ψ, hψ⟩ := G.dual_mulP_surjective m (WithConv.toConv φ)
    exact ⟨ψ.ofConv, congrArg WithConv.ofConv hψ⟩
  obtain ⟨σ, hσ⟩ := f.dualMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  refine ⟨(Module.evalEquiv O (G.A m)).symm.toLinearMap ∘ₗ σ.dualMap ∘ₗ
    (Module.evalEquiv O (G.A (m + 1))).toLinearMap, fun a => ?_⟩
  change (Module.evalEquiv O (G.A m)).symm _ = a
  rw [LinearEquiv.symm_apply_eq]
  ext φ
  exact LinearMap.congr_fun (LinearMap.congr_fun hσ φ) a

def QuotTower.full {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) : QuotTower G where
  B m := G.A m
  j m := G.mulP m
  ρ m := (exists_retraction_mulP G m).choose
  r m := G.res m
  s _ := BialgHom.id O _
  ρ_j m := (exists_retraction_mulP G m).choose_spec
  r_surjective := G.res_surjective
  j_r m b := by rw [G.mulP_res, G.res_mulP]
  j_s _ _ := rfl
  tors_le m := by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective m), G.mulP_comp_res]

theorem QuotTower.kerIdeal_full {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (m : ℕ) :
    kerIdeal ((QuotTower.full G).j m) = torsionIdeal O (G.A (m + 1)) p := by
  change kerIdeal (G.mulP m) = _
  rw [← kerIdeal_comp_of_surjective _ (G.res_surjective m), G.mulP_comp_res]

theorem QuotTower.map_res_kerIdeal {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O}
    (T : QuotTower G) (m : ℕ) :
    Ideal.map (G.res (m + 1) : G.A (m + 2) →ₐ[O] G.A (m + 1)) (kerIdeal (T.j (m + 1))) =
      kerIdeal (T.j m) := by
  have h : (G.res (m + 1)).comp (T.j (m + 1)) = (T.j m).comp (T.r m) :=
    BialgHom.ext fun b => (T.j_r m b).symm
  rw [← kerIdeal_comp, h, kerIdeal_comp_of_surjective (T.j m) (T.r_surjective m)]

theorem QuotTower.kerIdeal_full_mu_ne (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Nontrivial O] :
    kerIdeal ((QuotTower.full (PDivGroup.mu p O)).j 0) ≠ augIdeal O ((PDivGroup.mu p O).A 1) := by
  rw [QuotTower.kerIdeal_full]
  intro h
  have h1 : torsionIdeal O ((PDivGroup.mu p O).A 1) p ≤ RingHom.ker (AlgHom.id O _) :=
    (torsionIdeal_le_ker_iff p _).2 (by
      simpa using (PDivGroup.mu p O).pts_pow_self 1 (WithConv.toConv (AlgHom.id O _)))
  have h2 : muT O (p ^ 1) - 1 ∈ augIdeal O ((PDivGroup.mu p O).A 1) := by
    change counit (R := O) (muT O (p ^ 1) - 1) = 0
    rw [map_sub, (isGroupLikeElem_muT O _).counit_eq_one, Bialgebra.counit_one, sub_self]
  have h3 : muT O (p ^ 1) = 1 := sub_eq_zero.1 (h1 (h.ge h2))
  haveI : Fact (1 < p ^ 1) := ⟨by simpa using (Fact.out : p.Prime).one_lt⟩
  have h4 : (AddMonoidAlgebra.single (1 : ZMod (p ^ 1)) (1 : O)) = AddMonoidAlgebra.single 0 1 := h3
  exact one_ne_zero (AddMonoidAlgebra.single_left_injective one_ne_zero h4)

theorem ptIdeal_bot {O A : Type} [CommRing O] [CommRing A] [HopfAlgebra O A] :
    ptIdeal (⊥ : Subgroup (WithConv (A →ₐ[O] O))) = augIdeal O A := by
  ext a
  simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker, Subtype.forall, Subgroup.mem_bot,
    forall_eq]
  exact Iff.rfl

theorem isInv_algebraMap {O A : Type} [CommRing O] [CommRing A] [HopfAlgebra O A]
    (Q : Subgroup (WithConv (A →ₐ[O] O))) (c : O) : IsInv Q (algebraMap O A c) := by
  intro x q _
  simp

example {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (m : ℕ) :
    (QuotTower.full G).B m = G.A m := rfl

example {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (m : ℕ) (a : G.A m) :
    (QuotTower.full G).j m a = G.mulP m a := rfl

end GlobalTheory.HTPair
