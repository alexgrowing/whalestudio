import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import GroundTheory.Brauer.TensorSimple
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

section DensityCentralizer

variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
  [Algebra.IsCentral F C] [IsSimpleRing C]

theorem exists_sum_mul_mul_eq_matrixUnit (n : ℕ) (hn : 0 < n) (hC : Module.finrank F C = n ^ 2)
    (γ : C) (hγ : (minpoly F γ).natDegree = n)
    (L : Type) [Field L] (ι : L →+* C) (hιinj : Function.Injective ι)
    (hι : ∀ z : C, z * γ = γ * z ↔ ∃ w, ι w = z) (r : ℕ) (e : Fin r → C)
    (he : ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) (i i' : Fin r) :
    ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → C), ∀ β : Fin r → L,
      ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i := by
  classical
  let S : Subalgebra F C := Subalgebra.centralizer F {γ}
  have memS : ∀ z : C, z ∈ S ↔ ∃ w, ι w = z := by
    intro z
    rw [← hι z]
    simp [S, Subalgebra.mem_centralizer_iff, eq_comm]
  have hιS : ∀ w, ι w ∈ S := fun w => (memS _).2 ⟨w, rfl⟩
  have hγS : γ ∈ S := (memS γ).2 ((hι γ).1 rfl)
  have hcomm : ∀ s t : C, s ∈ S → t ∈ S → s * t = t * s := by
    intro s t hs ht
    obtain ⟨a, rfl⟩ := (memS s).1 hs
    obtain ⟨b, rfl⟩ := (memS t).1 ht
    rw [← map_mul, ← map_mul, mul_comm]
  let j : L →+* S :=
    { toFun := fun w => ⟨ι w, hιS w⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hj : Function.Bijective j := by
    refine ⟨fun a b h => hιinj (congrArg Subtype.val h), fun s => ?_⟩
    obtain ⟨w, hw⟩ := (memS s).1 s.2
    exact ⟨w, Subtype.ext hw⟩
  haveI : IsSimpleRing S := IsSimpleRing.of_ringEquiv (RingEquiv.ofBijective j hj) inferInstance
  let Φ : S ⊗[F] Cᵐᵒᵖ →ₐ[F] Module.End F C :=
    (AlgHom.mulLeftRight F C).comp (Algebra.TensorProduct.map S.val (AlgHom.id F Cᵐᵒᵖ))
  have hΦ : ∀ (s : S) (b : Cᵐᵒᵖ) (x : C), Φ (s ⊗ₜ b) x = (s : C) * x * b.unop := by
    intro s b x
    simp [Φ, AlgHom.mulLeftRight_apply]
  have hΦinj : Function.Injective Φ :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain Φ.toRingHom).resolve_right
      (not_subsingleton _)

  have hWl : ∀ t : S ⊗[F] Cᵐᵒᵖ, ∀ (s : S) (x : C), Φ t ((s : C) * x) = (s : C) * Φ t x := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => intro s x; simp
    | tmul a b =>
      intro s x
      rw [hΦ, hΦ, ← mul_assoc, hcomm _ _ a.2 s.2, mul_assoc, mul_assoc, mul_assoc]
    | add t u ht hu =>
      intro s x
      simp only [map_add, LinearMap.add_apply, ht, hu, mul_add]
  let W : Submodule F (Module.End F C) :=
    { carrier := {f | ∀ (s : S) (x : C), f ((s : C) * x) = (s : C) * f x}
      add_mem' := by
        intro a b ha hb s x
        simp only [Set.mem_setOf_eq] at ha hb
        simp [ha s x, hb s x, mul_add]
      zero_mem' := by intro s x; simp
      smul_mem' := by
        intro c f hf s x
        simp only [Set.mem_setOf_eq] at hf
        simp [hf s x, mul_smul_comm] }
  have hrange : LinearMap.range Φ.toLinearMap ≤ W := by
    rintro _ ⟨t, rfl⟩
    exact hWl t

  let θ : (Fin r → S) →ₗ[F] C :=
    { toFun := fun β => ∑ k, (β k : C) * e k
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; simp [Finset.smul_sum, smul_mul_assoc] }
  have hθ : ∀ β, θ β = ∑ k, (β k : C) * e k := fun β => rfl
  have hθinj : Function.Injective θ := by
    intro a b hab
    let wa : Fin r → L := fun k => ((memS _).1 (a k).2).choose
    let wb : Fin r → L := fun k => ((memS _).1 (b k).2).choose
    have hwa : ∀ k, ι (wa k) = a k := fun k => ((memS _).1 (a k).2).choose_spec
    have hwb : ∀ k, ι (wb k) = b k := fun k => ((memS _).1 (b k).2).choose_spec
    have h1 : θ a = ∑ k, ι (wa k) * e k := by simp [hθ, hwa]
    have h2 : θ a = ∑ k, ι (wb k) * e k := by rw [hab]; simp [hθ, hwb]
    have := (he (θ a)).unique h1 h2
    funext k
    apply Subtype.ext
    rw [← hwa, ← hwb, this]
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨c, hc, -⟩ := he x
    exact ⟨fun k => ⟨ι (c k), hιS _⟩, by simp [hθ, hc]⟩
  let θe : (Fin r → S) ≃ₗ[F] C := LinearEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  have hθe : ∀ β, θe β = ∑ k, (β k : C) * e k := fun β => rfl
  have hθsmul : ∀ (s : S) (x : C), θe.symm ((s : C) * x) = fun k => s * θe.symm x k := by
    intro s x
    rw [θe.symm_apply_eq, hθe]
    conv_lhs => rw [← θe.apply_symm_apply x, hθe]
    simp [Finset.mul_sum, mul_assoc]

  have hdimC : Module.finrank F C = r * Module.finrank F S := by
    rw [← θe.finrank_eq, Module.finrank_pi_fintype]
    simp
  have hdS : n ≤ Module.finrank F S := by
    let γS : S := ⟨γ, hγS⟩
    have hmin : minpoly F γS = minpoly F γ := by
      have := minpoly.algHom_eq S.val Subtype.val_injective γS
      simpa [γS] using this.symm
    have := (linearIndependent_pow (K := F) γS).fintype_card_le_finrank
    simpa [hmin, hγ] using this
  have hsrc : Module.finrank F (S ⊗[F] Cᵐᵒᵖ) = Module.finrank F S * n ^ 2 := by
    rw [Module.finrank_tensorProduct, MulOpposite.finrank, hC]
  have hrk : Module.finrank F (LinearMap.range Φ.toLinearMap) = Module.finrank F S * n ^ 2 := by
    rw [LinearMap.finrank_range_of_inj hΦinj, hsrc]
  let Ψ : W →ₗ[F] (Fin r → Fin r → S) :=
    { toFun := fun f k => θe.symm ((f : Module.End F C) (e k))
      map_add' := by intro a b; funext k; simp
      map_smul' := by intro c a; funext k; simp }
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hfe : ∀ k, (f : Module.End F C) (e k) = 0 := by
      intro k
      have := congrFun hf k
      simpa [Ψ] using this
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨c, hc, -⟩ := he x
    rw [hc, map_sum]
    have hfW := f.2
    simp only [W, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hfW
    simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [show ι (c k) = ((⟨ι (c k), hιS _⟩ : S) : C) from rfl, hfW, hfe, mul_zero]
  have hW : Module.finrank F W ≤ r * (r * Module.finrank F S) := by
    have := LinearMap.finrank_le_finrank_of_injective hΨ
    simpa [Module.finrank_pi_fintype] using this
  have hrn : r ≤ n := by
    have h1 : r * n ≤ n * n := by
      calc r * n ≤ r * Module.finrank F S := Nat.mul_le_mul_left _ hdS
        _ = n * n := by rw [← hdimC, hC, sq]
    exact Nat.le_of_mul_le_mul_right h1 hn
  have hWeq : LinearMap.range Φ.toLinearMap = W := by
    apply Submodule.eq_of_le_of_finrank_le hrange
    rw [hrk]
    refine hW.trans ?_
    calc r * (r * Module.finrank F S) ≤ n * (n * Module.finrank F S) :=
          Nat.mul_le_mul hrn (Nat.mul_le_mul_right _ hrn)
      _ = Module.finrank F S * n ^ 2 := by ring

  let E : Module.End F C :=
    LinearMap.mulRight F (e i) ∘ₗ (S.val.toLinearMap ∘ₗ
      ((LinearMap.proj i' : (Fin r → S) →ₗ[F] S) ∘ₗ θe.symm.toLinearMap))
  have hE : ∀ x, E x = (θe.symm x i' : C) * e i := fun x => rfl
  have hEW : E ∈ W := by
    intro s x
    rw [hE, hE, hθsmul]
    simp [mul_assoc]
  rw [← hWeq] at hEW
  obtain ⟨t, ht⟩ := hEW
  have hrep : ∀ t : S ⊗[F] Cᵐᵒᵖ, ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → C),
      ∀ x, Φ t x = ∑ k, ι (l k) * x * c k := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | tmul a b =>
      obtain ⟨w, hw⟩ := (memS a).1 a.2
      exact ⟨1, fun _ => w, fun _ => b.unop, by intro x; simp [hΦ, hw]⟩
    | add t u ht hu =>
      obtain ⟨N₁, l₁, c₁, h₁⟩ := ht
      obtain ⟨N₂, l₂, c₂, h₂⟩ := hu
      exact ⟨N₁ + N₂, Fin.append l₁ l₂, Fin.append c₁ c₂, by
        intro x; simp [Fin.sum_univ_add, h₁, h₂]⟩
  obtain ⟨N, l, c, hlc⟩ := hrep t
  refine ⟨N, l, c, fun β => ?_⟩
  set x := ∑ i'', ι (β i'') * e i'' with hx
  have hsym : θe.symm x = fun k => ⟨ι (β k), hιS _⟩ := by
    rw [θe.symm_apply_eq, hθe]
  rw [← hlc, show Φ t x = E x from congrArg (fun f => f x) ht, hE, hsym]

end DensityCentralizer

theorem exists_sum_mul_mul_eq_matrixUnit_htGroup : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (r : ℕ) (e : Fin r → G.C),
    (∀ x : G.C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) → ∀ i i' : Fin r,
    ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → G.C), ∀ β : Fin r → L,
      ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i := by
  intro p _ G γ hγ L _ _ ι hinj hι r e he i i'
  exact exists_sum_mul_mul_eq_matrixUnit G.n G.n_pos G.rankC (γ : G.C) hγ L ι.toRingHom hinj hι r e he i i'

end GlobalTheory
