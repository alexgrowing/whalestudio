import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.LB (resG_resG)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineQuot

theorem bijective_of_basis_unit {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (B' : Module.Basis (Fin 1) R M) (B : Module.Basis (Fin 1) R N)
    (f : M →ₗ[R] N) (u : Rˣ) (h : f (B' 0) = (u : R) • B 0) : Function.Bijective f := by
  have hsum (P : Type) [AddCommGroup P] [Module R P] (C : Module.Basis (Fin 1) R P) (m : P) :
      m = C.repr m 0 • C 0 := by
    conv_lhs => rw [← C.sum_repr m]
    simp
  constructor
  · refine (injective_iff_map_eq_zero f).2 fun m hm => ?_
    rw [hsum M B' m, map_smul, h, smul_smul] at hm
    have h1 : B'.repr m 0 * u = 0 := by
      simpa using congrArg (fun n => B.repr n 0) hm
    have h2 : B'.repr m 0 = 0 := (Units.mul_left_eq_zero u).1 h1
    rw [hsum M B' m, h2, zero_smul]
  · intro n
    refine ⟨(B.repr n 0 * ((u⁻¹ : Rˣ) : R)) • B' 0, ?_⟩
    rw [map_smul, h, smul_smul, mul_assoc, Units.inv_mul, mul_one, ← hsum N B n]

theorem gen_of_jointEpi : ∀ (T : Scheme.{0}) (L Q : T.Modules) (N : ℕ) (s : Fin (N + 1) → (L ⟶ Q)),
    IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s := by
  intro T L Q N s hL hQ hs x
  have := Abelian.hasFiniteBiproducts (C := T.Modules)
  let p : (⨁ fun _ : Fin (N + 1) => L) ⟶ Q := biproduct.desc s
  have hp : Epi p := (Preadditive.epi_iff_cancel_zero p).2 fun Z a ha => hs Z a fun j => by
    have := congrArg (biproduct.ι (fun _ : Fin (N + 1) => L) j ≫ ·) ha
    simpa [p] using this
  obtain ⟨U₁, e', -, hx₁, -, he'⟩ := hL.exists_affine (V := ⊤) (x := x) trivial
  obtain ⟨U₂, e, -, hx₂, h₂, he⟩ := hQ.exists_affine hx₁
  obtain ⟨W, hW, hxW, t, ht⟩ := exists_app_eq_of_epi p (e 0) hx₂
  have hW' : W ≤ U₁ := hW.trans h₂
  let u : Fin (N + 1) → Γ(L, W) := fun j => (biproduct.π (fun _ : Fin (N + 1) => L) j).app W t
  have hsum : ∑ j, (s j).app W (u j) = resM Q hW (e 0) := by
    rw [← ht]
    have hpd : p = ∑ j, biproduct.π (fun _ : Fin (N + 1) => L) j ≫ s j := biproduct.desc_eq
    let ev : ((⨁ fun _ : Fin (N + 1) => L) ⟶ Q) →+ Γ(Q, W) :=
      AddMonoidHom.mk' (fun φ => φ.app W t) fun _ _ => rfl
    have := map_sum ev (fun j => biproduct.π (fun _ : Fin (N + 1) => L) j ≫ s j) Finset.univ
    rw [← hpd] at this
    exact this.symm
  let B' := he'.basis hW'
  let B := he.basis hW
  let a : Fin (N + 1) → Γ(T, W) := fun j => B'.repr (u j) 0
  let c : Fin (N + 1) → Γ(T, W) := fun j => B.repr ((s j).app W (resM L hW' (e' 0))) 0
  have hone (P : Type) [AddCommGroup P] [Module Γ(T, W) P] (C : Module.Basis (Fin 1) Γ(T, W) P)
      (m : P) : m = C.repr m 0 • C 0 := by
    conv_lhs => rw [← C.sum_repr m]
    simp
  have hu (j : Fin (N + 1)) : u j = a j • resM L hW' (e' 0) := by
    rw [← IsFrame.basis_apply he' hW']; exact hone _ B' (u j)
  have hc (j : Fin (N + 1)) : (s j).app W (resM L hW' (e' 0)) = c j • resM Q hW (e 0) := by
    rw [← IsFrame.basis_apply he hW]; exact hone _ B _
  have hac : ∑ j, a j * c j = 1 := by
    have h1 : (∑ j, a j * c j) • B 0 = (1 : Γ(T, W)) • B 0 := by
      rw [one_smul, Finset.sum_smul]
      calc ∑ j, (a j * c j) • B 0 = ∑ j, (s j).app W (u j) :=
            Finset.sum_congr rfl fun j _ => by
              rw [hu, Scheme.Modules.Hom.app_smul, hc, smul_smul, IsFrame.basis_apply]
        _ = B 0 := by rw [hsum, IsFrame.basis_apply]
    simpa using congrArg (fun n => B.repr n 0) h1
  obtain ⟨j, hj⟩ : ∃ j, x ∈ T.basicOpen (c j) := by
    by_contra hno
    push_neg at hno
    have hmem (j : Fin (N + 1)) : T.presheaf.germ W x hxW (c j) ∈ IsLocalRing.maximalIdeal _ :=
      fun hu' => hno j ((T.mem_basicOpen (c j) x hxW).2 hu')
    have : T.presheaf.germ W x hxW (∑ j, a j * c j) ∈ IsLocalRing.maximalIdeal _ := by
      rw [map_sum]
      exact Ideal.sum_mem _ fun j _ => by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ (hmem j)
    rw [hac, map_one] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨j, T.basicOpen (c j), hj, fun V hV => ?_⟩
  have hVW : V ≤ W := hV.trans (T.basicOpen_le (c j))
  have hunit : IsUnit (resG T hVW (c j)) := by
    have h0 := (T.toRingedSpace.isUnit_res_basicOpen (c j)).map (resG T hV)
    have : resG T hV (resG T (T.basicOpen_le (c j)) (c j)) = resG T hVW (c j) := resG_resG _ _ _
    rw [← this]; exact h0
  have key : GlobalTheory.QCoh.appLinear (s j) V ((he'.basis (hVW.trans hW')) 0) =
      ((hunit.unit : Γ(T, V)ˣ) : Γ(T, V)) • (he.basis (hVW.trans hW)) 0 := by
    rw [IsUnit.unit_spec, GlobalTheory.QCoh.appLinear_apply, IsFrame.basis_apply, IsFrame.basis_apply,
      ← resM_resM hW' hVW, app_resM, hc, resM_smul, resM_resM]
  have hb := bijective_of_basis_unit (R := Γ(T, V)) _ _ _ _ key
  exact hb

end GlobalTheory.LineQuot

end
