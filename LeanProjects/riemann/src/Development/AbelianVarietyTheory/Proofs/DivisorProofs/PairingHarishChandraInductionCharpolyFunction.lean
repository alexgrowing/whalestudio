import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.Mass

theorem gal_id (F : Type) [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem sum_comp_surj {G M : Type} [Group G] [Group M] [Fintype G] [Fintype M]
    (π : G →* M) (hs : Function.Surjective π) (g : M → ℂ) :
    ∑ h : G, g (π h) = ((Finset.univ.filter fun h : G => π h = 1).card : ℂ) * ∑ z : M, g z := by
  rw [← Finset.sum_fiberwise Finset.univ π (fun h => g (π h)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_congr rfl (fun h hh => by rw [(Finset.mem_filter.1 hh).2]), Finset.sum_const, nsmul_eq_mul,
    MonoidHom.card_fiber_eq_of_mem_range π (hs z) (hs 1)]

theorem aux (A B k N s : ℂ) (h : k * (A * B) ≠ 0) : A * B * ((k * (A * B))⁻¹ * (N * (k * s))) = N * s := by
  calc A * B * ((k * (A * B))⁻¹ * (N * (k * s))) = (k * (A * B)) * (k * (A * B))⁻¹ * (N * s) := by ring
    _ = N * s := by rw [mul_inv_cancel₀ h, one_mul]

theorem mass : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (S : F[X] → ℂ), (Nat.card (GL (Fin a) F) : ℂ) * (Nat.card (GL (Fin b) F) : ℂ) * ∑ᶠ x, hc a b α β n x * star (chG S n x) = (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y * star (S (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) := by
  intro F _ _ a b n hn α β S
  obtain ⟨H, π, hH, hsurj, hπ, -, hchar⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  have hcl : IsCl (chG S n) := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) a b n α β).2.2 S).2
  haveI : Fintype F := Fintype.ofFinite F
  set g : GL (Fin a) F × GL (Fin b) F → ℂ := fun z => α z.1 * β z.2 *
    star (S (Matrix.charpoly (z.1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (z.2 : Matrix (Fin b) (Fin b) F)))
    with hg
  have hT : ∀ y : GL (Fin n) F, ∑ x : GL (Fin n) F, (if InPar a (y⁻¹ * x * y) then
      α (tlG a (y⁻¹ * x * y)) * β (brG a b (y⁻¹ * x * y)) else 0) * star (chG S n x) = ∑ p : H, g (π p) := by
    intro y
    rw [Fintype.sum_equiv (MulAut.conj y⁻¹).toEquiv _
      (fun p => (if InPar a p then α (tlG a p) * β (brG a b p) else 0) * star (chG S n p))
      (fun x => by simp [MulAut.conj_apply, show ∀ x y, chG S n (y⁻¹ * x * y) = chG S n x from hcl])]
    have h1 : ∀ p : GL (Fin n) F, (if InPar a p then α (tlG a p) * β (brG a b p) else 0) * star (chG S n p)
        = if p ∈ H then α (tlG a p) * β (brG a b p) * star (chG S n p) else 0 := by
      intro p; rw [hH p]; split_ifs <;> simp
    simp only [h1]
    rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter (· ∈ H)) (p := (· ∈ H)) (by simp)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hg]
    rw [← hchar p, hπ p]
    rfl
  have hL : ∑ᶠ x, hc a b α β n x * star (chG S n x) = (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ *
      ∑ y : GL (Fin n) F, ∑ x : GL (Fin n) F, (if InPar a (y⁻¹ * x * y) then
      α (tlG a (y⁻¹ * x * y)) * β (brG a b (y⁻¹ * x * y)) else 0) * star (chG S n x) := by
    rw [finsum_eq_sum_of_fintype]
    simp only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, Finset.sum_mul]
  have hR : ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y * star (S (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) = ∑ z, g z := by
    simp only [finsum_eq_sum_of_fintype]
    rw [← Fintype.sum_prod_type']
  have hP : Nat.card {p : GL (Fin n) F // InPar a p} = Nat.card H :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => (hH x).symm))
  have hS := sum_comp_surj π hsurj g
  have hC := sum_comp_surj π hsurj (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_prod] at hC
  rw [hL, hR, hP]
  simp only [hT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hS]
  simp only [Nat.card_eq_fintype_card]
  have hne : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hC] at hne ⊢
  push_cast at hne ⊢
  exact aux _ _ _ _ _ hne

end GlobalTheory.Shin.Mass
