import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobi
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.PrimOrth

section Key

variable {F : Type} [Field F]

def headSub (a n : ℕ) : Submodule F (Fin n → F) where
  carrier := {v | ∀ i : Fin n, a ≤ (i : ℕ) → v i = 0}
  add_mem' := by
    intro v w hv hw i hi
    simp [hv i hi, hw i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by
    intro c v hv i hi
    simp [hv i hi]

theorem mem_headSub {a n : ℕ} (v : Fin n → F) :
    v ∈ headSub a n ↔ ∀ i : Fin n, a ≤ (i : ℕ) → v i = 0 := Iff.rfl

def InParM (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0

theorem single_mem_headSub {a n : ℕ} (j : Fin n) (hj : (j : ℕ) < a) :
    (Pi.single j (1 : F) : Fin n → F) ∈ headSub a n := by
  rw [mem_headSub]
  intro i hi
  have : i ≠ j := by intro h; subst h; omega
  simp [Pi.single_apply, this]

theorem toLin'_apply_single {n : ℕ} (H : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    Matrix.toLin' H (Pi.single j 1) i = H i j := by
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem mapsTo_headSub {a n : ℕ} (M : Matrix (Fin n) (Fin n) F) (hM : InParM a M) :
    ∀ v ∈ headSub a n, Matrix.toLin' M v ∈ headSub a n := by
  intro v hv
  rw [mem_headSub] at hv ⊢
  intro i hi
  rw [Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : (j : ℕ) < a
  · rw [hM i j hj hi, zero_mul]
  · rw [hv j (by omega), mul_zero]

theorem entry_eq_zero {a n : ℕ} (H : Matrix (Fin n) (Fin n) F)
    (hH : Matrix.toLin' H ∈ nilRad (headSub a n)) (i j : Fin n) (hij : a ≤ (i : ℕ) ∨ (j : ℕ) < a) :
    H i j = 0 := by
  simp only [nilRad, Set.mem_setOf_eq] at hH
  rw [← toLin'_apply_single H i j]
  rcases hij with hi | hj
  · exact (mem_headSub _).1 (hH.1 _) i hi
  · rw [hH.2 _ (single_mem_headSub j hj)]; rfl

theorem neg_mem_nilRad {V : Type} [AddCommGroup V] [Module F V] {A : Submodule F V} {h : Module.End F V}
    (hh : h ∈ nilRad A) : -h ∈ nilRad A := by
  simp only [nilRad, Set.mem_setOf_eq] at hh ⊢
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · simpa using A.neg_mem (hh.1 x)
  · simp [hh.2 x hx]

theorem injective_add {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A : Submodule F V)
    (g h : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A) (hh : h ∈ nilRad A) (hinj : Function.Injective g) :
    Function.Injective (g + h) := by
  simp only [nilRad, Set.mem_setOf_eq] at hh
  obtain ⟨h1, h2⟩ := hh
  have hres : Function.Surjective (g.restrict hg) := by
    rw [← LinearMap.injective_iff_surjective]
    intro u w huw
    apply Subtype.ext; apply hinj
    have := congrArg Subtype.val huw
    simpa [LinearMap.restrict_apply] using this
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [LinearMap.add_apply] at hx
  have hgx : g x ∈ A := by
    have : g x = -(h x) := eq_neg_of_add_eq_zero_left hx
    rw [this]; exact A.neg_mem (h1 x)
  obtain ⟨u, hu⟩ := hres ⟨g x, hgx⟩
  have hgu : g u = g x := by
    have := congrArg Subtype.val hu
    simpa [LinearMap.restrict_apply] using this
  have hxA : x ∈ A := by rw [← hinj hgu]; exact u.2
  have hgx0 : g x = 0 := by rw [h2 x hxA, add_zero] at hx; exact hx
  exact hinj (by rw [hgx0, map_zero])

theorem isUnit_iff_injective {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit M ↔ Function.Injective (Matrix.toLin' M) := by
  rw [Matrix.isUnit_iff_isUnit_det, ← LinearMap.det_toLin', ← LinearMap.isUnit_iff_isUnit_det,
    Module.End.isUnit_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, LinearMap.injective_iff_surjective.1 h⟩⟩

theorem inParM_add_iff {a n : ℕ} (M H : Matrix (Fin n) (Fin n) F)
    (hH : Matrix.toLin' H ∈ nilRad (headSub a n)) : InParM a (M + H) ↔ InParM a M := by
  have hz : ∀ i j : Fin n, (j : ℕ) < a → H i j = 0 := fun i j hj => entry_eq_zero H hH i j (Or.inr hj)
  constructor
  · intro h i j hj hi
    have := h i j hj hi
    rwa [Matrix.add_apply, hz i j hj, add_zero] at this
  · intro h i j hj hi
    rw [Matrix.add_apply, hz i j hj, add_zero]
    exact h i j hj hi

theorem isUnit_add_iff {a n : ℕ} (M H : Matrix (Fin n) (Fin n) F)
    (hH : Matrix.toLin' H ∈ nilRad (headSub a n)) (hM : InParM a M) : IsUnit (M + H) ↔ IsUnit M := by
  rw [isUnit_iff_injective, isUnit_iff_injective, map_add]
  constructor
  · intro h
    have hM' : InParM a (M + H) := (inParM_add_iff M H hH).2 hM
    have := injective_add (headSub a n) (Matrix.toLin' M + Matrix.toLin' H) (-Matrix.toLin' H)
      (by rw [← map_add]; exact mapsTo_headSub _ hM') (neg_mem_nilRad hH) h
    simpa using this
  · intro h
    exact injective_add (headSub a n) _ _ (mapsTo_headSub M hM) hH h

theorem unitPar_add_iff {a n : ℕ} (M H : Matrix (Fin n) (Fin n) F)
    (hH : Matrix.toLin' H ∈ nilRad (headSub a n)) :
    (IsUnit (M + H) ∧ InParM a (M + H)) ↔ (IsUnit M ∧ InParM a M) := by
  rw [inParM_add_iff M H hH]
  constructor
  · rintro ⟨hu, hp⟩; exact ⟨(isUnit_add_iff M H hH hp).1 hu, hp⟩
  · rintro ⟨hu, hp⟩; exact ⟨(isUnit_add_iff M H hH hp).2 hu, hp⟩

theorem tl_add {a n : ℕ} (M H : Matrix (Fin n) (Fin n) F)
    (hH : Matrix.toLin' H ∈ nilRad (headSub a n)) : tl a (M + H) = tl a M := by
  ext i j
  simp only [tl, ent]
  split_ifs with h
  · rw [Matrix.add_apply, entry_eq_zero H hH _ _ (Or.inr j.2), add_zero]
  · rfl

end Key

theorem sum_inPar_psiG {F : Type} [Field F] [Finite F] (R : F[X] → ℂ) (hR : IsAdditive R) (a n : ℕ)
    (ha : 0 < a) (han : a < n) (α : GL (Fin a) F → ℂ) :
    ∑ᶠ p : GL (Fin n) F, (if InPar a p then α (tlG a p) else 0) * star (psiG R n p) = 0 := by
  classical
  haveI := Fintype.ofFinite F
  let ψ : Matrix (Fin n) (Fin n) F → ℂ := fun M => psi R (Fin n → F) (Matrix.toLin' M)
  let β : Matrix (Fin n) (Fin n) F → ℂ := fun M => α (toG (tl a M))
  let G : Matrix (Fin n) (Fin n) F → ℂ := fun M =>
    if IsUnit M ∧ InParM a M then β M * star (ψ M) else 0
  have stepA : ∑ᶠ p : GL (Fin n) F, (if InPar a p then α (tlG a p) else 0) * star (psiG R n p) =
      ∑ M, G M := by
    rw [finsum_eq_sum_of_fintype]
    have himg : (Finset.univ : Finset (GL (Fin n) F)).image (fun p : GL (Fin n) F => p.val) =
        Finset.univ.filter IsUnit := by
      ext M; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]; exact Iff.rfl
    have := Finset.sum_image (s := (Finset.univ : Finset (GL (Fin n) F)))
      (g := fun p : GL (Fin n) F => p.val)
      (f := fun M => (if InParM a M then β M else 0) * star (ψ M)) (fun x _ y _ h => Units.ext h)
    rw [himg, Finset.sum_filter] at this
    rw [show ∑ M, G M = ∑ M, if IsUnit M then (if InParM a M then β M else 0) * star (ψ M) else 0 from
      Finset.sum_congr rfl fun M _ => by simp only [G]; split_ifs <;> simp_all]
    rw [this]; rfl
  have hA0 : headSub (F := F) a n ≠ ⊥ := by
    intro h
    have hmem := single_mem_headSub (F := F) (⟨0, by omega⟩ : Fin n) ha
    rw [h, Submodule.mem_bot] at hmem
    have := congrFun hmem ⟨0, by omega⟩
    simp at this
  have hAtop : headSub (F := F) a n ≠ ⊤ := by
    intro h
    have hmem : (Pi.single (⟨a, han⟩ : Fin n) (1 : F) : Fin n → F) ∈ headSub a n := by rw [h]; trivial
    have := (mem_headSub _).1 hmem ⟨a, han⟩ le_rfl
    simp at this
  let Nfin : Finset (Matrix (Fin n) (Fin n) F) :=
    Finset.univ.filter (fun H => Matrix.toLin' H ∈ nilRad (headSub (F := F) a n))
  have hNcoe : (↑Nfin : Set (Matrix (Fin n) (Fin n) F)) = Matrix.toLin' ⁻¹' nilRad (headSub (F := F) a n) := by
    ext; simp [Nfin]
  have fiber : ∀ M, ∑ h ∈ Nfin, G (M + h) = 0 := by
    intro M
    by_cases hM : IsUnit M ∧ InParM a M
    · have e1 : ∀ h ∈ Nfin, G (M + h) = β M * star (ψ (M + h)) := by
        intro h hh
        have hh' : Matrix.toLin' h ∈ nilRad (headSub (F := F) a n) := (Finset.mem_filter.1 hh).2
        have hu : IsUnit (M + h) ∧ InParM a (M + h) := (unitPar_add_iff M h hh').2 hM
        simp only [G, if_pos hu, β, tl_add M h hh']
      have hprim := GlobalTheory.CuspGL.isPrimitive_psi F (Fin n → F) R hR (headSub a n) hA0 hAtop
        (Matrix.toLin' M) (mapsTo_headSub M hM.2)
      rw [← Set.image_preimage_eq (nilRad (headSub (F := F) a n)) Matrix.toLin'.surjective,
        finsum_mem_image (Matrix.toLin'.injective.injOn), ← hNcoe, finsum_mem_coe_finset] at hprim
      have e2 : ∑ h ∈ Nfin, β M * star (ψ (M + h)) = β M * star (∑ h ∈ Nfin, ψ (M + h)) := by
        rw [star_sum, Finset.mul_sum]
      rw [Finset.sum_congr rfl e1, e2]
      simp only [ψ, map_add]
      rw [hprim, star_zero, mul_zero]
    · refine Finset.sum_eq_zero fun h hh => ?_
      have hh' : Matrix.toLin' h ∈ nilRad (headSub (F := F) a n) := (Finset.mem_filter.1 hh).2
      simp only [G]
      rw [if_neg]
      rwa [unitPar_add_iff M h hh']
  have hshift : ∀ h, ∑ M, G (M + h) = ∑ M, G M := fun h =>
    Fintype.sum_equiv (Equiv.addRight h) _ _ (fun M => rfl)
  have h0 : (0 : Matrix (Fin n) (Fin n) F) ∈ Nfin := by
    have : Matrix.toLin' (0 : Matrix (Fin n) (Fin n) F) ∈ nilRad (headSub (F := F) a n) := by
      rw [map_zero]
      simp only [nilRad, Set.mem_setOf_eq, LinearMap.zero_apply]
      exact ⟨fun _ => Submodule.zero_mem _, fun _ _ => by trivial⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
  have hcard : (Nfin.card : ℂ) * ∑ M, G M = 0 := by
    calc (Nfin.card : ℂ) * ∑ M, G M = ∑ h ∈ Nfin, ∑ M, G M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ h ∈ Nfin, ∑ M, G (M + h) := Finset.sum_congr rfl fun h _ => (hshift h).symm
      _ = ∑ M, ∑ h ∈ Nfin, G (M + h) := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun M _ => fiber M
  have hne : (Nfin.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem h0)
  rw [stepA]
  exact (mul_eq_zero.1 hcard).resolve_left hne

end GlobalTheory.Shin.PrimOrth

namespace GlobalTheory.Shin.PrimOrth

theorem psiG_zero {F : Type} [Field F] (S : F[X] → ℂ) (x : GL (Fin 0) F) : psiG S 0 x = S 1 := by
  unfold psiG
  rw [psi_eq]
  have hc : LinearMap.charpoly (Matrix.toLin' (x : Matrix (Fin 0) (Fin 0) F)) = 1 := by
    apply Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    rw [LinearMap.charpoly_natDegree]; simp
  have he : IsEmpty {W : Submodule F (Fin 0 → F) // W ≠ ⊤ ∧
      ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin 0) (Fin 0) F) v ∈ W} := by
    refine ⟨fun W => W.2.1 (eq_top_iff.2 fun v _ => ?_)⟩
    rw [Subsingleton.elim v 0]; exact W.1.zero_mem
  rw [hc, finsum_of_isEmpty, sub_zero]

theorem gal_id {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem sum_hc_cusp {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (S : F[X] → ℂ)
    (hS : S 1 = 0) (n k a : ℕ) (ha : a < n) :
    ∑ᶠ x : GL (Fin n) F, hc a (n - a) (psiG S a) (fun _ => 1) n x * star (cusp θ n k x) = 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · have h0 : ∀ x : GL (Fin n) F, hc 0 n (psiG S 0) (fun _ => 1) n x = 0 := by
      intro x; simp [hc, hcTw, psiG_zero, hS]
    simp only [Nat.sub_zero, h0, zero_mul, finsum_zero]
  haveI := Fintype.ofFinite (GL (Fin n) F)
  have hcl := (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 1) (fun _ => 1)).2.2 (rootSum θ k)
  have hR := (GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  have key : ∀ y : GL (Fin n) F, ∑ x : GL (Fin n) F, (if InPar a (y⁻¹ * x * y) then
      psiG S a (tlG a (y⁻¹ * x * y)) * 1 else 0) * star (cusp θ n k x) = 0 := by
    intro y
    have e := Fintype.sum_equiv (MulAut.conj y⁻¹).toEquiv
      (fun x => (if InPar a (y⁻¹ * x * y) then psiG S a (tlG a (y⁻¹ * x * y)) * 1 else 0) * star (cusp θ n k x))
      (fun p => (if InPar a p then psiG S a (tlG a p) else 0) * star (cusp θ n k p)) (fun p => by
        have h2 : cusp θ n k (y⁻¹ * p * y) = cusp θ n k p := by
          unfold cusp; rw [hcl.1 p y]
        simp [MulAut.conj_apply, ← h2])
    rw [e]
    have L := sum_inPar_psiG (rootSum θ k) hR a n ha0 (by omega) (psiG S a)
    rw [finsum_eq_sum_of_fintype] at L
    simp only [cusp, star_mul']
    calc _ = star ((-1 : ℂ) ^ (n - 1)) * ∑ x : GL (Fin n) F, (if InPar a x then psiG S a (tlG a x) else 0) *
          star (psiG (rootSum θ k) n x) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [L, mul_zero]
  rw [finsum_eq_sum_of_fintype]
  have hx : ∀ x : GL (Fin n) F, hc a (n - a) (psiG S a) (fun _ => 1) n x =
      (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ * ∑ y : GL (Fin n) F,
        (if InPar a (y⁻¹ * x * y) then psiG S a (tlG a (y⁻¹ * x * y)) * 1 else 0) := by
    intro x; simp only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype]
  simp_rw [hx, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have := key y
  simp only [mul_one, mul_assoc] at this ⊢
  rw [this, mul_zero]

end GlobalTheory.Shin.PrimOrth

theorem GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ)
    (S : F[X] → ℂ) (n k : ℕ), S 1 = 0 →
    ∑ᶠ x, psiG S n x * star (cusp θ n k x) = ∑ᶠ x, chG S n x * star (cusp θ n k x) := by
  intro F _ _ θ S n k hS
  haveI := Fintype.ofFinite (GL (Fin n) F)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have hz : ∀ a ∈ Finset.range n, ∑ x : GL (Fin n) F,
      hc a (n - a) (psiG S a) (fun _ => 1) n x * star (cusp θ n k x) = 0 := by
    intro a ha
    have := GlobalTheory.Shin.PrimOrth.sum_hc_cusp θ S hS n k a (Finset.mem_range.1 ha)
    rwa [finsum_eq_sum_of_fintype] at this
  simp_rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ), Finset.sum_eq_zero hz, sub_zero]
