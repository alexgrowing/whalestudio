import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.DSIC

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem map_qminor {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) :
    f (qminor E a b u) = qminor (fun c d => f (E c d)) a b u := by
  simp only [qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp, Tm, map_add]
  split_ifs <;> simp

theorem qminor_mem {A : Type} [Ring A] [Algebra ℂ A] (T : Subalgebra ℂ A) {n t : ℕ}
    (E : Fin n → Fin n → A) (hE : ∀ c d, E c d ∈ T) (a b : Fin t → Fin n) (u : ℂ) : qminor E a b u ∈ T := by
  refine T.sum_mem fun σ _ => T.mul_mem (intCast_mem T _) (T.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine T.add_mem ?_ (hE _ _)
  split_ifs
  · exact T.algebraMap_mem _
  · exact T.zero_mem

section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def adjPairs (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Subalgebra ℂ (Pr V) where
  carrier := {p | ∀ x y, ⟪p.1 x, y⟫_ℂ = ⟪x, p.2.unop y⟫_ℂ}
  mul_mem' := fun {p q} hp hq x y => by
    show ⟪p.1 (q.1 x), y⟫_ℂ = ⟪x, q.2.unop (p.2.unop y)⟫_ℂ
    rw [hp, hq]
  add_mem' := fun {p q} hp hq x y => by
    show ⟪p.1 x + q.1 x, y⟫_ℂ = ⟪x, p.2.unop y + q.2.unop y⟫_ℂ
    rw [inner_add_left, inner_add_right, hp, hq]
  algebraMap_mem' := fun c x y => by
    show ⟪c • x, y⟫_ℂ = ⟪x, (starRingEnd ℂ c) • y⟫_ℂ
    rw [inner_smul_left, inner_smul_right]

def fstP (V : Type) [AddCommGroup V] [Module ℂ V] : Pr V →ₐ[ℂ] Module.End ℂ V :=
  { (RingHom.fst (Module.End ℂ V) (Module.End ℂ V)ᵐᵒᵖ : Pr V →+* Module.End ℂ V) with commutes' := fun _ => rfl }

theorem qdet_adj {n : ℕ} {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E)
    (hU : IsUnitary ε E) (w : ℂ) (x y : V) : ⟪qdet E w x, y⟫_ℂ = ⟪x, qdet E (star w) y⟫_ℂ := by
  let e : Fin n → ℤˣ := fun a => if ε a then 1 else -1
  let P : Fin n → Fin n → Pr V := fun a b => mkP (E a b) ((sgn ε a b : ℂ) • E b a)
  have hP : GlRel P := by
    intro a b c d
    have h1 := hE a b c d
    have h2 := hE d c b a
    refine Prod.ext ?_ (MulOpposite.unop_injective ?_)
    · show E a b * E c d - E c d * E a b = (if b = c then P a d else 0).1 - (if d = a then P c b else 0).1
      rw [h1]
      congr 1 <;> split_ifs <;> rfl
    · show ((sgn ε c d : ℂ) • E d c) * ((sgn ε a b : ℂ) • E b a) - ((sgn ε a b : ℂ) • E b a) * ((sgn ε c d : ℂ) • E d c) =
        ((if b = c then P a d else 0).2).unop - ((if d = a then P c b else 0).2).unop
      rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (sgn ε a b : ℂ), ← smul_sub, h2, smul_sub]
      congr 1
      · by_cases h : b = c
        · subst h
          simp only [if_true, P, mkP, MulOpposite.unop_op, sgn]
          congr 1
          cases ε a <;> cases ε b <;> cases ε d <;> simp
        · rw [if_neg h, if_neg (Ne.symm h), smul_zero]; rfl
      · by_cases h : d = a
        · subst h
          simp only [if_true, P, mkP, MulOpposite.unop_op, sgn]
          congr 1
          cases ε c <;> cases ε b <;> cases ε d <;> simp
        · rw [if_neg h, if_neg (Ne.symm h), smul_zero]; rfl
  have hs : ∀ a b, star (P a b) = (((e a * e b : ℤˣ) : ℤ) : Pr V) * P b a := by
    intro a b
    by_cases h : ε a = ε b
    · have : e a * e b = 1 := by simp only [e, h]; split_ifs <;> simp
      rw [this]
      simp only [Units.val_one, Int.cast_one, one_mul, P, sgn, h, if_true, Complex.ofReal_one, one_smul]
      rfl
    · have : e a * e b = -1 := by
        simp only [e]; revert h; cases ε a <;> cases ε b <;> simp
      rw [this]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul, P, sgn, h, Ne.symm h,
        if_false, Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul]
      show mkP (-E b a) (E a b) = mkP (-E b a) (- -E a b)
      rw [neg_neg]
  have h := Formalism.FourierDecayAlt.P.star_quantum_minor (Pr V) n n P e hP hs id id w
  rw [Int.units_mul_self] at h
  simp only [Units.val_one, Int.cast_one, one_mul] at h
  have hm := qminor_mem (adjPairs V) P (fun a b x y => by
    show ⟪E a b x, y⟫_ℂ = ⟪x, (sgn ε a b : ℂ) • E b a y⟫_ℂ
    rw [hU, inner_smul_right]) id id w x y
  have e1 : ∀ u, (qminor P id id u).1 = qdet E u := fun u => map_qminor (fstP V) P id id u
  have e2 : (qminor P id id w).2.unop = qdet E (star w) := by
    rw [← e1, ← h]; rfl
  rw [← e1, hm, e2]

end

theorem qminor_intertwine {V : Type} [AddCommGroup V] [Module ℂ V] {n t : ℕ} (τ : Module.End ℂ V)
    (E E' : Fin n → Fin n → Module.End ℂ V) (h : ∀ a b, τ * E a b = E' a b * τ) (a b : Fin t → Fin n) (u : ℂ) :
    τ * qminor E a b u = qminor E' a b u * τ := by
  simp only [qminor, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← (Int.cast_commute _ τ).eq, mul_assoc, mul_assoc]
  congr 1
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  induction List.finRange t with
  | nil => simp
  | cons k l ih =>
    have hk : τ * Tm E (u - k) (a (σ k)) (b k) = Tm E' (u - k) (a (σ k)) (b k) * τ := by
      simp only [Tm, mul_add, add_mul, h]
      split_ifs
      · rw [Algebra.commutes]
      · simp
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, hk, mul_assoc, ih, mul_assoc]

theorem capelli_spread : Spread := by
  intro n ε lam H _ _ σ S E hU hI hS v₀ h0 hv₀ v Y
  let c : ℂ → ℂ := fun Y => Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y
  let K : Submodule ℂ S :=
    { carrier := {x | ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) x = c Y • x}
      add_mem' := fun ha hb Y => by rw [map_add, ha Y, hb Y, smul_add]
      zero_mem' := fun Y => by simp
      smul_mem' := fun s x hx Y => by rw [map_smul, hx Y, smul_comm] }
  have hK : ∀ g ∈ PI.UpqRep.UJset ε, ∀ x ∈ K.map S.subtype, σ g x ∈ K.map S.subtype := by
    rintro g hg _ ⟨x, hx, rfl⟩
    let τ : Module.End ℂ S := (σ g : H →ₗ[ℂ] H).restrict (hS.stab g hg)
    have h1 : g⁻¹ * g = 1 := by
      have := PI.UpqRep.coeMatrix_left_inv ε g hg
      rw [Matrix.inv_eq_left_inv this, this]
    have hτ : ∀ a b, τ * E a b = Econj E g g⁻¹ a b * τ := by
      intro a b
      ext y
      have := hS.conj g hg a b y (τ y) rfl
      simp only [Econj, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
        Submodule.coe_smul]
      exact this
    refine ⟨τ x, fun Y => ?_, rfl⟩
    have := qminor_intertwine τ E _ hτ id id (Y + ((n : ℂ) - 1) / 2)
    have h2 := covariant_det_of_lin covariant_linear _ n E g g⁻¹ hS.gl h1 (mul_eq_one_comm.1 h1) (Y + ((n : ℂ) - 1) / 2)
    unfold qdet at h2
    rw [h2] at this
    have h3 := congrArg (fun T : Module.End ℂ S => T x) this
    simp only [Module.End.mul_apply] at h3
    rw [qdet, ← h3]
    have h4 := hx Y
    rw [qdet] at h4
    rw [h4, map_smul]
  have hcl : (K.map S.subtype).topologicalClosure = ⊤ := by
    refine (hI _ (K.map S.subtype).isClosed_topologicalClosure fun g hg x hx => ?_).resolve_left fun hb => h0 ?_
    · exact map_mem_closure (σ g).continuous hx (hK g hg)
    · have : (v₀ : H) ∈ (K.map S.subtype).topologicalClosure :=
        Submodule.le_topologicalClosure _ ⟨v₀, hv₀, rfl⟩
      rw [hb] at this
      exact Subtype.ext this
  set d : S := qdet E (Y + ((n : ℂ) - 1) / 2) v - c Y • v with hd
  have horth : (d : H) ∈ (K.map S.subtype)ᗮ := by
    rintro _ ⟨x, hx, rfl⟩
    show ⟪x, d⟫_ℂ = 0
    have h1 := qdet_adj hS.gl hS.unit (star Y + ((n : ℂ) - 1) / 2) x v
    have h2 : star (star Y + ((n : ℂ) - 1) / 2) = Y + ((n : ℂ) - 1) / 2 := by simp
    have h3 : starRingEnd ℂ (c (star Y)) = c Y := by simp [c, Formalism.QuantumDeterminants.capP]
    rw [h2, hx (star Y), inner_smul_left, h3] at h1
    rw [hd, inner_sub_right, inner_smul_right, h1, sub_self]
  rw [← Submodule.orthogonal_closure, hcl, Submodule.top_orthogonal_eq_bot] at horth
  exact sub_eq_zero.1 (Subtype.ext horth)

end CompanionTheory.D.DSIC
