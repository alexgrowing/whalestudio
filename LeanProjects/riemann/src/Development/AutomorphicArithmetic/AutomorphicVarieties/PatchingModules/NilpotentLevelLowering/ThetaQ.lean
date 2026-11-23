import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixPiIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dom_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (t : Fin n → kˣ) : ∃ a b : Fin n → kˣ, Dom a ∧ Dom b ∧ t = a * b⁻¹ := by
  have key : ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · exact ⟨1, fun _ _ i => h.elim i⟩
    obtain ⟨p, hp⟩ := Finite.exists_min (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
    set c : kˣ := t p.2 * (t p.1)⁻¹ with hc
    have h1 : valuation k (c : k) ≤ 1 := by simpa using hp (p.1, p.1)
    refine ⟨c, fun s hs i j hij => ?_⟩
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    have h2 : valuation k (s i : k) * valuation k (c : k) ≤ valuation k (s j : k) := by
      rcases hs with rfl | rfl
      · simpa using h1
      · have := mul_le_mul_right (hp (i, j)) (valuation k (s i : k))
        refine this.trans (le_of_eq ?_)
        rw [← map_mul, ← Units.val_mul]
        congr 2
        simp
    have hj := j.2
    have hlt' : (i : ℕ) < j := hlt
    have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
    rw [e]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
    rw [← mul_assoc]
    exact mul_le_mul' h2 (mul_le_of_le_one_right' (pow_le_one' h1 _))
  obtain ⟨c, hc⟩ := key
  refine ⟨t * (fun i : Fin n => c ^ (n - (i : ℕ))), (1 : Fin n → kˣ) * (fun i : Fin n => c ^ (n - (i : ℕ))),
    hc t (Or.inr rfl), hc 1 (Or.inl rfl), ?_⟩
  simp

private theorem comm_dc {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (φ : Module.End A M) (h : ∀ g, Commute φ (ρ g)) :
    Commute φ (dc ρ K K' x) :=
  finsum_induction (fun e => Commute φ e) (Commute.zero_right φ) (fun _ _ h1 h2 => h1.add_right h2) fun _ => h _

section

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ)

private theorem comm_at {j j' : Fin q} (h : j ≠ j') (g : GLw n (w j)) (g' : GLw n (w j')) :
    Commute (ρ (atJ n w j g)) (ρ (atJ n w j' g')) :=
  (Pi.mulSingle_commute (f := fun j => GLw n (w j)) h g g').map ρ

private theorem mem_UC (m : M) :
    m ∈ fixd ρ (UC n w C) ↔ ∀ j, m ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) :=
  by apply _root_.UpperTheory.Reformulated.B.Gr34.mem_UC <;> assumption

private theorem one_place (j : Fin q) (hq : IsUnit (qj w j : A)) :
    ∃ θ : (Fin n → ((w j).adicCompletion L)ˣ) →* (Module.End A (fixd ρ (UC n w C)))ˣ, ∀ t, Dom t →
      ∀ m : fixd ρ (UC n w C), ((θ t : Module.End A (fixd ρ (UC n w C))) m : M) =
        dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) m := by
  obtain ⟨hmul, hunit, -⟩ := domMul _ n (C j) A M (ρ.comp (atJ n w j))
  have happ : ∀ x (v : fixd (ρ.comp (atJ n w j)) (iwC _ n (C j))),
      (hk (ρ.comp (atJ n w j)) (iwC _ n (C j)) x v : M) =
        dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) x v := fun x =>
    (hkApply A _ M (ρ.comp (atJ n w j)) _ _ x ((heckePairIwC _ n (C j)).1 x)).1
  have hcomm : ∀ j', j' ≠ j → ∀ g x, Commute (ρ (atJ n w j' g))
      (dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) x) := fun j' h g x =>
    comm_dc _ _ _ _ _ fun g' => comm_at ρ h g g'
  have hpres : ∀ x, ∀ m ∈ fixd ρ (UC n w C),
      dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) x m ∈ fixd ρ (UC n w C) := by
    intro x m hm
    rw [mem_UC] at hm ⊢
    intro j'
    by_cases e : j' = j
    · subst e
      exact happ x ⟨m, hm _⟩ ▸ (hk (ρ.comp (atJ n w j')) (iwC _ n (C j')) x ⟨m, hm _⟩).2
    · intro u hu
      have h1 := LinearMap.congr_fun (hcomm j' e u x).eq m
      rw [Module.End.mul_apply, Module.End.mul_apply, show ρ (atJ n w j' u) m = m from hm j' u hu] at h1
      exact h1
  let f : (Fin n → ((w j).adicCompletion L)ˣ) → Module.End A (fixd ρ (UC n w C)) := fun t =>
    (dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t)).restrict (hpres _)
  have hf : ∀ t m, (f t m : M) =
    dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) m := fun _ _ => rfl
  have fmul : ∀ a b, Dom a → Dom b → f (a * b) = f a * f b := by
    intro a b ha hb
    ext m
    have h1 := congrArg Subtype.val (LinearMap.congr_fun (hmul a b ha hb) ⟨m, (mem_UC ρ C _).1 m.2 j⟩)
    rw [Module.End.mul_apply, happ, happ, happ] at h1
    exact h1.symm
  have funit : ∀ a, Dom a → IsUnit (f a) := by
    intro a ha
    obtain ⟨hi, hs⟩ := (Module.End.isUnit_iff _).1 (hunit hq a ha)
    refine (Module.End.isUnit_iff _).2 ⟨fun m m' h => ?_, fun m => ?_⟩
    · have := @hi ⟨m, (mem_UC ρ C _).1 m.2 j⟩ ⟨m', (mem_UC ρ C _).1 m'.2 j⟩ (Subtype.ext (by
        rw [happ, happ]; exact congrArg Subtype.val h))
      have h2 := congrArg Subtype.val this
      exact Subtype.ext h2
    · obtain ⟨v, hv⟩ := hs ⟨m, (mem_UC ρ C _).1 m.2 j⟩
      have hv' := congrArg Subtype.val hv
      rw [happ] at hv'
      refine ⟨⟨v, (mem_UC ρ C _).2 fun j' => ?_⟩, Subtype.ext hv'⟩
      by_cases e : j' = j
      · subst e
        exact v.2
      · intro u hu
        have hm : ρ (atJ n w j' u) v ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) := by
          intro g hg
          have h1 := LinearMap.congr_fun (comm_at ρ e u g).eq v
          rw [Module.End.mul_apply, Module.End.mul_apply, show ρ (atJ n w j g) v = v from v.2 g hg] at h1
          exact h1.symm
        have := @hi ⟨_, hm⟩ v (Subtype.ext (by
          rw [happ, happ]
          have h1 := LinearMap.congr_fun (hcomm j' e u (diagT _ (Fin n) a)).eq v
          rw [Module.End.mul_apply, Module.End.mul_apply, hv'] at h1
          rw [hv']
          exact h1.symm.trans ((mem_UC ρ C _).1 m.2 j' u hu)))
        exact congrArg Subtype.val this
  let P : Submonoid (Fin n → ((w j).adicCompletion L)ˣ) :=
    { carrier := {t | Dom t}
      one_mem' := dom_one
      mul_mem' := fun {a b} ha hb i j hij => by
        simp only [Pi.mul_apply, Units.val_mul, map_mul]
        exact mul_le_mul' (ha i j hij) (hb i j hij) }
  obtain ⟨θ, hθ, -⟩ := monoidExt _ _ P f (fun t => by
      obtain ⟨a, b, ha, hb, h⟩ := dom_gen t
      exact ⟨a, ha, b, hb, h⟩)
    (by
      have h := fmul 1 1 dom_one dom_one
      rw [mul_one] at h
      exact (funit 1 dom_one).mul_left_cancel (h.symm.trans (mul_one _).symm))
    (fun a ha b hb => fmul a b ha hb) (fun a ha => funit a ha)
  exact ⟨θ, fun t ht m => by rw [hθ t ht, hf]⟩

end

theorem UpperTheory.V.Pa.Lev.thetaQ :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ), (∀ j, IsUnit (qj w j : A)) → ∃ Θ, IsThetaQ ρ C Θ := by
  intro L _ _ n q w A M _ _ _ ρ C hq
  choose Θ hΘ using fun j => one_place ρ C j (hq j)
  refine ⟨Θ, hΘ, fun j j' t t' => ?_⟩
  by_cases e : j = j'
  · subst e
    exact (Commute.all t t').map _
  have hd : ∀ a b, Dom a → Dom b → Commute (Θ j a) (Θ j' b) := by
    intro a b ha hb
    refine Units.ext (LinearMap.ext fun m => Subtype.ext ?_)
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hΘ j a ha, hΘ j' b hb,
      hΘ j' b hb, hΘ j a ha]
    exact LinearMap.congr_fun (comm_dc _ _ _ _ _ fun g' =>
      (comm_dc _ _ _ _ _ fun g => comm_at ρ (Ne.symm e) g' g).symm).eq (m : M)
  obtain ⟨a, b, ha, hb, rfl⟩ := dom_gen t
  obtain ⟨c, d, hc, hd', rfl⟩ := dom_gen t'
  rw [map_mul, map_mul, map_inv, map_inv]
  exact ((hd a c ha hc).mul_right (hd a d ha hd').inv_right).mul_left
    ((hd b c hb hc).mul_right (hd b d hb hd').inv_right).inv_left
