import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatDefs

noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW MvPolynomial

namespace SatP

section Proj

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}

def emb (s : Lt) : ℕ × Fin N0 → Lt × ℕ × Fin N0 := fun p => (s, p.1, p.2)

theorem emb_inj (s : Lt) : Function.Injective (emb (N0 := N0) s) := by
  intro a b h
  simp only [emb, Prod.mk.injEq] at h
  exact Prod.ext h.2.1 h.2.2

def res (s : Lt) (m : Lt × ℕ × Fin N0 →₀ ℕ) : ℕ × Fin N0 →₀ ℕ :=
  m.comapDomain (emb s) (emb_inj s).injOn

theorem res_apply (s : Lt) (m : Lt × ℕ × Fin N0 →₀ ℕ) (p : ℕ × Fin N0) :
    res s m p = m (emb s p) :=
  Finsupp.comapDomain_apply _ _ _ _

theorem res_sum (n : Lt → (ℕ × Fin N0 →₀ ℕ)) (t : Lt) :
    res t (∑ s, (n s).mapDomain (emb s)) = n t := by
  ext p
  rw [res_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · exact Finsupp.mapDomain_apply (emb_inj t) _ _
  · intro s _ hst
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    simp only [emb, Prod.mk.injEq] at hq
    exact hst hq.1
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem prod_rename_monomial (n : Lt → (ℕ × Fin N0 →₀ ℕ)) :
    ∏ s, rename (emb s) (monomial (n s) (1 : ℤ)) =
      monomial (∑ s, (n s).mapDomain (emb s)) 1 := by
  simp only [rename_monomial]
  rw [monomial_sum_one]

theorem nablaX_eq (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    nablaX N0 nu J = ∏ s, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c)) := by
  unfold nablaX minorX
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [AlgHom.map_det]
  congr 1
  ext i k
  simp [emb]

def Tmap (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ)) :
    MvPolynomial (Lt × ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  (basisMonomials (Lt × ℕ × Fin N0) ℤ).constr ℤ fun m =>
    ∏ s, rename (emb s) (π s (monomial (res s m) 1))

theorem Tmap_monomial (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ))
    (m : Lt × ℕ × Fin N0 →₀ ℕ) :
    Tmap π (monomial m 1) = ∏ s, rename (emb s) (π s (monomial (res s m) 1)) := by
  have : (monomial m (1 : ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℤ) =
      basisMonomials (Lt × ℕ × Fin N0) ℤ m := by
    rw [coe_basisMonomials]
  rw [this, Tmap, Module.Basis.constr_basis]

theorem Tmap_prod (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ))
    (h : Lt → MvPolynomial (ℕ × Fin N0) ℤ) :
    Tmap π (∏ s, rename (emb s) (h s)) = ∏ s, rename (emb s) (π s (h s)) := by
  suffices H : ∀ F : Finset Lt, ∀ h : Lt → MvPolynomial (ℕ × Fin N0) ℤ,
      (∀ s ∉ F, ∃ n, h s = monomial n 1) →
      Tmap π (∏ s, rename (emb s) (h s)) = ∏ s, rename (emb s) (π s (h s)) from
    H Finset.univ h (fun s hs => absurd (Finset.mem_univ s) hs)
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro h hh
    choose n hn using fun s => hh s (by simp)
    have : h = fun s => monomial (n s) 1 := funext hn
    subst this
    rw [prod_rename_monomial, Tmap_monomial]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [res_sum]
  | insert a F haF ih =>
    intro h hh
    have key : ∀ g : MvPolynomial (ℕ × Fin N0) ℤ,
        Tmap π (rename (emb a) g * ∏ s ∈ Finset.univ.erase a, rename (emb s) (h s)) =
          rename (emb a) (π a g) * ∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s)) := by
      let A : MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
        Tmap π ∘ₗ LinearMap.mulRight ℤ (∏ s ∈ Finset.univ.erase a, rename (emb s) (h s)) ∘ₗ
          (rename (emb a)).toLinearMap
      let B : MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
        LinearMap.mulRight ℤ (∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s))) ∘ₗ
          (rename (emb a)).toLinearMap ∘ₗ π a
      have hAB : A = B := by
        refine (basisMonomials (ℕ × Fin N0) ℤ).ext fun u => ?_
        rw [coe_basisMonomials]
        simp only [A, B, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
          AlgHom.toLinearMap_apply]
        have h1 := ih (Function.update h a (monomial u 1)) (by
          intro s hs
          by_cases hsa : s = a
          · subst hsa
            exact ⟨u, by simp⟩
          · rw [Function.update_of_ne hsa]
            exact hh s (by simp [hsa, hs]))
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
          ← Finset.mul_prod_erase _ (fun s => rename (emb s) (π s (Function.update h a (monomial u 1) s)))
            (Finset.mem_univ a)] at h1
        simp only [Function.update_self] at h1
        have e1 : ∏ s ∈ Finset.univ.erase a, rename (emb s) (Function.update h a (monomial u 1) s) =
            ∏ s ∈ Finset.univ.erase a, rename (emb s) (h s) :=
          Finset.prod_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        have e2 : ∏ s ∈ Finset.univ.erase a,
            rename (emb s) (π s (Function.update h a (monomial u 1) s)) =
            ∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s)) :=
          Finset.prod_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        rw [e1, e2] at h1
        exact h1
      intro g
      exact LinearMap.congr_fun hAB g
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase _ (fun s => rename (emb s) (π s (h s))) (Finset.mem_univ a)]
    exact key (h a)

theorem prod_mem_span (nu : Lt → YoungDiagram) (g : Lt → MvPolynomial (ℕ × Fin N0) ℤ)
    (hg : ∀ s, g s ∈ nablaSpan ℤ N0 (nu s)) :
    ∏ s, rename (emb s) (g s) ∈ Submodule.span ℤ (Set.range (nablaX N0 nu)) := by
  by_cases hne : Nonempty (ColChoice N0 nu)
  · obtain ⟨J0⟩ := hne
    suffices H : ∀ F : Finset Lt, ∏ s ∈ F, rename (emb s) (g s) ∈ Submodule.span ℤ
        (Set.range fun J : ColChoice N0 nu =>
          ∏ s ∈ F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c))) by
      have H1 := H Finset.univ
      have hf : (fun J : ColChoice N0 nu =>
          ∏ s, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c))) = nablaX N0 nu :=
        funext fun J => (nablaX_eq nu J).symm
      rw [hf] at H1
      exact H1
    intro F
    induction F using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact Submodule.subset_span ⟨J0, rfl⟩
    | insert a F haF ih =>
      rw [Finset.prod_insert haF]
      have ha : rename (emb a) (g a) ∈ Submodule.span ℤ (Set.range fun
          j : (∀ c : Fin ((nu a).rowLen 0), Fin ((nu a).colLen c) ↪o Fin N0) =>
            rename (emb a) (∏ c : Fin ((nu a).rowLen 0), minorX ℤ N0 ((nu a).colLen c) (j c))) := by
        have := Submodule.mem_map_of_mem (f := (rename (emb a)).toLinearMap) (hg a)
        rw [nablaSpan, Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hm := Submodule.mul_mem_mul ha ih
      rw [Submodule.span_mul_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨J, rfl⟩, rfl⟩
      change (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N0) at J
      refine ⟨Function.update J a j, ?_⟩
      show ∏ s ∈ insert a F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0),
          minorX ℤ N0 ((nu s).colLen c) (Function.update J a j s c)) =
        rename (emb a) (∏ c : Fin ((nu a).rowLen 0), minorX ℤ N0 ((nu a).colLen c) (j c)) *
          ∏ s ∈ F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0),
            minorX ℤ N0 ((nu s).colLen c) (J s c))
      rw [Finset.prod_insert haF, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun s hs => ?_
      have hsa : s ≠ a := fun h => haF (h ▸ hs)
      rw [Function.update_of_ne hsa]
  · have hex : ∃ s, IsEmpty (∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N0) := by
      by_contra hcon
      push Not at hcon
      exact hne ⟨fun s => (hcon s).some⟩
    obtain ⟨s, hs⟩ := hex
    have h0 : g s = 0 := by
      have := hg s
      rw [nablaSpan, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
      exact this
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (by rw [h0, map_zero])]
    exact Submodule.zero_mem _

end Proj

end SatP

open SatP in
theorem projZ : ProjZ := by
  intro hSB Lt _ _ N0 nu
  choose Cm hCm using fun s => hSB ℤ N0 (nu s)
  let π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ) := fun s =>
    (nablaSpan ℤ N0 (nu s)).subtype ∘ₗ Submodule.projectionOnto _ _ (hCm s)
  have hπmem : ∀ s x, π s x ∈ nablaSpan ℤ N0 (nu s) := fun s x =>
    (Submodule.projectionOnto _ _ (hCm s) x).2
  have hπfix : ∀ s x, x ∈ nablaSpan ℤ N0 (nu s) → π s x = x := fun s x hx => by
    simp only [π, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [Submodule.projectionOnto_apply_left (hCm s) ⟨x, hx⟩]
  refine ⟨Tmap π, fun P => ?_, fun J => ?_⟩
  · rw [MvPolynomial.as_sum P, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    have : monomial m (coeff m P) = coeff m P • monomial m (1 : ℤ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, LinearMap.map_smul, Tmap_monomial]
    exact Submodule.smul_mem _ _ (prod_mem_span nu _ fun s => hπmem s _)
  · rw [nablaX_eq, Tmap_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hπfix]
    exact Submodule.subset_span ⟨J s, rfl⟩

end GenFrameSpan
