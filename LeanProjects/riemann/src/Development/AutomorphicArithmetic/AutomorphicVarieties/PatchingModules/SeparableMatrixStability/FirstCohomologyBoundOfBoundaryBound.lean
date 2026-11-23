import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CoefficientsBoundedOfSelmerBoundary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelRed
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CoboundaryFirstSubsetSelmerFirst
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem card_submodule_mul_quotient_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (S B : Submodule A M)
    (hBS : (B : Set M) ⊆ S) (hS : (S : Set M).Finite) (I : Ideal A) (e : ℕ) (φ : (Fin e → A) → M)
    (hφ : ∀ c, φ c ∈ S) (hsub : ∀ c c', φ (c - c') = φ c - φ c') (hI : ∀ c, φ c ∈ B → ∀ i, c i ∈ I) :
    (B : Set M).ncard * Nat.card (A ⧸ I) ^ e ≤ (S : Set M).ncard := by
  haveI : Finite (S : Set M) := hS
  choose s hs using (Ideal.Quotient.mk_surjective (I := I))
  let f : ↥(B : Set M) × (Fin e → A ⧸ I) → ↥(S : Set M) := fun p =>
    ⟨φ (fun i => s (p.2 i)) + p.1, S.add_mem (hφ _) (hBS p.1.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hh
    have h1 : φ (fun i => s (c i)) + b = φ (fun i => s (c' i)) + b' := congrArg Subtype.val hh
    have h2 : φ ((fun i => s (c i)) - fun i => s (c' i)) ∈ B := by
      rw [hsub]
      have : φ (fun i => s (c i)) - φ (fun i => s (c' i)) = (b' : M) - b := by
        rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
      rw [this]
      exact B.sub_mem b'.2 b.2
    have h3 : c = c' := by
      funext i
      rw [← hs (c i), ← hs (c' i)]
      exact Ideal.Quotient.eq.2 (hI _ h2 i)
    subst h3
    exact Prod.ext (Subtype.ext (add_left_cancel h1)) rfl
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin e), Fintype.card_fin,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq] at this

theorem UpperTheory.V.Pa.firstCohomologyBound_of_boundaryBound :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (D0 : ℕ), TopFG G.Γ → FirstSelmerCardBoundAtAllLevels h k D0 → K1 h k D0 := by
  intro l _ L G G0 h n x k D0 hfg hB e z hz hind
  obtain ⟨C, hC⟩ := coefficients_bounded_of_selmer_boundary l L G G0 h n x k e z hfg hz hind
  obtain ⟨C', hC'⟩ := hB
  obtain ⟨⟨S0, hS0⟩, -⟩ := sel_lin l G.frame n x.A (DD x.A k.g) x.t (fun g => k.ρ1 x.A (h.p₀ g)) (k.w1 x.A)
    (k.wi1 x.A) (W1 n x.A x.A k.g x.a)
  have hS0' : (S0 : Set _) = Sel1 h x.A k := hS0
  have key : ∀ m, (m - C) * e ≤ m * D0 + C' := by
    intro m
    obtain ⟨⟨S, hS⟩, ⟨B, hB⟩⟩ := sel_lin l G.frame n x.A (DD (x.Am m) k.g) x.t (fun g => k.ρ1 (x.Am m) (h.p₀ g))
      (k.w1 (x.Am m)) (k.wi1 (x.Am m)) (W1 n x.A (x.Am m) k.g x.a)
    have hS' : (S : Set _) = Sel1 h (x.Am m) k := hS
    have hB' : (B : Set _) = Bd1 h (x.Am m) k := hB
    obtain ⟨hfin, hle⟩ := hC' m
    have hBS := coboundary_first_subset_selmer_first l L G G0 h n x k (x.Am m)
    rw [← hS'] at hfin hle hBS
    rw [← hB'] at hle hBS
    have hc := card_submodule_mul_quotient_le S B hBS hfin (Ideal.span {x.t ^ (m - C)}) e
      (fun c g => ((∑ i, c i • z i) g).map (x.redD k.g m))
      (fun c => by
        have h1 : (∑ i, c i • z i) ∈ Sel1 h x.A k := by
          rw [← hS0']
          exact S0.sum_mem fun i _ => S0.smul_mem _ (by rw [← SetLike.mem_coe, hS0']; exact hz i)
        have h2 := (sel_red l L G G0 h n x k x.A (x.Am m) (Ideal.Quotient.mkₐ x.A _)).2.1 _ h1
        rw [← hS'] at h2
        exact h2)
      (fun c c' => by
        funext g
        ext1 a b
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.map_apply, Matrix.sub_apply, map_sub])
      (fun c hc => hC m c (by rw [← hB']; exact hc))
    have hcard : Nat.card (x.A ⧸ Ideal.span {x.t ^ (m - C)}) = Nat.card x.K ^ (m - C) :=
      (am_fin l G0.frame n x (m - C) 0).2.1
    have hpos : 0 < Set.ncard (SetLike.coe B) := (Set.ncard_pos (hfin.subset hBS)).2 ⟨0, B.zero_mem⟩
    rw [hcard, ← pow_mul] at hc
    have h3 := Nat.le_of_mul_le_mul_left (hc.trans hle) hpos
    exact (Nat.pow_le_pow_iff_right (am_fin l G0.frame n x 0 0).2.2.2.2.2).1 h3
  by_contra hlt
  have h1 : D0 + 1 ≤ e := by omega
  have h2 := key (C + (C * D0 + C' + 1))
  rw [Nat.add_sub_cancel_left] at h2
  have h3 := (Nat.mul_le_mul_left (C * D0 + C' + 1) h1).trans h2
  nlinarith
