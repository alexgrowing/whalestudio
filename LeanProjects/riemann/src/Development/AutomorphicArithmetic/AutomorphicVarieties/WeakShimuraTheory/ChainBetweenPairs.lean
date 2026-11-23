import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChainMap

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Chn

section Abs

variable {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] {Φ : Fr O Γ} {a : O →+* k}

theorem rt_wt (h : Φ.Ok a) (i j : Fin 4) (g : Γ) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have h3 : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    have h0 : Φ.χ 0 g * Φ.χ 3 g = Φ.ν g := h.mul 0 g
    have h1 : Φ.χ 1 g * Φ.χ 2 g = Φ.ν g := h.mul 1 g
    rw [h1, ← h0, mul_inv_cancel_comm]
  show (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (wt i j).1 * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (wt i j).2 * Φ.χ j g = Φ.χ i g
  apply Additive.ofMul.injective
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, h3, wt, lamW, muW, ofMul_mul, ofMul_zpow, ofMul_inv,
      Matrix.cons_val] <;> module

theorem rt_ne (h : Φ.Ok a) : ∀ w ∈ roots, a (Φ.rt w Φ.g0) ≠ 1 := by
  intro w hw e
  have : ∃ i j, i ≠ j ∧ wt i j = w := by clear e; revert w; decide
  obtain ⟨i, j, hij, rfl⟩ := this
  have h1 := (h.dist i j hij).ne_zero
  rw [← rt_wt h i j, Units.val_mul, map_mul, e, one_mul, sub_self] at h1
  exact h1 rfl

theorem diag_ne {P : PD Φ.ι Γ k} (h : Φ.IsRes a P) (g : Γ) (i : Fin 4) : P.r g i i ≠ 0 := by
  rw [h.res.diag]; exact ((Φ.χ i g).isUnit.map a).ne_zero

theorem ps_zero {P : PD Φ.ι Γ k} (h : Φ.IsRes a P) (hs : Supp nP P.r) {g : Γ} (h0 : P.r g 2 0 = 0) : P.r g 3 1 = 0 := by
  have x01 := hs g 0 1 (by decide) (by decide)
  have x21 := hs g 2 1 (by decide) (by decide)
  have e' := congrFun (congrFun (h.pair.mult g) 3) 1
  simpa [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, x01, x21, h0, diag_ne h] using e'

theorem al_zero {P : PD Φ.ι Γ k} (h : Φ.IsRes a P) (hs : Supp nM P.r) {g : Γ} (h0 : P.r g 1 0 = 0) : P.r g 3 2 = 0 := by
  have x12 := hs g 1 2 (by decide) (by decide)
  have x02 := hs g 0 2 (by decide) (by decide)
  have e := congrFun (congrFun (h.pair.mult g) 1) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, x12, x02, h0, diag_ne h] using e

theorem ent_ps {P : PD Φ.ι Γ k} (h : Φ.IsRes a P) (hs : Supp nP P.r) : Ent P.r (-wPs) ↔ ∃ g, P.r g 2 0 ≠ 0 := by
  refine ⟨?_, fun ⟨g, hg⟩ => ⟨g, 2, 0, by decide, hg⟩⟩
  rintro ⟨g, i, j, hw, hg⟩
  have : i = 2 ∧ j = 0 ∨ i = 3 ∧ j = 1 := by clear hg; revert hw; revert i j; decide
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨g, hg⟩
  · exact ⟨g, fun h0 => hg (ps_zero h hs h0)⟩

theorem ent_al {P : PD Φ.ι Γ k} (h : Φ.IsRes a P) (hs : Supp nM P.r) : Ent P.r (-wAl) ↔ ∃ g, P.r g 1 0 ≠ 0 := by
  refine ⟨?_, fun ⟨g, hg⟩ => ⟨g, 1, 0, by decide, hg⟩⟩
  rintro ⟨g, i, j, hw, hg⟩
  have : i = 1 ∧ j = 0 ∨ i = 3 ∧ j = 2 := by clear hg; revert hw; revert i j; decide
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨g, hg⟩
  · exact ⟨g, fun h0 => hg (al_zero h hs h0)⟩

theorem samePs_ent {P P' : PD Φ.ι Γ k} (h : Φ.IsRes a P) (h' : Φ.IsRes a P') (hs : Supp nP P.r) (hs' : Supp nP P'.r)
    (e : P.SamePs P') : Ent P.r (-wPs) ↔ Ent P'.r (-wPs) := by
  simp only [ent_ps h hs, ent_ps h' hs', e.1]

theorem sameAl_ent {P P' : PD Φ.ι Γ k} (h : Φ.IsRes a P) (h' : Φ.IsRes a P') (hs : Supp nM P.r) (hs' : Supp nM P'.r)
    (e : P.SameAl P') : Ent P.r (-wAl) ↔ Ent P'.r (-wAl) := by
  simp only [ent_al h hs, ent_al h' hs', e.1]

theorem samePs_inV {P P' : PD Φ.ι Γ k} (h' : Φ.IsRes a P') (hs' : P'.In nP) (e : P.SamePs P') (hv : Fr.InV P) :
    Fr.InV P' := by
  refine ⟨fun g i j hij hw => ?_, fun v => ⟨hs'.2 v, e.2 v ▸ (hv.2 v).2⟩⟩
  have h0 : P'.r g 2 0 = 0 := (e.1 g).symm.trans (hv.1 g 2 0 (by decide) (by decide))
  have : wt i j ∉ nP ∨ i = 2 ∧ j = 0 ∨ i = 3 ∧ j = 1 := by revert hw; revert i j; decide
  rcases this with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hs'.1 g i j hij h1
  · exact h0
  · exact ps_zero h' hs'.1 h0

end Abs

section In

variable {ι Γ R : Type} [Group Γ] [CommRing R] {P P' : PD ι Γ R}

theorem qP (h : P.In qQ) : P.In nP :=
  ⟨fun g i j hij hw => h.1 g i j hij fun hq => hw (by revert hq; revert i j; decide), h.2⟩

theorem qM (h : Supp qQ P.r) : Supp nM P.r :=
  fun g i j hij hw => h g i j hij fun hq => hw (by revert hq; revert i j; decide)

theorem samePs_symm (h : P.SamePs P') : P'.SamePs P := ⟨fun g => (h.1 g).symm, fun v => (h.2 v).symm⟩

theorem sameAl_symm (h : P.SameAl P') : P'.SameAl P := ⟨fun g => (h.1 g).symm, fun v => (h.2 v).symm⟩

end In

section Map

variable {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R}

theorem pair_map {P : PD Φ.ι Γ R} (h : Φ.IsPair a P) (f : R →+* R') : Φ.IsPair (f.comp a) (P.map f) := by
  have cj : ∀ n X : M4 R, adj (n.map f) * X.map f * n.map f = (adj n * X * n).map f := fun n X => by
    rw [Matrix.map_mul, Matrix.map_mul, adj_map]
  refine ⟨fun g => gsp_map f (h.mult g), fun g hg => ?_, fun i j hij => ?_, fun v => ⟨?_, fun i => ?_, fun i j hij => ?_⟩,
    fun v s hs i j hij => ?_, fun v s hs i => ?_⟩
  · show (P.r g).map f = 1
    rw [h.kill g hg, Matrix.map_one _ (map_zero f) (map_one f)]
  · show f (P.r Φ.g0 i j) = 0
    rw [h.nrm hij, map_zero]
  · exact map_one f ▸ gsp_map f (h.low v).1
  · show f (P.n v i i) = 1
    rw [(h.low v).2.1, map_one]
  · show f (P.n v i j) = 0
    rw [(h.low v).2.2 i j hij, map_zero]
  · show (adj ((P.n v).map f) * (P.r s).map f * (P.n v).map f : M4 R') i j = 0
    rw [cj, Matrix.map_apply, h.flag v s hs i j hij, map_zero]
  · show (adj ((P.n v).map f) * (P.r s).map f * (P.n v).map f : M4 R') i i = 1
    rw [cj, Matrix.map_apply]
    exact (congrArg f (h.mu v s hs i)).trans (map_one f)

end Map

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

theorem res_mono (T : Tower D) {k : Type} [Field k] {a : c.O →+* k} {W W' : Finset ℕ} (h : W ⊆ W')
    {s : PD T.ι (G T.F Ω) k} (hs : (T.fr W).IsRes a s) : (T.fr W').IsRes a s := by
  refine ⟨⟨hs.pair.mult, fun g hg => hs.pair.kill g ?_, hs.pair.nrm, hs.pair.low, hs.pair.flag, hs.pair.mu⟩,
    ⟨hs.res.diag, hs.res.char, hs.res.shape⟩, hs.cont⟩
  obtain ⟨A, h1, h2, h3⟩ := hg
  exact ⟨A, fun p hp => h1 p (Finset.insert_subset_insert l h hp), h2, h3⟩

theorem red_zero (𝔞 : Amb l) (c : Coef l) : ∀ x ∈ maximalIdeal c.O, 𝔞.red c x = 0 := by
  intro x hx
  rw [RingHom.comp_apply, residue_eq_zero_iff]
  exact map_nonunit (𝔞.a c) x hx

theorem dies_mono {w : ℕ} {F F' : IntermediateField ℚ Ω} (h : F ≤ F') (hd : Dies l w F) : Dies l w F' :=
  fun θ h1 h2 => (IntermediateField.fixingSubgroup_antitone h).trans (hd θ h1 h2)

theorem seed_res (T : Tower D) (𝔞 : Amb l) {ι : PadicAlgCl l ≃+* ℂ} {c₁ : Coef l} {h : c.O ≤ c₁.O}
    {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPair ι h Q) : (T.fr ∅).IsRes (𝔞.red c) (Q.map (𝔞.red c₁)) := by
  have h1 : (T.fr ∅).IsRes ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O)) := by
    refine ⟨pair_map hQ.pair _, hQ.res, fun i j n => ?_⟩
    have h2 := (hQ.cont i j 1).comp (Ideal.Quotient.lift (maximalIdeal c₁.O ^ 1) (residue c₁.O)
      fun x hx => (residue_eq_zero_iff x).2 (by rwa [pow_one] at hx))
    exact h2.comp (Ideal.Quotient.mk ((⊥ : Ideal (ResidueField c₁.O)) ^ n))
  have h2 := (chainMap (T.fr ∅) _ (𝔞.j c₁) _).1.2 h1
  have e1 : (𝔞.j c₁).comp ((residue c₁.O).comp (inc h)) = 𝔞.red c :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c c₁ h x)
  rw [e1] at h2
  exact h2

end Gal

end UpperTheory.V.Ws.Chn
