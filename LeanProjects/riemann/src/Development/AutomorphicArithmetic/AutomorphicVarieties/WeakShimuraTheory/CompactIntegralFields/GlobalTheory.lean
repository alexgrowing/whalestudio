import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.LineM

variable {k : Type} [Field k]

private def GlobalTheory (X : M4 k) : Prop := ∀ i j : Fin 4, (i.1 < 2 ∨ 2 ≤ j.1) → X i j = 0

private def Par (X : M4 k) : Prop := ∀ i j : Fin 4, i.1 < 2 → 2 ≤ j.1 → X i j = 0

private noncomputable def comb (A B : M4 k) : M4 k[X] := Matrix.of fun i j => C (A i j) + X * C (B i j - A i j)

private theorem comb_apply (A B : M4 k) (i j : Fin 4) : comb A B i j = C (A i j) + X * C (B i j - A i j) := rfl

private theorem comb_eq (A B : M4 k) : comb A B = A.map C + (X : k[X]) • (B - A).map C := by
  ext1 i j; simp [comb_apply]

private theorem blk_mul {A B : M4 k} (hA : GlobalTheory A) (hB : GlobalTheory B) : A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l.1 2 with h | h
  · rw [hB l j (Or.inl h), mul_zero]
  · rw [hA i l (Or.inr h), zero_mul]

private theorem blk_par {A B : M4 k} (hA : GlobalTheory A) (hB : Par B) : GlobalTheory (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases hij with h | h
  · rw [hA i l (Or.inl h), zero_mul]
  rcases lt_or_ge l.1 2 with h' | h'
  · rw [hB l j h' h, mul_zero]
  · rw [hA i l (Or.inr h'), zero_mul]

private theorem par_blk {A B : M4 k} (hA : Par A) (hB : GlobalTheory B) : GlobalTheory (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases hij with h | h
  · rcases lt_or_ge l.1 2 with h' | h'
    · rw [hB l j (Or.inl h'), mul_zero]
    · rw [hA i l h h', zero_mul]
  · rw [hB l j (Or.inr h), mul_zero]

private theorem blk_sub_mul {A B A' B' : M4 k} (hA : Par A) (hB' : Par B') (h : GlobalTheory (B - A)) (h' : GlobalTheory (B' - A')) :
    GlobalTheory (B * B' - A * A') := by
  have e : B * B' - A * A' = (B - A) * B' + A * (B' - A') := by noncomm_ring
  intro i j hij
  rw [e, Matrix.add_apply, blk_par h hB' i j hij, par_blk hA h' i j hij, add_zero]

private theorem comb_mul {A B A' B' : M4 k} (h : GlobalTheory (B - A)) (h' : GlobalTheory (B' - A')) :
    comb A B * comb A' B' = comb (A * A') (B * B') := by
  have h0 := blk_mul h h'
  have e : B * B' - A * A' = (B - A) * A' + A * (B' - A') + (B - A) * (B' - A') := by noncomm_ring
  rw [h0, add_zero] at e
  have h1 : ((B - A).map C : M4 k[X]) * (B' - A').map C = 0 := by
    rw [← Matrix.map_mul, h0]; ext1 i j; simp
  simp only [comb_eq]
  rw [e, Matrix.map_add _ (fun a b => map_add C a b), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h1, smul_zero, add_zero, smul_add]
  abel

private theorem adj_comb (A B : M4 k) : adj (comb A B) = comb (adj A) (adj B) := by
  ext1 i j
  simp only [adj_apply, comb_apply, zsmul_eq_mul, map_sub, map_mul, map_intCast]
  ring

private theorem blk_adj {A B : M4 k} (h : GlobalTheory (B - A)) : GlobalTheory (adj B - adj A) := by
  intro i j hij
  have := h j.rev i.rev (by simp only [Fin.val_rev]; omega)
  rw [Matrix.sub_apply] at this ⊢
  rw [adj_apply, adj_apply, ← smul_sub, this, smul_zero]

private theorem par_adj {A : M4 k} (h : Par A) : Par (adj A) := by
  intro i j hi hj
  rw [adj_apply, h j.rev i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega), smul_zero]

private theorem comb_same {A B : M4 k} {i j : Fin 4} {x : k} (hA : A i j = x) (hB : B i j = x) :
    comb A B i j = C x := by
  simp [comb_apply, hA, hB]

private theorem comb_gsp {A B : M4 k} {ν : k} (h : GlobalTheory (B - A)) (hA : IsGSp ν A) (hB : IsGSp ν B) :
    IsGSp (C ν) (comb A B) := by
  unfold IsGSp at *
  rw [adj_comb, comb_mul (blk_adj h) h, hA, hB]
  ext1 i j
  rw [comb_same rfl rfl]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem e32 {A : M4 k} {ν : k} (hA : IsGSp ν A) (lo : ∀ i j, i < j → A i j = 0) :
    A 3 2 * A 0 0 + A 2 2 * A 1 0 = 0 := by
  have := congrFun (congrFun hA 1) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, lo 1 2 (by decide), lo 0 2 (by decide)] using this

private theorem blk_of {A B : M4 k} {ν : k} (hA : IsGSp ν A) (hB : IsGSp ν B) (lA : ∀ i j, i < j → A i j = 0)
    (lB : ∀ i j, i < j → B i j = 0) (d : ∀ i, A i i = B i i) (d0 : A 0 0 ≠ 0) (e : A 1 0 = B 1 0) : GlobalTheory (B - A) := by
  have h32 : B 3 2 = A 3 2 := by
    have h1 := e32 hA lA
    have h2 := e32 hB lB
    rw [← d, ← d, ← e] at h2
    exact mul_right_cancel₀ d0 (by linear_combination h2 - h1)
  intro i j hij
  rw [Matrix.sub_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [lA i j h, lB i j h, sub_zero]
  · subst h; rw [d, sub_self]
  · have : (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by revert i j; decide
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e, sub_self]
    · rw [h32, sub_self]

private theorem low_of {A : M4 k} (h : SuppM nM A) : ∀ i j, i < j → A i j = 0 := fun i j hij =>
  h i j hij.ne (by revert i j; decide)

private theorem par_of {A : M4 k} (h : ∀ i j, i < j → A i j = 0) : Par A := fun i j hi hj =>
  h i j (by rw [Fin.lt_def]; omega)

private theorem lc_of {Γ : Type} [TopologicalSpace Γ] {f : Γ → k} (h : AdicCont (⊥ : Ideal k) f) :
    IsLocallyConstant f := by
  have h1 := h 1
  refine IsLocallyConstant.desc f _ h1 fun x y hxy => ?_
  rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot] at hxy
  exact sub_eq_zero.mp hxy

end UpperTheory.V.Ws.LineM

open UpperTheory.V.Ws.LineM in
theorem UpperTheory.V.Ws.lineM :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ c c' : PD Φ.ι Γ k, Φ.IsRes a c → Φ.IsRes a c' → Supp nM c.r → Supp nM c'.r → c.SameAl c' → Φ.Linked a c c' := by
  intro O Γ _ _ _ _ _ _ Φ k _ a _ c c' hc hc' hs hs' hal
  have lr := fun g => low_of (hs g)
  have lr' := fun g => low_of (hs' g)
  have br : ∀ g, GlobalTheory (c'.r g - c.r g) := fun g =>
    blk_of (hc.pair.mult g) (hc'.pair.mult g) (lr g) (lr' g)
      (fun i => by rw [hc.res.diag, hc'.res.diag])
      (by rw [hc.res.diag]; exact ((Φ.χ 0 g).isUnit.map a).ne_zero) (hal.1 g)
  have bn : ∀ v, GlobalTheory (c'.n v - c.n v) := fun v =>
    blk_of (hc.pair.low v).1 (hc'.pair.low v).1 (hc.pair.low v).2.2 (hc'.pair.low v).2.2
      (fun i => by rw [(hc.pair.low v).2.1, (hc'.pair.low v).2.1])
      (by rw [(hc.pair.low v).2.1]; exact one_ne_zero) (hal.2 v)
  let ρ : Γ →* M4 k[X] :=
    { toFun := fun g => comb (c.r g) (c'.r g)
      map_one' := by
        ext1 i j
        rw [map_one, map_one, comb_same rfl rfl]
        by_cases e : i = j <;> simp [Matrix.one_apply, e]
      map_mul' := fun g h => by rw [map_mul, map_mul, comb_mul (br g) (br h)] }
  let P : PD Φ.ι Γ k[X] := ⟨ρ, fun v => comb (c.n v) (c'.n v)⟩
  have Pr : ∀ g, P.r g = comb (c.r g) (c'.r g) := fun _ => rfl
  have Pn : ∀ v, P.n v = comb (c.n v) (c'.n v) := fun _ => rfl
  have conj : ∀ v s, adj (P.n v) * P.r s * P.n v =
      comb (adj (c.n v) * c.r s * c.n v) (adj (c'.n v) * c'.r s * c'.n v) := fun v s => by
    rw [Pr, Pn, adj_comb, comb_mul (blk_adj (bn v)) (br s),
      comb_mul (blk_sub_mul (par_adj (par_of (hc.pair.low v).2.2)) (par_of (lr' s)) (blk_adj (bn v)) (br s)) (bn v)]
  refine ⟨P, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, Or.inr ?_⟩, ?_⟩, ?_, ?_⟩
  · intro g
    exact comb_gsp (br g) (hc.pair.mult g) (hc'.pair.mult g)
  · intro g hg
    rw [Pr, hc.pair.kill g hg, hc'.pair.kill g hg]
    ext1 i j
    rw [comb_same rfl rfl]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  · intro i j hij
    rw [Pr, comb_same (hc.pair.nrm hij) (hc'.pair.nrm hij), map_zero]
  · intro v
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · have := comb_gsp (bn v) (hc.pair.low v).1 (hc'.pair.low v).1
      rwa [map_one] at this
    · rw [Pn, comb_same ((hc.pair.low v).2.1 i) ((hc'.pair.low v).2.1 i), map_one]
    · rw [Pn, comb_same ((hc.pair.low v).2.2 i j hij) ((hc'.pair.low v).2.2 i j hij), map_zero]
  · intro v s hs i j hij
    rw [conj, comb_same (hc.pair.flag v s hs i j hij) (hc'.pair.flag v s hs i j hij), map_zero]
  · intro v s hs i
    unfold PD.ψ
    rw [conj, comb_same (hc.pair.mu v s hs i) (hc'.pair.mu v s hs i), map_one]
  · intro g i
    rw [Pr, comb_same (hc.res.diag g i) (hc'.res.diag g i)]; rfl
  · intro v s hs i
    unfold PD.ψ
    rw [conj, comb_same (hc.res.char v s hs i) (hc'.res.char v s hs i)]; rfl
  · intro g i j hij hw
    rw [Pr, comb_same (hs g i j hij hw) (hs' g i j hij hw), map_zero]
  · intro i j N
    exact ((lc_of (hc.cont i j)).prodMk (lc_of (hc'.cont i j))).comp
      fun x : k × k => Ideal.Quotient.mk ((⊥ : Ideal k[X]) ^ N) (C x.1 + X * C (x.2 - x.1))
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, Pr, comb_apply]
    · funext v; ext i j
      simp [PD.map, Pn, comb_apply]
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, Pr, comb_apply]
    · funext v; ext i j
      simp [PD.map, Pn, comb_apply]
