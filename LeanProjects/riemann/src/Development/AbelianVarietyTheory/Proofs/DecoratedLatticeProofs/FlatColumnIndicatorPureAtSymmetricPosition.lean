import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat.PureColPf

section Plain
variable {k : Type} [Field k] {n n' ι ι' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

theorem typeFrame_val' (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => 1) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change fromBlocks 1 0 0 (diagonal _) = _
  rw [← fromBlocks_diagonal]; simp

theorem typeFrame_inv_val' (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_val', diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp

theorem coords_entry (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (u : n ⊕ Fin c) (v : n' ⊕ Fin c') :
    (((typeFrame ϖ o).bas⁻¹).val * x * (typeFrame ϖ o').bas.val) u v =
      Sum.elim (fun _ => 1) (fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) u * x u v *
        Sum.elim (fun _ => 1) (fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) v := by
  rw [typeFrame_inv_val', typeFrame_val', mul_diagonal, diagonal_mul]

theorem affPt_col (p : ℕ) (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (a : n) (q : Fin (c + 1)) (hq : q.val + 1 = p) : affPt p x₀ e (.inl a) (.inr q) = 0 := by
  have : ¬ Free p ((.inl a, .inr q) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) := by
    simp only [Free]; omega
  simp [affPt, basePt, this]

end Plain

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_one_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (Φ : Matrix b a k → ℂ) : om μ (1 : GL a k) (1 : GL b k) Φ = Φ := by
  funext x
  simp [om, nabs]

end Loc

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem le_of_mul_pow_lt {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (r : ℕ) {y : k}
    (h : valuation k (y * (ϖ : k) ^ (r + 1)) < 1) : valuation k y ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k) := by
  have h1 := (hϖ _).1 h
  have h0 : ((ϖ : k) ^ (r + 1)) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have ey : y = (y * (ϖ : k) ^ (r + 1)) * ((ϖ : k) ^ (r + 1))⁻¹ := by field_simp
  have ec : (((ϖ ^ r)⁻¹ : kˣ) : k) = (ϖ : k) * ((ϖ : k) ^ (r + 1))⁻¹ := by
    simp [pow_succ]
  calc valuation k y = valuation k (y * (ϖ : k) ^ (r + 1)) * valuation k (((ϖ : k) ^ (r + 1))⁻¹) := by
        rw [← map_mul, ← ey]
    _ ≤ valuation k (ϖ : k) * valuation k (((ϖ : k) ^ (r + 1))⁻¹) := mul_le_mul_left h1 _
    _ = _ := by rw [← map_mul, ec]

theorem mul_pow_lt_of_le {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (r : ℕ) {y : k}
    (h : valuation k y ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k)) : valuation k (y * (ϖ : k) ^ (r + 1)) < 1 := by
  have h0 : ((ϖ : k) ^ (r + 1)) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have e : (((ϖ ^ r)⁻¹ : kˣ) : k) * (ϖ : k) ^ (r + 1) = ϖ := by
    simp [pow_succ]
  have h1 : valuation k (ϖ : k) < 1 := (hϖ _).2 le_rfl
  calc valuation k (y * (ϖ : k) ^ (r + 1)) = valuation k y * valuation k ((ϖ : k) ^ (r + 1)) := map_mul _ _ _
    _ ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k) * valuation k ((ϖ : k) ^ (r + 1)) := mul_le_mul_left h _
    _ = valuation k (ϖ : k) := by rw [← map_mul, e]
    _ < 1 := h1

end Main

section Chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem Phi_add_colAt (j c : ℕ) (H : j + 1 + c = s) (r : ℕ) (y : XIx (Fin κ) t (j + 1) → k)
    (hy : y ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹)
    (z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) :
    (S.T t).Phi j (c + 1) (by omega) (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y) =
      (S.T t).Phi j (c + 1) (by omega) z := by
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id) := fun _ => rfl
  rw [hΦ, hΦ]
  have e : ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o')
      (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y)).submatrix (ixSucc _ t j) id =
      ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') z).submatrix (ixSucc _ t j) id +
      ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') (colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y)).submatrix
        (ixSucc _ t j) id := by
    simp only [LatFrame.coords, Matrix.mul_add, Matrix.add_mul]
    rfl
  rw [e]
  refine TypeDatum.Phi_add _ (S.tame _) _ fun u v => ?_
  change valuation k ((((typeFrame S.ϖ o).bas⁻¹).val * colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y *
    (typeFrame S.ϖ o').bas.val) (o (ixSucc _ t j u)) (o' v)) < 1
  rw [coords_entry]
  generalize o (ixSucc _ t j u) = U
  generalize o' v = V
  rcases U with a | l <;> rcases V with b | q
  · simp [colAt]
  · by_cases hq : q.val = r
    · have := mul_pow_lt_of_le S.unif r (hy a)
      simpa [colAt, hq] using this
    · simp [colAt, hq]
  · simp [colAt]
  · simp [colAt]

end Chain

section Chain2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem mem_box_of_Phi_ne_zero (hpat : S.Pattern t) (j c : ℕ) (H : j + 1 + c = s) (r : ℕ) (hr : c + 1 = 2 * r)
    (z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k)
    (hz : ∀ a, z (.inl a) (.inr ⟨r, by omega⟩) = 0) (y : XIx (Fin κ) t (j + 1) → k)
    (h : (S.T t).Phi j (c + 1) (by omega) (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y) ≠ 0) :
    y ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹ := by
  have hρ : r ≤ S.ρ := by have := S.odd; omega
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id) := fun _ => rfl
  rw [hΦ] at h
  obtain ⟨⟨g, hg, e⟩, hmax⟩ := (TypeDatum.Phi_ne_zero_iff _ _).1 h
  have hpg := ((hpat j g).1 hg).2
  set x := z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y with hx
  let q₀ : Fin (c + 1 + 1) := ⟨r, by omega⟩
  let b : Ix (Fin κ ⊕ Fin (s + 1)) t j := .inl (.inr ⟨r, by omega⟩)
  have hb : o' b = .inr q₀ := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (by omega) q₀
  intro a
  apply le_of_mul_pow_lt S.unif r
  have key : (typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x (o.symm (.inl a)) b = y a * (S.ϖ : k) ^ (r + 1) := by
    change (((typeFrame S.ϖ o).bas⁻¹).val * x * (typeFrame S.ϖ o').bas.val) (o (o.symm (.inl a))) (o' b) = _
    rw [Equiv.apply_symm_apply, hb, coords_entry]
    simp [hx, hz, q₀, colAt]
  rw [← key]
  obtain ⟨w, hw⟩ : ∃ w, ixSucc _ t j w = o.symm (.inl a) := ⟨_, Equiv.apply_symm_apply _ _⟩
  have hw' : o (ixSucc _ t j w) = .inl a := by rw [hw, Equiv.apply_symm_apply]
  rw [← hw]
  rcases w with i | u
  · have hgi : g.val i b = (typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x (ixSucc _ t j (.inl i)) b := by
      rw [e]; rfl
    have hnf : ¬ FreeIx S.ρ i b ∧ i ≠ b := by
      rcases i with (e' | l) | ⟨q, u⟩
      · refine ⟨?_, by simp [b]⟩
        simp only [FreeIx, FreeTop, b, Fin.mk_lt_mk, not_lt]
        exact hρ
      · have hl : c + 1 ≤ l.val := by
          by_contra hl
          push_neg at hl
          have h1 : o (.inl (.inr l)) = .inr ⟨l.val, hl⟩ :=
            standardOrderExtendedBasis_apply_low_block (Fin κ) t (j + 1) (c + 1) (by omega) (⟨l.val, hl⟩ : Fin (c + 1))
          have h2 : o (ixSucc _ t j (.inl (.inl (.inr l)))) = o (.inl (.inr l)) := rfl
          rw [h2, h1] at hw'
          exact Sum.inr_ne_inl hw'
        refine ⟨?_, ?_⟩
        · simp only [FreeIx, FreeTop, b, Fin.lt_def, not_lt]
          omega
        · intro he
          simp only [b, Sum.inl.injEq, Sum.inr.injEq] at he
          have := congrArg Fin.val he
          simp at this
          omega
      · exact ⟨by simp [FreeIx, b], by simp [b]⟩
    have := hpg i b hnf.1
    rw [Matrix.one_apply_ne hnf.2, sub_zero, hgi] at this
    exact this
  · exact hmax u b

end Chain2

theorem _root_.GlobalTheory.LocFlat.pureCol_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
      S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureCol S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hpat hex
  haveI := hν.1
  intro j c H r hr
  obtain ⟨C, hC, hCe⟩ := hex j (c + 1) (by omega) (r + 1) (by omega) (by omega) (by have := S.odd; omega)
  have hreg := (Chain.ofType_regular S.P S.μ S.tame (fun j c h => typeFrame S.ϖ (stdOrd (Fin κ) t j c h))
    (LatFrame.refl k _)).2.2 (j + 1) (c + 1) (by omega)
  have hvol := volNat_Cgrp_pos ν (J := ((S.T t).lev (j + 1) (c + 1) (by omega)).J) hreg.1 hreg.2.1
    ((S.T t).bas (j + 1) (c + 1) (by omega)) 1
  set V := volNat ν ((S.T t).bas (j + 1) (c + 1) (by omega)) (Cgrp ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1)
    with hV
  refine ⟨C * V, mul_pos hC hvol, fun x => ?_⟩
  have hent : ∀ x₀, (S.T t).entry S.ψ ν j c H 1 1 x₀ =
      ((V⁻¹ : ℝ) : ℂ) * opE S.ψ ν 1 ((S.T t).Phi j (c + 1) (by omega)) x₀ := by
    intro x₀
    simp only [Chain.entry, xi, flat, om_one_one, hV]
  by_cases hy : (fun a => x a (Sum.inr ())) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹
  · rw [if_pos hy, mul_one, hent]
    have e : flCol S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x =
        opE S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x.toCols₁ := by
      unfold flCol
      congr 1
      funext z
      exact Phi_add_colAt S t j c H r _ hy z
    rw [e, hCe, Pi.smul_apply, smul_eq_mul]
    have hV0 : (V : ℂ) ≠ 0 := by exact_mod_cast hvol.ne'
    push_cast
    field_simp
  · rw [if_neg hy, mul_zero]
    unfold flCol opE
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
    have h0 : (S.T t).Phi j (c + 1) (by omega) (affPt (r + 1) x.toCols₁ e +
        colAt (XIx (Fin κ) t j) (c + 1) (r + 1) fun a => x a (Sum.inr ())) = 0 := by
      by_contra hne
      exact hy (mem_box_of_Phi_ne_zero S t hpat j c H r hr _
        (fun a => affPt_col _ _ _ _ _ rfl) _ hne)
    simp only [h0, zero_mul, Pi.zero_apply]

end GlobalTheory.LocFlat.PureColPf
