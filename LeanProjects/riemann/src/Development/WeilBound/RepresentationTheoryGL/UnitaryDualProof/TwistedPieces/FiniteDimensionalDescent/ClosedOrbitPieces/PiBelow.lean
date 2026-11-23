import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.PieceGood

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)}

theorem pi_orth (hA : CR A) {e e' : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) (he' : e' ∈ primIdem A) (h : e ≠ e') : e * e' = 0 := by
  obtain ⟨heA, hei, -, hep⟩ := he
  obtain ⟨heA', hei', -, hep'⟩ := he'
  have hc : e * e' = e' * e := hA.1 _ heA _ heA'
  have hm : e * e' ∈ A := A.mul_mem heA heA'
  have hi : IsIdempotentElem (e * e') := by
    unfold IsIdempotentElem
    calc e * e' * (e * e') = e * (e' * e) * e' := by simp only [mul_assoc]
      _ = e * e * (e' * e') := by rw [← hc]; simp only [mul_assoc]
      _ = e * e' := by rw [hei.eq, hei'.eq]
  have h1 : e * e' * e = e * e' := by rw [mul_assoc, ← hc, ← mul_assoc, hei.eq]
  have h2 : e * e' * e' = e * e' := by rw [mul_assoc, hei'.eq]
  rcases hep _ hm hi h1 with h3 | h3
  · exact h3
  rcases hep' _ hm hi h2 with h4 | h4
  · exact h4
  exact absurd (h3.symm.trans h4) h

theorem pi_field (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) {a : Matrix (Fin N) (Fin N) k} (ha : a ∈ A) : e * a = 0 ∨ ∃ b ∈ A, e * a * b = e := by
  obtain ⟨heA, hei, -, hep⟩ := he
  have hrA : e * a ∈ A := A.mul_mem heA ha
  letI iC : CommRing A := { (inferInstance : Ring A) with mul_comm := fun x y => Subtype.ext (hA.1 _ x.2 _ y.2) }
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, z, hz⟩ := IsArtinian.exists_pow_succ_smul_dvd (⟨e * a, hrA⟩ : A) (1 : A)
  simp only [smul_eq_mul, mul_one] at hz

  set r := e * a with hr
  set w : Matrix (Fin N) (Fin N) k := (z : Matrix (Fin N) (Fin N) k) with hw
  have hwA : w ∈ A := z.2
  have hz' : r ^ (n + 1) * w = r ^ n := by
    have := congrArg Subtype.val hz
    simpa using this
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.1
  have hrw : r * w = w * r := hcomm _ hrA _ hwA

  have key : ∀ j, r ^ (n + 1) * (r * w) ^ j = r ^ (n + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ (r * w) j, ← mul_assoc, ih, ← mul_assoc, ← pow_succ, pow_succ' r (n + 1), mul_assoc, hz', ← pow_succ']
  set m := n + 1
  have hm : r ^ m = r ^ m * (r * w) ^ m := (key m).symm
  have hpow : (r * w) ^ m = r ^ m * w ^ m := (Commute.mul_pow hrw m)
  set f := r ^ m * w ^ m with hf
  have hfA : f ∈ A := A.mul_mem (A.pow_mem hrA _) (A.pow_mem hwA _)
  have hrm : r ^ m = r ^ m * f := by rw [← hpow]; exact hm
  have hfi : IsIdempotentElem f := by
    unfold IsIdempotentElem
    calc f * f = r ^ m * f * w ^ m := by
          rw [hf]
          have : w ^ m * (r ^ m * w ^ m) = r ^ m * w ^ m * w ^ m := by
            rw [← mul_assoc, hcomm _ (A.pow_mem hwA _) _ (A.pow_mem hrA _)]
          rw [mul_assoc, this]; simp only [mul_assoc]
      _ = f := by rw [← hrm]
  have hre : r * e = r := by rw [hr, mul_assoc, hcomm a ha e heA, ← mul_assoc, hei.eq]
  have hfe : f * e = f := by
    have : r ^ m * e = r ^ m := by
      rw [show m = n + 1 from rfl, pow_succ, mul_assoc, hre]
    rw [hf, mul_assoc, hcomm _ (A.pow_mem hwA _) e heA, ← mul_assoc, this]
  rcases hep f hfA hfi hfe with h0 | h1
  · left
    have : r ^ m = 0 := by rw [hrm, h0, mul_zero]
    have hnil : IsNilpotent (⟨r, hrA⟩ : A) := ⟨m, by ext1; simpa using this⟩
    have := hA.2.eq_zero _ hnil
    simpa using congrArg Subtype.val this
  · right
    refine ⟨r ^ n * w ^ m, A.mul_mem (A.pow_mem hrA _) (A.pow_mem hwA _), ?_⟩
    rw [← h1, hf, ← mul_assoc, ← pow_succ']

theorem pi_lin (hA : CR A) :
    LinearIndependent k (fun e : primIdem A => (e : Matrix (Fin N) (Fin N) k)) := by
  rw [linearIndependent_iff']
  intro s g hs i hi
  have hmul : (i : Matrix (Fin N) (Fin N) k) * ∑ j ∈ s, g j • (j : Matrix (Fin N) (Fin N) k) = g i • (i : Matrix (Fin N) (Fin N) k) := by
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [mul_smul_comm, i.2.2.1.eq]
    · intro j _ hji
      rw [mul_smul_comm, pi_orth hA i.2 j.2 (fun h => hji (Subtype.ext h.symm)), smul_zero]
    · intro h; exact absurd hi h
  rw [hs, mul_zero] at hmul
  rcases smul_eq_zero.mp hmul.symm with h | h
  · exact h
  · exact absurd h i.2.2.2.1

theorem pi_fin (hA : CR A) : (primIdem A).Finite := by
  have := (pi_lin hA).finite
  exact Set.finite_coe_iff.mp this

theorem pi_below (hA : CR A) : ∀ (n : ℕ) (g : Matrix (Fin N) (Fin N) k), g.rank = n → g ∈ A → IsIdempotentElem g → g ≠ 0 →
    ∃ p ∈ primIdem A, p * g = p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g hn hgA hgi hg0
  by_cases hprim : ∀ f ∈ A, IsIdempotentElem f → f * g = f → f = 0 ∨ f = g
  · exact ⟨g, ⟨hgA, hgi, hg0, hprim⟩, hgi.eq⟩
  push Not at hprim
  obtain ⟨h, hhA, hhi, hhg, hh0, hhg'⟩ := hprim
  have hgh : g * h = h := by rw [hA.1 _ hgA _ hhA, hhg]
  have hlt : h.rank < g.rank := by
    unfold Matrix.rank
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne ?_ ?_
    · rw [← hgh, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
    · intro heq
      apply hhg'
      have : ∀ v, h *ᵥ (g *ᵥ v) = g *ᵥ v := by
        intro v
        have hv : g *ᵥ v ∈ LinearMap.range h.mulVecLin := heq ▸ ⟨v, rfl⟩
        obtain ⟨u, hu⟩ := hv
        simp only [Matrix.mulVecLin_apply] at hu
        rw [← hu, Matrix.mulVec_mulVec, hhi.eq]
      have hhg2 : h * g = g := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, this v]
      rw [← hhg2, hhg]
  obtain ⟨p, hp, hph⟩ := ih _ (hn ▸ hlt) h rfl hhA hhi hh0
  refine ⟨p, hp, ?_⟩
  calc p * g = p * h * g := by rw [hph]
    _ = p * h := by rw [mul_assoc, hhg]
    _ = p := hph

theorem pi_sum (hA : CR A) : ∑ e ∈ (pi_fin hA).toFinset, e = 1 := by
  set s := ∑ e ∈ (pi_fin hA).toFinset, e with hs
  have hsA : s ∈ A := A.sum_mem fun e he => ((pi_fin hA).mem_toFinset.mp he).1
  have hps : ∀ p ∈ primIdem A, p * s = p := by
    intro p hp
    rw [hs, Finset.mul_sum, Finset.sum_eq_single p]
    · exact hp.2.1.eq
    · intro j hj hjp
      exact pi_orth hA hp ((pi_fin hA).mem_toFinset.mp hj) (Ne.symm hjp)
    · intro h; exact absurd ((pi_fin hA).mem_toFinset.mpr hp) h
  have hss : s * s = s := by
    rw [hs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e he => ?_
    exact hps e ((pi_fin hA).mem_toFinset.mp he)
  by_contra hne
  have hu0 : 1 - s ≠ 0 := fun h => hne (sub_eq_zero.mp h).symm
  have hui : IsIdempotentElem (1 - s) := by
    unfold IsIdempotentElem
    rw [sub_mul, one_mul, mul_sub, mul_one, hss, sub_self, sub_zero]
  obtain ⟨p, hp, hpu⟩ := pi_below hA _ (1 - s) rfl (A.sub_mem A.one_mem hsA) hui hu0
  rw [mul_sub, mul_one, hps p hp, sub_self] at hpu
  exact hp.2.2.1 hpu.symm

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
