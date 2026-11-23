import Formalism.HermitianCurvature.StatementTL

namespace Formalism.FourierDecayAlt.TL

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {r : ℕ} {L : LevelData A r} {st : Start A}

theorem fn_comm (L : LevelData A r) {x y : A} (hx : x ∈ zfns L) (hy : y ∈ zfns L) : x * y = y * x :=
  L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem z10 (h : IsLevelStart L st) {Y : ℂ} (hi : Y ∈ st.inv) :
    st.QQ Y 1 0 * L.ζ = L.ζ * st.QQ Y 1 0 - st.QQ Y 1 1 ∧ Commute (st.QQ Y 1 0) L.ζb := by
  have hlow := h.low Y hi
  have htau := h.tau Y
  have mζ : L.ζ ∈ zfns L := by simp [zfns]
  have mζi : L.ζi ∈ zfns L := by simp [zfns]
  have mζb : L.ζb ∈ zfns L := by simp [zfns]
  have mGG : L.GG ∈ zfns L := by simp [zfns]
  have mGGi : L.GGi ∈ zfns L := by simp [zfns]
  have cm : ∀ {x y : A}, x ∈ zfns L → y ∈ zfns L → Commute x y := fun hx hy => fn_comm L hx hy
  have hX : ∀ g ∈ zfns L, Commute (st.x Y) g := h.x_fn Y
  have hE : ∀ g ∈ zfns L, Commute (st.ee Y) g := h.ee_fn Y
  have hc : ∀ a : A, Commute (algebraMap ℂ A (Y + 1 / 2)) a := fun a => Algebra.commutes _ a
  have hl : L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y =
      -L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) + L.ζb * L.ζi * L.GGi * st.ee Y) := by
    simp only [Formalism.FourierDecayAlt.R.LevelData.l0]
    abel
  rw [hl] at hlow
  have hT : ∀ g ∈ zfns L, Commute (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
      L.ζb * L.ζi * L.GGi * st.ee Y) g := by
    intro g hg
    apply Commute.add_left
    · exact ((hc _).mul_left ((cm mζb hg).mul_left (cm mGGi hg))).neg_left
    · exact (((cm mζb hg).mul_left (cm mζi hg)).mul_left (cm mGGi hg)).mul_left (hE _ hg)
  have hTz := hT _ mζ
  have hGXz : Commute (L.GG * st.x Y) L.ζ := (cm mGG mζ).mul_left (hX _ mζ)
  constructor
  · rw [hlow, htau]
    calc L.GG * st.x Y * (-L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y)) * L.ζ
        = L.GG * st.x Y * (-(L.nab * L.ζ) + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y) * L.ζ) := by noncomm_ring
      _ = L.GG * st.x Y * (-(L.ζ * L.nab + 1) + L.ζ * (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y)) := by rw [L.nab_ζ, hTz.eq]
      _ = (L.GG * st.x Y * L.ζ) * (-L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y)) - L.GG * st.x Y := by noncomm_ring
      _ = L.ζ * (L.GG * st.x Y * (-L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y))) - L.GG * st.x Y := by
        rw [hGXz.eq]
        noncomm_ring
  · rw [hlow]
    have hnab : Commute L.nab L.ζb := L.nab_ζb
    exact ((cm mGG mζb).mul_left (hX _ mζb)).mul_left (hnab.neg_left.add_left (hT _ mζb))

theorem zetaQQ : ZetaQQ := by
  intro A _ _ _ _ r L st hS h Y hY hi
  have mζ : L.ζ ∈ zfns L := by simp [zfns]
  have mζb : L.ζb ∈ zfns L := by simp [zfns]
  have mG : L.GG ∈ zfns L := by simp [zfns]
  have sζb : star L.ζb = L.ζ := by rw [← hS.1, star_star]
  have herm : ∀ Z : ℂ, star Z = Z → ∀ i j, star (st.QQ Z i j) = st.QQ Z j i := fun Z hZ i j => by
    have := congrFun (congrFun (h.start.herm Z hZ) j) i
    rwa [Matrix.conjTranspose_apply] at this
  have base : ∀ Z : ℂ, star Z = Z → Z ∈ st.inv →
      (st.QQ Z 1 0 * L.ζ = L.ζ * st.QQ Z 1 0 - st.QQ Z 1 1 ∧ Commute (st.QQ Z 1 0) L.ζb ∧
      st.QQ Z 0 1 * L.ζb = L.ζb * st.QQ Z 0 1 + st.QQ Z 1 1 ∧ Commute (st.QQ Z 0 1) L.ζ ∧
      Commute (st.QQ Z 1 1) L.ζ ∧ Commute (st.QQ Z 1 1) L.ζb) := fun Z hZ hZi => by
    obtain ⟨a, b⟩ := z10 h hZi
    refine ⟨a, b, ?_, ?_, ?_, ?_⟩
    · have := congrArg star a
      rw [star_mul, star_sub, star_mul, herm Z hZ, herm Z hZ, hS.1] at this
      rw [this]; abel
    · have := congrArg star b.eq
      rw [star_mul, star_mul, herm Z hZ, sζb] at this
      exact this.symm
    · rw [h.tau]; exact Commute.mul_left (fn_comm L mG mζ) (h.x_fn Z _ mζ)
    · rw [h.tau]; exact Commute.mul_left (fn_comm L mG mζb) (h.x_fn Z _ mζb)
  refine ⟨base Y hY hi, fun hn => ?_⟩
  have cancel : ∀ Z ∈ st.inv, ∀ u : A, u * st.QQ Z 1 1 = 0 → u = 0 := fun Z hZ u hu => by
    rw [h.tau] at hu
    have : u * (L.GG * st.x Z) * st.xi Z * L.GGi = u := by
      rw [mul_assoc u, mul_assoc L.GG, (h.x_xi Z hZ).1, mul_one, mul_assoc, L.GG_GGi, mul_one]
    rw [← this, hu, zero_mul, zero_mul]
  have key : st.QQ Y 0 0 * L.ζb = L.ζb * st.QQ Y 0 0 + st.QQ Y 1 0 := by
    obtain ⟨-, b10, b01, -, -, -⟩ := base Y hY hi
    rcases hn with hm | hp
    · have hr : star (Y - 1) = Y - 1 := by rw [star_sub, hY, star_one]
      obtain ⟨-, -, c01, -, -, c11⟩ := base _ hr hm
      have d := congrFun (congrFun (h.start.det (Y - 1)).1 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, YangianSpanCharacter.T.J] at d
      have dq := Algebra.commutes (st.q (Y - 1)) L.ζb
      rw [← d] at dq
      apply eq_of_sub_eq_zero
      apply cancel _ hm
      have e1 := c11.eq
      have e2 := b10.eq
      calc _ = st.QQ Y 0 0 * (L.ζb * st.QQ (Y - 1) 1 1) - L.ζb * st.QQ Y 0 0 * st.QQ (Y - 1) 1 1
            - st.QQ Y 1 0 * st.QQ (Y - 1) 1 1 := by noncomm_ring
        _ = ((-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1)) +
            (st.QQ Y 1 0 * (st.QQ (Y - 1) 0 1 * L.ζb) - L.ζb * st.QQ Y 1 0 * st.QQ (Y - 1) 0 1
              - st.QQ Y 1 0 * st.QQ (Y - 1) 1 1) := by rw [← e1]; noncomm_ring
        _ = 0 := by
          rw [c01, ← e2]
          have : (-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1) = 0 := by
            rw [sub_eq_zero]; simpa [neg_mul] using dq
          rw [this]; noncomm_ring
    · have hr : star (Y + 1) = Y + 1 := by rw [star_add, hY, star_one]
      obtain ⟨-, c10, -, -, -, c11⟩ := base _ hr hp
      have d := congrFun (congrFun (h.start.det Y).2 0) 1
      have d' := congrFun (congrFun (h.start.det Y).2 1) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, YangianSpanCharacter.T.J] at d d'
      have dq := Algebra.commutes (st.q Y) L.ζb
      rw [← d] at dq
      apply eq_of_sub_eq_zero
      apply cancel _ hp
      have e1 := c11.eq
      have e2 := c10.eq
      have d2 : st.QQ Y 1 0 * st.QQ (Y + 1) 1 1 = st.QQ Y 1 1 * st.QQ (Y + 1) 1 0 := by
        have := d'; rw [neg_add_eq_zero] at this; exact this.symm
      calc _ = st.QQ Y 0 0 * (L.ζb * st.QQ (Y + 1) 1 1) - L.ζb * st.QQ Y 0 0 * st.QQ (Y + 1) 1 1
            - st.QQ Y 1 0 * st.QQ (Y + 1) 1 1 := by noncomm_ring
        _ = ((-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1)) +
            (st.QQ Y 0 1 * (st.QQ (Y + 1) 1 0 * L.ζb) - L.ζb * st.QQ Y 0 1 * st.QQ (Y + 1) 1 0
              - st.QQ Y 1 0 * st.QQ (Y + 1) 1 1) := by rw [← e1]; noncomm_ring
        _ = 0 := by
          rw [e2, ← mul_assoc (st.QQ Y 0 1), b01, d2]
          have : (-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1) = 0 := by
            rw [sub_eq_zero]; simpa [neg_mul] using dq
          rw [this]; noncomm_ring
  refine ⟨key, ?_⟩
  have := congrArg star key
  rw [star_mul, star_add, star_mul, herm Y hY, herm Y hY, sζb] at this
  rw [this]; abel

end

end Formalism.FourierDecayAlt.TL
