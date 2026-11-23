import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Gys

section

variable {R : Type} [CommRing R]

private theorem gsp_uD (d : Fin 4 → R) (ν : R) (h : ∀ i, d i * d i.rev = ν) (x y t : R) :
    IsGSp ν (uQ x y t * Matrix.diagonal d) := by
  have h0 : d 0 * d 3 = ν := h 0
  have h1 : d 1 * d 2 = ν := h 1
  have hM : uQ x y t * Matrix.diagonal d =
      !![d 0, 0, 0, 0; x * d 0, d 1, 0, 0; y * d 0, 0, d 2, 0; t * d 0, y * d 1, -x * d 2, d 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uQ, Matrix.mul_diagonal]
  unfold IsGSp
  rw [hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj, sgn, Matrix.mul_apply, Fin.sum_univ_four, Fin.rev] <;>
    first | exact h0 | exact h1 | ring1 | linear_combination h0 | linear_combination h1

private theorem suppM_mul {S : Finset (ℤ × ℤ)} {X : M4 R} (h : SuppM S X) (d : Fin 4 → R) :
    SuppM S (X * Matrix.diagonal d) := by
  intro i j hij hw
  simp [Matrix.mul_diagonal, h i j hij hw]

private theorem suppM_mono {S S' : Finset (ℤ × ℤ)} (hS : S ⊆ S') {X : M4 R} (h : SuppM S X) : SuppM S' X :=
  fun i j h1 h2 => h i j h1 fun h3 => h2 (hS h3)

end

section

variable {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R)

private theorem chi1 (g : Γ) : a (Φ.χ 1 g) = a (Φ.rt (-wAl) g) * a (Φ.χ 0 g) := by
  simp only [Fr.rt, wAl, MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg, zpow_one, zpow_zero, mul_one, mul_inv_rev, inv_inv]
  rw [← map_mul]
  congr 1
  simp [Units.ext_iff]

private theorem chi2 (g : Γ) : a (Φ.χ 2 g) = a (Φ.rt (-wPs) g) * a (Φ.χ 0 g) := by
  simp only [Fr.rt, wPs, MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg, zpow_one, zpow_zero, one_mul, mul_inv_rev, inv_inv]
  rw [← map_mul]
  congr 1
  simp [Units.ext_iff]

private theorem chi3 (h : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (g : Γ) :
    a (Φ.χ 3 g) = a (Φ.rt (-wAl) g) * a (Φ.rt (-wPs) g) * a (Φ.χ 0 g) := by
  have h0 : Φ.χ 0 g * Φ.χ 3 g = Φ.ν g := h 0 g
  have h1 : Φ.χ 1 g * Φ.χ 2 g = Φ.ν g := h 1 g
  have key : Φ.χ 3 g = Φ.rt (-wAl) g * Φ.rt (-wPs) g * Φ.χ 0 g := by
    simp only [Fr.rt, wAl, wPs, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_neg, Prod.snd_neg, neg_zero,
      zpow_neg, zpow_one, zpow_zero, mul_one, one_mul]
    rw [eq_inv_mul_of_mul_eq h0, ← h1]
    simp only [mul_inv_rev, inv_inv]
    simp only [mul_assoc]
    rw [inv_mul_cancel, mul_one, mul_left_comm]
  rw [key]
  simp

end

end UpperTheory.V.Ws.Gys

private theorem exists_hom_M4_eq_uQ_mul_diagonal_of_cup {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R]
    (Φ : Fr O Γ) (a : O →+* R) (hΦ : Φ.Ok a) (x y z : Γ → R) (m : Φ.ι → R)
    (hx : Φ.Coc a (-wAl) x) (hy : Φ.Coc a (-wPs) y) (hz : Φ.Cup a (-wAl) (-wPs) x y z m) :
    ∃ r : Γ →* M4 R, ∀ g, r g =
      uQ (x g) (y g) (2 * z g - x g * y g) * Matrix.diagonal (fun i => a ↑(Φ.χ i g)) := by
  have x1 : x 1 = 0 := by
    have h := hx.coc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    linear_combination -h
  have y1 : y 1 = 0 := by
    have h := hy.coc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    linear_combination -h
  have z1 : z 1 = 0 := by
    have h := hz.coc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    linear_combination -h - y 1 * x1
  refine ⟨{ toFun := fun g => uQ (x g) (y g) (2 * z g - x g * y g) * Matrix.diagonal (fun i => a ↑(Φ.χ i g)),
            map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · simp [x1, y1, z1, uQ_zero]
  · intro g h
    rw [mul_assoc, ← mul_assoc (Matrix.diagonal _),
      diag_mul_uQ (fun i => a ↑(Φ.χ i g)) _ _ (UpperTheory.V.Ws.Gys.chi1 Φ a g) (UpperTheory.V.Ws.Gys.chi2 Φ a g)
        (UpperTheory.V.Ws.Gys.chi3 Φ a hΦ.mul g),
      mul_assoc (uQ _ _ _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal, ← mul_assoc, uQ_mul]
    rw [hx.coc, hy.coc, hz.coc, Fr.rt_add, Units.val_mul, map_mul]
    congr 1
    · congr 1 <;> ring
    · congr 1
      funext i
      simp [map_mul]

private theorem adj_uQ_eq_uQ_neg {R : Type} [CommRing R] (p q u : R) : adj (uQ p q u) = uQ (-p) (-q) (-u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj, uQ, sgn, Fin.rev]

private theorem adj_uQ_conj_uQ_mul_diagonal_eq_diagonal {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R)
    (hmul : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (s : Γ) (x y z p q u : R)
    (hx : x = p - a ↑(Φ.rt (-wAl) s) * p) (hy : y = q - a ↑(Φ.rt (-wPs) s) * q)
    (hz : z = u - a ↑(Φ.rt (-wAl + -wPs) s) * u - y * a ↑(Φ.rt (-wAl) s) * p) :
    adj (uQ p q (2 * u - p * q)) * (uQ x y (2 * z - x * y) * Matrix.diagonal (fun i => a ↑(Φ.χ i s))) *
      uQ p q (2 * u - p * q) = Matrix.diagonal (fun i => a ↑(Φ.χ i s)) := by
  rw [adj_uQ_eq_uQ_neg, mul_assoc, mul_assoc,
    diag_mul_uQ (fun i => a ↑(Φ.χ i s)) _ _ (UpperTheory.V.Ws.Gys.chi1 Φ a s) (UpperTheory.V.Ws.Gys.chi2 Φ a s)
      (UpperTheory.V.Ws.Gys.chi3 Φ a hmul s),
    ← mul_assoc, ← mul_assoc, uQ_mul, uQ_mul]
  rw [Fr.rt_add, Units.val_mul, map_mul] at hz
  subst hz
  subst hx
  subst hy
  have e : ∀ A B C : R, A = 0 → B = 0 → C = 0 →
      uQ A B C * Matrix.diagonal (fun i => a ↑(Φ.χ i s)) = Matrix.diagonal (fun i => a ↑(Φ.χ i s)) := by
    intro A B C hA hB hC
    rw [hA, hB, hC, uQ_zero, one_mul]
  apply e <;> ring

theorem UpperTheory.V.Ws.Gys.ob :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R), Φ.Ok a → (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v ∧ ∀ i, a (Φ.χ i s) = 1) → ∀ (x y z : Γ → R) (m n : Φ.ι → R),
      Φ.Coc a (-wAl) x → x Φ.g0 = 0 → Φ.LocTriv a (-wAl) x m → Φ.Coc a (-wPs) y → y Φ.g0 = 0 → Φ.LocTriv a (-wPs) y n →
      Φ.Cup a (-wAl) (-wPs) x y z m → z Φ.g0 = 0 →
        ∃ s : PD Φ.ι Γ R, Φ.IsRes a s ∧ s.In qQ ∧ (∀ g, s.r g 1 0 = x g * a (Φ.χ 0 g)) ∧ (∀ v, s.n v 1 0 = m v) ∧
          (∀ g, s.r g 2 0 = y g * a (Φ.χ 0 g)) ∧ ∀ v, s.n v 2 0 = n v := by
  intro O Γ R _ _ _ _ Φ a hΦ hMu x y z m n hx hx0 hxl hy hy0 hyl hz hz0
  choose o ho using hz.loc
  obtain ⟨r, hr⟩ := exists_hom_M4_eq_uQ_mul_diagonal_of_cup Φ a hΦ x y z m hx hy hz
  have hconj : ∀ v, ∀ s ∈ Φ.Gv v, adj (uQ (m v) (n v) (2 * o v - m v * n v)) * r s *
      uQ (m v) (n v) (2 * o v - m v * n v) = Matrix.diagonal (fun i => a ↑(Φ.χ i s)) := by
    intro v s hs
    rw [hr]
    exact adj_uQ_conj_uQ_mul_diagonal_eq_diagonal Φ a hΦ.mul s _ _ _ _ _ _ (hxl v s hs) (hyl v s hs) (ho v s hs)
  have hlc : ∀ i j, IsLocallyConstant fun g => r g i j := by
    intro i j
    simp only [hr, Matrix.mul_diagonal]
    apply IsLocallyConstant.mul
    · fin_cases i <;> fin_cases j <;> simp [uQ] <;>
        first
        | exact IsLocallyConstant.const _
        | exact hx.lc
        | exact hy.lc
        | exact hx.lc.neg
        | exact ((IsLocallyConstant.const 2).mul hz.lc).sub (hx.lc.mul hy.lc)
    · exact hΦ.lc j
  refine ⟨⟨r, fun v => uQ (m v) (n v) (2 * o v - m v * n v)⟩,
    ⟨⟨?mult, ?kill, ?nrm, ?low, ?flag, ?mu⟩, ⟨?diag, ?char, ?shape⟩, ?cont⟩, ?inn, ?e1, ?e2, ?e3, ?e4⟩
  case mult =>
    intro g
    dsimp only
    rw [hr]
    apply UpperTheory.V.Ws.Gys.gsp_uD
    intro i
    show a ↑(Φ.χ i g) * a ↑(Φ.χ i.rev g) = a ↑(Φ.ν g)
    rw [← map_mul, ← Units.val_mul, hΦ.mul]
  case kill =>
    intro g hg
    dsimp only
    rw [hr, hx.kill g hg, hy.kill g hg, hz.kill g hg]
    simp [hΦ.kill g hg, uQ_zero]
  case nrm =>
    dsimp only
    rw [hr, hx0, hy0, hz0]
    simpa [uQ_zero] using Matrix.isDiag_diagonal (fun i => a ↑(Φ.χ i Φ.g0))
  case low =>
    intro v
    exact isLow_uQ _ _ _
  case flag =>
    intro v s hs
    dsimp only
    rw [hconj v s hs]
    intro i j hij
    exact Matrix.diagonal_apply_ne _ hij.ne'
  case mu =>
    intro v s hs i
    obtain ⟨hg, h1⟩ := hMu v s hs
    show (adj (uQ (m v) (n v) (2 * o v - m v * n v)) * r s * uQ (m v) (n v) (2 * o v - m v * n v)) i i = 1
    rw [hconj v s hg]
    simp [h1 i]
  case diag =>
    intro g i
    dsimp only
    rw [hr]
    fin_cases i <;> simp [uQ, Matrix.mul_diagonal]
  case char =>
    intro v s hs i
    show (adj (uQ (m v) (n v) (2 * o v - m v * n v)) * r s * uQ (m v) (n v) (2 * o v - m v * n v)) i i = _
    rw [hconj v s hs]
    simp
  case shape =>
    left
    constructor
    · intro g
      show SuppM nP (r g)
      rw [hr]
      exact UpperTheory.V.Ws.Gys.suppM_mono (by decide)
        (UpperTheory.V.Ws.Gys.suppM_mul (suppM_uQ _ _ _) _)
    · intro v
      exact suppM_uQ _ _ _
  case cont =>
    intro i j N
    exact (hlc i j).comp _
  case inn =>
    constructor
    · intro g
      show SuppM qQ (r g)
      rw [hr]
      exact UpperTheory.V.Ws.Gys.suppM_mul (suppM_uQ _ _ _) _
    · intro v
      exact suppM_uQ _ _ _
  case e1 =>
    intro g
    show r g 1 0 = _
    rw [hr]
    simp [uQ, Matrix.mul_diagonal]
  case e2 =>
    intro v
    simp [uQ]
  case e3 =>
    intro g
    show r g 2 0 = _
    rw [hr]
    simp [uQ, Matrix.mul_diagonal]
  case e4 =>
    intro v
    simp [uQ]
