import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.DistLift

theorem hv {a b : ℕ} [NeZero b] (h : a ∣ b) (z : ZMod b) : ((z.val : ℕ) : ZMod a) = ZMod.castHom h (ZMod a) z := by
  rw [ZMod.natCast_val, ZMod.castHom_apply]

theorem dvd_of_cast {a : ℕ} {p q : ℕ} (h : (p : ZMod a) = (q : ZMod a)) : (a : ℤ) ∣ (p : ℤ) - q := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h, sub_self]

theorem eq_of_dvd {a : ℕ} [NeZero a] {p q : ZMod a} (h : (a : ℤ) ∣ (p.val : ℤ) - q.val) : p = q := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h; push_cast at h
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h; exact sub_eq_zero.mp h

variable {l N M₀ : ℕ} [NeZero l] [NeZero N] [NeZero M₀] [NeZero (l * M₀)] [NeZero (N * M₀)] [NeZero (N * (l * M₀))]

theorem sc1 (j : ℕ) (hN : Nat.Coprime l N) (hj : Nat.Coprime l j) (h : N * M₀ ∣ N * (l * M₀))
    (s : ZMod (N * M₀)) (t : ZMod (l * M₀))
    (ht : ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀) t = ((j * s.val : ℕ) : ZMod M₀)) :
    ∃! s' : ZMod (N * (l * M₀)), ZMod.castHom h (ZMod (N * M₀)) s' = s ∧ ((j * s'.val : ℕ) : ZMod (l * M₀)) = t := by
  have hc : IsCoprime (l : ℤ) ((j : ℤ) * N) := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.mul_right hj hN)
    push_cast at this; exact this
  have hM : (M₀ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M₀
  apply existsUnique_of_exists_of_unique
  · rw [← hv] at ht
    obtain ⟨e, he⟩ := dvd_of_cast ht
    obtain ⟨α, β, hab⟩ := hc
    refine ⟨((s.val + N * M₀ * (β * e) : ℤ) : ZMod _), ?_, ?_⟩
    · rw [map_intCast]
      have : ((N : ZMod (N * M₀)) * M₀) = 0 := by rw [← Nat.cast_mul, ZMod.natCast_self]
      push_cast; rw [this, zero_mul, add_zero, ZMod.natCast_zmod_val]
    · rw [Nat.cast_mul, hv (dvd_mul_left _ N), map_intCast, ← ZMod.natCast_zmod_val t, ← Int.cast_natCast j,
        ← Int.cast_natCast t.val, ← Int.cast_mul, ZMod.intCast_eq_intCast_iff_dvd_sub]
      refine ⟨α * e, ?_⟩
      push_cast at he ⊢
      linear_combination he - M₀ * e * hab
  · rintro s1 s2 ⟨a1, b1⟩ ⟨a2, b2⟩
    rw [← hv] at a1 a2
    obtain ⟨e, he⟩ := dvd_of_cast (a1.trans a2.symm)
    obtain ⟨f, hf⟩ := dvd_of_cast (b1.trans b2.symm)
    push_cast at he hf
    have h1 : (l : ℤ) ∣ (j * N) * e := ⟨f, mul_left_cancel₀ hM (by linear_combination hf - j * he)⟩
    obtain ⟨r, hr⟩ := hc.dvd_of_dvd_mul_left h1
    apply eq_of_dvd
    exact ⟨r, by push_cast; rw [he, hr]; ring⟩

theorem div_red (v : ℕ) : ((v % (N * M₀) / N : ℕ) : ZMod M₀) = ((v / N : ℕ) : ZMod M₀) := by
  rw [Nat.mod_mul_right_div_self, ZMod.natCast_mod]

theorem val_cast (h : N * M₀ ∣ N * (l * M₀)) (s' : ZMod (N * (l * M₀))) :
    (ZMod.castHom h (ZMod (N * M₀)) s').val = s'.val % (N * M₀) := by
  rw [← hv, ZMod.val_natCast]

theorem sc2 (h : N * M₀ ∣ N * (l * M₀))
    (s : ZMod (N * M₀)) (hs : N ∣ s.val) (t : ZMod (l * M₀))
    (ht : ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀) t = ((s.val / N : ℕ) : ZMod M₀)) :
    ∃! s' : ZMod (N * (l * M₀)), ZMod.castHom h (ZMod (N * M₀)) s' = s ∧ ((s'.val / N : ℕ) : ZMod (l * M₀)) = t := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  apply existsUnique_of_exists_of_unique
  · rw [← hv] at ht
    obtain ⟨e, he⟩ := dvd_of_cast ht
    obtain ⟨c, hc⟩ := hs
    rw [hc, Nat.mul_div_cancel_left _ hN] at he
    refine ⟨((N * t.val : ℕ) : ZMod _), ?_, ?_⟩
    · rw [map_natCast, ← ZMod.natCast_zmod_val s, ← Int.cast_natCast, ← Int.cast_natCast s.val,
        ZMod.intCast_eq_intCast_iff_dvd_sub, hc]
      exact ⟨-e, by push_cast; linear_combination (-N : ℤ) * he⟩
    · rw [ZMod.val_natCast_of_lt (Nat.mul_lt_mul_of_pos_left (ZMod.val_lt t) hN), Nat.mul_div_cancel_left _ hN,
        ZMod.natCast_zmod_val]
  · have key : ∀ s' : ZMod (N * (l * M₀)), ZMod.castHom h (ZMod (N * M₀)) s' = s → N ∣ s'.val := by
      intro s' e
      rw [← e, val_cast] at hs
      exact (Nat.dvd_mod_iff (dvd_mul_right N M₀)).mp hs
    rintro s1 s2 ⟨a1, b1⟩ ⟨a2, b2⟩
    obtain ⟨c1, h1⟩ := key _ a1
    obtain ⟨c2, h2⟩ := key _ a2
    rw [h1, Nat.mul_div_cancel_left _ hN] at b1
    rw [h2, Nat.mul_div_cancel_left _ hN] at b2
    obtain ⟨f, hf⟩ := dvd_of_cast (b1.trans b2.symm)
    apply eq_of_dvd
    rw [h1, h2]
    exact ⟨f, by push_cast at hf ⊢; linear_combination (N : ℤ) * hf⟩

theorem cD_red (h : N * M₀ ∣ N * (l * M₀)) (m : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))) :
    (cD N (l * M₀) m).map (ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀)) =
      cD N M₀ (m.map (ZMod.castHom h (ZMod (N * M₀)))) := by
  have e : ∀ v : ℕ, ((v % (N * M₀) : ℕ) : ZMod M₀) = v := fun v => by
    rw [ZMod.natCast_eq_natCast_iff']; exact Nat.mod_mod_of_dvd _ (dvd_mul_left _ _)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [cD, Matrix.map_apply, val_cast, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_natCast, div_red, Nat.cast_mul, map_mul, e]

theorem lift_mat (hN : Nat.Coprime l N) (h : N * M₀ ∣ N * (l * M₀))
    (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) (hm : N ∣ (m 1 0).val) (Z : Matrix (Fin 2) (Fin 2) (ZMod (l * M₀)))
    (hZ : Z.map (ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀)) = cD N M₀ m) :
    ∃! m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀))),
      m'.map (ZMod.castHom h (ZMod (N * M₀))) = m ∧ cD N (l * M₀) m' = Z := by
  obtain ⟨a, ⟨a1, a2⟩, a3⟩ := sc1 1 hN (Nat.coprime_one_right l) h (m 0 0) (Z 0 0)
    (by rw [one_mul]; exact congrFun (congrFun hZ 0) 0)
  obtain ⟨b, ⟨b1, b2⟩, b3⟩ := sc1 N hN hN h (m 0 1) (Z 0 1) (congrFun (congrFun hZ 0) 1)
  obtain ⟨c, ⟨c1, c2⟩, c3⟩ := sc2 h (m 1 0) hm (Z 1 0) (congrFun (congrFun hZ 1) 0)
  obtain ⟨d, ⟨d1, d2⟩, d3⟩ := sc1 1 hN (Nat.coprime_one_right l) h (m 1 1) (Z 1 1)
    (by rw [one_mul]; exact congrFun (congrFun hZ 1) 1)
  simp only [one_mul] at a2 a3 d2 d3
  refine ⟨!![a, b; c, d], ⟨?_, ?_⟩, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    exacts [a1, b1, c1, d1]
  · ext i j
    fin_cases i <;> fin_cases j
    exacts [a2, b2, c2, d2]
  · rintro m' ⟨e1, e2⟩
    ext i j
    fin_cases i <;> fin_cases j
    exacts [a3 _ ⟨congrFun (congrFun e1 0) 0, congrFun (congrFun e2 0) 0⟩,
      b3 _ ⟨congrFun (congrFun e1 0) 1, congrFun (congrFun e2 0) 1⟩,
      c3 _ ⟨congrFun (congrFun e1 1) 0, congrFun (congrFun e2 1) 0⟩,
      d3 _ ⟨congrFun (congrFun e1 1) 1, congrFun (congrFun e2 1) 1⟩]

theorem kill (z : ZMod (l * M₀)) (hz : ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀) z = 0) : (l : ZMod (l * M₀)) * z = 0 := by
  rw [← hv, ZMod.natCast_eq_zero_iff] at hz
  obtain ⟨c, hc⟩ := hz
  rw [← ZMod.natCast_zmod_val z, hc, ← Nat.cast_mul, ← mul_assoc, Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem solve_mat [Fact l.Prime] (D T : Matrix (Fin 2) (Fin 2) (ZMod (l * M₀)))
    (hD : ZMod.castHom (dvd_mul_right l M₀) (ZMod l) D.det ≠ 0) (W : Matrix (Fin 2) (Fin 2) (ZMod M₀))
    (hT : T.map (ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀)) = D.map (ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀)) * W) :
    ∃! Z : Matrix (Fin 2) (Fin 2) (ZMod (l * M₀)),
      Z.map (ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀)) = W ∧ D * Z = T := by
  set ρ := ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀) with hρ
  obtain ⟨δ, t, hδ⟩ : ∃ δ t : ZMod (l * M₀), δ * D.det = 1 + l * t := by
    obtain ⟨δ, hδ⟩ := ZMod.castHom_surjective (dvd_mul_right l M₀) (ZMod.castHom (dvd_mul_right l M₀) (ZMod l) D.det)⁻¹
    have : ZMod.castHom (dvd_mul_right l M₀) (ZMod l) (δ * D.det - 1) = 0 := by
      rw [map_sub, map_mul, hδ, inv_mul_cancel₀ hD, map_one, sub_self]
    rw [← hv, ZMod.natCast_eq_zero_iff] at this
    obtain ⟨c, hc⟩ := this
    refine ⟨δ, c, ?_⟩
    rw [← Nat.cast_mul, ← hc, ZMod.natCast_zmod_val]; ring
  have hk : ∀ F : Matrix (Fin 2) (Fin 2) (ZMod (l * M₀)), F.map ρ = 0 → (δ * D.det) • F = F := by
    intro F hF
    ext i j
    have := kill (F i j) (congrFun (congrFun hF i) j)
    rw [Matrix.smul_apply, smul_eq_mul, hδ]
    linear_combination t * this
  have hsub : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod (l * M₀)), (A - B).map ρ = A.map ρ - B.map ρ := fun A B => by
    ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  apply existsUnique_of_exists_of_unique
  · have hW : (W.map fun a => ((a.val : ℕ) : ZMod (l * M₀))).map ρ = W := by
      ext i j; simp only [Matrix.map_apply, map_natCast, ZMod.natCast_zmod_val]
    set W0 := W.map fun a => ((a.val : ℕ) : ZMod (l * M₀))
    have hF : (T - D * W0).map ρ = 0 := by rw [hsub, Matrix.map_mul, hW, hT, sub_self]
    refine ⟨W0 + (δ • D.adjugate) * (T - D * W0), ?_, ?_⟩
    · rw [Matrix.map_add _ (map_add ρ), Matrix.map_mul, hF, hW, mul_zero, add_zero]
    · rw [mul_add, ← mul_assoc, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, Matrix.smul_mul, one_mul, hk _ hF]; abel
  · rintro Z1 Z2 ⟨a1, b1⟩ ⟨a2, b2⟩
    have hF : (Z1 - Z2).map ρ = 0 := by rw [hsub, a1, a2, sub_self]
    have h0 : (δ • D.adjugate) * (D * (Z1 - Z2)) = 0 := by rw [mul_sub, b1, b2, sub_self, mul_zero]
    rw [← mul_assoc, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, Matrix.smul_mul, one_mul, hk _ hF] at h0
    exact sub_eq_zero.mp h0

theorem dn_vecMul (x : Row (l * M₀)) (Z : Matrix (Fin 2) (Fin 2) (ZMod (l * M₀))) :
    dn l M₀ (x ᵥ* Z) = dn l M₀ x ᵥ* Z.map (ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀)) := by
  ext j
  simp only [dn, Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_add, map_mul, Matrix.map_apply]

theorem solve_rows [Fact l.Prime] (x y x' y' : Row (l * M₀))
    (hD : ((x 0).val : ZMod l) * ((y 1).val : ZMod l) - ((x 1).val : ZMod l) * ((y 0).val : ZMod l) ≠ 0)
    (W : Matrix (Fin 2) (Fin 2) (ZMod M₀)) (hx : dn l M₀ x' = dn l M₀ x ᵥ* W) (hy : dn l M₀ y' = dn l M₀ y ᵥ* W) :
    ∃! Z : Matrix (Fin 2) (Fin 2) (ZMod (l * M₀)),
      Z.map (ZMod.castHom (dvd_mul_left M₀ l) (ZMod M₀)) = W ∧ x ᵥ* Z = x' ∧ y ᵥ* Z = y' := by
  have key : ∀ Z : Matrix (Fin 2) (Fin 2) (ZMod (l * M₀)),
      Matrix.of ![x, y] * Z = Matrix.of ![x', y'] ↔ x ᵥ* Z = x' ∧ y ᵥ* Z = y' := by
    intro Z
    constructor
    · intro e
      exact ⟨congrFun e 0, congrFun e 1⟩
    · rintro ⟨e1, e2⟩
      ext i j
      fin_cases i
      exacts [congrFun e1 j, congrFun e2 j]
  have := solve_mat (Matrix.of ![x, y]) (Matrix.of ![x', y']) (by
    simp only [hv (dvd_mul_right l M₀)] at hD
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]; exact hD) W (by
    ext i j
    fin_cases i
    exacts [congrFun hx j, congrFun hy j])
  simpa only [key] using this

noncomputable def red (h : N * M₀ ∣ N * (l * M₀)) (m : GL (Fin 2) (ZMod (N * (l * M₀)))) : GL (Fin 2) (ZMod (N * M₀)) :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod (N * M₀))) m

theorem red_coe (h : N * M₀ ∣ N * (l * M₀)) (m : GL (Fin 2) (ZMod (N * (l * M₀)))) :
    (red h m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) =
      (m : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))).map (ZMod.castHom h (ZMod (N * M₀))) := rfl

theorem red_det (h : N * M₀ ∣ N * (l * M₀)) (m : GL (Fin 2) (ZMod (N * (l * M₀)))) :
    Matrix.GeneralLinearGroup.det (red h m) =
      Units.map (ZMod.castHom h (ZMod (N * M₀))).toMonoidHom (Matrix.GeneralLinearGroup.det m) := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, red_coe, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det _ _).symm

theorem fibre [Fact l.Prime] (hN : Nat.Coprime l N) (hl : l ∣ M₀) (h : N * M₀ ∣ N * (l * M₀)) (x y x' y' : Row (l * M₀))
    (hD : ((x 0).val : ZMod l) * ((y 1).val : ZMod l) - ((x 1).val : ZMod l) * ((y 0).val : ZMod l) ≠ 0)
    (m : GL (Fin 2) (ZMod (N * M₀))) (hm : N ∣ ((m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) 1 0).val)
    (hx : dn l M₀ x' = dn l M₀ x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))))
    (hy : dn l M₀ y' = dn l M₀ y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))) :
    ∃! m' : GL (Fin 2) (ZMod (N * (l * M₀))), red h m' = m ∧
      x ᵥ* cD N (l * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))) = x' ∧
      y ᵥ* cD N (l * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))) = y' := by
  obtain ⟨Z, ⟨z1, z2, z3⟩, z4⟩ := solve_rows x y x' y' hD _ hx hy
  obtain ⟨A, ⟨a1, a2⟩, a3⟩ := lift_mat hN h _ hm Z z1
  have hu : IsUnit A.det := by
    have h1 : IsUnit (ZMod.castHom h (ZMod (N * M₀)) A.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, a1]
      exact (Matrix.GeneralLinearGroup.det m).isUnit
    rw [← hv, ZMod.isUnit_iff_coprime] at h1
    rw [← ZMod.natCast_zmod_val A.det, ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.mul_right (h1.coprime_dvd_right (hl.mul_left N)) h1).coprime_dvd_right (by rw [mul_left_comm])
  refine ⟨Matrix.GeneralLinearGroup.mk'' A hu, ⟨Units.ext a1, ?_, ?_⟩, ?_⟩
  · rw [← z2, ← a2]; rfl
  · rw [← z3, ← a2]; rfl
  · rintro m' ⟨e1, e2, e3⟩
    have e0 : (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))).map (ZMod.castHom h (ZMod (N * M₀))) = m := by
      rw [← red_coe, e1]
    exact Units.ext (a3 _ ⟨e0, z4 _ ⟨by rw [cD_red h, e0], e2, e3⟩⟩)

theorem cnd_red (hl : l ∣ M₀) (h : N * M₀ ∣ N * (l * M₀)) (g : SL(2, ℤ)) (m : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))) :
    Cnd l N g (m.map (ZMod.castHom h (ZMod (N * M₀)))) ↔ Cnd l N g m := by
  have e : ∀ k v : ℕ, k ∣ N * M₀ → ((v % (N * M₀) : ℕ) : ZMod k) = v := fun k v hk => by
    rw [ZMod.natCast_eq_natCast_iff']; exact Nat.mod_mod_of_dvd _ hk
  simp only [Cnd, Matrix.map_apply, val_cast, e N _ (dvd_mul_right _ _), e l _ (hl.mul_left N)]

theorem wt_red [Fact l.Prime] {n : ℕ} (hl : l ^ n ∣ M₀) (h : N * M₀ ∣ N * (l * M₀)) (m : GL (Fin 2) (ZMod (N * (l * M₀))))
    (w : ℕ) (u : Fin 2 → ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣
      ((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod (N * (l * M₀)))ˣ) : ZMod (N * (l * M₀))).val : ℤ_[l]) *
        ((((m : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))) 0 0).val : ℤ_[l]) * u 0 +
          (((m : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))) 0 1).val : ℤ_[l]) * u 1) ^ w -
      ((((Matrix.GeneralLinearGroup.det (red h m))⁻¹ : (ZMod (N * M₀))ˣ) : ZMod (N * M₀)).val : ℤ_[l]) *
        ((((red h m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) 0 0).val : ℤ_[l]) * u 0 +
          (((red h m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) 0 1).val : ℤ_[l]) * u 1) ^ w := by
  have e : ∀ s : ZMod (N * (l * M₀)), Ideal.Quotient.mk (Ideal.span {(l : ℤ_[l]) ^ n})
      ((ZMod.castHom h (ZMod (N * M₀)) s).val : ℤ_[l]) = Ideal.Quotient.mk (Ideal.span {(l : ℤ_[l]) ^ n}) (s.val : ℤ_[l]) := by
    intro s
    rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton, val_cast]
    obtain ⟨c, hc⟩ := hl.mul_left N
    refine ⟨(c * (s.val / (N * M₀)) : ℕ), ?_⟩
    have := Nat.mod_add_div s.val (N * M₀)
    have h2 : s.val = s.val % (N * M₀) + l ^ n * (c * (s.val / (N * M₀))) := by rw [← mul_assoc (l ^ n), ← hc, this]
    have h3 := congrArg (Nat.cast : ℕ → ℤ_[l]) h2
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at h3
    linear_combination h3
  have e2 : (((Matrix.GeneralLinearGroup.det (red h m))⁻¹ : (ZMod (N * M₀))ˣ) : ZMod (N * M₀)) =
      ZMod.castHom h (ZMod (N * M₀)) (((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod (N * (l * M₀)))ˣ) : ZMod (N * (l * M₀))) := by
    rw [red_det, ← map_inv]; rfl
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, e2, red_coe]
  simp only [Matrix.map_apply, map_mul, map_pow, map_add, e]

theorem sum_fibre [Fact l.Prime] (hN : Nat.Coprime l N) (hl : l ∣ M₀) (h : N * M₀ ∣ N * (l * M₀)) (x y : Row (l * M₀))
    (hD : ((x 0).val : ZMod l) * ((y 1).val : ZMod l) - ((x 1).val : ZMod l) * ((y 0).val : ZMod l) ≠ 0)
    (m : GL (Fin 2) (ZMod (N * M₀))) (hm : N ∣ ((m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) 1 0).val)
    {A : Type} [AddCommMonoid A] (F : Row (l * M₀) → Row (l * M₀) → A) :
    ∑ m' ∈ Finset.univ.filter (fun m' : GL (Fin 2) (ZMod (N * (l * M₀))) => red h m' = m),
      F (x ᵥ* cD N (l * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))))
        (y ᵥ* cD N (l * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀))))) =
    ∑ x' ∈ Finset.univ.filter (fun x' => dn l M₀ x' = dn l M₀ x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))),
      ∑ y' ∈ Finset.univ.filter (fun y' => dn l M₀ y' = dn l M₀ y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))),
        F x' y' := by
  have mt : ∀ (z : Row (l * M₀)) (m' : GL (Fin 2) (ZMod (N * (l * M₀)))), red h m' = m →
      dn l M₀ (z ᵥ* cD N (l * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀))))) =
        dn l M₀ z ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) := by
    intro z m' e
    rw [dn_vecMul, cD_red h, ← red_coe, e]
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun m' _ => (x ᵥ* cD N (l * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))),
    y ᵥ* cD N (l * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))))) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro m' hm'
    rw [Finset.mem_filter] at hm'
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨mt x m' hm'.2, mt y m' hm'.2⟩
  · intro m1 h1 m2 h2 e
    rw [Finset.mem_filter] at h1 h2
    rw [Prod.mk.injEq] at e
    exact (fibre hN hl h x y _ _ hD m hm (mt x m2 h2.2) (mt y m2 h2.2)).unique ⟨h1.2, e.1, e.2⟩ ⟨h2.2, rfl, rfl⟩
  · rintro ⟨x', y'⟩ hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨m', ⟨e1, e2, e3⟩, -⟩ := fibre hN hl h x y x' y' hD m hm hp.1 hp.2
    exact ⟨m', Finset.mem_filter.mpr ⟨Finset.mem_univ _, e1⟩, Prod.ext e2 e3⟩

theorem rep_prod {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    {ι : Type} (S : Finset ι) (f : ι → X.Kˣ) (a : ι → X.Khat l) (h : ∀ i, Rep X l n (f i) (a i)) :
    Rep X l n (∏ i ∈ S, f i) (∑ i ∈ S, a i) := by
  obtain ⟨c1, c2, -⟩ := sCls Ω ε X l n
  induction S using Finset.induction_on with
  | empty =>
    have := (c2 _ _ _ _ (c1 1) (c1 1)).2
    rwa [div_self', sub_self] at this
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (c2 _ _ _ _ (h i) ih).1

end UpperTheory.V.Z.Kato.Nb.DistLift

open UpperTheory.V.Z.Kato.Nb.DistLift in
theorem UpperTheory.V.Z.Kato.Nb.sXiDist :
    UpperTheory.V.Z.Kato.Nb.SXiDist := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL M' _ _ h hM' x y hB P a u
  obtain ⟨rfl, -, dl, pos, cop, -⟩ := hL
  subst hM'
  have hl : l ∣ M₀ := (dvd_pow_self l (by omega)).trans dl
  obtain ⟨-, -, -, -, a5, -⟩ := sApi Ω ε X l n
  obtain ⟨c1, -, -, c4, -⟩ := sCls Ω ε X l n
  simp only [Xi]
  rw [map_sub, sub_eq_zero, map_sum, map_sum, eq_comm]
  refine Eq.trans ?_ (Finset.sum_fiberwise_of_maps_to (g := red h)
    (t := Finset.univ.filter (fun m : GL (Fin 2) (ZMod (N * M₀)) =>
      Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) ∧ P (Matrix.GeneralLinearGroup.det m))) ?_ _)
  swap
  · intro m' hm'
    rw [Finset.mem_filter] at hm' ⊢
    refine ⟨Finset.mem_univ _, (cnd_red hl h g _).mpr hm'.2.1, ?_⟩
    rw [red_det]; exact hm'.2.2
  refine Finset.sum_congr rfl fun m hm => Eq.symm ?_
  rw [Finset.mem_filter] at hm
  have hm10 : N ∣ ((m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) 1 0).val := (ZMod.natCast_eq_zero_iff _ _).mp hm.2.1.1
  rw [Finset.filter_filter, Finset.filter_congr (q := fun m' => red h m' = m) (fun m' _ => ⟨fun e => e.2, fun e => ⟨⟨
    (cnd_red hl h g _).mp (by rw [← red_coe, e]; exact hm.2.1), by rw [← red_det, e]; exact hm.2.2⟩, e⟩⟩)]
  refine Eq.trans (Finset.sum_congr rfl (fun m' hm' => by
    have e := a5 _ _ (clsK X l n (slD X N (a (x ᵥ* cD N (l * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀)))))
      (y ᵥ* cD N (l * M₀) (m' : Matrix (Fin 2) (Fin 2) (ZMod (N * (l * M₀))))) : X.K))) (wt_red dl h m' w u)
    rewrite [map_sub, sub_eq_zero, (Finset.mem_filter.mp hm').2] at e
    exact e)) ?_
  rw [← map_sum, ← Finset.smul_sum, sum_fibre cop hl h x y hB.2 m hm10 (fun x' y' => clsK X l n (slD X N (a x' y' : X.K))),
    map_smul, map_smul]
  congr 1
  rw [← sub_eq_zero, ← map_sub]
  refine c4 _ _ _ _ (rep_prod X l n _ _ _ fun x' => rep_prod X l n _ _ _ fun y' =>
    c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (a x' y'))) (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (pushD X l M₀ a _ _))) ⟨1, ?_⟩
  simp only [pushD, map_prod, one_pow, mul_one]
