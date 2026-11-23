import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PsiMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem mul_zpow_pow_eq_one_of_pow_eqs {H : Type*} [CommGroup H] (P A C : H) (N k : ℕ) (m a : ℤ)
    (hP : P ^ (2 * N) = A ^ (2 * N) * C ^ (2 * (N : ℤ) * m)) (hA : A ^ k = C ^ (a * k)) :
    (P * C ^ (-(m + a))) ^ (2 * N * k) = 1 := by
  have hP' : P ^ ((2 * N : ℕ) : ℤ) = A ^ ((2 * N : ℕ) : ℤ) * C ^ (2 * (N : ℤ) * m) := by
    rw [zpow_natCast, zpow_natCast]
    exact hP
  have hA' : A ^ (k : ℤ) = C ^ (a * k) := by
    rw [zpow_natCast]
    exact hA
  rw [← zpow_natCast, mul_zpow]
  have e1 : P ^ ((2 * N * k : ℕ) : ℤ) = (P ^ ((2 * N : ℕ) : ℤ)) ^ (k : ℤ) := by
    rw [← zpow_mul]
    push_cast
    ring_nf
  have e2 : A ^ (((2 * N : ℕ) : ℤ) * k) = C ^ (a * k * (2 * N)) := by
    rw [mul_comm, zpow_mul, hA', ← zpow_mul]
    push_cast
    ring_nf
  rw [e1, hP', mul_zpow, ← zpow_mul A, ← zpow_mul C, ← zpow_mul C, e2, ← zpow_add, ← zpow_add]
  convert zpow_zero C using 2
  push_cast
  ring

theorem UpperTheory.V.Ws.auArith :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X 0 B φ → ∀ (y : X.A →ₐ[c'.O] PadicAlgCl l) (x : B.Pt), (∀ b, x b = y (algebraMap X.B X.A (φ b))) → (∀ (v : W.Vl l T.L) (i : Fin 4), Continuous (x.psi v i)) → ∀ m : Fin 4 → ℤ, StrictAnti m → T.Wts (fun i => 2 * m i) (X.P.map (y : X.A →+* PadicAlgCl l)) → ∃ w : K.s.Wt 4, x.Arith w := by
  intro hGAR Ω _ _ _ l _ c D T c' h K X B φ hφ y x hx hcont m hm hW
  obtain ⟨U, hUo, hU⟩ := hW
  haveI : Finite (G T.F Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUo
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hpowU : ∀ g : G T.F Ω, g ^ U.normalCore.index ∈ U :=
    fun g => Subgroup.normalCore_le U (U.normalCore.pow_index_mem g)
  have hN0 : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hl' : ∀ v : W.Vl l T.L, (K.s.A v).valuation (l : Ω) < 1 := by
    intro v
    rw [K.hA v]
    exact T.ovl _
  choose a b k hk hb hcyc using fun v : W.Vl l T.L => K.cyc (K.s.A v) (hl' v)
  refine ⟨fun v j _ => -(m j + a v), ?_, ?_⟩
  · intro v τ i j hij
    have := hm hij
    simp only
    omega
  · intro v j
    have hlw : ((l : ℕ) : 𝓞 T.L) ∈ (K.s.w v).asIdeal := (K.s.hw v (l : 𝓞 T.L)).1 (by simpa using hl' v)
    refine UpperTheory.V.Loc.laArith hGAR (K.s.hw v) hlw (x.psi v j) (hcont v j) (m j + a v)
      (2 * U.normalCore.index * k v) ?_ ?_
    · exact Nat.mul_pos (Nat.mul_pos two_pos (Nat.pos_of_ne_zero hN0)) (hk v)
    · intro g hg
      set N := U.normalCore.index
      set P := x.psi v j g
      set A := Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (K.κ ↑g)
      set C := cycBar T.L Ω l ↑g
      apply mul_zpow_pow_eq_one_of_pow_eqs P A C N (k v) (m j) (a v)
      · obtain ⟨_, hIneF, hpsi⟩ := UpperTheory.V.Ws.auPsi D T c' h K X B 0 φ hφ y x hx v j (g ^ N)
        have hgN : ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ∈ Ine (K.s.A v) := by
          rw [Subgroup.coe_pow]
          exact Subgroup.pow_mem _ hg N
        have hin := hU (K.e v) j _ ⟨by rw [Subgroup.coe_pow, map_pow]; exact hpowU _, hIneF hgN⟩
        have e0 : x.psi v j (g ^ N) = P ^ N := map_pow _ _ _
        have hκN : (algebraMap c'.O (PadicAlgCl l)) (↑(K.κ ↑(g ^ N)) * ↑(K.β ↑(g ^ N)) ^ 0) = ↑(A ^ N) := by
          rw [pow_zero, mul_one, Subgroup.coe_pow, map_pow, Units.val_pow_eq_pow_val, map_pow,
            Units.val_pow_eq_pow_val]
          rfl
        have hcN : cycBar T.F Ω l (resLe T.F_le ↑(g ^ N)) = C ^ N := by
          show cycBar T.L Ω l ↑(g ^ N) = _
          rw [Subgroup.coe_pow, map_pow]
        rw [hcN] at hin
        rw [e0, hκN] at hpsi
        apply Units.ext
        have e3 : (↑(P ^ (2 * N)) : PadicAlgCl l) = (↑(P ^ N)) ^ 2 := by
          rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]
        rw [e3, hpsi, mul_pow]
        erw [hin]
        rw [Units.val_mul]
        congr 1
        · rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]
        · congr 1
          rw [← zpow_natCast, ← zpow_mul]
          congr 1
          push_cast
          ring
      · have h1 := congrArg (Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l))
          (hcyc v ↑g hg).1
        have h2 : Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l)
            (chiO T.L Ω l c'.O ↑g) = C := by
          have := congrArg (fun f => f (↑g : G T.L Ω)) (UpperTheory.V.Ws.auChi T.L Ω c').1
          exact this
        rw [map_one, map_pow, map_mul, map_zpow, h2, mul_pow, mul_eq_one_iff_eq_inv] at h1
        rw [h1, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
        congr 1
        ring
