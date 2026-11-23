import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OrdinaryFlagThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep2
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepValuesInFiniteExtension
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.Th UpperTheory.V.Z.J

namespace UpperTheory.V.Z.Keep.OrdFlag2

open Matrix

private theorem tri_of_lines {k H : Type} [Field k] (T : H → Matrix (Fin 2) (Fin 2) k) (a b : H → k) (x y p q : k)
    (hx : x ≠ 0 ∨ y ≠ 0) (hp : p ≠ 0 ∨ q ≠ 0) (hpx : p * x + q * y = 0)
    (h0 : ∀ s, T s 0 0 * x + T s 0 1 * y = a s * x) (h1 : ∀ s, T s 1 0 * x + T s 1 1 * y = a s * y)
    (h2 : ∀ s, p * T s 0 0 + q * T s 1 0 = b s * p) (h3 : ∀ s, p * T s 0 1 + q * T s 1 1 = b s * q) :
    ∃ Q : GL (Fin 2) k, ∀ s, ((Q : Matrix (Fin 2) (Fin 2) k) * T s * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 0 = 0 ∧
      ((Q : Matrix (Fin 2) (Fin 2) k) * T s * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 0 0 = a s ∧
      ((Q : Matrix (Fin 2) (Fin 2) k) * T s * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = b s := by
  obtain ⟨u, v, huv⟩ : ∃ u v : k, u * x + v * y = 1 := by
    rcases hx with h | h
    · exact ⟨x⁻¹, 0, by field_simp; ring⟩
    · exact ⟨0, y⁻¹, by field_simp; ring⟩
  have hd : u * q - v * p ≠ 0 := fun e => by
    have e1 : q = (u * q - v * p) * x := by linear_combination (-q) * huv + v * hpx
    have e2 : p = -(u * q - v * p) * y := by linear_combination (-p) * huv + u * hpx
    rw [e, zero_mul] at e1
    rw [e, neg_zero, zero_mul] at e2
    rcases hp with h | h
    · exact h e2
    · exact h e1
  set d := u * q - v * p with hdd
  let Q0 : Matrix (Fin 2) (Fin 2) k := !![u, v; p, q]
  let Q1 : Matrix (Fin 2) (Fin 2) k := !![x, -v / d; y, u / d]
  have hQ : Q0 * Q1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination huv
    · field_simp; ring
    · linear_combination hpx
    · field_simp; rw [hdd]; ring
  let Q : GL (Fin 2) k := ⟨Q0, Q1, hQ, mul_eq_one_comm.1 hQ⟩
  refine ⟨Q, fun s => ?_⟩
  have e : ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = Q1 := rfl
  have e' : (Q : Matrix (Fin 2) (Fin 2) k) = Q0 := rfl
  rw [e, e']
  have a0 := h0 s
  have a1 := h1 s
  have a2 := h2 s
  have a3 := h3 s
  refine ⟨?_, ?_, ?_⟩
  · simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    linear_combination x * a2 + y * a3 + b s * hpx
  · simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    linear_combination u * a0 + v * a1 + a s * huv
  · simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    field_simp
    linear_combination (-v) * a2 + u * a3

end UpperTheory.V.Z.Keep.OrdFlag2

namespace UpperTheory.V.Z.Keep.OrdFlag2

open Matrix

private theorem flag_block {k H : Type} [Field k] (R : H → Matrix (Fin 3) (Fin 3) k) (a c : H → k) (g : GL (Fin 3) k)
    (hb : ∀ s, R s 0 1 = 0 ∧ R s 1 0 = 0 ∧ R s 1 2 = 0 ∧ R s 2 1 = 0 ∧ R s 1 1 = 1)
    (ht : ∀ s, ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 1 0 = 0 ∧
      ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 2 0 = 0 ∧
      ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 2 1 = 0 ∧
      ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 0 = a s ∧
      ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 2 2 = c s)
    (s0 s2 : H) (h0 : a s0 ≠ 1) (h2 : c s2 ≠ 1) :
    ∃ Q : GL (Fin 2) k, ∀ s, ((Q : Matrix (Fin 2) (Fin 2) k) * corner (R s) * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 0 = 0 ∧
      ((Q : Matrix (Fin 2) (Fin 2) k) * corner (R s) * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 0 0 = a s ∧
      ((Q : Matrix (Fin 2) (Fin 2) k) * corner (R s) * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = c s := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 3) (Fin 3) k, P = (g : Matrix (Fin 3) (Fin 3) k) := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Matrix (Fin 3) (Fin 3) k, I = ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := ⟨_, rfl⟩
  have hPI : P * I = 1 := by rw [hP, hI, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hIP : I * P = 1 := by rw [hP, hI, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← hP, ← hI] at ht
  have hcol : ∀ s i, (R s * I) i 0 = a s * I i 0 := fun s i => by
    obtain ⟨t1, t2, -, t4, -⟩ := ht s
    have e : R s * I = I * (P * R s * I) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hIP, Matrix.one_mul]
    rw [e, Matrix.mul_apply, Fin.sum_univ_three, t1, t2, t4]
    ring
  have hrow : ∀ s j, (P * R s) 2 j = c s * P 2 j := fun s j => by
    obtain ⟨-, t2, t3, -, t5⟩ := ht s
    have e : P * R s = (P * R s * I) * P := by
      rw [Matrix.mul_assoc _ I P, hIP, Matrix.mul_one]
    rw [e, Matrix.mul_apply, Fin.sum_univ_three, t2, t3, t5]
    ring
  have hz : I 1 0 = 0 := by
    have h := hcol s0 1
    obtain ⟨-, b2, b3, -, b5⟩ := hb s0
    rw [Matrix.mul_apply, Fin.sum_univ_three, b2, b3, b5] at h
    have h' : (a s0 - 1) * I 1 0 = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 h0)
  have ht1 : P 2 1 = 0 := by
    have h := hrow s2 1
    obtain ⟨b1, -, -, b4, b5⟩ := hb s2
    rw [Matrix.mul_apply, Fin.sum_univ_three, b1, b4, b5] at h
    have h' : (c s2 - 1) * P 2 1 = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 h2)
  have e20 : P 2 0 * I 0 0 + P 2 2 * I 2 0 = 0 := by
    have h := congrFun (congrFun hPI 2) 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, ht1, Matrix.one_apply_ne (by decide)] at h
    linear_combination h
  have e00 : P 0 0 * I 0 0 + P 0 2 * I 2 0 = 1 := by
    have h := congrFun (congrFun hPI 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, hz, Matrix.one_apply_eq] at h
    linear_combination h
  have e22 : P 2 0 * I 0 2 + P 2 2 * I 2 2 = 1 := by
    have h := congrFun (congrFun hPI 2) 2
    rw [Matrix.mul_apply, Fin.sum_univ_three, ht1, Matrix.one_apply_eq] at h
    linear_combination h
  have hx : I 0 0 ≠ 0 ∨ I 2 0 ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at e00
    simp at e00
  have hp : P 2 0 ≠ 0 ∨ P 2 2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at e22
    simp at e22
  refine tri_of_lines (fun s => corner (R s)) a c (I 0 0) (I 2 0) (P 2 0) (P 2 2) hx hp e20 (fun s => ?_) (fun s => ?_)
    (fun s => ?_) (fun s => ?_)
  · have h := hcol s 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, hz] at h
    show R s 0 0 * I 0 0 + R s 0 2 * I 2 0 = _
    linear_combination h
  · have h := hcol s 2
    rw [Matrix.mul_apply, Fin.sum_univ_three, hz] at h
    show R s 2 0 * I 0 0 + R s 2 2 * I 2 0 = _
    linear_combination h
  · have h := hrow s 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, ht1] at h
    show P 2 0 * R s 0 0 + P 2 2 * R s 2 0 = _
    linear_combination h
  · have h := hrow s 2
    rw [Matrix.mul_apply, Fin.sum_univ_three, ht1] at h
    show P 2 0 * R s 0 2 + P 2 2 * R s 2 2 = _
    linear_combination h

private theorem ne_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    (A : ValuationSubring Ω) (hv : A.valuation (l : Ω) < 1) {M : ℕ} (hM : 1 ≤ M) (d : ℤ) (hd : d ≠ 0)
    (χ : G F Ω →* (Qbar l)ˣ) (hχ : Af.KillsMu M χ) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ)
    (hI : ∀ s : ↥(Dec (F := F) A), (s : G F Ω) ∈ Ine (F := F) A → κ s = cycBar F Ω l s ^ d * χ s) :
    ∃ s, κ s ≠ 1 := by
  have hfin : Finite χ.range := (UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ hχ).to_subtype
  have hN : ∀ s, χ s ^ Nat.card χ.range = 1 := fun s =>
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, s, rfl⟩ : χ.range)))
  have hN0 : Nat.card χ.range ≠ 0 := Nat.card_pos.ne'
  obtain ⟨g, hg, hne⟩ := UpperTheory.V.Ws.Pt.cycIne F Ω l A hv (d * Nat.card χ.range)
    (mul_ne_zero hd (by exact_mod_cast hN0))
  refine ⟨⟨g, Ine_le_Dec A hg⟩, fun e => hne ?_⟩
  have h1 := hI ⟨g, Ine_le_Dec A hg⟩ hg
  rw [e] at h1
  have h2 : cycBar F Ω l g ^ d = (χ g)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
  rw [_root_.zpow_mul, h2, zpow_natCast, inv_pow, hN, inv_one]

end UpperTheory.V.Z.Keep.OrdFlag2

theorem UpperTheory.V.Z.Keep.ordFlag2 :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ) (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A), Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → Block η r → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω], η.ker = galOf ℚ K Ω → ∀ W : G K Ω →* GL (Fin 2) (Qbar l), (∀ s, (W s).val = corner (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat) → ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∃ A' : ValuationSubring Ω, IsPlaceOver A' w ∧ ∃ κ, Af.FlagAt N ![(e : ℤ), -(e : ℤ)] W A' κ := by
  intro Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ C₀ k hΦ A _ _ r hr hbl h11 K _ _ _ _ _ hK W hW w hw
  have hker : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker := fun s => by
    rw [hK, ← range_galEmb]
    exact ⟨s, rfl⟩
  let j : G K Ω →* η.ker := (galEmb ℚ K Ω).codRestrict _ hker
  let ρ : G K Ω →* GL (Fin 3) (Qbar l) := (glPart η (UnitaryThreeInertia.push A.val r) hr.red.mult).comp j
  have hρ : ∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat := fun s => rfl
  obtain ⟨A', hA, κ, χ, hχ, ⟨g, hg⟩, hI⟩ :=
    UpperTheory.V.Z.Keep.ordFlag3 Ω l c N e ψ η σ g₁ B M hL L Φ C₀ k hΦ A r hr K hK ρ hρ w hw
  have hv : A'.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hw
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have he : (e : ℤ) ≠ 0 := by
    have := hL.e_pos
    omega
  obtain ⟨s0, h0⟩ := OrdFlag2.ne_one A' hv hN (e : ℤ) he (χ 0) (hχ 0) (κ 0) (hI 0)
  obtain ⟨s2, h2⟩ := OrdFlag2.ne_one A' hv hN (-(e : ℤ)) (neg_ne_zero.2 he) (χ 2) (hχ 2) (κ 2) (hI 2)
  have hent : ∀ (s : G K Ω) (a b : Fin 3), Odd (wt a b) → (ρ s).val a b = 0 := fun s a b h => by
    rw [hρ, UnitaryThreeInertia.push, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, hbl _ (hker s) a b h]
    exact map_zero _
  have hmid : ∀ s : G K Ω, (ρ s).val 1 1 = 1 := fun s => by
    rw [hρ, UnitaryThreeInertia.push, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, h11 _ (hker s)]
    exact map_one _
  obtain ⟨Q, hQ⟩ := OrdFlag2.flag_block (fun s : ↥(Dec (F := K) A') => (ρ s.1).val)
    (fun s => ((κ 0 s : (Qbar l)ˣ) : Qbar l)) (fun s => ((κ 2 s : (Qbar l)ˣ) : Qbar l)) g
    (fun s => ⟨hent _ _ _ (by decide), hent _ _ _ (by decide), hent _ _ _ (by decide), hent _ _ _ (by decide), hmid _⟩)
    (fun s => by
      obtain ⟨t1, t2⟩ := hg s
      exact ⟨t1 1 0 (by decide), t1 2 0 (by decide), t1 2 1 (by decide), t2 0, t2 2⟩)
    s0 s2 (fun e => h0 (Units.ext e)) (fun e => h2 (Units.ext e))
  refine ⟨A', hA, ![κ 0, κ 2], ![χ 0, χ 2], fun i => ?_, ⟨Q, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s hs => ?_⟩
  · fin_cases i
    · exact hχ 0
    · exact hχ 2
  · have e1 : (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val = (Q : Matrix (Fin 2) (Fin 2) (Qbar l)) * corner (ρ s.1).val * ((Q⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      rw [Units.val_mul, Units.val_mul, hW, ← hρ]
    have hij' : i = 1 ∧ j = 0 := by
      revert hij; fin_cases i <;> fin_cases j <;> simp
    obtain ⟨rfl, rfl⟩ := hij'
    show (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val 1 0 = 0
    rw [e1]
    exact (hQ s).1
  · have e1 : (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val = (Q : Matrix (Fin 2) (Fin 2) (Qbar l)) * corner (ρ s.1).val * ((Q⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      rw [Units.val_mul, Units.val_mul, hW, ← hρ]
    fin_cases i
    · show (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val 0 0 = _
      rw [e1]
      exact (hQ s).2.1
    · show (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val 1 1 = _
      rw [e1]
      exact (hQ s).2.2
  · fin_cases i
    · exact hI 0 s hs
    · exact hI 2 s hs
