import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus
import Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Matrix

namespace PositivityTheory.ThKG.CayleyTransformDarboux

section Alg

variable {R E β : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) [Fintype β] [DecidableEq β]

theorem mul_diagT {α : Type} (z : Matrix α β E) : z * (diagCols β : Matrix (β ⊕ β) β E)ᵀ = fromCols z z := by
  rw [diagCols, transpose_fromRows, transpose_one]
  exact (mul_fromCols z 1 1).trans (by rw [Matrix.mul_one])

theorem cayley {J : Matrix β β E} (g : UG c J) (gd : UG c (dbl J))
    (hgd : ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)
    (h : E) (h2 : h + h = 1) (hc : c h = h) (t : GL β E) (ht : (t : Matrix β β E) = h • (((g : GL β E) : Matrix β β E) + 1)) :
    ∃ n w p : UG c (dbl J), gd = w * n * w⁻¹ * p ∧
      ((n : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) * (diagCols β : Matrix (β ⊕ β) β E) =
        (diagCols β : Matrix (β ⊕ β) β E) * ((1 : GL β E) : Matrix β β E) ∧
      ((p : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) * (diagCols β : Matrix (β ⊕ β) β E) =
        (diagCols β : Matrix (β ⊕ β) β E) * (t : Matrix β β E) := by
  set G : Matrix β β E := ((g : GL β E) : Matrix β β E) with hG
  have hg : Gᵀ * J * G.map c = J := g.2
  set k : Matrix β β E := ((t⁻¹ : GL β E) : Matrix β β E)
  have tk : (t : Matrix β β E) * k = 1 := t.mul_inv
  have kt : k * (t : Matrix β β E) = 1 := t.inv_mul
  have ma : ∀ A B : Matrix β β E, (A + B).map c = A.map c + B.map c := fun A B => Matrix.map_add _ (map_add c) _ _
  have ms : ∀ A B : Matrix β β E, (A - B).map c = A.map c - B.map c := fun A B => Matrix.map_sub _ (map_sub c) _ _
  have mn : ∀ A : Matrix β β E, (-A).map c = -A.map c := fun A => Matrix.map_neg _ (map_neg c) _
  have mm : ∀ A B : Matrix β β E, (A * B).map c = A.map c * B.map c := fun A B => Matrix.map_mul (f := c.toRingHom)
  have m1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have m0 : (0 : Matrix β β E).map c = 0 := Matrix.map_zero _ (map_zero c)
  have mh : ∀ A : Matrix β β E, (h • A).map c = h • A.map c := fun A => by ext i j; simp [hc]
  obtain ⟨T, hT⟩ : ∃ T, T = h • h • ((G - 1) * k) := ⟨_, rfl⟩
  have Tt : T * (t : Matrix β β E) = h • h • (G - 1) := by rw [hT, smul_mul, smul_mul, Matrix.mul_assoc, kt, Matrix.mul_one]
  have sk : Tᵀ * J + J * T.map c = 0 := by
    have e : (t : Matrix β β E)ᵀ * (Tᵀ * J + J * T.map c) * (t : Matrix β β E).map c = 0 := by
      calc _ = (T * (t : Matrix β β E))ᵀ * J * (t : Matrix β β E).map c +
            (t : Matrix β β E)ᵀ * J * (T * (t : Matrix β β E)).map c := by
            simp only [transpose_mul, mm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 0 := by
            rw [Tt, ht]
            simp only [mh, ma, ms, m1, transpose_smul, transpose_add, transpose_sub, transpose_one, smul_mul, Matrix.mul_smul,
              Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, hg, Matrix.one_mul, Matrix.mul_one]
            module
    calc _ = ((t : Matrix β β E) * k)ᵀ * (Tᵀ * J + J * T.map c) * ((t : Matrix β β E) * k).map c := by rw [tk, m1]; simp
      _ = kᵀ * ((t : Matrix β β E)ᵀ * (Tᵀ * J + J * T.map c) * (t : Matrix β β E).map c) * k.map c := by
          simp only [transpose_mul, mm, Matrix.mul_assoc]
      _ = 0 := by rw [e]; simp
  have sk' : Tᵀ * J = -(J * T.map c) := eq_neg_of_add_eq_zero_left sk
  let n : UG c (dbl J) := ⟨⟨fromBlocks (1 + T) (-T) T (1 - T), fromBlocks (1 - T) T (-T) (1 + T),
    by rw [fromBlocks_multiply, ← fromBlocks_one]; congr 1 <;> noncomm_ring,
    by rw [fromBlocks_multiply, ← fromBlocks_one]; congr 1 <;> noncomm_ring⟩, by
      change (fromBlocks (1 + T) (-T) T (1 - T))ᵀ * dbl J * (fromBlocks (1 + T) (-T) T (1 - T)).map c = dbl J
      simp only [dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, ma, ms, mn, m1, transpose_add, transpose_sub,
        transpose_neg, transpose_one, Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, sk']
      congr 1 <;> noncomm_ring⟩
  let w : UG c (dbl J) := ⟨⟨fromBlocks 1 0 0 (-1), fromBlocks 1 0 0 (-1),
    by rw [fromBlocks_multiply, ← fromBlocks_one]; simp, by rw [fromBlocks_multiply, ← fromBlocks_one]; simp⟩, by
      change (fromBlocks 1 0 0 (-1))ᵀ * dbl J * (fromBlocks 1 0 0 (-1) : Matrix (β ⊕ β) (β ⊕ β) E).map c = dbl J
      simp [dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, mn, m1, m0]⟩
  refine ⟨n, w, (w * n * w⁻¹)⁻¹ * gd, by group, ?_, ?_⟩
  · change fromBlocks (1 + T) (-T) T (1 - T) * fromRows 1 1 = fromRows 1 1 * 1
    simp [fromBlocks_mul_fromRows]
  · have e : ((w * n * w⁻¹ : UG c (dbl J)) : GL (β ⊕ β) E).1 * ((diagCols β : Matrix (β ⊕ β) β E) * (t : Matrix β β E)) =
        (gd : GL (β ⊕ β) E).1 * (diagCols β : Matrix (β ⊕ β) β E) := by
      change fromBlocks 1 0 0 (-1) * fromBlocks (1 + T) (-T) T (1 - T) * fromBlocks 1 0 0 (-1) *
        (fromRows 1 1 * (t : Matrix β β E)) = _
      have a : ∀ A : Matrix β β E, h • A + h • A = A := fun A => by rw [← add_smul, h2, one_smul]
      rw [hgd, diagCols, fromRows_mul, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_mul_fromRows, fromBlocks_mul_fromRows]
      simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul,
        Matrix.mul_neg, neg_neg, Matrix.add_mul, Matrix.sub_mul, Tt]
      congr 1
      · rw [add_assoc, a, ht, ← smul_add]
        convert a G using 1
        module
      · rw [show ∀ A B : Matrix β β E, -A + -(-0 + -(B - A)) = B - (A + A) from fun A B => by abel, a, ht]
        convert a 1 using 1
        module
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.mul_assoc, ← e, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem darboux_ext {R W κ : Type} [CommRing R] [AddCommGroup W] [Module R W] {B : W → W → R} [Fintype κ] {d d' : Darboux B κ}
    (h : ∀ w, d.e w = d'.e w) : d = d' := by
  cases d; cases d'
  congr
  exact LinearEquiv.ext h

theorem weilB_eq {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}
    {χ χ' : Chr F E} {om om' : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)}
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) JA JB d χ om) (h' : IsUWeilB (cA σ) (adeleClass F) ψ (-1) JA JB d χ' om')
    (g : UG (cA σ) JB) (a : AE F E) (a2 : a + a = 1) (ac : cA σ a = a) (t : GL β (AE F E))
    (ht : (t : Matrix β β (AE F E)) = a • (((g : GL β (AE F E)) : Matrix β β (AE F E)) + 1))
    (hχ : χ (GeneralLinearGroup.det t) = χ' (GeneralLinearGroup.det t)) : ∀ Φ ∈ schA F κ, om g Φ = om' g Φ := by
  obtain ⟨-, dd, od, h1, ⟨-, h2, h3⟩, h4⟩ := h
  obtain ⟨-, dd', od', h1', ⟨-, h2', h3'⟩, h4'⟩ := h'
  obtain rfl : dd = dd' := darboux_ext fun w => by rw [← fromCols_toCols w, h1, h1']
  have inv : ∀ (o : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) x φ, o x (o x⁻¹ φ) = φ := fun o x φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have sc : ∀ x, ∃ s : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), od' x φ = s • od x φ := fun x => by
    obtain ⟨s, hs⟩ := PositivityTheory.ThKF0.schur hψ dd (od x⁻¹ ∘ₗ od' x) (fun φ hφ => h2.pres _ _ (h2'.pres _ _ hφ))
      (fun l hl => h2'.adm x _ (h2.adm _ l hl)) fun w φ hφ => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, h2'.impl x w φ hφ, h2.impl _ _ _ (h2'.pres _ _ hφ), actB, actB,
          Matrix.mul_assoc, ← transpose_mul]
        change dd.rho ψ (w * ((x⁻¹ * x : UG (cA σ) (dbl JB)) : GL (β ⊕ β) (AE F E)).1ᵀ) _ = _
        simp
    refine ⟨s, fun φ hφ => ?_⟩
    rw [← map_smul, ← hs φ hφ, LinearMap.comp_apply, inv]
  choose s hs using sc
  obtain ⟨l, hl, hl1, φ₀, hφ₀, hl0⟩ := GlobalTheory.diagLagrangian_form F ψ κ
  have ne : ∀ x, od x φ₀ ≠ 0 := fun x e => by
    have := inv od x⁻¹ φ₀
    rw [inv_inv, e, map_zero] at this
    exact hl0 (by rw [← this, map_zero])
  have smul : ∀ x y, s (x * y) = s x * s y := fun x y => by
    refine smul_left_injective ℂ (ne (x * y)) ?_
    dsimp only
    rw [← hs _ _ hφ₀, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hs y _ hφ₀, map_smul,
      hs x _ (h2.pres _ _ hφ₀), smul_smul, mul_comm]
  have s1 : s 1 = 1 := smul_left_injective ℂ (ne 1) (by dsimp only; rw [← hs _ _ hφ₀, map_one, map_one, one_smul])
  have hinv : ∀ z : Matrix α β (AE F E), ∀ φ ∈ schA F (κ ⊕ κ), l (dd.rho ψ (z * (diagCols β)ᵀ) φ) = l φ := fun z φ hφ => by
    refine (congrArg (fun y => l (dd.rho ψ y φ)) (mul_diagT z)).trans ?_
    rw [Darboux.rho, h1]
    exact hl1 _ _ φ hφ
  have par : ∀ (p : UG (cA σ) (dbl JB)) (u : GL β (AE F E)), (p : GL (β ⊕ β) (AE F E)).1 * diagCols β = diagCols β * u.1 →
      χ (GeneralLinearGroup.det u) = χ' (GeneralLinearGroup.det u) → s p = 1 := fun p u e e' => by
    have a1 := h3 l hl hinv p u e φ₀ hφ₀
    have a2 := h3' l hl hinv p u e φ₀ hφ₀
    rw [hs p _ hφ₀, map_smul, ← e', ← a1, smul_eq_mul] at a2
    refine (mul_eq_right₀ ?_).1 a2
    rw [a1]
    refine mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) ?_) hl0
    exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (NNReal.coe_pos.2 MeasureTheory.distribHaarChar_pos) _).ne'
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl _ _ (cA σ) β JB g
  obtain ⟨n, w, p, e, hn, hp⟩ := cayley (cA σ) g gd hgd a a2 ac t ht
  have sg : s gd = 1 := by
    rw [e, smul, smul, smul, par n 1 hn (by simp), par p t hp hχ, mul_one, mul_one, ← smul, mul_inv_cancel, s1]
  obtain ⟨φ₂, hφ₂, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
  intro Φ hΦ
  have := hs gd _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Φ hΦ φ₂ hφ₂)
  rw [sg, one_smul, h4 g gd hgd Φ hΦ φ₂ hφ₂, h4' g gd hgd Φ hΦ φ₂ hφ₂] at this
  funext x
  exact (mul_right_cancel₀ h0 (congrFun this (Sum.elim x 0))).symm

theorem good_unit (hc : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {n : ℕ} (a : AE F E) (a2 : a + a = 1)
    (g : Matrix (Fin n) (Fin n) (AE F E)) (hg : ∀ i j, (g - 1) i j ∈ atI F E) (h0 : ∀ w, (g.map (piInf (τ w)) + 1).det ≠ 0) :
    ∃ t : GL (Fin n) (AE F E), t.1 = a • (g + 1) ∧ ((GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1 ∈ atI F E := by
  have e : a • (g + 1) = 1 + a • (g - 1) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * a2
  have h1 : (a • (g + 1)).det - 1 ∈ atI F E := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, map_one]
    have : (Ideal.Quotient.mk (atI F E)).mapMatrix (a • (g + 1)) = 1 := by
      rw [e, map_add, map_one, add_eq_left]
      ext i j
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ a (hg i j))
    rw [this, det_one]
  obtain ⟨u, hu, hu'⟩ := exists_unit hc τ (fun w => piInf (τ w) (a • (g + 1)).det) fun w => by
    have a0 : piInf (τ w) a ≠ 0 := fun z => by
      have := congrArg (piInf (τ w)) a2
      simp [z] at this
    rw [det_smul, map_mul, map_pow, RingHom.map_det, map_add, map_one]
    exact mul_ne_zero (pow_ne_zero _ a0) (h0 w)
  have : (a • (g + 1)).det = u := eq_of_inf hc τ (by simpa using sub_mem h1 hu) fun w => (hu' w).symm
  obtain ⟨t, ht⟩ := (isUnit_iff_isUnit_det _).2 (this ▸ u.isUnit)
  exact ⟨t, ht, by rw [GeneralLinearGroup.val_det_apply, ht]; exact h1⟩

open Polynomial in
theorem exists_rot {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) :
    ∃ z : ℂ, z * star z = 1 ∧ star z + 1 ≠ 0 ∧ ∀ w, (z • G w + 1).det ≠ 0 := by
  let q : ι → ℂ[X] := fun w => ((1 + C Complex.I * X) • (G w).map C + (1 - C Complex.I * X) • (1 : Matrix _ _ ℂ[X])).det
  have ev : ∀ w (x : ℂ), (q w).eval x = ((1 + Complex.I * x) • G w + (1 - Complex.I * x) • (1 : Matrix _ _ ℂ)).det := fun w x => by
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases e : i = j <;> simp [e, one_apply]
  have q0 : ∏ w, q w ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ e => by
    have := ev w Complex.I
    rw [e, Complex.I_mul_I] at this
    norm_num at this
    exact pow_ne_zero n two_ne_zero this.symm
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ))).exists_notMem_finite
    (finite_setOf_isRoot q0)
  have hk' : ∀ w, (q w).eval (k : ℂ) ≠ 0 := fun w e => hk (by
    change (∏ w, q w).eval _ = 0
    rw [eval_prod]; exact Finset.prod_eq_zero (Finset.mem_univ w) e)
  have b1 : (1 - Complex.I * k : ℂ) ≠ 0 := fun e => by simpa using congrArg Complex.re e
  have b2 : (1 + Complex.I * k : ℂ) ≠ 0 := fun e => by simpa using congrArg Complex.re e
  have st : star ((1 + Complex.I * k) / (1 - Complex.I * k) : ℂ) = (1 - Complex.I * k) / (1 + Complex.I * k) := by
    simp [sub_eq_add_neg]
  refine ⟨(1 + Complex.I * k) / (1 - Complex.I * k), by rw [st]; field_simp, ?_, fun w e => hk' w ?_⟩
  · rw [st, div_add_one b2]
    exact div_ne_zero (by norm_num) b2
  · rw [ev, show (1 + Complex.I * k) • G w + (1 - Complex.I * k) • (1 : Matrix _ _ ℂ) =
      (1 - Complex.I * k) • (((1 + Complex.I * k) / (1 - Complex.I * k)) • G w + 1) by
        rw [smul_add, smul_smul, mul_div_cancel₀ _ b1], det_smul, e, mul_zero]

theorem realUniq : Loc.RealUniq := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW χX' χW' om om' r s r' s' k hP hP' hk hk' g hg
  have hc := hP.base.cm
  obtain ⟨-, ⟨d₁, e₁, h₁⟩, -⟩ := hP.weil
  obtain ⟨-, ⟨d₂, e₂, h₂⟩, -⟩ := hP'.weil
  obtain rfl : d₁ = d₂ := darboux_ext fun w => by rw [← transpose_transpose w, e₁, e₂]
  let a : AE F E := algebraMap (AF F) _ ⅟2
  have a2 : a + a = 1 := by rw [← map_add, invOf_two_add_invOf_two, map_one]
  have good : ∀ x : UA σ X.J, (∀ i j, (mat x - 1) i j ∈ atI F E) → (∀ w, ((mat x).map (piInf (B.emb w)) + 1).det ≠ 0) →
      ∀ Φ ∈ schA F (Fin n × Fin d), om (x, 1) Φ = om' (x, 1) Φ := fun x hx h0 => by
    obtain ⟨t, ht, ht'⟩ := good_unit hc B.emb a a2 (mat x) hx h0
    exact weilB_eq hP.base.std h₁ h₂ x a a2 ((cA σ).commutes _) t ht (Circle.ext ((hk _ ht').trans (hk' _ ht').symm))
  obtain ⟨z, z1, z2, z3⟩ := exists_rot fun w => (mat g).map (piInf (B.emb w))
  obtain ⟨u, hu, hu'⟩ := exists_unit hc B.emb (fun _ => z) fun _ e => by simp [e] at z1
  have uu : (u : AE F E) * cA σ u = 1 := eq_of_inf hc B.emb (by
      have := add_mem (Ideal.mul_mem_right (cA σ u) _ hu) (at_cA (σ := σ) hu)
      rwa [map_sub, map_one, sub_mul, one_mul, sub_add_sub_cancel] at this)
    fun w => by rw [map_mul, piInf_cA hc, hu', z1, map_one]
  let ζ : UA σ X.J := ⟨Units.map (scalar (Fin n)).toMonoidHom u, by
    change (scalar (Fin n) (u : AE F E))ᵀ * _ * (scalar (Fin n) (u : AE F E)).map (cA σ) = _
    rw [scalar_apply, diagonal_transpose, diagonal_map (map_zero _)]
    ext i j
    rw [mul_diagonal, diagonal_mul, mul_right_comm, uu, one_mul]⟩
  have mζ : ∀ x : UA σ X.J, mat (ζ * x) = (u : AE F E) • mat x := fun x => by
    change scalar (Fin n) (u : AE F E) * mat x = _
    rw [scalar_apply, ← smul_eq_diagonal_mul]
  have mζ' : mat ζ⁻¹ = ((u⁻¹ : (AE F E)ˣ) : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    change scalar (Fin n) ((u⁻¹ : (AE F E)ˣ) : AE F E) = _
    rw [scalar_apply, smul_one_eq_diagonal]
  have g1 := good (ζ * g) (fun i j => by
      rw [mζ, show (u : AE F E) • mat g - 1 = (u : AE F E) • (mat g - 1) + ((u : AE F E) - 1) • 1 by
        rw [smul_sub, sub_smul, one_smul, sub_add_sub_cancel]]
      exact add_mem (Ideal.mul_mem_left _ _ (at_entry hg i j)) (Ideal.mul_mem_right _ _ hu))
    fun w => by
      convert z3 w using 3
      rw [mζ]; ext i j; simp [hu']
  have g2 := good ζ⁻¹ (fun i j => by
      rw [mζ', show ((u⁻¹ : (AE F E)ˣ) : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) - 1 =
        (((u⁻¹ : (AE F E)ˣ) : AE F E) - 1) • 1 by rw [sub_smul, one_smul]]
      exact Ideal.mul_mem_right _ _ (inv_at hu))
    fun w => by
      have : piInf (B.emb w) ((u⁻¹ : (AE F E)ˣ) : AE F E) = star z := by
        have h3 := congrArg (piInf (B.emb w)) u.mul_inv
        rw [map_mul, hu', map_one] at h3
        exact (eq_inv_of_mul_eq_one_right h3).trans (eq_inv_of_mul_eq_one_right z1).symm
      rw [show (mat ζ⁻¹).map (piInf (B.emb w)) + 1 = (star z + 1) • 1 by
        rw [mζ']; ext i j; by_cases e : i = j <;> simp [e, this], det_smul, det_one, mul_one]
      exact pow_ne_zero _ z2
  intro Φ hΦ
  have e : ((g, 1) : UA σ X.J × UA σ W.J) = (ζ⁻¹, 1) * (ζ * g, 1) := by simp
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, g1 Φ hΦ]
  exact g2 _ (h₂.1.pres (ζ * g) Φ hΦ)

end PositivityTheory.ThKG.CayleyTransformDarboux

end
