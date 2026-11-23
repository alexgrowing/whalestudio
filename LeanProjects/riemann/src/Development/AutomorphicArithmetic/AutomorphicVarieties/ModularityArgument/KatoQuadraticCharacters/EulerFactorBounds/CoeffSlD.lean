import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.SymmetricSquareCoefficients

private theorem coeQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  unfold toGQ
  rw [dif_pos h]
  rfl

private theorem mulQ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by
    rw [Matrix.det_mul]
    exact mul_pos h h'
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coeQ _ hmm, coeQ _ h, coeQ _ h', Matrix.map_mul]

private theorem slQ (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  apply Subtype.ext
  apply Units.ext
  rw [coeQ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)]
  rfl

private theorem detD {N : ℕ} (hN : 0 < N) : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1]).det := by
  simpa [Matrix.det_fin_two_of] using hN

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem eOm_zero : eOm ε 0 = 1 := by
  simp only [eOm, Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun ε.injective 1

private theorem coeff_slD (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (f : X.K) (r : ℚ) :
    (X.exp (slD X N f)).coeff r = (X.exp f).coeff (r / N) := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hg : (((toGQ !![(N : ℤ), 0; 0, 1] : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(N : ℚ), 0; 0, 1] := by
    rw [coeQ _ (detD hN)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h10 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 0 = 0 := by simp [ent, hg]
  have h00 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 0 = N := by simp [ent, hg]
  have h01 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 1 = 0 := by simp [ent, hg]
  have h11 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 1 = 1 := by simp [ent, hg]
  have key := X.exp_upper _ h10 f (r / N)
  rw [h00, h01, h11, div_one, div_one, mul_zero, div_mul_cancel₀ _ hN', eOm_zero, one_mul] at key
  exact key

private theorem gal_slD (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (slD X N f) = slD X N (X.gal s f) := by
  apply X.exp.toRingHom.injective
  ext r
  change (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, coeff_slD X hN, coeff_slD X hN, X.gal_exp]

private theorem sl_slD (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (h h' : Matrix (Fin 2) (Fin 2) ℤ) (hh : 0 < h.det)
    (e : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) (f : X.K) :
    X.sl (toGQ h) (slD X N f) = slD X N (X.sl (toGQ h') f) := by
  have hD := detD hN
  have hh' : 0 < h'.det := by
    have key := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_mul] at key
    exact (mul_pos_iff_of_pos_right hD).1 (key ▸ mul_pos hD hh)
  unfold slD
  rw [← X.sl_mul, ← X.sl_mul, ← mulQ _ _ hD hh, ← mulQ _ _ hh' hD, e]

private theorem un_group (X : Tower Ω ε) (m : ℕ) :
    1 ∈ X.Un m ∧ ∀ f ∈ X.Un m, ∀ f' ∈ X.Un m, f * f' ∈ X.Un m ∧ f⁻¹ ∈ X.Un m := by
  refine ⟨fun W _ => ⟨1, by simp⟩, fun f hf f' hf' => ⟨fun W hW => ?_, fun W hW => ?_⟩⟩
  · obtain ⟨g, hg⟩ := hf W hW
    obtain ⟨g', hg'⟩ := hf' W hW
    refine ⟨g * g', ?_⟩
    have key : ((f * f' : X.Kˣ) : X.K) / ((g * g' : X.Kˣ) : X.K) ^ m = ((f : X.K) / (g : X.K) ^ m) * ((f' : X.K) / (g' : X.K) ^ m) := by
      rw [Units.val_mul, Units.val_mul]
      ring
    rw [key, map_mul, hg, hg', one_mul]
  · obtain ⟨g, hg⟩ := hf W hW
    refine ⟨g⁻¹, ?_⟩
    have key : ((f⁻¹ : X.Kˣ) : X.K) / ((g⁻¹ : X.Kˣ) : X.K) ^ m = ((f : X.K) / (g : X.K) ^ m)⁻¹ := by
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div]
      simp only [inv_pow, div_inv_eq_mul]
      ring
    rw [key, map_inv₀, hg, inv_one]

variable [IsAlgClosure ℚ Ω]

private theorem exPrim (M : ℕ) [NeZero M] : ∃ ζ : Ω, IsPrimitiveRoot ζ M := by
  haveI := IsAlgClosure.isAlgClosed ℚ (K := Ω)
  haveI := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne M)⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic M Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 (NeZero.pos M)).ne')
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.1 hζ⟩

private theorem uniq (M : ℕ) [NeZero M] (a b : ℕ) (h : ∀ z : Ω, z ^ M = 1 → z ^ a = z ^ b) :
    (a : ZMod M) = b := by
  obtain ⟨ζ, hζ⟩ := exPrim (Ω := Ω) M
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨M, NeZero.pos M, hζ.pow_eq_one⟩
  have key := hfin.pow_eq_pow_iff_modEq.1 (h ζ hζ.pow_eq_one)
  rw [← hζ.eq_orderOf] at key
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 key

private theorem cyc_app (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (z : Ω) (hz : z ^ M = 1) :
    s z = z ^ (cycM M s : ZMod M).val := by
  refine cycM_spec M s ?_ z hz
  obtain ⟨ζ, hζ⟩ := exPrim (Ω := Ω) M
  have hsζ : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hsζ.pow_eq_one
  have hcop : i.Coprime M := (hζ.pow_iff_coprime (NeZero.pos M) i).1 (hi' ▸ hsζ)
  refine ⟨ZMod.unitOfCoprime i hcop, fun w hw => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, map_pow, ← hi', ← pow_mul, ← pow_mul, mul_comm]

private theorem cyc_eq (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (a : ℕ) (h : ∀ z : Ω, z ^ M = 1 → s z = z ^ a) :
    (cycM M s : ZMod M) = a := by
  have key := uniq (Ω := Ω) M (cycM M s : ZMod M).val a (fun z hz => by rw [← cyc_app M s z hz, h z hz])
  rwa [ZMod.natCast_zmod_val] at key

private theorem rep_app (M : ℕ) [NeZero M] (y : (ZMod M)ˣ) (z : Ω) (hz : z ^ M = 1) :
    repM (Ω := Ω) M y z = z ^ (y : ZMod M).val := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨ζ, hζ⟩ := exPrim (Ω := Ω) M
  have hm : ∀ {ξ : Ω}, IsPrimitiveRoot ξ M → Polynomial.cyclotomic M ℚ = minpoly ℚ ξ := fun hξ =>
    minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
      (by rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
          exact hξ.isRoot_cyclotomic (NeZero.pos M)) (Polynomial.cyclotomic.monic M ℚ)
  obtain ⟨s, hs⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1
    ((hm (hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime y))).symm.trans (hm hζ))
  have hs' : s ζ = ζ ^ (y : ZMod M).val := hs
  refine repM_spec M y ⟨s, fun w hw => ?_⟩ z hz
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
  rw [map_pow, hs', ← pow_mul, ← pow_mul, mul_comm]

end UpperTheory.V.Z.Kato.Nb.SymmetricSquareCoefficients

open UpperTheory.V.Z.Kato.Nb.SymmetricSquareCoefficients in
theorem UpperTheory.V.Z.Kato.Nb.sSlD :
    UpperTheory.V.Z.Kato.Nb.SSlD := by
  intro Ω _ _ _ ε X N hN
  obtain ⟨φ, hφ1, hφ2⟩ := X.j_hol
  have hover := GlobalTheory.T.overAffineJLine_comap_sl_gal ε X ε.injective ⟨φ, hφ2, hφ1⟩
  refine ⟨fun s f => gal_slD X hN s f, fun h h' hh e f => sl_slD X hN h h' hh e f, slQ,
    fun h h' hh hh' => mulQ h h' hh hh', fun m q f hf => ?_, fun m s f hf => ?_, un_group X, fun M _ s => ?_⟩
  · exact KmapA.un_map X (X.sl q).toRingEquiv (fun W hW => (hover W hW).1 q) m f hf
  · exact KmapA.un_map X (X.gal s) (fun W hW => (hover W hW).2 s) m f hf
  refine ⟨?_, fun t => ?_, fun y => ?_, ?_, fun M' _ hM' => ?_⟩
  · have hspec : ∀ z : Ω, z ^ M = 1 → s z = z ^ (cycM M s : ZMod M).val := fun z hz => cyc_app M s z hz
    have heps : ∀ z : Ω, z ^ M = 1 → s z = z ^ (cyc M s).val := by
      unfold cyc
      exact Classical.epsilon_spec (p := fun y : ZMod M => ∀ z : Ω, z ^ M = 1 → s z = z ^ y.val) ⟨_, hspec⟩
    have key := uniq (Ω := Ω) M (cyc M s).val (cycM M s : ZMod M).val (fun z hz => by rw [← heps z hz, hspec z hz])
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at key
  · apply Units.ext
    rw [Units.val_mul, cyc_eq M (s * t) ((cycM M s : ZMod M).val * (cycM M t : ZMod M).val)
      (fun z hz => by rw [AlgEquiv.mul_apply, cyc_app M t z hz, map_pow, cyc_app M s z hz, ← pow_mul]),
      Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · apply Units.ext
    rw [cyc_eq M (repM M y) (y : ZMod M).val (fun z hz => rep_app M y z hz), ZMod.natCast_zmod_val]
  · rw [mem_fixMu_iff]
    constructor
    · intro hs
      apply Units.ext
      rw [cyc_eq M s 1 (fun z hz => by rw [pow_one]; exact hs z hz), Nat.cast_one, Units.val_one]
    · intro hs z hz
      rw [cyc_app M s z hz, hs, Units.val_one, ZMod.val_one_eq_one_mod]
      have key : z ^ (1 % M) = z ^ 1 := by
        conv_rhs => rw [← Nat.mod_add_div 1 M]
        rw [pow_add, pow_mul, hz, one_pow, mul_one]
      rw [key, pow_one]
  · apply Units.ext
    rw [Units.coe_map, cyc_eq M' s (cycM M s : ZMod M).val
      (fun z hz => cyc_app M s z (by obtain ⟨k, hk⟩ := hM'; rw [hk, pow_mul, hz, one_pow]))]
    simp [ZMod.castHom_apply, ZMod.natCast_val]
