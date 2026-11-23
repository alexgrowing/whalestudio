import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.WcocEdge0
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Witalg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IntCastEqZeroOfDvd
import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSetStatement
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.Zc

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private def E1 (X : Tower Ω ε) (l n : ℕ) [Fact l.Prime] (a b : X.Fn l) : Prop :=
  AdicCompletion.eval (idl l) (X.Kl l) n (a ![1, 0]) = AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0])

private theorem galB_col (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![1, 0]) := by
  have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
    funext i; fin_cases i <;> simp
  have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
  rw [hu] at hg
  exact hg

private theorem E1.gal {X : Tower Ω ε} {l n : ℕ} [Fact l.Prime] {a b : X.Fn l} (h : E1 X l n a b) (s : Ω ≃ₐ[ℚ] Ω) :
    E1 X l n (X.galB l s a) (X.galB l s b) := by
  unfold E1 at *
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply] at h
  rw [galB_col, galB_col, AdicCompletion.eval_apply, AdicCompletion.eval_apply, Tower.kmap]
  erw [AdicCompletion.map_val_apply, AdicCompletion.map_val_apply]
  rw [h]

private theorem cls_mul_pow (X : Tower Ω ε) (l n : ℕ) [Fact l.Prime] (f v : X.Kˣ) :
    X.cls l n (f * v ^ l ^ n) = X.cls l n f := by
  unfold Tower.cls
  rw [Submodule.Quotient.eq, ofMul_mul, TensorProduct.tmul_add, add_sub_cancel_left, ofMul_pow,
    TensorProduct.tmul_smul, ← Nat.cast_smul_eq_nsmul ℤ_[l]]
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  rw [Ideal.span_singleton_pow]
  push_cast
  exact Ideal.mem_span_singleton_self _

private theorem gal_sl_comm [IsAlgClosed Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {σ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω M)
    {f : X.K} (hf : f ∈ topL X M) (g : SL(2, ℤ)) : X.gal σ (X.sl (ofSL g) f) = X.sl (ofSL g) (X.gal σ f) := by
  rw [mem_lev_iff] at hf
  have hζ := isPrimitiveRoot_eOm ε hM
  exact X.recip M f (Nat.pos_of_ne_zero hM) hf _ hζ σ 1
    (by rw [zpow_one]; exact (mem_fixMu_iff σ).1 hσ _ hζ.pow_eq_one) g g (by simp)

private theorem FF_mul [IsAlgClosed Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) {σ τ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω (topMu l n m N))
    (hτ : wkMu X l n m N x c d τ ∈ topL X (topMu l n m N)) {u : X.K}
    (hu : wkMu X l n m N x c d (σ * τ) = wkMu X l n m N x c d σ * X.gal σ (wkMu X l n m N x c d τ) * u ^ l ^ n) :
    FF X l n m N x c d w gm (σ * τ) = FF X l n m N x c d w gm σ * X.gal σ (FF X l n m N x c d w gm τ) *
      (∏ r₀ : (ZMod l)ˣ, ∏ γ ∈ Gs N l (topMu l n m N),
        X.sl (ofSL (gm r₀ * liftSL _ γ)) u ^ ex l n w (gm r₀ * liftSL _ γ)) ^ l ^ n := by
  unfold FF
  simp only [map_prod, map_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r₀ _ => Finset.prod_congr rfl fun γ _ => ?_
  rw [hu, map_mul, map_mul, map_pow, gal_sl_comm X (NeZero.ne _) hσ hτ, mul_pow, mul_pow]
  ring

private theorem coc_col [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N]
    (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (hp : Par l N c d gm) (x : ZMod N) (w m n c₀ : ℕ) (hw : Odd w) (hm : 1 ≤ m)
    (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (hB : ∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ))
    {σ τ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω (topMu l n m N)) (hτ : τ ∈ fixMu Ω (topMu l n m N)) :
    E1 X l n (bB (σ * τ)) (bB σ + X.galB l σ (bB τ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨hmem, hco⟩ := wcoc ε X l N c d gm hp x m n hm
  obtain ⟨u, -, hu0, hu⟩ := hco σ hσ τ hτ
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  obtain ⟨hadd, -, hgal, -⟩ := witalg ε X l N n hN1
  obtain ⟨f₁, e₁, w₁⟩ := wit ε X l N c d gm hp x w m n c₀ hw hm σ _ (hB σ hσ)
  obtain ⟨f₂, e₂, w₂⟩ := wit ε X l N c d gm hp x w m n c₀ hw hm τ _ (hB τ hτ)
  obtain ⟨f₃, e₃, w₃⟩ := wit ε X l N c d gm hp x w m n c₀ hw hm (σ * τ) _ (hB _ (mul_mem hσ hτ))
  have hF := FF_mul X l n m N x c d w gm hσ (hmem τ).1 hu
  set U : X.K := ∏ r₀ : (ZMod l)ˣ, ∏ γ ∈ Gs N l (topMu l n m N),
    X.sl (ofSL (gm r₀ * liftSL _ γ)) u ^ ex l n w (gm r₀ * liftSL _ γ) with hUdef
  have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.2 fun r₀ _ => Finset.prod_ne_zero_iff.2 fun γ _ =>
    pow_ne_zero _ ((map_ne_zero _).2 hu0)
  let v : X.Kˣ := Units.mk0 (U ^ l ^ c₀) (pow_ne_zero _ hU0)
  have hfv : f₃ = (f₁ * Units.map (X.gal σ).toMonoidHom f₂) * v ^ l ^ n := by
    apply Units.ext
    have hv : ((v ^ l ^ n : X.Kˣ) : X.K) = (U ^ l ^ c₀) ^ l ^ n := by simp [v]
    have hg : ((Units.map (X.gal σ).toMonoidHom f₂ : X.Kˣ) : X.K) = X.gal σ f₂ := rfl
    rw [Units.val_mul, Units.val_mul, hv, hg, e₃, hF, e₁, e₂, map_pow, mul_pow, mul_pow]
    ring
  have h12 := hadd _ _ _ _ w₁ (hgal σ _ _ w₂)
  show AdicCompletion.eval (idl l) (X.Kl l) n _ = AdicCompletion.eval (idl l) (X.Kl l) n _
  rw [w₃.2.1, h12.2.1, hfv, cls_mul_pow]

private theorem cycM_mul' [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (s t : Ω ≃ₐ[ℚ] Ω) :
    cycM M (s * t) = cycM M s * cycM M t := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have h1 := cycM_apply M (s * t) hζ.pow_eq_one
  rw [AlgEquiv.mul_apply, cycM_apply M t hζ.pow_eq_one, map_pow, cycM_apply M s hζ.pow_eq_one, ← pow_mul] at h1
  apply Units.ext
  apply ZMod.val_injective
  refine hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ?_
  rw [← h1, Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hζ.pow_eq_one]

private theorem redTop_cycM [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N]
    (y : (ZMod (l ^ (m + n)))ˣ) (s : Ω ≃ₐ[ℚ] Ω)
    (h : s (zt ε l (m + n)) = zt ε l (m + n) ^ (y : ZMod (l ^ (m + n))).val) :
    redTop l n m N (cycM (topM l n m (N * N)) s) = y := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero l := ⟨hl0⟩
  have hζ : IsPrimitiveRoot (zt ε l (m + n)) (l ^ (m + n)) := by
    have h0 := isPrimitiveRoot_eOm ε (pow_ne_zero (m + n) hl0)
    rw [Nat.cast_pow] at h0
    exact h0
  have hz : zt ε l (m + n) ^ topM l n m (N * N) = 1 := (hζ.pow_eq_one_iff_dvd _).2 (Dvd.intro _ rfl)
  have h1 := cycM_apply (topM l n m (N * N)) s hz
  rw [h] at h1
  have h2 : (y : ZMod (l ^ (m + n))).val ≡ (cycM (topM l n m (N * N)) s : ZMod (topM l n m (N * N))).val [MOD l ^ (m + n)] := by
    have hpos : 0 < l ^ (m + n) := pow_pos (Nat.pos_of_ne_zero hl0) _
    exact hζ.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
      (by rw [← pow_eq_pow_mod _ hζ.pow_eq_one, ← pow_eq_pow_mod _ hζ.pow_eq_one]; exact h1)
  apply Units.ext
  show ZMod.castHom _ _ ((cycM (topM l n m (N * N)) s : (ZMod (topM l n m (N * N)))ˣ) : ZMod (topM l n m (N * N))) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ← ZMod.natCast_zmod_val (y : ZMod (l ^ (m + n)))]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 h2).symm.trans (by simp)

private theorem bTop_coc [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N]
    (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (hp : Par l N c d gm) (x : ZMod N) (w m n c₀ : ℕ) (hw : Odd w) (hm : 1 ≤ m)
    (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (hB : ∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ))
    (s t : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (topM l n m (N * N)))ˣ) :
    E1 X l n (bTop X l n m N bB (s * t) y)
      (bTop X l n m N bB s y + X.galB l s (bTop X l n m N bB t (y * (cycM (topM l n m (N * N)) s)⁻¹))) := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have h2 := (witalg ε X l N n hN1).2.2.2
  have hp' : shArg (topM l n m (N * N)) s y ∈ fixMu Ω (topMu l n m N) := shArg_mem_fixMu _ s y
  have hq' : shArg (topM l n m (N * N)) t (y * (cycM (topM l n m (N * N)) s)⁻¹) ∈ fixMu Ω (topMu l n m N) :=
    shArg_mem_fixMu _ t _
  have hc := (coc_col ε X l N c d gm hp x w m n c₀ hw hm bB hB hp' hq').gal (repM (topM l n m (N * N)) y)
  have e : shArg (topM l n m (N * N)) (s * t) y =
      shArg (topM l n m (N * N)) s y * shArg (topM l n m (N * N)) t (y * (cycM (topM l n m (N * N)) s)⁻¹) := by
    unfold shArg
    rw [cycM_mul', mul_inv, mul_assoc y]
    simp only [mul_assoc, mul_inv_cancel_left]
  have e2 : repM (topM l n m (N * N)) y * shArg (topM l n m (N * N)) s y =
      s * repM (topM l n m (N * N)) (y * (cycM (topM l n m (N * N)) s)⁻¹) := by
    unfold shArg
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [← e, map_add, ← h2, e2, h2] at hc
  exact hc

private theorem bMid_coc [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N]
    (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (hp : Par l N c d gm) (x : ZMod N) (w m n c₀ : ℕ) (hw : Odd w) (hm : 1 ≤ m)
    (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (hB : ∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ))
    (s t : Ω ≃ₐ[ℚ] Ω) (z y₀ : (ZMod (l ^ (m + n)))ˣ) (hy₀ : redTop l n m N (cycM (topM l n m (N * N)) s) = y₀) :
    E1 X l n (bMid X l n m N bB (s * t) z)
      (bMid X l n m N bB s z + X.galB l s (bMid X l n m N bB t (z * y₀⁻¹))) := by
  classical
  have hmul : ∀ a b, redTop l n m N (a * b) = redTop l n m N a * redTop l n m N b := fun a b => map_mul _ _ _
  have hinv : ∀ a, redTop l n m N a⁻¹ = (redTop l n m N a)⁻¹ := fun a => map_inv (Units.map _) a
  unfold E1 bMid
  rw [Finset.sum_apply, map_sum, map_sum (X.galB l s), Pi.add_apply, map_add, Finset.sum_apply, map_sum,
    Finset.sum_apply, map_sum,
    Finset.sum_congr rfl (fun y _ => bTop_coc ε X l N c d gm hp x w m n c₀ hw hm bB hB s t y)]
  simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_nbij' (fun y => y * (cycM (topM l n m (N * N)) s)⁻¹) (fun y => y * cycM (topM l n m (N * N)) s)
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [hmul, hinv, hy, hy₀]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [hmul, hy, hy₀, inv_mul_cancel_right]
  · intro y _; simp
  · intro y _; simp
  · intro y _; rfl

end UpperTheory.Kd.L.Zc

open UpperTheory.Kd.L.Zc in
theorem UpperTheory.Kd.L.zcoc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (w m n c₀ : ℕ), Odd w → 1 ≤ m → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l, (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ)) → (∀ s z, bMid X l n m N bB s z ∈ X.B N l w) ∧ ∀ χ : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ (m + n)))ˣ, (∀ s, s (zt ε l (m + n)) = zt ε l (m + n) ^ (χ s : ZMod (l ^ (m + n))).val) → ∀ s t, Stab A s → ∀ z (φ₁ φ₂ φ₃ : HahnSeries ℚ Ω), IsThB X A N l n (bMid X l n m N bB (s * t) z) φ₁ → IsThB X A N l n (bMid X l n m N bB s z) φ₂ → IsThB X A N l n (bMid X l n m N bB t (z * (χ s)⁻¹)) φ₃ → ∀ r, CgA A l n (φ₁.coeff r) (φ₂.coeff r + s (φ₃.coeff r)) := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm hp A hA x w m n c₀ hw hm bB hB
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hp.cop).symm
  have hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := X.j_hol
    exact ⟨φ, h2, h1⟩
  have hmem : ∀ s z, bMid X l n m N bB s z ∈ X.B N l w := by
    intro s z
    refine Submodule.sum_mem _ fun y _ => ?_
    exact GlobalTheory.T.galB_mem_kummer_invariant_set ε X ε.injective hj N l w hp.odd hp.five hcop hw _ _
      (hB _ (shArg_mem_fixMu (topM l n m (N * N)) s y)).1
  refine ⟨hmem, fun χ hχ s t hs z φ₁ φ₂ φ₃ h₁ h₂ h₃ r => ?_⟩
  have hg := GlobalTheory.T.isCuspFunctionalValue_galB_equivariant Ω ε X A N l n w s hA (fun x => (hs x).symm) _ (hmem t _) _ h₃
  obtain ⟨f₂, w₂, d₂⟩ := (isThB_iff X A N l n _ _).1 h₂
  obtain ⟨f₃, w₃, d₃⟩ := (isThB_iff X A N l n _ _).1 hg
  have hw' := (witalg ε X l N n hN1).1 _ _ _ _ w₂ w₃
  have hE := bMid_coc ε X l N c d gm hp x w m n c₀ hw hm bB hB s t z (χ s) (redTop_cycM l n m N (χ s) s (hχ s))
  have hT : IsThB X A N l n (bMid X l n m N bB (s * t) z) (φ₂ + HahnSeries.map φ₃ (s : Ω →+* Ω)) :=
    (isThB_iff X A N l n _ _).2 ⟨f₂ * f₃, ⟨hw'.1, hE.trans hw'.2.1, hw'.2.2⟩, GlobalTheory.ThAdd.isDl_mul d₂ d₃⟩
  have := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol hp.odd hp.cop hp.five hA n w hw _ (hmem _ _) _ _ h₁ hT r
  simpa using this
