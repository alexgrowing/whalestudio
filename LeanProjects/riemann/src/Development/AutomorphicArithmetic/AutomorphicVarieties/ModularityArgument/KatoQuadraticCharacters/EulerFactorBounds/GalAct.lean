import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeAction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctionsStatement

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.GalAct

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem act_sl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (g h : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (h : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((g * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
    (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos) b

private theorem gam_le (N l : ℕ) : Gam N l ≤ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l :=
  inf_le_inf_right _ (CongruenceSubgroup.Gamma1_in_Gamma0 N)

private theorem conj_mem (N l : ℕ) (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gam N l)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) : δ * γ * δ⁻¹ ∈ Gam N l := by
  obtain ⟨a1, a2, a3⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 (Subgroup.mem_inf.1 hγ).1
  have a4 : ((δ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hδ).1
  refine GamComm.mul_inv_mem_Gam N l _ δ (mul_mem hδ (gam_le N l hγ)) hδ ?_ ?_
  · simp [en, Matrix.mul_apply, Fin.sum_univ_two, a1, a3]
  · simp [en, Matrix.mul_apply, Fin.sum_univ_two, a2, a4]

private theorem act_act_conj (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (γ δ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l ((δ * γ * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  rw [act_sl, act_sl, inv_mul_cancel_right]

private theorem galB_mem [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (hN : 0 < N)
    (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : b ∈ X.B N l w) : X.galB l s b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  have hA := (kmap_A_stable ε X ε.injective ⟨φ, h2, h1⟩ l).2 s
  have himg : X.galB l s '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨StabGal.galB_mem_Pol X l w s hA c hc.1, fun γ hγ => StabGal.inv_galB X N l w hN s c hc γ hγ⟩
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.galB l s) hb)

private theorem act_mem [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (δ : SL(2, ℤ))
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  have hA := (kmap_A_stable ε X ε.injective ⟨φ, h2, h1⟩ l).1 (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))
  have himg : X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ hA c hc.1, fun γ hγ => ?_⟩
    rw [act_act_conj, hc.2 _ (conj_mem N l γ δ hγ hδ)]
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.act l _) hb)

private theorem eval_congr (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (a t : X.Fn l) (ht : PolMod X l w n t)
    (hat : CgF X l n a t) (u v : Fin 2 → ℤ_[l]) (huv : ∀ i, PadicInt.toZModPow n (u i) = PadicInt.toZModPow n (v i)) :
    AdicCompletion.eval (idl l) (X.Kl l) n (a u) = AdicCompletion.eval (idl l) (X.Kl l) n (a v) := by
  obtain ⟨c, -, hc⟩ := ht
  have e : ∀ x, AdicCompletion.eval (idl l) (X.Kl l) n (a x) = AdicCompletion.eval (idl l) (X.Kl l) n (t x) := fun x => by
    rw [← sub_eq_zero, ← map_sub]; exact hat x
  rw [e, e, ← sub_eq_zero, ← map_sub, hc, hc, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← sub_smul, map_smul]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  simp [huv]

private theorem comm [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) (hN : 0 < N)
    (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : InvM X l N w n b) (δ : SL(2, ℤ))
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) :
    CgF X l n (X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b))
      (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b)) := by
  obtain ⟨⟨t, ht, hbt⟩, hinv, -⟩ := hb
  obtain ⟨hE, -, -, -, -, hact, hgal, -⟩ := sApi Ω ε X l n
  intro u
  have hcls := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  have hF := hcls.2.2.2.2.2.1
  obtain ⟨f, hf⟩ := hcls.1 (AdicCompletion.eval (idl l) (X.Kl l) n
    (b ![(mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))
  obtain ⟨M₀, hM₀, hlev⟩ := X.level (f : X.K)
  have hlp : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨M, hM, hM0, hMN, hMl, hMn⟩ : ∃ M : ℕ, 0 < M ∧ M₀ ∣ M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M :=
    ⟨M₀ * N * l * l ^ n, by positivity, ⟨N * l * l ^ n, by ring⟩, ⟨M₀ * l * l ^ n, by ring⟩,
      ⟨M₀ * N * l ^ n, by ring⟩, ⟨M₀ * N * l, by ring⟩⟩
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hMn s
  obtain ⟨g, h00, h01, h10, h11⟩ := GlobalTheory.exists_sl2_conj_diag_zmod M i hi δ
  have hc : (en δ 0 0 : ZMod M) = en g 0 0 ∧ (en δ 0 1 : ZMod M) = ((i : ℤ) : ZMod M) * en g 0 1 ∧
      ((i : ℤ) : ZMod M) * en δ 1 0 = en g 1 0 ∧ (en δ 1 1 : ZMod M) = en g 1 1 :=
    ⟨h00, by simpa only [Int.cast_natCast] using h01, by simpa only [Int.cast_natCast] using h10, h11⟩
  have hrec := X.recip M f hM (fun γ hγ => hlev γ (GamComm.gamma_le_of_dvd hM0 hγ)) ζ hζ s i
    (by rw [zpow_natCast, hs]) g δ hc
  have h10' : (((i : ℤ) * en δ 1 0 : ℤ) : ZMod M) = en g 1 0 := by push_cast; exact h10
  have hg0 : ∀ K : ℕ, K ∣ M → δ ∈ CongruenceSubgroup.Gamma0 K → g ∈ CongruenceSubgroup.Gamma0 K := fun K hK h => by
    have a : (en δ 1 0 : ZMod K) = 0 := CongruenceSubgroup.Gamma0_mem.1 h
    refine CongruenceSubgroup.Gamma0_mem.2 ((GamComm.intCast_eq_of_dvd hK h10').symm.trans ?_)
    rw [Int.cast_mul, a, mul_zero]
  have hgam : g * δ⁻¹ ∈ Gam N l :=
    GamComm.mul_inv_mem_Gam N l g δ
      (Subgroup.mem_inf.2 ⟨hg0 N hMN (Subgroup.mem_inf.1 hδ).1, hg0 l hMl (Subgroup.mem_inf.1 hδ).2⟩) hδ
      (GamComm.intCast_eq_of_dvd hMN h00) (GamComm.intCast_eq_of_dvd hMN h11)
  have hdg : CgF X l n (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) (X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b) := by
    have h := hact (δ : Matrix (Fin 2) (Fin 2) ℤ) _ _ (hinv _ hgam)
    rw [act_sl, inv_mul_cancel_right] at h
    exact hE.symm h
  have h1 := hgal s _ _ hdg u
  rw [map_sub, sub_eq_zero] at h1 ⊢
  rw [h1]
  have hpol := eval_congr X l w n b t ht hbt _ _
    (StabGal.twist_congr l n M hMn δ g i (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) hc
      (by simpa only [Int.cast_natCast] using hχ) u)
  have hL := hF (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hF (X.gal s) _ _ hf.symm)
  have hR := hF (X.gal s) _ _ (hF (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hpol.symm.trans hf.symm))
  refine hR.trans (Eq.trans ?_ hL.symm)
  congr 1
  apply Units.ext
  change X.gal s (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ)) f) = X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ)) (X.gal s f)
  rw [StabGal.toGQ_SL, StabGal.toGQ_SL, hrec]

private theorem polMod_galB [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ)
    (s : Ω ≃ₐ[ℚ] Ω) (t : X.Fn l) (ht : PolMod X l w n t) : PolMod X l w n (X.galB l s t) := by
  obtain ⟨c, hcU, hc⟩ := ht
  obtain ⟨-, -, -, -, hmap, -, hpow⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, -, hgU, hU, -⟩ := sSlD Ω ε X 1 one_pos
  refine ⟨fun i => ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i),
    fun i => ?_, fun u => ?_⟩
  · obtain ⟨f, hf, hr⟩ := hcU i
    obtain ⟨j, hj⟩ := hpow _ ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) _ (hmap (X.gal s) f _ hr)
    refine ⟨_, ?_, hj⟩
    have h0 : Units.map (X.gal s : X.K →* X.K) f ∈ X.Un (l ^ n) := hgU _ s f hf
    clear hj
    induction j with
    | zero => rw [pow_zero]; exact (hU _).1
    | succ k ih => rw [pow_succ]; exact ((hU _).2 _ ih _ h0).1
  · show X.kmap l (X.gal s) (t ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _
    rw [hc]
    simp only [map_sum, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

end UpperTheory.V.Z.Kato.Nb.GalAct

open UpperTheory.V.Z.Kato.Nb.GalAct in
theorem UpperTheory.V.Z.Kato.Nb.sGalAct :
    UpperTheory.V.Z.Kato.Nb.SGalAct := by
  intro Ω _ _ _ ε X l _ N w n hN s a ha
  have hcomm := comm X l N w n hN s a ha
  obtain ⟨⟨t, ht, hat⟩, hinv, b, hb, hba⟩ := ha
  obtain ⟨hE, -, -, -, -, hact, hgal, -⟩ := sApi Ω ε X l n
  have hba' : CgF X l n b (((l : ℤ_[l]) ^ cL X l N w) • a) := hba
  refine ⟨⟨⟨_, polMod_galB X l w n s t ht, hgal s _ _ hat⟩, fun γ hγ => ?_, X.galB l s b, galB_mem X l N w hN s b hb, ?_⟩,
    fun δ hδ => ⟨⟨⟨_, (sInvApi Ω ε X l N w n).2.2.2.2.2.2.2 _ t
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos) ht, hact _ _ _ hat⟩, fun γ hγ => ?_,
      X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b, act_mem X l N w δ hδ b hb, ?_⟩, hcomm δ hδ⟩⟩
  · exact hE.trans (hE.symm (hcomm γ (gam_le N l hγ))) (hgal s _ _ (hinv γ hγ))
  · have h := hgal s _ _ hba'
    rw [map_smul] at h
    exact h
  · rw [act_act_conj]
    exact hact _ _ _ (hinv _ (conj_mem N l γ δ hγ hδ))
  · have h := hact (δ : Matrix (Fin 2) (Fin 2) ℤ) _ _ hba'
    rw [map_smul] at h
    exact h
