import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaB

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
open Formalism.IndefR.LiftF Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.AutEtaA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Idem

variable (F E) in

def rI : AEF F E := algebraMap (AF F) (AEF F E) (pairA F 1 0)

theorem rI_idem : rI F E * rI F E = rI F E := by
  rw [rI, ← map_mul]
  congr 1
  exact Prod.ext (mul_one _) (mul_zero _)

theorem rI_mul_fin (ι : Af F) : rI F E * algebraMap (AF F) (AEF F E) (pairA F 0 ι) = 0 := by
  rw [rI, ← map_mul, show pairA F 1 0 * pairA F 0 ι = 0 from Prod.ext (mul_zero _) (zero_mul _), map_zero]

theorem infPart_rI : infPartF F E (rI F E) = 1 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 1 0 ⊗ₜ 1) = 1
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 1 0) = 1 from rfl, AlgHom.id_apply]
  rfl

theorem infPart_fin (ι : Af F) : infPartF F E (algebraMap (AF F) (AEF F E) (pairA F 0 ι)) = 0 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 ι ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 ι) = 0 from rfl, TensorProduct.zero_tmul]

theorem ev_rI (Q : HeightOneSpectrum (𝓞 E)) : ev F E Q (rI F E) = 0 := by
  rw [rI, ev_alg]
  exact map_zero _

theorem ev_fin (Q : HeightOneSpectrum (𝓞 E)) (ι : Af F) :
    ev F E Q (algebraMap (AF F) (AEF F E) (pairA F 0 ι)) = complMap rfl (evalV F (Q.under (𝓞 F)) ι) := by
  rw [ev_alg]
  rfl

theorem piInf_inc {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (incAF F E x) = τ.1 x := by
  change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [show compInf F E w ((1 : AF F) ⊗ₜ[F] x) = evInf F w 1 ⊗ₜ[F] x from rfl, infEmb_tmul, map_one, map_one, one_mul]

theorem piInf_rI {w : InfinitePlace F} (τ : EmbOver E w) : piInf τ (rI F E) = 1 := by
  have h1 : piInf τ (rI F E + algebraMap (AF F) (AEF F E) (pairA F 0 1)) = 1 := by
    rw [rI, ← map_add, show pairA F 1 0 + pairA F 0 1 = 1 from Prod.ext (add_zero _) (zero_add _), map_one, map_one]
  have h2 : piInf τ (algebraMap (AF F) (AEF F E) (pairA F 0 1)) = 0 := by
    change infEmb τ (compInf F E w (pairA F 0 1 ⊗ₜ[F] (1 : E))) = _
    rw [show compInf F E w (pairA F 0 1 ⊗ₜ[F] (1 : E)) = evInf F w (pairA F 0 1) ⊗ₜ[F] (1 : E) from rfl,
      show evInf F w (pairA F 0 1) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), TensorProduct.zero_tmul, map_zero]
  rw [map_add, h2, add_zero] at h1
  exact h1

end Idem

section Main

theorem eta_real {B : Base F E} {η : (AEF F E)ˣ →* Circle} (h3 : HasExp B.emb η (fun _ => 1)) (t : (AEF F E)ˣ) :
    (η (GlobalTheory.InertTrivial.proj (rI F E) rI_idem t) : ℂ) =
      ∏ w, piInf (B.emb w) (t : AEF F E) / (‖piInf (B.emb w) (t : AEF F E)‖ : ℂ) := by
  have hAt : At (evI F) (((GlobalTheory.InertTrivial.proj (rI F E) rI_idem t : (AEF F E)ˣ) : AEF F E) - 1) := by
    intro u hu
    have hu1 : u.1 = 0 := (RingEquiv.map_eq_zero_iff (InfiniteAdeleRing.ringEquiv_mixedSpace F)).1 hu
    have h0 : algebraMap (AF F) (AEF F E) u * rI F E = 0 := by
      rw [rI, ← map_mul, show u * pairA F 1 0 = 0 from Prod.ext (show u.1 * 1 = 0 by rw [hu1, zero_mul])
        (show u.2 * 0 = 0 from mul_zero _), map_zero]
    rw [GlobalTheory.InertTrivial.proj_val, Algebra.smul_def]
    linear_combination ((t : AEF F E) - 1) * h0
  rw [h3 _ hAt]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hpi : piInf (B.emb w) ((GlobalTheory.InertTrivial.proj (rI F E) rI_idem t : (AEF F E)ˣ) : AEF F E) =
      piInf (B.emb w) (t : AEF F E) := by
    rw [GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub, map_one, piInf_rI]
    ring
  rw [zpow_one, hpi]

set_option maxHeartbeats 1000000 in
theorem exists_half_character_eta_product {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {η : (AEF F E)ˣ →* Circle}
    (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1) (h3 : HasExp B.emb η (fun _ => 1)) (h4 : UnramInert σ η)
    {lam : ℕ →* ℂ} (hlam : GoodNorm (sgOF σ) lam)
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) :
    ∃ ε, IsHalfF σ ε ∧ ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ v, tauB B v x = r := by
  have hcm := hB.cm
  have : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  have := hB.unram
  obtain ⟨θ, d, ε, ι, hd0, hσθ, hθθ, hdec, e1, e2, e3, e4, e5, e6⟩ := exists_half hcm
  refine ⟨ε, ⟨e1, e2, e3, e6⟩, ?_⟩
  set J := algebraMap (AF F) (AEF F E) (pairA F 0 ι) with hJdef
  have hc2 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, e1]
  have hJ : J * J = J := by rw [← e4]; linear_combination e1 + hc2 + 2 * e2
  have hrJ : rI F E * J = 0 := rI_mul_fin ι
  have hf : (1 - rI F E - J) * (1 - rI F E - J) = 1 - rI F E - J := by
    linear_combination hJ + rI_idem (F := F) (E := E) + 2 * hrJ
  have evJ : ∀ Q : HeightOneSpectrum (𝓞 E), (Fx σ Q → ev F E Q J = 0) ∧ (¬ Fx σ Q → ev F E Q J = 1) := by
    intro Q
    rw [hJdef, ev_fin]
    rcases e5 (Q.under (𝓞 F)) with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · exact ⟨fun hQ => absurd h6 (not_sq_of_fx hcm hd0 hσθ hθθ hdec hQ), fun _ => by rw [h5, map_one]⟩
    · exact ⟨fun _ => by rw [h5, map_zero],
        fun hQ => absurd (sq_of_split hcm hd0 hσθ hθθ hdec (isSplit_of_not_fx hcm hQ)) h6⟩
  have hker : ∀ y : (AEF F E)ˣ, (∀ Q, Fx σ Q → wv F E Q y = 1) → (η.comp (GlobalTheory.InertTrivial.proj _ hf)) y = 1 := by
    intro y hy
    have hint : ∀ z : (AEF F E)ˣ, (∀ Q, Fx σ Q → wv F E Q z = 1) →
        finPartF F E (GlobalTheory.InertTrivial.proj _ hf z : AEF F E) ∈ intAEF F E := by
      intro z hz
      refine (int_iff _).2 fun Q => ?_
      have hevf : ev F E Q (1 - rI F E - J) = 1 - ev F E Q J := by rw [map_sub, map_sub, map_one, ev_rI, sub_zero]
      rw [GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub (ev F E Q) 1, map_one, hevf]
      by_cases hQ : Fx σ Q
      · rw [(evJ Q).1 hQ]
        simp only [sub_zero, one_mul, sub_self, add_zero]
        exact le_of_eq (hz Q hQ)
      · rw [(evJ Q).2 hQ]
        simp
    have hinf : infPartF F E (1 - rI F E - J) = 0 := by
      rw [map_sub, map_sub, map_one, infPart_rI, hJdef, infPart_fin]
      ring
    refine h4 _ ?_ ?_ (hint y hy) ?_
    · rw [GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub (infPartF F E) 1 (1 - rI F E - J), hinf, map_one]
      ring
    · intro e he
      have hcc : ∀ z, cAF σ (cAF σ z) = z := GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hcm)
      have heJ : e * J = e := by
        rw [← e4]
        rcases e6 e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · have : e * cAF σ ε = 0 := by
            have := congrArg (cAF σ) a2
            rwa [map_mul, hcc, map_zero, mul_comm] at this
          linear_combination a1 + this
        · have : e * cAF σ ε = e := by
            have := congrArg (cAF σ) a2
            rwa [map_mul, hcc, mul_comm] at this
          linear_combination a1 + this
      obtain ⟨he1, he2, v, ε', ⟨α, hα, -, -⟩, he3⟩ := he
      have her : e * rI F E = 0 := by
        have h0 : e = e * algebraMap (AF F) (AEF F E) ε' := by rw [← he3]; linear_combination -he1 - he2
        rw [h0, mul_assoc, mul_comm (algebraMap _ _ ε'), hα, rI_mul_fin, mul_zero]
      rw [GlobalTheory.InertTrivial.proj_val]
      linear_combination (1 - (y : AEF F E)) * her + (1 - (y : AEF F E)) * heJ
    · rw [← map_inv]
      exact hint _ fun Q hQ => by rw [map_inv, hy Q hQ, inv_one]
  have hgen : ∀ P, Fx σ P → ∃ z, wv F E P z = WithZero.exp (-1 : ℤ) ∧ (∀ Q, Q ≠ P → wv F E Q z = 1) ∧
      ((η.comp (GlobalTheory.InertTrivial.proj _ hf)) z : ℂ) = -1 := by
    intro P hP
    have hns : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (P.under (𝓞 F)) := fun hs =>
      not_sq_of_fx hcm hd0 hσθ hθθ hdec hP (sq_of_split hcm hd0 hσθ hθθ hdec hs)
    have hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (P.under (𝓞 F)) :=
      GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
    let π : (Fv F (P.under (𝓞 F)))ˣ := Formalism.L2.Host.atFin (P.under (𝓞 F)) (Formalism.L2.Host.unif (P.under (𝓞 F)))
    let a : (AF F)ˣ := Neutral.B1.localIdele F (P.under (𝓞 F)) π
    have ha1 : (a : AF F).2 (P.under (𝓞 F)) = π := Neutral.B1.localIdele_snd_self F (P.under (𝓞 F)) π
    have ha2 : ∀ u, u ≠ P.under (𝓞 F) → (a : AF F).2 u = 1 := fun u hu' => Pi.mulSingle_eq_of_ne hu' _
    have hι : evalV F (P.under (𝓞 F)) ι = 0 := by
      rcases e5 (P.under (𝓞 F)) with ⟨-, h6⟩ | ⟨h5, -⟩
      · exact absurd h6 (not_sq_of_fx hcm hd0 hσθ hθθ hdec hP)
      · exact h5
    refine ⟨idFF F E a, ?_, fun Q hQ => ?_, ?_⟩
    · rw [wv_apply]
      change Valued.v (ev F E P (algebraMap (AF F) (AEF F E) (a : AF F))) = _
      rw [ev_alg]
      change Valued.v (complMap rfl ((a : AF F).2 (P.under (𝓞 F)))) = _
      rw [ha1, valued_complMap rfl π.ne_zero, GlobalTheory.LFun.isUnram_iff.1 hu P rfl, pow_one]
      exact Formalism.L2.Host.unif_spec (P.under (𝓞 F))
    · have hQv : Q.under (𝓞 F) ≠ P.under (𝓞 F) := fun h => hQ (GlobalTheory.LFun.eq_of_not_isSplit hns h rfl)
      rw [wv_apply]
      change Valued.v (ev F E Q (algebraMap (AF F) (AEF F E) (a : AF F))) = _
      rw [ev_alg]
      change Valued.v (complMap rfl ((a : AF F).2 (Q.under (𝓞 F)))) = _
      rw [ha2 _ hQv, map_one, map_one]
    · have hsnd : (0 + ι) * ((a : AF F).2 - 1) = 0 := by
        refine GlobalTheory.SplitDetCharF.af_ext' F fun u => ?_
        rw [map_mul, map_sub, map_one, map_add, map_zero, zero_add]
        by_cases hu' : u = P.under (𝓞 F)
        · rw [hu', hι, zero_mul]
        · rw [show evalV F u (a : AF F).2 = 1 from ha2 u hu', sub_self, mul_zero]
      have hprod : (pairA F 1 0 + pairA F 0 ι) * ((a : AF F) - 1) = 0 :=
        Prod.ext (show (1 + 0) * ((a : AF F).1 - 1) = 0 by
          rw [show (a : AF F).1 = 1 from rfl]; ring) hsnd
      have hz : (rI F E + J) * (algebraMap (AF F) (AEF F E) (a : AF F) - 1) = 0 := by
        rw [rI, hJdef, ← map_add, ← map_one (algebraMap (AF F) (AEF F E)), ← map_sub, ← map_mul, hprod, map_zero]
      have hpz : GlobalTheory.InertTrivial.proj _ hf (idFF F E a) = idFF F E a := by
        refine Units.ext ?_
        rw [GlobalTheory.InertTrivial.proj_val]
        change (1 - rI F E - J) * algebraMap (AF F) (AEF F E) (a : AF F) + (1 - (1 - rI F E - J)) =
          algebraMap (AF F) (AEF F E) (a : AF F)
        linear_combination -hz
      show ((η (GlobalTheory.InertTrivial.proj _ hf (idFF F E a)) : Circle) : ℂ) = -1
      rw [hpz]
      obtain ⟨⟨η₀, h0⟩, hres⟩ := h2
      rw [hres η₀ h0 a, pow_one, GlobalTheory.EtaSignReal.eq_signToCircle η₀ h0, MonoidHom.comp_apply,
        GlobalTheory.LFun.normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2
          (GlobalTheory.LFun.not_mem_normGroup_of_inert hcm.2.2.1 hns hu (Formalism.L2.Host.unif_spec (P.under (𝓞 F))))]
      change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = -1
      rw [if_neg (by decide)]
      simp
  have hlamP : ∀ P : HeightOneSpectrum (𝓞 E),
      (Fx σ P → lam (Ideal.absNorm P.asIdeal) = -(Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)) ∧
      (¬ Fx σ P → lam (Ideal.absNorm P.asIdeal) = (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)) := fun P =>
    ⟨fun hP => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      exact ((hlam.2 P.asIdeal P.isMaximal (Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot)).2 hP).1,
    fun hP => hsq _ (fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) fun q hq hi hd =>
      hP (hi P.asIdeal P.isMaximal (GlobalTheory.EtaProduct.mem_of_dvd_absNorm P hq hd))⟩
  have lam_int : ∀ (u : 𝓞 E) (k : Eˣ), (k : E) = u → lam (Ideal.absNorm (Ideal.span {u})) =
      ((η.comp (GlobalTheory.InertTrivial.proj _ hf)) (Units.map (incAF F E).toMonoidHom k) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ) :=
    fun u k hk => hom_fix (Fx σ) (wv F E) (Units.map (incAF F E).toMonoidHom) (η.comp (GlobalTheory.InertTrivial.proj _ hf)) lam
      (fun Q k => wv_inc Q k) hker hgen hlamP u k hk
  have product : ∀ k : Eˣ, (η (GlobalTheory.InertTrivial.proj J hJ (Units.map (incAF F E).toMonoidHom k)) : ℂ) *
      ((η.comp (GlobalTheory.InertTrivial.proj _ hf)) (Units.map (incAF F E).toMonoidHom k) : ℂ) *
      ∏ w, tauB B w k / (‖tauB B w k‖ : ℂ) = 1 := by
    intro k
    have e0 := congrArg η (GlobalTheory.EtaProduct.proj_three (rI_idem (F := F) (E := E)) hJ hrJ hf
      (Units.map (incAF F E).toMonoidHom k))
    rw [h1.2 k, η.map_mul, η.map_mul] at e0
    have e1' := congrArg (fun z : Circle => (z : ℂ)) e0
    simp only [Circle.coe_mul, Circle.coe_one] at e1'
    have er := eta_real h3 (Units.map (incAF F E).toMonoidHom k)
    have hk' : ((Units.map (incAF F E).toMonoidHom k : (AEF F E)ˣ) : AEF F E) = incAF F E (k : E) := rfl
    rw [hk'] at er
    simp only [piInf_inc] at er
    rw [show ∏ w, tauB B w k / (‖tauB B w k‖ : ℂ) =
      (η (GlobalTheory.InertTrivial.proj (rI F E) rI_idem (Units.map (incAF F E).toMonoidHom k)) : ℂ) from er.symm]
    exact e1'.symm
  intro x k hx hk y hy
  obtain ⟨u, z, hz, e⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hzE : (z : E) ≠ 0 := by simpa using hz0
  have e' : x * (z : E) = u := by rw [← e]; exact div_mul_cancel₀ _ hzE
  have huE : (u : E) ≠ 0 := e' ▸ mul_ne_zero hx hzE
  have hN : ∀ a : 𝓞 E, ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℚ) = |Algebra.norm ℚ (a : E)| := fun a => by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]
  have hk' : k * Ideal.absNorm (Ideal.span {z}) = Ideal.absNorm (Ideal.span {u}) := by
    have : ((k * Ideal.absNorm (Ideal.span {z}) : ℕ) : ℚ) = (Ideal.absNorm (Ideal.span {u}) : ℕ) := by
      rw [Nat.cast_mul, hN, hN, hk, ← e', map_mul, abs_mul]
    exact_mod_cast this
  have nz : Ideal.absNorm (Ideal.span {z}) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using hz0
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx (by simpa using hk.symm)
  have l1 := lam_int u (Units.mk0 _ huE) rfl
  have l2 := lam_int z (Units.mk0 _ hzE) rfl
  have eu : Units.mk0 _ huE = Units.mk0 x hx * Units.mk0 _ hzE := Units.ext e'.symm
  rw [← hk', map_mul, l2, eu, map_mul, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul,
    Circle.coe_mul] at l1
  have l3 : lam k = ((η.comp (GlobalTheory.InertTrivial.proj _ hf)) (Units.map (incAF F E).toMonoidHom (Units.mk0 x hx)) : ℂ) *
      (Real.sqrt k : ℂ) := by
    refine mul_right_cancel₀ (l2 ▸ hlam.1 _ nz) (l1.trans ?_)
    ring
  have p := product (Units.mk0 x hx)
  have ey : GlobalTheory.InertTrivial.proj J hJ (Units.map (incAF F E).toMonoidHom (Units.mk0 x hx)) = y :=
    Units.ext (by rw [GlobalTheory.InertTrivial.proj_val, hy, e4]; rfl)
  rw [ey, Units.val_mk0, Finset.prod_div_distrib, ← Complex.ofReal_prod] at p
  have hp : 0 < ∏ w, ‖tauB B w x‖ := Finset.prod_pos fun w _ => norm_pos_iff.2 ((map_ne_zero _).2 hx)
  refine ⟨Real.sqrt k * ∏ w, ‖tauB B w x‖, mul_pos (Real.sqrt_pos.2 (by positivity)) hp, ?_⟩
  have hp' : ((∏ w, ‖tauB B w x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [← mul_div_assoc, div_eq_one_iff_eq hp'] at p
  rw [l3, Complex.ofReal_mul, ← p]
  ring

end Main

end PositivityTheory.ThKW.AutEtaA

end
