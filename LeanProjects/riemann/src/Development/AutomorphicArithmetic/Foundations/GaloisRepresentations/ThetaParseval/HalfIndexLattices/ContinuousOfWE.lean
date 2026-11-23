import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MemSEOfFin

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

noncomputable section

namespace UpperTheory.TP.W

private theorem exists_signChar {ι G : Type} [CommGroup G] (w : ι → G →* WithZero (Multiplicative ℤ))
    (hne : ∀ i g, w i g ≠ 0) (hfin : ∀ g, {i | w i g ≠ 1}.Finite) (s : ι → Circle) :
    ∃ κ : G →* Circle, ∀ g, κ g = ∏ᶠ i, s i ^ WithZero.log (w i g) := by
  have hsup : ∀ g, (Function.mulSupport fun i => s i ^ WithZero.log (w i g)).Finite := fun g =>
    (hfin g).subset fun i hi h => hi (by simp [h])
  refine ⟨{ toFun := fun g => ∏ᶠ i, s i ^ WithZero.log (w i g), map_one' := ?_, map_mul' := ?_ }, fun _ => rfl⟩
  · simp
  · intro x y
    rw [← finprod_mul_distrib (hsup x) (hsup y)]
    refine finprod_congr fun i => ?_
    rw [map_mul, WithZero.log_mul (hne i x) (hne i y), _root_.zpow_add]

private theorem finprod_invol {ι : Type} (c : ι → ι) (hc : ∀ i, c (c i) = i) (f : ι → Circle)
    (hf : (Function.mulSupport f).Finite) (h1 : ∀ i, f i * f (c i) = 1) (h2 : ∀ i, f i ≠ 1 → c i ≠ i) :
    ∏ᶠ i, f i = 1 := by
  rw [finprod_eq_prod f hf]
  refine Finset.prod_involution (fun i _ => c i) (fun i _ => h1 i) (fun i _ => h2 i) (fun i hi => ?_) (fun i _ => hc i)
  rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hi ⊢
  intro h
  exact hi (by simpa [h] using h1 i)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private def cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  ⟨P.asIdeal.comap (sgOF σ), Ideal.comap_isPrime _ _, by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro hb
    have : sgOF σ x ∈ P.asIdeal.comap (sgOF σ) := by
      show sgOF σ (sgOF σ x) ∈ P.asIdeal
      rw [sgOF_sgOF h]; exact hx
    rw [hb, Ideal.mem_bot] at this
    exact hx0 (by rw [← sgOF_sgOF h x, this, map_zero])⟩

private theorem mem_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    r ∈ (cj h P).asIdeal ↔ sgOF σ r ∈ P.asIdeal := Iff.rfl

private theorem cj_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) : cj h (cj h P) = P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun r => ?_)
  rw [mem_cj, mem_cj, sgOF_sgOF h]

private theorem cj_fx (h : IsCMExt F E σ) {P : HeightOneSpectrum (𝓞 E)} (hP : Fx σ P) : Fx σ (cj h P) := by
  intro r hr
  rw [mem_cj] at hr ⊢
  rw [sgOF_sgOF h]
  have := hP _ hr
  rwa [sgOF_sgOF h] at this

private theorem fx_of_cj_eq (h : IsCMExt F E σ) {P : HeightOneSpectrum (𝓞 E)} (hP : cj h P = P) : Fx σ P := by
  intro r hr
  have h1 : r ∈ (cj h P).asIdeal := by rw [hP]; exact hr
  exact h1

private theorem under_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    (cj h P).under (𝓞 F) = P.under (𝓞 F) := by
  refine HeightOneSpectrum.ext ?_
  show (P.asIdeal.comap (sgOF σ)).comap (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [Ideal.comap_comap]
  congr 1
  exact RingHom.ext sgOF_alg

private theorem absNorm_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (cj h P).asIdeal = Ideal.absNorm P.asIdeal := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom (sgOF σ) (sgOF σ)
    (RingHom.ext (sgOF_sgOF h)) (RingHom.ext (sgOF_sgOF h))
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine Nat.card_congr (Ideal.quotientEquiv (cj h P).asIdeal P.asIdeal e ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (e : 𝓞 E →+* 𝓞 E) e.surjective P.asIdeal).symm

private theorem ram_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    (cj h P).asIdeal.ramificationIdx (𝓞 F) = P.asIdeal.ramificationIdx (𝓞 F) := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have e1 := Ideal.ramificationIdxIn_eq_ramificationIdx ((cj h P).asIdeal.under (𝓞 F)) (cj h P).asIdeal (E ≃ₐ[F] E)
  have e2 := Ideal.ramificationIdxIn_eq_ramificationIdx (P.asIdeal.under (𝓞 F)) P.asIdeal (E ≃ₐ[F] E)
  have e3 : (cj h P).asIdeal.under (𝓞 F) = P.asIdeal.under (𝓞 F) := congrArg HeightOneSpectrum.asIdeal (under_cj h P)
  rw [← e1, ← e2, e3]

private def sgn (σ : E →ₐ[F] E) (lam : ℕ →* ℂ) (P : HeightOneSpectrum (𝓞 E)) : Circle :=
  if Fx σ P then 1 else
    if lam (Ideal.absNorm P.asIdeal) = (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) then 1 else -1

private theorem sgn_mul (lam : ℕ →* ℂ) (P : HeightOneSpectrum (𝓞 E)) : sgn σ lam P * sgn σ lam P = 1 := by
  unfold sgn
  split_ifs <;> simp

private theorem sgn_cj (h : IsCMExt F E σ) (lam : ℕ →* ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    sgn σ lam (cj h P) = sgn σ lam P := by
  have : Fx σ (cj h P) ↔ Fx σ P := ⟨fun a => cj_cj h P ▸ cj_fx h a, cj_fx h⟩
  unfold sgn
  simp only [this, absNorm_cj]

private theorem lam_eq {lam : ℕ →* ℂ} (hlam : GoodNorm (sgOF σ) lam) {P : HeightOneSpectrum (𝓞 E)} (hP : ¬ Fx σ P) :
    lam (Ideal.absNorm P.asIdeal) = (sgn σ lam P : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) := by
  have h2 : lam (Ideal.absNorm P.asIdeal) ^ 2 = (Ideal.absNorm P.asIdeal : ℂ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (hlam.2 P.asIdeal P.isMaximal (Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot)).1
  have h3 : ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ^ 2 = (Ideal.absNorm P.asIdeal : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  unfold sgn
  rw [if_neg hP]
  split_ifs with h
  · simpa using h
  · have h4 := sq_eq_sq_iff_eq_or_eq_neg.1 (h2.trans h3.symm)
    simpa using h4.resolve_left h

private theorem wv_ne (Q : HeightOneSpectrum (𝓞 E)) (z : (AEF F E)ˣ) : wv F E Q z ≠ 0 :=
  ((Group.isUnit z).map (wv F E Q)).ne_zero

private theorem wv_eq_one {Q : HeightOneSpectrum (𝓞 E)} {z : (AEF F E)ˣ} (h1 : Valued.v (ev F E Q z) ≤ 1)
    (h2 : Valued.v (ev F E Q ((z⁻¹ : (AEF F E)ˣ) : AEF F E)) ≤ 1) : wv F E Q z = 1 := by
  have e : wv F E Q z * wv F E Q z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = wv F E Q z * wv F E Q z⁻¹ := e.symm
    _ ≤ wv F E Q z := mul_le_of_le_one_right' h2

private theorem ev_int (y : AEF F E) : ∀ᶠ Q in Filter.cofinite, Valued.v (ev F E Q y) ≤ 1 := by
  filter_upwards [(GlobalTheory.LFun.finAdEquiv F E (finPartF F E y)).2] with Q hQ
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hQ

private theorem wv_fin (z : (AEF F E)ˣ) : {Q | wv F E Q z ≠ 1}.Finite := by
  refine (Filter.eventually_cofinite.1 ((ev_int (z : AEF F E)).and (ev_int ((z⁻¹ : (AEF F E)ˣ) : AEF F E)))).subset ?_
  intro Q hQ hc
  exact hQ (wv_eq_one hc.1 hc.2)

private theorem fin_of_SE {z : AF F ⊗[F] E} (hz : z ∈ GlobalTheory.HeckeExtend.SE F E) : finPartF F E z ∈ Formalism.IndefR.LiftF.intAEF F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨t, ⟨c, hc, e⟩, o, rfl⟩ := hg
    rw [one_smul] at e
    refine AddSubgroup.subset_closure ⟨c, hc, o, ?_⟩
    rw [map_mul, PositivityTheory.ThKW.Eta.fin_j, e]
    show (c ⊗ₜ[F] (1 : E)) * ((1 : Af F) ⊗ₜ[F] (o : E)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

private theorem wv_of_WE {z : (AEF F E)ˣ} (hz : z ∈ GlobalTheory.HeckeExtend.WE F E 1) (Q : HeightOneSpectrum (𝓞 E)) :
    wv F E Q z = 1 :=
  wv_eq_one ((int_iff _).1 (fin_of_SE (PositivityTheory.ThKW.Eta.mem_SE_of_CE hz.1)) Q)
    ((int_iff _).1 (fin_of_SE (PositivityTheory.ThKW.Eta.mem_SE_of_CE hz.2)) Q)

private theorem continuous_of_WE (κ : (AEF F E)ˣ →* Circle) (h : ∀ z ∈ GlobalTheory.HeckeExtend.WE F E 1, κ z = 1) :
    Continuous κ := by
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hWo : IsOpen (GlobalTheory.HeckeExtend.WE F E 1 : Set (AF F ⊗[F] E)ˣ) := by
    have ho := GlobalTheory.HeckeExtend.CE_isOpen F E 1 one_pos
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  refine continuous_of_continuousAt_one _ ?_
  unfold ContinuousAt
  rw [map_one]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hWo.mem_nhds (one_mem _)] with z hz
  exact (h z hz).symm

private theorem wv_idFF {v : HeightOneSpectrum (𝓞 F)} {Q : HeightOneSpectrum (𝓞 E)} (hv : Q.under (𝓞 F) = v)
    (a : (AF F)ˣ) : wv F E Q (idFF F E a) =
      Valued.v ((sndA F (a : AF F)) v) ^ Q.asIdeal.ramificationIdx (𝓞 F) := by
  subst hv
  have h0 : (sndA F (a : AF F)) (Q.under (𝓞 F)) ≠ 0 :=
    (a.isUnit.map ((evalV F (Q.under (𝓞 F))).comp (sndA F))).ne_zero
  rw [wv_apply]
  change Valued.v (ev F E Q (algebraMap (AF F) (AEF F E) (a : AF F))) = _
  rw [ev_alg]
  exact valued_complMap rfl h0

theorem kapEx : KapEx := by
  intro F E _ _ _ _ _ σ h lam hlam
  obtain ⟨κ, hκ⟩ := exists_signChar (wv F E) wv_ne wv_fin (sgn σ lam)
  have hsup : ∀ z, (Function.mulSupport fun Q => sgn σ lam Q ^ WithZero.log (wv F E Q z)).Finite := fun z =>
    (wv_fin z).subset fun i hi h => hi (by simp [h])
  refine ⟨κ, ?_, fun z => ?_, fun a => ?_, fun z hz => ?_, fun P hP z h1 h2 => ?_⟩
  · exact continuous_of_WE κ fun z hz => by
      rw [hκ]
      simp [wv_of_WE hz]
  · rw [hκ, ← finprod_mul_distrib (hsup z) (hsup z)]
    have : ∀ Q, sgn σ lam Q ^ WithZero.log (wv F E Q z) * sgn σ lam Q ^ WithZero.log (wv F E Q z) = 1 := fun Q => by
      rw [← _root_.mul_zpow, sgn_mul, _root_.one_zpow]
    simp [this]
  · rw [hκ]
    refine finprod_invol (cj h) (cj_cj h) _ (hsup _) (fun P => ?_) (fun P hP hc => hP ?_)
    · by_cases hP : Fx σ P
      · have a1 : sgn σ lam P = 1 := if_pos hP
        have a2 : sgn σ lam (cj h P) = 1 := if_pos (cj_fx h hP)
        rw [a1, a2, _root_.one_zpow, _root_.one_zpow, one_mul]
      · have e : wv F E (cj h P) (idFF F E a) = wv F E P (idFF F E a) := by
          rw [wv_idFF (under_cj h P), ram_cj, wv_idFF rfl]
        rw [sgn_cj, e, ← _root_.mul_zpow, sgn_mul, _root_.one_zpow]
    · have : sgn σ lam P = 1 := if_pos (fx_of_cj_eq h hc)
      rw [this, _root_.one_zpow]
  · rw [hκ]
    have : ∀ Q, sgn σ lam Q ^ WithZero.log (wv F E Q z) = 1 := fun Q => by
      by_cases hQ : Fx σ Q
      · have a1 : sgn σ lam Q = 1 := if_pos hQ
        rw [a1, _root_.one_zpow]
      · simp [hz Q hQ]
    simp [this]
  · have e : κ z = sgn σ lam P := by
      rw [hκ, finprod_eq_single _ P (fun Q hQ => by simp [h2 Q hQ]), h1, WithZero.log_exp, _root_.zpow_neg, zpow_one]
      exact inv_eq_of_mul_eq_one_left (sgn_mul lam P)
    rw [e]
    exact lam_eq hlam hP

end UpperTheory.TP.W

end
