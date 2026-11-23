import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrConc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsSeed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open Polynomial
open scoped Matrix
set_option linter.overlappingInstances false
section SlopeTestRemainingChoices
variable {l : ℕ} [Fact l.Prime]
private theorem tri {a b c : Qbar l} (h : ‖a - b‖ < 1) (h' : ‖b - c‖ < 1) : ‖a - c‖ < 1 := by
  rw [← sub_add_sub_cancel a b c]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h h')
private theorem near_of_res {c : Coef l} {a b : c.O} (h : residue c.O a = residue c.O b) : ‖a.1 - b.1‖ < 1 := by
  have h1 : a - b ∈ maximalIdeal c.O := by
    rw [← residue_eq_zero_iff, map_sub, h, sub_self]
  have h2 := (Fr.sc_norm l c _).2.1 h1
  rwa [Subalgebra.coe_sub] at h2
private theorem norm_unit {c : Coef l} (a : c.Oˣ) : ‖a.val.1‖ = 1 :=
  le_antisymm (Fr.sc_norm l c _).1 (not_lt.1 fun h => (Fr.sc_norm l c _).2.2 h a.isUnit)
private theorem norm_of_near {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) : ‖a‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b) (by rw [hb]; exact h.ne)
  rwa [sub_add_cancel, hb, max_eq_right h.le] at this
private theorem near_mul {a b a' b' : Qbar l} (h : ‖a - b‖ < 1) (h' : ‖a' - b'‖ < 1) (hb : ‖b‖ = 1) (hb' : ‖b'‖ = 1) :
    ‖a * a' - b * b'‖ < 1 := by
  refine tri (b := b * a') ?_ ?_
  · rwa [← sub_mul, norm_mul, norm_of_near h' hb', mul_one]
  · rwa [← mul_sub, norm_mul, hb, one_mul]
private theorem near_zpow {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) (w : ℤ) : ‖a ^ w - b ^ w‖ < 1 := by
  have ha := norm_of_near h hb
  have hn : ∀ k : ℕ, ‖a ^ k - b ^ k‖ < 1 := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ]; exact near_mul ih h (by rw [norm_pow, hb, one_pow]) hb
  obtain ⟨k, rfl | rfl⟩ := w.eq_nat_or_neg
  · simpa using hn k
  · have ha0 : a ^ k ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero))
    have hb0 : b ^ k ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [hb]; exact one_ne_zero))
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_sub_inv ha0 hb0, norm_div, norm_mul, norm_pow, norm_pow, ha, hb,
      norm_sub_rev]
    simpa using hn k
private theorem eq_one_of_near {u : Qbar l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1) (h : ‖u - 1‖ < 1) : u = 1 :=
  _root_.UpperTheory.Reformulated.B.S7.eq_one_of_near hm hu h
private theorem one_of_diag {Γ : Type} [Group Γ] {n : ℕ} {r : Γ →* GL (Fin n) (Qbar l)} {H : Subgroup Γ}
    {χ : Fin n → Γ →* (Qbar l)ˣ} (h : IsDiagOn r H χ) {s : Γ} (hs : s ∈ H) (h1 : ∀ i, χ i s = 1) : r s = 1 := by
  obtain ⟨g, hg⟩ := h
  have : g * r s * g⁻¹ = 1 := Units.ext (by rw [hg s hs]; simp [h1])
  rwa [mul_inv_eq_one, mul_eq_left] at this
private theorem flag_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {r : Γ →* GL (Fin n) (Qbar l)}
    {κ : Fin n → Γ →* (Qbar l)ˣ} (hr : ∀ a b, Continuous fun g => (r g).val a b) (h : W.HasFlag r κ) (i : Fin n) :
    Continuous fun g => (κ i g).val := by
  obtain ⟨P, hP⟩ := h
  have : ∀ g, (κ i g).val = ∑ b, (∑ a, P.val i a * (r g).val a b) * (P⁻¹).val b i := fun g => by
    rw [← (hP g).2 i]
    simp only [Units.val_mul, Matrix.mul_apply]
  simp only [this]
  exact continuous_finset_sum _ fun b _ => (continuous_finset_sum _ fun a _ =>
    continuous_const.mul (hr a b)).mul continuous_const
private theorem comm_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {κ : Γ →* (Qbar l)ˣ}
    (h : Continuous fun g => (κ g).val) {g : Γ} (hg : g ∈ (commutator Γ).topologicalClosure) : κ g = 1 := by
  refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker κ) ?_ hg
  have : (κ.ker : Set Γ) = {g | (κ g).val = 1} := by ext; simp
  rw [this]
  exact isClosed_eq h continuous_const
private theorem pt_ex {c : Coef l} [Fr.IsCoef l c.O] {F : Fr.Frame l (ResidueField c.O)} {n : ℕ} (T : Setup F n)
    (r : F.G0 →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (hP : ∀ g, (r g).valᵀ * P.val * (r (F.conj g)).val = P.val)
    (ρ : T.G.G₀ →* GL (Fin n) (Qbar l)) (hρ : ρ = tw (r.comp T.K.π) (T.K.κA (Qbar l)))
    (hc : ∀ a b, Continuous fun g => (ρ g).val a b)
    (ψ : ∀ v, Fin n → T.G.Gv v →* (Qbar l)ˣ) (hf : ∀ v, W.HasFlag (ρ.comp (T.G.φ v)) (ψ v))
    (h1 : ∀ g, ∃ b : Fin n → c.O, (∀ i, residue c.O (b i) = T.r.chib i g) ∧
      ∀ k, ‖(ρ g).val.charpoly.coeff k - (∏ i, (X - C (b i).1)).coeff k‖ < 1)
    (h2 : ∀ u, ∀ g ∈ T.r.Ip u, ρ g = 1)
    (h3 : ∀ v i g, ∃ b : c.O, residue c.O b = T.r.chib i (T.G.φ v g) ∧ ‖(ψ v i g).val - b.1‖ < 1) :
    ∃ x : T.B.B →ₐ[c.O] Qbar l, T.B.u.Maps (x : T.B.B →+* Qbar l) (W.GDet.ofRep (W.mat ρ)) ψ := by
  refine (W.exists_determinantPair_over_algebraicIntegers l T.G c.O n T.r T.B ρ ψ hc ⟨P, fun g => ?_⟩ (fun i g a ha => ?_) h2 (fun v i g a ha => ?_)
    (fun v i g => ?_) hf).exists
  · have h := congrArg (fun u : c.Oˣ => algebraMap c.O (Qbar l) u) (T.K.κ_conj g)
    have e : ((T.G.eps c.O (Qbar l) g ^ (1 - (n : ℤ)) : (Qbar l)ˣ) : Qbar l) =
        algebraMap c.O (Qbar l) (T.G.eps c.O c.O g ^ (1 - (n : ℤ)) : c.Oˣ) :=
      congrArg Units.val (map_zpow (Units.map (algebraMap c.O (Qbar l) : c.O →* Qbar l)) (T.G.eps c.O c.O g) _).symm
    rw [e, ← h, hρ]
    change (tw _ _ g).valᵀ * _ * (tw _ _ _).val = _
    rw [tw_val, tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, T.K.π_conj, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul, Units.val_mul, map_mul]
    rfl
  · obtain ⟨b, hb, hk⟩ := h1 g
    have e : residue c.O ((-1) ^ i * (∏ j, (X - C (b j))).coeff (n - i)) = residue c.O a := by
      rw [ha, W.Resid.Dbar, W.GDet.lam, (AlgebraTools.Det.repApi _).2.1, map_mul, ← coeff_map, Polynomial.map_prod]
      change _ = _ * (Matrix.diagonal _).charpoly.coeff _
      rw [Matrix.charpoly_diagonal]
      simp only [map_pow, map_neg, map_one, Polynomial.map_sub, map_X, map_C, hb]
    refine tri ?_ (near_of_res e)
    rw [W.GDet.lam, (AlgebraTools.Det.repApi _).2.1]
    have e' : ((-1) ^ i * (∏ j, (X - C (b j))).coeff (n - i) : c.O).1 =
        (-1) ^ i * (∏ j, (X - C (b j).1)).coeff (n - i) := by
      have e0 : ∀ y : c.O, y.1 = algebraMap c.O (Qbar l) y := fun _ => rfl
      rw [e0 (_ * _), map_mul, ← coeff_map, Polynomial.map_prod, map_pow, map_neg, map_one]
      simp only [Polynomial.map_sub, map_X, map_C]
      rfl
    rw [e', ← mul_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hk (n - i)
  · obtain ⟨b, hb, hk⟩ := h3 v i g
    exact tri hk (near_of_res (by rw [hb, ha, T.K.psib]))
  · rw [T.r.th_comm v i g (T.K.mu v g.2), comm_one (flag_cont (r := ρ.comp (T.G.φ v)) (fun a b => (hc a b).comp (T.G.φ_cont v)) (hf v) i)
      (T.K.mu v g.2)]
    simp
private theorem t2_space_open_subgroup (F : W.GFrame l) : T2Space F.G₀ :=
  haveI : T3Space F.Γ := {}
  inferInstance
private theorem pr_surj {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := by
  rintro ⟨g, hg⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  obtain ⟨t, rfl⟩ := (V.hη g).1 hg
  exact ⟨t, rfl⟩
private theorem val_iff {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] {A : ValuationSubring Ω} {v : W.Plc L}
    (h : IsPlaceOver A v) : A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  simpa using h (l : ℕ)
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {n : ℕ} {ka : G L Ω →* (Qbar l)ˣ}
private def prT (R : CReal k c₁ f n ka) : G L Ω →* R.T.G.G₀ := R.V.pr
private theorem beta_ex (R : CReal k c₁ f n ka) : ∃ β : Fin n → G L Ω →* c₁.Oˣ,
    (∀ i s, residue c₁.O (β i s) = R.T.r.chib i (prT R s)) ∧
      ∀ i s, (β i s).val.1 = (Ψ (galEmb ℚ L Ω s)).val.1 ^ Fr.w n i * (ka s).val := by
  let j : c.O →+* c₁.O := (Subalgebra.inclusion R.le).toRingHom
  refine ⟨fun i => (W.pushCh j (Ψ.comp (galEmb ℚ L Ω))) ^ Fr.w n i * R.K.κ.comp R.V.pr, fun i s => ?_, fun i s => ?_⟩
  · have h : (Φ.ext f).Ψ (R.K.π (R.V.pr s)) = W.pushCh (residue c₁.O) (W.pushCh j (Ψ.comp (galEmb ℚ L Ω))) s := by
      rw [R.π_pr]
      apply Units.ext
      change f (Φ.Ψ (k.p _)) = _
      rw [k.psi]
      exact R.hf _ _ rfl
    refine Eq.trans ?_ (congrArg Units.val (R.K.chib i (R.V.pr s)).symm)
    rw [h]
    exact congrArg Units.val ((map_mul (Units.map (residue c₁.O : c₁.O →* ResidueField c₁.O)) _ _).trans
      (congrArg (· * _) (map_zpow _ _ _)))
  · rw [← R.κ_pr]
    refine (congrArg Units.val ((map_mul (Units.map (c₁.O.val : c₁.O →* Qbar l)) _ _).trans
      (congrArg (· * _) (map_zpow _ _ _)))).trans ?_
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
    rfl
private theorem main (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (hM : l ∣ M) (R : CReal k c₁ f n ka)
    (hka : IsKa σ M ι n ka) (χ' : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ) (hχ : ¬ l ∣ orderOf χ')
    (hc : ∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Ψ s).val.1‖ < 1) (m : ℕ) (hm : 2 ≤ m) (r : G L Ω →* GL (Fin n) (Qbar l))
    (hr : _root_.UpperTheory.V.Sd.IsSeedAlt ι σ (fun i => ((cycBar ℚ Ω l ^ j * χ') ^ Fr.w n i).comp (galEmb ℚ L Ω))
      (fun i => (χ' ^ Fr.w n i).comp (galEmb ℚ L Ω)) (fun i => m * Fr.w n i) ka r)
    (J : Ideal R.B₀.B) (hJ : R.B₀.PointTheoremBaseObject ι J) : R.T.IdealSpecializationPoint J := by
  have hε : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A,
      ‖(χ' (galEmb ℚ L Ω s)).val - (Ψ (galEmb ℚ L Ω s)).val.1‖ < 1 := fun A hA s hs => by
    have h1 : cycZ ℚ Ω l (galEmb ℚ L Ω s) = 1 := (places L Ω l A).2.2.2 hA hs
    have h2 := hc (galEmb ℚ L Ω s)
    simpa [cycBar, h1] using h2
  have hχo : ∀ s, (χ' s).val ^ orderOf χ' = 1 := fun s => by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one]; rfl
  obtain ⟨r', hr'c, hr', hform⟩ := UpperTheory.exists_frame_factorization_of_trivial_on_inertia k r hr.cont fun A hA s hs h1 =>
    one_of_diag (hr.away A hA) hs fun i => by
      have h2 : χ' (galEmb ℚ L Ω s) = 1 := Units.ext (eq_one_of_near hχ (hχo _) (by simpa [h1] using hε A hA s hs))
      simp [h2]
  obtain ⟨P, hPs, hP⟩ := hr.pair
  obtain ⟨β, hβ1, hβ2⟩ := beta_ex R
  have hκ : ∀ s, R.T.K.κA (Qbar l) (prT R s) = ka s := fun s => Units.ext (R.κ_pr s)
  have hkn : ∀ s, ‖(ka s).val‖ = 1 := fun s => R.κ_pr s ▸ norm_unit _
  have hzn : ∀ s (w : ℤ), ‖(Ψ s).val.1 ^ w‖ = 1 := fun s w => by rw [norm_zpow, norm_unit, one_zpow]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : R.T.G.G₀ →* GL (Fin n) (Qbar l), ρ = tw (r'.comp R.T.K.π) (R.T.K.κA (Qbar l)) := ⟨_, rfl⟩
  have hρr : ∀ s, ρ (prT R s) = tw r ka s := fun s => Units.ext (by
    rw [hρ, tw_val, tw_val, hκ, ← hr' s, ← R.π_pr s]; rfl)
  obtain ⟨hS1, -, hS3, hS4, -⟩ := Sd.shapeFacts l (G L Ω) n r ka
  have hS5' := (Sd.shapeFacts l (G L Ω) n (tw r ka) ka).2.2.2.2.1
  have htw : Continuous (tw r ka) := by
    have h1 : ∀ {r : G L Ω →* GL (Fin n) (Qbar l)} {ka : G L Ω →* (Qbar l)ˣ}, Continuous r → Continuous ka →
        Continuous fun s => (tw r ka s).val := fun h h' => by
      simp only [tw_val]
      exact (Units.continuous_val.comp h').smul (Units.continuous_val.comp h)
    refine Units.continuous_iff.2 ⟨h1 hr.cont hka.alg.1, ?_⟩
    simp only [← map_inv]
    exact (h1 hr.cont hka.alg.1).comp continuous_inv
  have hρc : ∀ a b, Continuous fun g => (ρ g).val a b := fun a b => by
    haveI := t2_space_open_subgroup R.T.G
    have hp : Continuous (prT R) := R.V.pr_cont W.continuous_resP
    have hq : Topology.IsQuotientMap (prT R) := hp.isClosedMap.isQuotientMap hp (pr_surj R.V)
    rw [hq.continuous_iff]
    simp only [Function.comp_def, hρr]
    exact (Units.continuous_val.comp htw).matrix_elem a b
  have hX : ∀ i s, ‖(((cycBar ℚ Ω l ^ j * χ') ^ Fr.w n i).comp (galEmb ℚ L Ω) s).val -
      (Ψ (galEmb ℚ L Ω s)).val.1 ^ Fr.w n i‖ < 1 := fun i s => by
    rw [MonoidHom.comp_apply, MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]
    exact near_zpow (hc _) (norm_unit _) _
  have htame : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A,
      (∀ i, R.T.r.chib i (prT R s) = 1) → tw r ka s = 1 := fun A hA s hs h1 => by
    obtain ⟨o, ho, hko⟩ := hka.ord
    refine one_of_diag (hS1 _ _ (hr.away A hA)) hs fun i => Units.ext ?_
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.zpow_apply, Units.val_mul, Units.val_zpow_eq_zpow_val]
    refine eq_one_of_near (m := orderOf χ' * o) (fun h => ((Fact.out : l.Prime).dvd_mul.1 h).elim hχ ho) ?_ ?_
    · rw [mul_pow, ← zpow_natCast, ← zpow_mul, mul_comm (Fr.w n i), zpow_mul, zpow_natCast, pow_mul, hχo, one_pow, one_zpow,
        one_mul, pow_mul', ← Units.val_pow_eq_pow_val, hko A hA s hs, Units.val_one, one_pow]
    · refine tri (near_mul (near_zpow (hε A hA s hs) (norm_unit _) _) (by simp) (hzn _ _) (hkn s)) ?_
      rw [← hβ2]
      exact near_of_res (b := 1) (by rw [hβ1, h1, map_one, Units.val_one])
  choose κ hκf hκi hκc using fun v : W.Vl l L => hr.above (R.s.A v) ((val_iff (R.s.hA v)).2 v.2)
  let ψ : ∀ v : W.Vl l L, Fin n → Dec (F := L) (R.s.A v) →* (Qbar l)ˣ := fun v i =>
    κ v i * ka.comp (Dec (F := L) (R.s.A v)).subtype
  have hfl : ∀ v : W.Vl l L, W.HasFlag ((tw r ka).comp (Dec (F := L) (R.s.A v)).subtype) (ψ v) := fun v => hS3 _ _ (hκf v)
  have hfl' : ∀ v, W.HasFlag (ρ.comp (R.T.G.φ v)) (ψ v) := fun v => by
    have : ρ.comp (R.T.G.φ v) = (tw r ka).comp (Dec (F := L) (R.s.A v.1)).subtype := MonoidHom.ext fun s => hρr s.1
    exact this ▸ hfl v
  refine (pt_ex R.T r' P (hform P hP) ρ hρ hρc ψ hfl' (fun g => ?_) (fun u g hg => ?_) (fun v i g => ?_)).elim
    fun x hx => ?_
  rotate_right
  · obtain ⟨ρ', h1, h2⟩ := UpperTheory.universalMaps_point_of_polarized_flagged_rep R.T (Qbar l) x r' ρ P ψ hPs (hform P hP) hρ hx hfl'
      ⟨hr.irr.1, fun _ _ _ => trivial, fun U hU hi => hr.irr.2.2 U hU fun s => hr' s ▸ hi (k.p0 s)⟩
    refine ⟨Qbar l, inferInstance, inferInstance, inferInstance, x, ρ', h1, ?_, h2⟩
    have hA := fun v : W.Vl l L => UpperTheory.diagonal_characters_regular_algebraic_of_inertia_weights H ι (R.s.hw v)
      ((val_iff (R.s.hw v)).1 ((val_iff (R.s.hA v)).2 v.2)) ka hka.alg n m hm (κ v) (hκi v)
    choose wt hwt1 hwt2 using fun v => (hA v).1
    have hψ : ∀ v i, W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R.B₀) x v i = ψ v i := hx.2
    refine hJ x wt (tw r ka) (by have := R.n23; omega) (by have := R.n23; omega) ⟨hwt1, fun v i => hψ v i ▸ hwt2 v i⟩
      ?_ htw hr.aut (fun s hs => htame _ ?_ s hs fun i => ?_)
      fun v => ⟨?_, fun a b => ?_⟩
    · refine (congrArg (W.GDet.comap · (prT R)) hx.1).trans (((AlgebraTools.Det.repApi _).2.2.2.2.2.2.1 _).trans ?_)
      exact congrArg _ (MonoidHom.ext fun s => congrArg Units.val (hρr s))
    · obtain ⟨d, rfl⟩ := hM
      refine fun h => R.v0M ?_
      rw [Nat.cast_mul, map_mul]
      exact mul_lt_one_of_lt_of_le h ((ValuationSubring.valuation_le_one_iff _ _).2 (natCast_mem _ d))
    · exact R.v0.1 i ⟨s, hs, rfl⟩
    · exact (funext (hψ v) : _ = ψ v) ▸ hfl v
    · rw [hψ, hψ]
      exact (hA v).2 a b
  · obtain ⟨s, rfl⟩ : ∃ s, prT R s = g := pr_surj R.V g
    refine ⟨fun i => β i s, fun i => hβ1 i s, fun a => ?_⟩
    rw [hρr]
    refine hS5' _ (fun i => W.pushCh (c₁.O.val : c₁.O →+* Qbar l) (β i)) 1 (fun i t => ?_) (hS4 _ hkn hr.res) (fun i t => ?_) s a
    · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hkn, mul_one]
      exact norm_of_near (hX i t) (hzn _ _)
    · change ‖(β i t).val.1 - _‖ < 1
      rw [hβ2, norm_sub_rev]
      exact near_mul (hX i t) (by simp) (hzn _ _) (hkn _)
  · obtain ⟨⟨s, hs, rfl⟩, h2⟩ := hg
    exact (hρr s).trans (htame _ (fun h => R.s.St_l u.1 u.2 ((val_iff (R.s.hA u.1)).1 h)) s hs fun i =>
      Subgroup.mem_iInf.1 h2 i)
  · refine ⟨β i g.1, hβ1 i g.1, ?_⟩
    rw [hβ2]
    exact near_mul (a' := (ka g.1).val) (tri (hκc v i g) (hX i g.1)) (by simp) (hzn _ _) (hkn _)
end SlopeTestRemainingChoices
theorem UpperTheory.V.Pr.seedPtOf_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.V.Pr.SeedPtOfAlt := by
  intro H Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k c₁ _ f n ka R hka χ' j hχ hc m hm r hr J hJ
  exact main H ι ((Dvd.intro _ rfl).trans hL.dvd) R hka χ' j hχ hc m hm r hr J hJ
end
