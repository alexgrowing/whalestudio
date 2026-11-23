import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PrimeTypeRows
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockComplementLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistedGLEmbedding
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DeterminantInTorus

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.JumpDictionaryFoundation

section Emb

variable (D : D7)

theorem embOver_false_sqrt (ρ : D.what₂.Tau) :
    embOver D ρ false D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
  ((factEmb D.R D.host).2 _).2 (D.eTau ρ).2

theorem embOver_true_apply (ρ : D.what₂.Tau) (x : D.host.E) :
    embOver D ρ true x = starRingEnd ℂ (embOver D ρ false x) :=
  D.host.conjE_apply (embOver D ρ false) x

theorem conj_ne {R : Ranks} (H : Host R) :
    starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

theorem embOver_true_ne (ρ ρ' : D.what₂.Tau) : embOver D ρ true ≠ embOver D ρ' false := by
  intro h
  have h1 := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [embOver_true_apply, embOver_false_sqrt, embOver_false_sqrt] at h1
  exact conj_ne D.host h1

theorem sqrt_sq {R : Ranks} (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  apply H.φ₀.injective
  rw [map_pow, h3, h0]
  simp

theorem exists_embOver (φ : D.host.E →+* ℂ) : ∃ ρ b, φ = embOver D ρ b := by
  have key : ∀ ψ : D.host.E →+* ℂ, ψ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) →
      ∃ ρ, ψ = embOver D ρ false := by
    intro ψ h
    obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 ψ
    refine ⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 h⟩, ?_⟩
    simp [embOver]
  have h0 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h1 : φ D.host.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
    rw [← map_pow, sqrt_sq, h0]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · obtain ⟨ρ, h⟩ := key φ h2
    exact ⟨ρ, false, h⟩
  · obtain ⟨ρ, h⟩ := key ((starRingEnd ℂ).comp φ) (by rw [RingHom.comp_apply, h2]; simp)
    refine ⟨ρ, true, RingHom.ext fun x => ?_⟩
    rw [embOver_true_apply, ← h]
    simp

end Emb

section Frob

variable {R : Ranks} (H : Host R)

theorem exists_finite_split : ∃ A : Set (HeightOneSpectrum (𝓞 H.E)), A.Finite ∧
    ∀ v, v ∉ A → v.asIdeal.inertiaDeg ℤ = 1 → IsSplitPl H v := by
  have hint : IsIntegral ℤ H.sqrtMinusD := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    have := (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (H.d : ℤ))).neg
    simpa using this
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  let b : 𝓞 H.E := ⟨_, hint⟩
  have hb : c b - b ≠ 0 := by
    intro h
    have h1 : H.conj H.sqrtMinusD = H.sqrtMinusD := congrArg (fun y : 𝓞 H.E => (y : H.E)) (sub_eq_zero.1 h)
    have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
    have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
    have h4 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := h2
    rw [h1, h3] at h4
    exact conj_ne H h4.symm
  refine ⟨{v | v.asIdeal ∣ Ideal.span {c b - b}},
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hb), fun v hv hd => ?_⟩
  by_contra hs
  apply hv
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified H.E).1 v).2 hd
  have hst : ∀ x ∈ v.asIdeal, c x ∈ v.asIdeal := by
    intro x hx
    by_contra hx'
    refine hs ⟨x, hx, fun y hy => ?_⟩
    have : y = c x := RingOfIntegers.ext hy
    rwa [this]
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hcard : Nat.card (𝓞 H.E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := rfl
  have := v.isPrime
  have htop : AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) = ⊤ :=
    zmultiples_eq_top_of_prime_card hcard one_ne_zero
  have hmem : Ideal.Quotient.mk v.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) := by
    rw [htop]; trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
  have h1 : b - (n : 𝓞 H.E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq, ← hn]; simp
  have h2 := hst _ h1
  rw [map_sub, map_intCast] at h2
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  have := v.asIdeal.sub_mem h2 h1
  simpa using this

variable {H} {what₂ : Rows.Data R} (N : NData R H what₂)

theorem eq_of_frob (hC : GlobalTheory.TwSys.Cheb) (i : N.Loc) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    {a b : G H.E N.Om → Y} (ha : Continuous a) (hb : Continuous b)
    (h : ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → a σ = b σ) : a = b := by
  classical
  funext g
  by_contra hne
  have hV : IsOpen {s : G H.E N.Om | a (s * g) ≠ b (s * g)} :=
    (isClosed_eq (ha.comp (continuous_mul_const g)) (hb.comp (continuous_mul_const g))).isOpen_compl
  have : IsGalois H.E N.Om := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV (by simpa using hne)
  obtain ⟨A, hA, hsp⟩ := exists_finite_split H
  have hl : (placesOver H.E (N.l i)).Finite := by
    have h0 : ((N.l i : ℕ) : 𝓞 H.E) ≠ 0 := Nat.cast_ne_zero.2 (N.lPrime i).out.ne_zero
    refine (Ideal.finite_factors (I := Ideal.span {((N.l i : ℕ) : 𝓞 H.E)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  obtain ⟨v, hv, hd, -, B, hB, -, σ, hσ, hU'⟩ := hC H.E N.Om U.toSubgroup U.isOpen U.isNormal' g
    (hA.toFinset ∪ hl.toFinset ∪ N.S i ∪ N.Q i)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
  have := hU hU'
  simp only [Set.mem_ofPred_eq, inv_mul_cancel_right] at this
  exact this (h v ⟨hsp v hv.1.1.1 hd, hv.1.1.2, hv.1.2, hv.2⟩ B σ hB hσ)

end Frob

variable (D : D7)

def AlgebraicCharacter_at : Prop :=
  ∀ (i : D.nd.Loc) (π : D.naut.CG 1) (s : ℝ) (z : (D.host.E →+* ℂ) → ℤ),
    (∀ φ, (D.naut.infG π φ).map (· + (s : ℂ)) = {(z φ : ℂ)}) →
    ∃ r : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i)),
      Continuous (fun g => ((r g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i)))) ∧
      (∀ w : PlE D.host, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.locG π w) →
        ∀ (B : ValuationSubring D.nd.Om) (σ : GE D.nd), IsPlaceOver (F := D.host.E) B w →
          IsFrob (F := D.host.E) B (normV w) σ →
          D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) s) =
            {D.naut.iotaQC i (((r σ : GL (Fin 1) (Qbar (D.nd.l i))) :
              Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)}) ∧
      (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i r w) ∧
      ∀ τ : D.host.E →+* Qbar (D.nd.l i),
        D.naut.jumpsW i r τ = {-z ((D.naut.iotaQC i).toRingHom.comp τ)}

section Local

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def globEmb (τ : LocEmb D i w hw) : D.host.E →+* Qbar (D.nd.l i) :=
  (D.nbr i w hw).LL.1.val.toRingHom.comp (τ.toRingHom.comp (Br.cEw D.nbr i w hw))

theorem mult_eq_count {n : ℕ} (r : GE D.nd →* GL (Fin n) (D.nd.O i))
    (hc : Continuous fun g => ((r g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i)))
    (hd : Br.IsdRW D.loc D.nbr i w hw r) (τ : LocEmb D i w hw) (a : ℤ) :
    (Br.IsJumpW D.loc D.nbr i w hw r τ a ↔
      a ∈ D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) r) (globEmb D i w hw τ)) ∧
    Br.jumpMult D.loc D.nbr i w hw r τ a =
      ((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) r) (globEmb D i w hw τ)).count a : ℤ) := by
  have h := ((D.loc_tie i w hw).2.1 n r hc).2.2.2 (globEmb D i w hw τ) τ (fun _ => rfl)
  exact ⟨(h.1 hd a).symm, (h.2 hd a).symm⟩

theorem jumpsAre_of_mult {n : ℕ} (r : GE D.nd →* GL (Fin n) (D.nd.O i))
    (hc : Continuous fun g => ((r g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i)))
    (hd : Br.IsdRW D.loc D.nbr i w hw r) (τ : LocEmb D i w hw) (J : Multiset ℚ)
    (h1 : ∀ q ∈ J, ∃ a : ℤ, q = (a : ℚ))
    (h2 : ∀ a : ℤ, Br.jumpMult D.loc D.nbr i w hw r τ a = (J.count (a : ℚ) : ℤ)) :
    JumpsAre D i w hw r τ J := by
  refine ⟨h1, fun a => ?_, h2⟩
  obtain ⟨e1, e2⟩ := mult_eq_count D i w hw r hc hd τ a
  rw [h2 a, Nat.cast_inj] at e2
  rw [e1, ← Multiset.one_le_count_iff_mem, ← Multiset.one_le_count_iff_mem, e2]

include hw in
theorem continuous_iotaOQ : Continuous (iotaOQ D.nd D.naut i) := by
  have h : (iotaOQ D.nd D.naut i : D.nd.O i → Qbar (D.nd.l i)) =
      fun x => (((D.nbr i w hw).toLL x : ↥(D.nbr i w hw).LL.1) : Loc.Om (D.nd.l i)) :=
    funext (D.loc_tie i w hw).1
  rw [h]
  exact continuous_subtype_val.comp (continuous_subtype_val.comp (D.nbr i w hw).eO_cont)

end Local

section Block

variable (i : D.nd.Loc)

theorem chiGL_apply (k : ℕ) (g : GE D.nd) (a b : Fin 1) :
    ((chiGL D i k g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) a b =
      ((D.nd.chi i k g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain rfl : a = b := Subsingleton.elim _ _
  simp [chiGL]

theorem continuous_chiGL (k : ℕ) : Continuous fun g =>
    ((chiGL D i k g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [chiGL_apply]
  exact D.nd.chi_cont i k

def blockExp (k : ℕ) : ℝ := ((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2 + -((k : ℝ) - 1)

theorem chi_frob (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ D.R.t) (w : PlE D.host) (hw : SplitOut D.nd i w)
    (B : ValuationSubring D.nd.Om) (σ : GE D.nd) (hB : IsPlaceOver (F := D.host.E) B w)
    (hσ : IsFrob (F := D.host.E) B (normV w) σ) :
    D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) (blockExp D k)) =
      {D.naut.iotaQC i (iotaOQ D.nd D.naut i ((D.nd.chi i k σ : (D.nd.O i)ˣ) : D.nd.O i))} := by
  obtain ⟨hu, hf⟩ := D.naut.chi_mu i w hw
  rw [blockExp, ← D.naut.lpTw_add, D.naut.frobEig_tw _ _ ((D.naut.unr_tw _ _).2 hu), hf B σ hB hσ,
    Multiset.map_singleton, D.nd.chi_def i k h1 h2]
  congr 1
  have hc := cycZ_of_isFrob (l := D.nd.l i) hw.2.1 hB hσ
  let F : (D.nd.O i)ˣ →* ℂˣ := Units.map (iotaO D.nd D.naut i).toMonoidHom
  have hF : ∀ u : (D.nd.O i)ˣ, D.naut.iotaQC i (iotaOQ D.nd D.naut i (u : D.nd.O i)) = (F u : ℂ) := fun _ => rfl
  have he : (F (((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
      (cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i))) σ) : ℂ) = (normV w : ℂ) := by
    change iotaO D.nd D.naut i (algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      ((cycZ D.host.E D.nd.Om (D.nd.l i) σ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) = _
    rw [hc, map_natCast, map_natCast]
  rw [hF, MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow, Units.val_mul,
    Units.val_zpow_eq_zpow_val, he, ← Complex.cpow_intCast]
  push_cast
  rfl

end Block

theorem range_map_reflect (t : ℕ) (f : ℕ → ℚ) :
    (Multiset.range t).map (fun k => f (t - 1 - k)) = (Multiset.range t).map f := by
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ (Multiset.nodup_range t) (Multiset.nodup_range t)
    (fun k _ => t - 1 - k) (fun k hk => ?_) (fun a ha b hb h => ?_) (fun b hb => ⟨t - 1 - b, ?_, ?_⟩)
    (fun _ _ => rfl)
  all_goals simp only [Multiset.mem_range] at *
  all_goals omega

theorem icc_val (t : ℕ) : (Finset.Icc 1 t).val = (Multiset.range t).map (· + 1) := by
  refine (Multiset.Nodup.ext (Finset.Icc 1 t).nodup
    ((Multiset.nodup_range t).map (add_left_injective 1))).2 fun a => ?_
  simp only [Finset.mem_val, Finset.mem_Icc, Multiset.mem_map, Multiset.mem_range]
  exact ⟨fun h => ⟨a - 1, by omega, by omega⟩, fun ⟨b, h1, h2⟩ => by omega⟩

theorem fullPar_eq {R : Ranks} (P : HCParam R) (j : Fin R.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.fullPar P j = param P j := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.fullPar GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.sigPar GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.runPar param run
  rw [icc_val, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp]
  push_cast
  ring

theorem embAt_eq (ρ : D.what₂.Tau) (b : Bool) : GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.embAt D ρ (!b) = embOver D ρ b := by
  cases b <;> rfl

theorem paramTie_of_weightParam (h : WeightParam D) : GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.ParamTie D := by
  intro i ρ b
  rw [fullPar_eq]
  cases b
  · refine (h i ρ).2.trans (Multiset.map_congr rfl fun p _ => ?_)
    simp [GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.sg]
  · refine (h i ρ).1.trans (Multiset.map_congr rfl fun p _ => ?_)
    simp [GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.sg]

theorem exists_halves (R : Ranks) : ∃ u v : ℕ, R.r = 2 * u + 1 ∧ R.t = 2 * v + 1 ∧ R.nV = 2 * (u + v + 1) := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨v, hv⟩ := R.t_odd
  have := R.two_le_m
  refine ⟨a + b - 1, v, ?_, hv, ?_⟩ <;> simp only [Ranks.nV, Ranks.r] <;> omega

def firstJump (i : D.nd.Loc) (ρ : D.what₂.Tau) (b : Bool) : ℚ :=
  (if b then -1 else 1) * ((D.hc ρ).e (liftIdx D i) + 1 / 2) + (D.R.r : ℚ) / 2

theorem firstJump_int (i : D.nd.Loc) (ρ : D.what₂.Tau) (b : Bool) : ∃ a : ℤ, firstJump D i ρ b = a := by
  obtain ⟨u, v, hu, -, -⟩ := exists_halves D.R
  obtain ⟨e, he⟩ := (D.hc ρ).e_int (liftIdx D i)
  unfold firstJump
  rw [he, hu]
  cases b
  · exact ⟨e + u + 1, by simp; ring⟩
  · exact ⟨-e + u, by simp; ring⟩

theorem inf_block (hB : BlockCharParam D) (i : D.nd.Loc) (k : ℕ) (ρ : D.what₂.Tau) (b : Bool) :
    (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ b)).map (· + (blockExp D k : ℂ)) =
      {((-(firstJump D i ρ b + ((k : ℚ) - 1)) : ℚ) : ℂ)} := by
  cases b
  · rw [(hB i ρ).1, Multiset.map_singleton]
    congr 1
    simp only [blockExp, firstJump, Ranks.nV]
    push_cast
    simp
    ring
  · rw [(hB i ρ).2, Multiset.map_singleton]
    congr 1
    simp only [blockExp, firstJump, Ranks.nV]
    push_cast
    simp
    ring

theorem chi_jumps (hG : AlgebraicCharacter_at D) (hC : GlobalTheory.TwSys.Cheb) (hB : BlockCharParam D)
    (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ D.R.t) :
    Br.IsdRW D.loc D.nbr i w hw (chiGL D i k) ∧
    ∀ (τ : LocEmb D i w hw) (ρ : D.what₂.Tau) (b : Bool), cxEmb D i w hw τ = embOver D ρ b →
      JumpsAre D i w hw (chiGL D i k) τ {firstJump D i ρ b + ((k : ℚ) - 1)} := by
  have hz : ∀ φ, ∃ z : ℤ, (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) φ).map
      (· + (blockExp D k : ℂ)) = {(z : ℂ)} := by
    intro φ
    obtain ⟨ρ, b, rfl⟩ := exists_embOver D φ
    obtain ⟨a, ha⟩ := firstJump_int D i ρ b
    refine ⟨-(a + (k - 1)), ?_⟩
    rw [inf_block D hB, ha]
    push_cast
    rfl
  choose z hz using hz
  obtain ⟨r, hrc, hrf, hrd, hrj⟩ := hG i _ _ z hz
  have hr : r = mapRep (iotaOQ D.nd D.naut i) (chiGL D i k) := by
    have h := eq_of_frob D.nd hC i
      (a := fun g => ((r g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)
      (b := fun g => iotaOQ D.nd D.naut i ((D.nd.chi i k g : (D.nd.O i)ˣ) : D.nd.O i))
      ((continuous_apply 0).comp ((continuous_apply 0).comp hrc))
      ((continuous_iotaOQ D i w hw).comp (D.nd.chi_cont i k)) fun v hv B σ hB hσ => by
        have e1 := hrf v hv.2.1 (D.naut.chi_mu i v hv).1 B σ hB hσ
        rw [chi_frob D i k h1 h2 v hv B σ hB hσ, Multiset.singleton_inj] at e1
        exact ((D.naut.iotaQC i).injective e1).symm
    ext g a b
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    refine (congrFun h g).trans ?_
    rw [← chiGL_apply D i k g 0 0]
    rfl
  subst hr
  have hd : Br.IsdRW D.loc D.nbr i w hw (chiGL D i k) :=
    ((D.loc_tie i w hw).2.1 1 _ (continuous_chiGL D i k)).2.1.1 (hrd w hw)
  refine ⟨hd, fun τ ρ b hτ => ?_⟩
  have hq : firstJump D i ρ b + ((k : ℚ) - 1) = ((-z (embOver D ρ b) : ℤ) : ℚ) := by
    have e := (inf_block D hB i k ρ b).symm.trans (hz _)
    rw [Multiset.singleton_inj] at e
    have e' : -(firstJump D i ρ b + ((k : ℚ) - 1)) = (z (embOver D ρ b) : ℚ) := by exact_mod_cast e
    rw [Int.cast_neg, ← e', neg_neg]
  rw [hq]
  refine jumpsAre_of_mult D i w hw _ (continuous_chiGL D i k) hd τ _
    (fun q hq => ⟨_, Multiset.mem_singleton.1 hq⟩) fun a => ?_
  rw [(mult_eq_count D i w hw _ (continuous_chiGL D i k) hd τ a).2, hrj, ← hτ]
  simp only [Multiset.count_singleton, Int.cast_inj]
  rfl

theorem summand_of_complement (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) : Summand_at D := by
  intro i π hπ r hr k h1 h2
  obtain ⟨ρ, ⟨e, he⟩, -, -⟩ := h i π hπ r hr
  let c : Fin D.R.t := ⟨k - 1, by omega⟩
  have hc : c.1 + 1 = k := by simp only [c]; omega
  let f : (Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] KK D.nd i :=
    (LinearMap.proj c) ∘ₗ (LinearMap.snd _ _ _) ∘ₗ e.toLinearMap
  have hf : ∀ u, f u = (e u).2 c := fun _ => rfl
  have hrep : ∀ g u, matRep (mapM (toK D.nd i) ((Units.coeHom _).comp r)) g u =
      GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.fracRep r g u := fun _ _ => rfl
  have hv : f (e.symm (0, Pi.single c 1)) = 1 := by simp [hf]
  refine ⟨e.symm (0, Pi.single c 1), LinearMap.ker f, fun h0 => ?_, fun g => ?_, fun g u hu => ?_, ?_⟩
  · rw [h0, map_zero] at hv
    exact zero_ne_one hv
  · apply e.injective
    rw [hrep, he, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply, map_smul, e.apply_symm_apply]
    refine Prod.ext (by simp) (funext fun c' => ?_)
    by_cases hcc : c' = c
    · subst hcc
      simp only [hc, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    · simp [Pi.single_eq_of_ne hcc]
  · rw [LinearMap.mem_ker, hf] at hu ⊢
    rw [hrep, he, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply]
    simp [hu]
  · set v := e.symm (0, Pi.single c 1)
    refine ⟨Submodule.disjoint_def.2 fun u h1 h2 => ?_, codisjoint_iff.2 (eq_top_iff.2 fun u _ => ?_)⟩
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 h1
      rw [LinearMap.mem_ker, map_smul, hv, smul_eq_mul, mul_one] at h2
      rw [h2, zero_smul]
    · refine Submodule.mem_sup.2 ⟨f u • v, Submodule.mem_span_singleton.2 ⟨_, rfl⟩, u - f u • v, ?_, by simp⟩
      rw [LinearMap.mem_ker, map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]

open Classical in

def shift (φ : D.host.E →+* ℂ) : ℤ :=
  if ∃ ρ, φ = embOver D ρ false then (D.R.nV / 2 : ℕ) else ((D.R.nV / 2 : ℕ) : ℤ) - 1

theorem shift_embOver (ρ : D.what₂.Tau) (b : Bool) :
    (shift D (embOver D ρ b) : ℚ) = (D.R.nV : ℚ) / 2 - if b then 1 else 0 := by
  obtain ⟨u, v, -, -, hn⟩ := exists_halves D.R
  have h2 : D.R.nV / 2 = u + v + 1 := by omega
  unfold shift
  cases b
  · rw [if_pos ⟨ρ, rfl⟩, h2, hn]
    simp
  · rw [if_neg (fun ⟨ρ', h⟩ => embOver_true_ne D ρ ρ' h), h2, hn]
    simp

theorem jumpsWith (hJ : GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.Explicit_at D) (hW : WeightParam D) :
    JumpsWith D true fun _ _ => shift D := by
  intro i x r hr w hw τ ρ b hτ
  obtain ⟨hd, hj⟩ := hJ (paramTie_of_weightParam D hW) i x r hr w hw
  have key : GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.JumpsAre D i w hw r τ ((PP D i ρ).map fun p =>
      sgnOf true b * p + (shift D (embOver D ρ b) : ℚ)) := by
    rw [shift_embOver]
    cases b
    · have h := ((hj τ ρ).1 hτ).1
      rw [fullPar_eq] at h
      convert h using 1
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [sgnOf]
      norm_num
      ring
    · have h := (hj τ ρ).2 hτ
      rw [fullPar_eq] at h
      convert h using 1
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [sgnOf]
      norm_num
      ring
  exact jumpsAre_of_mult D i w hw r hr.1 hd τ _ key.1 key.2

theorem block_interval (i : D.nd.Loc) (ρ : D.what₂.Tau) (b : Bool) :
    ((blockPP D i ρ).map fun p => sgnOf true b * p + (shift D (embOver D ρ b) : ℚ)) =
      (Multiset.range D.R.t).map fun k : ℕ => firstJump D i ρ b + (k : ℚ) := by
  rw [shift_embOver, blockPP, run, Multiset.map_map]
  cases b
  · refine Multiset.map_congr rfl fun k _ => ?_
    simp only [Function.comp, sgnOf, firstJump, Ranks.nV]
    norm_num
    ring
  · rw [← range_map_reflect D.R.t fun k : ℕ => firstJump D i ρ true + (k : ℚ)]
    refine Multiset.map_congr rfl fun k hk => ?_
    rw [Multiset.mem_range] at hk
    have e : ((D.R.t - 1 - k : ℕ) : ℚ) = (D.R.t : ℚ) - 1 - k := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    simp only [Function.comp, sgnOf, firstJump, Ranks.nV, e]
    norm_num
    ring

theorem blockWith (hG : AlgebraicCharacter_at D) (hC : GlobalTheory.TwSys.Cheb) (hB : BlockCharParam D) :
    BlockWith D true fun _ _ => shift D := by
  intro i w hw
  refine ⟨fun k h1 h2 => (chi_jumps D hG hC hB i w hw k h1 h2).1, fun τ ρ b hτ => ?_⟩
  obtain ⟨a, ha⟩ := firstJump_int D i ρ b
  refine ⟨a, fun k h1 h2 => ?_, ?_⟩
  · rw [← ha]
    exact (chi_jumps D hG hC hB i w hw k h1 h2).2 τ ρ b hτ
  · rw [← ha]
    exact block_interval D i ρ b

theorem jumpDictTied_at (hJ : GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.Explicit_at D) (hG : AlgebraicCharacter_at D)
    (hC : GlobalTheory.TwSys.Cheb) (hZ : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) : JumpDictionaryAt D := fun hW hB =>
  ⟨fun i x r hr w hw => (hJ (paramTie_of_weightParam D hW) i x r hr w hw).1,
    ⟨true, fun _ _ => shift D, jumpsWith D hJ hW, blockWith D hG hC hB⟩, summand_of_complement D hZ⟩

theorem jumpDict_at (hW : WeightParam D) (hB : BlockCharParam D) (hJ : GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.Explicit_at D)
    (hG : AlgebraicCharacter_at D) (hC : GlobalTheory.TwSys.Cheb) (hZ : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) :
    JumpDict_at D := jumpDictTied_at D hJ hG hC hZ hW hB

def InputsF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x, Fm.x1 < x → ∀ a : Fm.Ix x, WeightParam (Fm.D x a) ∧ BlockCharParam (Fm.D x a) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions.Explicit_at (Fm.D x a) ∧ AlgebraicCharacter_at (Fm.D x a) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at (Fm.D x a)

theorem jumpDictF {eps : ℝ} (Fm : FamP eps) (hC : GlobalTheory.TwSys.Cheb) (h : InputsF Fm) : JumpDictF Fm := by
  intro x hx a
  obtain ⟨hW, hB, hJ, hG, hZ⟩ := h x hx a
  exact jumpDict_at _ hW hB hJ hG hC hZ

theorem jumpDictClosed (C : FamClass) (hC : GlobalTheory.TwSys.Cheb) (h : Closed C fun Fm _ => InputsF Fm) :
    JumpDictClosed C := h.imp fun Fm _ _ hI => jumpDictF Fm hC hI

theorem fullPar_eq' {R : Ranks} (P : HCParam R) (j : Fin R.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.fullPar P j = param P j := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.fullPar GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.sigPar GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.runPar param run
  congr 1
  refine Multiset.map_congr rfl fun k _ => ?_
  ring

theorem weightTie_of_weightParam (h : WeightParam D) : GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.WeightTie D := by
  intro i ρ
  rw [GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.lamWt_eq, fullPar_eq', Multiset.map_map, Multiset.map_map]
  refine ⟨(h i ρ).1, (h i ρ).2.trans (Multiset.map_congr rfl fun p _ => ?_)⟩
  simp

theorem blockCharParam_of_charTie (h : GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.CharTie D) : BlockCharParam D := by
  intro i ρ
  obtain ⟨h1, h2, h3⟩ := h ρ
  constructor
  · refine (D.naut.infG_tw _ _ _ _ h2).trans ?_
    rw [(h1 i).1, Multiset.map_singleton]
    congr 1
    push_cast
    rfl
  · refine (D.naut.infG_tw _ _ _ _ h3).trans ?_
    rw [(h1 i).2, Multiset.map_singleton]
    congr 1
    push_cast
    rfl

theorem exists_family {i : D.nd.Loc} (hR : GlobalTheory.IndefiniteRowSideFullHecke.DeterminantInTorus.RxConcl D i) {x : D.nd.X i}
    {r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)} (hr : IsHeckeGalois D.nd i x r) :
    ∃ r', GoodR D.nd i r' ∧ r' x = r := by
  classical
  obtain ⟨r₀, h₀, -⟩ := hR
  refine ⟨Function.update r₀ x r, fun y => ?_, Function.update_self ..⟩
  by_cases hy : y = x
  · subst hy
    rwa [Function.update_self]
  · rw [Function.update_of_ne hy]
    exact h₀ y

theorem jumpDictCrys_at_of_weights (hW : WeightParam D) (hT : GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.CharTie D)
    (hG2 : GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.Weights_at D) (hR : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DeterminantInTorus.RxConcl D i)
    (hG : AlgebraicCharacter_at D) (hC : GlobalTheory.TwSys.Cheb) (hZ : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) :
    JumpDictCrys_at D := by
  obtain ⟨hc, ht⟩ := hG2 (weightTie_of_weightParam D hW) hT
  have hd : ∀ i r, GoodR D.nd i r → ∀ w hw, GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.DeRhamAt (D := D) i w hw r := by
    intro i r hr w hw
    by_cases hl : ∃ k, D.nd.l i = D.host.g k
    · exact (ht i hl r hr w hw).1
    · exact (hc i (not_exists.1 hl) r hr w hw).2
  refine ⟨⟨fun i x r hr w hw => ?_, ⟨true, fun _ _ => shift D, fun i x r hr w hw τ ρ b hτ => ?_,
    blockWith D hG hC (blockCharParam_of_charTie D hT)⟩, summand_of_complement D hZ⟩,
    fun i hl x r hr w hw => ?_⟩
  · obtain ⟨r', h', rfl⟩ := exists_family D (hR i) hr
    exact (hd i r' h' w hw).1 x
  · obtain ⟨r', h', rfl⟩ := exists_family D (hR i) hr
    obtain ⟨h1, h2⟩ := hd i r' h' w hw
    have key : GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding.HasJumps i w hw (r' x) τ ((PP D i ρ).map fun p =>
        sgnOf true b * p + (shift D (embOver D ρ b) : ℚ)) := by
      rw [shift_embOver]
      cases b
      · have h := (((h2 τ).2 ρ).1 hτ).1 x
        rw [fullPar_eq'] at h
        convert h using 1
        refine Multiset.map_congr rfl fun p _ => ?_
        simp only [sgnOf]
        norm_num
        ring
      · have h := (((h2 τ).2 ρ).2 hτ).1 x
        rw [fullPar_eq'] at h
        convert h using 1
        refine Multiset.map_congr rfl fun p _ => ?_
        simp only [sgnOf]
        norm_num
        ring
    exact jumpsAre_of_mult D i w hw _ hr.1 (h1 x) τ _ key.1 key.2
  · obtain ⟨r', h', rfl⟩ := exists_family D (hR i) hr
    exact (hc i hl r' h' w hw).1 x

end GlobalTheory.JumpDictionaryFoundation

end
