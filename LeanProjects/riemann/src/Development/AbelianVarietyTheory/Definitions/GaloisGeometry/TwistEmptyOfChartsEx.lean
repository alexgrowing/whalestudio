import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistedLevelExtension
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

noncomputable section

namespace GlobalTheory.TwU.WildChar

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker _root_.Formalism.UG _root_.Formalism.L2.Forms
open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

theorem exists_char {G : Type} [CommGroup G] (H : Subgroup G) (g : G) (hg : g ∉ H) :
    ∃ η : G →* ℂˣ, (∀ h ∈ H, η h = 1) ∧ η g ≠ 1 := by
  have h0 : (Additive.ofMul (QuotientGroup.mk g : G ⧸ H)) ≠ 0 := fun h => hg ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero h0
  let j : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      rintro x ⟨n, rfl⟩
      exact ⟨n, by simp⟩)
  have hj : ∀ t, j t = 0 → t = 0 := by
    intro t ht
    induction t using QuotientAddGroup.induction_on with
    | H q =>
      obtain ⟨n, hn⟩ := (QuotientAddGroup.eq_zero_iff (((q : ℚ) : ℝ))).1 ht
      refine (QuotientAddGroup.eq_zero_iff _).2 ⟨n, ?_⟩
      simp only [zsmul_eq_mul, mul_one] at hn ⊢
      exact_mod_cast hn
  let φ : Additive (G ⧸ H) →+ AddCircle (1 : ℝ) := j.comp (c : Additive (G ⧸ H) →+ AddCircle (1 : ℚ))
  let ψ : G →* Circle :=
    { toFun := fun x => AddCircle.toCircle (φ (Additive.ofMul (QuotientGroup.mk x : G ⧸ H)))
      map_one' := by simp
      map_mul' := fun x y => by rw [QuotientGroup.mk_mul, ofMul_mul, map_add, AddCircle.toCircle_add] }
  refine ⟨Circle.toUnits.comp ψ, fun h hh => ?_, fun h => hc (hj _ ?_)⟩
  · have : (QuotientGroup.mk h : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff _).2 hh
    have h2 : ψ h = 1 := by
      show AddCircle.toCircle (φ (Additive.ofMul (QuotientGroup.mk h : G ⧸ H))) = 1
      rw [this]; simp
    simp [h2]
  · have h1 : ψ g = 1 := by
      apply Circle.ext
      simpa using congrArg Units.val h
    have h2 : AddCircle.toCircle (φ (Additive.ofMul (QuotientGroup.mk g : G ⧸ H))) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h1
    exact AddCircle.injective_toCircle one_ne_zero h2

theorem exists_irr (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (M N : ℕ) (hM : M ≠ 0) (hN : 0 < N) :
    ∃ a : P.adicCompletion E, Valued.v (a - 1) ≤ Valued.v (M : P.adicCompletion E) ∧ Valued.v a = 1 ∧
      ∀ e : E, a ^ N ≠ algebraMap E _ e := by
  letI : NontriviallyNormedField (P.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hc : (⋃ e : E, {a : P.adicCompletion E | a ^ N = algebraMap E _ e}).Countable := by
    refine Set.countable_iUnion fun e => Set.Finite.countable ?_
    classical
    refine (Polynomial.nthRoots N (algebraMap E (P.adicCompletion E) e)).toFinset.finite_toSet.subset fun a ha => ?_
    simpa [Polynomial.mem_nthRoots hN] using ha
  have hd := Set.Countable.dense_compl (P.adicCompletion E) hc
  have hM0 : Valued.v (M : P.adicCompletion E) ≠ 0 := by
    rw [Valuation.ne_zero_iff, ← map_natCast (algebraMap E (P.adicCompletion E))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hM)
  have hM1 : Valued.v (M : P.adicCompletion E) ≤ 1 := by
    rw [← map_natCast (algebraMap E (P.adicCompletion E)), valued_algebraMap, ← map_natCast (algebraMap (𝓞 E) E)]
    exact P.valuation_le_one _
  have hn : {a : P.adicCompletion E | Valued.v (a - 1) < Valued.v (M : P.adicCompletion E)} ∈ nhds (1 : P.adicCompletion E) := by
    have hb : {a : P.adicCompletion E | ‖a - 1‖ < ‖(M : P.adicCompletion E)‖} ∈ nhds (1 : P.adicCompletion E) := by
      refine IsOpen.mem_nhds (isOpen_lt (by fun_prop) continuous_const) ?_
      simp only [Set.mem_setOf_eq, sub_self, norm_zero, norm_pos_iff]
      exact (Valuation.ne_zero_iff _).1 hM0
    refine Filter.mem_of_superset hb fun a ha => ?_
    exact Valued.toNormedField.norm_lt_iff.1 ha
  obtain ⟨a, ha, ha'⟩ := hd.inter_nhds_nonempty hn
  refine ⟨a, le_of_lt ha', ?_, fun e he => ha (Set.mem_iUnion.2 ⟨e, he⟩)⟩
  have := Valuation.map_one_add_of_lt Valued.v (lt_of_lt_of_le ha' hM1)
  simpa using this

section Idele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)

theorem exists_wild (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P ≠ P)
    (hu : ∀ w : HeightOneSpectrum (𝓞 E), conjPrime₂ w = P → w.under (𝓞 F) = P.under (𝓞 F)) (N : ℕ) (hN : 0 < N) (M : ℕ) (hM : M ≠ 0) :
    ∃ (s : (AfE F E)ˣ) (η : (P.adicCompletion E)ˣ →* ℂˣ), sigR hc.sig _ (s : AfE F E) * s = 1 ∧
      (∀ v, v ≠ P.under (𝓞 F) → prV (E := E) v (s : AfE F E) = 1) ∧ (∃ r ∈ RInt F E, (s : AfE F E) - 1 = M * r) ∧
      (∀ y : (P.adicCompletion E)ˣ, (∃ e : E, (y : P.adicCompletion E) = algebraMap E _ e) → η y = 1) ∧
      η (Units.map (adAt F P).toMonoidHom (s ^ N)) ≠ 1 := by
  classical
  obtain ⟨a, h1, h2, h3⟩ := exists_irr E P M N hM hN
  have ha0 : a ≠ 0 := fun h => by simp [h] at h2
  set au := Units.mk0 a ha0
  set b : (AfE F E)ˣ := finAf F E (Neutral.B1.localIdele E P au) with hb
  have bP : adAt F P (b : AfE F E) = a := by rw [hb, adAt_finAf, compAt_localIdele_self]; rfl
  have bw : ∀ w, w ≠ P → adAt F w (b : AfE F E) = 1 := fun w hw => by rw [hb, adAt_finAf, compAt_localIdele_ne hw]
  have sbw : ∀ w, conjPrime₂ w ≠ P → adAt F w (sigR hc.sig _ (b : AfE F E)) = 1 := fun w hw => by
    have e := valued_sigR hc w ((b : AfE F E) - 1)
    rw [map_sub (adAt F (conjPrime₂ w)), bw _ hw, map_one, sub_self, map_zero, Valuation.zero_iff, map_sub, map_sub, map_one, map_one,
      sub_eq_zero] at e
    exact e
  set sb : (AfE F E)ˣ := Units.map (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)).toMonoidHom b with hsb
  have hsbv : (sb : AfE F E) = sigR hc.sig _ (b : AfE F E) := rfl
  have hsbi : ((sb⁻¹ : (AfE F E)ˣ) : AfE F E) = sigR hc.sig _ ((b⁻¹ : (AfE F E)ˣ) : AfE F E) := rfl
  have inv1 : ∀ (w : HeightOneSpectrum (𝓞 E)) (x : (AfE F E)ˣ), adAt F w ((x⁻¹ : (AfE F E)ˣ) : AfE F E) = (adAt F w (x : AfE F E))⁻¹ := fun w x => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  have sP : adAt F P ((b * sb⁻¹ : (AfE F E)ˣ) : AfE F E) = a := by
    rw [Units.val_mul, map_mul, inv1, hsbv, sbw P hP, bP, inv_one, mul_one]
  obtain ⟨η, hη, hη'⟩ := exists_char (Units.map (algebraMap E (P.adicCompletion E)).toMonoidHom).range (au ^ N) (by
    rintro ⟨e, he⟩
    exact h3 e (by simpa [au] using (congrArg Units.val he).symm))
  refine ⟨b * sb⁻¹, η, ?_, fun v hv => ?_, ?_, fun y ⟨e, he⟩ => hη y ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hsbi, PtExist.sig_sig, ← hsbi, ← hsbv]
    calc (sb : AfE F E) * ((b⁻¹ : (AfE F E)ˣ) : AfE F E) * ((b : AfE F E) * ((sb⁻¹ : (AfE F E)ˣ) : AfE F E))
        = ((sb * b⁻¹ * (b * sb⁻¹) : (AfE F E)ˣ) : AfE F E) := by simp only [Units.val_mul]
      _ = 1 := by rw [show sb * b⁻¹ * (b * sb⁻¹) = 1 by group, Units.val_one]
  · rw [← sub_eq_zero, ← map_one (prV (E := E) v), ← map_sub]
    refine ((AdComp.prV_zero_int_iff F E v _).1).2 fun w hw => ?_
    have w1 : w ≠ P := fun e => hv (by rw [← hw, e])
    have w2 : conjPrime₂ w ≠ P := fun e => hv (by rw [← hw, hu w e])
    rw [map_sub, Units.val_mul, map_mul, inv1, hsbv, sbw w w2, bw w w1]
    simp
  · have hM' : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
    set r0 : AfE F E := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (M : E)⁻¹ * ((b : AfE F E) - 1) with hr0
    have e0 : (b : AfE F E) - 1 = M * r0 := by
      rw [hr0, ← mul_assoc, ← map_natCast (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)), ← map_mul, mul_inv_cancel₀ hM', map_one, one_mul]
    have hr : r0 ∈ RInt F E := by
      refine (mem_rInt_iff F E _).2 fun w => ?_
      rw [← adAt_apply, hr0, map_mul, adAt_inclE, map_sub, map_one]
      by_cases hw : w = P
      · subst hw
        rw [bP, map_inv₀, map_natCast, map_mul, map_inv₀]
        have hM0 : Valued.v (M : w.adicCompletion E) ≠ 0 := by
          rw [Valuation.ne_zero_iff, ← map_natCast (algebraMap E (w.adicCompletion E))]
          exact (map_ne_zero _).2 hM'
        rw [inv_mul_le_iff₀ (zero_lt_iff.2 hM0), mul_one]
        exact h1
      · rw [bw w hw]; simp
    have hbi : ((b⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := by
      refine (mem_rInt_iff F E _).2 fun w => ?_
      rw [← adAt_apply, inv1]
      by_cases hw : w = P
      · subst hw
        rw [bP, map_inv₀, h2, inv_one]
      · rw [bw w hw]; simp
    refine ⟨(r0 - sigR hc.sig _ r0) * ((sb⁻¹ : (AfE F E)ˣ) : AfE F E),
      mul_mem (sub_mem hr (sigR_mem_rInt hc hr)) (hsbi ▸ sigR_mem_rInt hc hbi), ?_⟩
    have e1 : (sb : AfE F E) - 1 = M * sigR hc.sig _ r0 := by
      have := congrArg (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) e0
      rwa [map_sub, map_one, map_mul, map_natCast] at this
    have e2 : (sb : AfE F E) * ((sb⁻¹ : (AfE F E)ˣ) : AfE F E) = 1 := Units.mul_inv sb
    rw [Units.val_mul]
    linear_combination ((sb⁻¹ : (AfE F E)ˣ) : AfE F E) * e0 - ((sb⁻¹ : (AfE F E)ˣ) : AfE F E) * e1 + e2
  · have e0 : e ≠ 0 := fun h => y.ne_zero (by rw [he, h, map_zero])
    exact ⟨Units.mk0 e e0, Units.ext he.symm⟩
  · have : Units.map (adAt F P).toMonoidHom ((b * sb⁻¹) ^ N) = au ^ N := by
      rw [map_pow]
      congr 1
      exact Units.ext sP
    rwa [this]

end Idele

section Central

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) {u : D.what₂.Word} (μ : D.what₂.Tup)

def modulus : ℕ := ∏ P : SB t μ, qOf (seamP t.seam P.1) ^ (t.cst μ).D P

theorem modulus_ne : modulus t μ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun P _ => pow_ne_zero _ (by
    unfold qOf
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact (seamP t.seam P.1).ne_bot)

variable {t μ} {St : ChainCharts D u μ} {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

set_option maxHeartbeats 1000000 in

theorem chi_central (H : AdTie A dtU a) (h0 : 0 < D.R.m) (β : (St 0 h0.le).Ch) (v₀ : HeightOneSpectrum (𝓞 D.host.F)) (hv : v₀ ∈ (St 0 h0.le).bad)
    (s : (AfE D.host.F D.host.E)ˣ) (hs : sigR (sigD D) _ (s : AfE D.host.F D.host.E) * s = 1)
    (hoff : ∀ v, v ≠ v₀ → prV (E := D.host.E) v (s : AfE D.host.F D.host.E) = 1)
    (hM : ∃ r ∈ RInt D.host.F D.host.E, (s : AfE D.host.F D.host.E) - 1 = (modulus t μ : ℕ) * r) :
    ∃ h : Matrix.GeneralLinearGroup.scalar (Fin (D.R.N 0)) s ∈ ((St 0 h0.le).K β).lev.U, ((St 0 h0.le).K β).lev.chi ⟨_, h⟩ = 1 := by
  classical
  obtain ⟨-, hge, hchi⟩ := H.levMid 0 h0 (Nat.zero_le _) β
  set κ := Matrix.GeneralLinearGroup.scalar (Fin (D.R.N 0)) s with hκ
  have hκv : (κ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (AfE D.host.F D.host.E)) = (s : AfE D.host.F D.host.E) • 1 := by
    rw [hκ]; ext i j; simp [Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, Matrix.diagonal_apply]
  have hcomm : ∀ g : GL (Fin (D.R.N 0)) (AfE D.host.F D.host.E), g⁻¹ * κ * g = κ := fun g => by
    have : κ * g = g * κ := Units.ext (by rw [Units.val_mul, Units.val_mul, hκv]; simp)
    rw [mul_assoc, this, inv_mul_cancel_left]
  have hU : κ ∈ UPts (sigD D) (gramN D 0 h0.le) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    show cT _ _ * _ * _ = _
    have : cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((s : AfE D.host.F D.host.E) • (1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _)) =
        sigR (sigD D) _ (s : AfE D.host.F D.host.E) • 1 := by
      ext i j
      by_cases e : i = j
      · subst e; simp [cT]
      · simp [cT, Matrix.one_apply, e, Ne.symm e]
    rw [hκv, this]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
    rw [mul_comm, hs, one_smul]
  have hinv : ∀ P : SB t μ, CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) κ := fun P i j => by
    obtain ⟨r, hr, e⟩ := hM
    obtain ⟨c, hc⟩ : qOf (seamP t.seam P.1) ^ (t.cst μ).D P ∣ modulus t μ := Finset.dvd_prod_of_mem _ (Finset.mem_univ P)
    have hq : ((qOf (seamP t.seam P.1) : ℕ) : D.host.E) ^ (t.cst μ).D P ≠ 0 := by
      have := modulus_ne t μ
      rw [hc] at this
      exact_mod_cast left_ne_zero_of_mul this
    refine ⟨1, fun h => (seamP t.seam P.1).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [map_one, map_one, one_mul, hκv]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [e, hc, Nat.cast_mul, Nat.cast_pow, ← map_natCast (iA D.host.F D.host.E) (qOf _), ← map_pow, mul_assoc, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hq, map_one, one_mul]
      exact mul_mem (natCast_mem _ c) hr
    · simp [Matrix.one_apply, hij]
  have hfr : ∀ P : SB t μ, InFrame t.seam (A.fb 0 h0.le β) (t.cst μ).D P κ⁻¹ 1 := fun P => by
    unfold InFrame NearAt
    have e : ((ratA D.host.F (A.fb 0 h0.le β P))⁻¹ * κ⁻¹ * ratA D.host.F (A.fb 0 h0.le β P))⁻¹ =
        (ratA D.host.F (A.fb 0 h0.le β P))⁻¹ * κ * ratA D.host.F (A.fb 0 h0.le β P) := by group
    rw [e, hcomm, map_one, map_one, mul_one]
    exact hinv P
  have hfr1 : ∀ P : SB t μ, InFrame t.seam (A.fb 0 h0.le β) (t.cst μ).D P 1 1 := fun P => by
    unfold InFrame NearAt
    simpa using congAt_one (F := D.host.F) (N := D.R.N 0) (seamP t.seam P.1) ((t.cst μ).D P)
  have hrel : ∀ P : SB t μ, ∃ z, A.midRel 0 h0 β P 1 z := fun P =>
    (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) 0 P _ 1).2 (Subgroup.one_mem _)
  choose z hz using hrel
  have hm : κ⁻¹ ∈ ((St 0 h0.le).K β).lev.U := by
    refine (((St 0 h0.le).K β).lev.U_eq κ⁻¹).2 ⟨inv_mem hU, fun v => ?_⟩
    by_cases e : v = v₀
    · subst e
      obtain ⟨P, hP, ho⟩ := H.bad 0 h0.le v hv
      exact hge ⟨P, hP⟩ v ho κ⁻¹ (inv_mem hU) ⟨1, z _, hz _, hfr _⟩
    · have : bc (prV (E := D.host.E) v) κ = 1 := by
        apply Units.ext
        show (κ.1).map _ = 1
        rw [hκv]
        ext i j
        by_cases hij : i = j
        · subst hij; simp [hoff v e]
        · simp [Matrix.one_apply, hij]
      rw [map_inv, this, inv_one]
      exact one_mem _
  refine ⟨(inv_mem_iff).1 hm, ?_⟩
  have e1 := hchi ⟨κ⁻¹, hm⟩ (fun _ => 1) z fun P => ⟨hz P, hfr P⟩
  have e2 := hchi 1 (fun _ => 1) z fun P => ⟨hz P, hfr1 P⟩
  rw [map_one, Units.val_one, one_mul] at e2
  rw [e2, mul_one] at e1
  have e3 : ((St 0 h0.le).K β).lev.chi ⟨κ⁻¹, hm⟩ = 1 := Units.ext e1
  rw [← inv_eq_one, ← map_inv]
  exact e3

end Central

section Twist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

def detAt (F : Type) [Field F] [NumberField F] [Algebra F E] (n : ℕ) (P : HeightOneSpectrum (𝓞 E)) (η : (P.adicCompletion E)ˣ →* ℂˣ) :
    GL (Fin n) (AfE F E) →* ℂˣ :=
  η.comp ((Units.map (adAt F P).toMonoidHom).comp Matrix.GeneralLinearGroup.det)

theorem detAt_eq_one (P : HeightOneSpectrum (𝓞 E)) (η : (P.adicCompletion E)ˣ →* ℂˣ) (x : GL (Fin n) (AfE F E))
    (h : bc (prV (E := E) (P.under (𝓞 F))) x = 1) : detAt F n P η x = 1 := by
  have h1 : prV (E := E) (P.under (𝓞 F)) (x.1.det - 1) = 0 := by
    have h2 := congrArg (fun g => Matrix.det (Units.val g)) h
    simp only [Formalism.UG.bc, Units.coe_map, Units.val_one, Matrix.det_one] at h2
    rw [map_sub, map_one, RingHom.map_det, sub_eq_zero]
    exact h2
  have h3 := ((AdComp.prV_zero_int_iff F E _ _).1).1 h1 P rfl
  rw [map_sub, map_one, sub_eq_zero] at h3
  have h4 : Units.map (adAt F P).toMonoidHom (Matrix.GeneralLinearGroup.det x) = 1 := Units.ext h3
  show η (Units.map (adAt F P).toMonoidHom (Matrix.GeneralLinearGroup.det x)) = 1
  rw [h4, map_one]

def twistLev (S : StepLevel F E σ J T f bad) (P : HeightOneSpectrum (𝓞 E)) (η : (P.adicCompletion E)ˣ →* ℂˣ) :
    StepLevel F E σ J T f (insert (P.under (𝓞 F)) bad) :=
  { S with
    Uloc_hyp := fun v hv hT => S.Uloc_hyp v (fun h => hv (Set.mem_insert_of_mem _ h)) hT
    chi := S.chi * (detAt F n P η).comp S.U.subtype
    chi_triv := fun x hx => by
      show S.chi x * detAt F n P η x.1 = 1
      rw [S.chi_triv x fun v hv => hx v (Set.mem_insert_of_mem _ hv), detAt_eq_one P η _ (hx _ (Set.mem_insert _ _)), mul_one] }

theorem detAt_pt [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ Q)
    {η : (P.adicCompletion E)ˣ →* ℂˣ} (hη : ∀ y : (P.adicCompletion E)ˣ, (∃ e : E, (y : P.adicCompletion E) = algebraMap E _ e) → η y = 1)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) : detAt F n P η g = 1 := by
  refine hη _ ⟨(Matrix.of fun i j => p.fr ⟨P, hP⟩ (Pi.single j 1) i).det, ?_⟩
  show adAt F P g.1.det = _
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  exact Matrix.ext fun i j => h.fr ⟨P, hP⟩ i j

theorem detAt_mid [StarRing E] {hc : CMData F E} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ Q) (hP' : P ∈ Q')
    {η : (P.adicCompletion E)ˣ →* ℂˣ} (hη : ∀ y : (P.adicCompletion E)ˣ, (∃ e : E, (y : P.adicCompletion E) = algebraMap E _ e) → η y = 1)
    {y x k : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (h : IsPtOf hc (y * x * k) p) (h' : IsPtOf hc (y * k) p') :
    detAt F n P η x = 1 := by
  have e1 := detAt_pt hP hη h
  have e2 := detAt_pt hP' hη h'
  rw [map_mul, map_mul, mul_right_comm, ← map_mul, e2, one_mul] at e1
  exact e1

theorem move_twist_central (S : StepLevel F E σ J T f bad) (P : HeightOneSpectrum (𝓞 E)) (η : (P.adicCompletion E)ˣ →* ℂˣ)
    (k : basePts (twistLev S P η)) (s : (AfE F E)ˣ) (hm : Matrix.GeneralLinearGroup.scalar (Fin n) s ∈ (moveLev k).U) (e : (moveLev k).chi ⟨_, hm⟩ = 1) :
    ∃ hm' : Matrix.GeneralLinearGroup.scalar (Fin n) s ∈ S.U,
      S.chi ⟨_, hm'⟩ * η (Units.map (adAt F P).toMonoidHom (s ^ n)) = 1 := by
  have hc : k.1 * Matrix.GeneralLinearGroup.scalar (Fin n) s * k.1⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) s := by
    rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    exact ((Matrix.scalar_commute (s : AfE F E) (fun _ => Commute.all _ _) _).eq).symm
  have hm' : k.1 * Matrix.GeneralLinearGroup.scalar (Fin n) s * k.1⁻¹ ∈ S.U := hm
  have e' : S.chi ⟨_, hm'⟩ * detAt F n P η (k.1 * Matrix.GeneralLinearGroup.scalar (Fin n) s * k.1⁻¹) = 1 := e
  have e2 : detAt F n P η (Matrix.GeneralLinearGroup.scalar (Fin n) s) = η (Units.map (adAt F P).toMonoidHom (s ^ n)) := by
    show η (Units.map _ (Matrix.GeneralLinearGroup.det _)) = _
    congr 2
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.scalar]
  refine ⟨hc ▸ hm', ?_⟩
  rw [← e2]
  simpa only [hc] using e'

end Twist

section Charts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
  {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}

set_option maxHeartbeats 1000000 in

def twistChart (K : LevelChart D T bad i hi stab lat) (P : HeightOneSpectrum (𝓞 D.host.E)) (η : (P.adicCompletion D.host.E)ˣ →* ℂˣ) :
    LevelChart D T (insert (P.under (𝓞 D.host.F)) bad) i hi stab lat where
  lev := twistLev K.lev P η
  y := K.y
  y_bij := K.y_bij
  y_lat := K.y_lat
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

end Charts

section True

open GlobalTheory.TwU.AtTrue

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

def SideNoChar {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi)
    (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (K : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi)) : Prop :=
  (∀ v ∈ bad, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v) ∧ ∀ i hi, I.IdY l Z u a i hi (eY i hi) ∧ ∀ β, FunKilled (K i hi β).lev (X.piT u)

def TieOnAllReadings : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z))
    (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (Kc : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC)
    (ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX) (t : KerEntTied ex) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt),
    StdData I l Z t dt → ∀ (u : B.Word) (a : I.ι) bad Ch chOf eY K, SideNoChar I l Z u a bad Ch chOf eY K →
    (∀ i hi, I.ReadsK l Z u a i hi (chOf i hi) (K i hi)) →
    ∃ (k : ChainBase (charts I l Z u a bad Ch chOf eY K)) (A : AdData t u a (moveCharts (charts I l Z u a bad Ch chOf eY K) k)),
      AdPins A dt ∧ AdTie A dt (B.fields.conjO (X.piT u))

def ReadingsEx : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι),
    ∃ bad Ch chOf eY K, SideNoChar I l Z u a bad Ch chOf eY K ∧ ∀ i hi, I.ReadsK l Z u a i hi (chOf i hi) (K i hi)

set_option maxHeartbeats 2000000 in

theorem readsK_twist {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m)
    {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (K : Fam I l Z u a i hi bad chOf)
    {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ I.Q a) {η : (P.adicCompletion B.host.E)ˣ →* ℂˣ}
    (hη : ∀ y : (P.adicCompletion B.host.E)ˣ, (∃ e : B.host.E, (y : P.adicCompletion B.host.E) = algebraMap B.host.E _ e) → η y = 1)
    (h : I.ReadsK l Z u a i hi chOf K) : I.ReadsK l Z u a i hi chOf fun β => twistChart (D := I.rec7 l Z) (K β) P η := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, { hk with chr := fun c x κ h1 h2 => ?_ }⟩
  have e3 : detAt B.host.F (B.R.N i) P η x.1 = 1 := detAt_mid hP (I.Q_subset_SQ a hP) hη h2 (hk.pt c)
  refine Eq.trans ?_ (hk.chr c x κ h1 h2)
  show (((K (chOf c)).lev.chi x * detAt B.host.F (B.R.N i) P η x.1 : ℂˣ) : ℂ) = _
  rw [e3, mul_one]
  rfl

set_option maxHeartbeats 4000000 in

theorem twist_empty_of_tieMoved (h : TieOnAllReadings) {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (Kc : G.Consts) (Y : DivX (I.rec7 l Z))
    (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX) (t : KerEntTied ex) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt)
    (hS : StdData I l Z t dt) (u : B.Word) (a : I.ι) (bad Ch chOf eY K) (hs : SideNoChar I l Z u a bad Ch chOf eY K)
    (hK : ∀ i hi, I.ReadsK l Z u a i hi (chOf i hi) (K i hi)) : I.Q a = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun P hPQ => ?_
  have h0 : 0 < B.R.m := by have := B.R.two_le_m; omega
  have hN : 0 < B.R.N 0 := by have := B.R.m_add_three_le_k; unfold Ranks.N; omega
  have hsp : conjPrime₂ P ≠ P := fun e => by
    have hm : P ∈ uSG (B.primes X).vGs I.SQ := Finset.mem_union_right _ (I.Q_subset_SQ a hPQ)
    exact (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1.split P hm (by rw [e]; exact hm)
  have hu : ∀ w : HeightOneSpectrum (𝓞 B.host.E), conjPrime₂ w = P → w.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := fun w e =>
    ((under_eq_iff B.host w P).2 (Or.inr e.symm)).symm
  obtain ⟨s, η, s1, s2, s3, hη, hne⟩ := exists_wild (F := B.host.F) (E := B.host.E) B.sp.cm P hsp hu (B.R.N 0) hN (modulus t a) (modulus_ne t a)
  obtain ⟨β⟩ : Nonempty (Ch 0 h0.le) := by
    haveI : NeZero (B.R.N 0) := ⟨hN.ne'⟩
    refine ⟨chOf 0 h0.le ((I.stp u a 0).cl (l.idx0 a).some ⟨(DecoF.base _ _ _ _ _, ∅), ?_⟩)⟩
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by have := B.R.two_le_m; omega)]
    rfl
  have key : ∀ η' : (P.adicCompletion B.host.E)ˣ →* ℂˣ,
      (∀ y : (P.adicCompletion B.host.E)ˣ, (∃ e : B.host.E, (y : P.adicCompletion B.host.E) = algebraMap B.host.E _ e) → η' y = 1) →
      ∃ hm : Matrix.GeneralLinearGroup.scalar (Fin (B.R.N 0)) s ∈ (K 0 h0.le β).lev.U,
        (K 0 h0.le β).lev.chi ⟨_, hm⟩ * η' (Units.map (adAt B.host.F P).toMonoidHom (s ^ B.R.N 0)) = 1 := fun η' hη' => by
    obtain ⟨k, A, -, H⟩ := h I hI hP l Z L hT Gi Gl Kc Y cX ex t dt hS u a (insert (P.under (𝓞 B.host.F)) bad) Ch chOf eY
      (fun i hi β => twistChart (D := I.rec7 l Z) (K i hi β) P η')
      ⟨fun v hv => hv.elim (fun e => Or.inr ⟨P, hPQ, e.symm⟩) (hs.1 v), fun i hi => ⟨(hs.2 i hi).1, (hs.2 i hi).2⟩⟩
      (fun i hi => readsK_twist I l Z u a i hi (chOf i hi) (K i hi) hPQ hη' (hK i hi))
    obtain ⟨hm, e⟩ := chi_central H h0 β (P.under (𝓞 B.host.F)) (Set.mem_insert _ _) s s1 s2 s3
    exact move_twist_central (K 0 h0.le β).lev P η' (k 0 h0.le β) s hm e
  obtain ⟨m1, e1⟩ := key 1 fun _ _ => rfl
  obtain ⟨m2, e2⟩ := key η hη
  rw [MonoidHom.one_apply, mul_one] at e1
  exact hne (by rwa [e1, one_mul] at e2)

theorem twist_empty_of_chartsEx (h : TieOnAllReadings) (h0 : ReadingsEx) {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (Kc : G.Consts)
    (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX) (t : KerEntTied ex)
    (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) (hS : StdData I l Z t dt) (u : B.Word) (a : I.ι) : I.Q a = ∅ := by
  obtain ⟨bad, Ch, chOf, eY, K, hs, hK⟩ := h0 I hI hP l Z u a
  exact twist_empty_of_tieMoved h I hI hP l Z L hT Gi Gl Kc Y cX ex t dt hS u a bad Ch chOf eY K hs hK

theorem not_stdData_of_tieMoved (h : TieOnAllReadings) (h0 : ReadingsEx) {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (Kc : G.Consts)
    (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX) (t : KerEntTied ex)
    (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) : ¬ StdData I l Z t dt := fun hS =>
  (GlobalTheory.Mem.Col2.TC.TwModel.Q_star_nonempty hI).ne_empty (twist_empty_of_chartsEx h h0 I hI hP l Z L hT Gi Gl Kc Y cX ex t dt hS B.u₀ I.muStar)

end True

end GlobalTheory.TwU.WildChar

end

noncomputable section

namespace GlobalTheory.TwU.Rigid

open _root_.Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.MainNotions.G.KAat _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV
open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

theorem exists_pt_one {x : (AfE D.host.F D.host.E)ˣ} (hx : x ∈ U1 (sigD D)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x := by
  have h1 : x * conjId (sigD D) x = 1 := hx
  have h2 : (x : AfE D.host.F D.host.E) * Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x : AfE D.host.F D.host.E) = 1 := by
    have := congrArg (fun z : (AfE D.host.F D.host.E)ˣ => (z : AfE D.host.F D.host.E)) h1
    simpa [conjId] using this
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 1) x, ?_⟩, ?_⟩
  · show Formalism.UG.cT _ _ * _ * _ = _
    ext i j
    fin_cases i; fin_cases j
    simp [Formalism.UG.cT, Matrix.mul_apply]
    rw [mul_comm]
    exact h2
  · apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]

theorem exists_decomp (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ (c : (D.chTw u μ).cls i) (_ : (St i hi).chOf c = β) (γ : GL (Fin (D.R.N i)) D.host.E)
      (_ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ : ((St i hi).K β).lev.U),
      x.1 = ratA D.host.F γ * (((St i hi).y c).1 * κ.1) := by
  obtain ⟨c, hc⟩ := ((St i hi).K β).y_bij.2 (Quotient.mk'' x)
  obtain ⟨g, ⟨γ, hγ, hg⟩, κ, hκ, e⟩ := (DoubleCoset.eq _ _ _ _).1 hc
  refine ⟨c.1, c.2, γ, hγ, ⟨κ.1, hκ⟩, ?_⟩
  rw [← (St i hi).y_eq c, e]
  show g.1 * _ * κ.1 = _
  rw [mul_assoc]
  exact congrArg (· * _) hg.symm

theorem muT_unique {Xi Xi' : AdDatum St} {m m' : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ} (H : AdLawAt A dtU a Xi m) (H' : AdLawAt A dtU a Xi' m')
    {i : ℕ} (hi : i < D.R.m) {x : (AfE D.host.F D.host.E)ˣ} (hx : x ∈ U1 (sigD D)) : m (i + 1) x = m' (i + 1) x := by
  obtain ⟨y, rfl⟩ := exists_pt_one hx
  rw [H.mu_read i hi, H'.mu_read i hi]

set_option maxHeartbeats 1000000 in

theorem xiAd_unique {Xi Xi' : AdDatum St} {m m' : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ} (H : AdLawAt A dtU a Xi m) (H' : AdLawAt A dtU a Xi' m') :
    Xi = Xi' := by
  funext i hi β β' x x' z
  obtain ⟨c, rfl, γ, hγ, κ, e⟩ := exists_decomp i _ β x
  obtain ⟨c', rfl, γ', hγ', κ', e'⟩ := exists_decomp (i + 1) hi β' x'
  have hκ := (((St i _).K _).lev.U_eq κ.1).1 κ.2
  have hκ' := (((St (i + 1) hi).K _).lev.U_eq κ'.1).1 κ'.2
  let x₁ := (St i (Nat.le_of_succ_le hi)).y c * ⟨κ.1, hκ.1⟩
  let x₁' := (St (i + 1) hi).y c' * ⟨κ'.1, hκ'.1⟩
  rw [H.rat i hi _ _ x₁ x₁' x x' γ hγ γ' hγ' e e', H'.rat i hi _ _ x₁ x₁' x x' γ hγ γ' hγ' e e']
  generalize inFr _ _ z = w
  have d := Formalism.L2.DIV.det_in_unitary_one D.host.F D.host.E (sigD D) _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i (Nat.le_of_succ_le hi)) κ.1 hκ.1
  have d' := Formalism.L2.DIV.det_in_unitary_one D.host.F D.host.E (sigD D) _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D (i + 1) hi) κ'.1 hκ'.1
  have l := H.lev i hi _ _ _ _ x₁ x₁' κ κ' rfl rfl w
  have l' := H'.lev i hi _ _ _ _ x₁ x₁' κ κ' rfl rfl w
  rw [H.read] at l
  rw [H'.read, ← muT_unique H H' hi d, ← muT_unique H H' hi d', ← l] at l'
  exact (mul_left_cancel₀ (mul_ne_zero (H.mu_ne hi d') (Units.ne_zero _)) l').symm

theorem chart_nonempty (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) : ∃ c, (St i hi).chOf c = β :=
  let ⟨c, hc, _⟩ := exists_decomp i hi β 1
  ⟨c, hc⟩

theorem not_topLev_neg {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (j : ℕ) (P : rowSG Pr sel mu) (z : X.K) : ¬ TopLev (R := R) Ch sel mu cst j P (LinearEquiv.neg X.E) z := by
  rintro ⟨g', -, -, h, -⟩
  have hN := R.N_pos j
  have hl : R.N j - 1 < R.N j := by omega
  have h1 := LinearMap.congr_fun h (Pi.single ⟨R.N j - 1, hl⟩ 1)
  simp only [atNL, dif_pos hl, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.neg_apply, LinearMap.proj_apply, Pi.neg_apply, Pi.single_eq_same] at h1
  norm_num at h1

end GlobalTheory.TwU.Rigid

end

noncomputable section

namespace GlobalTheory.TwU.Model

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.UG
open scoped TensorProduct

section CongBasic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

theorem intAtA_sum {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) :
    IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congAt_mul (n : ℕ) {k k' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P n k) (h' : CongAt P n k') :
    CongAt P n (k * k') := by
  intro a b
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set c := iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ with hc
  set d := iA F E (algebraMap (𝓞 E) E (((qOf P : ℕ) : 𝓞 E) ^ n)) with hd
  have hcd : d * c = 1 := by
    rw [hc, hd, ← map_mul, map_pow, map_natCast, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have e : ((k * k' : GL (Fin N) _) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      ((k : Matrix (Fin N) (Fin N) _) - 1) * ((k' : Matrix (Fin N) (Fin N) _) - 1) + (((k : Matrix (Fin N) (Fin N) _) - 1) + ((k' : Matrix (Fin N) (Fin N) _) - 1)) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add, Matrix.mul_apply, Finset.mul_sum]
  refine intAtA_add (intAtA_sum _ _ fun l _ => ?_) (intAtA_add (h a b) (h' a b))
  have e2 : ∀ x y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, c * (x * y) = d * ((c * x) * (c * y)) := by
    intro x y
    linear_combination (-(c * (x * y))) * hcd
  rw [e2]
  exact intAtA_mul (intAtA_int _) (intAtA_mul (h a l) (h' l b))

end CongBasic

theorem sameCoset_equiv {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (P : rowSG Pr sel mu) :
    Equivalence (fun y y' : Sp X.E n => SameCoset sel mu cst P y y') where
  refl := fun y l => by
    rw [sub_self, Pi.zero_apply, mul_zero]
    exact ciIntAt_zero
  symm := fun {y y'} h l => by
    have h1 := ciIntAt_neg (h l)
    rwa [← mul_neg, ← Pi.neg_apply, neg_sub] at h1
  trans := fun {x y z} h h' l => by
    have h1 := (h l).add (h' l)
    rwa [← mul_add, ← Pi.add_apply, sub_add_sub_cancel] at h1

end GlobalTheory.TwU.Model

end
