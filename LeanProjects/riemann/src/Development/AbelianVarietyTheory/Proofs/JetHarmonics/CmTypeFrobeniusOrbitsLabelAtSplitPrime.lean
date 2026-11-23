import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEmbeddingsIntegralAndDistinctModMaximal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrobAllEmbeddings
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LabSplit

theorem exists_reps {P : Type} [Fintype P] (d : ℕ) [NeZero d] (pos : P → ℕ → P) (h0 : ∀ z, pos z 0 = z)
    (hadd : ∀ z s t, pos (pos z s) t = pos z (s + t)) (hfree : ∀ z s t, pos z s = pos z t ↔ s ≡ t [MOD d]) :
    ∃ Z : Finset P, ∀ z', ∃! p : P × ZMod d, p.1 ∈ Z ∧ pos p.1 p.2.val = z' := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  let S : Setoid P :=
    { r := fun z z' => ∃ s, pos z s = z'
      iseqv :=
        { refl := fun z => ⟨0, h0 z⟩
          symm := by
            rintro z _ ⟨s, rfl⟩
            refine ⟨(d - 1) * s, ?_⟩
            rw [hadd]
            conv_rhs => rw [← h0 z]
            rw [hfree]
            have : s + (d - 1) * s = d * s := by
              obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
              simp only [Nat.add_sub_cancel_left]; ring
            rw [this]
            exact (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
          trans := by
            rintro z _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
            exact ⟨s + t, (hadd z s t).symm⟩ } }
  refine ⟨Finset.univ.filter fun z => (Quotient.mk S z).out = z, fun z' => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s, pos (Quotient.mk S z').out s = z' := Quotient.mk_out (s := S) z'
  have hmod : ((s : ZMod d)).val ≡ s [MOD d] := by
    rw [ZMod.val_natCast]; exact Nat.mod_modEq s d
  refine ⟨((Quotient.mk S z').out, (s : ZMod d)), ⟨by simp, ?_⟩, ?_⟩
  · exact ((hfree _ _ _).2 hmod).trans hs
  · rintro ⟨z, t⟩ ⟨hz, ht⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ht
    have h1 : Quotient.mk S z = Quotient.mk S z' := Quotient.sound ⟨_, ht⟩
    have h2 : z = (Quotient.mk S z').out := by rw [← h1, hz]
    refine Prod.ext h2 ?_
    rw [h2, ← hs] at ht
    have h3 : pos (Quotient.mk S z').out t.val = pos (Quotient.mk S z').out s := by
      rw [hs] at ht ⊢; exact ht
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).2 ((hfree _ _ _).1 h3)
    simpa using h4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)

theorem rt_sq_field : (H.rt : E) ^ 2 = -(H.d : E) := by
  have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  simpa using this

theorem inPsi_conj_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, rt_sq_field]; simp
  have h2 : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have h := H.sqrt_neg_disc_sq
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [pow_two] at hre him
    have : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [this]
  have h0 : -H.rt0 ≠ H.rt0 := by
    intro h
    have h3 : H.rt0 = 0 := by linear_combination -h / 2
    have h4 := H.sqrt_neg_disc_sq
    rw [h3] at h4
    have : (H.d : ℂ) = 0 := by linear_combination h4
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · rw [h, h2]; simp [h0]
  · rw [h, map_neg, h2]; simp [h0]

theorem not_MM_neg_sub_pow {C : Type} [Field C] (V : VF C) (d : ℕ) (r : C) (hr : r ^ 2 = -(d : C)) (hi : V.Ge 0 r)
    (h2 : V.l ≠ 2) (hj : jacobiSym (-(d : ℤ)) V.l = 1) : ¬ V.MM (-r - r ^ V.l) := by
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
  have hp := legendreSym.eq_pow V.l (-(d : ℤ))
  rw [hj] at hp
  have hdv : (V.l : ℤ) ∣ (-(d : ℤ)) ^ (V.l / 2) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hp ⊢
    rw [← hp, sub_self]
  obtain ⟨k, hk⟩ := hdv
  have hnd : ¬ (V.l : ℤ) ∣ -(d : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← legendreSym.eq_zero_iff, hj]
    exact one_ne_zero
  have hpr : Prime (V.l : ℤ) := Nat.prime_iff_prime_int.1 V.l_prime
  have hn2 : ¬ (V.l : ℤ) ∣ (2 : ℤ) := by
    intro h
    have : V.l ∣ 2 := by exact_mod_cast h
    exact h2 ((Nat.prime_dvd_prime_iff_eq V.l_prime Nat.prime_two).1 this)
  have hv2 := GlobalTheory.EmbSep.v_intCast_eq_zero V hn2
  have hvd := GlobalTheory.EmbSep.v_intCast_eq_zero V hnd
  have hodd : V.l = 2 * (V.l / 2) + 1 := by
    have := V.l_prime.eq_two_or_odd.resolve_left h2
    omega
  have hkC : (-(d : C)) ^ (V.l / 2) = 1 + (V.l : C) * (k : C) := by
    have := congrArg (Int.cast : ℤ → C) hk
    push_cast at this
    linear_combination this
  have hpow : r ^ V.l = r + (V.l : C) * ((k : C) * r) := by
    conv_lhs => rw [hodd, pow_succ, pow_mul, hr, hkC]
    ring
  have hk0 : V.Ge 0 (k : C) := by
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · simpa using VF.ge_natCast (V := V) n
    · simpa using (VF.ge_natCast (V := V) n).neg
  intro hM
  have h1 : 0 < V.v ((V.l : C) * ((k : C) * r)) := by
    rw [V.v.map_mul, V.v_l]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (hk0.mul_int hi))
  have h3 := V.v.map_lt_add hM h1
  have h4 : -r - r ^ V.l + (V.l : C) * ((k : C) * r) = -(((2 : ℤ) : C) * r) := by
    rw [hpow]; push_cast; ring
  rw [h4, V.v.map_neg, V.v.map_mul, hv2, zero_add] at h3
  have h5 : ((-(d : ℤ) : ℤ) : C) = r * r := by push_cast; rw [← hr]; ring
  rw [h5, V.v.map_mul] at hvd
  have h6 : 0 < V.v r + V.v r := lt_of_lt_of_le h3 (le_add_of_nonneg_right h3.le)
  rw [hvd] at h6
  exact lt_irrefl _ h6

theorem labelling_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → N.cls V.l = PrimeClass.splitK → ∀ j : ℕ, ∃ (d : ℕ) (_ : NeZero d) (pos : RPl N.R → ℕ → RPl N.R) (Z : Finset (RPl N.R)), RF.IsReps (parAt N j d pos) Z ∧ Z.Nonempty ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod d => tauSp N pl pos x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauSp (d := d) N pl pos z g) := by
  intro E _ _ _ H lv c N pl hP la T io C _ _ V ι hE hl _ hcls j
  obtain ⟨φ, hφ⟩ := GlobalTheory.RowAt.exists_frob_all_embeddings E H lv c T io C V ι hE hP.galois hP.comm
  haveI : Inhabited (RPl N.R) := ⟨(false, 0)⟩
  have h2 : V.l ≠ 2 := by
    intro h
    unfold NumDatum.cls primeClass at hcls
    rw [if_pos (show V.l ∈ N.H.small from h ▸ Nat.mem_primeFactors.2 ⟨Nat.prime_two, N.H.two_dvd_QS, N.H.QS_pos.ne'⟩)] at hcls
    exact absurd hcls (by decide)
  have hj : jacobiSym (-(H.d : ℤ)) V.l = 1 := by
    rw [hP.d_eq]
    by_contra h
    unfold NumDatum.cls primeClass at hcls
    split_ifs at hcls
  have hfix : φ (H.rt : E) = H.rt := by
    have h1 : (φ (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      rw [← map_pow, rt_sq_field]; simp
    refine (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_right fun h => ?_
    let τ : E →+* ℂ := pl default
    have h3 : emA3 io ι (τ.comp (φ : E →+* E)) H.rt = -emA3 io ι τ H.rt := by
      have : embK c (τ.comp (φ : E →+* E)) H.rt = -embK c τ H.rt := by
        apply Subtype.ext
        rw [embK_coe]
        push_cast
        rw [embK_coe]
        simp [h]
      simp only [emA3, RingHom.comp_apply, this, map_neg]
    have h4 := hφ τ H.rt
    rw [h3] at h4
    refine not_MM_neg_sub_pow V H.d _ ?_ ?_ h2 hj h4
    · rw [← map_pow, H.rt_sq]; simp
    · exact ge_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral H.rt))
  have hfixs : ∀ s : ℕ, (φ ^ s) (H.rt : E) = H.rt := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [pow_succ, AlgEquiv.mul_apply, hfix, ih]
  have hex : ∀ (z : RPl N.R) (s : ℕ), ∃ z', pl z' = (pl z).comp ((φ ^ s : E ≃ₐ[ℚ] E) : E →+* E) := by
    intro z s
    refine (hP.psi _).1 ?_
    have : InPsi H (pl z) := (hP.psi _).2 ⟨z, rfl⟩
    unfold InPsi at this ⊢
    change pl z ((φ ^ s) (H.rt : E)) = H.rt0
    rw [hfixs]; exact this
  choose pos hpos using hex
  haveI : NeZero (orderOf φ) := ⟨(orderOf_pos φ).ne'⟩
  have h0 : ∀ z, pos z 0 = z := fun z => hP.inj (by rw [hpos]; ext x; simp)
  have hadd : ∀ z s t, pos (pos z s) t = pos z (s + t) := fun z s t =>
    hP.inj (by rw [hpos, hpos, hpos]; ext x; simp [pow_add])
  have hfree : ∀ z s t, pos z s = pos z t ↔ s ≡ t [MOD orderOf φ] := by
    intro z s t
    rw [← pow_eq_pow_iff_modEq, ← hP.inj.eq_iff, hpos, hpos]
    constructor
    · intro h
      ext x
      exact (pl z).injective (RingHom.congr_fun h x)
    · intro h; rw [h]
  obtain ⟨Z, hZ⟩ := exists_reps (orderOf φ) pos h0 hadd hfree
  have hin : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have hnc : ∀ z z', pl z ≠ ComplexEmbedding.conjugate (pl z') := fun z z' h =>
    (inPsi_conj_iff H _).1 (h ▸ hin z) (hin z')
  have huniq : ∀ (z z' : Z) (s s' : ZMod (orderOf φ)), pl (pos z s.val) = pl (pos z' s'.val) → z = z' ∧ s = s' := by
    intro z z' s s' h
    have := (hZ (pos z' s'.val)).unique (y₁ := (z.1, s)) (y₂ := (z'.1, s')) ⟨z.2, hP.inj h⟩ ⟨z'.2, rfl⟩
    exact ⟨Subtype.ext (congrArg Prod.fst this), congrArg Prod.snd this⟩
  refine ⟨orderOf φ, inferInstance, pos, Z, hZ, ?_, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp, -⟩ := hZ default
    exact ⟨p.1, hp.1⟩
  · rintro ⟨z, g, s⟩ ⟨z', g', s'⟩ h
    simp only [tauSp] at h
    split_ifs at h with hg hg' hg'
    · obtain ⟨rfl, rfl⟩ := huniq _ _ _ _ h
      rw [hg, hg']
    · exact absurd h (hnc _ _)
    · exact absurd h.symm (hnc _ _)
    · obtain ⟨rfl, rfl⟩ := huniq _ _ _ _ (star_injective h)
      have : g = g' := by omega
      rw [this]
  · intro τ
    by_cases hτ : InPsi H τ
    · obtain ⟨z', rfl⟩ := (hP.psi _).1 hτ
      obtain ⟨p, hp, -⟩ := hZ z'
      exact ⟨(⟨p.1, hp.1⟩, 0, p.2), by simp [tauSp, hp.2]⟩
    · obtain ⟨z', hz'⟩ := (hP.psi _).1 ((inPsi_conj_iff H τ).2 hτ)
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, 1, p.2), ?_⟩
      simp only [tauSp, hp.2, hz', one_ne_zero, if_false]
      exact star_star τ
  · intro z g s x
    have h1 : pos z (s + 1).val = pos z (s.val + 1) := by
      rw [hfree, ← ZMod.natCast_eq_natCast_iff]
      simp
    have h3 : pl (pos z (s + 1).val) = (pl (pos z s.val)).comp (φ : E →+* E) := by
      rw [h1, hpos, hpos]; ext y; simp [pow_succ]
    have h4 : tauSp (d := orderOf φ) N pl pos z g (s + 1) = (tauSp (d := orderOf φ) N pl pos z g s).comp (φ : E →+* E) := by
      unfold tauSp
      split_ifs
      · exact h3
      · rw [h3]; rfl
    rw [h4]
    exact hφ _ x

end GlobalTheory.LabSplit
