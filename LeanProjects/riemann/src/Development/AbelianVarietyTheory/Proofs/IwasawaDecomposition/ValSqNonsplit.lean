import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiser

noncomputable section

namespace GlobalTheory.HeightCounting.FitTw

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain Neutral.B1

theorem val_mem_of_ae {L : Type} [Field L] [NumberField L] (χ : HChar L) (Λ : Subgroup ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    {P : HeightOneSpectrum (𝓞 L)} (hPu : χ.UnrAt P) : χ.val P ∈ Λ := by
  classical
  by_cases hP : P ∈ S
  swap
  · exact hv P hP
  obtain ⟨b, hb1, hb2⟩ : ∃ a ∈ P.asIdeal, a ∉ P.asIdeal ^ 2 := by
    have := Ideal.pow_succ_lt_pow P.ne_bot 1 (P := P.asIdeal)
    rw [pow_one] at this
    exact SetLike.exists_of_lt this
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => 2)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have h1 := ha P hP
  rw [if_pos rfl] at h1
  have ha2 : a ∉ P.asIdeal ^ 2 := fun h => hb2 (by simpa using (P.asIdeal ^ 2).sub_mem h h1)
  have ha1 : a ∈ P.asIdeal := by
    have := P.asIdeal.add_mem (Ideal.pow_le_self two_ne_zero h1) hb1
    simpa using this
  have ha0 : (a : L) ≠ 0 := by
    intro h0
    have h1 : a = 0 := by exact_mod_cast h0
    exact ha2 (h1 ▸ zero_mem _)
  have hval : χ.locK P (Units.mk0 _ ha0) = χ.val P := χ.val_eq hPu _ (by
    unfold IsUnifAt
    rw [TypeValues.val_atFin P _ a rfl, TypeValues.intValuation_eq_of_mem ha1 ha2])
  have h := TypeValues.productRule χ S hu (Units.mk0 _ ha0)
  rw [hi, one_mul, Finset.prod_eq_single_of_mem P hP (fun v hvS hvP => TypeValues.locK_eq_one (ht v) _ a rfl (by
    have h1 := ha v hvS
    rw [if_neg hvP] at h1
    exact Ideal.pow_le_self two_ne_zero h1)), hval] at h
  rw [eq_inv_of_mul_eq_one_left h]
  refine Λ.inv_mem (finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun v => ?_)
  exact finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun hvS => Λ.zpow_mem (hv v hvS) _

def toHC {E : Type} [Field E] [NumberField E] (χ : HChar E) : NC.HC E := ⟨χ.1, χ.2.1, χ.2.2⟩

theorem of_at {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : NC.HC E) (e : ∀ x, h.χ x = χ.1 x)
    {v : HeightOneSpectrum (𝓞 E)} {α : ℂ} (ha : h.At v α) : χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = α := by
  have k := GlobalTheory.HeckeUnifVal.at_val_and_unr_iff χ h (MonoidHom.ext e) v
  have hu : χ.UnrAt v := k.2.2 ha.1
  exact ⟨hu, (k.1 hu).unique ha⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem val_sq_nonsplit (D : D7) {χ : HChar D.host.E} (ht : χ.TrivOn D.host.F) {v : PlE D.host} (hu : χ.UnrAt v)
    (hv : ¬ IsSplitPl D.host v) : χ.val v ^ 2 = 1 := by
  refine TypeValues.val_sq_eq_one D.sp.cm ht hu ?_
  have h : ∀ x ∈ v.asIdeal, Formalism.L2.Col.cO D.host.E x ∈ v.asIdeal := fun x hx => by
    by_contra hn
    refine hv ⟨x, hx, fun y hy hm => hn ?_⟩
    have : Formalism.L2.Col.cO D.host.E x = y := RingOfIntegers.ext ((Formalism.BasicNotions.bridge_star_holds D.R D.host (x : D.host.E)).trans hy.symm)
    rwa [this]
  refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
  rw [Formalism.L2.Col.mem_conjP]
  refine ⟨fun h1 => ?_, h a⟩
  have := h _ h1
  rwa [Formalism.L2.Col.cO_cO] at this

theorem cpow_sqrt (q r t : ℕ) :
    ((q : ℕ) : ℂ) ^ ((((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2 : ℝ) : ℂ) = (Real.sqrt q : ℂ) ^ (-(r : ℤ)) := by
  have h0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have e : (((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2 : ℝ) = (1 / 2 : ℝ) * ((-(r : ℤ) : ℤ) : ℝ) := by
    push_cast; ring
  rw [e, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow h0, Real.rpow_mul h0, Real.rpow_intCast, Real.sqrt_eq_rpow,
    Complex.ofReal_zpow]

set_option maxHeartbeats 1000000 in

theorem psiL_gal {D : D7} {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (T : NCharTied D cf C tp)
    (nct : NChTie D C) (hψ : PsiChoiceCompatible D cf C tp) (a : D.nd.Loc) (H1 : NC.HC D.host.E)
    (hH : ∀ (j : Fin D.R.m), j.1 + 1 = D.nd.j a → ∀ x, H1.χ x = (cf.mu0 j * cf.delAt (D.nd.l a) * cf.eta⁻¹).1 x)
    (hr : NC.Read D.nd.plOm.1 (D.ntw.chi1 (D.ntw.twOf a) (D.nd.j a) (D.ntw.twSide a))
      (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))
      (if D.ntw.twSide a then D.ntw.emb0 (D.ntw.twOf a) else D.ntw.emb0b (D.ntw.twOf a)) (NC.complexEmbeddingRestrictedToSubfield D) H1 (-(D.R.r : ℤ))) :
    IsGalOf D a Set.univ (D.ntw.psiL a) (tp.psi (D.nd.w a)) 0 := by
  classical
  obtain ⟨ψ0, -, h2, h3⟩ := nct.psi_eq
  have hto : ∀ g, toC D a ((D.ntw.psiL a g : (D.nd.O a)ˣ) : D.nd.O a) =
      D.what₂.embLL ((ψ0 (D.nd.w a) g : (D.what₂.LL)ˣ) : D.what₂.LL) := fun g => by
    rw [← D.naut.iota_LL a, h3 a g]
    rfl
  have hP := tp.psi_is (D.nd.w a) (D.nd.w_tw a)
  obtain ⟨B1, h1⟩ := hr
  let j : Fin D.R.m := ⟨D.nd.j a - 1, by have := D.nd.j_range a; omega⟩
  have hj : j.1 + 1 = D.nd.j a := by have := D.nd.j_range a; show D.nd.j a - 1 + 1 = _; omega
  have hone := T.chi_one a j hj
  have htup : tp.tup (D.nd.mu a) j * cf.eta⁻¹ = (cf.mu0 j * cf.delAt (D.nd.l a) * cf.eta⁻¹) * tp.psi (D.nd.w a) := by
    rw [TupTied.tup, D.nd.mu_w, tp.xi_tw, D.nd.w_l]
    rw [← mul_assoc, mul_right_comm _ (tp.psi (D.nd.w a))]
  rw [htup] at hone
  have hfin := NC.finite_placesOver (E := D.host.E) (D.nd.l a)
  let S : Finset (PlE D.host) := B1 ∪ hfin.toFinset ∪ D.nd.S a ∪ D.nd.Q a
  have hu : ∀ v, v ∉ S → (tp.psi (D.nd.w a)).UnrAt v := fun v hv =>
    (hP.ram v).2 (by rw [← nct.Q_eq a]; exact fun h => hv (Finset.mem_union_right _ h))
  have hv : ∀ v, v ∉ S → (tp.psi (D.nd.w a)).val v ∈ RationalValues.unitsIn D.what₂.embLL.fieldRange := fun v hv => by
    show (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
    by_cases hs : IsSplitPl D.host v
    swap
    · have h1 : (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, val_sq_nonsplit D hP.triv (hu v hv) hs, Units.val_one]
      rcases sq_eq_one_iff.1 h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact neg_mem (one_mem _)
    simp only [S, Finset.mem_union, not_or, Set.Finite.mem_toFinset] at hv
    obtain ⟨⟨⟨v1, v2⟩, v3⟩, v4⟩ := hv
    obtain ⟨α, hα, x1, hx1, hσ1⟩ := h1 v v1
    obtain ⟨σ, hσ⟩ := NC.frob_exists D v
    obtain ⟨hu1, hval⟩ := of_at _ H1 (hH j hj) hα
    have hup : (tp.psi (D.nd.w a)).UnrAt v := (hP.ram v).2 (by rw [← nct.Q_eq a]; exact v4)
    have k := hone v ⟨hs, v2, v3, v4⟩ v2 (fun x hx => by rw [HChar.loc_mul, hu1 x hx, hup x hx, one_mul])
      _ σ (D.nd.plOm.2 v) hσ
    have tw := D.ntw.twO_emb a x1 _ (hσ1 σ hσ)
    have hc : (D.nd.chi a 1 σ : D.nd.O a) =
        D.ntw.twist₂ a (D.ntw.chi1 (D.ntw.twOf a) (D.nd.j a) (D.ntw.twSide a) σ : D.ntw.O0 (D.ntw.twOf a)) *
          (D.ntw.psiL a σ : D.nd.O a) := by
      rw [D.ntw.chi_tw a]
      rfl
    have h4 : toC D a (D.ntw.twist₂ a (D.ntw.chi1 (D.ntw.twOf a) (D.nd.j a) (D.ntw.twSide a) σ :
        D.ntw.O0 (D.ntw.twOf a))) = NC.complexEmbeddingRestrictedToSubfield D x1 := by
      simp only [toC, RingHom.comp_apply, NC.complexEmbeddingRestrictedToSubfield]
      rw [← tw]
      exact D.naut.iota_LL a (x1 : D.what₂.LL)
    have hq := cpow_sqrt (normV v) D.R.r D.R.t
    rw [hc, map_mul, h4, hx1, hto, HChar.val_mul, Units.val_inv_eq_inv_val, Units.val_mul, hval] at k
    have k' : α⁻¹ * (Real.sqrt (normV v) : ℂ) ^ (-(D.R.r : ℤ)) *
        D.what₂.embLL ((ψ0 (D.nd.w a) σ : (D.what₂.LL)ˣ) : D.what₂.LL) =
        (α * (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ))⁻¹ * (Real.sqrt (normV v) : ℂ) ^ (-(D.R.r : ℤ)) := by
      rw [← hq]; rw [← hq] at k; exact k
    have hs0 : ((Real.sqrt (normV v) : ℝ) : ℂ) ^ (-(D.R.r : ℤ)) ≠ 0 := by
      have : 0 < Real.sqrt (normV v) := Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NC.normV_ne_zero v)))
      exact zpow_ne_zero _ (by exact_mod_cast this.ne')
    have hα0 : α ≠ 0 := by rw [← hval]; exact Units.ne_zero _
    have k2 : D.what₂.embLL ((ψ0 (D.nd.w a) σ : (D.what₂.LL)ˣ) : D.what₂.LL) = (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ)⁻¹ := by
      rw [mul_inv, mul_right_comm] at k'
      exact mul_left_cancel₀ (inv_ne_zero hα0) (mul_right_cancel₀ hs0 k')
    rw [← inv_inv (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ), ← k2]
    exact inv_mem ⟨_, rfl⟩
  intro v _ hl huv B σ hB hσ
  have : IsTotallyComplex D.host.E := by
    letI := D.host.cmStar
    exact D.sp.cm.cmUnram.1
  obtain ⟨n, hn⟩ := hP.ord
  have hm := val_mem_of_ae _ _ S hP.tame
    (TypeValues.inf_eq_one _ (pow_pos (D.what₂.places.resChar_prime _).pos n) hn) hu hv huv
  obtain ⟨y, hy⟩ : ((((tp.psi (D.nd.w a)).val v)⁻¹ : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := inv_mem hm
  have k := hψ (D.nd.w a) (D.nd.w_tw a) v ((hP.ram v).1 huv) (by rw [D.nd.w_l]; exact hl) B σ hB hσ y hy
  rw [← h2] at k
  rw [hto, ← (C.embW (D.nd.w a)).injective k]
  simp only [Complex.ofReal_zero, Complex.cpow_zero, mul_one]
  exact hy

theorem psiL_read {D : D7} {χ : HChar D.host.E} (a : D.nd.Loc) (Q : Finset (PlE D.host)) (hQ : ∀ v, v ∉ Q → χ.UnrAt v)
    (h : IsGalOf D a Set.univ (D.ntw.psiL a) χ 0) :
    NC.ReadC D.nd.plOm.1 (D.ntw.psiL a) (NC.iotaC D a) (toHC χ) 0 := by
  classical
  have hfin := NC.finite_placesOver (E := D.host.E) (D.nd.l a)
  refine ⟨hfin.toFinset ∪ Q, fun P hP => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset] at hP
  have hu := hQ P hP.2
  refine ⟨_, (GlobalTheory.HeckeUnifVal.at_val_and_unr_iff χ (toHC χ) rfl P).1 hu, _, rfl, fun σ hσ => ?_⟩
  have k := h P (Set.mem_univ _) hP.1 hu _ σ (D.nd.plOm.2 P) hσ
  simp only [Complex.ofReal_zero, Complex.cpow_zero, mul_one, Units.val_inv_eq_inv_val] at k
  exact k.trans (mul_one _).symm

theorem psi_is {D : D7} {cf : CharFrame D} {C : NChoice D} (tp : TupTied D cf C) (nct : NChTie D C) (a : D.nd.Loc) :
    IsPsi (D.nd.l a) (D.nd.Q a) (tp.psi (D.nd.w a)) := by
  rw [nct.Q_eq a, ← D.nd.w_l a]
  exact tp.psi_is _ (D.nd.w_tw a)

theorem etaT_link {D : D7} {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (T : NCharTied D cf C tp)
    (η : NC.HC D.host.E) (h : ∀ x, η.χ x = cf.eta.1 x) (w : PlE D.host) (α : ℂ) (ha : η.At w α) :
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹} := by
  obtain ⟨hu, hv⟩ := of_at _ _ h ha
  rw [T.frob _ w (by rw [T.etaT]; exact hu), T.etaT, Units.val_inv_eq_inv_val, hv]

theorem muC_link {D : D7} {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (T : NCharTied D cf C tp)
    (K : NC.NChiData D) (h1 : ∀ (j : Fin D.R.m) x, (K.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x)
    (h2 : ∀ s x, (K.del s).χ x = (cf.delAt (D.ntw.l s)).1 x) (h3 : ∀ a x, (K.psi a).χ x = (tp.psi (D.nd.w a)).1 x)
    (i : D.nd.Loc) (w : PlE D.host) (α : ℂ) (ha : (K.mu0 (D.nd.j i) * K.del (D.ntw.twOf i) * K.psi i).At w α) :
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹} := by
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩
  have hj : j.1 + 1 = D.nd.j i := by have := D.nd.j_range i; show D.nd.j i - 1 + 1 = _; omega
  have e := T.muC i j hj
  have htup : tp.tup (D.nd.mu i) j = cf.mu0 j * cf.delAt (D.nd.l i) * tp.psi (D.nd.w i) := by
    rw [TupTied.tup, D.nd.mu_w, tp.xi_tw, D.nd.w_l, ← mul_assoc]
  obtain ⟨hu, hv⟩ := of_at (tp.tup (D.nd.mu i) j) _ (fun x => by
    rw [htup, NC.HC.mul_χ, NC.HC.mul_χ, MonoidHom.mul_apply, MonoidHom.mul_apply, ← hj, h1, h2, h3, D.ntw.twOf_l]
    rfl) ha
  rw [T.frob _ w (by rw [e]; exact hu), e, Units.val_inv_eq_inv_val, hv]

theorem psiL_gal' {D : D7} {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (T : NCharTied D cf C tp)
    (nct : NChTie D C) (hψ : PsiChoiceCompatible D cf C tp) (K : NC.NChiData D) (h0 : ∀ x, K.etaT.χ x = cf.eta.1 x)
    (h1 : ∀ (j : Fin D.R.m) x, (K.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x)
    (h2 : ∀ s x, (K.del s).χ x = (cf.delAt (D.ntw.l s)).1 x)
    (hr : ∀ s j (b : Bool), 1 ≤ j → j ≤ D.R.m → NC.Read D.nd.plOm.1 (D.ntw.chi1 s j b)
      (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s))) (if b then D.ntw.emb0 s else D.ntw.emb0b s) (NC.complexEmbeddingRestrictedToSubfield D)
      (K.firstHeckeCharacter s j) (-(D.R.r : ℤ))) (a : D.nd.Loc) :
    IsGalOf D a Set.univ (D.ntw.psiL a) (tp.psi (D.nd.w a)) 0 :=
  psiL_gal T nct hψ a _ (fun j hj x => by
    rw [NC.NChiData.firstHeckeCharacter, NC.HC.mul_χ, NC.HC.mul_χ, NC.HC.inv_χ, MonoidHom.mul_apply, MonoidHom.mul_apply,
      MonoidHom.inv_apply, ← hj, h1, h2, h0, D.ntw.twOf_l]
    rfl) (hr _ _ _ (D.nd.j_range a).1 (D.nd.j_range a).2)

end GlobalTheory.HeightCounting.FitTw

end
