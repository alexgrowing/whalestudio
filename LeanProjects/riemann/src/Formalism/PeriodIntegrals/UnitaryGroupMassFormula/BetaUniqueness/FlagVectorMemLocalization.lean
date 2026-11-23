import Mathlib
import Formalism.PeriodIntegrals.BetaLUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.EqZeroOfNormLtOne

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
open PI.UnitaryGroupMassFormula.BetaLUniq.EigA

namespace PI.UnitaryGroupMassFormula.BetaLUniq.EigB

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def cO : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (starRingAut : E ≃+* E)

theorem cO_coe (o : 𝓞 E) : algebraMap (𝓞 E) E (cO o) = star (algebraMap (𝓞 E) E o) := rfl

theorem star_InO {x : E} (h : InO x) : InO (star x) := by
  obtain ⟨o, rfl⟩ := h
  exact ⟨cO o, cO_coe o⟩

theorem star_natCast_E (g : ℕ) : star (g : E) = g := by
  simp

def conjPrime₂ (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (cO (E := E)).toRingHom
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro p hp
    have : (cO (E := E)).symm p ∈ P.asIdeal.comap (cO (E := E)).toRingHom := by
      simp only [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply]; exact hp
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    simpa using congrArg cO this

theorem mem_conjP (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E) : s ∈ (conjPrime₂ P).asIdeal ↔ cO s ∈ P.asIdeal := by
  simp [conjPrime₂]

theorem natCast_mem_conjP (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) (hg : (g : 𝓞 E) ∈ P.asIdeal) :
    (g : 𝓞 E) ∈ (conjPrime₂ P).asIdeal := by
  rw [mem_conjP, map_natCast]; exact hg

section Loc

variable {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

theorem mem_locP (p : Ideal (𝓞 E)) [p.IsPrime] (M : Submodule (𝓞 E) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p M ↔ ∃ s : 𝓞 E, s ∉ p ∧ s • x ∈ M := Iff.rfl

theorem le_locP (p : Ideal (𝓞 E)) [p.IsPrime] (M : Submodule (𝓞 E) W) : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M :=
  fun x hx => ⟨1, p.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono (p : Ideal (𝓞 E)) [p.IsPrime] {M N : Submodule (𝓞 E) W} (h : M ≤ N) :
    Formalism.HermitianLatticesTheory.localization₂ p M ≤ Formalism.HermitianLatticesTheory.localization₂ p N := by
  rintro x ⟨s, hs, hx⟩; exact ⟨s, hs, h hx⟩

theorem localization_le_localization_of_le_localization' (p : Ideal (𝓞 E)) [hp : p.IsPrime] {M N : Submodule (𝓞 E) W}
    (h : N ≤ Formalism.HermitianLatticesTheory.localization₂ p M) : Formalism.HermitianLatticesTheory.localization₂ p N ≤ Formalism.HermitianLatticesTheory.localization₂ p M := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, htx⟩ := h hx
  refine ⟨t * s, ?_, by rw [mul_smul]; exact htx⟩
  intro hts
  rcases hp.mem_or_mem hts with h1 | h1
  · exact ht h1
  · exact hs h1

theorem exists_smul_mem_of_forall_mem_localization (p : Ideal (𝓞 E)) [hp : p.IsPrime] (M : Submodule (𝓞 E) W) {n : ℕ} (x : Fin n → W)
    (hx : ∀ a, x a ∈ Formalism.HermitianLatticesTheory.localization₂ p M) : ∃ s : 𝓞 E, s ∉ p ∧ ∀ a, s • x a ∈ M := by
  classical
  choose f hf using hx
  refine ⟨∏ a, f a, ?_, fun a => ?_⟩
  · intro hmem
    obtain ⟨c, -, hc⟩ := (Ideal.IsPrime.prod_mem_iff).mp hmem
    exact (hf c).1 hc
  · rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a), mul_comm, mul_smul]
    exact M.smul_mem _ (hf a).2

end Loc

variable {S : HSpace E}

theorem smulO (o : 𝓞 E) (x : S.V) : o • x = (algebraMap (𝓞 E) E o) • x :=
  (algebraMap_smul E o x).symm

theorem hT_swap (x y : S.V) : S.hT y x = star (S.hT x y) :=
  (S.herm.eq x y).symm

theorem hT_smul_left (c : E) (x y : S.V) : S.hT (c • x) y = star c * S.hT x y := by
  simp [LinearMap.map_smulₛₗ, starRingEnd_apply]

theorem hT_smul_right (c : E) (x y : S.V) : S.hT x (c • y) = c * S.hT x y := by
  simp

variable (Λ : Submodule (𝓞 E) S.V)

theorem int_of_unimod (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    InO (S.hT x y) := by
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU; rw [hU]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one] at hy'
  exact hy' x hx

theorem mem_of_left_dual (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {w : S.V}
    (hw : ∀ l ∈ Λ, InO (S.hT w l)) : w ∈ Λ := by
  have : w ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]
    intro l hl
    rw [hT_swap]
    exact star_InO (hw l hl)
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU
  rwa [hU] at this

variable {Λ}

theorem Xsp_eq {r : ℕ} {T : E} (F : LFlag S r T) : Xsp F = Submodule.span E (Set.range F.fl.e) := rfl

theorem e_mem_Xsp {r : ℕ} {T : E} (F : LFlag S r T) (a : Fin r) : F.fl.e a ∈ Xsp F :=
  Submodule.subset_span ⟨a, rfl⟩

theorem hT_X {r : ℕ} {T : E} (F : LFlag S r T) {x y : S.V} (hx : x ∈ Xsp F) (hy : y ∈ Xsp F) :
    S.hT x y = 0 := by
  rw [Xsp_eq] at hx hy
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb => obtain ⟨j, rfl⟩ := hb; exact F.fl.e_iso i j
    | zero => simp
    | add _ _ _ _ h1 h2 => simp [h1, h2]
    | smul c _ _ h => simp [h]
  | zero => simp
  | add _ _ _ _ h1 h2 => simp [h1, h2]
  | smul c _ _ h => simp [h]

theorem Xflag_r {r : ℕ} {T : E} (F : LFlag S r T) : Xflag F r = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)
  congr 1
  ext x; simp

theorem e_mem_loc {g r : ℕ} {T : E} {F : LFlag S r T} (hFC : IsFixedConv Λ g F)
    (Q : HeightOneSpectrum (𝓞 E)) (hgQ : (g : 𝓞 E) ∈ Q.asIdeal) (a : Fin r) :
    haveI := Q.isPrime; F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (XLam Λ F) := by
  have := Q.isPrime
  obtain ⟨c, -, hc1, heq⟩ := hFC.1 Q
  have hc := hc1 hgQ
  change Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (XLam Λ F) = _ at heq
  rw [heq]
  apply le_locP
  apply Submodule.subset_span
  exact ⟨a, by simp [hc a]⟩

theorem XLam_le_loc {g r : ℕ} {T : E} {F : LFlag S r T} (hFC : IsFixedConv Λ g F)
    (Q : HeightOneSpectrum (𝓞 E)) (hgQ : (g : 𝓞 E) ∈ Q.asIdeal) :
    haveI := Q.isPrime;
    XLam Λ F ≤ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Submodule.span (𝓞 E) (Set.range F.fl.e)) := by
  have := Q.isPrime
  obtain ⟨c, -, hc1, heq⟩ := hFC.1 Q
  have hc := hc1 hgQ
  change Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (XLam Λ F) = _ at heq
  have : (fun a => c a • F.fl.e a) = F.fl.e := by funext a; simp [hc a]
  rw [this] at heq
  rw [← heq]
  exact le_locP _ _

theorem coe_smul (o : 𝓞 E) (x : S.V) : ((o : E)) • x = o • x := algebraMap_smul E o x

theorem frame_castSucc {r : ℕ} {T : E} (F : LFlag S r T) (a : Fin r) :
    frame F (Fin.castSucc a) = F.fl.e a := by
  simp [frame, FlagG.fvec]

theorem frame_last {r : ℕ} {T : E} (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [frame, FlagG.fvec]

theorem flag_vector_mem_localization {g r : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}
    {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)} (hFC : IsFixedConv Λ g F) (hA : AdmWit Λ g F F' ξ)
    (Q : HeightOneSpectrum (𝓞 E)) (hgQ : (g : 𝓞 E) ∈ Q.asIdeal) (a : Fin r)
    (ih : ∀ c : Fin r, c.val < a.val → F.fl.e c ∈
      (haveI := Q.isPrime; Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F'))) :
    haveI := Q.isPrime;
    F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') := by
  have := Q.isPrime
  set N := Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') with hN
  have hgΛ : Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) ≤ N :=
    localization_mono _ le_sup_left
  have heΛ : ∀ c : Fin r, F.fl.e c ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ := fun c =>
    localization_mono _ inf_le_left (e_mem_loc hFC Q hgQ c)
  set b : Fin (r + 1) := Fin.castSucc a with hb
  let term : Fin (r + 1) → S.V := fun c => ((ξ c b : 𝓞 E) : E) • frame F c
  have hlast : ξ (Fin.last r) b = 0 := hA.1 _ _ (Fin.castSucc_lt_last a)
  have hterm_loc : ∀ c, term c ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ := by
    intro c
    induction c using Fin.lastCases with
    | last => simp [term, hlast]
    | cast c' =>
      simp only [term, frame_castSucc, coe_smul]
      exact Submodule.smul_mem _ _ (heΛ c')
  have hterm_N : ∀ c ∈ Finset.univ.erase b, term c ∈ N := by
    intro c hc
    have hcb : c ≠ b := Finset.ne_of_mem_erase hc
    induction c using Fin.lastCases with
    | last => simp [term, hlast]
    | cast c' =>
      have hc' : c' ≠ a := fun h => hcb (by rw [h])
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hc') with h | h
      · simp only [term, frame_castSucc, coe_smul]
        exact Submodule.smul_mem _ _ (ih c' h)
      · have : ξ (Fin.castSucc c') b = 0 := hA.1 _ _ (by
          rw [hb]; exact Fin.castSucc_lt_castSucc_iff.mpr (Fin.lt_def.mpr h))
        simp [term, this]
  have hsum : frameAct (frame F) ξ b = F.fl.e a + ∑ c ∈ Finset.univ.erase b, term c := by
    have h1 := Finset.add_sum_erase Finset.univ term (Finset.mem_univ b)
    have h2 : term b = F.fl.e a := by
      simp [term, hb, hA.2.1, frame_castSucc]
    rw [h2] at h1
    rw [h1]
    rfl
  have hd : frame F' b - frameAct (frame F) ξ b ∈
      Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := hA.2.2 b Q hgQ
  have hfa_loc : frameAct (frame F) ξ b ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ :=
    Submodule.sum_mem _ (fun c _ => hterm_loc c)
  have he'_loc : frame F' b ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ := by
    have h3 : frame F' b = frameAct (frame F) ξ b + (frame F' b - frameAct (frame F) ξ b) := by abel
    rw [h3]
    exact Submodule.add_mem _ hfa_loc (localization_mono _ (Submodule.smul_le_right) hd)
  have he'_N : frame F' b ∈ N := by
    obtain ⟨s, hs, hsx⟩ := he'_loc
    refine ⟨s, hs, Submodule.mem_sup_right ⟨hsx, ?_⟩⟩
    show s • frame F' b ∈ Xsp F'
    rw [frame_castSucc]
    exact Submodule.smul_of_tower_mem _ s (e_mem_Xsp F' a)
  have hfin : F.fl.e a = frame F' b - (frame F' b - frameAct (frame F) ξ b) -
      ∑ c ∈ Finset.univ.erase b, term c := by
    rw [hsum]; abel
  rw [hfin]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ he'_N (hgΛ hd)) (Submodule.sum_mem _ hterm_N)

theorem e_mem_loc_adm {g r : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}
    {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)} (hFC : IsFixedConv Λ g F) (hA : AdmWit Λ g F F' ξ)
    (Q : HeightOneSpectrum (𝓞 E)) (hgQ : (g : 𝓞 E) ∈ Q.asIdeal) (a : Fin r) :
    haveI := Q.isPrime;
    F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') := by
  suffices h : ∀ n : ℕ, ∀ a : Fin r, a.val < n → F.fl.e a ∈
      (haveI := Q.isPrime; Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F')) from
    h r a a.2
  intro n
  induction n with
  | zero => intro a ha; omega
  | succ n ihn =>
    intro a ha
    exact flag_vector_mem_localization hFC hA Q hgQ a (fun c hc => ihn c (by omega))

theorem hT_sum_left {ι : Type*} (s : Finset ι) (f : ι → S.V) (y : S.V) :
    S.hT (∑ i ∈ s, f i) y = ∑ i ∈ s, S.hT (f i) y := by
  rw [map_sum, LinearMap.sum_apply]

theorem algebraMap_injO : Function.Injective (algebraMap (𝓞 E) E) :=
  FaithfulSMul.algebraMap_injective (𝓞 E) E

theorem noKill {g r : ℕ} {T : E} {F : LFlag S r T} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hFC : IsFixedConv Λ g F) (P : HeightOneSpectrum (𝓞 E)) (hgP : (g : 𝓞 E) ∈ P.asIdeal)
    (s₀ : 𝓞 E) (hs₀ : s₀ ∉ (conjPrime₂ P).asIdeal) (c : Fin r → 𝓞 E)
    (hc : ∀ l ∈ Λ, ∃ p ∈ P.asIdeal, algebraMap (𝓞 E) E p =
      ∑ a, algebraMap (𝓞 E) E (c a) * S.hT (s₀ • F.fl.e a) l) :
    ∀ a, c a ∈ P.asIdeal := by
  have hPp := P.isPrime
  obtain ⟨π, hπP, hπ0, b, hbP, hbπ⟩ := exists_pi_b P.asIdeal P.ne_bot
  set πE := algebraMap (𝓞 E) E π with hπE_def
  have hπE : πE ≠ 0 := by
    intro h; apply hπ0; apply algebraMap_injO; rw [← hπE_def, h, map_zero]
  set bE := algebraMap (𝓞 E) E b
  set s₀E := algebraMap (𝓞 E) E s₀
  let y : S.V := ∑ a, star (algebraMap (𝓞 E) E (c a)) • (s₀ • F.fl.e a)
  let w : S.V := star (bE / πE) • y
  have hwl : ∀ l ∈ Λ, InO (S.hT w l) := by
    intro l hl
    obtain ⟨p, hp, hpe⟩ := hc l hl
    have e1 : S.hT w l = bE / πE * algebraMap (𝓞 E) E p := by
      simp only [w, y, hT_smul_left, star_star, hT_sum_left, hpe]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hbπ p hp)
    refine ⟨t, ?_⟩
    rw [e1]
    have : algebraMap (𝓞 E) E t * πE = bE * algebraMap (𝓞 E) E p := by
      rw [hπE_def, ← map_mul, ht, map_mul]
    field_simp
    rw [this]
  have hwΛ : w ∈ Λ := mem_of_left_dual Λ hU hwl
  have hwX : w ∈ Xsp F := by
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro a _
    apply Submodule.smul_mem
    exact Submodule.smul_of_tower_mem _ s₀ (e_mem_Xsp F a)
  have hQ := natCast_mem_conjP P g hgP
  obtain ⟨s', hs', hs'w⟩ := XLam_le_loc (Λ := Λ) hFC (conjPrime₂ P) hQ ⟨hwΛ, hwX⟩
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hs'w
  have hind := Fintype.linearIndependent_iff.mp F.fl.e_indep
    (fun a => algebraMap (𝓞 E) E (o a) -
      algebraMap (𝓞 E) E s' * (star (bE / πE) * (star (algebraMap (𝓞 E) E (c a)) * s₀E))) (by
      have h1 : ∑ a, algebraMap (𝓞 E) E (o a) • F.fl.e a = s' • w := by
        rw [← ho]; simp only [coe_smul]
      have h2 : s' • w = ∑ a, (algebraMap (𝓞 E) E s' * (star (bE / πE) *
          (star (algebraMap (𝓞 E) E (c a)) * s₀E))) • F.fl.e a := by
        simp only [w, y, smulO, Finset.smul_sum, smul_smul, s₀E]
      simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self])
  intro a
  have ha := sub_eq_zero.mp (hind a)

  have hst := congrArg star ha
  rw [← cO_coe] at hst
  simp only [star_mul, star_star, star_div₀] at hst
  rw [← cO_coe, ← cO_coe] at hst

  have key : algebraMap (𝓞 E) E (cO (o a) * π) = algebraMap (𝓞 E) E (b * c a * cO s' * cO s₀) := by
    simp only [map_mul]
    rw [hst]
    field_simp
    ring
  have key' := algebraMap_injO key
  have hmem : b * c a * cO s' * cO s₀ ∈ P.asIdeal := by
    rw [← key']; exact Ideal.mul_mem_left _ _ hπP
  have hs'P : cO s' ∉ P.asIdeal := fun h => hs' ((mem_conjP P s').mpr h)
  have hs₀P : cO s₀ ∉ P.asIdeal := fun h => hs₀ ((mem_conjP P s₀).mpr h)
  rcases hPp.mem_or_mem hmem with h | h
  · rcases hPp.mem_or_mem h with h | h
    · rcases hPp.mem_or_mem h with h | h
      · exact absurd h hbP
      · exact h
    · exact absurd h hs'P
  · exact absurd h hs₀P

def iv (ε : S.V) (x : S.V) : 𝓞 E := by
  classical
  exact if h : InO (S.hT ε x) then h.choose else 0

theorem iv_spec (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {ε x : S.V} (hε : ε ∈ Λ) (hx : x ∈ Λ) :
    algebraMap (𝓞 E) E (iv ε x) = S.hT ε x := by
  have h := int_of_unimod Λ hU hε hx
  simp only [iv, h, dif_pos]
  exact h.choose_spec

theorem surj {r : ℕ} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (P : HeightOneSpectrum (𝓞 E))
    (ε : Fin r → S.V) (hε : ∀ a, ε a ∈ Λ)
    (hnk : ∀ c : Fin r → 𝓞 E, (∀ l ∈ Λ, ∃ p ∈ P.asIdeal, algebraMap (𝓞 E) E p =
      ∑ a, algebraMap (𝓞 E) E (c a) * S.hT (ε a) l) → ∀ a, c a ∈ P.asIdeal) :
    ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∀ u : Fin r → 𝓞 E, ∃ l ∈ Λ, ∀ a,
      S.hT (ε a) l = algebraMap (𝓞 E) E t * algebraMap (𝓞 E) E (u a) := by
  classical
  have hmax : P.asIdeal.IsMaximal := P.isMaximal
  let _ : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field _
  let mk := Ideal.Quotient.mk P.asIdeal
  have iv_add : ∀ a, ∀ x ∈ Λ, ∀ y ∈ Λ, iv (ε a) (x + y) = iv (ε a) x + iv (ε a) y := by
    intro a x hx y hy
    apply algebraMap_injO
    rw [map_add, iv_spec hU (hε a) hx, iv_spec hU (hε a) hy, iv_spec hU (hε a) (Λ.add_mem hx hy),
      map_add]
  have iv_smul : ∀ a, ∀ (o : 𝓞 E), ∀ x ∈ Λ, iv (ε a) (o • x) = o * iv (ε a) x := by
    intro a o x hx
    apply algebraMap_injO
    rw [map_mul, iv_spec hU (hε a) hx, iv_spec hU (hε a) (Λ.smul_mem o hx), smulO, hT_smul_right]
  have iv_zero : ∀ a, iv (ε a) 0 = 0 := by
    intro a
    apply algebraMap_injO
    rw [iv_spec hU (hε a) Λ.zero_mem, map_zero, map_zero]
  let ρ : S.V → Fin r → 𝓞 E ⧸ P.asIdeal := fun x a => mk (iv (ε a) x)
  let Wk : Submodule (𝓞 E ⧸ P.asIdeal) (Fin r → 𝓞 E ⧸ P.asIdeal) :=
    { carrier := {w | ∃ x ∈ Λ, ρ x = w}
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        refine ⟨x + y, Λ.add_mem hx hy, ?_⟩
        funext a; simp only [ρ, Pi.add_apply, iv_add a x hx y hy, map_add]
      zero_mem' := ⟨0, Λ.zero_mem, by funext a; simp [ρ, iv_zero]⟩
      smul_mem' := by
        rintro q _ ⟨x, hx, rfl⟩
        obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine ⟨o • x, Λ.smul_mem o hx, ?_⟩
        funext a; simp only [ρ, Pi.smul_apply, iv_smul a o x hx, map_mul, smul_eq_mul]; rfl }
  have hW : Wk = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne)
      inferInstance
    let ef : Fin r → (Fin r → 𝓞 E ⧸ P.asIdeal) := fun a j => if a = j then 1 else 0
    have hc : ∀ a, ∃ c : 𝓞 E, mk c = f (ef a) := fun a => Ideal.Quotient.mk_surjective _
    choose c hc using hc
    have hfw : ∀ w, f w = ∑ a, w a * f (ef a) := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ f w]
      simp [ef, smul_eq_mul]
    have hall := hnk c (by
      intro l hl
      refine ⟨∑ a, c a * iv (ε a) l, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem]
        have h1 : f (ρ l) = 0 := by
          have : f (ρ l) ∈ Wk.map f := Submodule.mem_map_of_mem ⟨l, hl, rfl⟩
          rw [hfW] at this
          exact (Submodule.mem_bot _).mp this
        rw [hfw] at h1
        rw [map_sum]
        simp only [map_mul]
        rw [← h1]
        apply Finset.sum_congr rfl
        intro a _
        show mk (c a) * mk (iv (ε a) l) = mk (iv (ε a) l) * f (ef a)
        rw [hc a]; ring
      · rw [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [map_mul, iv_spec hU (hε a) hl])
    apply hf0
    apply LinearMap.ext
    intro w
    rw [hfw]
    simp only [LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro a _
    rw [← hc a, Ideal.Quotient.eq_zero_iff_mem.mpr (hall a), mul_zero]
  have hlam : ∀ a, ∃ x ∈ Λ, ρ x = fun j => if a = j then 1 else 0 := by
    intro a
    have : (fun j => if a = j then (1 : 𝓞 E ⧸ P.asIdeal) else 0) ∈ Wk := by rw [hW]; trivial
    exact this
  choose lam hlamΛ hlamρ using hlam
  let Mo : Matrix (Fin r) (Fin r) (𝓞 E) := fun b a => iv (ε b) (lam a)
  have hMo : Mo.map mk = 1 := by
    ext b a
    have h := congrFun (hlamρ a) b
    simp only [ρ] at h
    show mk (iv (ε b) (lam a)) = (1 : Matrix (Fin r) (Fin r) _) b a
    rw [h, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hdet : mk Mo.det = 1 := by
    rw [RingHom.map_det]
    change (Mo.map mk).det = 1
    rw [hMo, Matrix.det_one]
  refine ⟨Mo.det, ?_, ?_⟩
  · intro hmem
    have : mk Mo.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hdet] at this
    exact one_ne_zero this
  · intro u
    let wv := Mo.adjugate.mulVec u
    refine ⟨∑ a, wv a • lam a, Submodule.sum_mem _ (fun a _ => Λ.smul_mem _ (hlamΛ a)), ?_⟩
    intro b
    have hmv : (Mo.mulVec wv) b = Mo.det * u b := by
      simp only [wv, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
    have e1 : S.hT (ε b) (∑ a, wv a • lam a) = algebraMap (𝓞 E) E ((Mo.mulVec wv) b) := by
      rw [map_sum]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [smulO, hT_smul_right, ← iv_spec hU (hε b) (hlamΛ a)]
      simp only [Mo]; ring
    rw [e1, hmv, map_mul]

theorem mem_gΛ (g : ℕ) {x : S.V} (hx : x ∈ Ideal.span {(g : 𝓞 E)} • Λ) : ∃ l ∈ Λ, x = (g : 𝓞 E) • l := by
  rw [Submodule.ideal_span_singleton_smul] at hx
  obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  exact ⟨l, hl, rfl⟩

theorem g_mem_gΛ (g : ℕ) {l : S.V} (hl : l ∈ Λ) : (g : 𝓞 E) • l ∈ Ideal.span {(g : 𝓞 E)} • Λ :=
  Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl

theorem hT_gl (g : ℕ) (l y : S.V) : S.hT ((g : 𝓞 E) • l) y = (g : E) * S.hT l y := by
  rw [smulO, hT_smul_left, map_natCast, star_natCast_E]

theorem iotaLift {g r : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}
    {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hFC : IsFixedConv Λ g F) (hA : AdmWit Λ g F F' ξ) (P : HeightOneSpectrum (𝓞 E))
    (hgP : (g : 𝓞 E) ∈ P.asIdeal) (x' : S.V) (hx'Λ : x' ∈ Λ) (hx'o : x' ∈ orth S (Xsp F')) :
    ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∃ l ∈ Lrep Λ F, l - t • x' ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
  have hPp := P.isPrime
  set Q := conjPrime₂ P
  have hQp := Q.isPrime
  have hgQ := natCast_mem_conjP P g hgP
  obtain ⟨s₀, hs₀, hs₀e⟩ := exists_smul_mem_of_forall_mem_localization Q.asIdeal Λ F.fl.e
    (fun a => localization_mono _ inf_le_left (e_mem_loc hFC Q hgQ a))
  let ε : Fin r → S.V := fun a => s₀ • F.fl.e a
  obtain ⟨t₀, ht₀, hsurj⟩ := surj hU P ε hs₀e (noKill (Λ := Λ) hU hFC P hgP s₀ hs₀)
  obtain ⟨s₁', hs₁', hs₁e⟩ := exists_smul_mem_of_forall_mem_localization Q.asIdeal _ F.fl.e
    (fun a => e_mem_loc_adm (Λ := Λ) hFC hA Q hgQ a)
  have hval : ∀ a, ∃ o : 𝓞 E, algebraMap (𝓞 E) E (cO s₁') * S.hT (ε a) x' =
      (g : E) * algebraMap (𝓞 E) E o := by
    intro a
    obtain ⟨y₁, hy₁, y₂, hy₂, hsum⟩ := Submodule.mem_sup.mp (hs₁e a)
    obtain ⟨l₁, hl₁, rfl⟩ := mem_gΛ (Λ := Λ) g hy₁
    obtain ⟨o, ho⟩ := int_of_unimod Λ hU hl₁ hx'Λ
    refine ⟨cO s₀ * o, ?_⟩
    have h0 : S.hT y₂ x' = 0 := (mem_orth S).mp hx'o y₂ hy₂.2
    have h1 : S.hT (s₁' • F.fl.e a) x' = (g : E) * algebraMap (𝓞 E) E o := by
      rw [← hsum, map_add, LinearMap.add_apply, h0, add_zero, hT_gl, ho]
    rw [smulO, hT_smul_left, ← cO_coe] at h1
    simp only [ε]
    rw [smulO, hT_smul_left, ← cO_coe, map_mul]
    calc algebraMap (𝓞 E) E (cO s₁') * (algebraMap (𝓞 E) E (cO s₀) * S.hT (F.fl.e a) x')
        = algebraMap (𝓞 E) E (cO s₀) * (algebraMap (𝓞 E) E (cO s₁') * S.hT (F.fl.e a) x') := by ring
      _ = _ := by rw [h1]; ring
  choose u hu using hval
  obtain ⟨lam, hlam, hlamv⟩ := hsurj u
  let t : 𝓞 E := t₀ * cO s₁'
  let l : S.V := t • x' - (g : 𝓞 E) • lam
  have hs₁P : cO s₁' ∉ P.asIdeal := fun h => hs₁' ((mem_conjP P s₁').mpr h)
  refine ⟨t, fun h => ?_, l, ⟨?_, ?_⟩, ?_⟩
  · rcases hPp.mem_or_mem h with h | h
    · exact ht₀ h
    · exact hs₁P h
  · exact Λ.sub_mem (Λ.smul_mem _ hx'Λ) (Λ.smul_mem _ hlam)
  ·
    have hεl : ∀ a, S.hT (ε a) l = 0 := by
      intro a
      simp only [l, map_sub, smulO, hT_smul_right, hlamv]
      have := hu a
      simp only [t, map_mul]
      rw [mul_assoc, this, map_natCast]
      ring
    have hel : ∀ a, S.hT (F.fl.e a) l = 0 := by
      intro a
      have h := hεl a
      simp only [ε, smulO, hT_smul_left] at h
      rcases mul_eq_zero.mp h with h | h
      · exfalso
        have : algebraMap (𝓞 E) E s₀ = 0 := by
          have := congrArg star h; rwa [star_star, star_zero] at this
        apply hs₀
        rw [(algebraMap_injO (this.trans (map_zero _).symm))]
        exact zero_mem _
      · exact h
    show l ∈ orth S (Xsp F)
    rw [mem_orth]
    intro x hx
    rw [Xsp_eq] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hel a
    | zero => simp
    | add _ _ _ _ h1 h2 => simp [h1, h2]
    | smul c _ _ h => simp [h]
  · have : l - t • x' = -((g : 𝓞 E) • lam) := by simp only [l]; abel
    rw [this]
    exact Submodule.neg_mem _ (g_mem_gΛ (Λ := Λ) g hlam)

theorem symm_mem {β : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ β) {x : S.V} (hx : x ∈ Λ) : β.symm x ∈ Λ := by
  have h2 := h.2
  unfold Formalism.HermitianLatticesTheory.gmap at h2
  rw [← h2] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem symm_mem_X {r : ℕ} {T' : E} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}
    (h : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j) {x : S.V} (hx : x ∈ Xsp F'') :
    β.symm x ∈ Xsp F' := by
  rw [← Xflag_r, ← h r] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← Xflag_r]
  simpa using hy

theorem cong {g r : ℕ} {T T' : E} {F : LFlag S r T} {F' F'' : LFlag S r T'}
    {ξ' ξ'' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)} (β₁ β₂ : S.V ≃ₗ[E] S.V)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hFC : IsFixedConv Λ g F) (hA' : AdmWit Λ g F F' ξ')
    (hA'' : AdmWit Λ g F F'' ξ'') (hP1 : IsPair Λ F F' F'' β₁ g) (hP2 : IsPair Λ F F' F'' β₂ g)
    (P : HeightOneSpectrum (𝓞 E)) (hgP : (g : 𝓞 E) ∈ P.asIdeal) (y : S.V) (hyΛ : y ∈ Λ)
    (hyo : y ∈ orth S (Xsp F')) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
      s • (β₁.symm (β₂ y) - y) ∈ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  have hPp := P.isPrime
  obtain ⟨t, ht, l, hl, hlx⟩ := iotaLift hU hFC hA' P hgP y hyΛ hyo
  set x := t • y
  have hx : x ∈ Lrep Λ F' := ⟨Λ.smul_mem t hyΛ, Submodule.smul_of_tower_mem _ t hyo⟩
  have hN' : l - x ∈ NgX Λ g F F' := Submodule.mem_sup_left (Submodule.mem_sup_left hlx)
  have h1 := (hP1.2.2.2 x hx l hl).mp hN'
  have h2 := (hP2.2.2.2 x hx l hl).mp hN'
  have hd : β₂ x - β₁ x ∈ NgX Λ g F F'' := by
    have : β₂ x - β₁ x = (l - β₁ x) - (l - β₂ x) := by abel
    rw [this]; exact Submodule.sub_mem _ h1 h2
  have hle : NgX Λ g F F'' ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
      (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F'') := by
    apply sup_le (sup_le ((le_sup_left).trans (le_locP _ _)) ?_) ((le_sup_right).trans (le_locP _ _))
    refine (XLam_le_loc hFC P hgP).trans (localization_le_localization_of_le_localization' _ ?_)
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact e_mem_loc_adm hFC hA'' P hgP a
  obtain ⟨s, hs, hsd⟩ := hle hd
  obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ := Submodule.mem_sup.mp hsd
  obtain ⟨l₁, hl₁, rfl⟩ := mem_gΛ (Λ := Λ) g hz₁
  refine ⟨s * t, fun h => ?_, ?_⟩
  · rcases hPp.mem_or_mem h with h | h
    · exact hs h
    · exact ht h
  · have key : (s * t) • (β₁.symm (β₂ y) - y) = β₁.symm (s • (β₂ x - β₁ x)) := by
      simp only [x, smulO, map_smul, map_sub, LinearEquiv.symm_apply_apply, smul_sub, map_mul,
        mul_smul]
    rw [key, ← hz, map_add, smulO, map_smul, ← smulO]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (g_mem_gΛ (Λ := Λ) g
      (symm_mem hP1.1 hl₁))) (Submodule.mem_sup_right ⟨symm_mem hP1.1 hz₂.1, ?_⟩)
    exact symm_mem_X hP1.2.1 hz₂.2

end PI.UnitaryGroupMassFormula.BetaLUniq.EigB
