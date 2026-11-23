import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.CongLevel GlobalTheory.GO.ChRoot

noncomputable section

namespace GlobalTheory.Mem.LevFin

section Loc

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_int_congr {c : ℕ} (hq : (c : E) ≠ 0) {a : E} (ha : IntAt P a) :
    ∃ r : 𝓞 E, IntAt P ((c : E)⁻¹ * (a - algebraMap (𝓞 E) E r)) := by
  obtain ⟨r, s, hs, h⟩ := ha
  have hq' : ((c : ℕ) : 𝓞 E) ≠ 0 := fun h0 => hq (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have hfin : Finite (𝓞 E ⧸ Ideal.span {((c : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hq')
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => Ideal.Quotient.mk (Ideal.span {((c : ℕ) : 𝓞 E)}) (s ^ k))
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm he.symm (by omega)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  obtain ⟨t, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 he)
  have hc' := congrArg (algebraMap (𝓞 E) E) hc
  simp only [map_mul, map_natCast, map_sub, map_pow] at hc'
  refine ⟨r * s ^ d, t * r, s ^ (i + 1), fun hm => hs (P.isPrime.mem_of_pow_mem _ hm), ?_⟩
  simp only [map_mul, map_pow]
  rw [← h]
  field_simp
  linear_combination (-(algebraMap (𝓞 E) E s * a)) * hc'

theorem intAt_neg {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  simpa using (IntAt.coe P (-1)).mul ha

variable [StarRing E]

theorem finiteIndex_of_cong {n c : ℕ} (hc : (c : E) ≠ 0) (H : Subgroup (GLint E n P))
    (hH : ∀ κ : GLint E n P, (∀ x ∈ stdAt E n P, (c : E)⁻¹ • (κ.1 x - x) ∈ stdAt E n P) → κ ∈ H) : H.FiniteIndex := by
  classical
  have hq' : ((c : ℕ) : 𝓞 E) ≠ 0 := fun h0 => hc (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have hfin : Finite (𝓞 E ⧸ Ideal.span {((c : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hq')
  have he : ∀ i : Fin n, (Pi.single i 1 : Sp E n) ∈ stdAt E n P := by
    intro i
    rw [mem_stdAt']
    intro l
    rw [Pi.single_apply]
    split_ifs
    · exact intAt_one'
    · exact intAt_zero'
  choose r hr using fun (κ : GLint E n P) (i l : Fin n) =>
    exists_int_congr (P := P) hc (mem_stdAt'.1 ((κ.2 _).2 (he i)) l)
  let f : GLint E n P → Fin n → Fin n → 𝓞 E ⧸ Ideal.span {((c : ℕ) : 𝓞 E)} :=
    fun κ i l => Ideal.Quotient.mk _ (r κ i l)
  have key : ∀ a b, f a = f b → a⁻¹ * b ∈ H := by
    intro a b hab
    have h1 : ∀ i l, IntAt P ((c : E)⁻¹ * (b.1 (Pi.single i 1) l - a.1 (Pi.single i 1) l)) := by
      intro i l
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun hab i) l))
      have ht' := congrArg (algebraMap (𝓞 E) E) ht
      simp only [map_mul, map_natCast, map_sub] at ht'
      have := ((hr b i l).add (intAt_neg (hr a i l))).add (intAt_neg (IntAt.coe P t))
      convert this using 1
      field_simp
      linear_combination ht'
    refine hH _ fun x hx => ?_
    refine (a.2 _).1 ?_
    have e : a.1 ((c : E)⁻¹ • ((a⁻¹ * b).1 x - x)) = (c : E)⁻¹ • (b.1 x - a.1 x) := by
      rw [map_smul, map_sub]
      congr 2
      exact LinearEquiv.apply_symm_apply _ _
    rw [e, mem_stdAt']
    intro l
    have ex : x = ∑ i, x i • (Pi.single i 1 : Sp E n) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply]
    have e2 : ((c : E)⁻¹ • (b.1 x - a.1 x)) l =
        ∑ i, x i * ((c : E)⁻¹ * (b.1 (Pi.single i 1) l - a.1 (Pi.single i 1) l)) := by
      conv_lhs => rw [ex]
      simp only [map_sum, map_smul, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e2]
    exact Finset.sum_induction _ (IntAt P) (fun _ _ => IntAt.add) intAt_zero' fun i _ =>
      (mem_stdAt'.1 hx i).mul (h1 i l)
  have : Finite (GLint E n P ⧸ H) := by
    refine Finite.of_injective (fun z : GLint E n P ⧸ H => f z.out) fun z z' h => ?_
    rw [← z.out_eq, ← z'.out_eq]
    exact QuotientGroup.eq.2 (key _ _ h)
  exact Subgroup.finiteIndex_of_finite_quotient

omit [StarRing E] in
theorem natCast_smul_mem {N : ℕ} (L : Submodule (𝓞 E) (Sp E N)) (c : ℕ) {x : Sp E N} (hx : x ∈ L) : (c : E) • x ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx c

omit [StarRing E] in

theorem stab_of_cong {N q : ℕ} (hq : (q : E) ≠ 0) (L : Submodule (𝓞 E) (Sp E N)) (g : Sp E N ≃ₗ[E] Sp E N)
    (h1 : ∀ x ∈ L, (q : E)⁻¹ • (g x - x) ∈ L) (h2 : ∀ x ∈ L, (q : E)⁻¹ • (g⁻¹ x - x) ∈ L) : g ∈ stabL E N L := by
  have key : ∀ g : Sp E N ≃ₗ[E] Sp E N, (∀ x ∈ L, (q : E)⁻¹ • (g x - x) ∈ L) → ∀ x ∈ L, g x ∈ L := by
    intro g h x hx
    have := add_mem (natCast_smul_mem L q (h x hx)) hx
    rwa [smul_smul, mul_inv_cancel₀ hq, one_smul, sub_add_cancel] at this
  intro x
  refine ⟨fun hx => ?_, key g h1 x⟩
  have := key _ h2 _ hx
  rwa [show g⁻¹ (g x) = x from LinearEquiv.symm_apply_apply _ x] at this

theorem conj_extE_cong {n c q j : ℕ} (hq : (q : E) ≠ 0) (ex : ℕ → ℕ) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (hb : ∀ x ∈ LocE.lamY P q n c ex, h⁻¹ x ∈ LocE.lamY P q n c ex ∧ ((q : E) ^ j) • h x ∈ LocE.lamY P q n c ex)
    (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : ∀ x ∈ stdAt E n P, ((q ^ (j + 1) : ℕ) : E)⁻¹ • (κ x - x) ∈ stdAt E n P) :
    ∀ x ∈ LocE.lamY P q n c ex, (q : E)⁻¹ • ((h⁻¹ * extE c κ * h) x - x) ∈ LocE.lamY P q n c ex := by
  intro x hx
  have h1 := (hb _ (inX_mem_lamY P q c ex _ (hκ _ (resX_mem P q c ex _ (hb x hx).2)))).1
  convert h1 using 1
  have e : (h⁻¹ * extE c κ * h) x - x = h⁻¹ (Loc.inX E n c (κ (resX c (h x)) - resX c (h x))) := by
    show h⁻¹ (extE c κ (h x)) - x = _
    rw [extE_apply, map_add, show h⁻¹ (h x) = x from LinearEquiv.symm_apply_apply _ x, add_sub_cancel_left]
  rw [e]
  simp only [map_smul, ← smul_sub, smul_smul]
  congr 1
  push_cast
  field_simp
  ring

end Loc

theorem qOf_ne {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) : ((qOf P : ℕ) : X.E) ≠ 0 :=
  Nat.cast_ne_zero.2 (qOf_pos P).ne'

theorem mem_Jat {X : Fields} {Pr : Primes X} {R : Ranks} (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (g : AutY X R j)
    (hs : g ∈ stabL X.E _ (lamYat (Pr := Pr) j w))
    (hc : ∀ x ∈ lamYat (Pr := Pr) (R := R) j w, (qOf w : X.E)⁻¹ • (g x - x) ∈ lamYat (Pr := Pr) (R := R) j w) :
    g ∈ Jat (Pr := Pr) sharp j w := by
  have hq := qOf_ne w
  unfold lamYat at hs hc
  unfold Jat
  by_cases hw : w ∈ Pr.vGs
  · rw [if_pos hw] at hs hc ⊢
    split_ifs
    · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
      · exact sclLat_le w _ hq _ _ _
      · exact smul_mem_sclLat w _ hq _ _ _ x hx
      · exact bvec_mem w _ hq _ _ _
    · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
      · exact sclLat_le w _ hq _ _ _
      · exact smul_mem_sclLat w _ hq _ _ _ x hx
      · exact bvec_mem w _ hq _ _ _
  · rw [if_neg hw] at hs hc ⊢
    have hp : LocE.parL w (qOf w) (R.k + j) (R.N j) (cOf R j) = LocE.sclLat w (qOf w) (R.N j + cOf R j)
        (fun l => LocE.scE (R.N j) 0 l + if R.k + j ≤ l ∧ l < R.N j then 1 else 0) := by
      unfold LocE.parL
      congr 1
      funext l
      simp [LocE.scE]
    refine ⟨fun x => ?_, ?_⟩
    · rw [← mem_lamY_zero (q := qOf w), ← mem_lamY_zero (q := qOf w)]
      exact hs x
    · have := mem_flagU (qOf w) (LocE.lamY w (qOf w) (R.N j) (cOf R j) 0)
        (fun _ => LocE.parL w (qOf w) (R.k + j) (R.N j) (cOf R j)) (fun _ => 0) 0 {0}
        (fun s => by rw [hp]; exact sclLat_le w _ hq _ _ _)
        (fun s x hx => by rw [hp]; exact smul_mem_sclLat w _ hq _ _ _ x hx) (fun _ => zero_mem _) _ hs hc
      exact this.1 0 rfl

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem lev_finiteIndex (hL : L.Ok Ch sel mu cst G m2) (j : ℕ) (b : L.β j)
    (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) : (L.levQ j b P).H.FiniteIndex := by
  classical
  have hq := qOf_ne P.1
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  obtain ⟨h, hh⟩ : ∃ h, h = L.h j b P' := ⟨_, rfl⟩
  have hb : ∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P.1 ∧
      ((qOf P.1 : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P.1 := by
    by_cases hP : P.1 ∈ Pr.vGs
    · have hs : h ∈ stabL X.E _ (lamYat (Pr := Pr) j P.1) := hh ▸ hL.stabG j b P' hP
      intro x hx
      refine ⟨((inv_mem hs) x).2 hx, ?_⟩
      rw [← Nat.cast_pow]
      exact natCast_smul_mem _ _ ((hs x).2 hx)
    · rw [hh]
      exact hL.boundQ j b P' hP
  refine finiteIndex_of_cong (c := qOf P.1 ^ (j + 1)) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hq) _ fun κ hκ => ?_
  rw [hL.grpQ j b P, Subgroup.mem_subgroupOf]
  change κ.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 (L.h j b P')
  rw [← hh]
  refine ⟨extE _ κ.1, ⟨extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ κ.1, ?_⟩, extE_inX _ κ.1⟩
  have e : (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ.1) = h⁻¹ * extE (cOf R j) κ.1 * h := by simp
  show (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ.1) ∈ Jat (Pr := Pr) cst.sharp j P.1
  rw [e]
  have hκ' : ∀ x ∈ stdAt X.E (R.N j) P.1,
      ((qOf P.1 ^ (j + 1) : ℕ) : X.E)⁻¹ • (κ.1⁻¹ x - x) ∈ stdAt X.E (R.N j) P.1 := by
    intro x hx
    have := neg_mem (hκ _ (((inv_mem κ.2) x).2 hx))
    rwa [show κ.1 (κ.1⁻¹ x) = x from LinearEquiv.apply_symm_apply _ x, ← smul_neg, neg_sub] at this
  have h1 := conj_extE_cong hq _ h hb κ.1 hκ
  have h2 := conj_extE_cong hq _ h hb κ.1⁻¹ hκ'
  refine mem_Jat _ _ _ _ (stab_of_cong hq _ _ h1 ?_) h1
  have e2 : (h⁻¹ * extE (cOf R j) κ.1 * h)⁻¹ = h⁻¹ * extE (cOf R j) κ.1⁻¹ * h := by
    rw [← extE_inv]
    group
  rw [e2]
  exact h2

theorem root_mul {K : Type} [Field K] {a b : K} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) : IsOfFinOrder (a * b) :=
  ha.mul hb

theorem root_inv {K : Type} [Field K] {a : K} (ha : IsOfFinOrder a) : IsOfFinOrder a⁻¹ := by
  rw [isOfFinOrder_iff_pow_eq_one] at ha ⊢
  obtain ⟨k, hk, h⟩ := ha
  exact ⟨k, hk, by rw [inv_pow, h, inv_one]⟩

theorem tame_root {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
    (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : 𝓞 E ⧸ P.asIdeal) (j : ℕ) (d : ℕ → E)
    (h : ψ a * ∏ i ∈ Finset.range j, LocE.unitV (χ i) (d i) ≠ 0) :
    IsOfFinOrder (ψ a * ∏ i ∈ Finset.range j, LocE.unitV (χ i) (d i)) := by
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine root_mul ?_ ?_
  · rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨Nat.card (𝓞 E ⧸ P.asIdeal), Nat.card_pos, ?_⟩
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  · have h2 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h)
    refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => root_mul) IsOfFinOrder.one fun i hi => ?_
    rw [isOfFinOrder_iff_pow_eq_one]
    exact unitV_root _ _ (h2 i hi)

theorem intAt_n1Arg_G {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n c q : ℕ}
    (hq : (q : E) ≠ 0) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (hr : r ∈ stabL E _ (LocE.lamY P q n c fun i => i + 1)) : IntAt P ((q : E) * Loc.n1Arg r) := by
  unfold Loc.n1Arg
  rw [Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · have h1 := (hr _).2 (bvec_mem P q hq (n + c) (LocE.scE n fun i => i + 1) (n + i + 1))
    have h2 := (mem_sclLat P q _ _ _).1 h1 ⟨n + i, hi⟩
    convert h2 using 1
    have e1 : LocE.scE n (fun i => i + 1) (n + i + 1) = ((i + 2 : ℕ) : ℤ) := by
      unfold LocE.scE
      rw [if_neg (by omega)]
      congr 1
      beta_reduce
      omega
    have e2 : LocE.scE n (fun i => i + 1) (n + i) = ((i + 1 : ℕ) : ℤ) := by
      unfold LocE.scE
      rw [if_neg (by omega)]
      congr 1
      beta_reduce
      omega
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    simp only [e1, e2, zpow_natCast]
    field_simp
    ring
  · simpa using intAt_zero'

theorem lam_root_G (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (b : L.β j)
    (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (hP : P.1 ∈ Pr.vGs) (g : (L.levQ j b P).H) :
    ∃ k : ℕ, 0 < k ∧ (L.levQ j b P).lam g ^ k = 1 := by
  classical
  have hg := Subgroup.mem_subgroupOf.1 ((hL.grpQ j b P).le g.2)
  obtain ⟨r, hr, hrg⟩ := hg
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  obtain ⟨h, hh⟩ : ∃ h, h = L.h j b P' := ⟨_, rfl⟩
  have hχ : (((L.levQ j b P).lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P' (L.h j b P') r := hL.chrQ j b P g r hr hrg
  replace hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h := hh ▸ hr
  rw [← hh] at hχ
  have hs : h ∈ stabL X.E _ (lamYat (Pr := Pr) j P.1) := hh ▸ hL.stabG j b P' hP
  have hD := hL.depthG P' hP
  unfold lamYat at hs
  rw [if_pos hP] at hs
  have hκ : (MulAut.conj h⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) cst.sharp j P.1 := hr.2
  have e : (MulAut.conj h⁻¹).toMonoidHom r = h⁻¹ * r * h := by simp
  rw [e] at hκ
  have hκ' : h⁻¹ * r * h ∈ stabL X.E _ (LocE.lamY P.1 (qOf P.1) (R.N j) (cOf R j) fun i => i + 1) := by
    unfold Jat at hκ
    rw [if_pos hP] at hκ
    split_ifs at hκ
    · exact hκ.1
    · exact hκ.1
  have hr' := mul_mem (mul_mem hs hκ') (inv_mem hs)
  rw [show h * (h⁻¹ * r * h) * h⁻¹ = r by group] at hr'
  have hint : IntAt P'.1 ((qOf P'.1 : X.E) ^ cst.D P' * Loc.n1Arg r) := by
    rw [hD, pow_one]
    exact intAt_n1Arg_G (qOf_ne _) r hr'
  have h1 : IsOfFinOrder (cst.psi P' (Loc.n1Arg r)) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos (qOf_pos _) _, psi_root hL.cst_ok P' _ hint⟩
  have hne := ((L.levQ j b P).lam g).ne_zero
  have h2 : IsOfFinOrder (((L.levQ j b P).lam g : X.Kˣ) : X.K) := by
    rw [hχ] at hne ⊢
    unfold chiInv at hne ⊢
    refine root_mul (root_inv h1) ?_
    replace hne := right_ne_zero_of_mul hne
    unfold lamRow at hne ⊢
    rw [if_pos (show P'.1 ∈ Pr.vGs from hP)] at hne ⊢
    split_ifs at hne ⊢
    · exact tame_root _ _ _ _ _ hne
    · exact tame_root _ _ _ _ _ hne
  obtain ⟨k, hk, h3⟩ := isOfFinOrder_iff_pow_eq_one.1 h2
  exact ⟨k, hk, Units.ext (by rw [Units.val_pow_eq_pow_val, h3, Units.val_one])⟩

end Main

theorem levQ_finiteIndex_and_root : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ j, j < R.m → ∀ b P, (L.levQ j b P).H.FiniteIndex ∧ ∀ g, ∃ m : ℕ, 0 < m ∧ (L.levQ j b P).lam g ^ m = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 _ _ hL j hj b P
  refine ⟨lev_finiteIndex hL j b P, fun g => ?_⟩
  by_cases hP : P.1 ∈ Pr.vGs
  · exact lam_root_G hL b P hP g
  · exact lam_root hL (by have := hL.hm; omega) b P hP g

end GlobalTheory.Mem.LevFin
