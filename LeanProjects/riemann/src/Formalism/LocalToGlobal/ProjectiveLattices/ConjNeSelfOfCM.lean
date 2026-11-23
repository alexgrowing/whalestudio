import Formalism.LocalToGlobal.ProjectiveLattices.CrudeOrd
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeDiv
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} [StarRing (𝓞 E)]

def SatDir (T : CDVR) {d : ℕ} (uvec : Lt1 Dw → Fin d → T.Fr) : Prop :=
  ∀ τ : E →+* ℂ, ∃ W : Fin (Dw.mult τ) → Fin d → T.V,
    ∀ i i' : Fin (Dw.mult τ), ∑ j, uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (W i j) = if i' = i then 1 else 0

variable (Dw) in

def DomW (a : (E →+* ℂ) × ℕ → ℕ) : Prop := Crude.Dom Dw.mult (fun τ i => a (τ, i))

def crudeBd {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (D : ℕ) : ℝ :=
  (ramOverZ la : ℝ) * (D : ℝ) / ((resCharOf la : ℝ) - 1)

omit [StarRing (𝓞 E)] in
theorem conj_ne_self_of_CM (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by
  haveI := NumberField.IsCMField.isTotallyComplex E
  intro hτ
  have hc := NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_mk_iff] at hc
  exact hc hτ

theorem Crude.le_degree {σ : Type} (α : σ →₀ ℕ) (s : σ) : α s ≤ α.degree := by
  by_cases hs : s ∈ α.support
  · have hd : α.degree = ∑ i ∈ α.support, α i := rfl
    rw [hd]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) hs
  · have h0 : α s = 0 := by simpa using hs
    rw [h0]
    exact Nat.zero_le _

omit [IsCMField E] [StarRing (𝓞 E)] in
variable (Dw) in

def colP {n : ℕ} (hn : Fintype.card (Lt1 Dw) ≤ n) : Lt1 Dw → Fin n :=
  fun p => Fin.castLE hn (Fintype.equivFin (Lt1 Dw) p)

open Classical in
variable (Dw) in

def P1 (T : CDVR) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Fintype.card (Lt1 Dw) ≤ n) :
    MvPolynomial (LtN Dw n) T.Fr :=
  MvPolynomial.map (Int.castRingHom T.Fr) (Crude.Pmin Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)))

open Classical in
variable (Dw) in

def fact1 (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Fintype.card (Lt1 Dw) ≤ n) : ℕ :=
  (Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i))).prod fun _ t => t.factorial

def crudeInf {T : CDVR} {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB T.Fr d O) (h : PS T.Fr 2 d) (w0 : O)
    (k : ℕ) (uvec : Lt1 Dw → Fin d → T.Fr) (e : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  ⨅ (P : MvPolynomial (LtN Dw n) T.Fr) (_ : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n d) (_ : IsIntPS T f),
    nval T.V e (nabValN B T.Fr h w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => uvec ⟨ℓ.1, ℓ.2.1⟩) P)

private theorem ordGe_prod_lemma (T : CDVR) {n d : ℕ} {ι : Type} (φ : ι → PS T.Fr n d)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (α : ι →₀ ℕ) :
    Crude.OrdGe α.degree (α.prod fun i e => φ i ^ e) := by
  classical
  have hpow : ∀ i (e : ℕ), Crude.OrdGe e (φ i ^ e) := by
    intro i e
    induction e with
    | zero => exact Crude.cro_ordGe_zero (φ i ^ 0)
    | succ e ih =>
      rw [pow_succ]
      exact Crude.OrdGe.mul ih ((Crude.ordGe_one_iff _).2 (hφ i))
  have hd : α.degree = ∑ i ∈ α.support, α i := rfl
  rw [hd]
  unfold Finsupp.prod
  generalize α.support = s
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, Finset.prod_empty]
    exact Crude.cro_ordGe_zero _
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact Crude.OrdGe.mul (hpow a (α a)) ih

theorem crude_val {T : CDVR} {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB T.Fr d O) (h : PS T.Fr 2 d)
    (hg : B.IsCanonGauge T.Fr h) (w0 : O) (k : ℕ) (uvec : Lt1 Dw → Fin d → T.Fr) (hsat : SatDir T uvec)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n) :
    P1 Dw T a hn ∈ FFV (Dw := Dw) T a n ∧ ∃ f : PS T.Fr n d, IsIntPS T f ∧ Crude.OrdGe (DF Dw a) f ∧
      nabValN B T.Fr h w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => uvec ⟨ℓ.1, ℓ.2.1⟩) (P1 Dw T a hn) =
        (fact1 Dw a hn : T.Fr) := by
  classical
  have hβ : Function.Injective (colP Dw hn) := fun p q hpq =>
    (Fintype.equivFin (Lt1 Dw)).injective (Fin.castLE_injective hn hpq)
  set α := Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)) with hαdef
  have hdeg : α.degree = DF Dw a := by rw [hαdef, Crude.diagExp_degree]; rfl
  have hcoeff : (P1 Dw T a hn).coeff α = 1 := Crude.Pmin_coeff_diag (k := T.Fr) (hβ := hβ) (ha := ha)
  have hαmem : α ∈ (P1 Dw T a hn).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]; exact one_ne_zero
  refine ⟨?_, ?_⟩
  · show MvPolynomial.map (Int.castRingHom T.Fr) (Crude.Pmin Dw.mult n (colP Dw hn) (fun τ i => a (τ, i))) ∈
      HaO Dw.mult n T.Fr (algebraMap T.V T.Fr).range ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
    exact Crude.Pmin_mem (O := (algebraMap T.V T.Fr).range) (cc := ComplexEmbedding.conjugate)
      (isX := InPsi H) (hcc := fun τ _ => conj_ne_self_of_CM τ) (hβ := hβ) (ha := ha)

  have hsat' : ∀ τ : E →+* ℂ, ∃ W : Fin (Dw.mult τ) → Fin d → T.V, ∀ i i' : Fin (Dw.mult τ),
      ∑ j, uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (W i j) = if i' = i then 1 else 0 := hsat
  choose W hW using hsat'
  let φV : LtN Dw n → PS T.V n d := fun ℓ =>
    if (∃ i, colP Dw hn ⟨ℓ.1, i⟩ = ℓ.2.2) then ∑ j, C (W ℓ.1 ℓ.2.1 j) * X (ℓ.2.2, j) else 0
  let φ : LtN Dw n → PS T.Fr n d := fun ℓ =>
    if (∃ i, colP Dw hn ⟨ℓ.1, i⟩ = ℓ.2.2) then
      ∑ j, C (algebraMap T.V T.Fr (W ℓ.1 ℓ.2.1 j)) * X (ℓ.2.2, j) else 0
  have hmapφ : ∀ ℓ, MvPowerSeries.map (algebraMap T.V T.Fr) (φV ℓ) = φ ℓ := by
    intro ℓ
    simp only [φV, φ]
    split_ifs <;> simp [map_sum]
  have hφ0 : ∀ ℓ, constantCoeff (φ ℓ) = 0 := by
    intro ℓ
    simp only [φ]
    split_ifs <;> simp [map_sum]
  have hdual : ∀ l ∈ Crude.GoodL Dw.mult n (colP Dw hn), ∀ l',
      Crude.Lin ((fun ℓ : LtN Dw n => ℓ.2.2) l) ((fun ℓ : LtN Dw n => uvec ⟨ℓ.1, ℓ.2.1⟩) l) (φ l') =
        C (if l = l' then 1 else 0) := by
    rintro ⟨τ, i0, b⟩ ⟨i, hi⟩ ⟨τ', i', b'⟩
    simp only [φ]
    dsimp only at hi ⊢
    by_cases hg : ∃ i'', colP Dw hn ⟨τ', i''⟩ = b'
    · rw [if_pos hg, Crude.Lin_linForm]
      congr 1
      by_cases hbb : b = b'
      · subst hbb
        obtain ⟨i'', hi''⟩ := hg
        have hp : (⟨τ, i⟩ : Lt1 Dw) = ⟨τ', i''⟩ := hβ (hi.trans hi''.symm)
        obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hp
        rw [if_pos rfl, hW τ i' i0]
        by_cases h : i0 = i'
        · subst h; simp
        · rw [if_neg h, if_neg]
          intro hl
          cases hl
          exact h rfl
      · rw [if_neg hbb, if_neg]
        intro hl
        cases hl
        exact hbb rfl
    · rw [if_neg hg, if_neg]
      · simpa using Crude.div_Lin_C (n := n) b (uvec ⟨τ, i0⟩) (0 : T.Fr)
      · intro hl
        cases hl
        exact hg ⟨i, hi⟩
  obtain ⟨f, hfdef⟩ : ∃ f : PS T.Fr n d, f = MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : T.Fr)) :=
    ⟨_, rfl⟩
  have hfprod : f = α.prod fun ℓ e => φ ℓ ^ e := by
    rw [hfdef, MvPolynomial.aeval_monomial, map_one, one_mul]
  have hfint : IsIntPS T f := by
    intro m
    have hmap : f = MvPowerSeries.map (algebraMap T.V T.Fr) (α.prod fun ℓ e => φV ℓ ^ e) := by
      rw [hfprod]
      unfold Finsupp.prod
      rw [map_prod]
      simp only [map_pow, hmapφ]
    rw [hmap, MvPowerSeries.coeff_map]
    exact ⟨_, rfl⟩
  have hOrd : Crude.OrdGe (DF Dw a) f := by
    rw [hfprod, ← hdeg]
    exact ordGe_prod_lemma T φ hφ0 α
  have hPdeg : ∀ m ∈ (P1 Dw T a hn).support, m.degree = DF Dw a := fun m hm =>
    Crude.Pmin_degree (ha := ha) (m := m) (hm := hm)
  refine ⟨f, hfint, hOrd, ?_⟩
  rw [Crude.nabValN_eq_lin B h hg w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => uvec ⟨ℓ.1, ℓ.2.1⟩)
    (P1 Dw T a hn) (DF Dw a) hPdeg hOrd, Finset.sum_eq_single α]
  · rw [hfdef, Crude.linMon_aeval_monomial _ _ φ hφ0 _ hdual α α
      (fun l hl => Crude.Pmin_good (m := α) (hm := hαmem) (ℓ := l) (hℓ := hl)), if_pos rfl, hcoeff, one_mul]
    rfl
  · intro m hm hne
    rw [hfdef, Crude.linMon_aeval_monomial _ _ φ hφ0 _ hdual m α
      (fun l hl => Crude.Pmin_good (m := m) (hm := hm) (ℓ := l) (hℓ := hl)), if_neg hne, mul_zero]
  · intro hα
    exact absurd hαmem hα

theorem crude_inf {T : CDVR} {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB T.Fr d O) (h : PS T.Fr 2 d)
    (hg : B.IsCanonGauge T.Fr h) (w0 : O) (k : ℕ) (uvec : Lt1 Dw → Fin d → T.Fr) (hsat : SatDir T uvec)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n)
    {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {io : K →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) :
    crudeInf B h w0 k uvec e a n ≤ (crudeBd la (DF Dw a) : EReal) ∧
      (DF Dw a < resCharOf la → crudeInf B h w0 k uvec e a n ≤ 0) := by
  classical
  obtain ⟨hP, f, hfI, -, hval⟩ := crude_val B h hg w0 k uvec hsat a n ha hn
  have hle : crudeInf B h w0 k uvec e a n ≤ nval T.V e ((fact1 Dw a hn : ℕ) : T.Fr) := by
    unfold crudeInf
    exact iInf_le_of_le (P1 Dw T a hn) (iInf_le_of_le hP (iInf_le_of_le f
      (iInf_le_of_le hfI (by rw [hval]))))
  have hdeg : (Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i))).degree = DF Dw a := by
    rw [Crude.diagExp_degree]; rfl
  refine ⟨hle.trans ?_, fun hlt => hle.trans ?_⟩
  · have h1 := Crude.nval_factProd_le (ho := ho) (α := Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)))
    rw [hdeg] at h1
    exact h1
  · have h2 := Crude.nval_factProd_le_zero (ho := ho) (α := Crude.diagExp Dw.mult n (colP Dw hn) (fun τ i => a (τ, i)))
      (hα := fun s => lt_of_le_of_lt (Crude.le_degree _ s) (hdeg ▸ hlt))
    exact h2

end Gen

end Formalism.L2.Pj
