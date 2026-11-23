import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ActLin

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace ExpOf

variable {R : Type} [CommRing R]

open Formalism.FG.SolveVAux in

theorem coeff_single_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (a : σ → MvPowerSeries τ R) (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (t : τ) :
    coeff (Finsupp.single t 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single t 1) (a s) := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hlow : ∀ s, Low 1 (a s) := fun s => (low_one_iff _).2 (ha s)
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun s : σ => Finsupp.single s 1))]
  · rw [Finset.sum_image (fun p _ q _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.prod_single_index (h := fun (s : σ) (e : ℕ) => a s ^ e) (pow_zero _), pow_one, smul_eq_mul]
  · intro e he
    rw [Function.mem_support] at he
    by_contra hne
    apply he
    have hz : coeff (Finsupp.single t 1) (e.prod fun s n => a s ^ n) = 0 := by
      rcases Nat.lt_or_ge e.degree 2 with hd | hd
      · rcases Nat.lt_or_ge e.degree 1 with hd1 | hd1
        · have he0 : e = 0 := by
            have : e.degree = 0 := by omega
            exact (Finsupp.degree_eq_zero_iff e).1 this
          rw [he0, Finsupp.prod_zero_index, coeff_one, if_neg]
          exact Finsupp.single_ne_zero.2 one_ne_zero
        · obtain ⟨p, rfl⟩ := degree_eq_one e (by omega)
          exact absurd (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ p))) hne
      · have hl := low_P hlow e
        exact hl _ (by rw [Finsupp.degree_single]; omega)
    rw [hz, smul_zero]

end ExpOf

def LinEigSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C : ChartAt Xo c y) (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin C.d),
    ∑ j, dLin (C.B.A.act a) i j * C.uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i

namespace ExpOf

variable {S : Type} [CommRing S]

def linPt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d n : ℕ}
    (uvec : Lt1 Dw → Fin d → S) (b : Fin n) (i : Fin d) : MvPowerSeries (Fin n × Fin (dL Dw)) S :=
  ∑ ℓ : Lt1 Dw, MvPowerSeries.C (uvec ℓ i) * MvPowerSeries.X (b, ltIdx Dw ℓ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}

theorem cc_linPt {n : ℕ} (uvec : Lt1 Dw → Fin d → S) (b : Fin n) (i : Fin d) :
    constantCoeff (linPt uvec b i) = 0 := by
  simp [linPt]

theorem subst_linPt {n m : ℕ} (uvec : Lt1 Dw → Fin d → S) (b : Fin n)
    (a : Fin n × Fin (dL Dw) → MvPowerSeries (Fin m × Fin (dL Dw)) S) (ha : HasSubst a) (i : Fin d) :
    subst a (linPt uvec b i) = ∑ ℓ : Lt1 Dw, MvPowerSeries.C (uvec ℓ i) * a (b, ltIdx Dw ℓ) := by
  rw [linPt, ← coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [map_mul, coe_substAlgHom, subst_X ha]
  congr 1
  rw [MvPowerSeries.subst_C]

def expPhi (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (j : Fin d) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  subst (fun p : Fin 1 × Fin d => linPt uvec (0 : Fin 1) p.2) (ε j)

theorem hasSubst_linPt {n : ℕ} (uvec : Lt1 Dw → Fin d → S) (b : Fin n) :
    HasSubst (fun p : Fin 1 × Fin d => linPt uvec b p.2) :=
  hasSubst_of_constantCoeff_zero fun p => cc_linPt uvec b p.2

theorem coeff_linPt (uvec : Lt1 Dw → Fin d → S) (ℓ : Lt1 Dw) (i : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1) (linPt uvec (0 : Fin 1) i) = uvec ℓ i := by
  classical
  rw [linPt, map_sum]
  simp only [coeff_C_mul, coeff_X]
  rw [Finset.sum_eq_single ℓ]
  · simp
  · intro ℓ' _ h
    rw [if_neg, mul_zero]
    intro e
    apply h
    have := Finsupp.single_left_injective one_ne_zero e
    exact ((ltIdx Dw).injective (congrArg Prod.snd this)).symm
  · simp

end ExpOf

namespace ExpOf

variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}

theorem dLin_inv (ℓ ε : Pt S 1 d) (hℓ1 : dLin ℓ = 1) (hinv : IsInvPair ε ℓ) : dLin ε = 1 := by
  have h := dLin_comp1 ℓ ε hinv.1
  rw [hinv.2.2.2, dLin_pt, hℓ1, one_mul] at h
  exact h.symm

theorem expPhi_const (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (hε : ∀ i, constantCoeff (ε i) = 0) (j : Fin d) :
    constantCoeff (expPhi uvec ε j) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_linPt uvec 0) (fun p => cc_linPt uvec 0 p.2) (hε j)

theorem expPhi_lin (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (hdε : dLin ε = 1) (ℓ : Lt1 Dw) (j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1) (expPhi uvec ε j) = uvec ℓ j := by
  classical
  rw [expPhi, coeff_single_subst (fun p : Fin 1 × Fin d => linPt uvec (0 : Fin 1) p.2)
    (fun p => cc_linPt uvec (0 : Fin 1) p.2)]
  simp only [coeff_linPt]
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  have hd : ∀ i, coeff (Finsupp.single ((0 : Fin 1), i) 1) (ε j) = if j = i then 1 else 0 := fun i => by
    have := congrFun (congrFun hdε j) i
    simpa only [dLin, Matrix.one_apply] using this
  simp only [hd, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end ExpOf

namespace ExpOf

variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}

theorem hasSubst_XX : HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
    (X ((0 : Fin 2), q.2) + X ((1 : Fin 2), q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
  hasSubst_of_constantCoeff_zero fun q => by simp

theorem hasSubst_Λ (uvec : Lt1 Dw → Fin d → S) :
    HasSubst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => cc_linPt uvec p.1 p.2

theorem subst_Λ_comp1 (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (b : Fin 2) (i : Fin d) :
    subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2) (comp1 ε (pt S (n := 2) d b) i) =
      subst (fun q : Fin 1 × Fin d => linPt uvec b q.2) (ε i) := by
  have ha : HasSubst (fun q : Fin 1 × Fin d => (![pt S (n := 2) d b] : Fin 1 → Pt S 2 d) q.1 q.2) :=
    hasSubst_of_constantCoeff_zero fun q => by
      obtain ⟨k, i⟩ := q
      fin_cases k
      simp [pt]
  rw [comp1, ev, subst_comp_subst_apply ha (hasSubst_Λ uvec)]
  congr 1
  funext q
  obtain ⟨k, i'⟩ := q
  fin_cases k
  show subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2) (X (b, i')) = _
  rw [subst_X (hasSubst_Λ uvec)]

theorem atPt_expPhi (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (b : Fin 2) (i : Fin d) :
    atPt b (expPhi uvec ε i) = subst (fun q : Fin 1 × Fin d => linPt uvec b q.2) (ε i) := by
  have hb : HasSubst (fun q : Fin 1 × Fin (dL Dw) => (X (b, q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    hasSubst_of_constantCoeff_zero fun q => by simp
  rw [atPt, expPhi, subst_comp_subst_apply (hasSubst_linPt uvec 0) hb]
  congr 1
  funext q
  rw [subst_linPt uvec 0 _ hb, linPt]

theorem expPhi_hom (G : FGLaw S d) (uvec : Lt1 Dw → Fin d → S) (ℓ ε : Pt S 1 d) (hinv : IsInvPair ε ℓ)
    (htr : transF G.F ε ℓ = pt S (n := 2) d 0 + pt S (n := 2) d 1) (j : Fin d) :
    subst (fun p : Fin 2 × Fin d => atPt p.1 (expPhi uvec ε p.2)) (G.F j) =
      subst (fun q : Fin 1 × Fin (dL Dw) =>
        (X ((0 : Fin 2), q.2) + X ((1 : Fin 2), q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) (expPhi uvec ε j) := by
  have hε0 := hinv.1
  have hℓ0 := hinv.2.1
  have hcc : ∀ (b : Fin 2) i, constantCoeff (comp1 ε (pt S (n := 2) d b) i) = 0 :=
    fun b i => cc_comp1 _ _ hε0 (cc_pt b) i
  have hccA : ∀ i, constantCoeff
      (addOf G.F (comp1 ε (pt S (n := 2) d 0)) (comp1 ε (pt S (n := 2) d 1)) i) = 0 :=
    fun i => cc_ev _ (fun k i => by fin_cases k <;> exact hcc _ i) (G.const i)
  have hΦ : addOf G.F (comp1 ε (pt S (n := 2) d 0)) (comp1 ε (pt S (n := 2) d 1)) =
      comp1 ε (pt S (n := 2) d 0 + pt S (n := 2) d 1) := by
    have h1 : comp1 ℓ (addOf G.F (comp1 ε (pt S (n := 2) d 0)) (comp1 ε (pt S (n := 2) d 1))) =
        pt S (n := 2) d 0 + pt S (n := 2) d 1 := htr
    have h2 := congrArg (comp1 ε) h1
    rw [germComp1_germComp1_eq_substitute ε ℓ _ hℓ0 hccA, hinv.2.2.1, germCompOne_identityPoint_left _ hccA] at h2
    exact h2
  have ha : HasSubst (fun p : Fin 2 × Fin d =>
      (![comp1 ε (pt S (n := 2) d 0), comp1 ε (pt S (n := 2) d 1)] : Fin 2 → Pt S 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨b, i⟩ := p
      fin_cases b <;> exact hcc _ i
  have hL : subst (fun p : Fin 2 × Fin d => atPt p.1 (expPhi uvec ε p.2)) (G.F j) =
      subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2)
        (addOf G.F (comp1 ε (pt S (n := 2) d 0)) (comp1 ε (pt S (n := 2) d 1)) j) := by
    rw [addOf, ev, subst_comp_subst_apply ha (hasSubst_Λ uvec)]
    congr 1
    funext p
    obtain ⟨b, i⟩ := p
    rw [atPt_expPhi]
    fin_cases b
    · exact (subst_Λ_comp1 uvec ε 0 i).symm
    · exact (subst_Λ_comp1 uvec ε 1 i).symm
  have hR : subst (fun q : Fin 1 × Fin (dL Dw) =>
      (X ((0 : Fin 2), q.2) + X ((1 : Fin 2), q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) (expPhi uvec ε j) =
      subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2) (comp1 ε (pt S (n := 2) d 0 + pt S (n := 2) d 1) j) := by
    have hs : HasSubst (fun q : Fin 1 × Fin d =>
        (![pt S (n := 2) d 0 + pt S (n := 2) d 1] : Fin 1 → Pt S 2 d) q.1 q.2) :=
      hasSubst_of_constantCoeff_zero fun q => by
        obtain ⟨k, i⟩ := q
        fin_cases k
        simp [pt]
    rw [expPhi, subst_comp_subst_apply (hasSubst_linPt uvec 0) hasSubst_XX, comp1, ev,
      subst_comp_subst_apply hs (hasSubst_Λ uvec)]
    congr 1
    funext q
    obtain ⟨k, i⟩ := q
    fin_cases k
    show _ = subst (fun p : Fin 2 × Fin d => linPt uvec p.1 p.2)
      (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × Fin d) S)
    rw [subst_linPt uvec 0 _ hasSubst_XX, ← coe_substAlgHom (hasSubst_Λ uvec), map_add, coe_substAlgHom,
      subst_X (hasSubst_Λ uvec), subst_X (hasSubst_Λ uvec), linPt, linPt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [mul_add]
  rw [hL, hR, hΦ]

end ExpOf

namespace ExpOf

variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}

end ExpOf

theorem isExpOf_expPhi {S : Type} [CommRing S] [Algebra ℚ S] {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {d : ℕ} (G : FGLaw S d) (uvec : Lt1 Dw → Fin d → S) (ℓ ε : Pt S 1 d)
    (hℓ1 : dLin ℓ = 1) (hinv : IsInvPair ε ℓ)
    (htr : transF G.F ε ℓ = pt S (n := 2) d 0 + pt S (n := 2) d 1) :
    IsExpOf G.F uvec (ExpOf.expPhi uvec ε) :=
  ⟨ExpOf.expPhi_const uvec ε hinv.1, fun ℓ' j => ExpOf.expPhi_lin uvec ε (ExpOf.dLin_inv ℓ ε hℓ1 hinv) ℓ' j,
    fun j => ExpOf.expPhi_hom G uvec ℓ ε hinv htr j⟩

theorem isExpOf_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    {y : FrPt Xo c S} (C : ChartAt Xo c y) :
    ∃ φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S, IsExpOf C.B.G.F C.uvec φ := by
  obtain ⟨ℓ, hℓ0, hℓ1, hadd⟩ := ReciprocityTheory.ChartRestriction.G.TB.LogPf.logSt S C.d C.B.G
  obtain ⟨ε, hinv, htr⟩ := formal_exp_law S C.d C.B.G ℓ hℓ0 hℓ1 hadd
  exact ⟨ExpOf.expPhi C.uvec ε, isExpOf_expPhi C.B.G C.uvec ℓ ε hℓ1 hinv htr⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
