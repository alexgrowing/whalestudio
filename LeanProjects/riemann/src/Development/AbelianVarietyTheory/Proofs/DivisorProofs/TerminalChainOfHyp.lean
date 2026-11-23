import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VdivLnIdFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairStatementOfHeightAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialNumeratorLinearExtension
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairTerm

section Algebra

theorem exists_monomial_eq_prod_X {σ : Type} (n : ℕ) : ∀ d : σ →₀ ℕ, d.degree = n →
    ∃ a : Fin n → σ, (monomial d (1 : ℚ)) = ∏ k, X (a k) := by
  classical
  induction n with
  | zero =>
    intro d hd
    rw [Finsupp.degree_eq_zero_iff] at hd
    subst hd
    exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro d hd
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    have hle : Finsupp.single i 1 ≤ d := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr hi
    obtain ⟨d', rfl⟩ := exists_add_of_le hle
    have hd' : d'.degree = n := by
      rw [map_add, Finsupp.degree_single] at hd
      omega
    obtain ⟨a, ha⟩ := ih d' hd'
    refine ⟨Fin.cons i a, ?_⟩
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← ha, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

theorem homog_induction {σ : Type} {n : ℕ} (q : MvPolynomial σ ℚ → Prop) (h0 : q 0)
    (hadd : ∀ a b, q a → q b → q (a + b)) (hmon : ∀ (a : ℚ) (ν : Fin n → σ), q (a • ∏ k, X (ν k)))
    (P : MvPolynomial σ ℚ) (hP : P.IsHomogeneous n) : q P := by
  classical
  rw [P.as_sum]
  refine Finset.sum_induction _ q hadd h0 fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero h)
  obtain ⟨a, ha⟩ := exists_monomial_eq_prod_X n d hdeg
  have h1 : monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℚ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h1, ha]
  exact hmon _ _

theorem numL_prod {A : Type} (num : Multiset A → ℝ) (d : ℕ) (M : Multiset A) (hM : Multiset.card M = d) :
    numL num d (M.map X).prod = num M := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, Finsupp.toMultiset m = M := ⟨Multiset.toFinsupp M, Multiset.toFinsupp_toMultiset M⟩
  rw [GlobalTheory.NumLRename.prod_map_X_toMultiset, GlobalTheory.NumLRename.numL_monomial, one_mul, if_pos]
  rw [← hM, Finsupp.card_toMultiset, Finsupp.degree, Finsupp.sum]; rfl

theorem isHomogeneous_aeval_of_weighted {σ τ : Type} (w : σ → ℕ) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ s, (f s).IsHomogeneous (w s)) {m : ℕ} {G : MvPolynomial σ ℚ} (hG : G.IsWeightedHomogeneous w m) :
    (aeval f G).IsHomogeneous m := by
  classical
  rw [G.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun d hd => ?_
  have h := hG (mem_support_iff.1 hd)
  rw [aeval_monomial, ← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod, ← zero_add (∑ _ ∈ _, _)]
  refine IsHomogeneous.mul (isHomogeneous_C _ _) (IsHomogeneous.prod _ _ _ fun s _ => ?_)
  simpa [mul_comm] using (hf s).pow (d s)

variable {L A Cp ι : Type} [Fintype Cp] [Fintype ι]

theorem pair_ext (num : Cp → Multiset A → ℝ) (sym : Bool × L → A) (d : ℕ) (Z : ι → ITh)
    (cl : ∀ la, Bool × L → (Z la).Ch) (Dv : ∀ la, (Z la).VDiv) (lg : ℝ) (w cv : ι → ℝ) (l : L)
    (h : ∀ ν : Fin d → Bool × L, ∑ c, (num c (sym (false, l) ::ₘ Finset.univ.val.map fun i => sym (ν i)) -
      num c (sym (true, l) ::ₘ Finset.univ.val.map fun i => sym (ν i))) =
      lg * ∑ la, w la * ((((Z la).capDeg (Dv la) (∏ i, cl la (ν i)) : ℚ) : ℝ) / cv la))
    (P : MvPolynomial (Bool × L) ℚ) (hP : P.IsHomogeneous d) :
    ∑ c, numL (num c) (d + 1) (rename sym (toR ((X (false, l) - X (true, l)) * P))) =
      lg * ∑ la, w la * ((((Z la).capDeg (Dv la) (aeval (cl la) P) : ℚ) : ℝ) / cv la) := by
  refine homog_induction (fun P => ∑ c, numL (num c) (d + 1) (rename sym (toR ((X (false, l) - X (true, l)) * P))) =
      lg * ∑ la, w la * ((((Z la).capDeg (Dv la) (aeval (cl la) P) : ℚ) : ℝ) / cv la)) ?_ ?_ ?_ P hP
  · simp [toR]
  · intro a b ha hb
    simp only [toR, mul_add, map_add, Finset.sum_add_distrib, Rat.cast_add, add_div] at ha hb ⊢
    rw [ha, hb]
  · intro a ν
    have e (b : Bool) (c : Cp) : numL (num c) (d + 1) (rename sym (toR (X (b, l) * ∏ i, X (ν i)))) =
        num c (sym (b, l) ::ₘ Finset.univ.val.map fun i => sym (ν i)) := by
      rw [← numL_prod (num c) (d + 1) _ (by simp)]
      congr 1
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_map]
      simp only [toR, map_mul, map_prod, map_X, rename_X]
      rfl
    have e' (c : Cp) : numL (num c) (d + 1) (rename sym (toR ((X (false, l) - X (true, l)) * a • ∏ i, X (ν i)))) =
        (a : ℝ) * (num c (sym (false, l) ::ₘ Finset.univ.val.map fun i => sym (ν i)) -
          num c (sym (true, l) ::ₘ Finset.univ.val.map fun i => sym (ν i))) := by
      rw [← e, ← e, ← map_sub, ← smul_eq_mul (a : ℝ), ← map_smul]
      congr 1
      simp only [toR, smul_eq_C_mul, map_mul, map_sub, map_C, rename_C, eq_ratCast]
      ring
    simp only [e', ← Finset.mul_sum, h, map_smul, map_prod, aeval_X, smul_eq_mul, Rat.cast_mul]
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun la _ => by ring

variable {Tau : Type} [Fintype Tau] {N g : ℕ}

def evL (rt : Rt Tau N → L) (wl : Fin g ⊕ Fin g → L) : MvPolynomial (Vm Tau N) ℚ →ₐ[ℚ] MvPolynomial (Bool × L) ℚ :=
  aeval fun v => match v with
    | Sum.inl (b, x) => X (b, rt x)
    | Sum.inr (b, k) => C ((k.factorial : ℚ)⁻¹) * ∑ l, X (b, wl l) ^ k

theorem evL_homog (rt : Rt Tau N → L) (wl : Fin g ⊕ Fin g → L) {m : ℕ} {G : MvPolynomial (Vm Tau N) ℚ}
    (hG : G.IsWeightedHomogeneous (wt Tau N) m) : (evL rt wl G).IsHomogeneous m := by
  refine isHomogeneous_aeval_of_weighted _ _ ?_ hG
  rintro (⟨b, x⟩ | ⟨b, k⟩)
  · exact isHomogeneous_X _ _
  · have := (isHomogeneous_C (Bool × L) ((k.factorial : ℚ)⁻¹)).mul
      (IsHomogeneous.sum Finset.univ (fun l => (X (b, wl l) : MvPolynomial (Bool × L) ℚ) ^ k) k
        fun l _ => isHomogeneous_X_pow _ _)
    rwa [zero_add] at this

def gk (k : ℕ) (l : L) : MvPolynomial (Bool × L) ℚ :=
  ∑ a ∈ Finset.range k, X (false, l) ^ a * X (true, l) ^ (k - 1 - a)

theorem gk_homog (k : ℕ) (l : L) : (gk k l).IsHomogeneous (k - 1) := by
  refine IsHomogeneous.sum _ _ _ fun a ha => ?_
  have h := (isHomogeneous_X_pow (R := ℚ) ((false, l) : Bool × L) a).mul (isHomogeneous_X_pow (true, l) (k - 1 - a))
  have := Finset.mem_range.1 ha
  rwa [show a + (k - 1 - a) = k - 1 by omega] at h

theorem evL_dCh (rt : Rt Tau N → L) (wl : Fin g ⊕ Fin g → L) (k : ℕ) (G : MvPolynomial (Vm Tau N) ℚ) :
    evL rt wl ((X (Sum.inr (false, k)) - X (Sum.inr (true, k))) * G) =
      ∑ l, (X (false, wl l) - X (true, wl l)) * ((k.factorial : ℚ)⁻¹ • (gk k (wl l) * evL rt wl G)) := by
  rw [map_mul, map_sub]
  simp only [evL, aeval_X]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← geom_sum₂_mul, smul_eq_C_mul, gk]
  ring

theorem arMix_dCh (I : ArIn Tau N g Cp) (Sx : Finset ℕ) (R : ℝ) (q : ℕ) (sym : ∀ c, Bool × L → I.A c)
    (rt : Rt Tau N → L) (wl : Fin g ⊕ Fin g → L)
    (h₁ : ∀ c b x, sym c (b, rt x) = I.root (Function.update (ArIn.ind Sx) q b) R x c)
    (h₂ : ∀ c b l, sym c (b, wl l) = I.whole (Function.update (ArIn.ind Sx) q b) R l c) (k : ℕ)
    (G : MvPolynomial (Vm Tau N) ℚ) :
    I.arMix Sx R q (dCh Tau N k * toR G) = ∑ c, numL (I.num c) (dimFl Tau N + 1)
      (rename (sym c) (toR (evL rt wl ((X (Sum.inr (false, k)) - X (Sum.inr (true, k))) * G)))) := by
  have e : dCh Tau N k * toR G = toR ((X (Sum.inr (false, k)) - X (Sum.inr (true, k))) * G) := by
    simp [dCh, toR]
  have e' (c : Cp) (G : MvPolynomial (Vm Tau N) ℚ) :
      I.mixEv Sx R q c (toR G) = rename (sym c) (toR (evL rt wl G)) := by
    induction G using MvPolynomial.induction_on with
    | C a => simp [toR, evL, ArIn.mixEv]
    | add P Q hP hQ =>
      simp only [toR, map_add] at hP hQ ⊢
      rw [hP, hQ]
    | mul_X P v hP =>
      simp only [toR, map_mul, map_X] at hP ⊢
      rw [hP]
      congr 1
      rcases v with ⟨b, x⟩ | ⟨b, k⟩
      · simp [evL, ArIn.mixEv, h₁]
      · simp only [evL, ArIn.mixEv, aeval_X, map_X, rename_X, map_mul, map_C, rename_C, map_sum, map_pow, h₂, eq_ratCast,
          Rat.cast_inv, Rat.cast_natCast]
  rw [e, ArIn.arMix, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun c _ => congrArg (numL _ _) (e' c _)

end Algebra

section Whole

variable {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {L A Cp ι : Type} [Fintype Cp] [Fintype ι]

theorem whole_ext {rk : ι → Emb D p → ℕ} (M : ∀ la, DV.Mdl D p N (rk la))
    (rt' : ∀ la, Bool × Rt D.what₂.Tau N → (M la).Z.LB) (num : Cp → Multiset A → ℝ) (sym : Bool × L → A) (d : ℕ)
    (rt : Rt D.what₂.Tau N → L) (wl : Fin (D.R.f * N) ⊕ Fin (D.R.f * N) → L)
    (cl : ∀ la, Bool × L → (M la).Z.Ch) (Dv : ∀ la, L → (M la).Z.VDiv) (lg : ℝ) (w : ι → ℝ)
    (h : ∀ (l : L) (ν : Fin d → Bool × L), ∑ c, (num c (sym (false, l) ::ₘ Finset.univ.val.map fun i => sym (ν i)) -
      num c (sym (true, l) ::ₘ Finset.univ.val.map fun i => sym (ν i))) =
      lg * ∑ la, w la * ((((M la).Z.capDeg (Dv la l) (∏ i, cl la (ν i)) : ℚ) : ℝ) / ((M la).cov : ℝ)))
    (hrt : ∀ la b x, cl la (b, rt x) = (M la).Z.c1 (rt' la (b, x)))
    (hl : ∀ la i, cl la (false, wl (.inl i)) = (M la).Z.c1 ((M la).lieW.x i) ∧
      cl la (true, wl (.inl i)) = (M la).Z.c1 ((M la).lieW.x' i) ∧ Dv la (wl (.inl i)) = (M la).lieW.Dv i)
    (ho : ∀ la i, cl la (false, wl (.inr i)) = (M la).Z.c1 ((M la).omW.x i) ∧
      cl la (true, wl (.inr i)) = (M la).Z.c1 ((M la).omW.x' i) ∧ Dv la (wl (.inr i)) = (M la).omW.Dv i)
    (k m : ℕ) (hk : 1 ≤ k) (hm : m + k = d + 1) (G : MvPolynomial (Vm D.what₂.Tau N) ℚ)
    (hG : G.IsWeightedHomogeneous (wt D.what₂.Tau N) m) :
    ∑ c, numL (num c) (d + 1) (rename sym (toR (evL rt wl ((X (Sum.inr (false, k)) - X (Sum.inr (true, k))) * G)))) =
      lg * ∑ la, w la * ((chk (M la).lieW k (evC (M la) (rt' la) G) + chk (M la).omW k (evC (M la) (rt' la) G)) /
        ((M la).cov : ℝ)) := by
  have hev (la : ι) : aeval (cl la) (evL rt wl G) = evC (M la) (rt' la) G := by
    have : (aeval (cl la)).comp (evL rt wl) = (aeval (M la).Z.c1).comp (evV (M la) (rt' la)) := by
      refine MvPolynomial.algHom_ext ?_
      rintro (⟨b, x⟩ | ⟨_ | _, k⟩)
      · simp [evL, evV, hrt]
      · simp [evL, evV, Fintype.sum_sum_type, fun i => (hl la i).1, fun i => (ho la i).1]
      · simp [evL, evV, Fintype.sum_sum_type, fun i => (hl la i).2.1, fun i => (ho la i).2.1]
    exact congrArg (fun f => f G) this
  have hgk (la : ι) (l : L) : aeval (cl la) (gk k l) = Gk (M la).Z k (cl la (false, l)) (cl la (true, l)) := by
    simp [gk, Gk]
  have key (l : L) := pair_ext num sym d (fun la => (M la).Z) cl (fun la => Dv la l) lg w (fun la => ((M la).cov : ℝ)) l
    (h l) ((k.factorial : ℚ)⁻¹ • (gk k l * evL rt wl G)) (by
      rw [smul_eq_C_mul]
      have := ((gk_homog k l).mul (evL_homog rt wl hG)).C_mul ((k.factorial : ℚ)⁻¹)
      rwa [show k - 1 + m = d by omega] at this)
  rw [evL_dCh]
  simp only [toR, map_sum] at key ⊢
  rw [Finset.sum_comm]
  simp only [key]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun la _ => ?_
  rw [← Finset.mul_sum, ← Finset.sum_div]
  congr 2
  simp only [map_smul, map_mul, hev, hgk, Fintype.sum_sum_type, fun i => (hl la i).1, fun i => (ho la i).1,
    fun i => (hl la i).2.1, fun i => (ho la i).2.1, fun i => (hl la i).2.2, fun i => (ho la i).2.2, chk, ck,
    smul_eq_mul, Rat.cast_mul, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.sum_div]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

end Whole

section Signed

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j)

def rootLn (x : Rt D.what₂.Tau N) : Ln S.Dw :=
  if h : (x.2 : ℕ) < S.Dw.p then (false, ⟨.inl (tauEmb D x.1, x.2), by
    have e : S.Dw.mult (tauEmb D x.1) = S.Dw.p := by rw [Datum.mult, if_pos (A.cm x.1)]
    simp only [letterOf]
    rw [dif_pos (by omega)]
    rfl⟩)
  else (true, ⟨.inl (conjEmb (tauEmb D x.1), S.Dw.p + S.Dw.q - 1 - x.2), by
    have e : S.Dw.mult (tauEmb D x.1) = S.Dw.p := by rw [Datum.mult, if_pos (A.cm x.1)]
    have e' := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (tauEmb D x.1)
    have h₂ := S.rank_eq
    have := x.2.2
    simp only [letterOf]
    rw [dif_pos (by omega)]
    rfl⟩)

def wholeLn : Fin (D.R.f * N) ⊕ Fin (D.R.f * N) → Ln S.Dw
  | .inl k => (false, ⟨.inr k, by rw [letterOf_whole]; rfl⟩)
  | .inr k => (true, ⟨.inr k.rev, by rw [letterOf_whole]; rfl⟩)

theorem lnSym_rootLn (a : ℕ → Bool) (R : Option ℝ) (x : Rt D.what₂.Tau N) :
    lnSym a R (rootLn S x) = rootSym S.Dw a R (tauEmb D x.1) x.2 := by
  unfold rootLn rootSym
  split_ifs <;> rfl

theorem lnSym_wholeLn (a : ℕ → Bool) (R : Option ℝ) (l : Fin (D.R.f * N) ⊕ Fin (D.R.f * N)) :
    lnSym a R (wholeLn S l) = wholeSym a R l := by
  rcases l with k | k <;> rfl

variable {S} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : DV.KW p →+* ℂ)

theorem lnLB_rootLn (b : Bool) (x : Rt D.what₂.Tau N) : lnLB z b (rootLn S x) = rootOf z jc (b, x) := by
  unfold rootLn rootOf admitted.rootLB
  split_ifs
  · exact lnLB_false z b _
  · exact lnLB_true z b _

end Signed

theorem termWSt_of_pairSt (hP : PairSt) : TermWSt := by
  intro D O hO p _
  classical
  choose jc hjc hnu using fun la : Formalism.L2.Geo.PlL D p => AdmTest.exists_placeW_nonunit D p la
  choose z _ using fun la => admEx O.S O.κ p Fact.out (placeW D p la (jc la)) (hnu la) 3 (one_add_lt_three Fact.out)
  letI := Formalism.L2.Geo.finPl D p
  refine ⟨Formalism.L2.Geo.PlL D p, Formalism.L2.Geo.finPl D p, Formalism.L2.Geo.wtL D p, fun la => placeW D p la (jc la), hnu, jc, z,
    fun la => (AdmTest.placeW_spec (hjc la)).2, Formalism.L2.Geo.wtL_sum D p, ?_⟩
  intro Sx R hR k m hk hm G hG
  have key := whole_ext (fun la => mdlOf (z la) (jc la)) (fun la => rootOf (z la) (jc la))
    (A := Sym D.host.E →₀ ℤ) (arIn O.s O.Φ O.met.hm).num
    (fun x : Bool × Ln O.S.Dw => lnSym (Function.update (ArIn.ind Sx) p x.1) (some R) x.2) (dimFl D.what₂.Tau O.N)
    (rootLn O.S) (wholeLn O.S) (fun la x => (lnLB (z la) x.1 x.2).c1)
    (fun la l => vdiv Fact.out (hnu la) _ _ _ (lnId (z la) Fact.out (hnu la) l)) (Real.log p) (Formalism.L2.Geo.wtL D p)
    (hP D O hO p _ hnu (fun la => (AdmTest.placeW_spec (hjc la)).1) z Sx R hR)
    (fun la b x => congrArg FinLB.c1 (lnLB_rootLn (z la) (jc la) b x))
    (fun la i => ⟨congrArg FinLB.c1 ((lnLB_false _ _ _).trans (mdlOf_lieW (z la) (jc la) i).1.symm),
      congrArg FinLB.c1 ((lnLB_false _ _ _).trans (mdlOf_lieW (z la) (jc la) i).2.symm),
      vdiv_lnId_false (z la) _ _ _ _ (letterOf_whole O.S i)⟩)
    (fun la i => ⟨congrArg FinLB.c1 ((lnLB_true _ _ _).trans (mdlOf_omW (z la) (jc la) i).1.symm),
      congrArg FinLB.c1 ((lnLB_true _ _ _).trans (mdlOf_omW (z la) (jc la) i).2.symm),
      (vdiv_lnId_true (z la) _ _ _ _ (letterOf_whole O.S i.rev)).trans (mdlOf_omW_Dv (z la) (jc la) i).symm⟩)
    k m hk hm G hG
  refine Eq.trans ?_ key
  exact arMix_dCh (arIn O.s O.Φ O.met.hm) Sx R p
    (fun _ (x : Bool × Ln O.S.Dw) => lnSym (Function.update (ArIn.ind Sx) p x.1) (some R) x.2) (rootLn O.S) (wholeLn O.S)
    (fun _ b x => lnSym_rootLn O.S _ _ x) (fun _ b l => lnSym_wholeLn O.S _ _ l) k G

theorem termWSt_holds : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
    GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd → TermWSt :=
  fun h2 hH hA _ _ => termWSt_of_pairSt (GlobalTheory.T.pair_statement_of_height_alteration h2 hH hA)

end GlobalTheory.PairTerm

end
