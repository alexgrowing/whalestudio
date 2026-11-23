import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootLetterInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedMetricArithmeticFunctionShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFlagWholeSymbolMultiple

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ConstLat GlobalTheory.ArInt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open GlobalTheory.ShFam.Pad.LieGen
open scoped Classical

namespace GlobalTheory.EigWhole.Assemble

section General

def sgnSub (ι : Type) : MvPolynomial (ι ⊕ ι) ℝ →ₐ[ℝ] MvPolynomial ι ℝ := aeval (Sum.elim X fun i => -X i)

theorem isArFun_dual (hI : ArIso) {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {p : Z ⟶ Sp k}
    {D : ℕ} (hX : IsArithVar p D) {ι : Type} [Fintype ι] (L : ι → HermLB p) {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun L D Φ) : IsArFun (Sum.elim L fun i => (L i).dual) D (Φ ∘ₗ (sgnSub ι).toLinearMap) := by
  let n : ι ⊕ ι → ι → ℤ := Sum.elim (fun j i => if i = j then 1 else 0) fun j i => if i = j then -1 else 0
  have iso : ∀ j, (comb L (n j)).Isometric (Sum.elim L (fun i => (L i).dual) j) := fun j => by
    refine HermLB.icls_eq_iff.1 ?_
    rw [GlobalTheory.ArInt.icls_comb]
    rcases j with j | j
    · simp [n, ite_smul]
    · simp [n, ite_smul, HermLB.icls_dual]
  have h := ((hI k Z p D hX).2 ι L Φ hΦ).2.2 (ι ⊕ ι) _ n iso
  have e : (aeval fun j => lin fun i => (n j i : ℝ) : MvPolynomial (ι ⊕ ι) ℝ →ₐ[ℝ] MvPolynomial ι ℝ) = sgnSub ι := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rcases j with j | j <;> simp [lin, n, sgnSub, apply_ite]
  rwa [e] at h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem adlOf_eq {C : GlobalTheory.TrueGeo.CxSt F} (hm : Mets Y C) {w w' : Sym E →₀ ℤ} (h : expo Dw w' = expo Dw w)
    (h' : parOf w' = parOf w) : adlOf Y hm w' = { adlOf Y hm w with lg := (adlOf Y hm w').lg } := by
  have key (n n' : Pad.Letter Dw → ℤ) (h : n = n') (r r' : Option ℝ) (h' : r = r') (lg) :
      (⟨divOf Y n, 1, fun σ => hm r σ n, 0, lg⟩ : GlobalTheory.TrueGeo.Adl C Y.Y) = ⟨divOf Y n', 1, fun σ => hm r' σ n', 0, lg⟩ := by
    rw [h, h']
  exact key _ _ h _ _ h' _

theorem lgOf_neg_congr {w w' : Sym E →₀ ℤ} (h : expo Dw w = expo Dw w') (v : HeightOneSpectrum (𝓞 F))
    (ε : GlobalTheory.TrueGeo.Ext v) (y : GlobalTheory.TrueGeo.AlgPt Y.Y) (hl : lgOf Y w v ε y = lgOf Y w' v ε y) :
    lgOf Y (-w) v ε y = lgOf Y (-w') v ε y := by
  rw [GlobalTheory.CombInd.DualComb.lgOf_neg, GlobalTheory.CombInd.DualComb.lgOf_neg, hl, GlobalTheory.CombInd.DualComb.expo_neg,
    GlobalTheory.CombInd.DualComb.expo_neg, h]

omit [NumberField E] [IsCMField E] in

theorem parOf_single' (a : Sym E) {n : ℤ} (hn : n ≠ 0) : parOf (Finsupp.single a n) = a.2.1 := by
  have h : (Finsupp.single a n).support.Nonempty := by simp [Finsupp.support_single_ne_zero _ hn]
  rw [parOf, dif_pos h, Finset.mem_singleton.1 (Finsupp.support_single_subset h.choose_spec)]

end General

variable {D : D7} (O : Setup D)

theorem eigAt_eq (a : ℕ → Bool) (R : Option ℝ) (s : ℤ) (k : Fin (D.R.f * O.N)) :
    eigAt O.S.Dw a R s k = Finsupp.single (a, R, .inl ((rootLetter O.S (rootEquiv O.S k)).1,
      ((rootLetter O.S (rootEquiv O.S k)).2 : ℕ))) s := by
  have h : (letters O.S.Dw)[(k : ℕ)]? = some (rootLetter O.S (rootEquiv O.S k)) := letterOf_rootEquiv O.S k
  unfold eigAt
  rw [h]

theorem rootSym_eq (a : ℕ → Bool) (R : Option ℝ) (r : DV.Rt D.what₂.Tau O.N) :
    rootSym O.S.Dw a R (DV.tauEmb D r.1) r.2 = Finsupp.single (a, R, .inl ((rootLetter O.S r).1,
      ((rootLetter O.S r).2 : ℕ))) (if (r.2 : ℕ) < O.j then 1 else -1) := by
  have hp := O.S.p_eq
  have hq := O.S.rank_eq
  unfold rootSym rootLetter
  by_cases hi : (r.2 : ℕ) < O.j
  · rw [if_pos (by omega), dif_pos hi, if_pos hi]
  · rw [if_neg (by omega), dif_neg hi, if_neg hi]
    have : O.S.Dw.p + O.S.Dw.q = O.N := by omega
    rw [this]

def rootAt : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N) → DV.Rt D.what₂.Tau O.N :=
  Sum.elim (rootEquiv O.S) fun k => rootEquiv O.S k.rev

def eigVar (i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) : Var O ⊕ Var O :=
  if (((rootAt O i).2 : ℕ) < O.j ↔ i.isLeft) then .inl (.inl (rootAt O i)) else .inr (.inl (rootAt O i))

def famD (T : Finset ℕ) (R : ℝ) : Var O ⊕ Var O → Sym D.host.E →₀ ℤ := Sum.elim (fam O T R) fun i => -fam O T R i

theorem famD_eigVar (T : Finset ℕ) (R : ℝ) (i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) :
    famD O T R (eigVar O i) = eigSym O.S.Dw (ArIn.ind T) (some R) i := by
  unfold eigVar
  rcases i with k | k
  · rw [eigSym_inl, eigAt_eq]
    by_cases h : ((rootEquiv O.S k).2 : ℕ) < O.j <;> simp [rootAt, h, famD, fam, rootSym_eq]
  · rw [eigSym_inr, eigAt_eq]
    by_cases h : ((rootEquiv O.S k.rev).2 : ℕ) < O.j <;> simp [rootAt, h, famD, fam, rootSym_eq]

theorem sum_sq_eigVar : sgnSub (Var O) (∑ i, X (eigVar O i) ^ 2) = 2 * ∑ x, X (Sum.inl x) ^ 2 := by
  have h (i) : sgnSub (Var O) (X (eigVar O i) ^ 2) = X (Sum.inl (rootAt O i)) ^ 2 := by
    unfold eigVar
    split_ifs <;> simp [sgnSub]
  rw [map_sum, Finset.sum_congr rfl fun i _ => h i, Fintype.sum_sum_type, two_mul]
  congr 1
  · exact Equiv.sum_comp (rootEquiv O.S) fun x => (X (Sum.inl x) ^ 2 : MvPolynomial (Var O) ℝ)
  · exact Equiv.sum_comp (Fin.revPerm.trans (rootEquiv O.S)) fun x => (X (Sum.inl x) ^ 2 : MvPolynomial (Var O) ℝ)

theorem parOf_eigSym (a : ℕ → Bool) (R : Option ℝ) (i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) :
    parOf (eigSym O.S.Dw a R i) = parOf (wholeSym (E := D.host.E) a R i) := by
  rcases i with k | k
  · rw [eigSym_inl, eigAt_eq, wholeSym, parOf_single' _ one_ne_zero, parOf_single' _ one_ne_zero]
  · rw [eigSym_inr, eigAt_eq, wholeSym, parOf_single' _ (by simp), parOf_single' _ (by simp)]

theorem lgOf_eigSym {T : Finset ℕ} {R : ℝ} {c : O.s.Comp} (hA : AwayAgree O T R c)
    (i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ε : GlobalTheory.TrueGeo.Ext v)
    (y : GlobalTheory.TrueGeo.AlgPt (O.var c)) (hv : ¬ resP v ∣ (NumberField.discr D.host.E).natAbs) :
    lgOf (O.Φ.C c) (wholeSym (ArIn.ind T) (some R) i) v ε y =
      lgOf (O.Φ.C c) (eigSym O.S.Dw (ArIn.ind T) (some R) i) v ε y := by
  have key (k : Fin (D.R.f * O.N)) : lgOf (O.Φ.C c) (wholeSym (ArIn.ind T) (some R) (.inl k : _ ⊕ Fin _)) v ε y =
      lgOf (O.Φ.C c) (eigSym O.S.Dw (ArIn.ind T) (some R) (.inl k : _ ⊕ Fin _)) v ε y := by
    rw [eigSym_inl, eigAt_eq]
    exact hA k _ (letterOf_rootEquiv O.S k) v ε y hv
  rcases i with k | k
  · exact key k
  · have h := lgOf_neg_congr (O.Φ.C c) (expo_eigSym O.S.Dw _ _ _).symm v ε y (key k.rev)
    rw [eigSym_inl, eigAt_eq, wholeSym, ← Finsupp.single_neg, ← Finsupp.single_neg] at h
    rw [eigSym_inr, eigAt_eq]
    exact h

theorem fam_par (T : Finset ℕ) (R : ℝ) (i : Var O) : ∀ a ∈ (fam O T R i).support, a.2.1 = some R := by
  intro a ha
  rcases i with x | k | k
  · rw [fam, rootSym_eq] at ha
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset ha)]
  · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset ha)]
  · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset ha)]

def wholeVar (i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) : Var O ⊕ Var O := .inl (.inr i)

theorem sgnSub_diff : sgnSub (Var O)
    ((∑ a : Fin (D.R.f * O.N + D.R.f * O.N), X (wholeVar O (finSumFinEquiv.symm a)) ^ 2 -
      ∑ a : Fin (D.R.f * O.N + D.R.f * O.N), X (eigVar O (finSumFinEquiv.symm a)) ^ 2) *
      rename Sum.inl (C (1 / 2 : ℝ) * rename Sum.inl (curveCl D.what₂.Tau O.N O.j))) = diffPol O := by
  have e₁ (Q : MvPolynomial (Var O) ℝ) : sgnSub (Var O) (rename Sum.inl Q) = Q := by
    rw [sgnSub, aeval_rename, Sum.elim_comp_inl, aeval_X_left_apply]
  have e₂ := Equiv.sum_comp (finSumFinEquiv (m := D.R.f * O.N) (n := D.R.f * O.N)).symm
    fun i => (X (eigVar O i) ^ 2 : MvPolynomial (Var O ⊕ Var O) ℝ)
  have e₃ := Equiv.sum_comp (finSumFinEquiv (m := D.R.f * O.N) (n := D.R.f * O.N)).symm
    fun i => (X (wholeVar O i) ^ 2 : MvPolynomial (Var O ⊕ Var O) ℝ)
  have e₄ : sgnSub (Var O) (∑ i, X (wholeVar O i) ^ 2) = ∑ i, X (Sum.inr i) ^ 2 := by
    simp only [map_sum, map_pow, sgnSub, wholeVar, aeval_X, Sum.elim_inl]
  have e₅ : (C (1 / 2 : ℝ) : MvPolynomial (Var O) ℝ) * 2 = 1 := by
    rw [show (2 : MvPolynomial (Var O) ℝ) = C 2 from rfl, ← C_mul]
    norm_num
  rw [e₂, e₃, map_mul, e₁, map_sub, sum_sq_eigVar, e₄, diffPol]
  linear_combination (-(∑ x, X (Sum.inl x) ^ 2) * rename Sum.inl (curveCl D.what₂.Tau O.N O.j)) * e₅

theorem mem_setB (B : ℝ) {p : ℕ} (hp : p ∈ (NumberField.discr D.host.E).natAbs.primeFactors) : p ∈ Pad.setB O.κ B := by
  have hd : (NumberField.discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  have hM : O.κ.l.M' ≠ 0 := (Nat.lcm_pos (lt_of_lt_of_le (by norm_num) O.κ.l.three_le) O.κ.l.A_pos).ne'
  exact Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp,
    ((Nat.dvd_of_mem_primeFactors hp).mul_left 2).mul_right _, mul_ne_zero (mul_ne_zero two_ne_zero hd) hM⟩)

def adlD (T : Finset ℕ) (R : ℝ) (c : O.s.Comp) (i : Var O ⊕ Var O) :
    GlobalTheory.TrueGeo.Adl (GlobalTheory.TrueGeo.cxSt D.what₂.LL) (O.var c) := adlOf (O.Φ.C c) (O.met.hm c) (famD O T R i)

theorem adlD_eigVar (T : Finset ℕ) (R : ℝ) (c : O.s.Comp) (i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) :
    adlD O T R c (eigVar O i) = adlOf (O.Φ.C c) (O.met.hm c) (eigSym O.S.Dw (ArIn.ind T) (some R) i) := by
  rw [adlD, famD_eigVar]

theorem adlD_wholeVar (T : Finset ℕ) (R : ℝ) (c : O.s.Comp) (i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) :
    adlD O T R c (wholeVar O i) = adlOf (O.Φ.C c) (O.met.hm c) (wholeSym (ArIn.ind T) (some R) i) := rfl

theorem induced_adlD (hO : O.Core) (T : Finset ℕ) (R : ℝ) (c : O.s.Comp) (M : GlobalTheory.TrueGeo.Model (O.var c))
    (L : Var O → HermLB M.p) (m : ℕ+) (hI : ∀ i, (adlOf (O.Φ.C c) (O.met.hm c) (fam O T R i)).Induced M (L i) m 0) (i) :
    (adlD O T R c i).Induced M (Sum.elim L (fun i => (L i).dual) i) m 0 := by
  obtain ⟨x, P, hW⟩ := hO
  rcases i with i | i
  · exact hI i
  · have h := hI i
    unfold adlD
    rw [hW.hm_eq] at h ⊢
    exact GlobalTheory.CombInd.DualComb.induced_neg D O.A O.N O.j O.S O.κ O.s x O.Φ c M m R _ _ (fam_par O T R i) h

theorem adlD_eigVar_eq (T : Finset ℕ) (R : ℝ) (c : O.s.Comp) (i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) :
    adlD O T R c (eigVar O i) = { adlD O T R c (wholeVar O i) with lg := (adlD O T R c (eigVar O i)).lg } := by
  rw [adlD_eigVar, adlD_wholeVar]
  exact adlOf_eq _ _ (expo_eigSym _ _ _ _) (parOf_eigSym O _ _ _)

end GlobalTheory.EigWhole.Assemble

namespace GlobalTheory.EigWhole

open Assemble

theorem ramModel_of_hypotheses : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd →
    RamModel := by
  intro h2 hH hR hS hP D O hO B hB R hR2 c hA M L m Ψ hI hΨ
  haveI := M.ar.isIntegral
  have hd : (NumberField.discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  rw [← sgnSub_diff]
  refine GlobalTheory.T.induced_metric_arithmetic_function_shift h2 hR _ (O.var c) M _ (adlD O (Pad.setB O.κ B) R c) _ m (Ψ ∘ₗ (sgnSub (Var O)).toLinearMap)
    (induced_adlD O hO _ R c M L m hI) (isArFun_dual h2.p4.arIso M.ar L hΨ) _
    (fun a => wholeVar O (finSumFinEquiv.symm a)) (fun a => eigVar O (finSumFinEquiv.symm a))
    (fun a => adlD_eigVar_eq O _ R c _) (NumberField.discr D.host.E).natAbs.primeFactors (fun p hp => ?_)
    (fun a v ε y hv => ?_) _
  · have hp' := Nat.prime_of_mem_primeFactors hp
    simp only [adlD_eigVar, adlD_wholeVar]
    exact ⟨hp', GlobalTheory.T.relative_flag_whole_symbol_multiple h2 hH hR hS hP D O hO _ R hR2 p hp' (mem_setB O B hp) c⟩
  · rw [adlD_eigVar, adlD_wholeVar]
    exact lgOf_eigSym O hA _ v ε y fun h => hv (Nat.mem_primeFactors.2 ⟨LineTest.residueCharacteristic_prime v, h, hd⟩)

end GlobalTheory.EigWhole

end
