import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VdivLnIdFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx

namespace GlobalTheory.PairTerm

section Vert

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

structure VertSub (p : ℕ) (X : Scheme.{0}) (n : ℕ) (z : X) : Type 1 where

  Z : Scheme.{0}

  i : Z ⟶ X
  imm : IsClosedImmersion i
  int : IsIntegral Z

  alg : Algebra (ZMod p) Γ(Z, ⊤)
  gen : i (genericPoint Z) = z
  dim : topologicalKrullDim Z = n

open Classical in

def vertNum (p : ℕ) [Fact p.Prime] (V : Cover Y) (n : ℕ) (N : Fin n → HermLB V.p) (z : V.X) : ℝ :=
  if h : Nonempty (VertSub p V.X n z) then
    letI := h.some.alg
    haveI := h.some.imm
    haveI := h.some.int
    (interNum (ZMod p) (structureModule h.some.Z) (fun j => (N j).B.pull h.some.i) : ℝ)
  else 0

theorem vertNum_cast (p : ℕ) [Fact p.Prime] (V : Cover Y) {n n' : ℕ} (h : n = n') (N : Fin n' → HermLB V.p) (z : V.X) :
    vertNum p V n (fun j => N (Fin.cast h j)) z = vertNum p V n' N z := by
  subst h
  rfl

def LiesOverPl (V : Cover Y) (v : HeightOneSpectrum (𝓞 F)) (z : V.X) : Prop := (V.p z).asIdeal = v.asIdeal

def RatNorms (V : Cover Y) (M : HermLB V.p) (r : M.B.ι → V.X.functionFieldˣ)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
    (i : M.B.ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ M.B.U i →
      l v e y = Real.log (e.w (valAt (z ≫ V.j) (r i : V.X.functionField)))

end Vert

section Syms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def wOf (a : ℕ → Bool) (p : ℕ) (R : ℝ) {n : ℕ} (x : Ln Dw) (ν : Fin n → Bool × Ln Dw) : Bool ⊕ Fin n → (Sym E →₀ ℤ) :=
  Sum.elim (fun b => lnSym (Function.update a p b) (some R) x) fun i => lnSym (Function.update a p (ν i).1) (some R) (ν i).2

theorem mem_support_lnSym {a : ℕ → Bool} {R : Option ℝ} {x : Ln Dw} {b : Sym E}
    (h : b ∈ (lnSym a R x).support) : b.1 = a ∧ b.2.1 = R := by
  rcases x with ⟨_ | _, st⟩ <;> simp only [lnSym] at h <;>
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)] <;> exact ⟨rfl, rfl⟩

theorem parOf_lnSym (a : ℕ → Bool) (R : Option ℝ) (x : Ln Dw) : parOf (lnSym a R x) = R := by
  have h : (lnSym a R x).support.Nonempty := by
    rcases x with ⟨_ | _, st⟩ <;> simp [lnSym, Finsupp.support_single_ne_zero]
  rw [parOf, dif_pos h]
  exact (mem_support_lnSym h.choose_spec).2

theorem expo_lnSym (a a' : ℕ → Bool) (R : Option ℝ) (x : Ln Dw) : expo Dw (lnSym a R x) = expo Dw (lnSym a' R x) := by
  funext y
  rcases x with ⟨_ | _, st⟩ <;> simp only [expo, lnSym] <;> rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

variable {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem adlOf_lnSym_eq {C : CxSt F} (hm : Mets Y C) (a a' : ℕ → Bool) (R : Option ℝ) (x : Ln Dw) :
    adlOf Y hm (lnSym a' R x) = { adlOf Y hm (lnSym a R x) with lg := (adlOf Y hm (lnSym a' R x)).lg } := by
  have key (n n' : Letter Dw → ℤ) (h : n = n') (r r' : Option ℝ) (h' : r = r') (lg) :
      (⟨divOf Y n, 1, fun σ => hm r σ n, 0, lg⟩ : Adl C Y.Y) = ⟨divOf Y n', 1, fun σ => hm r' σ n', 0, lg⟩ := by
    rw [h, h']
  exact key _ _ (expo_lnSym _ _ _ _) _ _ ((parOf_lnSym _ _ _).trans (parOf_lnSym _ _ _).symm) _

end Syms

end GlobalTheory.PairTerm

namespace GlobalTheory.PairTerm

section LgBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem abs_lnStep_sub_le' (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (p : ℕ) [hp : Fact p.Prime]
    (x : Sp ℂ_[p] ⟶ Z.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left))
    (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) :
    |lnStep Z.t x u p true st - lnStep Z.t x u p false st| ≤ Real.log p / ((p : ℝ) - 1) + vDiff E p * Real.log p := by
  rcases st with ⟨τ, k⟩ | k
  · exact LgDiff.abs_lnStep_sub_le HTBound.htBound Z p x u τ k
  · have hv : 0 ≤ vDiff E p * Real.log p := mul_nonneg (by unfold vDiff; positivity) (Real.log_natCast_nonneg p)
    have hL : 0 ≤ Real.log p / ((p : ℝ) - 1) := by
      have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
      exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)
    by_cases h : k < (letters Dw).length
    · have hs := LgDiff.abs_log_grNorm_DR_HT_le HTBound.htBound Z p x
        (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, h⟩
      rw [mul_one_div, abs_sub_comm] at hs
      simp only [lnStep, dif_pos h, lat]
      linarith
    · simp only [lnStep, dif_neg h, sub_self, abs_zero]
      linarith

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)}
  (Y : FlagCpt Z e)

theorem abs_lgOf_lnSym_update_sub_le (a : ℕ → Bool) (p : ℕ) (R : Option ℝ) (x : Ln Dw) (v : HeightOneSpectrum (𝓞 F))
    (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    |lgOf Y (lnSym (Function.update a p false) R x) v ε y - lgOf Y (lnSym (Function.update a p true) R x) v ε y| ≤
      (if resP v = p then 1 / ((p : ℝ) - 1) + vDiff E p else 0) * (-Real.log (ε.w (resP v : AlgebraicClosure F))) := by
  have hw : 0 ≤ -Real.log (ε.w (resP v : AlgebraicClosure F)) :=
    neg_nonneg.2 (Real.log_nonpos (ε.w.nonneg _) ((ε.mem_O _).1 (natCast_mem _ _)))
  have hp : (resP v).Prime := CharP.char_prime_of_ne_zero (𝓞 F ⧸ v.asIdeal) (CharP.ringChar_ne_zero_of_finite _)
  haveI := Fact.mk hp
  have hs (a : ℕ → Bool) (Φ : Sym E → ℝ) : ((lnSym a R x).sum fun b n => (n : ℝ) * Φ b) =
      if x.1 then -Φ (a, R, x.2.1) else Φ (a, R, x.2.1) := by
    rcases x with ⟨_ | _, st⟩ <;> simp only [lnSym] <;> rw [Finsupp.sum_single_index (by simp)] <;> push_cast <;>
      simp
  simp only [lgOf, dif_pos hp]
  rewrite [expo_lnSym (Function.update a p true) (Function.update a p false), add_sub_add_left_eq_sub, ← mul_sub,
    abs_mul, hs, hs]
  dsimp only
  by_cases h : resP v = p
  · subst h
    have hl := Real.log_pos (show (1 : ℝ) < resP v by exact_mod_cast hp.one_lt)
    rewrite [if_pos rfl, Function.update_self, Function.update_self]
    have key (t : ℝ) (ht : t ≤ Real.log (resP v) / ((resP v : ℝ) - 1) + vDiff E (resP v) * Real.log (resP v)) :
        |-Real.log (ε.w (resP v : AlgebraicClosure F)) / Real.log (resP v)| * t ≤
          (1 / ((resP v : ℝ) - 1) + vDiff E (resP v)) * (-Real.log (ε.w (resP v : AlgebraicClosure F))) := by
      refine (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans_eq ?_
      rw [abs_of_nonneg (div_nonneg hw hl.le)]
      field_simp
    refine key _ ?_
    split_ifs
    · rw [neg_sub_neg]
      exact abs_lnStep_sub_le' _ _ _ _ _
    · rw [abs_sub_comm]
      exact abs_lnStep_sub_le' _ _ _ _ _
  · have hb : Function.update a p false (resP v) = Function.update a p true (resP v) :=
      (Function.update_of_ne h _ _).trans (Function.update_of_ne h _ _).symm
    rewrite [hb, sub_self, abs_zero, mul_zero, if_neg h, zero_mul]
    exact le_rfl

end LgBound

end GlobalTheory.PairTerm
