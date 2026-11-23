import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialEqProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open IsDedekindDomain Formalism.L2.Pj GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.VertForm GlobalTheory.TrueCx

namespace GlobalTheory.PowerSumVert

open Formalism.BasicNotions.DV in

theorem core (h2 : Hypotheses2) (hH : HypothesesH) {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)
    (x : ToroidalCompactificationData s) (Φ : s.Flag) (hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)) (ehm : hm = metsOf x Φ)
    (hd : ∀ c, (Φ.C c).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) (Sx : Finset ℕ) (R : ℝ) (hR : 2 ≤ R) (p : ℕ) (hp : p.Prime)
    (c : s.Comp) (n : ℕ) (B : Fin n → Sym D.host.E →₀ ℤ)
    (hB : ∀ i, ∀ a ∈ (B i).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R)
    (hfl : FlagAt (fun i => adlOf (Φ.C c) (hm c) (B i)) p) (k : ℕ) (hk : 1 ≤ k) (y : Rt D.what₂.Tau N)
    (G : MvPolynomial (Sym D.host.E →₀ ℤ) ℝ)
    (hG : ∀ v ∈ G.vars, ∀ a ∈ v.support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R) :
    numL ((arIn s Φ hm).num c) (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1)
      ((∑ i, X (B i) ^ k) * ((X ((arIn s Φ hm).root (Function.update (ArIn.ind Sx) p false) R y c) -
        X ((arIn s Φ hm).root (Function.update (ArIn.ind Sx) p true) R y c)) * G)) = 0 := by
  subst ehm
  let ι : Type := Fin n ⊕ (Bool ⊕ {v // v ∈ G.vars})
  let a : Bool → ℕ → Bool := fun b => Function.update (ArIn.ind Sx) p b
  let w : ι → Sym D.host.E →₀ ℤ :=
    Sum.elim B (Sum.elim (fun b => rootSym S.Dw (a b) (some R) (tauEmb D y.1) y.2) Subtype.val)
  have ha (b : Bool) : {q | a b q = true}.Finite := (insert p Sx).finite_toSet.subset fun q hq => by
    by_cases e : q = p
    · simp [e]
    · simpa [a, ArIn.ind, e] using hq
  obtain ⟨M, L, m, Ψ, hI, hΨ, hnum⟩ := (GlobalTheory.ArTopTrue.arTop_true h2.p4 hH.deg HTBound.htBound D _ _ _ _ _ s x Φ c R hR).2
    ι w fun i b hb => by
      rcases i with i | b' | v
      · exact hB i b hb
      · obtain ⟨e₁, e₂⟩ := mem_support_rootSym hb
        exact ⟨e₁ ▸ ha _, e₂⟩
      · exact hG v.1 v.2 b hb
  obtain ⟨G', hG'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range G (Subtype.val : {v // v ∈ G.vars} → _)
    Subtype.val_injective fun v hv => ⟨⟨v, hv⟩, rfl⟩
  have hw : (w ∘ fun v : {v // v ∈ G.vars} => (Sum.inr (Sum.inr v) : ι)) = Subtype.val := rfl
  have hT : rename w ((∑ i, X (Sum.inl i : ι) ^ k) * ((X (Sum.inr (Sum.inl false) : ι) - X (Sum.inr (Sum.inl true))) *
      rename (fun v : {v // v ∈ G.vars} => (Sum.inr (Sum.inr v) : ι)) G')) =
      (∑ i, X (B i) ^ k) * ((X ((arIn s Φ (metsOf x Φ)).root (Function.update (ArIn.ind Sx) p false) R y c) -
        X ((arIn s Φ (metsOf x Φ)).root (Function.update (ArIn.ind Sx) p true) R y c)) * G) := by
    simp only [map_mul, map_sum, map_pow, map_sub, rename_X, rename_rename, hw, hG']
    rfl
  rw [← hd c]
  refine (congrArg (numL ((arIn s Φ (metsOf x Φ)).num c) ((Φ.C c).Y.dim + 1)) hT).symm.trans ?_
  refine (numL_rename w _ _ Ψ _ hΨ.2 hnum _).trans (div_eq_zero_iff.2 (.inl ?_))
  exact powerSum_mul_vertical h2 M _ L m Ψ hI hΨ p hp (fun i : Fin n => (Sum.inl i : ι)) hfl
    (Sum.inr (Sum.inl false)) (Sum.inr (Sum.inl true)) (adlOf_rootSym_eq _ _ _ _ _ _ _) _
    (add_nonneg (div_nonneg zero_le_one (sub_nonneg.2 (by exact_mod_cast hp.one_le))) (by unfold vDiff; positivity))
    (abs_lgOf_update_sub_le _ _ p _ _ _) k hk _

end GlobalTheory.PowerSumVert

namespace GlobalTheory.PowerSumVert

open Formalism.BasicNotions.DV in

theorem mixEv_vars {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag)
    {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (Φ.C k) C) (Sx : Finset ℕ) (R : ℝ) (p : ℕ) (c : s.Comp)
    (g : MvPolynomial (Vm D.what₂.Tau N) ℝ) :
    ∀ v ∈ ((arIn s Φ hm).mixEv Sx R p c g).vars, ∀ a ∈ (v : Sym D.host.E →₀ ℤ).support,
      {q | a.1 q = true}.Finite ∧ a.2.1 = some R := by
  intro v hv b hb
  have ha (b' : Bool) : {q | Function.update (ArIn.ind Sx) p b' q = true}.Finite :=
    (insert p Sx).finite_toSet.subset fun q hq => by
      by_cases e : q = p
      · simp [e]
      · simpa [ArIn.ind, e] using hq
  rw [ArIn.mixEv, MvPolynomial.aeval_eq_bind₁] at hv
  obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.1 (vars_bind₁ _ _ hv)
  rcases u with ⟨b', z⟩ | ⟨b', k⟩
  · simp only [vars_X, Finset.mem_singleton] at hu
    subst hu
    obtain ⟨e₁, e₂⟩ := mem_support_rootSym hb
    exact ⟨e₁ ▸ ha _, e₂⟩
  · dsimp only at hu
    rcases Finset.mem_union.1 (vars_mul _ _ hu) with h | h
    · simp [vars_C] at h
    · obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.1 (vars_sum_subset _ _ h)
      have hl' := vars_pow _ _ hl
      rw [vars_X, Finset.mem_singleton] at hl'
      subst hl'
      obtain ⟨e₁, e₂⟩ := mem_support_wholeSym hb
      exact ⟨e₁ ▸ ha _, e₂⟩

theorem powerSum_vert_mul : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core →
    ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → ∀ (c : O.s.Comp) (n : ℕ)
    (A : Fin n → (arIn O.s O.Φ O.met.hm).A c),
    (∀ i, ∀ a ∈ (A i : Sym D.host.E →₀ ℤ).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R) →
    FlagAt (fun i => adlOf (O.Φ.C c) (O.met.hm c) (A i)) p → ∀ k : ℕ, 1 ≤ k →
    ∀ (y : Rt D.what₂.Tau O.N) (G : MvPolynomial ((arIn O.s O.Φ O.met.hm).A c) ℝ),
    (∀ v ∈ G.vars, ∀ a ∈ (v : Sym D.host.E →₀ ℤ).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R) →
      numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        ((∑ i, X (A i) ^ k) * ((X ((arIn O.s O.Φ O.met.hm).root (Function.update (ArIn.ind Sx) p false) R y c) -
          X ((arIn O.s O.Φ O.met.hm).root (Function.update (ArIn.ind Sx) p true) R y c)) * G)) = 0 := by
  intro h2 hH _ _ D O hO Sx R hR p hp c n A hA hfl k hk y G hG
  obtain ⟨x, P, h⟩ := hO
  exact core h2 hH O.s x O.Φ O.met.hm h.hm_eq O.dim_eq Sx R hR p hp c n A hA hfl k hk y G hG

end GlobalTheory.PowerSumVert
