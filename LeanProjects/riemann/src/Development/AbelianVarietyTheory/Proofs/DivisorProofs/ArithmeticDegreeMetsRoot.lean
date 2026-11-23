import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTwistCompatibleModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTwistLevelModelStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open CategoryTheory

namespace GlobalTheory.ShFam.GalRelab

theorem numL_rename {A B : Type} (num : Multiset B → ℝ) (d : ℕ) (f : A → B) (P : MvPolynomial A ℝ) :
    GlobalTheory.ShFam.Pad.numL num d (MvPolynomial.rename f P) =
      GlobalTheory.ShFam.Pad.numL (fun M => num (M.map f)) d P := by
  classical
  have key : (GlobalTheory.ShFam.Pad.numL num d).comp (MvPolynomial.rename f).toLinearMap =
      GlobalTheory.ShFam.Pad.numL (fun M => num (M.map f)) d := by
    refine (MvPolynomial.basisMonomials A ℝ).ext fun m => ?_
    have hdeg : (Finsupp.mapDomain f m).degree = m.degree := by
      rw [Finsupp.degree_eq_weight_one, Finsupp.degree_eq_weight_one]
      simp [Finsupp.weight_apply, Finsupp.sum_mapDomain_index]
    have hb : (MvPolynomial.monomial (Finsupp.mapDomain f m) (1 : ℝ)) =
        MvPolynomial.basisMonomials B ℝ (Finsupp.mapDomain f m) := by
      simp [MvPolynomial.coe_basisMonomials]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials,
      MvPolynomial.rename_monomial, hb, GlobalTheory.ShFam.Pad.numL, GlobalTheory.ShFam.Pad.numL,
      Module.Basis.constr_basis, ← MvPolynomial.coe_basisMonomials, Module.Basis.constr_basis, hdeg,
      Finsupp.toMultiset_map]
  exact congrArg (fun L => L P) key

theorem powerset_map' {α β : Type} (f : α → β) (s : Multiset α) :
    (s.map f).powerset = s.powerset.map (Multiset.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.powerset_cons, ih, Multiset.map_map]

theorem polar_map {A B : Type} [AddCommMonoid A] [AddCommMonoid B] (top : A → ℝ) (top' : B → ℝ) (f : A →+ B)
    (M : Multiset A) (h : ∀ T ≤ M, top' (f T.sum) = top T.sum) :
    GlobalTheory.ShFam.Pad.polar top' (M.map f) = GlobalTheory.ShFam.Pad.polar top M := by
  unfold GlobalTheory.ShFam.Pad.polar
  rw [Multiset.card_map, powerset_map', Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun T hT => ?_
  simp only [Function.comp, Multiset.card_map]
  rw [← map_multiset_sum, h T (Multiset.mem_powerset.1 hT)]

end GlobalTheory.ShFam.GalRelab

namespace GlobalTheory.ShFam.GalRelab

def relab {E : Type} [Field E] (g : E →+* E) (a : GlobalTheory.ShFam.Pad.Sym E) : GlobalTheory.ShFam.Pad.Sym E :=
  (a.1, a.2.1, Sum.map (fun p => (p.1.comp g, p.2)) id a.2.2)

section Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem mapDomain_rootSym (g : E →+* E) (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) :
    (GlobalTheory.ShFam.Pad.rootSym Dw a R τ i).mapDomain (relab g) = GlobalTheory.ShFam.Pad.rootSym Dw a R (τ.comp g) i := by
  unfold GlobalTheory.ShFam.Pad.rootSym
  split_ifs <;> simp only [Finsupp.mapDomain_single] <;> rfl

theorem support_rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) :
    ∀ b ∈ (GlobalTheory.ShFam.Pad.rootSym Dw a R τ i).support, b.2.2.isLeft = true ∧ b.2.1 = R := by
  intro b hb
  unfold GlobalTheory.ShFam.Pad.rootSym at hb
  split_ifs at hb <;>
    · have := Finsupp.support_single_subset hb
      rw [Finset.mem_singleton] at this
      subst this
      exact ⟨rfl, rfl⟩

theorem support_sum {A : Type} (P : A → Prop) (T : Multiset (A →₀ ℤ)) (h : ∀ w ∈ T, ∀ b ∈ w.support, P b) :
    ∀ b ∈ T.sum.support, P b := by
  induction T using Multiset.induction_on with
  | empty => simp
  | cons w T ih =>
    intro b hb
    rw [Multiset.sum_cons] at hb
    rcases Finset.mem_union.1 (Finsupp.support_add hb) with h1 | h1
    · exact h w (Multiset.mem_cons_self _ _) b h1
    · exact ih (fun w' hw' => h w' (Multiset.mem_cons_of_mem hw')) b h1

end Roots

theorem tauEmb_mulRight (D : D7) (g : D.R.Psi) (ρ : D.what₂.Tau) :
    (Formalism.BasicNotions.DV.tauEmb D (((D.eTau.trans (Equiv.mulRight g)).trans D.eTau.symm).symm ρ)).comp
      ((D.host.sigmaOf (g : D.R.GG) : D.host.E ≃ₐ[ℚ] D.host.E) : D.host.E →+* D.host.E) =
      Formalism.BasicNotions.DV.tauEmb D ρ := by
  ext y
  simp only [RingHom.comp_apply, Formalism.BasicNotions.DV.tauEmb, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply, Equiv.mulRight_symm, Equiv.coe_mulRight]
  change D.host.φ₀ (D.host.sigmaOf _ (D.host.sigmaOf _ y)) = D.host.φ₀ (D.host.sigmaOf _ y)
  have hm : ∀ a b : D.R.GG, D.host.sigmaOf (a * b) = D.host.sigmaOf a * D.host.sigmaOf b :=
    fun a b => map_mul _ a b
  rw [← AlgEquiv.mul_apply, ← hm, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]

end GlobalTheory.ShFam.GalRelab

namespace GlobalTheory.ShFam.GalRelab

open GlobalTheory.ShFam.Pad in

theorem arDeg_relabel : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ τ τ' : D.what₂.Tau, ∃ σ : Equiv.Perm D.what₂.Tau, σ τ = τ' ∧ ∀ x : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∃ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ (B R : ℝ) (u : D.what₂.Tau → Fin O.N → ℝ), (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x O.Φ)).arDeg (GlobalTheory.FlagAr.setB O.Y B) R (linRoot (fun ρ i => u (σ ρ) i) ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N + 1)) = (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x' O.Φ)).arDeg (GlobalTheory.FlagAr.setB O.Y B) R (linRoot u ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N + 1)) := by
  intro h2 hH D O hO τ τ'
  let g : D.R.Psi := (D.eTau τ)⁻¹ * D.eTau τ'
  let σ : Equiv.Perm D.what₂.Tau := (D.eTau.trans (Equiv.mulRight g)).trans D.eTau.symm
  refine ⟨σ, by simp [σ, g], fun x => ?_⟩
  obtain ⟨x', e, hx⟩ := GlobalTheory.T.exists_galois_twist_level_model h2 hH D O hO (g : D.R.GG) g.2 (fun g' hg' => GlobalTheory.T.exists_galois_twist_compatible_model h2 D O hO g' hg') x
  refine ⟨x', fun B R u => ?_⟩
  have hlin : linRoot (fun ρ i => u (σ ρ) i) =
      MvPolynomial.rename (fun y : D.what₂.Tau × Fin O.N => (σ.symm y.1, y.2)) (linRoot u) := by
    unfold linRoot
    rw [map_neg, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.prodCongr σ (Equiv.refl _)) _ _ fun y => ?_
    simp [MvPolynomial.rename_X, MvPolynomial.algebraMap_eq]
  rw [hlin, ← map_pow]
  rw [ArIn.arDeg, ArIn.arDeg, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Fintype.sum_equiv e _ _ fun k => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.rename_rename]
  rw [numL_rename, numL_rename]
  refine congrArg (fun f => numL f (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N + 1) _) (funext fun M => ?_)
  let gg : D.host.E →+* D.host.E :=
    ((D.host.sigmaOf (g : D.R.GG) : D.host.E ≃ₐ[ℚ] D.host.E) : D.host.E →+* D.host.E)
  let rt : D.what₂.Tau × Fin O.N → Sym D.host.E →₀ ℤ := fun y =>
    rootSym O.S.Dw (ArIn.ind (GlobalTheory.FlagAr.setB O.Y B)) (some R) (Formalism.BasicNotions.DV.tauEmb D y.1) y.2
  change polar (fun w => (adlOf (O.Φ.C k) (metsOf x O.Φ k) w).arTop)
      (M.map (rt ∘ fun y => (σ.symm y.1, y.2))) =
    polar (fun w => (adlOf (O.Φ.C (e k)) (metsOf x' O.Φ (e k)) w).arTop) (M.map rt)
  have hM : M.map rt = (M.map (rt ∘ fun y => (σ.symm y.1, y.2))).map (Finsupp.mapDomain.addMonoidHom (relab gg)) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun y _ => ?_
    simp only [Function.comp, Finsupp.mapDomain.addMonoidHom_apply, rt]
    rw [mapDomain_rootSym, tauEmb_mulRight]
  rw [hM, polar_map]
  intro T hT
  refine (hx k (some R) T.sum ?_).symm
  refine support_sum _ T fun w hw => ?_
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_le hT hw)
  exact support_rootSym _ _ _ _ _

end GlobalTheory.ShFam.GalRelab
