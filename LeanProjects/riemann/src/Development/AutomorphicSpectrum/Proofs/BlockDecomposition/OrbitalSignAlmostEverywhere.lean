import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapOrbUnitEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianFormCharPoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsIntegralCharpolySplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSameSeparableCharpolySplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInert
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.KapOrbAE

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_integral_unitary (hE : Unr E) (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) :
    ∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  obtain ⟨M, G, hMP, hG, hGh, hMG⟩ := GlobalTheory.EllHermGlobal.exists_charpoly_herm E n P hP
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => GlobalTheory.ExInertUnit.eventually_mem_integers _
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => GlobalTheory.ExInertUnit.eventually_mem_integers _
  have h3 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => GlobalTheory.ExInertUnit.eventually_mem_integers _
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3 hw
  obtain ⟨γ, hγ, hc⟩ := GlobalTheory.ExInertUnit.local_step hE w hw M G hG hGh hMG hw1 hw2 hw3
  exact ⟨γ, hγ, by rw [hc, hMP]⟩

open GlobalTheory.UnitOrbCount in

theorem kapOrb_unit_pos (hU : Unr E) (n : ℕ) (hn : 1 ≤ n) (p₁ p₂ : E[X]) (h1 : p₁ ∈ Ell E p₁.natDegree)
    (h2 : p₂ ∈ Ell E p₂.natDegree) (hc : IsCoprime p₁ p₂) (hd : p₁.natDegree + p₂.natDegree = n) :
    ∀ᶠ w : Pl E in cofinite, kapOrb n w (atPl w p₁) (atPl w p₂) ((KL n w : Set (UL n w)).indicator 1) = 1 := by
  have hP := ell_mul p₁ p₂ h1 h2 hc hd
  obtain ⟨S, hS⟩ := exists_section (E := E)
  filter_upwards [GlobalTheory.BCT.OrbUnit.orbUnit_ae E hU n hn S hS _ hP, GlobalTheory.T.eventually_exists_integral_charpoly_split_place E hU n hn _ hP,
    exists_integral_unitary hU n _ hP, GlobalTheory.T.eventually_unitary_conj_of_same_elliptic_charpoly_inert E hU n hn _ hP] with w hA hE1 hE2 hU2
  have hmap : atPl w (p₁ * p₂) = atPl w p₁ * atPl w p₂ := Polynomial.map_mul _
  rw [hmap] at hA hE1 hE2 hU2
  obtain ⟨γ₀, hγ₀K, hγ₀P⟩ : ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w p₁ * atPl w p₂ := by
    by_cases hs : IsSplitAt w
    · exact hE1 hs
    · exact hE2 hs
  have huniq : ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w → γ.1.val.charpoly = atPl w p₁ * atPl w p₂ →
      γ'.1.val.charpoly = atPl w p₁ * atPl w p₂ → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
    intro γ γ' hk hk' hp hp'
    by_cases hs : IsSplitAt w
    · have := GlobalTheory.T.exists_conj_same_separable_charpoly_split_place E n _ hP w hs γ γ'
      rw [hmap] at this
      exact this hp hp'
    · exact hU2 hs γ γ' hk hk' hp hp'
  have key : ∀ γ : UL n w, γ.1.val.charpoly = atPl w p₁ * atPl w p₂ →
      ((∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) ↔ (Quot.mk _ γ : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀) := by
    intro γ hp
    rw [mk_eq_iff]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨k, hk⟩ := huniq _ γ₀ hg hγ₀K (by rw [cp_conj, hp]) hγ₀P
      exact ⟨g * k, by rw [hk]; group⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, hg ▸ hγ₀K⟩
  unfold kapOrb clSum
  simp only [Set.mem_setOf_eq]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : TwCl (MonoidHom.id (UL n w)), Quot.mk _ γ₀ = c₀ := ⟨_, rfl⟩
  rw [hc₀] at key
  rw [finsum_eq_single _ c₀]
  · have hc : (Quot.mk _ c₀.rep : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀ := by
      rw [hc₀]; exact Quot.out_eq _
    obtain ⟨g, hg⟩ := (mk_eq_iff _ _).1 hc
    have hp : c₀.rep.1.val.charpoly = atPl w p₁ * atPl w p₂ := by
      rw [← hγ₀P, hg, cp_conj]
    have hex : ∃ g : UL n w, g⁻¹ * c₀.rep * g ∈ KL n w :=
      ⟨g, hg ▸ hγ₀K⟩
    obtain ⟨hT, -, hQ⟩ := hA _ hp
    rw [if_pos hp, hT, if_pos hex, hQ (atPl w p₁) (dvd_mul_right _ _) hex, mul_one]
  · intro c hne
    have hc : (Quot.mk _ c.rep : TwCl (MonoidHom.id (UL n w))) = c := Quot.out_eq c
    by_cases hp : c.rep.1.val.charpoly = atPl w p₁ * atPl w p₂
    · obtain ⟨hT, -, -⟩ := hA c.rep hp
      rw [if_pos hp, hT, if_neg, mul_zero]
      intro hex
      apply hne
      rw [← hc]
      exact (key _ hp).1 hex
    · rw [if_neg hp]

instance subsingleton_units_rank_zero (w : Pl E) : Subsingleton (UL 0 w) := by
  refine ⟨fun a b => Subtype.ext (Units.ext ?_)⟩
  exact Subsingleton.elim _ _

theorem kapSign_zero (w : Pl E) (Q : (w.adicCompletion E)[X]) (γ : GLw 0 w) : kapSign 0 w Q γ = 1 := by
  unfold kapSign
  split_ifs with hs
  · rfl
  · simp only
    have hsub : Subsingleton (LinearMap.ker (Matrix.toLin' (aeval γ.val Q))) := by
      refine ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    haveI : IsEmpty (Fin (Module.finrank (w.adicCompletion E) (LinearMap.ker (Matrix.toLin' (aeval γ.val Q))))) := by
      rw [Module.finrank_zero_of_subsingleton]
      infer_instance
    rw [Matrix.det_isEmpty]
    simp [ordL]
    exact zpow_zero _

theorem kapOrb_unit_zero (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hQ : Q₁ * Q₂ = 1) :
    kapOrb 0 w Q₁ Q₂ ((KL 0 w : Set (UL 0 w)).indicator 1) = 1 := by
  haveI : Subsingleton (TwCl (MonoidHom.id (UL 0 w))) := by
    refine ⟨fun a b => ?_⟩
    induction a using Quot.ind with | _ x => ?_
    induction b using Quot.ind with | _ y => ?_
    rw [Subsingleton.elim x y]
  haveI : Unique (TwCl (MonoidHom.id (UL 0 w))) := ⟨⟨Quot.mk _ 1⟩, fun _ => Subsingleton.elim _ _⟩
  unfold kapOrb clSum
  rw [finsum_unique]
  set γ : UL 0 w := (default : TwCl (MonoidHom.id (UL 0 w))).rep
  have hcp : γ.1.val.charpoly = Q₁ * Q₂ := by
    rw [hQ]
    rw [Matrix.charpoly, Matrix.det_isEmpty]
  have hγ : γ ∈ KL 0 w := by
    rw [Subsingleton.elim γ 1]
    exact one_mem _
  have hT : twOrb (MonoidHom.id _) (KL 0 w) γ ((KL 0 w : Set (UL 0 w)).indicator 1) = 1 := by
    rw [GlobalTheory.BCT.OrbUnit.twOrb_unit (KL 0 w) γ, if_pos ⟨1, by simpa using hγ⟩]
    · intro g₁ g₂ _ _
      exact ⟨1, one_mem _, 1, one_mem _, Subsingleton.elim _ _⟩
    · intro g _ x _
      rw [Subsingleton.elim x 1]
      exact one_mem _
  have hcp' : γ ∈ {γ : UL 0 w | γ.1.val.charpoly = Q₁ * Q₂} := hcp
  rw [if_pos hcp', hT, mul_one]
  exact kapSign_zero w Q₁ γ.1

end GlobalTheory.CompanionTheory.KapOrbAE

theorem GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE : KapOrbAE := by
  intro E _ _ _ hU n K' f hf p₁ p₂ h1 h2 hc hd
  have hunit : ∀ᶠ w : Pl E in cofinite,
      kapOrb n w (atPl w p₁) (atPl w p₂) ((KL n w : Set (UL n w)).indicator 1) = 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have d1 : p₁.natDegree = 0 := by omega
      have d2 : p₂.natDegree = 0 := by omega
      have e1 : p₁ = 1 := h1.1.natDegree_eq_zero.1 d1
      have e2 : p₂ = 1 := h2.1.natDegree_eq_zero.1 d2
      refine Eventually.of_forall fun w => GlobalTheory.CompanionTheory.KapOrbAE.kapOrb_unit_zero w _ _ ?_
      simp [e1, e2]
    · exact GlobalTheory.CompanionTheory.KapOrbAE.kapOrb_unit_pos hU n hn p₁ p₂ h1 h2 hc hd
  have hall : ∀ᶠ w : Pl E in cofinite, kapOrb n w (atPl w p₁) (atPl w p₂) (f w) = 1 := by
    filter_upwards [hf.2, hunit] with w hw h
    rw [hw]
    exact h
  exact Filter.eventually_cofinite.1 hall
