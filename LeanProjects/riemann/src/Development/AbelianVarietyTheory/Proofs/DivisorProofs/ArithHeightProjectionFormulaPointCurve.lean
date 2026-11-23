import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntegralPullMulDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantRestrictionPointClosuresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultPullbackRationalSectionPushforwardStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.ProjCurve

section SlopeTestRemainingChoices

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}

open GlobalTheory.TwistTop in

theorem refines_trans {N L M : HermLB p} {π : N.B.ι → L.B.ι} {π' : L.B.ι → M.B.ι}
    (h : Refines N L π 0) (h' : Refines L M π' 0) : Refines N M (fun c => π' (π c)) 0 where
  le c := (h.le c).trans (h'.le _)
  g Z r z c c' hc hc' := (h.g Z r z c c' hc hc').trans (h'.g Z r z _ _ (h.le _ hc) (h.le _ hc'))
  φ σ c y hy := by
    rw [h.φ σ c y hy, h'.φ σ _ y (ptsIn_mono (h.le _) hy)]
    simp

open GlobalTheory.TwistTop in

theorem exists_refines_of_eq {N L L' : HermLB p} {π : N.B.ι → L.B.ι} (h : Refines N L π 0) (e : L = L') :
    ∃ π' : N.B.ι → L'.B.ι, Refines N L' π' 0 := by
  subst e
  exact ⟨π, h⟩

theorem pull_congr (L : HermLB p) {q : Y ⟶ Sp k} {f f' : Y ⟶ X} (e : f = f') (hf : f ≫ p = q)
    (hf' : f' ≫ p = q) : L.pull f hf = L.pull f' hf' := by
  subst e
  rfl

theorem isClosed_of_ne_generic {Z : Scheme.{0}} [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : IsClosed ({z} : Set Z) := by
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le)
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ with h | h
  · refine isClosed_of_closure_subset fun w hw => ?_
    have h₁ : (⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Z) ≤
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      closure_minimal (Set.singleton_subset_iff.2 hw) isClosed_closure
    have h₂ : z ∈ closure {w} := h h₁ (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h₂).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@h
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec Z)) hz

theorem log_card_residueField {W Z : Scheme.{0}} (g : W ⟶ Z) (w : W) [Finite (W.residueField w)] :
    Real.log (Nat.card (W.residueField w)) =
      (g.residueDegree w : ℝ) * Real.log (Nat.card (Z.residueField (g w))) := by
  letI := (g.residueFieldMap w).hom.toAlgebra
  have : Finite (Z.residueField (g w)) := Finite.of_injective _ (g.residueFieldMap w).hom.injective
  have : Module.Finite (Z.residueField (g w)) (W.residueField w) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := Z.residueField (g w)) (V := W.residueField w), Nat.cast_pow,
    Real.log_pow]
  rfl

end SlopeTestRemainingChoices

open GlobalTheory.TwistTop in

theorem main : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, CharZero Γ(clo y, ⊤) → HasDim y 1 →
    h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H' y hc hy
  have hAX := isAmb_of_isArithVar hX
  have hAY := isAmb_of_isArithVar hY
  have := hAX.isNoetherian
  have := hAY.isNoetherian
  obtain ⟨g, hgc, hgη, hgdeg⟩ := GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y
  have D₁ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hAY
  have D₂ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hAX

  have hdW : topologicalKrullDim (clo y) = 1 := by
    have h₁ := (D₁.2.2.2.2.1 (clo y) (cloι y) (genericPoint (clo y)) 1).1 (by rw [cloι_genericPoint]; exact hy)
    have h₂ := (D₁.2.2.2.2.2 (clo y) 1).1 h₁
    rw [h₂]
    rfl

  have hcZ : CharZero Γ(clo (π y), ⊤) := g.appTop.hom.charZero

  obtain ⟨m, hm⟩ := D₂.1
  obtain ⟨d', -, hd'⟩ := hm (π y)
  have hdZ' : topologicalKrullDim (clo (π y)) = d' :=
    (D₂.2.2.2.2.2 (clo (π y)) d').1 ((D₂.2.2.2.2.1 (clo (π y)) (cloι (π y)) _ d').1
      (by rw [cloι_genericPoint]; exact hd'))
  obtain ⟨hle, hiff⟩ := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ y 1 d' hy hd'
  have hd1 : d' = 1 := by
    have h0 : d' ≠ 0 := by
      rintro rfl
      exact hX.dim_ne_zero (cloι (π y)) hcZ (hdZ'.trans (by rfl))
    omega
  subst hd1
  have hdZ : topologicalKrullDim (clo (π y)) = 1 := hdZ'.trans (by rfl)
  have hdeg : π.residueDegree y ≠ 0 := hiff.2 rfl
  have hdegη : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]
  have hW : IsArithVar (cloι y ≫ q) 0 := hY.of_isClosedImmersion (cloι y) hc hdW
  have hZ : IsArithVar (cloι (π y) ≫ p) 0 := hX.of_isClosedImmersion (cloι (π y)) hcZ hdZ

  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr (cloι (π y))).isLB
  have hg' : g ≫ cloι (π y) ≫ p = cloι y ≫ q := by
    rw [← Category.assoc, hgc, Category.assoc, hπ]
  have hr' := MultPull.isRatSec_pull_map g (hgη ▸ specializes_rfl : g (genericPoint (clo y)) ⤳ genericPoint _) hr

  have h₁ : (cloι y ≫ π) ≫ p = cloι y ≫ q := by rw [Category.assoc, hπ]
  have h₂ : (g ≫ cloι (π y)) ≫ p = cloι y ≫ q := by rw [hgc, h₁]
  obtain ⟨ρ, hρ⟩ := exists_refines_of_eq (L.refines_pull_pull π hπ (cloι y) rfl h₁)
    (pull_congr L hgc.symm h₁ h₂)
  have hρ' := refines_trans hρ (L.refines_pull_comp (cloι (π y)) rfl g hg' h₂)

  have e₁ := H'.point (clo y) (cloι y) hc hdW _ (hρ'.isRatSec hr')
  rw [cloι_genericPoint] at e₁
  have e₂ : ((L.pull π hπ).restr (cloι y)).curveDeg (hρ'.isRatSec hr') =
      ((L.restr (cloι (π y))).pull g hg').curveDeg hr' := by
    unfold HermLB.curveDeg
    rw [hρ'.div hr']
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun z => hρ'.logNorm hr' (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint hW z]
    exact CartierDiv.genericPoint_notMem_supp _

  have e₃ := H.point (clo (π y)) (cloι (π y)) hcZ hdZ r hr
  rw [cloι_genericPoint] at e₃

  have a₁ := GlobalTheory.ArchDimZero.main k (clo y) (cloι y ≫ q) hW ((L.restr (cloι (π y))).pull g hg')
    ((L.restr (cloι (π y))).pull g hg') _ hr'
  have a₂ := GlobalTheory.T.archimedeanIntegral_pull_mul_degree k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) 0 hZ hW g hg' hgη
    (hdegη ▸ hdeg) (L.restr (cloι (π y))) (L.restr (cloι (π y))) r hr
  have a₃ := GlobalTheory.ArchDimZero.main k (clo (π y)) (cloι (π y) ≫ p) hZ (L.restr (cloι (π y)))
    (L.restr (cloι (π y))) r hr

  have f₁ := GlobalTheory.T.finsum_mult_pullback_rationalSection_pushforward k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) (hAX.sub _) (hAY.sub _) g hg' hgη
    (L.restr (cloι (π y))).B (L.restr (cloι (π y))).isLB r hr (fun z => Real.log (Nat.card ((clo (π y)).residueField z)))
  have f₂ : ∑ᶠ w, ((((L.restr (cloι (π y))).pull g hg').div hr').mult w : ℝ) *
      Real.log (Nat.card ((clo y).residueField w)) =
      ∑ᶠ w, ((((L.restr (cloι (π y))).pull g hg').div hr').mult w : ℝ) *
      ((g.residueDegree w : ℝ) * Real.log (Nat.card ((clo (π y)).residueField (g w)))) := by
    refine finsum_congr fun w => ?_
    by_cases hw : (((L.restr (cloι (π y))).pull g hg').div hr').mult w = 0
    · rw [hw, Int.cast_zero, zero_mul, zero_mul]
    have hne : w ≠ genericPoint (clo y) := fun e =>
      CartierDiv.genericPoint_notMem_supp _ (e ▸ CartierDiv.mem_supp_of_mult_ne_zero hw)
    have := hW.finite_residueField (isClosed_of_ne_generic hdW hne)
    rw [log_card_residueField g w]
  rw [e₁, e₂, e₃]
  unfold HermLB.curveDeg
  rw [← a₁, ← a₃, f₂]
  rw [hdegη] at f₁ a₂
  rw [a₂]
  erw [f₁]
  ring

end GlobalTheory.ProjCurve
