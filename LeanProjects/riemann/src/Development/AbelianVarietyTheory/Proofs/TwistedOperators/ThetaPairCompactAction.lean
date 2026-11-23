import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterInUnitaryArchimedeanMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairPolynomialCompactStatement

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KExpLine

section Abstract

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def zeroOn (S : Submodule ℂ (SchwartzMap Y ℂ)) (P : Finset Y) : Submodule ℂ S where
  carrier := {s | ∀ y ∈ P, (s : SchwartzMap Y ℂ) y = 0}
  add_mem' := by
    intro a b ha hb y hy
    simp [ha y hy, hb y hy]
  zero_mem' := by
    intro y _
    simp
  smul_mem' := by
    intro c a ha y hy
    simp [ha y hy]

theorem exists_finset_sep (S : Submodule ℂ (SchwartzMap Y ℂ)) [FiniteDimensional ℂ S] :
    ∃ P : Finset Y, ∀ s ∈ S, (∀ y ∈ P, s y = 0) → s = 0 := by
  classical
  obtain ⟨P, -, hmin⟩ := (measure fun P : Finset Y => Module.finrank ℂ (zeroOn S P)).wf.has_min Set.univ
    ⟨∅, trivial⟩
  refine ⟨P, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, s y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (SchwartzMap.ext h)
  have hlt : zeroOn S (insert y P) < zeroOn S P := by
    refine lt_of_le_of_ne (fun a ha z hz => ha z (Finset.mem_insert_of_mem hz)) fun heq => ?_
    have hmem : (⟨s, hs⟩ : S) ∈ zeroOn S P := h0
    rw [← heq] at hmem
    exact hy (hmem y (Finset.mem_insert_self y P))
  exact hmin (insert y P) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem sub_mem_of_hasDerivAt (S T : Submodule ℂ (SchwartzMap Y ℂ)) [FiniteDimensional ℂ S]
    (c d : ℝ → SchwartzMap Y ℂ) (hc : ∀ u, c u ∈ S) (hd : ∀ t, d t ∈ T)
    (hder : ∀ y t, HasDerivAt (fun u => c u y) (d t y) t) : c 1 - c 0 ∈ T := by
  classical
  obtain ⟨P, hP⟩ := exists_finset_sep S
  let E : S →ₗ[ℂ] (P → ℂ) :=
    { toFun := fun s p => (s : SchwartzMap Y ℂ) p
      map_add' := by intro a b; funext p; simp
      map_smul' := by intro a b; funext p; simp }
  have hE : LinearMap.ker E = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    exact Subtype.ext (hP s s.2 fun y hy => congrFun hs ⟨y, hy⟩)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective E hE
  let C : ℝ → (P → ℂ) := fun u p => c u p
  have hCd : ∀ t, HasDerivAt C (fun p => d t p) t := fun t => hasDerivAt_pi.2 fun p => hder p t
  have hLC : ∀ u, L (C u) = ⟨c u, hc u⟩ := fun u => LinearMap.congr_fun hL ⟨c u, hc u⟩
  let ev : SchwartzMap Y ℂ → Y → ℂ := fun g y => g y
  have hcomp : ∀ φ : (P → ℂ) →ₗ[ℂ] ℂ, ∀ t, HasDerivAt (fun u => φ (C u)) (φ (fun p => d t p)) t := fun φ t => by
    have h := (((LinearMap.toContinuousLinearMap φ).restrictScalars ℝ).hasFDerivAt (x := C t)).comp_hasDerivAt t (hCd t)
    simpa [Function.comp_def] using h

  have hdS : ∀ t, ((L (fun p => d t p) : S) : SchwartzMap Y ℂ) = d t := by
    intro t
    ext y
    let evy : S →ₗ[ℂ] ℂ :=
      { toFun := fun s => (s : SchwartzMap Y ℂ) y
        map_add' := by intro a b; simp
        map_smul' := by intro a b; simp }
    have h1 := hcomp (evy ∘ₗ L) t
    have h2 : (fun u => (evy ∘ₗ L) (C u)) = fun u => c u y := by
      funext u
      simp only [LinearMap.comp_apply, hLC u]
      rfl
    rw [h2] at h1
    exact (hder y t).unique h1 |>.symm
  let T' : Submodule ℂ S := T.comap S.subtype
  have hdT : ∀ t, L (fun p => d t p) ∈ T' := fun t => by
    show ((L (fun p => d t p) : S) : SchwartzMap Y ℂ) ∈ T
    rw [hdS t]
    exact hd t
  have key : (⟨c 1, hc 1⟩ : S) - ⟨c 0, hc 0⟩ ∈ T' := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    let ψ : (P → ℂ) →ₗ[ℂ] ℂ := φ ∘ₗ T'.mkQ ∘ₗ L
    have hg : ∀ t, HasDerivAt (fun u => ψ (C u)) 0 t := by
      intro t
      have := hcomp ψ t
      have h0 : ψ (fun p => d t p) = 0 := by
        show φ (T'.mkQ (L (fun p => d t p))) = 0
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T').2 (hdT t), map_zero]
      rwa [h0] at this
    have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
    have e1 : ∀ u, ψ (C u) = φ (Submodule.Quotient.mk ⟨c u, hc u⟩) := fun u => by
      show φ (T'.mkQ (L (C u))) = _
      rw [hLC u]
      rfl
    rw [e1, e1] at hconst
    rw [Submodule.Quotient.mk_sub, map_sub, hconst, sub_self]
  exact key

end Abstract

end GlobalTheory.KExpLine

namespace GlobalTheory.KExpLine

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem sub_mem_span_derivs : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ →
      f₁ - f ∈ Submodule.span ℂ {g₁ | g₁ ∈ M.Pol B.ψ B.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∃ g ∈ M.Pol B.ψ B.emb,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) g g₁} := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f hf f₁ hact
  obtain ⟨hDer, hOp, -, -⟩ := GlobalTheory.T.polynomial_datum_action_of_pair hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨γ, hγL, hγ1, hγK⟩ := GlobalTheory.T.exists_oneParameter_in_unitaryArchimedeanMaxCompact F E σ B n X r s hP.base hP.herm k hk
  obtain ⟨S, hSfin, hS⟩ := GlobalTheory.T.theta_pair_polynomial_compact hPr F E σ B n d X W M χX χW om r s r' s' hP f hf
  haveI := hSfin
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let c : ℝ → SInf F (Fin n × Fin d) := fun t => D t f
  have hcP : ∀ t, c t ∈ M.Pol B.ψ B.emb := fun t => hDP t f hf
  have hcA : ∀ t, Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (c t) := fun t => (hD t f hf (c t)).2 rfl
  have hc1 : c 1 = f₁ := ((hD 1 f hf f₁).1 (by rw [hγ1]; exact hact)).symm
  have hc0 : c 0 = f := by
    have h1 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by
      rw [ofAdd_zero, map_one]
    have hA : Acts (evI F) (om (γ (Multiplicative.ofAdd (0 : ℝ)), 1)) f f := by
      intro ρ _
      rw [h1]
      show om 1 _ = _
      rw [map_one]
      rfl
    exact ((hD 0 f hf f).1 hA).symm
  have hder : ∀ y t, HasDerivAt (fun u => c u y) (Dg (c t) y) t := by
    intro y t
    let ρ := GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)
    let x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (y, 0)
    have hx : (fun i => evI F (x i)) = y := funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv _ _ i
    have hρ : ρ x = 1 := by
      show GlobalTheory.ArchIsom.g0 F (Fin n × Fin d) (fun i => (x i).2) = 1
      have : (fun i => (x i).2) = (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := rfl
      rw [this]
      exact Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts _) _
    have htens : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) ρ x = g y := by
      intro g
      show g (fun i => evI F (x i)) * ρ x = g y
      rw [hx, hρ, mul_one]
    have hom : ∀ u, om (γ (Multiplicative.ofAdd u), 1) (tens (evI F) (⇑f) ρ) = tens (evI F) (⇑(c u)) ρ :=
      fun u => hcA u ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)
    have hsplit : ∀ s', om (γ (Multiplicative.ofAdd (s' + t)), 1) (tens (evI F) (⇑f) ρ) =
        om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) := by
      intro s'
      have e : ((γ (Multiplicative.ofAdd (s' + t)), (1 : UA σ W.J)) : UA σ X.J × UA σ W.J) =
          (γ (Multiplicative.ofAdd s'), 1) * (γ (Multiplicative.ofAdd t), 1) := by
        rw [ofAdd_add, map_mul, Prod.mk_mul_mk, mul_one]
      rw [e, map_mul, Module.End.mul_apply, hom t]
    have h0 := (hDg (c t) (hcP t) (Dg (c t))).2 rfl ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ (c t)) x
    have h0' : HasDerivAt (fun s' => c (s' + t) y) (Dg (c t) y) 0 := by
      have e1 : (fun s' : ℝ => om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) x) =
          fun s' => c (s' + t) y := by
        funext s'
        rw [← hsplit s', hom, htens]
      rw [e1, htens] at h0
      exact h0
    have h2' : HasDerivAt (fun u => c (u - t + t) y) (Dg (c t) y) t := by
      have := h0'
      rw [show (0 : ℝ) = t - t from (sub_self t).symm] at this
      exact this.comp_sub_const t t
    simpa only [sub_add_cancel] using h2'
  rw [← hc1, ← hc0]
  refine sub_mem_of_hasDerivAt S _ c (fun t => Dg (c t)) (fun u => hS _ (hγK _) (c u) (hcA u)) (fun t => ?_) hder
  exact Submodule.subset_span ⟨hDgP _ (hcP t), γ, hγL, c t, hcP t, (hDg (c t) (hcP t) _).2 rfl⟩

end GlobalTheory.KExpLine
