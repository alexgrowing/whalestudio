import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.CptKeeps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_quot {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_quot {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isPair_smaller {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_quot h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_quot h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem acts_pure {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ}
    (hM : M.IsGood ψ) {Op : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ}
    {T : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d)} (hT : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) Op (⇑f) (⇑(T f)))
    (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) : Op (pure f φ) = pure (T f) φ := by
  have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hM.std).mono fun v hv => hv.1.trans hv.2
  exact hT f _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd)

end GlobalTheory.ThK.CptKeeps

open GlobalTheory.ThK.CptKeeps in

theorem GlobalTheory.ThK.CptKeeps.polData_so_stable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V' B.emb, ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), om' (k, 1) Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hm k hk Φ hΦ
  have hP := isPair_smaller hm.triple
  have h1 : (1 : UA σ G.W.J) ∈ UAt σ G.W (evI F) := by
    intro u _
    show u • (mat (1 : UA σ G.W.J) - 1) = 0
    have : mat (1 : UA σ G.W.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  obtain ⟨T, hT1, -⟩ := GlobalTheory.T.weil_representation_unitary_equiv hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om'
    G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) hP.base hP.herm hP.skew hP.good hP.weil k hk.1 1 h1
  obtain ⟨D, hDmem, hD⟩ := (GlobalTheory.T.polynomial_datum_action_of_pair hKP.base F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om'
    G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) hP).2.1 k hk
  have hTpol : ∀ f ∈ G.M'.Pol B.ψ B.emb, T f ∈ G.M'.Pol B.ψ B.emb := fun f hf => by
    rw [(hD f hf (T f)).1 (hT1 f)]; exact hDmem f hf
  have hpure := fun f φ hSB hvac => acts_pure hP.good (Op := om' (k, 1)) (T := T) hT1 f φ hSB hvac
  refine ⟨?_, ?_⟩
  · have hle : PolData B G.M' ≤ (PolData B G.M').comap (om' (k, 1)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, hf, φ, hSB, hvac, rfl⟩
      show om' (k, 1) (pure f φ) ∈ PolData B G.M'
      rw [hpure f φ hSB hvac]
      exact Submodule.subset_span ⟨T f, hTpol f hf, φ, hSB, hvac, rfl⟩
    exact hle hΦ.1
  · have hle : G.M'.So B.ψ B.τ₁ ≤ (G.M'.So B.ψ B.τ₁).comap (om' (k, 1)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, φ, hSB, hvac, h₁, rfl⟩
      show om' (k, 1) (pure f φ) ∈ G.M'.So B.ψ B.τ₁
      rw [hpure f φ hSB hvac]
      exact Submodule.subset_span ⟨T f, φ, hSB, hvac, h₁, rfl⟩
    exact hle hΦ.2
