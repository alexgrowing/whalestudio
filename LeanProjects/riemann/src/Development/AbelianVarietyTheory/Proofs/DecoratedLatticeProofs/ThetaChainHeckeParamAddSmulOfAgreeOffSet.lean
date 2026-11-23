import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySatakeTransformEqOfBaseChangeSatakeParameStatement

noncomputable section

namespace GlobalTheory.LFun.ParLin

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SatCompare
open Formalism.MainNotions.SchurIrreducible (IsSplit)

section GLcase
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x x' : V}
  {B : Multiset ℂˣ}

theorem satGL_add (hx : IsSatVecGL w ρ x B) (hx' : IsSatVecGL w ρ x' B) (h0 : x + x' ≠ 0) :
    IsSatVecGL w ρ (x + x') B :=
  ⟨h0, add_mem hx.2.1 hx'.2.1, hx.2.2.1, fun ϖ hϖ j hj => by
    have e := (heckeLin (Final.GLintComm E w n) (Tj_mem_hecke hϖ j) ρ).map_add x x'
    simp only [heckeLin_apply] at e
    rw [e, hx.2.2.2 ϖ hϖ j hj, hx'.2.2.2 ϖ hϖ j hj, smul_add]⟩

theorem satGL_smul (hx : IsSatVecGL w ρ x B) {a : ℂ} (ha : a ≠ 0) : IsSatVecGL w ρ (a • x) B :=
  ⟨smul_ne_zero ha hx.1, Submodule.smul_mem _ a hx.2.1, hx.2.2.1, fun ϖ hϖ j hj => by
    rw [heckeVec_smul (Final.GLintComm E w n) (Tj_mem_hecke hϖ j), hx.2.2.2 ϖ hϖ j hj, smul_comm]⟩

end GLcase

section Ucase
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ϖ : L} {q : ℕ} {ρ : Representation ℂ (GU c n) V} {x x' : V}
  {α : Fin (n / 2) → ℂˣ}

theorem satU_add (hU : IsUnramInv ϖ c q) (hx : IsSatVecU ϖ q ρ x α) (hx' : IsSatVecU ϖ q ρ x' α) (h0 : x + x' ≠ 0) :
    IsSatVecU ϖ q ρ (x + x') α :=
  ⟨h0, add_mem hx.2.1 hx'.2.1, fun t ht => by
    have e := (heckeLin (P.isCommensurated_integral_unitary_of_unramified hU n) ht ρ).map_add x x'
    simp only [heckeLin_apply] at e
    rw [e, hx.2.2 t ht, hx'.2.2 t ht, smul_add]⟩

theorem satU_smul (hU : IsUnramInv ϖ c q) (hx : IsSatVecU ϖ q ρ x α) {a : ℂ} (ha : a ≠ 0) :
    IsSatVecU ϖ q ρ (a • x) α :=
  ⟨smul_ne_zero ha hx.1, Submodule.smul_mem _ a hx.2.1, fun t ht => by
    rw [heckeVec_smul (P.isCommensurated_integral_unitary_of_unramified hU n) ht, hx.2.2 t ht, smul_comm]⟩

end Ucase

section Vec
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {x x' : V} {B : Multiset ℂˣ}

theorem paramVec_smul (hx : IsParamVec σ J L h ρ x B) {a : ℂ} (ha : a ≠ 0) : IsParamVec σ J L h ρ (a • x) B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, satGL_smul hx ha⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, satU_smul hU hx ha, hB⟩

theorem paramVec_add (hx : IsParamVec σ J L h ρ x B) (hx' : IsParamVec σ J L h ρ x' B) (h0 : x + x' ≠ 0) :
    IsParamVec σ J L h ρ (x + x') B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, satGL_add hx (hx'.isSatVecGL hv he) h0⟩
  · rcases hx' with ⟨hv, -⟩ | ⟨-, c', ϖ', e', α', hU', he', hx', hB'⟩
    · exact absurd hv (not_isSplit_of_isInertAt hw)
    · obtain rfl : c' = c := (InertChart.existsUnique_isConjAt σ hw h).unique he'.1 he.1
      have h1 := IsSatVecU.of_unif hU' hU (IsSatVecU.of_chart he' he hx')
      have h2 : IsSatVecU ϖ (qV F v) (ρ.comp e.symm.toMonoidHom) x' α := ⟨h1.1, h1.2.1, fun t ht => by
        rw [h1.2.2 t ht, GlobalTheory.T.unitarySatakeTransform_eq_of_baseChangeSatakeParameter_eq (w.adicCompletion E) ϖ c' (qV F v) n hU α' α (hB'.symm.trans hB) t ht]⟩
      exact Or.inr ⟨hw, c', ϖ, e, α, hU, he, satU_add hU hx h2 h0, hB⟩

end Vec

end GlobalTheory.LFun.ParLin

noncomputable section

namespace GlobalTheory.LFun.ParLin

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

section Fun
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {S : Set (HeightOneSpectrum (𝓞 F))} {V : Type} [AddCommGroup V] [Module ℂ V] {f f' : GAd σ J → V} {B B' : Fam E}

theorem paramFun_of_agree (hf : IsParamFun σ J L S f B') (hB : ∀ w ∉ above E S, B w = B' w) :
    IsParamFun σ J L S f B := fun v hv w h => by
  have hw : w ∉ above E S := fun hm => hv (h ▸ hm)
  rw [hB w hw]
  exact hf v hv w h

theorem paramFun_add (hf : IsParamFun σ J L S f B) (hf' : IsParamFun σ J L S f' B) (h0 : f + f' ≠ 0) :
    IsParamFun σ J L S (f + f') B := fun v hv w h => paramVec_add (hf v hv w h) (hf' v hv w h) h0

theorem paramFun_smul (hf : IsParamFun σ J L S f B) {a : ℂ} (ha : a ≠ 0) : IsParamFun σ J L S (a • f) B :=
  fun v hv w h => paramVec_smul (hf v hv w h) ha

end Fun

end GlobalTheory.LFun.ParLin

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LFun.ParLin in

theorem isPar_add_smul : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' →
    (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) →
    u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  intro D c s
  have cne : ∀ f : GA D s.V → ℂ, f ≠ 0 → (fun g => conj (f g)) ≠ 0 := fun f hf h0 =>
    hf (funext fun g => by simpa using congrFun h0 g)
  refine ⟨fun u u' B B' a hu hu' hB h0 => ⟨h0, fun v hv => ?_⟩, fun u B a hu ha => ⟨smul_ne_zero ha hu.1, fun v hv => ?_⟩⟩
  · have hval : PiLocalization₂.val (u + a • u') v = PiLocalization₂.val u v + a • PiLocalization₂.val u' v := by simp [PiLocalization₂.val]
    have hc : (fun g => conj (PiLocalization₂.val (u + a • u') v g)) =
        (fun g => conj (PiLocalization₂.val u v g)) + (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    by_cases h1 : PiLocalization₂.val u v = 0
    · have h2 : a • PiLocalization₂.val u' v ≠ 0 := by rw [hval, h1, zero_add] at hv; exact hv
      have ha : a ≠ 0 := fun e => h2 (by simp [e])
      have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
      have hz : (fun g => conj (PiLocalization₂.val u v g)) = 0 := by funext g; simp [h1]
      rw [hz, zero_add]
      exact paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)
    · by_cases h2 : a • PiLocalization₂.val u' v = 0
      · have hz : (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) = 0 := by
          funext g
          have := congrFun h2 g
          simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
          rw [← map_mul, this, map_zero]
        rw [hz, add_zero]
        exact hu.2 v h1
      · have ha : a ≠ 0 := fun e => h2 (by simp [e])
        have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
        refine paramFun_add (hu.2 v h1) (paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)) ?_
        rw [← hc]
        exact cne _ hv
  · have hval : PiLocalization₂.val (a • u) v = a • PiLocalization₂.val u v := by simp [PiLocalization₂.val]
    have hu0 : PiLocalization₂.val u v ≠ 0 := fun e => hv (by rw [hval, e, smul_zero])
    have hc : (fun g => conj (PiLocalization₂.val (a • u) v g)) = (conj a) • (fun g => conj (PiLocalization₂.val u v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    exact paramFun_smul (hu.2 v hu0) (by simpa using ha)

end GlobalTheory.ChainOnto

example : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D) (s : GlobalTheory.ChainOnto.PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), GlobalTheory.ChainOnto.IsPar u B → GlobalTheory.ChainOnto.IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → GlobalTheory.ChainOnto.IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), GlobalTheory.ChainOnto.IsPar u B → a ≠ 0 → GlobalTheory.ChainOnto.IsPar (a • u) B := GlobalTheory.ChainOnto.isPar_add_smul
