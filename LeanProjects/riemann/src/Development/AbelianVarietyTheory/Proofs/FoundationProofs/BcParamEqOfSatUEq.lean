import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeylConjugateOfUnitarySatakeDiagDoubleCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariantStatement

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun.Orbit
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (WeylConjU bcParam bcParam_of_weylConj)

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ ϖ' : L}

theorem exists_dosetInd_eq (hU : IsUnramInv ϖ σ q) (hU' : IsUnramInv ϖ' σ q) {d : Fin n → ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    ∃ t' : GU σ n, t'.1.1 = Matrix.diagonal (fun i => ϖ' ^ d i) ∧ dosetInd ℂ (KU σ n) t' = dosetInd ℂ (KU σ n) t := by
  have h0 := GlobalTheory.InertThetaCompare.unif_ne_zero hU
  have h0' := GlobalTheory.InertThetaCompare.unif_ne_zero hU'
  have hv : ∀ a : ℤ, Valued.v (ϖ ^ a) = WithZero.exp (-a) := fun a => by
    simpa using GlobalTheory.InertThetaCompare.val_prod_zpow (ϖ := ϖ) hU.2.2.2.1 (Finset.univ : Finset Unit) fun _ => a
  have hd : ∀ i, d i + d i.rev = 0 := fun i => by
    have h1 := P.fSatake_unit_diag (P.fSatake_borel_of_diag ht) i
    rw [ht, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, hU.2.2.1, ← zpow_add₀ h0] at h1
    have h2 := hv (d i + d i.rev)
    rw [h1, map_one, eq_comm, WithZero.exp_eq_one] at h2
    omega
  obtain ⟨k, hk, hk'⟩ := P.fSatake_diag_exists (σ := σ) (fun i : Fin n => (ϖ' / ϖ) ^ d i) fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.1, hU'.2.2.1, ← zpow_add₀ (div_ne_zero h0' h0), hd, zpow_zero]
  have hK : k ∈ KU σ n := P.fSatake_diag_mem_K hk hk' fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.2.1, hU'.2.2.2.1, div_self WithZero.coe_ne_zero, one_zpow]
  refine ⟨t * k, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Units.val_mul, ht, hk, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← mul_zpow, mul_div_cancel₀ _ h0]
  · rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem
      (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k, hK, by rw [one_mul]⟩)]

variable [CompleteSpace L] {V : Type} [AddCommGroup V] [Module ℂ V] {α β : Fin (n / 2) → ℂˣ}

theorem satU_of_weylConj (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) (e : WeylConjU α β) :
    SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h (fun i => (β i : ℂ)) :=
  unitarySatakeTransform_weylConjugate_invariant GlobalTheory.T.unitarySatake_weylInvariant hU hh e

theorem weylConj_of_dosetInd (hU : IsUnramInv ϖ σ q)
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) = SatU ϖ q (dosetInd ℂ (KU σ n) t) fun i => (β i : ℂ)) :
    WeylConjU α β := weylConjugate_of_unitarySatake_diagDoubleCosets GlobalTheory.T.unitarySatake_weylInvariant hU h

theorem satU_eq_iff_weylConj (hU : IsUnramInv ϖ σ q) :
    (∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) ↔ WeylConjU α β :=
  ⟨fun h => weylConj_of_dosetInd hU fun _ _ _ _ => h _ (Final.DosetIndMem _ _ _ _),
    fun e _ hh => satU_of_weylConj hU hh e⟩

theorem bcParam_eq_of_satU_eq (hU : IsUnramInv ϖ σ q)
    (h : ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) :
    bcParam n α = bcParam n β := bcParam_of_weylConj ((satU_eq_iff_weylConj hU).1 h)

variable {ρ : Representation ℂ (GU σ n) V} {x : V}

theorem IsSatVecU.unique (hU : IsUnramInv ϖ σ q) (h : IsSatVecU ϖ q ρ x α) (h' : IsSatVecU ϖ q ρ x β) :
    WeylConjU α β :=
  (satU_eq_iff_weylConj hU).1 fun t ht => smul_left_injective ℂ h.1 ((h.2.2 t ht).symm.trans (h'.2.2 t ht))

theorem HasSatU.unique (hU : IsUnramInv ϖ σ q) (h : HasSatU ϖ q ρ α) (h' : HasSatU ϖ q ρ β) : WeylConjU α β := by
  obtain ⟨x, hx⟩ := h.exists_vec
  exact hx.unique hU (h'.2 x hx.2.1 hx.1)

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Place

variable {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

theorem toCompl_surjective (h : w.under (𝓞 F) = v) : Function.Surjective (toCompl h) := fun y => by
  obtain ⟨a, ha⟩ := (finAdEquiv F E).surjective (Neutral.B1.finiteSingle E w y)
  refine ⟨_, (finAdEquiv_apply h a).symm.trans ?_⟩
  rw [ha]
  classical exact Pi.mulSingle_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w y

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {V : Type} [AddCommGroup V] [Module ℂ V] {h : w.under (𝓞 F) = v}

theorem IsConjAt.unique {c c' : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
    (hc' : IsConjAt σ h c') : c = c' := RingHom.ext fun y => by
  obtain ⟨z, rfl⟩ := toCompl_surjective h y
  rw [hc, hc']

variable {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {B B' : Multiset ℂˣ}

theorem IsParamVec.unique (hx : IsParamVec σ J L h ρ x B) (hx' : IsParamVec σ J L h ρ x B') : B = B' := by
  by_cases hv : IsSplit (E := E) v
  · exact hx.unique_of_isSplit hv hx'
  obtain ⟨-, c, ϖ, e, α, hU, he, hα, rfl⟩ := hx.resolve_left fun h => hv h.1
  obtain ⟨-, c', ϖ', e', β, hU', he', hβ, rfl⟩ := hx'.resolve_left fun h => hv h.1
  obtain rfl := he.1.unique he'.1
  exact bcParam_of_weylConj (((hα.of_chart he he').of_unif hU hU').unique hU' hβ)

theorem HasParam.unique (hρ : HasParam σ J L h ρ B) (hρ' : HasParam σ J L h ρ B') : B = B' := by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact hx.unique (hρ'.isParamVec hx.mem_fixed hx.ne_zero)

theorem IsSysParam.unique {c : List ℤ → ℂ} (hc : IsSysParam σ n h c B) (hc' : IsSysParam σ n h c B') : B = B' := by
  rcases hc with ⟨hv, hB, hc⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, hc⟩ <;>
    rcases hc' with ⟨hv', hB', hc'⟩ | ⟨hw', τ', ϖ', β, hU', hτ', rfl, hc'⟩
  · exact eq_of_satEig_eq (qV_ne_zero w) hB hB' fun j hj => (hc j hj).symm.trans (hc' j hj)
  · exact absurd hv (not_isSplit_of_isInertAt hw')
  · exact absurd hv' (not_isSplit_of_isInertAt hw)
  · obtain rfl := hτ.unique hτ'
    refine bcParam_of_weylConj (weylConj_of_dosetInd hU fun d t hd ht => ?_)
    obtain ⟨t', ht', e⟩ := exists_dosetInd_eq hU hU' ht
    rw [← hc d t hd ht, hc' d t' hd ht', e, satU_indep hU hU' (Final.DosetIndMem _ _ _ _)]

end Place

section Global

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {S : Set (HeightOneSpectrum (𝓞 F))} {V : Type} [AddCommGroup V] [Module ℂ V]
  {Vl : HeightOneSpectrum (𝓞 F) → Type} [∀ v, AddCommGroup (Vl v)] [∀ v, Module ℂ (Vl v)]
  {π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)} {c c' : Fam E} {w : HeightOneSpectrum (𝓞 E)}

theorem HasParamOff.unique (h : HasParamOff σ J L S π c) (h' : HasParamOff σ J L S π c') (hw : w ∉ above E S) :
    c w = c' w := (h _ hw w rfl).unique (h' _ hw w rfl)

theorem IsParamVecOff.unique {ρ : Representation ℂ (GAd σ J) V} {x : V} (h : IsParamVecOff σ J L S ρ x c)
    (h' : IsParamVecOff σ J L S ρ x c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem IsSysParamOff.unique {s : HeightOneSpectrum (𝓞 E) → List ℤ → ℂ} (h : IsSysParamOff σ n S s c)
    (h' : IsSysParamOff σ n S s c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem LSTw_congr (h : ∀ w ∉ above E S, c w = c' w) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (s : ℂ) :
    LSTw S c m s = LSTw S c' m s := eulerProd_congr (fun w hw => by rw [twist, twist, h w hw]) s

end Global

end GlobalTheory.LFun

end
