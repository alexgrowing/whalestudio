import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjOfFrobeniusMatchStatement

noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleGal
open GlobalTheory.TypeLeaf (FrobDense)

theorem exists_aut {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    (φ ψ : O →+* Qbar l) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφ' : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (hψ' : ∀ z : ℤ_[l], ψ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ γ : Qbar l ≃+* Qbar l, ∀ x, γ (φ x) = ψ x := by
  have halg : Algebra.IsAlgebraic ℤ_[l] (Qbar l) :=
    haveI := IsLocalization.isAlgebraic (R := ℤ_[l]) ℚ_[l] (nonZeroDivisors ℤ_[l])
    Algebra.IsAlgebraic.trans ℤ_[l] ℚ_[l] (Qbar l)
  have key : ∀ (f : O →+* Qbar l) (hf : Function.Injective f),
      (∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) →
      letI := f.toAlgebra
      haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
      IsAlgClosure O (Qbar l) := fun f hf hf' => by
    letI := f.toAlgebra
    haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
    haveI : IsScalarTower ℤ_[l] O (Qbar l) := IsScalarTower.of_algebraMap_eq fun z => (hf' z).symm
    have hi : Function.Injective (algebraMap ℤ_[l] O) := fun x y h => by
      have := (hf' x).symm.trans ((congrArg f h).trans (hf' y))
      exact Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective this)
    exact ⟨inferInstance, Algebra.IsAlgebraic.extendScalars hi⟩
  let e := @IsAlgClosure.equiv O _ _ (Qbar l) (Qbar l) _ _ ψ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ ψ.toAlgebra _ _ |>.2 hψ) (key ψ hψ hψ') φ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ φ.toAlgebra _ _ |>.2 hφ) (key φ hφ hφ')
  exact ⟨@AlgEquiv.toRingEquiv O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e,
    fun x => @AlgEquiv.commutes O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e x⟩

variable {D : D7} {T : WDTie D.nd D.naut} {i : D.ntw.Tw} {j : FractionRing (D.ntw.O0 i) →+* ℂ}
  {ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i)} {π : D.naut.CG D.R.r} {s : ℝ}

theorem exists_conj (hF : FrobDense D) (hG : GalHodge D T) (hc : D.naut.csd π) (hr : RegAlgShift D.naut π s)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))
    (hM : FrobMatch D π (rd i j) ρ (s + (1 - (D.R.r : ℝ)) / 2))
    {φ : D.ntw.O0 i →+* Qbar (D.ntw.l i)} {ι : Qbar (D.ntw.l i) ≃+* ℂ} (hφ : Continuous φ)
    (hι : ∀ x, ι (φ x) = rd i j x) (hs : IsSSRep (mapRep φ ρ)) :
    ∃ r A, IsAttachedHodge D T ι π s r ∧ ∀ g, mapRep φ ρ g = A * r g * A⁻¹ := by
  obtain ⟨r, h⟩ := hG _ ι π s hc hr
  have e : ι.toRingHom.comp φ = rd i j := RingHom.ext hι
  obtain ⟨A, hA⟩ := GlobalTheory.T.conj_of_frobenius_match D T hF _ ι _ π s r (mapRep φ ρ) h.toIsAttachedAway (hρ.matrix_map hφ) hs
    (hM.mono fun w hw B σ hB hσ => by
      rw [← hw B σ hB hσ, ← e, ← Polynomial.map_map, ← Matrix.charpoly_map _ φ]
      rfl)
  exact ⟨r, A, h, hA⟩

def brEmb (i : D.ntw.Tw) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) : D.ntw.O0 i →+* Qbar (D.ntw.l i) :=
  (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).comp (D.ntwbr i v hv).toLL

theorem isModel_brEmb (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    IsModel (D.ntwbr i v hv) (resDec D.nd.plOm.1 (mapRep (brEmb i v hv) ρ) v) (D.ntwbr i v hv).LL
      (mapRep (D.ntwbr i v hv).toLL (ρ.comp (DecV D.nd v).subtype)) :=
  ⟨le_rfl, by ext g a b; rfl⟩

theorem exists_conj_br (hF : FrobDense D) (hG : GalHodge D T) (hc : D.naut.csd π) (hr : RegAlgShift D.naut π s)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))
    (hM : FrobMatch D π (rd i j) ρ (s + (1 - (D.R.r : ℝ)) / 2))
    {φ : D.ntw.O0 i →+* Qbar (D.ntw.l i)} {ι : Qbar (D.ntw.l i) ≃+* ℂ}
    (hφ : ∀ z : ℤ_[D.ntw.l i], φ (algebraMap _ _ z) = algebraMap ℚ_[D.ntw.l i] _ (z : ℚ_[D.ntw.l i]))
    (hι : ∀ x, ι (φ x) = rd i j x) (hs : IsSSRep (mapRep φ ρ))
    (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    ∃ (ι' : Qbar (D.ntw.l i) ≃+* ℂ) (r : _) (A : GL (Fin D.R.r) (Qbar (D.ntw.l i))),
      (∀ x, ι' (brEmb i v hv x) = rd i j x) ∧ IsAttachedHodge D T ι' π s r ∧
      ∀ g, resDec D.nd.plOm.1 (mapRep (brEmb i v hv) ρ) v g = A * resDec D.nd.plOm.1 r v g * A⁻¹ := by
  have hj : Function.Injective (rd i j) := j.injective.comp (IsFractionRing.injective _ _)
  have h1 : Function.Injective φ := fun x y h => hj (by rw [← hι, ← hι, h])
  have h2 : Function.Injective (brEmb i v hv) :=
    (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).injective.comp (GlobalTheory.EmbInj.toLL_inj _)
  obtain ⟨γ, hγ⟩ := exists_aut φ (brEmb i v hv) h1 h2 hφ fun z =>
    congrArg (fun y : ↥(OL (D.ntwbr i v hv).LL) => ((y : ↥(D.ntwbr i v hv).LL.1) : Om (D.ntw.l i)))
      ((D.ntwbr i v hv).eO_alg z)
  have h3 : ∀ x, (γ.symm.trans ι) (brEmb i v hv x) = rd i j x := fun x => by
    rw [← hγ, RingEquiv.trans_apply, γ.symm_apply_apply, hι]
  have h4 : mapRep (brEmb i v hv) ρ = mapRep γ.toRingHom (mapRep φ ρ) := by
    ext g a b
    exact (hγ _).symm
  obtain ⟨r, A, h, hA⟩ := exists_conj hF hG hc hr hρ hM (φ := brEmb i v hv)
    (continuous_subtype_val.comp (continuous_subtype_val.comp (D.ntwbr i v hv).eO_cont)) h3
    (h4 ▸ GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ _ _ _ hs)
  exact ⟨_, r, A, h3, h, fun g => hA g⟩

theorem att_of_frobMatch (hF : FrobDense D) (hG : GalHodge D T) (hc : D.naut.csd π) (hr : RegAlgShift D.naut π s)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))
    (hM : FrobMatch D π (rd i j) ρ (s + (1 - (D.R.r : ℝ)) / 2))
    {φ : D.ntw.O0 i →+* Qbar (D.ntw.l i)} {ι : Qbar (D.ntw.l i) ≃+* ℂ} (hφc : Continuous φ)
    (hφ : ∀ z : ℤ_[D.ntw.l i], φ (algebraMap _ _ z) = algebraMap ℚ_[D.ntw.l i] _ (z : ℚ_[D.ntw.l i]))
    (hι : ∀ x, ι (φ x) = rd i j x) (hs : IsSSRep (mapRep φ ρ)) :
    Att D.naut (bk0 D) i j ρ π (s + (1 - (D.R.r : ℝ)) / 2) := by
  have hj : Function.Injective (rd i j) := j.injective.comp (IsFractionRing.injective _ _)
  have h1 : Function.Injective φ := fun x y h => hj (by rw [← hι, ← hι, h])
  obtain ⟨r, A, h, hA⟩ := exists_conj hF hG hc hr hρ hM hφc hι hs
  refine ⟨fun w hw hu σ hσ => ?_, fun w hw hu B σ hB hσ => ?_, fun w hw => h.temp w hw, fun v hv => ?_,
    fun v hv τ τc hτ a => ?_⟩
  · have h2 := hA σ
    rw [(h.toIsAttachedAway.frob hw hu).1 σ hσ, mul_one, mul_inv_cancel] at h2
    refine Units.ext (Matrix.map_injective h1 ?_)
    exact (congrArg Units.val h2).trans (Matrix.map_one φ (map_zero φ) (map_one φ)).symm
  · rw [← (h.toIsAttachedAway.frob hw hu).2 B σ hB hσ, ← (RingHom.ext hι : ι.toRingHom.comp φ = rd i j),
      ← Polynomial.map_map, ← Matrix.charpoly_map _ φ]
    have h2 : ((mapRep φ ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i))).charpoly =
        ((r σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i))).charpoly := by
      rw [hA, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact congrArg (Polynomial.map ι.toRingHom) h2
  · obtain ⟨ι', r', A', -, h', hA'⟩ := exists_conj_br hF hG hc hr hρ hM hφ hι hs v hv
    obtain ⟨a1, a2, a3⟩ := h'.above v hv _ (D.ntwbr i v hv) (D.ntwbr_ind i v hv)
    obtain ⟨b1, b2, b3, -⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant _ (D.loc _) _ _ _ _ (D.ntwbr i v hv) _ _ _ A' hA'
    exact ⟨((isModel_brEmb v hv).isdRAt_iff _).1 (b1 a1.deRham),
      fun hu => ((isModel_brEmb v hv).isCrysAt_iff _).1 (b2 (a2 hu)),
      fun hu => ((isModel_brEmb v hv).isPotCrysAt_iff _).1 (b3 (a3 hu))⟩
  · obtain ⟨ι', r', A', hι', h', hA'⟩ := exists_conj_br hF hG hc hr hρ hM hφ hι hs v hv
    obtain ⟨a1, -, -⟩ := h'.above v hv _ (D.ntwbr i v hv) (D.ntwbr_ind i v hv)
    obtain ⟨-, -, -, b4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant _ (D.loc _) _ _ _ _ (D.ntwbr i v hv) _ _ _ A' hA'
    let c : D.host.E →+* ↥(D.ntwbr i v hv).Kw.1 :=
      ((D.ntwbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)).codRestrict (D.ntwbr i v hv).Kw.1 (D.ntwbr i v hv).j_E
    let τ₀ : D.host.E →+* Qbar (D.ntw.l i) :=
      (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).comp ((AlgHom.toRingHom τ).comp c)
    have hi : IsInduced (D.ntwbr i v hv) τ₀ τ := fun _ => rfl
    have e : ι'.toRingHom.comp τ₀ = τc := by
      ext x
      obtain ⟨n, d, hd, hnd⟩ := GlobalTheory.EmbInj.exists_frac (D.ntwbr i v hv) (τ (c x))
      have h3 := (map_mul (ι'.toRingHom.comp (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i)))) _ _).symm.trans
        (congrArg _ hnd)
      have h4 : rd i j d * ι' (τ₀ x) = rd i j n := by rw [← hι', ← hι']; exact h3
      exact mul_left_cancel₀ ((map_ne_zero_iff _ hj).2 hd) (h4.trans (hτ x n d ⟨hd, hnd⟩).symm)
    obtain ⟨J, hJ, hJ'⟩ := a1.jumps τ₀ _ τ hi
    refine ((b4 τ₀ J hJ').count_eq _ (isModel_brEmb v hv) hi a).symm.trans ?_
    rw [e] at hJ
    rw [← Multiset.count_map_eq_count' (fun n : ℤ => (n : ℂ)) J Int.cast_injective, hJ]
    congr 2
    refine Multiset.map_congr rfl fun z _ => ?_
    push_cast
    ring

end GlobalTheory.TripleLocal

end
