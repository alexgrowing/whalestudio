import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.CountL

theorem length_le_of_semilinear {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (hf : Function.Injective f) : Module.length R M ≤ Module.length S N := by
  have : RingHomSurjective σ := ⟨hσ⟩
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_strictMono (Submodule.map f) (Submodule.map_strictMono_of_injective hf)

theorem length_le_inf_comap_add {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (C : Submodule R M) (A H : Submodule S N) (hC : ∀ x ∈ C, f x ∈ A) :
    Module.length R ↥C ≤
      Module.length R ↥(C ⊓ H.comap f) + Module.length S (↥A ⧸ H.comap A.subtype) := by
  let g : ↥C →ₛₗ[σ] (↥A ⧸ H.comap A.subtype) :=
    (H.comap A.subtype).mkQ.comp ((f.domRestrict C).codRestrict A fun x => hC x x.2)
  have hg : ∀ x : ↥C, x ∈ LinearMap.ker g → f x ∈ H := fun x hx =>
    (Submodule.Quotient.mk_eq_zero (H.comap A.subtype)).1 hx
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype (LinearMap.ker g).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)]
  refine add_le_add ?_ ?_
  · refine Module.length_le_of_injective
      ((C.subtype.comp (LinearMap.ker g).subtype).codRestrict (C ⊓ H.comap f)
        fun x => ⟨x.1.2, hg x.1 x.2⟩) ?_
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  · refine length_le_of_semilinear hσ ((LinearMap.ker g).liftQ g le_rfl) ?_
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem exists_le_forall_le {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (K : ι → Submodule R M) (C : Submodule R M) (b : ℕ∞)
    (h : ∀ q, ∀ C₀ ≤ C, Module.length R ↥C₀ ≤ Module.length R ↥(C₀ ⊓ K q) + b) (Q : Finset ι) :
    ∃ C' : Submodule R M, C' ≤ C ∧ (∀ q ∈ Q, C' ≤ K q) ∧
      Module.length R ↥C ≤ (Q.card : ℕ∞) * b + Module.length R ↥C' := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨C₀, h₁, h₂, h₃⟩ := ih
    refine ⟨C₀ ⊓ K a, inf_le_left.trans h₁, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact inf_le_right
      · exact inf_le_left.trans (h₂ q hq)
    · rw [Finset.card_insert_of_notMem ha]
      refine h₃.trans ((add_le_add le_rfl (h a C₀ h₁)).trans (le_of_eq ?_))
      push_cast
      ring

theorem length_quot_natCast_le {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (p : ℕ) :
    Module.length S (S ⧸ Ideal.span {(p : S)}) ≤ Module.length R (R ⧸ Ideal.span {(p : R)}) := by
  refine length_le_of_semilinear (σ := e.symm.toRingHom) e.symm.surjective
    (Submodule.mapQ (Ideal.span {(p : S)}) (Ideal.span {(p : R)}) e.symm.toRingHom.toSemilinearMap ?_) ?_
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨e.symm y, by
      show _ = e.symm (y * p)
      simp⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : e.symm x ∈ Ideal.span {(p : R)} := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx'
    refine (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton'.2 ⟨e y, ?_⟩)
    simpa using congrArg e hy

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

noncomputable def locFunS {D : D7} (i : D.nd.Loc) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    (GE D.nd → KOG (D.nd.O i) k) →ₛₗ[(D.nbr i w hw).eO.toRingHom]
      (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) where
  toFun := locFun i M w hw
  map_add' a b := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_add _ _
  map_smul' c a := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_smulₛₗ c _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (e : ℕ), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs M e ∧ ∀ f ∈ C, InCut i r Xs M w hw f) → ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ f ∈ C', IsFinL i M f) ∧ Module.length (D.nd.O i) ↥C ≤ (((placesOver D.host.E (D.nd.l i)).ncard * e : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) + Module.length (D.nd.O i) ↥C' := by
  intro D i r Xs k M C e h
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin := finite_placesOver D.host.E (D.nd.l i) hl.ne_zero
  letI : Fintype ↥(placesOver D.host.E (D.nd.l i)) := hfin.fintype
  obtain ⟨C', h₁, h₂, h₃⟩ := exists_le_forall_le
    (fun q : ↥(placesOver D.host.E (D.nd.l i)) =>
      (HfD (Br.PD D.loc D.nbr i q.1 q.2) (Br.locLat D.nbr i q.1 q.2 M)).comap (locFunS i M q.1 q.2))
    C ((e : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i)) (by
      rintro ⟨w, hw⟩ C₀ hC₀
      refine (length_le_inf_comap_add (D.nbr i w hw).eO.surjective (locFunS i M w hw) C₀
        (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M)) _
        (fun f hf => (h w hw).2 f (hC₀ hf))).trans (add_le_add le_rfl ?_)
      refine le_trans (h w hw).1 (mul_le_mul' le_rfl ?_)
      unfold lenOl lenQ
      rw [Br.PD_p]
      exact length_quot_natCast_le (D.nbr i w hw).eO _) Finset.univ
  refine ⟨C', h₁, fun f hf w hw => h₂ ⟨w, hw⟩ (Finset.mem_univ _) hf, ?_⟩
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← mul_assoc] at h₃
  rw [Nat.cast_mul]
  exact h₃

end GlobalTheory.Cut.CountL
