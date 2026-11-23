import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LocalisationCoefficientExtensionIsWildInertiaCyc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.Take

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

section Plain

variable {Γ₀ Γ₁ : Type} [Group Γ₀] [Group Γ₁] {X₀ X₁ : Type} {A : Type} [CommRing A] {n r t : ℕ}

def pull (A : Type) [CommRing A] (e : X₁ ≃ X₀) : (X₀ → A) ≃ₐ[A] (X₁ → A) where
  toFun f := fun x => f (e x)
  invFun f := fun x => f (e.symm x)
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def pullT (e : X₁ ≃ X₀) (T : Subalgebra A (X₀ → A)) : Subalgebra A (X₁ → A) :=
  T.map (pull A e : (X₀ → A) →ₐ[A] (X₁ → A))

theorem pull_mem (e : X₁ ≃ X₀) {T : Subalgebra A (X₀ → A)} {f : X₀ → A} (hf : f ∈ T) :
    (fun x => f (e x)) ∈ pullT e T := ⟨f, hf, rfl⟩

def pullR (e : X₁ ≃ X₀) (γ : Γ₁ ≃* Γ₀) (rep : X₀ → (Γ₀ →* GL (Fin n) A)) : X₁ → (Γ₁ →* GL (Fin n) A) :=
  fun x => (rep (e x)).comp γ.toMonoidHom

variable (e : X₁ ≃ X₀) (γ : Γ₁ ≃* Γ₀)

theorem inRing_pull {T : Subalgebra A (X₀ → A)} {rep : X₀ → (Γ₀ →* GL (Fin n) A)}
    {a : X₀ → Matrix (Fin n) (Fin n) A} (h : InRing T rep a) :
    InRing (pullT e T) (pullR e γ rep) (fun x => a (e x)) := by
  obtain ⟨m, f, g, hf, rfl⟩ := h
  refine ⟨m, fun k x => f k (e x), fun k => γ.symm (g k), fun k => pull_mem e (hf k), ?_⟩
  funext x
  simp [pullR, mat, Finset.sum_apply]

theorem inCongruenceModule_pull_equivPoints {T : Subalgebra A (X₀ → A)} {rep : X₀ → (Γ₀ →* GL (Fin n) A)} {π : X₁}
    {a s : X₀ → Matrix (Fin n) (Fin n) A} (h : InMatrixCongruenceModule T rep (e π) a s) :
    InMatrixCongruenceModule (pullT e T) (pullR e γ rep) π (fun x => a (e x)) (fun x => s (e x)) := by
  obtain ⟨m, j, b, hj, rfl⟩ := h
  refine ⟨m, fun k x => j k (e x), fun k x => b k (e x),
    fun k => ⟨pull_mem e (hj k).1, (hj k).2.1, inRing_pull e γ (hj k).2.2⟩, ?_⟩
  funext x
  simp [Finset.sum_apply]

theorem mapRep_comp {B : Type} [CommRing B] (f : A →+* B) (ρ : Γ₀ →* GL (Fin n) A) (γ : Γ₁ →* Γ₀) :
    mapRep f (ρ.comp γ) = (mapRep f ρ).comp γ := rfl

theorem overK_comp (ρ : Γ₀ →* GL (Fin n) A) (γ : Γ₁ →* Γ₀) :
    overK (ρ.comp γ) = (overK ρ).comp γ := rfl

section Rep
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem isSS_comp {ρ : Representation K Γ₀ V} (h : IsSS ρ) : IsSS (ρ.comp γ.toMonoidHom : Representation K Γ₁ V) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W fun g v hv => by simpa using hW (γ.symm g) v hv
  exact ⟨W', fun g v hv => h1 (γ g) v hv, h2⟩

theorem absIrrDistinct_comp {ρ : Representation K Γ₀ V} (h : AbsIrrDistinct ρ) :
    AbsIrrDistinct (ρ.comp γ.toMonoidHom : Representation K Γ₁ V) := by
  obtain ⟨ι, i1, i2, Vs, hs, h1, h2, h3, h4⟩ := h
  refine ⟨ι, i1, i2, Vs, fun j g => hs j (γ g), h1, h2, fun j => ?_, fun j j' hj f hf => h4 j j' hj f fun g v => ?_⟩
  · rw [← h3 j]
    congr 1
    exact γ.surjective.range_comp fun g => (ρ g).restrict (hs j g)
  · obtain ⟨g, rfl⟩ := γ.surjective g
    exact hf g v

theorem isInv_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} {W : Submodule K (Fin a → K)} :
    IsInv (ρ.comp γ.toMonoidHom) W ↔ IsInv ρ W :=
  ⟨fun h g => by obtain ⟨g, rfl⟩ := γ.surjective g; exact h g, fun h g => h (γ g)⟩

theorem isSSRep_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} (h : IsSSRep ρ) : IsSSRep (ρ.comp γ.toMonoidHom) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_comp γ).1 hW)
  exact ⟨W', (isInv_comp γ).2 h1, h2⟩

theorem isIrrSub_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} {W : Submodule K (Fin a → K)} (h : IsIrrSub ρ W) :
    IsIrrSub (ρ.comp γ.toMonoidHom) W :=
  ⟨h.1, (isInv_comp γ).2 h.2.1, fun W' h1 h2 => h.2.2 W' h1 ((isInv_comp γ).1 h2)⟩

theorem absIrrSub_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} {W : Submodule K (Fin a → K)} (h : AbsIrrSub ρ W) :
    AbsIrrSub (ρ.comp γ.toMonoidHom) W := by
  unfold AbsIrrSub at h ⊢
  rw [mapRep_comp]
  exact isIrrSub_comp γ h

end Rep

variable [IsDomain A] [IsLocalRing A]

theorem setting_pull {T : Subalgebra A (X₀ → A)} {Z₀ : Finset X₀} {Z₁ : Finset X₁} (hZ : ∀ x ∈ Z₁, e x ∈ Z₀)
    {rep : X₀ → (Γ₀ →* GL (Fin n) A)} {ρ : X₀ → (Γ₀ →* GL (Fin r) A)} {χ : ℕ → (Γ₀ →* Aˣ)}
    (h : HidaSetting t T Z₀ rep ρ χ) :
    HidaSetting t (pullT e T) Z₁ (pullR e γ rep) (pullR e γ ρ) (fun c => (χ c).comp γ.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨((pull A e).subalgebraMap T).toRingEquiv.isLocalRing, fun x y hxy => ?_, fun x => ?_,
    fun g d => pull_mem e (h4 (γ g) d), fun x => ?_, fun x y g => h6 (e x) (e y) (γ g),
    fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨f, hf, hne⟩ := h2 (e x) (e y) (e.injective.ne hxy)
    exact ⟨_, pull_mem e hf, hne⟩
  · rw [pullR, overK_comp]
    exact isSS_comp γ (h3 (e x))
  · rw [pullR, overK_comp]
    exact absIrrDistinct_comp γ (h5 (e x))
  · obtain ⟨d, hd⟩ := h7 _ (hZ x hx)
    exact ⟨d, fun g => hd (γ g)⟩
  · rw [pullR, mapRep_comp]
    exact absIrrSub_comp γ (h8 _ (hZ x hx))

omit [IsLocalRing A] in
theorem isChoice_pull {T : Subalgebra A (X₀ → A)}
    {rep : X₀ → (Γ₀ →* GL (Fin n) A)} {ρ : X₀ → (Γ₀ →* GL (Fin r) A)} {χ : ℕ → (Γ₀ →* Aˣ)} {π : X₁} {g : Γ₁} {L : ℕ}
    {eB e1 X0 : X₀ → Matrix (Fin n) (Fin n) A} (h : IsChoice t T rep ρ χ (e π) (γ g) L eB e1 X0) :
    IsChoice t (pullT e T) (pullR e γ rep) (pullR e γ ρ) (fun c => (χ c).comp γ.toMonoidHom) π g L
      (fun x => eB (e x)) (fun x => e1 (e x)) (fun x => X0 (e x)) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨d, hd, hd'⟩, ⟨ϖ, s, hϖ, hs, hX⟩, h9⟩ := h
  refine ⟨⟨inRing_pull e γ h1, inRing_pull e γ h2, funext fun x => congrFun h3 (e x), funext fun x => congrFun h4 (e x),
    funext fun x => congrFun h5 (e x), funext fun x => congrFun h6 (e x)⟩, ⟨d, fun g => hd (γ g), hd'⟩,
    ⟨ϖ, fun x => s (e x), hϖ, inCongruenceModule_pull_equivPoints e γ hs, funext fun x => congrFun hX (e x)⟩, fun x => h9 (e x)⟩

end Plain

theorem exists_algebra {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [Algebra ℤ_[q] B] [Algebra A B]
    (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → algebraMap A B (algebraMap _ _ z) = algebraMap _ _ z') :
    ∃ (_ : Algebra ℤ_[q] A), Module.Finite ℤ_[q] A ∧ IsScalarTower ℤ_[q] A B := by
  subst h
  exact ⟨inferInstance, inferInstance, IsScalarTower.of_algebraMap_eq fun z => (hφ z z HEq.rfl).symm⟩

theorem continuous_of_isLocalHom {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] [IsLocalRing R] [IsLocalRing S]
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) (hS : IsAdic (IsLocalRing.maximalIdeal S))
    (f : R →+* S) [IsLocalHom f] : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, hR.hasBasis_nhds_zero.tendsto_iff hS.hasBasis_nhds_zero]
  intro n _
  refine ⟨n, trivial, fun x hx => ?_⟩
  have h1 : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S :=
    Ideal.map_le_iff_le_comap.2 (fun y hy => map_nonunit f y hy)
  have h2 := Ideal.mem_map_of_mem f hx
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

theorem adjoin_eq_span {A B X : Type} [CommRing A] [CommRing B] (φ : A →+* B) (s : Set (X → A)) :
    Subalgebra.toSubmodule (Algebra.adjoin B ((fun f : X → A => fun x => φ (f x)) '' s)) =
      Submodule.span B ((fun f : X → A => fun x => φ (f x)) '' (Algebra.adjoin A s : Set (X → A))) := by
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    refine Submodule.span_mono fun f hf => ?_
    induction hf using Submonoid.closure_induction with
    | mem f hf => exact Set.image_mono Algebra.subset_adjoin hf
    | one => exact ⟨1, one_mem _, by ext; simp⟩
    | mul f g _ _ hf hg =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, rfl⟩ := hg
      exact ⟨f * g, mul_mem hf hg, by ext; simp⟩
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    change _ ∈ Algebra.adjoin B _
    induction hf using Algebra.adjoin_induction with
    | mem f hf => exact Algebra.subset_adjoin ⟨f, hf, rfl⟩
    | algebraMap c => exact Subalgebra.algebraMap_mem _ (φ c)
    | add f g _ _ hf hg => convert add_mem hf hg using 1; ext; simp
    | mul f g _ _ hf hg => convert mul_mem hf hg using 1; ext; simp

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N₀ N₁ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁}
  {i₀ : N₀.Loc} {i₁ : N₁.Loc} (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁)

theorem continuous_φ : Continuous a.φ := by
  letI := a.φ.toAlgebra
  obtain ⟨_, _, _⟩ := exists_algebra a.l_eq (N₀.O i₀) (N₁.O i₁) a.φ_alg
  haveI : Algebra.IsIntegral (N₀.O i₀) (N₁.O i₁) := Algebra.IsIntegral.tower_top ℤ_[N₁.l i₁]
  haveI : FaithfulSMul (N₀.O i₀) (N₁.O i₁) := (faithfulSMul_iff_algebraMap_injective _ _).2 (Model.φ_injective a)
  haveI : IsLocalHom a.φ := Algebra.IsIntegral.isLocalHom (N₀.O i₀) (N₁.O i₁)
  exact continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ

theorem goodR_ext {rep : N₀.X i₀ → (GE N₀ →* GL (Fin R.nV) (N₀.O i₀))} (h : GoodR N₀ i₀ rep) :
    GoodR N₁ i₁ fun x => mapRep a.φ (pullR a.e a.γ rep x) := by
  intro x
  obtain ⟨h1, h2, h3⟩ := h (a.e x)
  refine ⟨(h1.comp a.γ_cont).matrix_map (continuous_φ a), ?_, fun w hw B σ hB hσ => ?_⟩
  · let ψ : Kf N₀ i₀ →+* Kf N₁ i₁ := IsFractionRing.map (Model.φ_injective a)
    have hψ : ∀ z, ψ (algebraMap _ _ z) = algebraMap _ _ (a.φ z) := fun z => by simp [ψ, IsFractionRing.map]
    letI := ψ.toAlgebra
    haveI : CharZero (Kf N₀ i₀) := ((A₀.iotaQC i₀).toRingHom.comp (A₀.iotaQ i₀)).charZero
    have h4 : IsSSRep (mapRep ψ _) := ssAscent (Kf N₀ i₀) (Kf N₁ i₁) _ _ _ (isSSRep_comp a.γ h2)
    convert h4 using 1
    ext g b c
    exact (hψ _).symm
  · obtain ⟨B', hB', hσ'⟩ := (a.frob w σ).1 ⟨B, hB, hσ⟩
    rw [Model.heckePol_map a x w hw, ← h3 w ((a.out w).1 hw) B' _ hB' hσ', ← Matrix.charpoly_map]
    rfl

theorem T_ext : Subalgebra.toSubmodule (N₁.T i₁) = Submodule.span (N₁.O i₁)
    ((fun f : N₁.X i₁ → N₀.O i₀ => fun x => a.φ (f x)) '' (pullT a.e (N₀.T i₀) : Set _)) := by
  rw [← N₁.T_gen i₁, ← N₀.T_gen i₀, pullT, AlgHom.map_adjoin, ← adjoin_eq_span]
  congr 2
  ext f
  constructor
  · rintro ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩
    obtain ⟨k1, k2, k3, k4⟩ := (a.out v).1 ⟨h1, h2, h3, h4⟩
    exact ⟨_, ⟨_, ⟨v, k, k1, k2, k3, k4, h5, h6, rfl⟩, rfl⟩, funext fun x => (a.hT v k x ⟨h1, h2, h3, h4⟩ h5 h6).symm⟩
  · rintro ⟨_, ⟨_, ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨k1, k2, k3, k4⟩ := (a.out v).2 ⟨h1, h2, h3, h4⟩
    exact ⟨v, k, k1, k2, k3, k4, h5, h6, funext fun x => (a.hT v k x ⟨k1, k2, k3, k4⟩ h5 h6).symm⟩

end Record

theorem takenWild_of_locExt : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → ∀ S : Set ℂ, Chosen N₀ A₀ i₀ S → Contains N₁ A₁ i₁ S → ∃ r ρ, GoodR N₁ i₁ r ∧ TakenWild N₁ i₁ r ρ := by
  intro R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a S hC hS
  obtain ⟨rep, ρ, hG, hSet, hch⟩ := hC
  letI := a.φ.toAlgebra
  obtain ⟨j1, j2, j3⟩ := exists_algebra a.l_eq (N₀.O i₀) (N₁.O i₁) a.φ_alg
  refine ⟨_, fun x => mapRep a.φ (pullR a.e a.γ ρ x), goodR_ext a hG, N₀.O i₀, inferInstance, inferInstance,
    inferInstance, j1, j2, inferInstance, j3, pullT a.e (N₀.T i₀), pullR a.e a.γ rep, pullR a.e a.γ ρ,
    fun c => (N₀.chi i₀ c).comp a.γ.toMonoidHom,
    ⟨Model.φ_injective a, T_ext a, fun _ => rfl, fun _ _ => rfl, a.chi⟩,
    setting_pull a.e a.γ (fun x => (a.Z x).1) hSet, fun π hπ => ?_⟩
  obtain ⟨g0, L, eB, e1, X0, hg, hc, hr⟩ := hch _ ((a.Z π).1 hπ)
  obtain ⟨g, rfl⟩ := a.γ.surjective g0
  refine ⟨g, L, _, _, _, (Model.localisationCoefficientExtension_isWildInertiaCyclotomic_iff a g).2 hg, isChoice_pull a.e a.γ hc, fun x => ?_⟩
  obtain ⟨α, hα, hP⟩ := hr (a.e x)
  choose β hβ using fun c => hS (α c) (hα c)
  refine ⟨β, ?_⟩
  apply Polynomial.map_injective ((A₁.iotaQC i₁).toRingHom.comp (A₁.iotaQ i₁)) (RingHom.injective _)
  rw [Polynomial.map_map, Polynomial.map_prod]
  refine Eq.trans ?_ (hP.trans ?_)
  · congr 1
    exact RingHom.ext a.φ_iota
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp [← hβ c]

end GlobalTheory.CoefDuty.Take

end
