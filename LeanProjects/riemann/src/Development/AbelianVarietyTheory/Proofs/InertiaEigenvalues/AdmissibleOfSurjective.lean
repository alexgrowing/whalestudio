import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.AdmClosure

section Lat

variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
variable {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def between [IsDomain O] [IsPrincipalIdealRing O] (L₁ L₂ : Lattice (O := O) ρ) (N : Submodule O V)
    (h₁ : N ≤ L₁.T) (h₂ : L₂.T ≤ N) (hs : ∀ g, ∀ x ∈ N, ρ g x ∈ N) : Lattice (O := O) ρ where
  T := N
  stable := hs
  fg := L₁.fg.of_le h₁
  free := by
    haveI := L₁.free
    haveI : Module.Finite O L₁.T := Module.Finite.iff_fg.mpr L₁.fg
    haveI : Module.Finite O (N.comap L₁.T.subtype) := inferInstance
    haveI : Module.Free O (N.comap L₁.T.subtype) := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe h₁)
  span := by
    rw [eq_top_iff, ← L₂.span]
    exact Submodule.span_mono h₂

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def prodEquiv (A : Submodule O V) (B : Submodule O V') : ↥(A.prod B) ≃ₗ[O] (↥A × ↥B) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def prodLattice (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') : Lattice (O := O) (ρ.prod ρ') where
  T := L.T.prod L'.T
  stable := fun g x hx => ⟨L.stable g _ hx.1, L'.stable g _ hx.2⟩
  fg := L.fg.prod L'.fg
  free := by
    haveI := L.free
    haveI := L'.free
    exact Module.Free.of_equiv (prodEquiv L.T L'.T).symm
  span := by
    have h := Submodule.span_prod_eq (R := LL) (s := (L.T : Set V)) (t := (L'.T : Set V')) L.T.zero_mem L'.T.zero_mem
    rw [L.span, L'.span, Submodule.prod_top] at h
    exact h

end Lat

section Bundled

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def prodLoc (T T' : LocLat G Qp LL O) : LocLat G Qp LL O where
  V := T.V × T'.V
  ρ := T.ρ.prod T'.ρ
  cont := fun x => (T.cont x.1).prodMk (T'.cont x.2)
  L := prodLattice T.L T'.L

end Bundled

def appendEquiv {R : Type} [CommRing R] {A : Type 1} (W : A → Type) [∀ x, AddCommGroup (W x)] [∀ x, Module R (W x)]
    {ι κ : Type} (F : ι → A) (F' : κ → A) :
    ((∀ j, W (F j)) × (∀ j, W (F' j))) ≃ₗ[R] (∀ j : ι ⊕ κ, W (Sum.elim F F' j)) where
  toFun x j := match j with
    | .inl a => x.1 a
    | .inr b => x.2 b
  invFun y := (fun a => y (.inl a), fun b => y (.inr b))
  map_add' _ _ := by funext j; cases j <;> rfl
  map_smul' _ _ := by funext j; cases j <;> rfl
  left_inv _ := rfl
  right_inv _ := by funext j; cases j <;> rfl

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {t : ℕ} {Ut : ZMod n → Multiset ℤ}

theorem sumFull_prod [IsTopologicalRing LL] {μ μ' : ℕ} {T T' : LocLat G Qp LL O} (h : SumFull PD emb Γ t Ut μ T)
    (h' : SumFull PD emb Γ t Ut μ' T') : SumFull PD emb Γ t Ut (μ + μ') (prodLoc T T') := by
  obtain ⟨F, hF, e, he⟩ := h
  obtain ⟨F', hF', e', he'⟩ := h'
  let s : Fin (μ + μ') ≃ Fin μ ⊕ Fin μ' := finSumFinEquiv.symm
  have key : ∀ (g : G) (x : T.V × T'.V) (j : Fin μ ⊕ Fin μ'),
      appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e (T.ρ g x.1), e' (T'.ρ g x.2)) j =
        (Sum.elim F F' j).ρ g (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e x.1, e' x.2) j) := by
    intro g x j
    cases j with
    | inl a => exact he g x.1 a
    | inr b => exact he' g x.2 b
  refine ⟨fun j => Sum.elim F F' (s j), fun j => ?_,
    ((e.prodCongr e').trans (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F')).trans
      (LinearEquiv.piCongrLeft LL (fun j => (Sum.elim F F' j).V) s).symm, fun g x j => key g x (s j)⟩
  beta_reduce
  cases s j with
  | inl a => exact hF a
  | inr b => exact hF' b

variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    {π : Representation O G M} {π' : Representation O G M'}

theorem admissible_prod [IsTopologicalRing LL] (h : Admissible PD emb Γ t Ut π) (h' : Admissible PD emb Γ t Ut π') :
    Admissible PD emb Γ t Ut (π.prod π') := by
  obtain ⟨hf, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  obtain ⟨hf', μ', T', hT', L₂', p', hle', hp', hg', hk'⟩ := h'
  refine ⟨inferInstance, μ + μ', prodLoc T T', sumFull_prod hT hT', prodLattice L₂ L₂',
    (p.prodMap p') ∘ₗ (prodEquiv T.L.T T'.L.T).toLinearMap, Submodule.prod_mono hle hle',
    (hp.prodMap hp').comp (prodEquiv T.L.T T'.L.T).surjective, fun g x => ?_, fun x => ?_⟩
  · exact Prod.ext (hg g (prodEquiv T.L.T T'.L.T x).1) (hg' g (prodEquiv T.L.T T'.L.T x).2)
  · exact Prod.ext_iff.trans (and_congr (hk (prodEquiv T.L.T T'.L.T x).1) (hk' (prodEquiv T.L.T T'.L.T x).2))

variable [IsDomain O] [IsPrincipalIdealRing O]

theorem admissible_of_surjective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hs : Function.Surjective f) (h : Admissible PD emb Γ t Ut π) : Admissible PD emb Γ t Ut π' := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := (LinearMap.ker (f ∘ₗ p)).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ f (p x) = 0 := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  refine ⟨Finite.of_surjective f hs, μ, T, hT, between T.L L₂ N h₁ (fun x hx => ?_) (fun g x hx => ?_),
    f ∘ₗ p, h₁, hs.comp hp, fun g x => ?_, fun x => (hN x).symm⟩
  · refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx, map_zero]
  · refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    rw [hg, hf, (hN ⟨x, h₁ hx⟩).mp hx, map_zero]
  · simp only [LinearMap.comp_apply, hg, hf]

theorem admissible_of_injective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hi : Function.Injective f) (h : Admissible PD emb Γ t Ut π') : Admissible PD emb Γ t Ut π := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := ((LinearMap.range f).comap p).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ p x ∈ LinearMap.range f := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  have h₂ : L₂.T ≤ N := fun x hx => by
    refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx]
    exact zero_mem _
  have hs : ∀ g, ∀ x ∈ N, T.ρ g x ∈ N := fun g x hx => by
    refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    obtain ⟨y, hy⟩ := (hN ⟨x, h₁ hx⟩).mp hx
    exact ⟨π g y, by rw [hg, hf, hy]⟩
  let q : N →ₗ[O] M := (LinearEquiv.ofInjective f hi).symm.toLinearMap ∘ₗ
    (p ∘ₗ Submodule.inclusion h₁).codRestrict (LinearMap.range f) (fun x => (hN ⟨x, h₁ x.2⟩).mp x.2)
  have hq : ∀ x : N, f (q x) = p ⟨x, h₁ x.2⟩ := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective f hi).apply_symm_apply ⟨_, (hN ⟨x, h₁ x.2⟩).mp x.2⟩)
  refine ⟨Finite.of_injective f hi, μ, withLat T (between T.L L₂ N h₁ h₂ hs), hT.withLat _, L₂, q, h₂,
    fun y => ?_, fun g x => hi ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := hp (f y)
    exact ⟨⟨x.1, (hN x).mpr ⟨y, hx.symm⟩⟩, hi ((hq _).trans hx)⟩
  · exact (hq _).trans ((hg g ⟨x.1, h₁ x.2⟩).trans ((congrArg (π' g) (hq x).symm).trans (hf g _).symm))
  · refine Iff.trans ?_ (hk ⟨x.1, h₁ x.2⟩)
    rw [← hq x, ← map_zero f]
    exact hi.eq_iff.symm

end Per

theorem admissible_closed : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Closed := by
  intro l _ P S M M' _ _ _ _ π π'
  obtain ⟨⟨hD, hDV, -⟩, -, -, hT, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  exact ⟨fun f hf => ⟨admissible_of_injective f hf, admissible_of_surjective f hf⟩, admissible_prod⟩

end GlobalTheory.AdmClosure
