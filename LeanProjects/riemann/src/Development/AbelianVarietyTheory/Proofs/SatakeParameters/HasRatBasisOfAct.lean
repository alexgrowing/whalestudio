import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.FormsDescent

section General

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

def coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (v : V) : V :=
  ∑ i, φ (b.repr v i) • b i

theorem repr_coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (v : V) (i : ι) :
    b.repr (coordMap F b φ v) i = φ (b.repr v i) := by
  unfold coordMap
  rw [b.repr_sum_self]

theorem coordMap_sum (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) {α : Type} [Fintype α]
    (x : α → K) (w : α → V) (hw : ∀ a i, b.repr (w a) i ∈ F) :
    coordMap F b φ (∑ a, x a • w a) = ∑ a, φ (x a) • w a := by
  apply b.repr.injective
  ext i
  rw [repr_coordMap]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := φ.map_smul (⟨b.repr (w a) i, hw a i⟩ : F) (x a)
  simp only [Subfield.smul_def, smul_eq_mul] at h
  rw [mul_comm (x a), h, mul_comm]

theorem map_coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (g : V →ₗ[K] V)
    (hg : ∀ i j, b.repr (g (b j)) i ∈ F) (v : V) :
    g (coordMap F b φ v) = coordMap F b φ (g v) := by
  have h1 : g v = ∑ j, b.repr v j • g (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul]
  rw [h1, coordMap_sum F b φ _ _ (fun a i => hg i a)]
  simp only [coordMap, map_sum, map_smul]

theorem exists_retraction (F : Subfield K) :
    ∃ φ : K →ₗ[F] K, (∀ x, φ x ∈ F) ∧ ∀ x ∈ F, φ x = x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F K)
    (LinearMap.ker_eq_bot.2 (algebraMap F K).injective)
  refine ⟨(Algebra.linearMap F K).comp g, fun x => (g x).2, fun x hx => ?_⟩
  have h := LinearMap.congr_fun hg ⟨x, hx⟩
  have h' : g x = ⟨x, hx⟩ := h
  show ((g x : F) : K) = x
  rw [h']

end General

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem hasRatBasis_of_act
    (h : ∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K) : S.HasRatBasis := by
  classical
  haveI : Module.Finite (cmMax K) K := Module.Finite.of_restrictScalars_finite ℚ (cmMax K) K
  let e := Module.finBasis (cmMax K) K
  let s : Set S.Forms := {f | S.IsRat (f : S.Cl → S.V)}
  have hs : ⊤ ≤ Submodule.span K s := by
    intro f _
    let φ : Fin (Module.finrank (cmMax K) K) → (K →ₗ[cmMax K] K) :=
      fun k => (Algebra.linearMap (cmMax K) K).comp (e.coord k)
    let g : Fin (Module.finrank (cmMax K) K) → S.Forms := fun k =>
      ⟨fun c => coordMap (cmMax K) S.bV (φ k) ((f : S.Cl → S.V) c), fun c γ => by
        rw [map_coordMap (cmMax K) S.bV (φ k) (S.ρ c γ) (h c γ), f.2 c γ]⟩
    have hf : f = ∑ k, e k • g k := by
      apply Subtype.ext
      funext c
      apply S.bV.repr.injective
      ext i
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul,
        Finsupp.coe_finset_sum, Finsupp.smul_apply, smul_eq_mul, g, repr_coordMap]
      conv_lhs => rw [← e.sum_repr (S.bV.repr ((f : S.Cl → S.V) c) i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
      rfl
    rw [hf]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    intro c i
    show S.bV.repr (coordMap (cmMax K) S.bV (φ k) ((f : S.Cl → S.V) c)) i ∈ cmMax K
    rw [repr_coordMap]
    exact (e.coord k _).2
  let b := Module.Basis.ofSpan hs
  refine ⟨b.reindex (b.indexEquiv (Module.finBasis K S.Forms)), fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact Module.Basis.ofSpan_subset hs ⟨_, rfl⟩

theorem repr_mem_of_isRat (h : S.HasRatBasis) (f : S.Forms) (hf : S.IsRat (f : S.Cl → S.V)) (a : Fin S.dim) :
    S.basis.repr f a ∈ cmMax K := by
  have hb : ∀ i, S.IsRat (S.basis i : S.Cl → S.V) := by
    have : S.basis = h.choose := by
      unfold CSD.basis
      exact dif_pos h
    rw [this]
    exact h.choose_spec
  obtain ⟨φ, h1, h2⟩ := exists_retraction (cmMax K)
  have key : f = ∑ a, φ (S.basis.repr f a) • S.basis a := by
    apply Subtype.ext
    funext c
    have e1 : (f : S.Cl → S.V) c = ∑ a, S.basis.repr f a • (S.basis a : S.Cl → S.V) c := by
      conv_lhs => rw [← S.basis.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    have e2 : coordMap (cmMax K) S.bV φ ((f : S.Cl → S.V) c) = (f : S.Cl → S.V) c := by
      apply S.bV.repr.injective
      ext i
      rw [repr_coordMap, h2 _ (hf c i)]
    rw [← e2, e1, coordMap_sum (cmMax K) S.bV φ _ _ (fun a i => hb a c i)]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have : S.basis.repr f a = φ (S.basis.repr f a) := by
    conv_lhs => rw [key]
    rw [S.basis.repr_sum_self]
  rw [this]
  exact h1 _

end GlobalTheory.FormsDescent

namespace GlobalTheory

theorem forms_rat : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K), ((∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K) → S.HasRatBasis) ∧ ∀ T : Module.End K S.Forms, S.HasRatBasis → (∀ f : S.Forms, S.IsRat (f : S.Cl → S.V) → S.IsRat ((T f : S.Forms) : S.Cl → S.V)) → ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax K := by
  intro K _ _ _ S
  refine ⟨FormsDescent.hasRatBasis_of_act S, fun T h hT a b => ?_⟩
  rw [LinearMap.toMatrix_apply]
  refine FormsDescent.repr_mem_of_isRat S h _ (hT _ ?_) a
  have : S.basis = h.choose := by
    unfold CSD.basis
    exact dif_pos h
  rw [this]
  exact h.choose_spec b

end GlobalTheory
