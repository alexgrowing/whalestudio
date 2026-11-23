import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PositiveRowsTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom

noncomputable section

open Module

namespace GlobalTheory.QPosCompare

section Rat

variable {K X E : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} (j : X →ₛₗ[σ] E)

def IsRatSub (W : Submodule ℂ E) : Prop := Submodule.span ℂ (j '' {x | j x ∈ W}) = W

structure IsForm : Prop where
  basis : ∃ (n : ℕ) (b : Basis (Fin n) K X), LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range j) = ⊤
  inner : ∀ x y, ∃ a : K, inner ℂ (j x) (j y) = σ a

variable {j}

theorem isRatSub_span (S : Set X) : IsRatSub j (Submodule.span ℂ (j '' S)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨x, hx, rfl⟩; exact hx
  · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, Submodule.subset_span ⟨x, hx, rfl⟩, rfl⟩

theorem IsRatSub.sup {W W' : Submodule ℂ E} (h : IsRatSub j W) (h' : IsRatSub j W') : IsRatSub j (W ⊔ W') := by
  rw [← h, ← h', ← Submodule.span_union, ← Set.image_union]
  exact isRatSub_span _

theorem IsForm.linInd (h : IsForm j) {ι : Type} [Fintype ι] {v : ι → X} (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun i => j (v i) := by
  obtain ⟨n, b, hb, -⟩ := h.basis
  let _ := σ.toAlgebra
  have h1 : LinearIndependent K fun i => b.equivFun (v i) :=
    hv.map' (b.equivFun : X →ₗ[K] (Fin n → K)) b.equivFun.ker
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun i => j (b i))
    (LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hb c
      (by simpa [Fintype.linearCombination_apply] using hc)))
  suffices he : (fun i => j (v i)) = (Fintype.linearCombination ℂ fun i => j (b i)) ∘
      fun i => (algebraMap K ℂ) ∘ b.equivFun (v i) by rw [he]; exact h3
  funext i
  simp only [Function.comp, Fintype.linearCombination_apply]
  conv_lhs => rw [← b.sum_equivFun (v i)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]; rfl

theorem IsForm.finite (h : IsForm j) : FiniteDimensional K X := by
  obtain ⟨n, b, -, -⟩ := h.basis
  exact Module.Finite.of_basis b

theorem span_image_eq {T : Submodule K X} {ι : Type} [Fintype ι] (b : Basis ι K T) :
    Submodule.span ℂ (j '' (T : Set X)) = Submodule.span ℂ (Set.range fun i => j (b i)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨x, hx, rfl⟩
    have : x = ∑ i, b.equivFun ⟨x, hx⟩ i • (b i : X) := by
      have := congrArg Subtype.val (b.sum_equivFun ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [this, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩; exact ⟨b i, (b i).2, rfl⟩

theorem IsForm.finrank_span (h : IsForm j) (T : Submodule K X) :
    finrank ℂ (Submodule.span ℂ (j '' (T : Set X))) = finrank K T := by
  have := h.finite
  rw [span_image_eq (finBasis K T)]
  have := finrank_span_eq_card (h.linInd ((finBasis K T).linearIndependent.map' T.subtype T.ker_subtype))
  rw [Fintype.card_fin] at this
  exact this

theorem IsForm.finrank_eq (h : IsForm j) : finrank ℂ E = finrank K X := by
  have h1 := h.finrank_span ⊤
  obtain ⟨n, b, -, hs⟩ := h.basis
  rw [Submodule.top_coe, Set.image_univ, hs] at h1
  simpa using h1

theorem IsForm.orthogonal [FiniteDimensional ℂ E] (h : IsForm j) {W : Submodule ℂ E} (hW : IsRatSub j W) :
    IsRatSub j Wᗮ := by
  have := h.finite
  choose p hp using h.inner
  set S : Submodule K X := W.comap j
  have hWS : Submodule.span ℂ (j '' (S : Set X)) = W := hW
  let b := finBasis K S
  let φ : X →ₗ[K] (Fin (finrank K S) → K) :=
    { toFun := fun x i => p (b i) x
      map_add' := fun x y => by
        funext i
        apply σ.injective
        simp only [Pi.add_apply, map_add, ← hp, inner_add_right]
      map_smul' := fun a x => by
        funext i
        apply σ.injective
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul, ← hp, map_smulₛₗ, inner_smul_right] }
  have hker : LinearMap.ker φ ≤ Wᗮ.comap j := by
    intro x hx
    show j x ∈ Wᗮ
    rw [← hWS, span_image_eq b, Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      have : p (b i) x = 0 := congrFun (LinearMap.mem_ker.1 hx) i
      rw [hp, this, map_zero]
    | zero => simp
    | add u v _ _ hu hv => rw [inner_add_left, hu, hv, add_zero]
    | smul a u _ hu => rw [inner_smul_left, hu, mul_zero]
  refine Submodule.eq_of_le_of_finrank_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩; exact hx
  · have e1 := h.finrank_span (Wᗮ.comap j)
    have e2 := Submodule.finrank_mono hker
    have e3 := φ.finrank_range_add_finrank_ker
    have e4 : finrank K (LinearMap.range φ) ≤ finrank K S := by
      simpa using (LinearMap.range φ).finrank_le
    have e5 := h.finrank_span S
    rw [hWS] at e5
    have e6 := W.finrank_add_finrank_orthogonal
    have e7 := h.finrank_eq
    have e8 : finrank ℂ (Submodule.span ℂ (j '' {x | j x ∈ Wᗮ})) = finrank K (Wᗮ.comap j) := e1
    omega

theorem IsForm.inf [FiniteDimensional ℂ E] (h : IsForm j) {W W' : Submodule ℂ E} (hW : IsRatSub j W)
    (hW' : IsRatSub j W') : IsRatSub j (W ⊓ W') := by
  have := h.orthogonal ((h.orthogonal hW).sup (h.orthogonal hW'))
  rwa [← Submodule.inf_orthogonal, Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at this

end Rat

section Twist

open Formalism.IndefR.Links

variable {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] (s : Bool)

theorem tw_map_sub (V : Submodule ℂ E) : V.map (Tw.mkL s E) = Tw.sub s V := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨Tw.out x, hx, rfl⟩⟩

theorem tw_span (S : Set E) : Submodule.span ℂ (Tw.mk s '' S) = Tw.sub s (Submodule.span ℂ S) := by
  rw [← tw_map_sub, Submodule.map_span]; rfl

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] {K X : Type} [Field K] [AddCommGroup X] [Module K X] {σ σ' : K →+* ℂ}
  (h : ∀ a, σ' a = cj s (σ a)) (j : X →ₛₗ[σ] E) (f : E →ₗ[ℂ] E')

end Twist

theorem isForm_of_pres {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* G} {S : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Formalism.IndefR.Bridge.ClassPres ι S σ ρ J χ) (M : Formalism.IndefR.Links.HMod (G → W))
    (hM : M.Is (Formalism.IndefR.Bridge.AdForms ι ρ J χ) (Formalism.IndefR.Bridge.adInner ι J P.y))
    (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) : IsForm j := by
  obtain ⟨hinj, hr, hip⟩ := hM
  obtain ⟨-, ⟨hli, hsp⟩, hiso⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨⟨_, S.basis, ?_, ?_⟩, fun x y => ⟨S.csum x y, ?_⟩⟩
  · refine LinearIndependent.of_comp M.e ?_
    have : (M.e ∘ fun i => j (S.basis i)) = fun i => P.extL (S.basis i) := funext fun i => hj _
    rw [this]; exact hli
  · apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_span, Submodule.map_top, hr, ← Set.range_comp]
    have : (M.e ∘ j) = P.extL := funext hj
    rw [this]; exact hsp
  · rw [hip, hj, hj]; exact hiso x y

def RatZAt {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {A : Formalism.L2.Indef.DefAmb Bs}
    (X : Formalism.IndefR.Cx.CxData A) (t : Bs.Tup) : Prop :=
  Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))) = LinearMap.range (LinearMap.adjoint (X.Θ t))

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem lPos_iff_ne_bot : R.LPos F ↔ ∀ b, (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ :=
  forall_congr' fun b => pos_iff_ne_bot R F b

def ZC : Submodule ℂ (R.HX A.μ0).H := LinearMap.range (LinearMap.adjoint (R.Th A.μ0))

def RationalAtBaseWeight : Prop := RatZAt (R.toCx F) A.μ0

variable {R} in

theorem isForm_jX (h : R.IsModels) (t : T) : IsForm (R.jX t) :=
  isForm_of_pres (R.B.R t).pres (R.HX t) (h.HX t) (R.jX t) (h.jX t)

end Compare

end GlobalTheory.QPosCompare

end
