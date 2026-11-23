import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent

noncomputable section

namespace GlobalTheory.CoefSpace

section Poly

open Formalism.BasicNotions Formalism.L2.DIV MvPolynomial Matrix
open scoped ComplexOrder InnerProductSpace

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem fockL_eq {σ : Type} (f g : MvPolynomial σ ℂ) : fockL f g = Formalism.REAL.fockF g f := by
  have h := Formalism.L2.Col.map_fockS (RingHom.id ℂ) f g (fun _ => rfl)
  simp only [RingHom.id_apply, MvPolynomial.map_id] at h
  exact h

theorem map_fockL {K σ : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (hφ : ∀ x, φ (star x) = star (φ x))
    (f g : MvPolynomial σ K) : φ (fockL f g) = fockL (map φ f) (map φ g) := by
  rw [fockL_eq]
  exact Formalism.L2.Col.map_fockS φ f g fun _ => hφ _

theorem map_pairP {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (hφ : ∀ x, φ (star x) = star (φ x))
    (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n) :
    φ (pairP lam G F F') = pairP lam (fun τ => (G τ).map φ) (map φ F) (map φ F') := by
  have h1 : φ (gramTw lam G) = gramTw lam (fun τ => (G τ).map φ) := by
    simp only [gramTw, map_prod, map_zpow₀, RingHom.map_det]
    rfl
  have h2 : φ (extNorm K lam) = extNorm ℂ lam := by
    simp only [extNorm, map_prod, ← fockL_apply, map_fockL φ hφ, map_extremal]
  rw [pairP_apply, pairP_apply, map_mul, map_div₀, h1, h2, map_fockL φ hφ, Formalism.L2.Col.map_blockAct]
  rfl

theorem map_actP {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (F : Pol K ι n) :
    map φ (actP lam B F) = actP lam (fun τ => Formalism.UG.bc φ (B τ)) (map φ F) := by
  have h3 : φ (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc φ (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h3, trAct,
    Formalism.L2.Col.map_blockAct]
  rfl

def bcVV {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) : VV K lam →ₛₗ[φ] VV ℂ lam where
  toFun x := ⟨map φ x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' a x := Subtype.ext (by simp [smul_eq_C_mul])

theorem bcVV_span {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) :
    Submodule.span ℂ (Set.range fun i => bcVV φ lam (bVV K lam i)) = ⊤ := by
  rw [eq_top_iff, ← (bVV ℂ lam).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨F, hF, e⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc φ lam i
  have : bVV ℂ lam i = bcVV φ lam ⟨F, hF⟩ := Subtype.ext ((bVV_coe ℂ lam i).trans e)
  rw [this, ← (bVV K lam).sum_repr ⟨F, hF⟩, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem bcVV_indep {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) :
    LinearIndependent ℂ fun i => bcVV φ lam (bVV K lam i) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (bcVV_span φ lam).ge
    (Module.finrank_eq_card_basis (bVV ℂ lam)).symm

theorem continuous_actP {X : Type} [TopologicalSpace X] (lam : ι → DomWeight n) (g : X → ι → GL (Fin n) ℂ)
    (hg : ∀ τ, Continuous fun x => (g x τ : Matrix (Fin n) (Fin n) ℂ)) (l : Pol ℂ ι n →ₗ[ℂ] ℂ) (F : Pol ℂ ι n) :
    Continuous fun x => l (actP lam (g x) F) := by
  let G : ι → Matrix (Fin n) (Fin n) C(X, ℂ) := fun τ a b => ⟨fun x => (g x τ : Matrix (Fin n) (Fin n) ℂ) b a,
    (continuous_apply_apply b a).comp (hg τ)⟩
  let P := Formalism.GradedWeylDivisibility.blockAct C(X, ℂ) G (map (algebraMap ℂ C(X, ℂ)) F)
  have key : ∀ x, trAct (g x) F = map (ContinuousMap.evalAlgHom ℂ ℂ x : C(X, ℂ) →+* ℂ) P := by
    intro x
    have : ((trAct (g x) : Pol ℂ ι n →ₐ[ℂ] Pol ℂ ι n) : Pol ℂ ι n →+* Pol ℂ ι n) =
        (map (ContinuousMap.evalAlgHom ℂ ℂ x : C(X, ℂ) →+* ℂ)).comp
          ((Formalism.GradedWeylDivisibility.blockAct C(X, ℂ) (n := n) G).toRingHom.comp (map (algebraMap ℂ C(X, ℂ)))) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [trAct]
      · intro v
        simp [trAct, Formalism.GradedWeylDivisibility.blockAct, G]
    exact DFunLike.congr_fun this F
  have h2 : ∀ x, l (trAct (g x) F) = ∑ m ∈ P.support, (P.coeff m) x * l (monomial m 1) := by
    intro x
    rw [key]
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, map_monomial]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul, h2, detTw_eq]
  refine Continuous.mul (continuous_finset_prod _ fun τ _ => (hg τ).matrix_det.zpow₀ _ fun x => Or.inl ?_)
    (continuous_finset_sum _ fun m _ => (P.coeff m).continuous.mul continuous_const)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (g x τ).isUnit).ne_zero

def gramOf (B : ι → GL (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (B τ : Matrix (Fin n) (Fin n) ℂ)ᴴ * (B τ : Matrix (Fin n) (Fin n) ℂ)

theorem pairK_pos (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ) (x : VV ℂ lam) (hx : x ≠ 0) :
    0 < pairK lam (gramOf B) x x := by
  have h := pairTransport ℂ ι n lam (fun _ => 1) B B x.1 x.1
  simp only [Matrix.mul_one] at h
  have hne : actP lam B x.1 ≠ 0 := fun h0 => hx (Subtype.ext (by
    have := congrArg (fun φ : Module.End ℂ (Pol ℂ ι n) => φ x.1) ((rhoP lam).map_mul B⁻¹ B)
    rw [inv_mul_cancel, map_one] at this
    refine this.trans ?_
    show actP lam B⁻¹ (actP lam B x.1) = 0
    rw [h0, map_zero]))
  obtain ⟨q, hq, e⟩ := extNormPos ℂ ι n lam
  rw [pairK_apply]
  unfold gramOf
  rw [← h, pairP_apply, pb_gramTw_one, pb_blockAct_one_tr, fockL_eq, e]
  refine mul_pos (one_div_pos.2 ?_) (ps_fockF_pos _ hne)
  rw [eq_ratCast, ← Complex.ofReal_ratCast]
  exact Complex.zero_lt_real.2 (by exact_mod_cast hq)

def HV (lam : ι → DomWeight n) (_B : ι → GL (Fin n) ℂ) : Type := VV ℂ lam

variable (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ)

instance : AddCommGroup (HV lam B) := inferInstanceAs (AddCommGroup (VV ℂ lam))

instance : Module ℂ (HV lam B) := inferInstanceAs (Module ℂ (VV ℂ lam))

@[reducible] def core : InnerProductSpace.Core ℂ (HV lam B) where
  inner x y := pairK lam (gramOf B) x y
  conj_inner_symm x y := (pairSymm ℂ ι n lam (gramOf B) fun τ => by simp [gramOf]).eq _ _
  re_inner_nonneg x := by
    by_cases hx : x = 0
    · subst hx
      exact le_of_eq (congrArg Complex.re (map_zero (pairK lam (gramOf B) 0))).symm
    · exact (Complex.lt_def.1 (pairK_pos lam B x hx)).1.le
  add_left x y z := LinearMap.map_add₂ (pairK lam (gramOf B)) x y z
  smul_left x y r := LinearMap.map_smulₛₗ₂ (pairK lam (gramOf B)) r x y
  definite x hx := by
    by_contra h
    exact (pairK_pos lam B x h).ne' hx

instance : NormedAddCommGroup (HV lam B) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (core lam B)

instance : InnerProductSpace ℂ (HV lam B) := InnerProductSpace.ofCore (core lam B).toCore

instance : FiniteDimensional ℂ (HV lam B) := (bVV ℂ lam).finiteDimensional_of_finite

theorem inner_HV (x y : HV lam B) : inner ℂ x y = pairK lam (gramOf B) x y := rfl

instance : Nontrivial (HV lam B) :=
  ⟨⟨_, (0 : VV ℂ lam), fun h => GlobalTheory.Proof.TensorMapDescent.ten_ne_zero (fun τ => extremal ℂ n (lam τ))
    (fun τ => Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _) (congrArg Subtype.val (h : (⟨_, GlobalTheory.Proof.TensorMapDescent.ten_mem lam _
      fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (natW_antitone _)⟩ : VV ℂ lam) = 0))⟩⟩

theorem continuous_HV {X : Type} [TopologicalSpace X] (g : X → ι → GL (Fin n) ℂ)
    (hg : ∀ τ, Continuous fun x => (g x τ : Matrix (Fin n) (Fin n) ℂ)) (v : HV lam B) :
    Continuous (X := X) (Y := HV lam B) fun x => rhoK lam (g x) v := by
  have : (fun x => (rhoK lam (g x) v : HV lam B)) = fun x => ∑ i,
      pairP lam (gramOf B) (Subtype.val (stdOrthonormalBasis ℂ (HV lam B) i)) (actP lam (g x) (Subtype.val v)) •
        stdOrthonormalBasis ℂ (HV lam B) i := by
    funext x
    exact ((stdOrthonormalBasis ℂ (HV lam B)).sum_repr' _).symm
  rw [this]
  exact continuous_finset_sum _ fun i _ => (continuous_actP lam g hg _ _).smul continuous_const

end Poly

end GlobalTheory.CoefSpace
