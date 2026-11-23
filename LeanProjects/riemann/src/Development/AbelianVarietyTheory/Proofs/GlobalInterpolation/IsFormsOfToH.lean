import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasRatBasisOfAct

noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.PeriodClassSum
open scoped Matrix ComplexOrder

theorem wForm_sum {C ι κ : Type} [Fintype C] [Fintype ι] [Fintype κ] (w : C → ℕ) (G : Matrix ι ι ℂ) (u : κ → C → ι → ℂ)
    (a b : κ → ℂ) : star a ⬝ᵥ (Matrix.of fun i j => wForm w G (u i) (u j)) *ᵥ b = wForm w G (∑ i, a i • u i) (∑ i, b i • u i) := by
  rw [dotProduct]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  simp only [wForm, Finset.sum_apply, Pi.smul_apply, star_sum, star_smul, sum_dotProduct, smul_dotProduct,
    Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring

section Metric

variable {K : Type} [Field K] [NumberField K] [StarRing K]

omit [NumberField K] in

theorem map_pair {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V) (p : V →ₗ⋆[K] V →ₗ[K] K)
    (φ : K →+* ℂ) (x y : V) (hx : ∀ i, b.repr x i ∈ cmMax K) :
    φ (p x y) = star (fun i => φ (b.repr x i)) ⬝ᵥ (Matrix.of fun i j => p (b i) (b j)).map φ *ᵥ fun i => φ (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, dotProduct,
    Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum, RingHom.id_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, hx i φ, starRingEnd_apply]
  ring

variable (S : CSD K) (v : InfinitePlace K)

def coAt (f : S.Cl → S.V) : S.Cl → S.ιV → ℂ := fun c i => v.embedding (S.bV.repr (f c) i)

theorem coAt_sum (x : S.Forms) :
    coAt S v (x : S.Cl → S.V) = ∑ i, v.embedding (S.basis.repr x i) • coAt S v (S.basis i : S.Cl → S.V) := by
  funext c k
  conv_lhs => rw [← S.basis.sum_repr x]
  simp only [coAt, AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, smul_eq_mul, map_mul]

theorem coAt_indep : LinearIndependent ℂ fun i => fun p : S.Cl × S.ιV => coAt S v (S.basis i : S.Cl → S.V) p.1 p.2 := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  let f : S.Forms →ₗ[K] (S.Cl × S.ιV → K) := LinearMap.pi fun p =>
    S.bV.coord p.2 ∘ₗ LinearMap.proj p.1 ∘ₗ S.Forms.subtype
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    funext c
    exact S.bV.forall_coord_eq_zero_iff.1 fun k => congrFun hφ (c, k)
  exact (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (S.basis.linearIndependent.map' f hf)

theorem H_map (hb : S.HasRatBasis) : S.H.map v.embedding = Matrix.of fun i j =>
    wForm S.wt (S.gramV.map v.embedding) (coAt S v (S.basis i : S.Cl → S.V)) (coAt S v (S.basis j : S.Cl → S.V)) := by
  ext i j
  simp only [Matrix.map_apply, CSD.H, Matrix.of_apply, CSD.csum, wForm, map_sum, map_mul, map_inv₀, map_natCast]
  exact Finset.sum_congr rfl fun c _ => congrArg _ (map_pair S.bV S.pair v.embedding _ _ (S.basis_rat hb i c))

theorem H_posDef (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) : (S.H.map v.embedding).PosDef := by
  rw [H_map S v hb]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
    exact wForm_conj _ hG.1 _ _
  · rw [wForm_sum]
    refine lt_of_le_of_ne (wForm_nonneg _ hG.posSemidef _) fun h0 => ha ?_
    have h1 := wForm_eq_zero _ S.wt_pos hG h0.symm
    funext i
    refine Fintype.linearIndependent_iff.1 (coAt_indep S v) a ?_ i
    funext p
    simpa using congrFun (congrFun h1 p.1) p.2

theorem normAt_sq (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) (x : S.Forms) :
    ((Formalism.HermitianLatticesTheory.normAt S.basis (stdFrame S.H) v x ^ 2 : ℝ) : ℂ) =
      wForm S.wt (S.gramV.map v.embedding) (coAt S v (x : S.Cl → S.V)) (coAt S v (x : S.Cl → S.V)) := by
  have hm := (frameOfSpec _ _ (H_posDef S v hb hG)).2
  have h1 := wForm_sum S.wt (S.gramV.map v.embedding) (fun i => coAt S v (S.basis i : S.Cl → S.V))
    (Formalism.HermitianLatticesTheory.vecAt S.basis v x) (Formalism.HermitianLatticesTheory.vecAt S.basis v x)
  rw [← H_map S v hb, ← hm, metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec] at h1
  rw [coAt_sum S v x]
  refine Eq.trans ?_ h1
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

variable (T : GSD K) (h : T.Ok) (hr : ∀ (g : T.G) i j, T.bV.repr (T.ρ g (T.bV j)) i ∈ cmMax K)

include hr in

theorem isFormsOf_toH (hG : ∀ v : InfinitePlace K, (T.gramV.map v.embedding).PosDef) (N : Submodule (𝓞 K) T.EqFun) :
    IsFormsOf T h N (T.toH h N) (LinearEquiv.refl _ _) := by
  refine ⟨fun _ => Iff.rfl, fun v (x : T.EqFun) => ?_⟩
  exact (normAt_sq (T.toCSD h) v (FormsDescent.hasRatBasis_of_act _ fun c γ => hr γ.1) (hG v) (T.res h x)).trans
    (ipAt_eq T h v x x).symm

include h hr in

theorem pairAt_rho (g : T.G) (x : T.V) : T.pairAt v (T.ρ g x) (T.ρ g x) = T.pairAt v x x := by
  let u : T.ιV → Unit → T.ιV → ℂ := fun k _ i => v.embedding (T.bV.repr (T.ρ g (T.bV k)) i)
  have h1 := wForm_sum (fun _ => 1) (T.gramV.map v.embedding) u (fun i => v.embedding (T.bV.repr x i))
    (fun i => v.embedding (T.bV.repr x i))
  have e1 : (Matrix.of fun i j => wForm (fun _ => 1) (T.gramV.map v.embedding) (u i) (u j)) = T.gramV.map v.embedding := by
    ext i j
    simp only [Matrix.of_apply, wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]
    refine (map_pair T.bV T.pair v.embedding _ _ fun k => hr g k i).symm.trans ?_
    rw [h.inv]
    rfl
  have e2 : (∑ i, v.embedding (T.bV.repr x i) • u i) = fun _ i => v.embedding (T.bV.repr (T.ρ g x) i) := by
    funext c k
    conv_rhs => rw [← T.bV.sum_repr x]
    simp only [u, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
      smul_eq_mul, map_mul]
  rw [e1, e2] at h1
  rw [pairAt_eq, pairAt_eq, h1]
  simp only [wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]

include hr in

theorem ipAt_sec (s : T.Sec) (φ : T.EqFun) : T.ipAt h v φ φ = letI := h.fintypeCl
    ∑ c, ((Nat.card (MulAction.stabilizer T.G (s.rep c)) : ℕ) : ℂ)⁻¹ *
      T.pairAt v ((φ : T.D → T.V) (s.rep c)) ((φ : T.D → T.V) (s.rep c)) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := T.outSec.exists_smul s c
  rw [T.wt_eq, ← hg, T.card_stab_smul, φ.2, pairAt_rho v T h hr]

end Metric

end GlobalTheory.PeriodOnStep
