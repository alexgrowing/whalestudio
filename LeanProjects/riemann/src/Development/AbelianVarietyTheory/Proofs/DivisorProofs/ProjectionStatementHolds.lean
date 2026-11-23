import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFrameValuationBound

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatModel.Proj

theorem exists_dual {O κ : Type} [CommRing O] [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℤ O)
    (hd : Algebra.discr ℤ b ≠ 0) :
    ∃ c : κ → O, (∀ a k, a * c k = ∑ i, b.repr (a * b i) k • c i) ∧
      ∑ i, c i * b i = ((Algebra.discr ℤ b : ℤ) : O) := by
  set T := Algebra.traceMatrix ℤ b with hT
  have hd' : T.det ≠ 0 := hd
  have nd : ∀ x y : O, (∀ l, Algebra.trace ℤ O (x * b l) = Algebra.trace ℤ O (y * b l)) → x = y := by
    intro x y h
    rw [← sub_eq_zero]
    have h1 : Matrix.vecMul (b.repr (x - y)) T = 0 := by
      funext l
      have h2 : Algebra.trace ℤ O ((x - y) * b l) = 0 := by rw [sub_mul, map_sub, h, sub_self]
      rw [← b.sum_repr (x - y), Finset.sum_mul, map_sum] at h2
      simp only [smul_mul_assoc, map_smul, smul_eq_mul] at h2
      exact h2
    have h3 := Matrix.eq_zero_of_vecMul_eq_zero hd' h1
    apply b.repr.injective
    rw [map_zero]
    exact DFunLike.coe_injective h3
  let c : κ → O := fun i => ∑ j, T.adjugate i j • b j
  have hc : ∀ i k, Algebra.trace ℤ O (c i * b k) = if i = k then T.det else 0 := by
    intro i k
    have h1 := congrFun (congrFun (Matrix.adjugate_mul T) i) k
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero] at h1
    rw [← h1]
    simp only [c, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]
    rfl
  have hc2 : ∀ i x, Algebra.trace ℤ O (c i * x) = T.det * b.repr x i := by
    intro i x
    conv_lhs => rw [← b.sum_repr x]
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, hc, smul_eq_mul, mul_ite, mul_zero]
    simp [mul_comm]
  refine ⟨c, fun a k => nd _ _ fun l => ?_, nd _ _ fun l => ?_⟩
  · rw [mul_comm a, _root_.mul_assoc, hc2]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hc, smul_eq_mul, mul_ite, mul_zero]
    simp [mul_comm]
  · simp only [Finset.sum_mul, map_sum, _root_.mul_assoc, hc2]
    rw [← zsmul_eq_mul, map_smul, Algebra.trace_eq_matrix_trace b, smul_eq_mul, Matrix.trace, ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]

section Lin

variable {O S M κ : Type} [CommRing O] [CommRing S] [AddCommGroup M] [Module S M] [Fintype κ]
  (ρ : O →+* Module.End S M) (σ : O →+* S) (b : Module.Basis κ ℤ O) (c : κ → O)

theorem eig_proj (hc : ∀ a k, a * c k = ∑ i, b.repr (a * b i) k • c i) (a : O) (v : M) :
    ρ a (∑ i, σ (c i) • ρ (b i) v) = σ a • ∑ i, σ (c i) • ρ (b i) v := by
  have h1 : ∀ i, ρ a (ρ (b i) v) = ∑ k, b.repr (a * b i) k • ρ (b k) v := fun i => by
    rw [← Module.End.mul_apply, ← map_mul]
    conv_lhs => rw [← b.sum_repr (a * b i)]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [map_sum, map_smul, h1, Finset.smul_sum, smul_smul, ← map_mul, hc, map_zsmul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, smul_assoc]

theorem proj_eig {d : ℤ} (hc : ∑ i, c i * b i = (d : O)) (v : M) (hv : ∀ a, ρ a v = σ a • v) :
    ∑ i, σ (c i) • ρ (b i) v = (d : S) • v := by
  simp only [hv, smul_smul, ← map_mul, ← Finset.sum_smul, ← map_sum, hc, map_intCast]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem eq_of_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} (T : Fin m → TanM x t.G) {w : Fin m → S}
    {u : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x (fun i => (tv (T i)).left) w u) :
    u = (tv (∑ i, w i • T i)).left := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨z, hz, e⟩ := (GlobalTheory.LieMet.isComb_iff T w _).2 rfl
  rw [← e]
  have : y = z := funext fun i => Over.OverMorphism.ext ((hy i).trans (hz i).symm)
  rw [this]

theorem exists_eigFam {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {g : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)}
    (he : IsTanBasis t ξ e) (σ : 𝓞 E →+* R) : ∃ U : Fin g → Fin g → R, EigFam t ξ σ e U := by
  classical
  let b := RingOfIntegers.basis E
  obtain ⟨c, hc1, hc2⟩ := exists_dual b (discr_ne_zero E)
  have hbas : ∀ w, IsTanAtG t ξ w → ∃ a, IsCombAtG t ξ e a w := fun w hw => by
    have h0 : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
      have : dualMap (RingHom.id R) = RingHom.id _ := by ext s <;> simp [dualMap]
      rw [this]
      exact Spec.map_id _
    have := he.2 R (RingHom.id R) w (by rwa [h0, Category.id_comp])
    simp only [h0, h1, Category.id_comp] at this
    exact this.exists
  choose ρ hρ using fun (a : 𝓞 E) (k : Fin g) =>
    hbas _ (GlobalTheory.LieMet.isTan_tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k))))
  refine ⟨fun k j => ∑ i, σ (c i) * ρ (b i) k j, fun S _ φ => ?_⟩
  have he' := isTanBasis_bc he φ
  let T : Fin g → TanM (spMap φ ≫ ξ) t.G := fun j => GlobalTheory.LieMet.tanOf (he'.1 j)
  have hT : bcV t φ e = fun j => (tv (T j)).left := rfl
  have hA : ∀ a k, actR t.act a (T k) = ∑ j, φ (ρ a k j) • T j := fun a k => by
    refine (GlobalTheory.LieMet.isComb_iff T _ _).1 ?_
    have := GlobalTheory.GradedPieces.comb_map φ rfl (hρ a k)
    have e1 : spMap (dualMap φ) ≫ (tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k)))).left =
        (tv (actR t.act a (T k))).left := (Category.assoc _ _ _).symm
    rw [e1] at this
    exact this
  have hU : ∀ k, ∑ j, φ (∑ i, σ (c i) * ρ (b i) k j) • T j = ∑ i, (φ.comp σ) (c i) • actR t.act (b i) (T k) := fun k => by
    simp only [hA, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul, RingHom.comp_apply]
    exact Finset.sum_comm
  refine ⟨fun k u hu a => ?_, fun w v hw hv => ?_⟩
  · rw [hT] at hu
    rw [eq_of_comb T hu, GlobalTheory.ShFam.Pad.Pull.eig_iff, hU]
    exact eig_proj _ _ b c hc1 a _
  · rw [hT] at hw
    have hv0 := eq_of_comb T hw
    have hv1 : ∀ a, actR t.act a (∑ i, w i • T i) = (φ.comp σ) a • ∑ i, w i • T i := fun a => by
      rw [← GlobalTheory.ShFam.Pad.Pull.eig_iff, ← hv0]
      exact hv a
    have h2 := proj_eig _ _ b c hc2 _ hv1
    have h3 : ∑ j, (∑ k, w k • fun j => φ (∑ i, σ (c i) * ρ (b i) k j)) j • T j =
        ∑ j, (((discr E : ℤ) : S) • w) j • T j := by
      have h4 : ∑ j, (((discr E : ℤ) : S) • w) j • T j = ((discr E : ℤ) : S) • ∑ j, w j • T j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      rw [h4]
      refine Eq.trans ?_ h2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hU]
      simp only [map_sum, map_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have hu := he.2 S φ _ (GlobalTheory.LieMet.isTan_tv (∑ j, (((discr E : ℤ) : S) • w) j • T j))
    have h5 := hu.unique ((GlobalTheory.LieMet.isComb_iff T _ _).2 rfl) ((GlobalTheory.LieMet.isComb_iff T _ _).2 h3.symm)
    rw [h5]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem projSt : ProjSt :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he _ => exists_eigFam he _

end GlobalTheory.FlatModel.Proj

end
