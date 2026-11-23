import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelWithoutExtraPlaces
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem gram_herm (hc : CMData F E) (S : HSpace E) : IsHerm (hc.sig : E →+* E) S.gram := by
  unfold IsHerm cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, HSpace.gram]
  show starRingEnd E (S.hT (S.frame j) (S.frame i)) = S.hT (S.frame i) (S.frame j)
  have h := S.herm
  first
    | exact h.eq (S.frame j) (S.frame i)
    | exact h (S.frame j) (S.frame i)

theorem gram_det_unit (hc : CMData F E) (S : HSpace E) : IsUnit S.gram.det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hrow : ∀ i, S.hT (S.frame i) (∑ j, v j • S.frame j) = 0 := by
    intro i
    have h1 : ∑ j, S.gram i j * v j = 0 := by
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct] using this
    rw [map_sum]
    refine (Finset.sum_congr rfl (fun j _ => ?_)).trans h1
    rw [map_smul, smul_eq_mul]
    exact mul_comm _ _
  have hzero : ∑ j, v j • S.frame j = 0 := by
    apply S.nondeg.2
    intro x
    have hx : S.hT.flip (∑ j, v j • S.frame j) = 0 :=
      S.frame.ext (fun i => by simpa using hrow i)
    simpa using LinearMap.congr_fun hx x
  have hv' := (Fintype.linearIndependent_iff.mp S.frame.linearIndependent) v hzero
  exact hv0 (funext hv')

theorem sig_conj (hc : CMData F E) (τ : E →+* ℂ) : τ.comp (hc.sig : E →+* E) = (starRingEnd ℂ).comp τ := by
  ext a
  exact hc.cmUnram.2.1 τ a

theorem exists_above (hc : CMData F E) (ι : F →+* ℝ) :
    ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι := by
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hc.deg2]; norm_num)
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  let φ : E →ₐ[F] ℂ := IsAlgClosed.lift
  refine ⟨φ.toRingHom, ?_⟩
  ext a
  exact φ.commutes a

private theorem star_dotProduct_Jpq_mulVec_eq_sub (p q : ℕ) (Z : Fin p ⊕ Fin q → ℂ) : star Z ⬝ᵥ (Jpq p q *ᵥ Z) =
    ∑ a, star (Z (Sum.inl a)) * Z (Sum.inl a) - ∑ b, star (Z (Sum.inr b)) * Z (Sum.inr b) := by
  rw [Jpq, Matrix.fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero, zero_add, Matrix.neg_mulVec, Pi.neg_apply, Pi.add_apply,
    Pi.star_apply, Function.comp_apply, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem gram_totDef (hc : CMData F E) (S : HSpace E) (hs : S.SigOK) (hd : S.IsDefinite) : IsTotDef hc.sig S.gram := by
  classical
  unfold IsTotDef
  refine ⟨hc.totReal, fun ι => ?_⟩
  unfold IsDefiniteAt
  obtain ⟨τ, hτ⟩ := exists_above hc ι
  have hJ : ∀ i j, star (S.gram i j) = S.gram j i := fun i j => by
    have hH := gram_herm hc S
    exact congrFun (congrFun hH j) i
  have hfix : ∀ x : Fin S.rank → E,
      star (hform (hc.sig : E →+* E) S.gram x x) = hform (hc.sig : E →+* E) S.gram x x := by
    intro x
    show star (∑ i, ∑ j, star (x i) * S.gram i j * x j) = ∑ i, ∑ j, star (x i) * S.gram i j * x j
    simp only [star_sum, star_mul', star_star, hJ]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hσ : ∀ z : E, τ ((hc.sig : E →+* E) z) = star (τ z) := fun z => RingHom.congr_fun (sig_conj hc τ) z
  have hτform : ∀ x : Fin S.rank → E, τ (hform (hc.sig : E →+* E) S.gram x x) =
      star (fun i => τ (x i)) ⬝ᵥ ((S.gram.map τ) *ᵥ (fun i => τ (x i))) := by
    intro x
    simp only [hform, map_sum, map_mul, hσ, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => mul_assoc _ _ _))
  have hre : ∀ (p q : ℕ) (e : Fin S.rank ≃ Fin p ⊕ Fin q) (y : Fin S.rank → ℂ),
      star y ⬝ᵥ ((S.gram.map τ) *ᵥ y) =
        star (y ∘ e.symm) ⬝ᵥ (((S.gram.map τ).reindex e e) *ᵥ (y ∘ e.symm)) := by
    intro p q e y
    simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply, Matrix.submatrix_apply, Pi.star_apply,
      Function.comp_apply]
    symm
    exact Fintype.sum_equiv e.symm _ _ (fun k => by
      congr 1
      exact Fintype.sum_equiv e.symm _ _ (fun l => rfl))
  have hconj : ∀ (p q : ℕ), HasSignature (S.gram.map τ) p q → ∀ y : Fin S.rank → ℂ, y ≠ 0 →
      ∃ Z : Fin p ⊕ Fin q → ℂ, Z ≠ 0 ∧ star y ⬝ᵥ ((S.gram.map τ) *ᵥ y) = star Z ⬝ᵥ (Jpq p q *ᵥ Z) := by
    intro p q hS y hy
    obtain ⟨e, P, hP⟩ := hS
    have hw : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
        ((↑P⁻¹ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (y ∘ e.symm)) = y ∘ e.symm := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have hcT : cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
        (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by
      ext i j
      rfl
    refine ⟨(↑P⁻¹ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (y ∘ e.symm), ?_, ?_⟩
    · intro h0
      apply hy
      funext i
      have h1 := congrFun hw (e i)
      rw [h0, Matrix.mulVec_zero] at h1
      simpa using h1.symm
    · rw [hre p q e y]
      generalize (↑P⁻¹ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (y ∘ e.symm) = z at hw ⊢
      rw [← hw, ← hP, hcT, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hJpq : ∀ (p q : ℕ) (Z : Fin p ⊕ Fin q → ℂ), star Z ⬝ᵥ (Jpq p q *ᵥ Z) =
      ∑ a, star (Z (Sum.inl a)) * Z (Sum.inl a) - ∑ b, star (Z (Sum.inr b)) * Z (Sum.inr b) :=
    fun p q Z => star_dotProduct_Jpq_mulVec_eq_sub p q Z
  have hpos : ∀ {m : ℕ} (u : Fin m → ℂ), u ≠ 0 → ∃ r : ℝ, 0 < r ∧ ∑ a, star (u a) * u a = (r : ℂ) := by
    intro m u hu
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hu
    refine ⟨∑ b, Complex.normSq (u b), Finset.sum_pos' (fun b _ => Complex.normSq_nonneg _)
      ⟨a, Finset.mem_univ _, Complex.normSq_pos.mpr ha⟩, ?_⟩
    push_cast
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Complex.normSq_eq_conj_mul_self]
    try rfl
  have hval : ∀ x : Fin S.rank → E, ∃ a : F, algebraMap F E a = hform (hc.sig : E →+* E) S.gram x x ∧
      ((ι a : ℝ) : ℂ) = star (fun i => τ (x i)) ⬝ᵥ ((S.gram.map τ) *ᵥ (fun i => τ (x i))) := by
    intro x
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp ((hc.fixed _).1 (hfix x))
    refine ⟨a, ha, ?_⟩
    rw [← hτform x, ← ha]
    have h2 := RingHom.congr_fun hτ a
    simp only [RingHom.comp_apply] at h2
    rw [h2]
    first
      | rfl
      | simp
  have hyne : ∀ x : Fin S.rank → E, x ≠ 0 → (fun i => τ (x i)) ≠ 0 := by
    intro x hx hy
    apply hx
    funext i
    exact (map_eq_zero τ).mp (congrFun hy i)
  rcases hd τ with hsig | hsig
  · left
    intro x hx
    obtain ⟨a, ha, hι⟩ := hval x
    refine ⟨a, ha, ?_⟩
    have hS : HasSignature (S.gram.map τ) S.rank 0 := by
      have h := hs τ
      rw [hsig] at h
      exact h
    obtain ⟨Z, hZ, hZeq⟩ := hconj _ _ hS _ (hyne x hx)
    rw [hZeq, hJpq] at hι
    have hu : (fun b => Z (Sum.inl b)) ≠ 0 := by
      intro hu
      apply hZ
      funext k
      rcases k with b | b
      · exact congrFun hu b
      · exact b.elim0
    obtain ⟨r, hr, hrr⟩ := hpos _ hu
    have h3 : ((ι a : ℝ) : ℂ) = (r : ℂ) := by
      rw [hι, ← hrr]
      simp
    have h4 := Complex.ofReal_injective h3
    linarith
  · right
    intro x hx
    obtain ⟨a, ha, hι⟩ := hval x
    refine ⟨a, ha, ?_⟩
    have hS : HasSignature (S.gram.map τ) 0 S.rank := by
      have h := hs τ
      rw [hsig] at h
      exact h
    obtain ⟨Z, hZ, hZeq⟩ := hconj _ _ hS _ (hyne x hx)
    rw [hZeq, hJpq] at hι
    have hu : (fun b => Z (Sum.inr b)) ≠ 0 := by
      intro hu
      apply hZ
      funext k
      rcases k with b | b
      · exact b.elim0
      · exact congrFun hu b
    obtain ⟨r, hr, hrr⟩ := hpos _ hu
    have h3 : ((ι a : ℝ) : ℂ) = ((-r : ℝ) : ℂ) := by
      rw [hι, Complex.ofReal_neg, ← hrr]
      simp
    have h4 := Complex.ofReal_injective h3
    linarith

theorem finite_classSet_of_finiteIndex {G : Type} [Group G] (Γ K K' : Subgroup G) (_h : K' ≤ K) [Finite (ClassSet Γ K)]
    [Finite (K ⧸ K'.subgroupOf K)] : Finite (ClassSet Γ K') := by
  classical
  let f : ClassSet Γ K × (K ⧸ K'.subgroupOf K) → ClassSet Γ K' :=
    fun p => DoubleCoset.mk Γ K' (Quotient.out p.1 * ((Quotient.out p.2 : K) : G))
  refine Finite.of_surjective f ?_
  intro q
  obtain ⟨g, rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨γ, k, hγ, hk, hout⟩ := DoubleCoset.mk_out_eq_mul Γ K g
  let kinv : K := ⟨k⁻¹, K.inv_mem hk⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K) kinv
  refine ⟨(DoubleCoset.mk Γ K g, (QuotientGroup.mk kinv : K ⧸ K'.subgroupOf K)), ?_⟩
  have e1 : (Quotient.out (DoubleCoset.mk Γ K g) : G) = γ * g * k := hout
  have e2 : ((Quotient.out (QuotientGroup.mk kinv : K ⧸ K'.subgroupOf K) : K) : G) = k⁻¹ * ((h : K) : G) :=
    (congrArg (fun x : K => (x : G)) hh).trans rfl
  show DoubleCoset.mk Γ K' (Quotient.out (DoubleCoset.mk Γ K g) *
      ((Quotient.out (QuotientGroup.mk kinv : K ⧸ K'.subgroupOf K) : K) : G)) = DoubleCoset.mk Γ K' g
  rw [e1, e2, DoubleCoset.eq]
  refine ⟨γ⁻¹, Γ.inv_mem hγ, ((h : K) : G)⁻¹, K'.inv_mem (Subgroup.mem_subgroupOf.mp h.2), ?_⟩
  group

def LevFinIdx (hc : CMData F E) (S : HSpace E) (Lb : Submodule (𝓞 E) (Fin S.rank → E))
    (U : Subgroup (GL (Fin S.rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) : Prop :=
  U ≤ levelAfL hc.sig S.gram Lb ∧ U.relIndex (levelAfL hc.sig S.gram Lb) ≠ 0

theorem finite_classSet_lev (hc : CMData F E) (S : HSpace E) (hs : S.SigOK) (hd : S.IsDefinite)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin S.rank → E)) = ⊤)
    (U : Subgroup (GL (Fin S.rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (hU : LevFinIdx hc S Lb U) :
    Finite (ClassSet (Formalism.L2.Herm.UFin hc S) (U.subgroupOf (Formalism.L2.Herm.UAf hc S))) := by
  have hL : Finite (ClassSet (Formalism.L2.Herm.UFin hc S) ((levelAfL hc.sig S.gram Lb).subgroupOf (Formalism.L2.Herm.UAf hc S))) :=
    Formalism.UG.Final.ClassSetFiniteL F E (Fin S.rank) hc.sig S.gram (sig_conj hc) (gram_herm hc S) (gram_det_unit hc S)
      (gram_totDef hc S hs hd) Lb hfin hspan
  have hle : U.subgroupOf (Formalism.L2.Herm.UAf hc S) ≤ (levelAfL hc.sig S.gram Lb).subgroupOf (Formalism.L2.Herm.UAf hc S) :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hU.1 (Subgroup.mem_subgroupOf.1 hx))
  have hq : Finite (((levelAfL hc.sig S.gram Lb).subgroupOf (Formalism.L2.Herm.UAf hc S)) ⧸
      (U.subgroupOf (Formalism.L2.Herm.UAf hc S)).subgroupOf ((levelAfL hc.sig S.gram Lb).subgroupOf (Formalism.L2.Herm.UAf hc S))) := by
    have h0 : (U.subgroupOf (Formalism.L2.Herm.UAf hc S)).relIndex
        ((levelAfL hc.sig S.gram Lb).subgroupOf (Formalism.L2.Herm.UAf hc S)) ≠ 0 := by
      rw [Subgroup.relIndex_subgroupOf (show levelAfL hc.sig S.gram Lb ≤ Formalism.L2.Herm.UAf hc S from inf_le_left)]
      exact hU.2
    have : ((U.subgroupOf (Formalism.L2.Herm.UAf hc S)).subgroupOf
        ((levelAfL hc.sig S.gram Lb).subgroupOf (Formalism.L2.Herm.UAf hc S))).FiniteIndex := ⟨h0⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  exact @finite_classSet_of_finiteIndex _ _ (Formalism.L2.Herm.UFin hc S)
    ((levelAfL hc.sig S.gram Lb).subgroupOf (Formalism.L2.Herm.UAf hc S)) (U.subgroupOf (Formalism.L2.Herm.UAf hc S)) hle hL hq

theorem finite_classSet_step {R : Ranks} (sp : Spaces R F E) {gp : Fin 2 → ℕ} {T f i : ℕ} (hi : i ≤ R.m)
    {Q : Finset (HeightOneSpectrum (𝓞 F))} (lev : Formalism.L2.Herm.StepLevelQ sp.cm (sp.X i) gp T f Q)
    (hU : LevFinIdx sp.cm (sp.X i) lev.Lb lev.U) :
    Finite (ClassSet (Formalism.L2.Herm.UFin sp.cm (sp.X i)) (lev.U.subgroupOf (Formalism.L2.Herm.UAf sp.cm (sp.X i)))) := finite_classSet_lev sp.cm (sp.X i) (sp.X_sig i) (sp.X_def i hi) lev.Lb lev.Lb_fin lev.Lb_span
    lev.U hU

end Formalism.L2.G
