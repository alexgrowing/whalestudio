import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EmbeddingTypeJumps

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory (SS intOE intAd)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev swp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Af F ⊗[F] E ≃ₐ[F] E ⊗[F] Af F :=
  Algebra.TensorProduct.comm F (Af F) E

def SI (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (Af F ⊗[F] E) :=
  (SS F E).comap (swp F E).toRingEquiv.toRingHom

theorem mem_SI {x : Af F ⊗[F] E} : x ∈ SI F E ↔ swp F E x ∈ SS F E := Iff.rfl

theorem intOE_of_isIntegral {x : E} (h : IsIntegral ℤ x) : x ∈ intOE E := ⟨⟨x, h⟩, rfl⟩

theorem isIntegral_of_intOE {x : E} (h : x ∈ intOE E) : IsIntegral ℤ x := by
  obtain ⟨y, rfl⟩ := h
  exact y.isIntegral_coe

theorem den_fin {ι : Type*} [Finite ι] (f : ι → Af F ⊗[F] E) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ i, (d : F) • f i ∈ SI F E := by
  let _ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  obtain ⟨d, hd, h⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_isCompact (F := F) (E := E)
    (Set.range fun i => swp F E (f i)) (Set.finite_range _).isCompact
  exact ⟨d, hd, fun i => by rw [mem_SI, map_smul]; exact h _ ⟨i, rfl⟩⟩

theorem incl_den : ∃ D : 𝓞 F, D ≠ 0 ∧
    ∀ e : E, (1 : Af F) ⊗ₜ[F] e ∈ SI F E → IsIntegral ℤ ((D : F) • e) := by
  obtain ⟨D, hD, h⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl F E
  refine ⟨D, hD, fun e he => isIntegral_of_intOE (h e ?_)⟩
  rw [mem_SI, Algebra.TensorProduct.comm_tmul] at he
  exact he

theorem coe_mul_smul (a b : 𝓞 F) (x : E) : ((a * b : 𝓞 F) : F) • x = (a : F) • (b : F) • x := by
  rw [← mul_smul]; push_cast; rfl

theorem den_E {ι : Type*} [Finite ι] (e : ι → E) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ i, IsIntegral ℤ ((d : F) • e i) := by
  obtain ⟨d, hd, h⟩ := den_fin (F := F) (E := E) fun i => (1 : Af F) ⊗ₜ[F] e i
  obtain ⟨D, hD, h'⟩ := incl_den (F := F) (E := E)
  refine ⟨D * d, mul_ne_zero hD hd, fun i => ?_⟩
  have := h' ((d : F) • e i) (by rw [TensorProduct.tmul_smul]; exact h i)
  rwa [coe_mul_smul]

theorem core {M : ℕ} (Λ : AddSubgroup (Fin M → Af F ⊗[F] E)) (c c' d1 d2 : 𝓞 F)
    (hup : ∀ y ∈ Λ, ∀ i, (c : F) • y i ∈ SI F E)
    (hlow : ∀ z : Fin M → Af F ⊗[F] E, (∀ i, z i ∈ SI F E) → (c' : F) • z ∈ Λ)
    (Gm Gi : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) (hGG : Gm * Gi = 1)
    (hd1 : ∀ i j, (d1 : F) • Gi i j ∈ SI F E) (hd2 : ∀ i j, (d2 : F) • Gm i j ∈ SI F E)
    (C : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) (hC : ∀ y ∈ Λ, (Gi * C * Gm).mulVec y ∈ Λ)
    (i j : Fin M) : ((c : F) * (d2 : F) * ((c' : F) * (d1 : F))) • C i j ∈ SI F E := by
  classical
  set z : Fin M → Af F ⊗[F] E := fun k => (d1 : F) • Gi k j with hz
  have hy : (c' : F) • z ∈ Λ := hlow z fun k => hd1 k j
  have hv := hC _ hy
  set v := (Gi * C * Gm).mulVec ((c' : F) • z) with hv'
  have hz' : z = (d1 : F) • Gi.mulVec (Pi.single j 1) := by
    ext k; simp [hz]
  have hM : Gm * (Gi * C * Gm * Gi) = C := by
    simp only [← Matrix.mul_assoc]
    rw [hGG, Matrix.one_mul, Matrix.mul_assoc, hGG, Matrix.mul_one]
  have hGv : Gm.mulVec v = ((c' : F) * (d1 : F)) • C.mulVec (Pi.single j 1) := by
    rw [hv', hz']
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul]
    rw [hM, smul_smul]
  have hvk : ∀ k, (c : F) • v k ∈ SI F E := hup v hv
  have key : ((c : F) * (d2 : F)) • (Gm.mulVec v) i ∈ SI F E := by
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have e : ((c : F) * (d2 : F)) • (Gm i k * v k) = ((d2 : F) • Gm i k) * ((c : F) • v k) := by
      rw [smul_mul_smul_comm, mul_comm (d2 : F)]
    rw [e]
    exact mul_mem (hd2 i k) (hvk k)
  have e2 : (((c' : F) * (d1 : F)) • C.mulVec (Pi.single j 1)) i = ((c' : F) * (d1 : F)) • C i j := by
    simp
  rw [hGv, e2, smul_smul] at key
  exact key

end Gen

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

def crd (W : Formalism.BasicNotions.HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

theorem int_smul_mem (W : Formalism.BasicNotions.HSpace E) {e : E} (he : IsIntegral ℤ e) {w : W.V} (hw : w ∈ W.L0) :
    e • w ∈ W.L0 := by
  let r : 𝓞 E := ⟨e, he⟩
  have h := W.L0.smul_mem r hw
  have h1 : r • w = e • w := (algebraMap_smul E r w).symm
  rw [← h1]; exact h

theorem crd_up (W : Formalism.BasicNotions.HSpace E) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ crd W, ∀ i, IsIntegral ℤ ((c : F) • x i) := by
  classical
  obtain ⟨s, hs⟩ := W.standardTuple_isLattice.fg
  obtain ⟨c, hc, h⟩ := den_E (F := F) (E := E) (fun p : s × Fin W.rank => W.frame.repr p.1 p.2)
  refine ⟨c, hc, fun x hx i => ?_⟩
  have hxi : x i = W.frame.repr (∑ k, x k • W.frame k) i := by
    rw [W.frame.repr_sum_self]
  have key : ∀ w ∈ Submodule.span (𝓞 E) (s : Set W.V), ∀ i, IsIntegral ℤ ((c : F) • W.frame.repr w i) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact fun i => h (⟨⟨y, hy⟩, i⟩)
    | zero => intro i; simpa using isIntegral_zero
    | add y z _ _ hy hz =>
      intro i
      rw [map_add, Finsupp.add_apply, smul_add]
      exact (hy i).add (hz i)
    | smul r y _ hy =>
      intro i
      have e : r • y = (r : E) • y := (algebraMap_smul E r y).symm
      rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_smul_comm]
      exact r.isIntegral_coe.mul (hy i)
  have hx' : ∑ k, x k • W.frame k ∈ Submodule.span (𝓞 E) (s : Set W.V) := by rw [hs]; exact hx
  rw [hxi]
  exact key _ hx' i

theorem alg_mul (a b : 𝓞 F) :
    algebraMap F E ((a * b : 𝓞 F) : F) = algebraMap F E (a : F) * algebraMap F E (b : F) := by
  rw [show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul]

theorem crd_low (W : Formalism.BasicNotions.HSpace E) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ crd W :=
  _root_.UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd_low W

end Lat

section Bound

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem unit_bound (W : Formalism.BasicNotions.HSpace E) (σ' : E →+* E) (hσ : ∀ a, σ' a = star a)
    (hτs : ∀ τ : E →+* ℂ, ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Formalism.UG.UJ σ' W.gram, ∀ (τ : E →+* ℂ) i j,
      ‖τ ((u : Matrix (Fin W.rank) (Fin W.rank) E) i j)‖ ≤ B := by
  classical
  have hY : ∀ τ : E →+* ℂ, ∃ Y : Matrix (Fin W.rank) (Fin W.rank) ℂ, IsUnit Y.det ∧
      ∀ y : W.V, ∑ i, ‖(Y.mulVec fun j => τ (W.frame.repr y j)) i‖ ^ 2 = (τ (W.hT y y)).re := by
    intro τ
    have h := hW τ
    rw [hsig τ] at h
    exact W.frame_of_pos τ (hτs τ) h
  choose Y hYu hYs using hY
  let R : (E →+* ℂ) → Fin W.rank → ℝ := fun τ j => Real.sqrt ((τ (W.gram j j)).re)
  let Bt : (E →+* ℂ) → ℝ := fun τ => (∑ k, ∑ l, ‖(Y τ)⁻¹ k l‖) * ∑ j, R τ j
  have hBt : ∀ τ, 0 ≤ Bt τ := fun τ =>
    mul_nonneg (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _)
      (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _)
  refine ⟨∑ τ, Bt τ, Finset.sum_nonneg fun τ _ => hBt τ, fun u hu τ i j => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (fun τ _ => hBt τ) (Finset.mem_univ τ))
  set um := (u : Matrix (Fin W.rank) (Fin W.rank) E) with hum
  have hu' : Formalism.UG.cT σ' um * W.gram * um = W.gram := hu
  let v : W.V := ∑ k, um k j • W.frame k
  have hrep : ∀ k, W.frame.repr v k = um k j := by
    intro k; simp only [v, W.frame.repr_sum_self]
  have e1 : W.hT v v = ∑ k, ∑ l, star (um k j) * (um l j * W.gram k l) := by
    simp only [v, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [RingHom.id_apply]; ring
  have e2 : (Formalism.UG.cT σ' um * W.gram * um) j j = ∑ l, ∑ k, σ' (um k j) * W.gram k l * um l j := by
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  have hform : W.hT v v = W.gram j j := by
    have h0 := congrFun (congrFun hu' j) j
    rw [e2] at h0
    rw [e1, ← h0, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hσ]; ring
  have hsum : ∑ l, ‖((Y τ).mulVec fun k => τ (um k j)) l‖ ^ 2 = (τ (W.gram j j)).re := by
    rw [← hform, ← hYs τ v]
    simp only [hrep]
  set w := (Y τ).mulVec fun k => τ (um k j) with hwdef
  have hw : ∀ l, ‖w l‖ ≤ R τ j := fun l => by
    calc ‖w l‖ = Real.sqrt (‖w l‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ R τ j := Real.sqrt_le_sqrt (by
          rw [← hsum]
          exact Finset.single_le_sum (f := fun l => ‖w l‖ ^ 2) (fun l _ => by positivity)
            (Finset.mem_univ l))
  have hzw : (fun k => τ (um k j)) = (Y τ)⁻¹.mulVec w := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec]
  have hi : τ (um i j) = ((Y τ)⁻¹.mulVec w) i := congrFun hzw i
  rw [hi]
  have h1 : ‖((Y τ)⁻¹.mulVec w) i‖ ≤ ∑ l, ‖(Y τ)⁻¹ i l‖ * ‖w l‖ := by
    simp only [Matrix.mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
  have h2 : ∑ l, ‖(Y τ)⁻¹ i l‖ * ‖w l‖ ≤ (∑ l, ‖(Y τ)⁻¹ i l‖) * R τ j := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hw l) (norm_nonneg _)
  have h3 : (∑ l, ‖(Y τ)⁻¹ i l‖) ≤ ∑ k, ∑ l, ‖(Y τ)⁻¹ k l‖ :=
    Finset.single_le_sum (f := fun k => ∑ l, ‖(Y τ)⁻¹ k l‖)
      (fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _) (Finset.mem_univ i)
  have h4 : R τ j ≤ ∑ j', R τ j' :=
    Finset.single_le_sum (f := R τ) (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ j)
  exact h1.trans (h2.trans (mul_le_mul h3 h4 (Real.sqrt_nonneg _)
    (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _)))

end Bound

section Gen2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

abbrev GamG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA (AF F) σ J) :=
  HFinIn (AF F) σ J

theorem intAd_of_intAf {a : Af F} (ha : a ∈ intAf F) : a ∈ intAd F := fun v => ha v

theorem latHat_up (W : Formalism.BasicNotions.HSpace E) : ∃ c : 𝓞 F, c ≠ 0 ∧
    ∀ y ∈ latHat F E (crd W), ∀ i, (c : F) • y i ∈ SI F E := by
  obtain ⟨c, hc, h⟩ := crd_up (F := F) W
  refine ⟨c, hc, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    intro i
    rw [← TensorProduct.tmul_smul, mem_SI, Algebra.TensorProduct.comm_tmul]
    exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.tmul_mem_SS (intOE_of_isIntegral (h x hx i)) (intAd_of_intAf ha)
  | zero => intro i; simp only [Pi.zero_apply, smul_zero]; exact (SI F E).zero_mem
  | add y z _ _ hy hz =>
    intro i; rw [Pi.add_apply, smul_add]; exact (SI F E).add_mem (hy i) (hz i)
  | neg y _ hy =>
    intro i; rw [Pi.neg_apply, smul_neg]; exact (SI F E).neg_mem (hy i)

theorem latHat_low (W : Formalism.BasicNotions.HSpace E) : ∃ c : 𝓞 F, c ≠ 0 ∧
    ∀ z : Fin W.rank → Af F ⊗[F] E, (∀ i, z i ∈ SI F E) → (c : F) • z ∈ latHat F E (crd W) := by
  classical
  obtain ⟨c, hc, h⟩ := crd_low (F := F) W
  refine ⟨c, hc, fun z hz => ?_⟩
  rw [← Finset.univ_sum_single z, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  have key : ∀ w ∈ AddSubgroup.closure {y : E ⊗[F] Af F | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a},
      ∀ x, swp F E x = w → (c : F) • Pi.single i x ∈ latHat F E (crd W) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨e, he, a, ha, rfl⟩ := hw
      intro x hx
      have hxa : x = a ⊗ₜ[F] e :=
        (swp F E).injective (by rw [hx, Algebra.TensorProduct.comm_tmul])
      subst hxa
      apply AddSubgroup.subset_closure
      refine ⟨a, fun v => ha v, Pi.single i ((c : F) • e), h i e (isIntegral_of_intOE he), ?_⟩
      funext k
      by_cases hk : k = i
      · subst hk; simp [TensorProduct.tmul_smul]
      · simp [hk]
    | zero =>
      intro x hx
      have hx0 : x = 0 := (swp F E).injective (by rw [hx, map_zero])
      subst hx0
      simp
    | add w1 w2 _ _ h1 h2 =>
      intro x hx
      have hx' : x = (swp F E).symm w1 + (swp F E).symm w2 :=
        (swp F E).injective (by rw [hx, map_add, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply])
      rw [hx', Pi.single_add, smul_add]
      exact add_mem (h1 _ (AlgEquiv.apply_symm_apply _ _)) (h2 _ (AlgEquiv.apply_symm_apply _ _))
    | neg w _ h1 =>
      intro x hx
      have hx' : x = -(swp F E).symm w :=
        (swp F E).injective (by rw [hx, map_neg, AlgEquiv.apply_symm_apply])
      rw [hx', Pi.single_neg, smul_neg]
      exact neg_mem (h1 _ (AlgEquiv.apply_symm_apply _ _))
  exact key _ (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.mem_closure_of_mem_SS (hz i)) _ rfl

theorem finMat_rat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (u : GL (Fin M) E) (h : HA (AF F) σ J)
    (hu : Formalism.UG.bc (inclR (AF F)) u = HA.mat (AF F) σ J h) :
    finMat σ J h = (u : Matrix (Fin M) (Fin M) E).map fun e => (1 : Af F) ⊗ₜ[F] e := by
  unfold finMat
  rw [← hu]
  ext i j
  simp [Formalism.UG.bc, inclR, Algebra.TensorProduct.map_tmul]

theorem stab_finite (W : Formalism.BasicNotions.HSpace E) (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (hτs : ∀ τ : E →+* ℂ, ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0))
    (K : Subgroup (HA (AF F) σ W.gram))
    (hK : ∀ k ∈ K, ∀ y ∈ latHat F E (crd W), (finMat σ W.gram k).mulVec y ∈ latHat F E (crd W))
    (g : HA (AF F) σ W.gram) : (Unfold.stab (GamG σ W.gram) K g).Finite := by
  classical
  have hmem : ∀ γ : GamG σ W.gram, ∃ u ∈ Formalism.UG.UJ (σ : E →+* E) W.gram,
      Formalism.UG.bc (inclR (AF F)) u = HA.mat (AF F) σ W.gram (γ : HA (AF F) σ W.gram) :=
    fun γ => Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp γ.2)
  choose u hu hbc using hmem
  set Gm := finMat σ W.gram g with hGm
  set Gi := finMat σ W.gram g⁻¹ with hGi
  have hGG : Gm * Gi = 1 := by rw [hGm, hGi, ← finMat_mul, mul_inv_cancel, finMat_one]
  obtain ⟨d1, hd1n, hd1⟩ := den_fin (F := F) (E := E) (fun p : Fin W.rank × Fin W.rank => Gi p.1 p.2)
  obtain ⟨d2, hd2n, hd2⟩ := den_fin (F := F) (E := E) (fun p : Fin W.rank × Fin W.rank => Gm p.1 p.2)
  obtain ⟨c, hcn, hup⟩ := latHat_up (F := F) W
  obtain ⟨c', hc'n, hlow⟩ := latHat_low (F := F) W
  obtain ⟨Dd, hDn, hD⟩ := incl_den (F := F) (E := E)
  obtain ⟨B, hB0, hB⟩ := unit_bound W (σ : E →+* E) hσ hτs hW hsig
  set s : F := (Dd : F) * ((c : F) * (d2 : F) * ((c' : F) * (d1 : F))) with hs
  have hne : ∀ x : 𝓞 F, x ≠ 0 → (x : F) ≠ 0 := fun x hx h0 => hx (by exact_mod_cast h0)
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact mul_ne_zero (hne _ hDn) (mul_ne_zero (mul_ne_zero (hne _ hcn) (hne _ hd2n))
      (mul_ne_zero (hne _ hc'n) (hne _ hd1n)))
  have hint : ∀ γ ∈ Unfold.stab (GamG σ W.gram) K g, ∀ i j,
      IsIntegral ℤ (s • (u γ : Matrix (Fin W.rank) (Fin W.rank) E) i j) := by
    intro γ hγ i j
    have hC : ∀ y ∈ latHat F E (crd W),
        (Gi * finMat σ W.gram (γ : HA (AF F) σ W.gram) * Gm).mulVec y ∈ latHat F E (crd W) := by
      intro y hy
      have h1 := hK _ hγ y hy
      rwa [finMat_mul, finMat_mul, ← Matrix.mul_assoc] at h1
    have h2 := core _ c c' d1 d2 hup hlow Gm Gi hGG (fun i j => hd1 (i, j)) (fun i j => hd2 (i, j)) _ hC i j
    rw [finMat_rat σ W.gram (u γ) _ (hbc γ), Matrix.map_apply, ← TensorProduct.tmul_smul] at h2
    have h3 := hD _ h2
    rwa [smul_smul] at h3
  have hS := NumberField.Embeddings.finite_of_norm_le (K := E) (A := ℂ)
    ((∑ τ : E →+* ℂ, ‖τ (algebraMap F E s)‖) * B)
  let f : GamG σ W.gram → Fin W.rank → Fin W.rank → E :=
    fun γ i j => s • (u γ : Matrix (Fin W.rank) (Fin W.rank) E) i j
  refine Set.Finite.of_finite_image (f := f) ?_ ?_
  · refine (Set.Finite.pi (fun _ : Fin W.rank => Set.Finite.pi (fun _ : Fin W.rank => hS))).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i j
    refine ⟨hint γ hγ i j, fun τ => ?_⟩
    show ‖τ (s • (u γ : Matrix (Fin W.rank) (Fin W.rank) E) i j)‖ ≤ _
    rw [Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (algebraMap F E s)‖)
      (fun τ _ => norm_nonneg _) (Finset.mem_univ τ)) (hB _ (hu γ) τ i j) (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  · intro γ _ γ' _ h
    have hu' : (u γ : Matrix (Fin W.rank) (Fin W.rank) E) = u γ' := by
      ext i j
      exact smul_right_injective E hs0 (congrFun (congrFun h i) j)
    have h2 : HA.mat (AF F) σ W.gram (γ : HA (AF F) σ W.gram) =
        HA.mat (AF F) σ W.gram (γ' : HA (AF F) σ W.gram) := by
      rw [← hbc, ← hbc, Units.ext hu']
    exact Subtype.ext (Subtype.ext h2)

end Gen2

section Open

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isModTopF : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩

theorem addGrpF : IsTopologicalAddGroup (Af F ⊗[F] E) := by
  have := isModTopF (F := F) (E := E)
  exact IsModuleTopology.topologicalAddGroup (R := Af F) _

def crdF {ι : Type} (b : Module.Basis ι F E) (i : ι) : Af F ⊗[F] E →ₗ[Af F] Af F where
  toFun := (TensorProduct.rid F (Af F)).toLinearMap ∘ₗ LinearMap.lTensor (Af F) (b.coord i)
  map_add' := map_add _
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a' e =>
      rw [TensorProduct.smul_tmul']
      simp [smul_eq_mul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem crdF_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (a : Af F) (e : E) :
    crdF b i (a ⊗ₜ[F] e) = b.repr e i • a := by
  simp [crdF]

theorem sum_crdF {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (x : Af F ⊗[F] E) :
    ∑ i, crdF b i x ⊗ₜ[F] b i = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [crdF_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, Module.Basis.sum_repr]
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

theorem isOpen_SI : IsOpen (SI F E : Set (Af F ⊗[F] E)) := by
  have := isModTopF (F := F) (E := E)
  have := addGrpF (F := F) (E := E)
  obtain ⟨n, b, -, -, hb, -⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_basis F E
  let O : Set (Af F ⊗[F] E) := ⋂ i, (crdF b i) ⁻¹' (intAd F : Set (Af F))
  have hO : IsOpen O := isOpen_iInter_of_finite fun i =>
    (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd (F := F)).preimage
      (IsModuleTopology.continuous_of_linearMap (crdF b i))
  have hOS : O ⊆ SI F E := by
    intro x hx
    rw [← sum_crdF b x]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [mem_SI, Algebra.TensorProduct.comm_tmul]
    exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.tmul_mem_SS (hb i) (Set.mem_iInter.mp hx i)
  have h0 : (0 : Af F ⊗[F] E) ∈ O := Set.mem_iInter.mpr fun i => by
    simp only [Set.mem_preimage, map_zero]; exact (intAd F).zero_mem
  exact AddSubgroup.isOpen_of_mem_nhds (SI F E).toAddSubgroup
    (Filter.mem_of_superset (hO.mem_nhds h0) hOS)

theorem isOpen_SIm (r : F) : IsOpen {x : Af F ⊗[F] E | r • x ∈ SI F E} := by
  have := isModTopF (F := F) (E := E)
  have e : (fun x : Af F ⊗[F] E => r • x) = fun x => algebraMap F (Af F) r • x :=
    funext fun x => (algebraMap_smul (Af F) r x).symm
  have hc : Continuous fun x : Af F ⊗[F] E => r • x := by rw [e]; exact continuous_const_smul _
  exact isOpen_SI.preimage hc

def finPr : AF F ⊗[F] E →ₛₗ[(sndA F : AF F →+* Af F)] Af F ⊗[F] E where
  toFun := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
  map_add' := map_add _
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a' e =>
      rw [TensorProduct.smul_tmul']
      simp [Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem continuous_finPr : Continuous (finPr (F := F) (E := E)) := by
  have := Unfold.isModTop (F := F) (E := E)
  have := isModTopF (F := F) (E := E)
  have := addGrpF (F := F) (E := E)
  exact IsModuleTopology.continuous_of_linearMapₛₗ (by exact continuous_snd) finPr

theorem continuous_finMat_entry (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (i j : Fin M) :
    Continuous fun h : HA (AF F) σ J => finMat σ J h i j := by
  have h1 : Continuous fun h : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j :=
    (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_val : Continuous fun g : GL (Fin M) (AF F ⊗[F] E) =>
        (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).comp continuous_subtype_val))
  exact continuous_finPr.comp h1

def SFin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) :
    Subgroup (HA (AF F) σ J) where
  carrier := {h | ∀ y, y ∈ latHat F E L ↔ (finMat σ J h).mulVec y ∈ latHat F E L}
  mul_mem' := by
    intro h h' hh hh' y
    rw [finMat_mul, ← Matrix.mulVec_mulVec, hh' y]
    exact hh _
  one_mem' := by intro y; rw [finMat_one, Matrix.one_mulVec]
  inv_mem' := by
    intro h hh y
    have e : (finMat σ J h).mulVec ((finMat σ J h⁻¹).mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]
    have := hh ((finMat σ J h⁻¹).mulVec y)
    rw [e] at this
    exact this.symm

variable [StarRing E]

theorem near (W : Formalism.BasicNotions.HSpace E) (c c' : 𝓞 F) (hc0 : (c : F) ≠ 0) (hc0' : (c' : F) ≠ 0)
    (hup : ∀ y ∈ latHat F E (crd W), ∀ i, (c : F) • y i ∈ SI F E)
    (hlow : ∀ z : Fin W.rank → Af F ⊗[F] E, (∀ i, z i ∈ SI F E) → (c' : F) • z ∈ latHat F E (crd W))
    (X : Matrix (Fin W.rank) (Fin W.rank) (Af F ⊗[F] E))
    (hX : ∀ i j, ((c : F) * (c' : F))⁻¹ • (X i j - (1 : Matrix (Fin W.rank) (Fin W.rank) (Af F ⊗[F] E)) i j) ∈ SI F E)
    (y : Fin W.rank → Af F ⊗[F] E) (hy : y ∈ latHat F E (crd W)) : X.mulVec y ∈ latHat F E (crd W) := by
  have e1 : X.mulVec y = y + (X - 1).mulVec y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  let z : Fin W.rank → Af F ⊗[F] E := fun i =>
    ∑ k, (((c : F) * (c' : F))⁻¹ • (X - 1) i k) * ((c : F) • y k)
  have hz : ∀ i, z i ∈ SI F E := fun i =>
    Subring.sum_mem _ fun k _ => mul_mem (by rw [Matrix.sub_apply]; exact hX i k) (hup y hy k)
  have e2 : (X - 1).mulVec y = (c' : F) • z := by
    funext i
    simp only [z, Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_smul_comm, smul_smul]
    have : (c' : F) * (((c : F) * (c' : F))⁻¹ * (c : F)) = 1 := by field_simp
    rw [this, one_smul]
  rw [e1, e2]
  exact add_mem hy (hlow z hz)

theorem isOpen_SFin (W : Formalism.BasicNotions.HSpace E) (σ : E →ₐ[F] E) :
    IsOpen (SFin σ W.gram (crd W) : Set (HA (AF F) σ W.gram)) := by
  have := Unfold.topGroupHA σ W.gram
  have := addGrpF (F := F) (E := E)
  obtain ⟨c, hc, hup⟩ := latHat_up (F := F) W
  obtain ⟨c', hc', hlow⟩ := latHat_low (F := F) W
  have hne : ∀ x : 𝓞 F, x ≠ 0 → (x : F) ≠ 0 := fun x hx h0 => hx (by exact_mod_cast h0)
  let r : F := ((c : F) * (c' : F))⁻¹
  let N1 : Set (HA (AF F) σ W.gram) := ⋂ p : Fin W.rank × Fin W.rank,
    (fun h => finMat σ W.gram h p.1 p.2 - (1 : Matrix (Fin W.rank) (Fin W.rank) (Af F ⊗[F] E)) p.1 p.2) ⁻¹'
      {x | r • x ∈ SI F E}
  have hN1o : IsOpen N1 := isOpen_iInter_of_finite fun p =>
    (isOpen_SIm r).preimage ((continuous_finMat_entry σ W.gram p.1 p.2).sub continuous_const)
  have h1N1 : (1 : HA (AF F) σ W.gram) ∈ N1 := Set.mem_iInter.mpr fun p => by
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, finMat_one, sub_self, smul_zero]
    exact (SI F E).zero_mem
  have hN1 : N1 ∈ nhds (1 : HA (AF F) σ W.gram) := hN1o.mem_nhds h1N1
  have hN1i : (fun h : HA (AF F) σ W.gram => h⁻¹) ⁻¹' N1 ∈ nhds (1 : HA (AF F) σ W.gram) := by
    refine continuous_inv.continuousAt.preimage_mem_nhds ?_
    rw [inv_one]; exact hN1
  have hnear : ∀ h ∈ N1, ∀ y ∈ latHat F E (crd W), (finMat σ W.gram h).mulVec y ∈ latHat F E (crd W) :=
    fun h hh y hy => near W c c' (hne c hc) (hne c' hc') hup hlow _
      (fun i j => Set.mem_iInter.mp hh (i, j)) y hy
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (Filter.inter_mem hN1 hN1i) ?_)
  rintro h ⟨hh, hhi⟩ y
  refine ⟨fun hy => hnear h hh y hy, fun hy => ?_⟩
  have := hnear h⁻¹ hhi _ hy
  rwa [Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one, Matrix.one_mulVec] at this

end Open

section Inf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem infEmb_real (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x)
    (τ : E →+* ℂ) (hτs : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hθ : IsInfEmb τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  refine (NumberField.InfiniteAdeleRing.denseRange_algebraMap (K := F)).induction_on
    (p := fun b => starRingEnd ℂ (θ (b ⊗ₜ[F] (1 : E))) = θ (b ⊗ₜ[F] (1 : E))) a
    (isClosed_eq (Complex.continuous_conj.comp hθ.2) hθ.2) (fun x => ?_)
  have e : (algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E x := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show starRingEnd ℂ (θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))) = θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))
  rw [e, hθ.1, ← hτs, hfix]

theorem infEmb_sig (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x)
    (τ : E →+* ℂ) (hτs : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hθ : IsInfEmb τ θ) (x : Ainf F ⊗[F] E) :
    θ (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ x) = starRingEnd ℂ (θ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have h1 : ∀ e' : E, a ⊗ₜ[F] e' = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] e') := fun e' => by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1 (σ e), h1 e]
    simp only [map_mul]
    rw [hθ.1, hθ.1, hσ, hτs, infEmb_real hfix τ hτs θ hθ a]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem infMat_unitary (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x)
    (τ : E →+* ℂ) (hτs : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hθ : IsInfEmb τ θ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) :
    (infMat σ J θ h).conjTranspose * J.map τ * infMat σ J θ h = J.map τ := by
  let ψ : AF F ⊗[F] E →+* ℂ :=
    θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hψs : ∀ x, ψ (sigR (AF F) σ x) = starRingEnd ℂ (ψ x) := by
    intro x
    have e : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (sigR (AF F) σ x) =
        Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ
          (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x) := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a e => simp [sigR, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (sigR (AF F) σ x)) = _
    rw [e, infEmb_sig σ hσ hfix τ hτs θ hθ]
    rfl
  have hψi : ∀ j, ψ (inclR (AF F) j) = τ j := by
    intro j
    show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] j)) = τ j
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, hθ.1]
  set H := ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hH
  have hU : Formalism.UG.cT (sigR (AF F) σ) H * JR (AF F) J * H = JR (AF F) J := h.2
  have hX : infMat σ J θ h = H.map ψ := rfl
  have h1 := congrArg (fun Z => Z.map ψ) hU
  simp only [Matrix.map_mul] at h1
  have e1 : (Formalism.UG.cT (sigR (AF F) σ) H).map ψ = (H.map ψ).conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply, hψs]
  have e2 : (JR (AF F) J).map ψ = J.map τ := by
    ext i j; simp [JR, hψi]
  rw [e1, e2] at h1
  rw [hX]; exact h1

theorem Jpq_zero (P : ℕ) : Formalism.UG.Jpq P 0 = 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem upq_of_unitary {P : ℕ} (A : Matrix (Fin P ⊕ Fin 0) (Fin P) ℂ) (Jt X : Matrix (Fin P) (Fin P) ℂ)
    (hJ : IsUnit Jt.det) (hA : A.conjTranspose * Formalism.UG.Jpq P 0 * A = Jt)
    (hX : X.conjTranspose * Jt * X = Jt) : ∃ b : Formalism.BasicNotions.UpqT P 0, Formalism.BasicNotions.UpqT.mat b * A = A * X := by
  rw [Jpq_zero, Matrix.mul_one] at hA
  let L : Matrix (Fin P) (Fin P ⊕ Fin 0) ℂ := Jt⁻¹ * A.conjTranspose
  have hLA : L * A = 1 := by
    simp only [L, Matrix.mul_assoc, hA]
    exact Matrix.nonsing_inv_mul _ hJ
  have hAL : A * L = 1 := (Matrix.mul_eq_one_comm_of_equiv (A := A) (B := L) (Equiv.sumEmpty (Fin P) (Fin 0))).mpr hLA
  let bm : Matrix (Fin P ⊕ Fin 0) (Fin P ⊕ Fin 0) ℂ := A * X * L
  have hbb : bm.conjTranspose * bm = 1 := by
    have : bm.conjTranspose * bm = L.conjTranspose * (X.conjTranspose * (A.conjTranspose * A) * X) * L := by
      simp only [bm, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hA, hX, ← hA]
    rw [show L.conjTranspose * (A.conjTranspose * A) * L = (A * L).conjTranspose * (A * L) by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [hAL, Matrix.conjTranspose_one, Matrix.one_mul]
  have hbb' : bm * bm.conjTranspose = 1 := (Matrix.mul_eq_one_comm_of_equiv (A := bm.conjTranspose) (B := bm) (Equiv.refl _)).mp hbb
  let g : GL (Fin P ⊕ Fin 0) ℂ := ⟨bm, bm.conjTranspose, hbb', hbb⟩
  have hg : g ∈ Formalism.UG.Upq P 0 := by
    show Formalism.UG.cT (starRingEnd ℂ) bm * Formalism.UG.Jpq P 0 * bm = Formalism.UG.Jpq P 0
    have e : Formalism.UG.cT (starRingEnd ℂ) bm = bm.conjTranspose := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [e, Jpq_zero, Matrix.mul_one, hbb]
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq P 0), ?_⟩
  show bm * A = A * X
  simp only [bm, Matrix.mul_assoc, hLA, Matrix.mul_one]

theorem inf_all (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x)
    (W : Formalism.BasicNotions.HSpace E) (hW : W.SigOK) (τ : E →+* ℂ) (hτs : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hsig : W.sig τ = (W.rank, 0)) (θ : Ainf F ⊗[F] E →+* ℂ) (hθ : IsInfEmb τ θ)
    (A : Matrix (Fin W.rank ⊕ Fin 0) (Fin W.rank) ℂ)
    (hA : A.conjTranspose * Formalism.UG.Jpq W.rank 0 * A = W.gram.map τ) (h : HA (AF F) σ W.gram) :
    ∃ b ∈ (Set.univ : Set (Formalism.BasicNotions.UpqT W.rank 0)),
      Formalism.BasicNotions.UpqT.mat b * A = A * infMat σ W.gram θ h := by
  have hJ : IsUnit (W.gram.map τ).det := by
    have h0 := hW τ
    rw [hsig] at h0
    obtain ⟨e, P', hP⟩ := h0
    have hd := congrArg Matrix.det hP
    rw [Jpq_zero, Matrix.det_one, Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self] at hd
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero, zero_mul] at hd
    exact zero_ne_one hd
  obtain ⟨b, hb⟩ := upq_of_unitary A _ _ hJ hA (infMat_unitary σ hσ hfix τ hτs θ hθ W.gram h)
  exact ⟨b, Set.mem_univ _, hb⟩

end Inf

section Rec

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stab_KSub_finite (D : D7) (W : HSpace D.host.E) (hW : W.SigOK)
    (hsig : ∀ τ, W.sig τ = (W.rank, 0))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (A : D.what₂.Tau → Matrix (Fin W.rank ⊕ Fin 0) (Fin W.rank) ℂ)
    (g : HA (AF D.host.F) D.sp.cm.sig W.gram) :
    (Unfold.stab (GamA D W) (KSub D W W.rank 0 θ A) g).Finite :=
  stab_finite W D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW hsig _
    (fun k hk y hy => ((show k ∈ KSet D W W.rank 0 θ A from hk).1 y).mp hy) g

theorem KSub_eq (D : D7) (W : HSpace D.host.E) (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin W.rank ⊕ Fin 0) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ).conjTranspose * Formalism.UG.Jpq W.rank 0 * A ρ = W.gram.map (embOf D ρ)) :
    (KSub D W W.rank 0 θ A : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) =
      (SFin D.sp.cm.sig W.gram (crd W) : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) := by
  ext h
  constructor
  · intro hh; exact (show h ∈ KSet D W W.rank 0 θ A from hh).1
  · intro hh
    refine (show h ∈ KSet D W W.rank 0 θ A from ⟨hh, fun ρ => ?_⟩)
    exact inf_all D.sp.cm.sig (fun _ => rfl) (fun x => (D.sp.cm.fixed _).mpr ⟨x, rfl⟩) W hW (embOf D ρ)
      (D.sp.cm.cmUnram.2.1 _) (hsig _) (θ ρ) (hθ ρ) (A ρ) (hA ρ) h

theorem measurableSet_KSub (D : D7) (W : HSpace D.host.E) (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin W.rank ⊕ Fin 0) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ).conjTranspose * Formalism.UG.Jpq W.rank 0 * A ρ = W.gram.map (embOf D ρ)) :
    MeasurableSet (KSub D W W.rank 0 θ A : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) := by
  have := Unfold.borelHA D.sp.cm.sig W.gram
  rw [KSub_eq D W hW hsig θ hθ A hA]
  exact (isOpen_SFin W D.sp.cm.sig).measurableSet

end Rec

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DefClassRest (D : D7) : Prop :=
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∃ (n : ℕ) (g : Fin n → HA (AF D.host.F) D.sp.cm.sig W.gram),
      (∀ x, ∃ i, ∃ γ : GamA D W, ∃ k : StabFin.SFin D.sp.cm.sig W.gram (L0c D W),
        x = (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k) ∧
      (∀ i j (γ γ' : GamA D W) (k k' : StabFin.SFin D.sp.cm.sig W.gram (L0c D W)),
        (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k =
          (γ' : HA (AF D.host.F) D.sp.cm.sig W.gram) * g j * k' → i = j) ∧
      ∑ i, ((Nat.card (Unfold.stab (GamA D W) (StabFin.SFin D.sp.cm.sig W.gram (L0c D W)) (g i)) : ℝ))⁻¹ =
        Formalism.HermitianLatticesTheory.mass W.hT W.L0

theorem defClassDecomp_of_rest (D : D7) (hR : DefClassRest D) : DefClassDecomp D := by
  intro W hW hsig θ hθ A hA
  have hK : KSub D W W.rank 0 θ A = StabFin.SFin D.sp.cm.sig W.gram (L0c D W) :=
    SetLike.coe_injective (StabFin.KSub_eq D W hW hsig θ hθ A hA)
  obtain ⟨n, g, hcov, hdisj, hsum⟩ := hR W hW hsig
  have := Unfold.borelHA D.sp.cm.sig W.gram
  rw [hK]
  exact ⟨(StabFin.isOpen_SFin W D.sp.cm.sig).measurableSet, n, g, hcov, hdisj,
    fun i => StabFin.stab_finite W D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW hsig _
      (fun k hk y hy => (hk y).mp hy) (g i), hsum⟩

theorem volume_mass_of_class_rest (D : D7) (hT : VolTie D) (hG : GenusMassStd D) (hR : DefClassRest D) : DefiniteVolumeEqMass D :=
  mass_volume_identity_of_class_decomp D hT hG (defClassDecomp_of_rest D hR)

theorem Link2_of_rest (hR : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps) x (i : Fm.Ix x), DefClassRest (Fm.D x i)) :
    Link2 :=
  Link2_of_decomp fun eps Fm x i => defClassDecomp_of_rest _ (hR eps Fm x i)

def ClassFin (D : D7) : Prop :=
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∃ (n : ℕ) (g : Fin n → HA (AF D.host.F) D.sp.cm.sig W.gram),
      (∀ x, ∃ i, ∃ γ : GamA D W, ∃ k : StabFin.SFin D.sp.cm.sig W.gram (L0c D W),
        x = (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k) ∧
      (∀ i j (γ γ' : GamA D W) (k k' : StabFin.SFin D.sp.cm.sig W.gram (L0c D W)),
        (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k =
          (γ' : HA (AF D.host.F) D.sp.cm.sig W.gram) * g j * k' → i = j)

def ClassMass (D : D7) : Prop :=
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∀ (n : ℕ) (g : Fin n → HA (AF D.host.F) D.sp.cm.sig W.gram),
      (∀ x, ∃ i, ∃ γ : GamA D W, ∃ k : StabFin.SFin D.sp.cm.sig W.gram (L0c D W),
        x = (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k) →
      (∀ i j (γ γ' : GamA D W) (k k' : StabFin.SFin D.sp.cm.sig W.gram (L0c D W)),
        (γ : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i * k =
          (γ' : HA (AF D.host.F) D.sp.cm.sig W.gram) * g j * k' → i = j) →
      ∑ i, ((Nat.card (Unfold.stab (GamA D W) (StabFin.SFin D.sp.cm.sig W.gram (L0c D W)) (g i)) : ℝ))⁻¹ =
        Formalism.HermitianLatticesTheory.mass W.hT W.L0

theorem defClassRest_of (D : D7) (h2 : ClassFin D) (h4 : ClassMass D) : DefClassRest D := by
  intro W hW hsig
  obtain ⟨n, g, hcov, hdisj⟩ := h2 W hW hsig
  exact ⟨n, g, hcov, hdisj, h4 W hW hsig n g hcov hdisj⟩

theorem volume_mass_of_class_items (D : D7) (hT : VolTie D) (hG : GenusMassStd D) (h2 : ClassFin D)
    (h4 : ClassMass D) : DefiniteVolumeEqMass D :=
  volume_mass_of_class_rest D hT hG (defClassRest_of D h2 h4)

theorem Link2_of_items (h2 : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps) x (i : Fm.Ix x), ClassFin (Fm.D x i))
    (h4 : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps) x (i : Fm.Ix x), ClassMass (Fm.D x i)) : Link2 :=
  Link2_of_rest fun eps Fm x i => defClassRest_of _ (h2 eps Fm x i) (h4 eps Fm x i)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
