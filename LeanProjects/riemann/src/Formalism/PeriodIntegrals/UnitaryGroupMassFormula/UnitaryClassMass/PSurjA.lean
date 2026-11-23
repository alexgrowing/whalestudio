import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.IsIntegralOfIntOE

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Fam

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : Type} [Fintype n]
  [DecidableEq n]

theorem fam_mul (e : ι → R) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (A B : ι → Matrix n n R) :
    (∑ i, e i • A i) * (∑ j, e j • B j) = ∑ i, e i • (A i * B i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he i, ite_smul, zero_smul]
  simp

theorem fam_one (e : ι → R) (hs : ∑ i, e i = 1) (X : Matrix n n R) : ∑ i, e i • X = X := by
  rw [← Finset.sum_smul, hs, one_smul]

theorem cT_fam (s : R →+* R) (e : ι → R) (A : ι → Matrix n n R) :
    cT s (∑ i, e i • A i) = ∑ i, s (e i) • cT s (A i) := by
  ext a c
  simp [cT, Matrix.sum_apply, map_sum, Matrix.smul_apply, map_mul]

end Fam

section Patch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (F E) in

abbrev finE : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

def incM (U : GL (Fin M) E) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  (U : Matrix (Fin M) (Fin M) E).map (inclR (AF F))

theorem incM_mul_inv (U : GL (Fin M) E) : incM (F := F) U * incM (F := F) U⁻¹ = 1 := by
  unfold incM
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_inv_mul (U : GL (Fin M) E) : incM (F := F) U⁻¹ * incM (F := F) U = 1 := by
  unfold incM
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_unitary (U : GL (Fin M) E) (hU : U ∈ UJ (σ : E →+* E) J) :
    cT (sigR (AF F) σ) (incM (F := F) U) * JR (AF F) J * incM (F := F) U = JR (AF F) J := by
  have := PI.UnitaryGroupMassFormula.UJClassFin.bc_mem (F := F) σ J U hU
  exact this

def patchGL (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (γ : ι → GL (Fin M) E) : GL (Fin M) (AF F ⊗[F] E) where
  val := ∑ i, e i • incM (γ i)
  inv := ∑ i, e i • incM (γ i)⁻¹
  val_inv := by
    rw [fam_mul e he]
    simp_rw [incM_mul_inv]
    exact fam_one e hs 1
  inv_val := by
    rw [fam_mul e he]
    simp_rw [incM_inv_mul]
    exact fam_one e hs 1

theorem patchGL_mem (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) : patchGL e he hs γ ∈ HR (AF F) σ J := by
  show cT (sigR (AF F) σ) (∑ i, e i • incM (γ i)) * JR (AF F) J * (∑ i, e i • incM (γ i)) = JR (AF F) J
  rw [cT_fam]
  simp_rw [hσe]
  conv_lhs => rw [← fam_one e hs (JR (AF F) J)]
  rw [fam_mul e he, fam_mul e he]
  simp_rw [incM_unitary σ J _ (hγ _)]
  exact fam_one e hs _

def patchHA (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) : HA (AF F) σ J :=
  (⟨patchGL e he hs γ, patchGL_mem σ J e he hs hσe γ hγ⟩ : HR (AF F) σ J)

theorem finE_inclR (x : E) : finE F E (inclR (AF F) x) = inclR (Af F) x := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem finMat_patch_inv (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) :
    finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹ =
      ∑ i, finE F E (e i) • ((γ i)⁻¹ : GL (Fin M) E).val.map (inclR (Af F)) := by
  have h0 : finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹ =
      (∑ i, e i • incM (F := F) (γ i)⁻¹).map (finE F E) := rfl
  rw [h0]
  ext a c
  simp [Matrix.map_apply, Matrix.sum_apply, incM, map_sum, map_mul, finE_inclR]

theorem patch_mulVec (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) (x : Fin M → E) :
    (finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x) =
      ∑ i, finE F E (e i) • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (((γ i)⁻¹ : GL (Fin M) E).val.mulVec x) := by
  rw [finMat_patch_inv, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.smul_mulVec, PI.UnitaryGroupMassFormula.UJClassFin.map_mulVec_vinc]

end Patch

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

theorem Oh_smul_latHat (L : Set (Fin M → E)) (hL : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ L, e • x ∈ L)
    {z : Af F ⊗[F] E} (hz : z ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : z • y ∈ latHat F E L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hz
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * c, PI.UnitaryGroupMassFormula.UJClassFin.intAf_mul ha hc, t • x, hL t ht x hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add y w _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [smul_neg]; exact neg_mem h1
  | zero => rw [zero_smul]; exact zero_mem _
  | add z w _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg z _ h1 => rw [neg_smul]; exact neg_mem h1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem latHat_split (L : Set (Fin M → E)) (hL : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ L, e • x ∈ L)
    (f : ι → Af F ⊗[F] E) (hf : ∀ i j, f i * f j = if i = j then f i else 0)
    (hO : ∀ i, f i ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) (y : ι → Fin M → Af F ⊗[F] E) :
    ∑ i, f i • y i ∈ latHat F E L ↔ ∀ i, f i • y i ∈ latHat F E L := by
  constructor
  · intro h j
    have h1 := Oh_smul_latHat L hL (hO j) h
    have e : f j • ∑ i, f i • y i = f j • y j := by
      rw [Finset.smul_sum]
      simp_rw [smul_smul, hf j, ite_smul, zero_smul]
      simp
    rwa [e] at h1
  · intro h
    exact AddSubgroup.sum_mem _ (fun i _ => h i)

end Split

theorem crd_int_smul {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ} (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ crdOf b L0, e • x ∈ crdOf b L0 := by
  intro e he x hx
  show ∑ i, (e • x) i • b i ∈ L0
  have : ∑ i, (e • x) i • b i = e • ∑ i, x i • b i := by
    rw [Finset.smul_sum]
    simp [smul_smul]
  rw [this]
  exact int_smul_mem L0 he hx

theorem equivFun_toLin {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (A : Matrix (Fin M) (Fin M) E) (v : V) :
    b.equivFun (Matrix.toLin b b A v) = A.mulVec (b.equivFun v) := by
  rw [Matrix.toLin_apply, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem equivFun_linOf_symm {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (U : GL (Fin M) E) (v : V) :
    b.equivFun ((linOf b U).symm v) = ((U⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun v) := by
  rw [← equivFun_toLin]
  rfl

end PI.UnitaryGroupMassFormula.UJClassMass

end
