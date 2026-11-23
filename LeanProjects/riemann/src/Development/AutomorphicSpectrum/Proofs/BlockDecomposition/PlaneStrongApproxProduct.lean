import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 Filter
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Sa2Prod

section Ring

open Matrix Formalism.UG

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def trunc (d : R) (A : Matrix n n R) : Matrix n n R := 1 + d • (A - 1)

theorem trunc_one (d : R) : trunc d (1 : Matrix n n R) = 1 := by simp [trunc]

theorem trunc_mul {d : R} (hd : d * d = d) (A B : Matrix n n R) :
    trunc d A * trunc d B = trunc d (A * B) := by
  have h : (d • (A - 1)) * (d • (B - 1)) = d • ((A - 1) * (B - 1)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd]
  unfold trunc
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add]
  abel

theorem mul_det_congr (d : R) {A B : Matrix n n R} (h : ∀ i j, d * A i j = d * B i j) :
    d * A.det = d * B.det := by
  let I : Ideal R := LinearMap.ker (LinearMap.mulLeft R d)
  have hI : ∀ x y : R, d * x = d * y → Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
    intro x y hxy
    refine Ideal.Quotient.eq.2 ?_
    change d * (x - y) = 0
    rw [mul_sub, hxy, sub_self]
  have hmap : (Ideal.Quotient.mk I).mapMatrix A = (Ideal.Quotient.mk I).mapMatrix B := by
    ext i j
    exact hI _ _ (h i j)
  have h2 : Ideal.Quotient.mk I A.det = Ideal.Quotient.mk I B.det := by
    rw [RingHom.map_det, RingHom.map_det, hmap]
  have h3 : A.det - B.det ∈ I := Ideal.Quotient.eq.1 h2
  have h4 : d * (A.det - B.det) = 0 := h3
  rw [mul_sub] at h4
  exact sub_eq_zero.1 h4

theorem det_trunc {d : R} (hd : d * d = d) {A : Matrix n n R} (hA : A.det = 1) :
    (trunc d A).det = 1 := by
  have h1 : d * (trunc d A).det = d * A.det := by
    refine mul_det_congr d fun i j => ?_
    simp only [trunc, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination ((A i j) - (1 : Matrix n n R) i j) * hd
  have h2 : (1 - d) * (trunc d A).det = (1 - d) * (1 : Matrix n n R).det := by
    refine mul_det_congr (1 - d) fun i j => ?_
    simp only [trunc, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (-((A i j) - (1 : Matrix n n R) i j)) * hd
  rw [hA] at h1
  rw [Matrix.det_one] at h2
  linear_combination h1 + h2

theorem cT_trunc (c : R →+* R) {d : R} (hc : c d = d) (A : Matrix n n R) :
    cT c (trunc d A) = trunc d (cT c A) := by
  ext i j
  simp only [cT, trunc, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, map_add, map_mul, map_sub, hc]
  have : ∀ p q : n, c ((1 : Matrix n n R) p q) = (1 : Matrix n n R) q p := by
    intro p q
    by_cases h : p = q
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  rw [this]

theorem trunc_unitary {d : R} (hd : d * d = d) {X Y J : Matrix n n R} (h : X * J * Y = J) :
    trunc d X * J * trunc d Y = J := by
  have e : trunc d X * J * trunc d Y =
      J + d • (X * J - J + J * Y - J) + (d * d) • ((X - 1) * J * (Y - 1)) := by
    unfold trunc
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, smul_add, smul_sub, smul_smul]
    abel
  rw [e, hd]
  have e2 : (X - 1) * J * (Y - 1) = X * J * Y - X * J - J * Y + J := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e2, h, add_assoc, ← smul_add]
  have e3 : X * J - J + J * Y - J + (J - X * J - J * Y + J) = 0 := by abel
  rw [e3, smul_zero, add_zero]

def truncGL {d : R} (hd : d * d = d) (g : GL n R) : GL n R where
  val := trunc d g.val
  inv := trunc d (g⁻¹).val
  val_inv := by rw [trunc_mul hd, Units.mul_inv, trunc_one]
  inv_val := by rw [trunc_mul hd, Units.inv_mul, trunc_one]

end Ring

section Adele

variable {F : Type} [Field F] [NumberField F]

theorem tendsto_fin (e : Finset (HeightOneSpectrum (𝓞 F)) → Af F)
    (he1 : ∀ T, ∀ v ∈ T, evalV F v (e T) = 1) (he0 : ∀ T, ∀ v, v ∉ T → evalV F v (e T) = 0) (a : Af F) :
    Tendsto (fun T => e T * a) atTop (nhds a) := by
  classical
  let sm : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → Af F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hsm : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
  let c : Finset (HeightOneSpectrum (𝓞 F)) → ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F) :=
    fun T v => if h : v ∉ T ∧ a v ∈ v.adicCompletionIntegers F then ⟨a v, h.2⟩ else 0
  have hc : Tendsto c atTop (nhds 0) := by
    refine tendsto_pi_nhds.2 fun v => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {v}] with T hT
    have hv : v ∈ T := hT (Finset.mem_singleton_self v)
    simp [c, hv]
  have h0 : sm 0 = 0 := rfl
  have h2 : Tendsto (fun T => sm (c T)) atTop (nhds 0) := by
    have := (hsm.tendsto 0).comp hc
    rwa [h0] at this
  have hS : {v | ¬ a v ∈ v.adicCompletionIntegers F}.Finite := Filter.eventually_cofinite.1 a.2
  have h3 := (tendsto_const_nhds (x := a)).sub h2
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop hS.toFinset] with T hT
  refine RestrictedProduct.ext _ _ fun v => ?_
  change a v - (sm (c T)) v = evalV F v (e T) * a v
  change a v - ((c T v : v.adicCompletionIntegers F) : v.adicCompletion F) = _
  by_cases hv : v ∈ T
  · have : c T v = 0 := by simp [c, hv]
    rw [this, he1 T v hv]
    simp
  · have hav : a v ∈ v.adicCompletionIntegers F := by
      by_contra hn
      exact hv (hT (hS.mem_toFinset.2 hn))
    have : c T v = ⟨a v, hav⟩ := by simp [c, hv, hav]
    rw [this, he0 T v hv]
    simp

end Adele

section Main

open GlobalTheory.Published.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem idem_mul {T : Finset (HeightOneSpectrum (𝓞 F))} {d : AF F}
    (hd : IsPlacesIdem (Finset.univ : Finset (InfinitePlace F)) T d) : d * d = d := by
  refine Prod.ext ?_ ?_
  · have h1 : d.1 = 1 := funext fun w => hd.1 w (Finset.mem_univ w)
    change d.1 * d.1 = d.1
    rw [h1, one_mul]
  · refine RestrictedProduct.ext _ _ fun v => ?_
    change evalV F v (sndA F d) * evalV F v (sndA F d) = evalV F v (sndA F d)
    by_cases hv : v ∈ T
    · rw [hd.2.2.1 v hv, one_mul]
    · rw [hd.2.2.2 v hv, zero_mul]

theorem tendsto_adele (d : Finset (HeightOneSpectrum (𝓞 F)) → AF F)
    (hd : ∀ T, IsPlacesIdem (Finset.univ : Finset (InfinitePlace F)) T (d T)) (a : AF F) :
    Tendsto (fun T => d T * a) atTop (nhds a) := by
  have h1 : ∀ T, (d T).1 = 1 := fun T => funext fun w => (hd T).1 w (Finset.mem_univ w)
  have h2 := tendsto_fin (fun T => sndA F (d T)) (fun T v hv => (hd T).2.2.1 v hv)
    (fun T v hv => (hd T).2.2.2 v hv) a.2
  have h3 := Filter.Tendsto.prodMk_nhds (tendsto_const_nhds (x := a.1)) h2
  have h3' : Tendsto (fun T => ((a.1, sndA F (d T) * a.2) : AF F)) atTop (nhds a) := h3
  have e : ∀ T, ((a.1, sndA F (d T) * a.2) : AF F) = d T * a := fun T => by
    refine Prod.ext ?_ rfl
    change a.1 = (d T).1 * a.1
    rw [h1, one_mul]
  exact h3'.congr e

theorem tendsto_tensor (d : Finset (HeightOneSpectrum (𝓞 F)) → AF F)
    (hd : ∀ T, IsPlacesIdem (Finset.univ : Finset (InfinitePlace F)) T (d T)) (x : AF F ⊗[F] E) :
    Tendsto (fun T => algebraMap (AF F) (AF F ⊗[F] E) (d T) * x) atTop (nhds x) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  induction x using TensorProduct.induction_on with
  | zero => simpa using tendsto_const_nhds
  | tmul a e =>
    have hc : Continuous fun t : AF F => t • ((1 : AF F) ⊗ₜ[F] e) := continuous_smul.comp (continuous_id.prodMk continuous_const)
    have h := (hc.tendsto a).comp (tendsto_adele d hd a)
    have e1 : ∀ t : AF F, t • ((1 : AF F) ⊗ₜ[F] e) = t ⊗ₜ[F] e := fun t => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1] at h
    refine h.congr fun T => ?_
    simp only [Function.comp_apply, e1, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.algebraMap_self, RingHom.id_apply]
  | add x y hx hy => simpa only [mul_add] using hx.add hy

theorem tendsto_trunc {M : ℕ} (d : Finset (HeightOneSpectrum (𝓞 F)) → AF F)
    (hd : ∀ T, IsPlacesIdem (Finset.univ : Finset (InfinitePlace F)) T (d T))
    (A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    Tendsto (fun T => trunc (algebraMap (AF F) (AF F ⊗[F] E) (d T)) A) atTop (nhds A) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (tendsto_const_nhds (x := (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j)).add
    (tendsto_tensor d hd ((A - 1) i j))
  have e : (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + (A - 1) i j = A i j := by simp
  rw [e] at h
  exact h

def truncHA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {d : AF F}
    (hd : algebraMap (AF F) (AF F ⊗[F] E) d * algebraMap (AF F) (AF F ⊗[F] E) d =
      algebraMap (AF F) (AF F ⊗[F] E) d) (g : HA (AF F) σ J) : HA (AF F) σ J :=
  let g' : HR (AF F) σ J := g
  (⟨truncGL hd g'.1, by
    have h : Formalism.UG.cT (sigR (AF F) σ) (g'.1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) * JR (AF F) J *
        (g'.1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = JR (AF F) J := g'.2
    change Formalism.UG.cT (sigR (AF F) σ) (trunc _ (g'.1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) * JR (AF F) J *
        trunc _ (g'.1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = JR (AF F) J
    rw [cT_trunc _ (sigR_algebraMap σ d)]
    exact trunc_unitary hd h⟩ : HR (AF F) σ J)

end Main

section Main2

open GlobalTheory.Published.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mat_truncHA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {d : AF F}
    (hd : algebraMap (AF F) (AF F ⊗[F] E) d * algebraMap (AF F) (AF F ⊗[F] E) d =
      algebraMap (AF F) (AF F ⊗[F] E) d) (g : HA (AF F) σ J) :
    ((HA.mat (AF F) σ J (truncHA σ J hd g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      trunc (algebraMap (AF F) (AF F ⊗[F] E) d) (HA.mat (AF F) σ J g).1 := rfl

theorem truncHA_mem (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {d : AF F}
    (hd : algebraMap (AF F) (AF F ⊗[F] E) d * algebraMap (AF F) (AF F ⊗[F] E) d =
      algebraMap (AF F) (AF F ⊗[F] E) d) {g : HA (AF F) σ J} (hg : g ∈ SUAdelic σ J) :
    truncHA σ J hd g ∈ SUSupp σ J d := by
  refine ⟨mem_SUAdelic.2 ?_, fun i j => ?_⟩
  · rw [mat_truncHA]
    exact det_trunc hd (mem_SUAdelic.1 hg)
  · rw [mat_truncHA]
    simp only [trunc, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hd]

theorem tendsto_truncHA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (d : Finset (HeightOneSpectrum (𝓞 F)) → AF F)
    (hd : ∀ T, IsPlacesIdem (Finset.univ : Finset (InfinitePlace F)) T (d T))
    (hi : ∀ T, algebraMap (AF F) (AF F ⊗[F] E) (d T) * algebraMap (AF F) (AF F ⊗[F] E) (d T) =
      algebraMap (AF F) (AF F ⊗[F] E) (d T)) (g : HA (AF F) σ J) :
    Tendsto (fun T => truncHA σ J (hi T) g) atTop (nhds g) := by
  let g' : HR (AF F) σ J := g
  have h1 := tendsto_trunc (E := E) d hd (g'.1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
  have h2 := tendsto_trunc (E := E) d hd ((g'.1)⁻¹ : GL (Fin M) (AF F ⊗[F] E)).val
  have h3 : Tendsto (fun T => truncGL (hi T) g'.1) atTop (nhds g'.1) := by
    refine Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_
    exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)
  exact tendsto_subtype_rng.2 h3

end Main2

theorem propProd : Sa2.PropProd := by
  intro F E _ _ _ _ _ σ M J N hN hS g hg
  classical
  choose d hd using fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
    GlobalTheory.Published.StrongApprox.exists_isPlacesIdem (F := F) Finset.univ T
  have hi : ∀ T, algebraMap (AF F) (AF F ⊗[F] E) (d T) * algebraMap (AF F) (AF F ⊗[F] E) (d T) =
      algebraMap (AF F) (AF F ⊗[F] E) (d T) := fun T => by rw [← map_mul, idem_mul (hd T)]
  exact hN.mem_of_tendsto (tendsto_truncHA σ J d hd hi g)
    (Eventually.of_forall fun T => hS _ _ _ (hd T) (truncHA_mem σ J (hi T) hg))

end GlobalTheory.CompanionTheory.Sa2Prod
