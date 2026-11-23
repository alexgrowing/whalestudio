import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVDx

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix

section Mat

variable {A : Type} [CommRing A] (s : A →+* A)

theorem hform_mul_right {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (Y i) (fun l => ∑ k, C j k * Y k l) =
      ∑ k, Formalism.UG.hform s Jm (Y i) (Y k) * C j k := by

  unfold Formalism.UG.hform
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hform_mul_left {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (fun l => ∑ k, C i k * Y k l) (Y j) =
      ∑ k, s (C i k) * Formalism.UG.hform s Jm (Y k) (Y j) := by

  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pol_solve {a : ℕ} (h πA : A) (hh : h + h = 1) (hsh : s h = h)
    (Γ Tm Tinv Sm E0 : Matrix (Fin a) (Fin a) A) (hΓ : Γ = Tm + πA • E0)
    (hTT : Tm * Tinv = 1) (hTs : (Tinv.map s)ᵀ * Tm = 1) (hS : ∀ i k, s (Sm k i) = Sm i k) :
    Γ * ((h • (Tinv * Sm))ᵀ)ᵀ + ((h • (Tinv * Sm))ᵀ).map s * Γ =
      Sm + πA • (h • (E0 * Tinv * Sm + Sm * (Tinv.map s)ᵀ * E0)) := by

  have hSm : (Smᵀ).map s = Sm := by
    ext i k
    simp [Matrix.map_apply, Matrix.transpose_apply, hS]
  have h2 : ((h • (Tinv * Sm))ᵀ).map s = h • (Sm * (Tinv.map s)ᵀ) := by
    ext i k
    simp [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, hS, hsh, map_sum]
  have e1 : Tm * (Tinv * Sm) = Sm := by rw [← Matrix.mul_assoc, hTT, Matrix.one_mul]
  have e2 : Sm * ((Tinv.map s)ᵀ * Tm) = Sm := by rw [hTs, Matrix.mul_one]
  have key : ∀ X Y Z : Matrix (Fin a) (Fin a) A,
      h • (Z + πA • X) + (h • Z + πA • h • Y) = (h + h) • Z + πA • h • (X + Y) := by
    intro X Y Z
    simp only [smul_add, add_smul]
    rw [smul_comm h πA X]
    abel
  rw [Matrix.transpose_transpose, h2, hΓ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [e1, e2, key, hh, one_smul]

end Mat

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

def intA (z : Fv F v ⊗[F] E) : Prop :=
  ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F

variable {b v}

theorem intA_add {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z + w) := by
  intro k
  rw [map_add, Finsupp.add_apply]
  exact add_mem (hz k) (hw k)

theorem intA_sum {ι : Type} (t : Finset ι) (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ t, intA b v (f i)) :
    intA b v (∑ i ∈ t, f i) := by

  intro k
  rw [map_sum, Finsupp.finset_sum_apply]
  exact sum_mem fun i hi => hf i hi k

theorem intA_smul {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {z : Fv F v ⊗[F] E}
    (hz : intA b v z) : intA b v (c • z) := by
  intro k
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hc (hz k)

theorem intA_incl (e : E) (h : ∀ m, algebraMap F (Fv F v) (b.repr e m) ∈ v.adicCompletionIntegers F) :
    intA b v (inclR (Fv F v) e) := by
  intro k
  have he : inclR (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e := rfl
  rw [he, Algebra.TensorProduct.basis_repr_tmul]
  simpa using h k

theorem incl_eq_tmul (e : E) : inclR (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e := rfl

theorem intA_mul (hg : ∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈
      v.adicCompletionIntegers F)
    {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z * w) := by

  have hB : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b) k = inclR (Fv F v) (b k) := fun k => by
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z,
    ← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr w, Finset.sum_mul_sum]
  refine intA_sum _ _ fun k _ => intA_sum _ _ fun l _ => ?_
  rw [smul_mul_smul_comm, hB, hB, ← map_mul]
  exact intA_smul (mul_mem (hz k) (hw l)) (intA_incl _ (hg k l))

theorem sigR_incl (σ : E →ₐ[F] E) (e : E) :
    sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by

  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem sigR_smul (σ : E →ₐ[F] E) (c : Fv F v) (z : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • z) = c • sigR (Fv F v) σ z := by

  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem intA_sig (σ : E →ₐ[F] E)
    (hg : ∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : intA b v z) : intA b v (sigR (Fv F v) σ z) := by

  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z, map_sum]
  refine intA_sum _ _ fun k _ => ?_
  rw [sigR_smul, Algebra.TensorProduct.basis_apply, ← incl_eq_tmul, sigR_incl]
  exact intA_smul (hz k) (intA_incl _ (hg k))

theorem aaInt (x : F) : ∀ᶠ v in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by

  first
  | exact (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  | (rw [Filter.eventually_cofinite]
     refine (HeightOneSpectrum.Support.finite (𝓞 F) x).subset fun v hv => ?_
     simp only [Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hv
     simpa [HeightOneSpectrum.Support, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hv)

def GoodV (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) : Prop :=
  (∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (J i j) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ m, algebraMap F (Fv F v) (b.repr (1 / 2 : E) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (Tinv i j) m) ∈ v.adicCompletionIntegers F)

theorem goodV_aa (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) :
    ∀ᶠ v in cofinite, GoodV b v σ J Tinv := by

  simp only [GoodV, Filter.eventually_and, Filter.eventually_all]
  exact ⟨fun k l m => aaInt _, fun k m => aaInt _, fun i j m => aaInt _, fun m => aaInt _,
    fun i j m => aaInt _⟩

end Int

theorem map_smulSub' {K V X : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup X]
    [Module K X] (D : V →+ X) (hDs : ∀ (t : K) w, D (t • w) = t • D w) (t : K)
    (L : AddSubgroup V) : (smulSub t L).map D = smulSub t (L.map D) := by

  simp only [smulSub, AddSubgroup.map_map]
  congr 1
  ext w
  simp [hDs]

theorem hensAA_holds : HensAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a ha1 ha2 X0 hT hdet d b
  have : FiniteDimensional F E := Module.Finite.of_basis b
  have hσ := sigma_invol σ hCM.2.2.2
  set TE := gramE σ J X0 with hTE
  have hu : IsUnit TE.det := isUnit_iff_ne_zero.2 hdet
  filter_upwards [goodV_aa b σ J TE⁻¹] with v hg
  obtain ⟨g1, g2, g3, g4, g5⟩ := hg
  intro y hy hyT
  have := locallyCompact_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Fv F v ⊗[F] E) := by
    obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
    exact h.isEmbedding.t2Space
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  obtain ⟨hπ0, hπ, hπO⟩ := unifV_spec v
  set π := unifV v with hπdef
  set s := sigR (Fv F v) σ with hsdef
  set L := latSub b v a M with hLdef
  have hLc : IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    PositiveNearLattice.isCompact_latV b v a M
  have hπL : ∀ w ∈ L, π • w ∈ L := fun w hw => LatFactsW.smul_mem_latSub b v hπO hw
  have hyL : ∀ i l, intA b v (y i l) := fun i l => hy i l

  let D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a :=
    { toFun := fun W => ⟨gramB (Fv F v) σ J y W, gramB_mem (Fv F v) σ hσ J hJ.1 y W⟩
      map_zero' := by
        apply Subtype.ext
        funext i j
        simp [gramB, hR, Formalism.UG.hform]
      map_add' := fun W W' => Subtype.ext (gramB_add_right (Fv F v) σ J y W W') }
  have hDv : ∀ W, (D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J y W :=
    fun _ => rfl
  have hDc : Continuous D :=
    ((continuous_gramB (Fv F v) σ J).comp (Continuous.prodMk continuous_const continuous_id)).subtype_mk _
  have hDs : ∀ (t : Fv F v) W, D (t • W) = t • D W := by
    intro t W
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J y (t • W) i j = t • gramB (Fv F v) σ J y W i j
    simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, smul_add]

  have hJi : ∀ i j, intA b v (JR (Fv F v) J i j) := fun i j => intA_incl _ (g3 i j)
  have hmul : ∀ {z w : Fv F v ⊗[F] E}, intA b v z → intA b v w → intA b v (z * w) :=
    fun hz hw => intA_mul g1 hz hw
  have hsig : ∀ {z : Fv F v ⊗[F] E}, intA b v z → intA b v (s z) := fun hz => intA_sig σ g2 hz
  have hRi : ∀ x z : Fin M → Fv F v ⊗[F] E, (∀ l, intA b v (x l)) → (∀ l, intA b v (z l)) →
      intA b v (hR (Fv F v) σ J x z) := by
    intro x z hx hz
    have e : hR (Fv F v) σ J x z = ∑ i, ∑ j, s (x i) * JR (Fv F v) J i j * z j := rfl
    rw [e]
    exact intA_sum _ _ fun i _ => intA_sum _ _ fun j _ =>
      hmul (hmul (hsig (hx i)) (hJi i j)) (hz j)
  have hgB : ∀ u w, u ∈ L → w ∈ L →
      (⟨gramB (Fv F v) σ J u w, gramB_mem (Fv F v) σ hσ J hJ.1 u w⟩ : HermR (Fv F v) σ a) ∈
        hermO b v σ a := by
    intro u w hu' hw' i j
    exact intA_add (hRi _ _ (hu' i) (hw' j)) (hRi _ _ (hw' i) (hu' j))
  have hgR : ∀ w, w ∈ L → gramH (Fv F v) σ hσ J hJ.1 w ∈ hermO b v σ a := by
    intro w hw' i j
    exact hRi _ _ (hw' i) (hw' j)
  have hOsm : ∀ {c : Fv F v}, c ∈ v.adicCompletionIntegers F → ∀ S ∈ hermO b v σ a,
      c • S ∈ hermO b v σ a := by
    intro c hc S hS i j
    exact intA_smul hc (hS i j)

  set Tm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := TE.map (inclR (Fv F v)) with hTm
  set Ti : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := TE⁻¹.map (inclR (Fv F v)) with hTi
  have hTT : Tm * Ti = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _)
      (map_one _)]
  have hTh : (TE.map (σ : E →+* E))ᵀ = TE := by
    ext i j
    exact hT i j
  have hE1 : (TE⁻¹.map (σ : E →+* E))ᵀ * TE = 1 := by
    calc (TE⁻¹.map (σ : E →+* E))ᵀ * TE
        = (TE⁻¹.map (σ : E →+* E))ᵀ * (TE.map (σ : E →+* E))ᵀ := by rw [hTh]
      _ = ((TE.map (σ : E →+* E)) * (TE⁻¹.map (σ : E →+* E)))ᵀ := (Matrix.transpose_mul _ _).symm
      _ = ((TE * TE⁻¹).map (σ : E →+* E))ᵀ := by rw [Matrix.map_mul]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one]
  have hTs : (Ti.map s)ᵀ * Tm = 1 := by
    have e : (Ti.map s)ᵀ = ((TE⁻¹.map (σ : E →+* E))ᵀ).map (inclR (Fv F v)) := by
      ext i j
      simp [hTi, hsdef, sigR_incl]
    rw [e, hTm, ← Matrix.map_mul, hE1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hTii : ∀ i j, intA b v (Ti i j) := fun i j => intA_incl _ (g5 i j)

  set h : Fv F v ⊗[F] E := inclR (Fv F v) (1 / 2 : E) with hhdef
  have hh : h + h = 1 := by rw [hhdef, ← map_add, add_halves, map_one]
  have hsh : s h = h := by
    rw [hsdef, hhdef, sigR_incl]
    congr 1
    rw [map_div₀, map_one, map_ofNat]
  have hhi : intA b v h := intA_incl _ g4

  have hyT' : gramH (Fv F v) σ hσ J hJ.1 y - hermOf (Fv F v) σ TE hT ∈ smulSub π (hermO b v σ a) := by
    have := hyT
    simp only [hF, zero_add, pow_one] at this
    exact this
  obtain ⟨E0h, hE0, hE0eq⟩ := (mem_smulSub _ _ _).1 hyT'
  set πA : Fv F v ⊗[F] E := algebraMap (Fv F v) (Fv F v ⊗[F] E) π with hπA
  have hΓ : gramR (Fv F v) σ J y = Tm + πA • (E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := by
    have e := congrArg Subtype.val hE0eq
    have e2 : π • (E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramR (Fv F v) σ J y - Tm := e
    rw [hπA, algebraMap_smul, e2]
    abel

  have hbase : ∀ S ∈ hermO b v σ a, ∃ l ∈ L, S - D l ∈ smulSub π (hermO b v σ a) := by
    intro S hS
    set Sm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := S.1 with hSm
    have hSh : ∀ i k, s (Sm k i) = Sm i k := fun i k => S.2 i k
    set C : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := (h • (Ti * Sm))ᵀ with hC
    set W : Fin a → Fin M → Fv F v ⊗[F] E := fun j l => ∑ k, C j k * y k l with hW
    have hCi : ∀ j k, intA b v (C j k) := by
      intro j k
      simp only [hC, Matrix.transpose_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
      exact hmul hhi (intA_sum _ _ fun m _ => hmul (hTii k m) (hS m j))
    have hWL : W ∈ L := fun j l => intA_sum _ _ fun k _ => hmul (hCi j k) (hyL k l)
    have hgW : gramB (Fv F v) σ J y W = gramR (Fv F v) σ J y * Cᵀ + C.map s * gramR (Fv F v) σ J y := by
      ext i j
      simp only [gramB, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      rw [show hR (Fv F v) σ J (y i) (W j) = ∑ k, hR (Fv F v) σ J (y i) (y k) * C j k from
          hform_mul_right s (JR (Fv F v) J) y C i j,
        show hR (Fv F v) σ J (W i) (y j) = ∑ k, s (C i k) * hR (Fv F v) σ J (y k) (y j) from
          hform_mul_left s (JR (Fv F v) J) y C i j]
      rfl
    have hsol := pol_solve s h πA hh hsh (gramR (Fv F v) σ J y) Tm Ti Sm E0h hΓ hTT hTs hSh
    set R : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
      h • ((E0h : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * Ti * Sm + Sm * (Ti.map s)ᵀ * E0h)
      with hRdef
    have hRi' : ∀ i j, intA b v (R i j) := by
      intro i j
      simp only [hRdef, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply, smul_eq_mul]
      refine hmul hhi (intA_add (intA_sum _ _ fun k _ => hmul (intA_sum _ _ fun m _ =>
        hmul (hE0 i m) (hTii m k)) (hS k j)) (intA_sum _ _ fun k _ => hmul (intA_sum _ _ fun m _ =>
        hmul (hS i m) (hsig (hTii k m))) (hE0 k j)))
    have hsol' : gramR (Fv F v) σ J y * Cᵀ + C.map s * gramR (Fv F v) σ J y = Sm + πA • R := hsol
    have hDW : (D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = Sm + π • R := by
      rw [hDv, hgW, hsol', hπA, algebraMap_smul]
    set Rh : HermR (Fv F v) σ a := π⁻¹ • (D W - S) with hRh
    have hRhv : (Rh : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = R := by
      show π⁻¹ • ((D W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) - Sm) = R
      rw [hDW, add_sub_cancel_left, inv_smul_smul₀ hπ0]
    have hRhO : Rh ∈ hermO b v σ a := by
      intro i j
      show intA b v ((Rh : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j)
      rw [hRhv]
      exact hRi' i j
    refine ⟨W, hWL, (mem_smulSub _ _ _).2 ⟨-Rh, (hermO b v σ a).neg_mem hRhO, ?_⟩⟩
    rw [hRh, smul_neg, smul_inv_smul₀ hπ0, neg_sub]
  have hreach := reach_of_approx π hπ L hLc hπL D hDc hDs (hermO b v σ a)
    (LatFactsW.isCompact_hermO b v σ a) hbase
  have hDL : L.map D = hermO b v σ a := by
    refine le_antisymm ?_ fun p hp => ?_
    · rintro _ ⟨W, hW, rfl⟩
      exact hgB y W hy hW
    · obtain ⟨l, hl, e⟩ := hreach p hp
      exact AddSubgroup.mem_map.2 ⟨l, hl, e⟩
  refine ⟨D, fun n => ?_, fun n Z hZ W hW => ?_⟩
  · rw [lamF, hF, map_smulSub' D hDs, hDL]
  · obtain ⟨z, hz, rfl⟩ := (mem_smulSub _ _ _).1 hZ
    obtain ⟨w, hw, rfl⟩ := (mem_smulSub _ _ _).1 hW
    rw [hF, mem_smulSub]
    have hB : (⟨gramB (Fv F v) σ J z w, gramB_mem (Fv F v) σ hσ J hJ.1 z w⟩ :
        HermR (Fv F v) σ a) ∈ hermO b v σ a := hgB z w hz hw
    have hG : π ^ n • gramH (Fv F v) σ hσ J hJ.1 w ∈ hermO b v σ a :=
      hOsm (pow_mem hπO n) _ (hgR w hw)
    refine ⟨_, (hermO b v σ a).add_mem hB hG, ?_⟩
    apply Subtype.ext
    show π ^ (n + 1 + 1) • (gramB (Fv F v) σ J z w + π ^ n • gramR (Fv F v) σ J w) =
      gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z + unifV v ^ (n + 1) • w) -
        gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z) - gramB (Fv F v) σ J y (unifV v ^ (n + 1) • w)
    have e2 : gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z + unifV v ^ (n + 1) • w) -
        gramR (Fv F v) σ J (y + unifV v ^ (0 + 1) • z) - gramB (Fv F v) σ J y (unifV v ^ (n + 1) • w) =
        gramB (Fv F v) σ J (unifV v ^ (0 + 1) • z) (unifV v ^ (n + 1) • w) +
          gramR (Fv F v) σ J (unifV v ^ (n + 1) • w) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, gramB, gramR, Pi.add_apply, hR_add_left,
        hR_add_right]
      ring
    have gBs : ∀ (t t' : Fv F v) (u u' : Fin a → Fin M → Fv F v ⊗[F] E),
        gramB (Fv F v) σ J (t • u) (t' • u') = (t * t') • gramB (Fv F v) σ J u u' := by
      intro t t' u u'
      ext i j
      simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, Matrix.smul_apply]
      module
    have gRs : ∀ (t : Fv F v) (u : Fin a → Fin M → Fv F v ⊗[F] E),
        gramR (Fv F v) σ J (t • u) = (t * t) • gramR (Fv F v) σ J u := by
      intro t u
      ext i j
      simp only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right, Matrix.smul_apply]
      module
    rw [e2, gBs, gRs, ← hπdef]
    module

end PI.VolStabS
