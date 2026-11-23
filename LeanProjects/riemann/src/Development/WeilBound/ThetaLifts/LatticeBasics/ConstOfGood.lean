import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DeterminantProjection
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.WeilBound.ThetaLifts.LatticeBasics.ConstIdele

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DeterminantProjection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem det_ne_zero_of_sig {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := fun z => by
  obtain ⟨e, A, hA⟩ := h
  let q : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr e)
  have := congrArg Matrix.det (show (Aᵀ.submatrix id q * M.submatrix q q) * (A.map star).submatrix q id = Matrix.fromBlocks 1 0 0 (-1) by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]; exact hA)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, z, mul_zero, zero_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) this.symm

omit [NumberField E] in
theorem hermND_transpose {B : Base F E} {X : Spc F E n} {r s : ℕ} (h : X.IsHerm σ B r s) : IsHermND σ X.Jᵀ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨fun i j => h.herm j i, fun z => det_ne_zero_of_sig (h.sig w) ?_⟩
  rw [Matrix.det_transpose] at z
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, z, map_zero]

omit [NumberField E] in
theorem mem_UG_of {J : Matrix (Fin n) (Fin n) E} {g : GL (Fin n) (AE F E)} :
    g ∈ UG (cA σ) (incM F J) ↔ g ∈ HR (AF F) σ Jᵀ := by
  change (g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J) ↔ (g.1.map (sigR (AF F) σ))ᵀ * (incM F J)ᵀ * g.1 = (incM F J)ᵀ
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    show (cA σ : AE F E → AE F E) = sigR (AF F) σ from funext cA_eq]

def sec {A : Type} [CommRing A] (R : Matrix (Fin n) (Fin n) A) (h : R * R = R) : A →* Matrix (Fin n) (Fin n) A where
  toFun z := 1 + (z - 1) • R
  map_one' := by simp
  map_mul' a b := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, add_assoc, ← add_smul]
    congr 2
    ring

theorem su_mem (hS : GlobalTheory.Published.StrongApproxSU) (hc : IsCMExt F E σ) {X : Spc F E n} (hJ : IsHermND σ X.Jᵀ) (hn : 2 ≤ n)
    (L : Subgroup (UA σ X.J)) (hL : IsClosed (L : Set (UA σ X.J))) (hr : ratU σ X.J ≤ L) {v : Pl F}
    (hv : ∀ u ∈ UAt σ X (evFin F v), u ∈ L) {ε : AF F} {e : AE F E} (hε : GlobalTheory.Published.IsPlacesIdem ∅ {v} ε) (e1 : e * e = e)
    (e2 : e * sigR (AF F) σ e = 0) (e3 : e + sigR (AF F) σ e = algebraMap (AF F) (AE F E) ε) (g : UA σ X.J)
    (hg : (mat g).det = 1) : g ∈ L := by
  let ι : HA (AF F) σ X.Jᵀ → UA σ X.J := fun x => ⟨HA.mat _ _ _ x, mem_UG_of.2 (show HR (AF F) σ X.Jᵀ from x).2⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have z : ∀ t, evFin F v t = 0 → t * ε = 0 := fun t ht => by
    refine Prod.ext (funext fun w => (congrArg (t.1 w * ·) (hε.2.1 w (Finset.notMem_empty w))).trans (mul_zero _))
      (FiniteAdeleRing.ext _ fun u => ?_)
    by_cases hu : u = v
    · subst hu
      exact (congrArg (· * ε.2 u) ht).trans (zero_mul _)
    · exact (congrArg (t.2 u * ·) (hε.2.2.2 u fun x => hu (Finset.mem_singleton.1 x))).trans (mul_zero _)
  refine closure_minimal (t := ι ⁻¹' L) ?_ (hL.preimage hι) (hS F E σ hc n _ hn hJ ∅ {v} ε hε
    (GlobalTheory.Published.StrongApprox.not_isCompact_split σ hn hJ v ε (hε.2.2.1 v (Finset.mem_singleton_self v)) e e1 e2 e3)
    (⟨g.1, mem_UG_of.1 g.2⟩ : HR (AF F) σ X.Jᵀ) (GlobalTheory.Published.StrongApprox.mem_SUAdelic.2 hg))
  rintro _ ⟨γ, ⟨-, y, -, hy⟩, h, ⟨-, hh⟩, rfl⟩
  have h1 : ι γ ∈ L := hr ⟨y, hy⟩
  have h2 : ι h ∈ L := hv _ fun t ht => Matrix.ext fun i j => by
    refine (congrArg (t • ·) (hh i j).symm).trans ?_
    rw [← Algebra.smul_def, smul_smul, z t ht, zero_smul, Matrix.zero_apply]
  exact mul_mem h1 h2

theorem exists_sec (hc : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ Jᵀ) (hn : 1 ≤ n) :
    ∃ S : normOne (cA σ) →* UA σ J, Continuous S ∧ (∀ z, (mat (S z)).det = (z.1 : (AE F E)ˣ)) ∧
      (∀ z : normOne (cA σ), (∃ k : E, k ≠ 0 ∧ ((z.1 : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) k) → S z ∈ ratU σ J) ∧
      ∀ (z : normOne (cA σ)) (t : AF F), t • (((z.1 : (AE F E)ˣ) : AE F E) - 1) = 0 → t • (mat (S z) - 1) = 0 := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hσ := GlobalTheory.UnitaryHeckeBaseChange.sig_sig hc
  obtain ⟨u, hu⟩ := exists_aniso (σ : E →+* E) hσ Jᵀ (fun i j => hJ.1 j i) hJ.2
  have ha := inv_mul_cancel₀ hu
  have hb : (σ : E →+* E) (hsq (σ : E →+* E) Jᵀ u)⁻¹ = (hsq (σ : E →+* E) Jᵀ u)⁻¹ := by
    rw [map_inv₀, sigma_hsq (σ : E →+* E) hσ _ fun i j => hJ.1 j i]
  generalize (hsq (σ : E →+* E) Jᵀ u)⁻¹ = b at ha hb
  let i : E →+* AE F E := inclR (F := F) (AF F)
  have hR := proj_idem' _ _ _ _ ha
  have hi : ∀ a, i ((σ : E →+* E) a) = sigR (AF F) σ (i a) := fun _ => rfl
  have hA : i b * hsq (sigR (AF F) σ) (Jᵀ.map i) (fun k => i (u k)) = 1 := by
    rw [← hsq_map i (σ : E →+* E) _ hi, ← map_mul, ha, map_one]
  have h1 := proj_unitary (sigR (AF F) σ) (GlobalTheory.UnitaryHeckeBaseChange.cA_cA hc) (Jᵀ.map i)
    (fun a b => (hi _).symm.trans (congrArg i (hJ.1 b a))) _ _ hA (by rw [← hi, hb])
  have h2 := det_proj' _ _ _ _ hA
  rw [← proj_map i (σ : E →+* E) (sigR (AF F) σ) hi] at h1 h2
  generalize proj (σ : E →+* E) Jᵀ u b = R at hR h1 h2
  have hR' : R.map i * R.map i = R.map i := by rw [← Matrix.map_mul, hR]
  have cS : Continuous (sec _ hR') := continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  refine ⟨((Units.map (sec _ hR')).comp (normOne (cA σ)).subtype).codRestrict _ fun z =>
    mem_UG_of.2 (h1 z.1 (by rw [← cA_eq, mul_comm]; exact mem_normOne.1 z.2)),
    ((Continuous.units_map _ cS).comp continuous_subtype_val).subtype_mk _, fun z => h2 _,
    fun z ⟨k, k0, hk⟩ => ⟨Units.map (sec _ hR) (Units.mk0 k k0), Units.ext (Matrix.ext fun a b => ?_)⟩, fun z t ht => ?_⟩
  · change i ((1 : Matrix _ _ E) a b + (k - 1) * R a b) =
      (1 : Matrix _ _ (AE F E)) a b + (((z.1 : (AE F E)ˣ) : AE F E) - 1) * i (R a b)
    rw [hk, map_add, map_mul, map_sub, map_one, Matrix.one_apply, Matrix.one_apply, apply_ite i, map_one, map_zero]
  · change t • (1 + (((z.1 : (AE F E)ˣ) : AE F E) - 1) • R.map i - 1) = 0
    rw [add_sub_cancel_left, ← smul_assoc, ht, zero_smul]

omit [NumberField E] in
theorem conj_mem_UAt {X : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {u : UA σ X.J} (hu : u ∈ UAt σ X ev) (g : UA σ X.J) :
    g⁻¹ * u * g ∈ UAt σ X ev := fun t ht => by
  have : mat (g⁻¹ * u * g) - 1 = mat g⁻¹ * (mat u - 1) * mat g := by
    rw [mul_sub, sub_mul, mul_one]
    exact congrArg₂ (· - ·) rfl (Units.inv_mul g.1).symm
  rw [this, ← smul_mul_assoc, ← mul_smul_comm, hu t ht, mul_zero, zero_mul]

theorem mem_of_good (hS : GlobalTheory.Published.StrongApproxSU) (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (hc : IsCMExt F E σ)
    [IsGalois ℚ E] {X : Spc F E n} (hJ : IsHermND σ X.Jᵀ) (hn : 2 ≤ n) (T : Finset (Pl F)) (L : Subgroup (UA σ X.J))
    (hL : IsClosed (L : Set (UA σ X.J))) (hr : ratU σ X.J ≤ L)
    (hv : ∀ v ∉ T, SplitsFully E v → ∀ u ∈ UAt σ X (evFin F v), u ∈ L) (g : UA σ X.J) : g ∈ L := by
  obtain ⟨v, a, b, ε, e, hε, e1, e2, e3⟩ := exists_split hH hc T
  obtain ⟨S, cS, s1, s2, s3⟩ := exists_sec hc hJ (by omega)
  have hg : IsUnit (incM F X.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ (Matrix.det_transpose X.J ▸ hJ.2)).map _
  let z : normOne (cA σ) := ⟨_, det_mem_normOne ⟨fun a b => congrArg (inclR (F := F) (AF F)) (hJ.1 b a), hg⟩ g⟩
  have h1 : S z ∈ L := normOne_mem hH hc T (L.comap S) (hL.preimage cS) (fun z h => hr (s2 z h))
    (fun v a b z hz => hv v a b _ fun t ht => s3 z t (hz t ht)) z
  have h2 : g * S z⁻¹ ∈ L := su_mem hS hc hJ hn L hL hr (hv v a b) hε e1 e2 e3 _ (by
    rw [show mat (g * S z⁻¹) = mat g * mat (S z⁻¹) from rfl, Matrix.det_mul, s1]
    exact z.1.mul_inv)
  simpa using mul_mem h2 h1

theorem constOfGood_of (hS : GlobalTheory.Published.StrongApproxSU) (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) : ConstOfGood := by
  intro F E _ _ _ _ _ σ B n X r s hB hX hn T f hf hr hv g
  have := hB.galois
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let L : Subgroup (UA σ X.J) :=
    { carrier := ⋂ g, {x | f (x * g) = f g}
      one_mem' := Set.mem_iInter.2 fun g => congrArg f (one_mul g)
      mul_mem' := fun {a b} ha hb => Set.mem_iInter.2 fun g =>
        (congrArg f (mul_assoc a b g)).trans ((Set.mem_iInter.1 ha _).trans (Set.mem_iInter.1 hb _))
      inv_mem' := fun {a} ha => Set.mem_iInter.2 fun g =>
        (Set.mem_iInter.1 ha _).symm.trans (congrArg f (mul_inv_cancel_left a g)) }
  have := mem_of_good hS hH hB.cm (hermND_transpose hX) hn T L
    (isClosed_iInter fun g => isClosed_eq (hf.comp (continuous_mul_const g)) continuous_const)
    (fun γ h => Set.mem_iInter.2 (hr γ h)) (fun v a b u hu => Set.mem_iInter.2 fun g =>
      (congrArg f (by group)).trans (hv v a b _ (conj_mem_UAt hu g) g)) g
  exact (congrArg f (mul_one g)).symm.trans (Set.mem_iInter.1 this 1)

end GlobalTheory.ThK.Dbl

end
