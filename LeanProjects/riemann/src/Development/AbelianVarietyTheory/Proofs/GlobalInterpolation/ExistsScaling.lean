import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeActions
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section
namespace GlobalTheory.LatticeDensity

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.SelfDualLatticeCompare

section Algebra

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))

theorem sigR_algebraMap (a : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) a) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) a := by
  show sigR (Fv F v) σ (a ⊗ₜ[F] (1 : E)) = a ⊗ₜ[F] (1 : E)
  simp [sigR]

theorem algebraMap_inj : Function.Injective (algebraMap (Fv F v) (Fv F v ⊗[F] E)) :=
  FaithfulSMul.algebraMap_injective _ _

theorem algebraMap_mem_iff (a : Fv F v) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) a ∈ SelfDualLatticeActions.OEv E v ↔ a ∈ v.adicCompletionIntegers F := by
  rw [mem_integralClosure_iff, isIntegral_algebraMap_iff (algebraMap_inj v)]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  · intro h
    exact isIntegral_algebraMap (x := (⟨a, h⟩ : v.adicCompletionIntegers F))

theorem trace_mem (hσ : IsCMExt F E σ) {z : Fv F v ⊗[F] E} (hz : z ∈ SelfDualLatticeActions.OEv E v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
  rw [← algebraMap_mem_iff (E := E), trace_tensor _ hσ]
  exact add_mem hz (SelfDualLatticeActions.sigR_mem v σ hz)

theorem exists_dual (hσ : IsCMExt F E σ) {w : Fv F v ⊗[F] E} {t n : v.adicCompletionIntegers F}
    (hw : w ∈ SelfDualLatticeActions.OEv E v) (hD : IsUnit (t ^ 2 - 4 * n))
    (ht : w + sigR (Fv F v) σ w = algebraMap (Fv F v) (Fv F v ⊗[F] E) t)
    (hn : w * sigR (Fv F v) σ w = algebraMap (Fv F v) (Fv F v ⊗[F] E) n) :
    ∃ c : Fin 2 → Fv F v ⊗[F] E, (∀ i, c i ∈ SelfDualLatticeActions.OEv E v) ∧
      (∀ z, z = algebraMap (Fv F v) _ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c 0 * z)) +
        algebraMap (Fv F v) _ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c 1 * z)) * w) ∧
      ∀ a b : Fv F v,
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
          (c 0 * (algebraMap (Fv F v) _ a + algebraMap (Fv F v) _ b * w)) = a ∧
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
          (c 1 * (algebraMap (Fv F v) _ a + algebraMap (Fv F v) _ b * w)) = b := by
  obtain ⟨d, hd⟩ := hD.exists_right_inv
  have hd' : (w - sigR (Fv F v) σ w) ^ 2 * algebraMap (Fv F v) (Fv F v ⊗[F] E) d = 1 := by
    have h1 := congrArg (fun x : v.adicCompletionIntegers F =>
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (x : Fv F v)) hd
    push_cast at h1
    have h4 : ((4 : v.adicCompletionIntegers F) : Fv F v) = 4 := rfl
    simp only [h4, map_ofNat, ← ht, ← hn] at h1
    linear_combination h1
  have hdm : algebraMap (Fv F v) (Fv F v ⊗[F] E) d ∈ SelfDualLatticeActions.OEv E v :=
    (algebraMap_mem_iff v _).2 d.2
  have hw' := SelfDualLatticeActions.sigR_mem v σ hw
  refine ⟨![-sigR (Fv F v) σ w * ((w - sigR (Fv F v) σ w) * algebraMap (Fv F v) _ d),
    (w - sigR (Fv F v) σ w) * algebraMap (Fv F v) _ d], ?_, fun z => ?_, fun a b => ⟨?_, ?_⟩⟩
  · rw [Fin.forall_fin_two]
    exact ⟨mul_mem (neg_mem hw') (mul_mem (sub_mem hw hw') hdm), mul_mem (sub_mem hw hw') hdm⟩
  · simp only [trace_tensor _ hσ, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_neg,
      map_sub, sigR_sigR _ hσ, sigR_algebraMap]
    linear_combination (-z) * hd'
  · apply algebraMap_inj (E := E) v
    simp only [trace_tensor _ hσ, Matrix.cons_val_zero, map_mul, map_neg, map_add,
      map_sub, sigR_sigR _ hσ, sigR_algebraMap]
    linear_combination (algebraMap (Fv F v) (Fv F v ⊗[F] E) a) * hd'
  · apply algebraMap_inj (E := E) v
    simp only [trace_tensor _ hσ, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_add,
      map_sub, sigR_sigR _ hσ, sigR_algebraMap]
    linear_combination (algebraMap (Fv F v) (Fv F v ⊗[F] E) b) * hd'

variable {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem hR_eq (x y : Fin M → Fv F v ⊗[F] E) : hR (Fv F v) σ J x y =
    Matrix.toBilin' (JR (Fv F v) J) (fun i => sigR (Fv F v) σ (x i)) y := by
  rw [Matrix.toBilin'_apply]
  rfl

theorem hR_sum_right (x : Fin M → Fv F v ⊗[F] E) (z : Fin M → Fv F v ⊗[F] E)
    (b : Fin M → Fin M → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ i, z i • b i) = ∑ i, z i * hR (Fv F v) σ J x (b i) := by
  simp only [hR_eq, map_sum, map_smul, smul_eq_mul]

theorem hR_sum_left (y : Fin M → Fv F v ⊗[F] E) (z : Fin M → Fv F v ⊗[F] E)
    (b : Fin M → Fin M → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (∑ i, z i • b i) y = ∑ i, sigR (Fv F v) σ (z i) * hR (Fv F v) σ J (b i) y := by
  have : (fun j => sigR (Fv F v) σ ((∑ i, z i • b i) j)) =
      ∑ i, sigR (Fv F v) σ (z i) • fun j => sigR (Fv F v) σ (b i j) := by
    funext j
    simp [Finset.sum_apply]
  simp only [hR_eq, this, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem hR_smul_left (x y : Fin M → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_add_left (x x' y : Fin M → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + x') y = hR (Fv F v) σ J x y + hR (Fv F v) σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem exists_frame {L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)}
    (hL : SelfDualLatticeActions.IsSelfDualLat v σ J L) (hb : SelfDualLatticeActions.HasOrthonormalBasis v σ J L) :
    ∃ g : (Fin M → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin M → Fv F v ⊗[F] E),
      (∀ y, y ∈ L ↔ ∀ i, g y i ∈ SelfDualLatticeActions.OEv E v) ∧
      ∀ x y, hR (Fv F v) σ J x y = ∑ i, sigR (Fv F v) σ (g x i) * g y i := by
  obtain ⟨e, he⟩ := hb
  have hon : ∀ i j, hR (Fv F v) σ J (e i) (e j) = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun he i) j
    rw [Matrix.one_apply] at this
    exact this
  have hco : ∀ (z : Fin M → Fv F v ⊗[F] E) i,
      hR (Fv F v) σ J (e i) (∑ j, z j • (e j : SelfDualLatticeActions.Wv E v M)) = z i := fun z i => by
    simp [hR_sum_right, hon]
  let f : (Fin M → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] (Fin M → Fv F v ⊗[F] E) :=
    Fintype.linearCombination _ fun j => (e j : SelfDualLatticeActions.Wv E v M)
  have hf : ∀ z, f z = ∑ j, z j • (e j : SelfDualLatticeActions.Wv E v M) := fun z =>
    Fintype.linearCombination_apply _ _ _
  have hLf : ∀ y ∈ L, ∃ z : Fin M → SelfDualLatticeActions.OEv E v, f (fun i => z i) = y := fun y hy => by
    refine ⟨fun i => e.repr ⟨y, hy⟩ i, ?_⟩
    have := congrArg Subtype.val (e.sum_repr ⟨y, hy⟩)
    rw [hf]
    rw [Submodule.coe_sum] at this
    exact this
  have hbij : Function.Bijective f := by
    constructor
    · intro z z' h
      funext i
      rw [← hco z i, ← hco z' i, ← hf, ← hf, h]
    · rw [← LinearMap.range_eq_top, eq_top_iff, ← hL.2.1, Submodule.span_le]
      intro y hy
      obtain ⟨z, hz⟩ := hLf y hy
      exact ⟨_, hz⟩
  refine ⟨(LinearEquiv.ofBijective f hbij).symm, fun y => ?_, fun x y => ?_⟩
  · obtain ⟨z, rfl⟩ := (LinearEquiv.ofBijective f hbij).surjective y
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.ofBijective_apply]
    constructor
    · intro h i
      obtain ⟨z', hz'⟩ := hLf _ h
      rw [← hbij.1 hz']
      exact (z' i).2
    · intro h
      rw [hf]
      exact L.sum_mem fun i _ => L.smul_mem (⟨z i, h i⟩ : SelfDualLatticeActions.OEv E v) (e i).2
  · obtain ⟨x, rfl⟩ := (LinearEquiv.ofBijective f hbij).surjective x
    obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective f hbij).surjective y
    simp only [LinearEquiv.symm_apply_apply]
    simp only [LinearEquiv.ofBijective_apply, hf, hR_sum_left, hco]

theorem exists_norm (hσ : IsCMExt F E σ) {w : Fv F v ⊗[F] E} {t n : v.adicCompletionIntegers F}
    (hw : w ∈ SelfDualLatticeActions.OEv E v) (hD : IsUnit (t ^ 2 - 4 * n))
    (ht : w + sigR (Fv F v) σ w = algebraMap (Fv F v) (Fv F v ⊗[F] E) t)
    (hn : w * sigR (Fv F v) σ w = algebraMap (Fv F v) (Fv F v ⊗[F] E) n)
    {u : Fv F v} (hu : Valued.v u = 1) :
    ∃ a ∈ SelfDualLatticeActions.OEv E v, a * sigR (Fv F v) σ a = algebraMap (Fv F v) (Fv F v ⊗[F] E) u := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  let c : SelfDualLatticeActions.OEv E v →+* SelfDualLatticeActions.OEv E v :=
    (sigR (Fv F v) σ).restrict (SelfDualLatticeActions.OEv E v).toSubring (SelfDualLatticeActions.OEv E v).toSubring
      fun _ => SelfDualLatticeActions.sigR_mem v σ
  have hc : ∀ x, (c x : Fv F v ⊗[F] E) = sigR (Fv F v) σ x := fun _ => rfl
  obtain ⟨d, hd, h1, h2⟩ := exists_dual v hσ hw hD ht hn
  have hb : ∀ r, c (algebraMap (v.adicCompletionIntegers F) _ r) = algebraMap _ _ r :=
    fun r => Subtype.ext (sigR_algebraMap v _)
  let u' : v.adicCompletionIntegers F := ⟨u, hu.le⟩
  have hu' : IsUnit u' := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hu
  obtain ⟨x, hx⟩ := GlobalTheory.UnramifiedHermitian.exists_norm_eq_of_henselian
    (R₀ := v.adicCompletionIntegers F) c (fun x => Subtype.ext (sigR_sigR _ hσ _)) hb
    (fun x hx => by
      have hx' : sigR (Fv F v) σ x = x := congrArg Subtype.val hx
      refine ⟨⟨_, trace_mem v hσ (mul_mem (hd 0) x.2)⟩, Subtype.ext ?_⟩
      have h3 := trace_tensor (Fv F v) hσ (d 0 * x)
      have h4 := trace_tensor (Fv F v) hσ (d 0 * 1)
      have h5 := (h2 1 0).1
      rw [map_zero, map_one, zero_mul, add_zero] at h5
      rw [h5, mul_one, map_one] at h4
      rw [map_mul (sigR (Fv F v) σ), hx', ← add_mul, ← h4, one_mul] at h3
      exact h3)
    ⟨⟨w, hw⟩, isUnit_of_mul_isUnit_left (y := ⟨w, hw⟩ - c ⟨w, hw⟩) (by
      convert hD.map (algebraMap _ (SelfDualLatticeActions.OEv E v))
      apply Subtype.ext
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      push_cast
      change _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (t : Fv F v) ^ 2 -
        4 * algebraMap (Fv F v) (Fv F v ⊗[F] E) (n : Fv F v)
      rw [hc, ← ht, ← hn]
      ring)⟩ (hb u') (hu'.map _)
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

end Algebra

section Coordinates

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F)) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem exists_coords (hσ : IsCMExt F E σ) (hJ : IsHermND σ J)
    {w : Fv F v ⊗[F] E} {t n : v.adicCompletionIntegers F}
    (hw : w ∈ SelfDualLatticeActions.OEv E v) (hD : IsUnit (t ^ 2 - 4 * n))
    (ht : w + sigR (Fv F v) σ w = algebraMap (Fv F v) (Fv F v ⊗[F] E) t)
    (hn : w * sigR (Fv F v) σ w = algebraMap (Fv F v) (Fv F v ⊗[F] E) n)
    {L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)}
    (hL : SelfDualLatticeActions.IsSelfDualLat v σ J L) (hb : SelfDualLatticeActions.HasOrthonormalBasis v σ J L)
    {ψ : AddChar (Fv F v) ℂ} {m : ℤ} (hm : SelfDualUnramifiedPlaces.DualExponent v ψ m) :
    ∃ e : (Fin 1 → Fin M → Fv F v ⊗[F] E) ≃L[Fv F v] (Fin M × Fin 2 → Fv F v),
      (∀ X, X 0 ∈ L ↔ ∀ i, e X i ∈ v.adicCompletionIntegers F) ∧
      (∀ X, qR (Fv F v) σ J (X 0) = ∑ i : Fin M,
        (e X (i, 0) ^ 2 + t * e X (i, 0) * e X (i, 1) + n * e X (i, 1) ^ 2)) ∧
      ∀ Y, (∀ i, Valued.v (e Y i) ≤ WithZero.exp m) ↔
        ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X 0 ∈ L → ψ (BR (Fv F v) σ J X Y) = 1 := by
  haveI := GlobalTheory.LocalDensityCompare.modTop (E := E) v
  haveI := GlobalTheory.LocalDensityCompare.topRing (E := E) v
  obtain ⟨c, hc, h1, h2⟩ := exists_dual v hσ hw hD ht hn
  obtain ⟨g, hg, hh⟩ := exists_frame v hL hb
  let e : (Fin 1 → Fin M → Fv F v ⊗[F] E) ≃ₗ[Fv F v] (Fin M × Fin 2 → Fv F v) :=
    { toFun := fun X p => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c p.2 * g (X 0) p.1)
      invFun := fun x _ => g.symm fun i =>
        algebraMap (Fv F v) _ (x (i, 0)) + algebraMap (Fv F v) _ (x (i, 1)) * w
      map_add' := fun X Y => by
        funext p
        simp [mul_add]
      map_smul' := fun a X => by
        funext p
        have : g ((a • X) 0) = a • g (X 0) := (g.restrictScalars (Fv F v)).map_smul a (X 0)
        change Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c p.2 * g ((a • X) 0) p.1) =
          a • Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c p.2 * g (X 0) p.1)
        rw [this, Pi.smul_apply, mul_smul_comm, map_smul]
      left_inv := fun X => by
        funext a
        rw [Subsingleton.elim a 0, LinearEquiv.symm_apply_eq]
        funext i
        exact (h1 _).symm
      right_inv := fun x => by
        funext ⟨i, j⟩
        simp only [LinearEquiv.apply_symm_apply]
        fin_cases j
        · exact (h2 _ _).1
        · exact (h2 _ _).2 }
  have he : ∀ X p, e X p = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c p.2 * g (X 0) p.1) :=
    fun _ _ => rfl
  have hg' : ∀ (X : Fin 1 → Fin M → Fv F v ⊗[F] E) i, g (X 0) i =
      algebraMap (Fv F v) _ (e X (i, 0)) + algebraMap (Fv F v) _ (e X (i, 1)) * w :=
    fun X i => h1 _
  refine ⟨{ e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap },
    fun X => ?_, fun X => ?_, fun Y => ?_⟩
  · rw [hg]
    constructor
    · intro h p
      exact trace_mem v hσ (mul_mem (hc _) (h _))
    · intro h i
      rw [hg']
      exact add_mem ((algebraMap_mem_iff v _).2 (h _))
        (mul_mem ((algebraMap_mem_iff v _).2 (h _)) hw)
  · apply algebraMap_inj (E := E) v
    rw [← hR_self _ hσ hJ, hh, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = algebraMap (Fv F v) _
      (e X (i, 0) ^ 2 + t * e X (i, 0) * e X (i, 1) + n * e X (i, 1) ^ 2)
    rw [hg']
    simp only [map_add, map_mul, map_pow, sigR_algebraMap, ← ht, ← hn]
    ring
  · change (∀ i, Valued.v (e Y i) ≤ WithZero.exp m) ↔ _
    have hB : ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, BR (Fv F v) σ J X Y =
        ∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ (g (X 0) i) * g (Y 0) i) := by
      intro X
      rw [BR, Fin.sum_univ_one, hh, map_sum]
    constructor
    · intro h X hX
      have hX' := fun i => SelfDualLatticeActions.sigR_mem v σ ((hg _).1 hX i)
      have : Valued.v (BR (Fv F v) σ J X Y) ≤ WithZero.exp m := by
        rw [hB]
        refine Valuation.map_sum_le _ fun i _ => ?_
        rw [hg' Y, mul_add, ← mul_assoc, mul_comm _ (algebraMap (Fv F v) _ (e Y (i, 0))),
          mul_comm _ (algebraMap (Fv F v) _ (e Y (i, 1))), mul_assoc, ← Algebra.smul_def,
          ← Algebra.smul_def, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        refine Valuation.map_add_le _ ?_ ?_
        · rw [map_mul]
          exact mul_le_of_le_of_le_one (h _) (trace_mem v hσ (hX' i))
        · rw [map_mul]
          exact mul_le_of_le_of_le_one (h _) (trace_mem v hσ (mul_mem (hX' i) hw))
      simpa using (hm _).2 this 1 (one_mem _)
    · intro h ⟨i, j⟩
      refine (hm _).1 fun s hs => ?_
      have := h (fun _ => g.symm (Pi.single i (algebraMap (Fv F v) _ s * sigR (Fv F v) σ (c j)))) (by
        rw [hg, LinearEquiv.apply_symm_apply]
        intro k
        rw [Pi.single_apply]
        split_ifs
        · exact mul_mem ((algebraMap_mem_iff v _).2 hs) (SelfDualLatticeActions.sigR_mem v σ (hc j))
        · exact zero_mem _)
      rw [hB, LinearEquiv.apply_symm_apply, Finset.sum_eq_single i
        (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), Pi.single_eq_same,
        map_mul (sigR (Fv F v) σ), sigR_algebraMap, sigR_sigR _ hσ, mul_assoc, ← Algebra.smul_def,
        map_smul, smul_eq_mul, mul_comm] at this
      exact this

theorem exists_scaling (hσ : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) {u : Fv F v} (hu : Valued.v u = 1)
    {a : Fv F v ⊗[F] E} (ha : a ∈ SelfDualLatticeActions.OEv E v)
    (hN : a * sigR (Fv F v) σ a = algebraMap (Fv F v) (Fv F v ⊗[F] E) u) :
    ∃ T : (Fin 1 → Fin M → Fv F v ⊗[F] E) ≃+ (Fin 1 → Fin M → Fv F v ⊗[F] E),
      Continuous T ∧ Continuous T.symm ∧ (∀ X, T X 0 ∈ L ↔ X 0 ∈ L) ∧
        ∀ X, qR (Fv F v) σ J (T X 0) = u * qR (Fv F v) σ J (X 0) := by
  haveI := GlobalTheory.LocalDensityCompare.topRing (E := E) v
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  set b := sigR (Fv F v) σ a * algebraMap (Fv F v) (Fv F v ⊗[F] E) u⁻¹ with hb
  have hab : a * b = 1 := by
    rw [hb, ← mul_assoc, hN, ← map_mul, mul_inv_cancel₀ hu0, map_one]
  have hbm : b ∈ SelfDualLatticeActions.OEv E v := mul_mem (SelfDualLatticeActions.sigR_mem v σ ha)
    ((algebraMap_mem_iff v _).2 (show Valued.v u⁻¹ ≤ 1 by rw [map_inv₀, hu, inv_one]))
  refine ⟨{ toFun := fun X => a • X
            invFun := fun X => b • X
            left_inv := fun X => by simp only [smul_smul, mul_comm b, hab, one_smul]
            right_inv := fun X => by simp only [smul_smul, hab, one_smul]
            map_add' := smul_add a }, continuous_const_smul a, continuous_const_smul b,
    fun X => ⟨fun h => ?_, fun h => L.smul_mem ⟨a, ha⟩ h⟩, fun X => ?_⟩
  · have h' : b • a • X 0 ∈ L := L.smul_mem ⟨b, hbm⟩ h
    rwa [smul_smul, mul_comm b, hab, one_smul] at h'
  · apply algebraMap_inj (E := E) v
    rw [map_mul, ← hR_self _ hσ hJ, ← hR_self _ hσ hJ, ← hN]
    change hR (Fv F v) σ J (a • X 0) (a • X 0) = _
    rw [hR_smul_left, hR_smul_right]
    ring

end Coordinates

end GlobalTheory.LatticeDensity
