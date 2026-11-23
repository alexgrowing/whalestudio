import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct Matrix RestrictedProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem eventually_algebraMap_mem_integers (a : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) a).2

theorem eventually_one_tmul_mem_intLoc (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (1 : Fv F v) ⊗ₜ[F] e ∈ intLoc F E v := by
  have : Algebra.IsAlgebraic ℤ E := IsFractionRing.comap_isAlgebraic_iff.2 (inferInstance : Algebra.IsAlgebraic ℚ E)
  obtain ⟨d, hd, hi⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) e).exists_integral_multiple
  have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
  filter_upwards [eventually_algebraMap_mem_integers (d : F)⁻¹] with v hv
  have h := tmul_mem_intLoc hv (⟨d • e, hi⟩ : 𝓞 E)
  convert h using 1
  change _ = _ ⊗ₜ[F] (d • e)
  rw [← Int.cast_smul_eq_zsmul F, ← TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hd', map_one]

theorem eventually_map_evalV_mem_intLoc (z : Af F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | add y z hy hz => filter_upwards [hy, hz] with v h h' using by rw [map_add]; exact add_mem h h'
  | tmul a e =>
    filter_upwards [a.2, eventually_one_tmul_mem_intLoc (F := F) e] with v h h'
    have := mul_mem (tmul_mem_intLoc (a := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a) h (1 : 𝓞 E)) h'
    simpa using this

theorem exists_map_evalV_eq (z : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v ⊗[F] E)
    (hz : ∀ᶠ v in cofinite, z v ∈ intLoc F E v) :
    ∃ Z : Af F ⊗[F] E, ∀ v, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) Z = z v := by
  let b := Module.finBasis F E
  let c := RingOfIntegers.basis E
  have h1 : ∀ k, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y ∈ intLoc F E v,
      (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F := fun k => by
    filter_upwards [eventually_all.2 fun j => eventually_algebraMap_mem_integers (b.repr (c j : E) k)] with v hv y hy
    refine intLoc_induction (p := fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) (fun a ha x => ?_) (by simp) (fun y z h h' => by simpa using add_mem h h')
      (fun y h => by simpa using h) hy
    have e : b.repr (x : E) k = ∑ j, c.repr x j • b.repr (c j : E) k := by
      have e' : (x : E) = ∑ j, c.repr x j • (c j : E) := by
        conv_lhs => rw [← c.sum_repr x]
        simp
      simp only [e', map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, e,
      map_sum, map_zsmul]
    exact mul_mem ha (sum_mem fun j _ => zsmul_mem (hv j) _)
  let A : Fin (Module.finrank F E) → Af F := fun k =>
    ⟨fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (z v) k, by
      filter_upwards [h1 k, hz] with v h h' using h _ h'⟩
  refine ⟨(Algebra.TensorProduct.basis (Af F) b).equivFun.symm A, fun v => ?_⟩
  apply (Algebra.TensorProduct.basis (Fv F v) b).repr.injective
  ext k
  rw [GlobalTheory.LatticeLocalGlobal.repr_map, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem eventually_one_tmul_mem_latLoc {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (fun i => (1 : Fv F v) ⊗ₜ[F] x i) ∈ latLoc F L v := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Eventually.of_forall fun v => tmul_mem_latLoc (one_mem _) hx
  | zero => exact Eventually.of_forall fun v => tmul_mem_latLoc (one_mem _) L.zero_mem
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with v h h'
    convert add_mem h h' using 1
    funext i
    exact TensorProduct.tmul_add _ _ _
  | smul c x _ hx =>
    filter_upwards [hx, eventually_one_tmul_mem_intLoc (F := F) c] with v h h'
    convert (latLoc F L v).smul_mem ⟨_, h'⟩ h using 1
    funext i
    change _ = (1 : Fv F v) ⊗ₜ[F] c * (1 : Fv F v) ⊗ₜ[F] x i
    simp

theorem eventually_latLoc_le {L L' : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc F L v ≤ latLoc F L' v := by
  obtain ⟨s, rfl⟩ := hL
  filter_upwards [(eventually_all_finset s).2 fun x _ => eventually_one_tmul_mem_latLoc (F := F) hL' x] with v hv y hy
  have h1 : ∀ x ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)), (fun i => (1 : Fv F v) ⊗ₜ[F] x i) ∈ latLoc F L' v := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hv x hx
    | zero => exact tmul_mem_latLoc (one_mem _) L'.zero_mem
    | add x y _ _ h h' =>
      convert add_mem h h' using 1
      funext i
      exact TensorProduct.tmul_add _ _ _
    | smul c x _ h =>
      convert (latLoc F L' v).smul_mem ⟨_, tmul_mem_intLoc (one_mem _) c⟩ h using 1
      funext i
      change (1 : Fv F v) ⊗ₜ[F] ((c : E) * x i) = (1 : Fv F v) ⊗ₜ[F] (c : E) * (1 : Fv F v) ⊗ₜ[F] x i
      simp
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  convert (latLoc F L' v).smul_mem ⟨_, tmul_mem_intLoc ha 1⟩ (h1 x hx) using 1
  funext i
  change _ = a ⊗ₜ[F] ((1 : 𝓞 E) : E) * (1 : Fv F v) ⊗ₜ[F] x i
  simp

variable (F) in

theorem eventually_latLoc_eq (L L' : Submodule (𝓞 E) (Fin n → E)) [hL : Submodule.IsLattice E L]
    [hL' : Submodule.IsLattice E L'] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc F L v = latLoc F L' v := by
  filter_upwards [eventually_latLoc_le (F := F) hL.fg hL'.span_eq_top,
    eventually_latLoc_le (F := F) hL'.fg hL.span_eq_top] with v h h' using le_antisymm h h'

omit [NumberField E] in

theorem isLattice_stdLattice : Submodule.IsLattice E (stdLattice E n) := by
  refine ⟨Submodule.fg_pi fun _ => ?_, eq_top_iff.2 fun y _ => ?_⟩
  · rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · rw [← Finset.univ_sum_single y]
    refine sum_mem fun i _ => ?_
    have h1 : (Pi.single i 1 : Fin n → E) ∈ stdLattice E n := fun j _ => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
      by_cases e : j = i
      · subst e; simp
      · simp [e]⟩
    convert Submodule.smul_mem _ (y i) (Submodule.subset_span h1) using 1
    rw [← Pi.single_smul, smul_eq_mul, mul_one]

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

omit [NumberField E] in
variable {σ J} in

theorem mem_stabLoc_stdLattice_iff {v : HeightOneSpectrum (𝓞 F)} {k : GLoc σ J v} :
    k ∈ stabLoc σ J (stdLattice E n) v ↔ (∀ i j, (matHom _ σ J k).1 i j ∈ intLoc F E v) ∧
      ∀ i j, (matHom _ σ J k⁻¹).1 i j ∈ intLoc F E v := by
  have h1 : ∀ k ∈ stabLoc σ J (stdLattice E n) v, ∀ i j, (matHom _ σ J k).1 i j ∈ intLoc F E v := fun k hk i j => by
    have := mem_latLoc_stdLattice.1 ((mem_stabLoc.1 hk (Pi.single j 1)).1 (mem_latLoc_stdLattice.2 fun l => by
      by_cases e : l = j
      · subst e; simp
      · simp [e])) i
    simpa using this
  have h2 : ∀ M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), (∀ i j, M i j ∈ intLoc F E v) →
      ∀ y ∈ latLoc F (stdLattice E n) v, M *ᵥ y ∈ latLoc F (stdLattice E n) v := fun M hM y hy =>
    mem_latLoc_stdLattice.2 fun i => show ∑ j, M i j * y j ∈ _ from
      sum_mem fun j _ => mul_mem (hM i j) (mem_latLoc_stdLattice.1 hy j)
  refine ⟨fun hk => ⟨h1 k hk, h1 _ (inv_mem hk)⟩, fun h => mem_stabLoc.2 fun y => ⟨h2 _ h.1 y, fun hy => ?_⟩⟩
  have := h2 _ h.2 _ hy
  rwa [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec] at this

theorem eventually_stabLoc_eq (L L' : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
    [Submodule.IsLattice E L'] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, stabLoc σ J L v = stabLoc σ J L' v := by
  filter_upwards [eventually_latLoc_eq F L L'] with v h
  rw [stabLoc, stabLoc, h]

variable (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]

theorem eventually_projFinLoc_mem_stabLoc (g : GFin σ J) :
    ∀ᶠ v in cofinite, projFinLoc σ J v g ∈ stabLoc σ J L v := by
  have := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_stabLoc_eq σ J L (stdLattice E n),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_map_evalV_mem_intLoc ((matHom _ σ J g).1 i j),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_map_evalV_mem_intLoc ((matHom _ σ J g⁻¹).1 i j)]
    with v h h1 h2
  rw [h, mem_stabLoc_stdLattice_iff, ← map_inv]
  exact ⟨h1, h2⟩

theorem eventually_proj_mem_stabLoc (g : GAd σ J) : ∀ᶠ v in cofinite, proj σ J v g ∈ stabLoc σ J L v := by
  simpa using eventually_projFinLoc_mem_stabLoc σ J L (projFin σ J g)

theorem existsUnique_projFinLoc_eq (x : ∀ v, GLoc σ J v) (hx : ∀ᶠ v in cofinite, x v ∈ stabLoc σ J L v) :
    ∃! g : GFin σ J, ∀ v, projFinLoc σ J v g = x v := by
  refine existsUnique_of_exists_of_unique ?_ fun g h hg hh => GFin_ext σ J fun v => (hg v).trans (hh v).symm
  have := isLattice_stdLattice (E := E) (n := n)
  have h0 : ∀ᶠ v in cofinite, (∀ i j, (matHom _ σ J (x v)).1 i j ∈ intLoc F E v) ∧
      ∀ i j, (matHom _ σ J (x v)⁻¹).1 i j ∈ intLoc F E v := by
    filter_upwards [eventually_stabLoc_eq σ J L (stdLattice E n), hx] with v h h'
    rwa [h, mem_stabLoc_stdLattice_iff] at h'
  choose A hA using fun i j => exists_map_evalV_eq (fun v => (matHom _ σ J (x v)).1 i j) (h0.mono fun v h => h.1 i j)
  choose B hB using fun i j =>
    exists_map_evalV_eq (fun v => (matHom _ σ J (x v)⁻¹).1 i j) (h0.mono fun v h => h.2 i j)
  let φ : ∀ v, Af F ⊗[F] E →+* Fv F v ⊗[F] E := fun v =>
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom
  have hext : ∀ M N : Matrix (Fin n) (Fin n) (Af F ⊗[F] E), (∀ v, M.map (φ v) = N.map (φ v)) → M = N :=
    fun M N h => Matrix.ext fun i j => GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => congrFun₂ (h v) i j
  have hA' : ∀ v, (Matrix.of A).map (φ v) = (matHom _ σ J (x v)).1 := fun v => Matrix.ext fun i j => hA i j v
  have hB' : ∀ v, (Matrix.of B).map (φ v) = (matHom _ σ J (x v)⁻¹).1 := fun v => Matrix.ext fun i j => hB i j v
  have hσ : ∀ v z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (φ v z) = φ v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z) := fun v z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hJ : ∀ v, (JR (Af F) J).map (φ v) = JR (Fv F v) J := fun v => by ext r s; simp [φ, JR, inclR]
  let u : GL (Fin n) (Af F ⊗[F] E) := ⟨Matrix.of A, Matrix.of B,
    hext _ _ fun v => by
      rw [Matrix.map_mul, hA', hB', map_inv, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)],
    hext _ _ fun v => by
      rw [Matrix.map_mul, hA', hB', map_inv, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hu : u ∈ HR (Af F) σ J := hext _ _ fun v => by
    change (cT _ (Matrix.of A) * _ * Matrix.of A).map _ = _
    rw [Matrix.map_mul, Matrix.map_mul, ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ _ _ (hσ v), hA', hJ]
    exact (x v).2
  exact ⟨⟨u, hu⟩, fun v => matHom_injective _ σ J (Units.ext (hA' v))⟩

def restrictedEquiv : GFin σ J ≃* Πʳ v, [GLoc σ J v, stabLoc σ J L v] :=
  MulEquiv.ofBijective (F := GFin σ J →* Πʳ v, [GLoc σ J v, stabLoc σ J L v])
    { toFun := fun g => ⟨fun v => projFinLoc σ J v g, eventually_projFinLoc_mem_stabLoc σ J L g⟩
      map_one' := Subtype.ext (funext fun v => map_one (projFinLoc σ J v))
      map_mul' := fun g h => Subtype.ext (funext fun v => map_mul (projFinLoc σ J v) g h) }
    ⟨fun _ _ e => GFin_ext σ J fun v => congrFun (congrArg Subtype.val e) v, fun x =>
      let ⟨g, hg, _⟩ := existsUnique_projFinLoc_eq σ J L x.1 x.2
      ⟨g, Subtype.ext (funext hg)⟩⟩

@[simp] theorem restrictedEquiv_apply (g : GFin σ J) (v : HeightOneSpectrum (𝓞 F)) :
    restrictedEquiv σ J L g v = projFinLoc σ J v g := rfl

end GlobalTheory.AdelicU

end
