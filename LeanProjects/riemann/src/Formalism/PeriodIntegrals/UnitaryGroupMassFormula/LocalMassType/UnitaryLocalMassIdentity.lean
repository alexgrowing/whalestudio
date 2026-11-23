import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.SelfDualMeasureSFinite

noncomputable section

namespace PI.LocMassTypU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
  Topology
open scoped TensorProduct
open PI.LocMassTypW

section Oev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem sc_mul_eq_smul (x : Fv F v) (y : Fv F v ⊗[F] E) : sc (E := E) v x * y = x • y := by
  rw [Algebra.smul_def]
  rfl

theorem sc_mul_sc (x y : Fv F v) : sc (E := E) v x * sc (E := E) v y = sc (E := E) v (x * y) := by
  simp [sc, Algebra.TensorProduct.tmul_mul_tmul]

theorem oev_smul {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : c • x ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨c, hc⟩ : v.adicCompletionIntegers F) hx

theorem oev_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := Submodule.add_mem _ hx hy

theorem oev_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v :=
  Submodule.neg_mem _ hx

theorem oev_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := Submodule.zero_mem _

def Osub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  add_mem' := oev_add v
  zero_mem' := oev_zero v
  neg_mem' := oev_neg v

theorem inclR_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, trivial, rfl⟩

attribute [local instance] LocMassOrdSF.finDim_FE

theorem exists_intBasis : ∃ b : Module.Basis (Fin (Module.finrank F E)) F E,
    ∀ i, IsIntegral ℤ (b i) := by
  classical
  let b0 := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b0)
  have hu : ∀ i : Fin (Module.finrank F E), IsUnit ((y : F)) := fun _ =>
    isUnit_iff_ne_zero.2 (by exact_mod_cast hy0)
  refine ⟨b0.isUnitSMul hu, fun i => ?_⟩
  have h := hy (b0 i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [Module.Basis.isUnitSMul_apply]
  have e : ((y : F)) • b0 i = y • b0 i := by
    rw [← Int.cast_smul_eq_zsmul F y (b0 i)]
  rw [e]
  exact h

def ib : Module.Basis (Fin (Module.finrank F E)) F E := (exists_intBasis (F := F) (E := E)).choose

theorem ib_int (i : Fin (Module.finrank F E)) : IsIntegral ℤ (ib (F := F) (E := E) i) :=
  (exists_intBasis (F := F) (E := E)).choose_spec i

def bas : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (ib (F := F) (E := E))

theorem bas_apply (i : Fin (Module.finrank F E)) :
    bas (E := E) v i = inclR (F := F) (Fv F v) (ib (F := F) (E := E) i) := by
  simp [bas, Algebra.TensorProduct.basis_apply, inclR]

theorem bas_mem (i : Fin (Module.finrank F E)) : bas (E := E) v i ∈ OEv (E := E) v := by
  rw [bas_apply]
  exact inclR_mem v ⟨_, ib_int i⟩

theorem oev_mem_nhds : OEv (E := E) v ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
  have := LocMassOrdSF.isModTop_tens (F := F) (E := E) (Fv F v)
  set e := (bas (E := E) v).equivFun
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have ho : IsOpen (e ⁻¹' (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _).preimage hc
  refine Filter.mem_of_superset (ho.mem_nhds (by simp [zero_mem])) ?_
  intro x hx
  rw [← (bas (E := E) v).sum_equivFun x]
  exact Submodule.sum_mem _ fun i _ => oev_smul v (hx i trivial) (bas_mem v i)

theorem isOpen_oev : IsOpen (OEv (E := E) v) := by
  have := LocMassOrdSF.isTopRing_tens (F := F) (E := E) (Fv F v)
  exact AddSubgroup.isOpen_of_mem_nhds (Osub (E := E) v) (oev_mem_nhds v)

end Oev

section Box

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def boxS {r : ℕ} (c : UIdx r → Fv F v) : Set (UIdx r → Fv F v ⊗[F] E) :=
  {x | ∀ p, sc (E := E) v (c p) * x p ∈ OEv (E := E) v}

def cU (r : ℕ) (p : UIdx r) : Fv F v := (alp v r p.1.1)⁻¹ * alp v r p.1.2

def cG (g r : ℕ) (p : UIdx r) : Fv F v := (alp v r p.1.1)⁻¹ * alp v r p.1.2 * (g : Fv F v)⁻¹

theorem uo_eq (r : ℕ) : UO (E := E) v r = boxS (E := E) v (cU v r) := rfl

theorem uog_eq (g r : ℕ) : UOg (E := E) v g r = boxS (E := E) v (cG v g r) := rfl

variable {v}

theorem boxS_zero {r : ℕ} (c : UIdx r → Fv F v) : (0 : UIdx r → Fv F v ⊗[F] E) ∈ boxS v c := by
  intro p
  simpa using oev_zero (E := E) v

theorem boxS_add {r : ℕ} {c : UIdx r → Fv F v} {x y : UIdx r → Fv F v ⊗[F] E}
    (hx : x ∈ boxS v c) (hy : y ∈ boxS v c) : x + y ∈ boxS v c := by
  intro p
  simpa [mul_add] using oev_add v (hx p) (hy p)

theorem boxS_neg {r : ℕ} {c : UIdx r → Fv F v} {x : UIdx r → Fv F v ⊗[F] E}
    (hx : x ∈ boxS v c) : -x ∈ boxS v c := by
  intro p
  simpa [mul_neg] using oev_neg v (hx p)

theorem isOpen_boxS {r : ℕ} (c : UIdx r → Fv F v) : IsOpen (boxS (E := E) v c) := by
  have := LocMassOrdSF.isTopRing_tens (F := F) (E := E) (Fv F v)
  have e : boxS (E := E) v c =
      ⋂ p, (fun x : UIdx r → Fv F v ⊗[F] E => sc (E := E) v (c p) * x p) ⁻¹' OEv (E := E) v := by
    ext x
    simp [boxS]
  rw [e]
  exact isOpen_iInter_of_finite fun p =>
    (isOpen_oev v).preimage (continuous_const.mul (continuous_apply p))

theorem natCast_ne_zero {g : ℕ} (hg : g.Prime) : (g : Fv F v) ≠ 0 := by
  have e : (g : Fv F v) = algebraMap F (Fv F v) (g : F) := (map_natCast _ g).symm
  rw [e]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hg.ne_zero)

theorem uog_subset {g : ℕ} (hg : g.Prime) (r : ℕ) : UOg (E := E) v g r ⊆ UO v r := by
  intro x hx p
  have h := hx p
  have e : sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2) * x p =
      (g : Fv F v) • (sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2 * (g : Fv F v)⁻¹) * x p) := by
    rw [← sc_mul_eq_smul, ← mul_assoc, sc_mul_sc]
    congr 2
    field_simp [natCast_ne_zero (F := F) (v := v) hg]
  rw [e]
  exact oev_smul v (natCast_mem _ g) h

end Box

theorem unitary_local_mass_identity : StepU := by
  intro F E _ _ _ _ _ σ n J ψ v r g hStd hg _
  have := LocMassOrdSF.finDim_FE (F := F) (E := E)
  have := LocMassOrdSF.secondCountable_Fv v
  have := LocMassOrdSF.sc_tens (F := F) (E := E) (Fv F v)
  have := LocMassOrdSF.isTopRing_tens (F := F) (E := E) (Fv F v)
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hSF : SFinite (sdE (E := E) ψ v (UIdx r)) := LocMassOrdSF.self_dual_measure_sFinite σ J ψ v hStd r
  have hInv : (sdE (E := E) ψ v (UIdx r)).IsAddLeftInvariant := by
    unfold sdE
    split_ifs with h
    · have := h.choose_spec.1
      infer_instance
    · exact ⟨fun _ => Measure.map_zero _⟩
  set μ := sdE (E := E) ψ v (UIdx r) with hμ
  have hmp : MeasurePreserving (MeasurableEquiv.shearAddRight (UIdx r → Fv F v ⊗[F] E))
      (μ.prod μ) (μ.prod μ) := measurePreserving_prod_add μ μ
  have hpre : (MeasurableEquiv.shearAddRight (UIdx r → Fv F v ⊗[F] E)) ⁻¹' deepCongruenceVolume v g r =
      UO v r ×ˢ UOg (E := E) v g r := by
    ext ⟨x, y⟩
    show (x, x + y) ∈ deepCongruenceVolume v g r ↔ x ∈ UO v r ∧ y ∈ UOg (E := E) v g r
    constructor
    · rintro ⟨hx, -, hd⟩
      refine ⟨hx, ?_⟩
      have hd' : x - (x + y) ∈ boxS (E := E) v (cG v g r) := hd
      have := boxS_neg hd'
      rw [uog_eq]
      simpa using this
    · rintro ⟨hx, hy⟩
      have hy' : y ∈ UO v r := uog_subset hg r hy
      rw [uo_eq] at hx hy'
      rw [uog_eq] at hy
      refine ⟨hx, boxS_add hx hy', ?_⟩
      have h1 := boxS_neg hy
      have e : x - (x + y) = -y := by abel
      show x - (x + y) ∈ boxS (E := E) v (cG v g r)
      rw [e]
      exact h1
  unfold volU
  rw [← hmp.measure_preimage_equiv, hpre, Measure.prod_prod, ENNReal.toReal_mul]

theorem positivity_of_local_mass : StepPos := by
  intro F E _ _ _ _ _ σ n J ψ v r g _ hg _ h
  have := LocMassOrdSF.finDim_FE (F := F) (E := E)
  have := LocMassOrdSF.isTopRing_tens (F := F) (E := E) (Fv F v)
  have hsub := uog_subset (E := E) (v := v) hg r
  have hop : IsOpen (UOg (E := E) v g r) := by
    rw [uog_eq]
    exact isOpen_boxS _
  have hne : (UOg (E := E) v g r).Nonempty := ⟨0, by rw [uog_eq]; exact boxS_zero _⟩
  revert h
  unfold sdE
  split_ifs with hex
  · intro h
    have := hex.choose_spec.1
    have hpos := hop.measure_pos hex.choose hne
    have hfin : hex.choose (UOg (E := E) v g r) < ⊤ :=
      lt_of_le_of_lt (measure_mono hsub) (lt_top_iff_ne_top.2 (ENNReal.toReal_ne_zero.1 h).2)
    exact ENNReal.toReal_ne_zero.2 ⟨hpos.ne', hfin.ne⟩
  · intro h
    simp at h

end PI.LocMassTypU
