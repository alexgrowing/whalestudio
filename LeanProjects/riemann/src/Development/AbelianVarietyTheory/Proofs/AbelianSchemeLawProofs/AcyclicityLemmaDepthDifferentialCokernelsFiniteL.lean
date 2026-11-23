import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing

namespace GlobalTheory
namespace FiniteLengthComplex

variable {R : Type} [CommRing R]

noncomputable def extCongrLeft {X X' : ModuleCat.{0} R} (e : X ≅ X') (Y : ModuleCat.{0} R) (n : ℕ) :
    Abelian.Ext.{0} X' Y n ≃ₗ[R] Abelian.Ext.{0} X Y n :=
  LinearEquiv.ofLinearMap ((Ext.mk₀ e.hom).precompOfLinear R Y (zero_add n))
    ((Ext.mk₀ e.inv).precompOfLinear R Y (zero_add n))
    (by ext x; simp) (by ext x; simp)

theorem subsingleton_ext_of_isZero_left {X : ModuleCat.{0} R} (h : IsZero X) (Y : ModuleCat.{0} R)
    (n : ℕ) : Subsingleton (Abelian.Ext.{0} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.mk₀_id_comp x, h.eq_zero_of_src (𝟙 X), Ext.mk₀_zero, Ext.zero_comp]

theorem shortExact_submodule {M : Type} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
      (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ N) N.subtype_injective
    N.mkQ_surjective

theorem nonempty_iso_residue [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] :
    Nonempty (ModuleCat.of R M ≅ ModuleCat.of R (R ⧸ maximalIdeal R)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R M›
  obtain rfl := eq_maximalIdeal hI
  exact ⟨e.toModuleIso⟩

theorem subsingleton_ext_of_isFiniteLength [IsLocalRing R] (Y : ModuleCat.{0} R) (n : ℕ)
    (hk : Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Subsingleton (Abelian.Ext.{0} (ModuleCat.of R M) Y n) := by
  induction hM with
  | of_subsingleton =>
    exact subsingleton_ext_of_isZero_left (ModuleCat.isZero_of_subsingleton _) Y n
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨e⟩ := nonempty_iso_residue (R := R) (M ⧸ N)
    have h3 := (extCongrLeft e Y n).symm.toEquiv.subsingleton
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₂ (shortExact_submodule N) Y x
      (@Subsingleton.elim _ ih _ _)
    rw [@Subsingleton.elim _ h3 y 0]
    exact Ext.comp_zero _ _ _ _ _

theorem length_ext_of_isFiniteLength [IsLocalRing R] (Y : ModuleCat.{0} R) (g : ℕ)
    (hk : ∀ n, n ≠ g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.length R (Abelian.Ext.{0} (ModuleCat.of R M) Y g) = Module.length R M *
      Module.length R (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y g) := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    have := subsingleton_ext_of_isZero_left
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M)) Y g
    rw [Module.length_eq_zero, Module.length_eq_zero (M := M), zero_mul]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨e⟩ := nonempty_iso_residue (R := R) (M ⧸ N)
    have hS := shortExact_submodule N
    rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N), Module.length_eq_one R (M ⧸ N), add_mul, one_mul, ← ih,
      (extCongrLeft e Y g).length_eq, add_comm]
    refine Module.length_eq_add_of_exact
      ((Ext.mk₀ (ModuleCat.ofHom N.mkQ)).precompOfLinear R Y (zero_add g))
      ((Ext.mk₀ (ModuleCat.ofHom N.subtype)).precompOfLinear R Y (zero_add g)) ?_ ?_ ?_
    · cases g with
      | zero =>
        have := hS.epi_g
        exact Ext.precomp_mk₀_injective_of_epi Y (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
          (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).g
      | succ g =>
        rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y x hx (add_comm 1 g)
        rw [@Subsingleton.elim _ (subsingleton_ext_of_isFiniteLength Y g (hk g (by omega)) N hN) y 0]
        exact Ext.comp_zero _ _ _ _ _
    · intro x
      have := hk (g + 1) (by omega)
      have h3 := (extCongrLeft e Y (g + 1)).symm.toEquiv.subsingleton
      exact Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 g) (@Subsingleton.elim _ h3 _ _)
    · intro x
      refine ⟨fun hx => Ext.contravariant_sequence_exact₂ hS Y x hx, ?_⟩
      rintro ⟨y, rfl⟩
      change (Ext.mk₀ _).comp ((Ext.mk₀ _).comp y (zero_add g)) (zero_add g) = 0
      rw [Ext.mk₀_comp_mk₀_assoc, ← ModuleCat.ofHom_comp,
        (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero]
      simp

theorem subsingleton_ext_free (X : ModuleCat.{0} R) (n : ℕ)
    (h : Subsingleton (Abelian.Ext.{0} X (ModuleCat.of R R) n))
    (F : ModuleCat.{0} R) [Module.Free R F] [Module.Finite R F] :
    Subsingleton (Abelian.Ext.{0} X F n) := by
  let b := Module.Free.chooseBasis R F
  have hid : 𝟙 F = ∑ i, (ModuleCat.ofHom (b.coord i) : F ⟶ ModuleCat.of R R) ≫
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b i)) : ModuleCat.of R R ⟶ F) := by
    ext x
    simp [ModuleCat.hom_sum, b.sum_repr x]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, hid, Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Subsingleton.elim (x.comp _ _) 0, Ext.zero_comp]

theorem subsingleton_ext_residue [IsRegularLocalRing R] (g : ℕ) (hg : ringKrullDim R = g)
    (n : ℕ) (hn : n ≠ g) :
    Subsingleton
      (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) n) := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : xs.length = g := by
    rw [hg] at hd
    exact_mod_cast hd
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ xs ?_ hreg n
      (hlen ▸ hlt)
    · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    · rw [smul_eq_mul, Ideal.mul_top]
      exact (maximalIdeal.isMaximal R).ne_top.lt_top
    · intro r hr
      rw [← h]
      exact Ideal.subset_span hr
  · have key := ModuleCat.projectiveDimension_quotient_eq_length.{0} xs hreg
    rw [projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, h, hlen] at key
    have : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ maximalIdeal R)) g :=
      (projectiveDimension_le_iff _ g).mp key.le
    exact HasProjectiveDimensionLT.subsingleton _ (g + 1) n hgt _

section Complex

variable (C : CochainComplex (ModuleCat.{0} R) ℕ)

noncomputable def opcyclesShortComplex (i : ℕ) : ShortComplex (ModuleCat.{0} R) :=
  ShortComplex.mk (C.fromOpcycles i (i + 1)) (C.pOpcycles (i + 1)) (by
    rw [← cancel_epi (C.pOpcycles i)]
    simp)

theorem opcyclesShortComplex_shortExact (i : ℕ) (h : IsZero (C.homology i)) :
    (opcyclesShortComplex C i).ShortExact := by
  have hm : Mono (C.fromOpcycles i (i + 1)) := by
    have hex := ShortComplex.exact_of_f_is_kernel
      (ShortComplex.mk (C.homologyι i) (C.fromOpcycles i (i + 1)) (by simp))
      (C.homologyIsKernel i (i + 1) (by simp))
    exact hex.mono_g (h.eq_zero_of_src _)
  have hex : (opcyclesShortComplex C i).Exact := by
    have h1 := ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk (C.d i (i + 1)) (C.pOpcycles (i + 1)) (by simp))
      (C.opcyclesIsCokernel i (i + 1) (by simp))
    let φ : ShortComplex.mk (C.d i (i + 1)) (C.pOpcycles (i + 1)) (by simp) ⟶
        opcyclesShortComplex C i :=
      { τ₁ := C.pOpcycles i, τ₂ := 𝟙 _, τ₃ := 𝟙 _
        comm₁₂ := by simp [opcyclesShortComplex]
        comm₂₃ := by simp [opcyclesShortComplex] }
    have : Epi φ.τ₁ := inferInstanceAs (Epi (C.pOpcycles i))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (C.X (i + 1))))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (C.opcycles (i + 1))))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp h1
  exact
    { exact := hex
      mono_f := hm
      epi_g := inferInstanceAs (Epi (C.pOpcycles (i + 1))) }

theorem isIso_pOpcycles_zero : IsIso (C.pOpcycles 0) :=
  C.isIso_pOpcycles 0 0 (by simp) (by simp)

theorem acyclicityLemma_depth_differentialCokernels_finiteLength [IsLocalRing R] (g : ℕ)
    (hX : ∀ i n, n < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.X i) n))
    (hH : ∀ i, IsFiniteLength R (C.homology i)) (i : ℕ) :
    (∀ n, n + i < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.opcycles i) n)) ∧
      (i < g → IsZero (C.homology i)) := by
  have key : ∀ i, (∀ n, n + i < g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (C.opcycles i) n)) →
      i < g → IsZero (C.homology i) := by
    intro i h hi
    have h0 : Subsingleton (Abelian.Ext.{0} (C.homology i) (C.opcycles i) 0) :=
      subsingleton_ext_of_isFiniteLength _ 0 (h 0 (by omega)) _ (hH i)
    have h1 : Subsingleton (C.homology i ⟶ C.opcycles i) :=
      Ext.addEquiv₀.subsingleton_congr.mp h0
    exact IsZero.of_mono_eq_zero (C.homologyι i) (Subsingleton.elim _ _)
  induction i with
  | zero =>
    refine (fun h => ⟨h, key 0 h⟩) fun n hn => ?_
    have := isIso_pOpcycles_zero C
    have := hX 0 n (by omega)
    refine subsingleton_of_forall_eq 0 fun x => ?_
    rw [← Ext.comp_mk₀_id x, ← IsIso.inv_hom_id (C.pOpcycles 0), ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero, Subsingleton.elim (x.comp _ _) 0, Ext.zero_comp]
  | succ i ih =>
    refine (fun h => ⟨h, key (i + 1) h⟩) fun n hn => ?_
    have hS := opcyclesShortComplex_shortExact C i (ih.2 (by omega))
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x rfl
      (@Subsingleton.elim _ (ih.1 (n + 1) (by omega)) _ _)
    rw [@Subsingleton.elim _ (hX (i + 1) n (by omega)) y 0]
    exact Ext.zero_comp _ _ _ _ _

theorem length_ext_opcycles (Y : ModuleCat.{0} R) (hP : ∀ i, Projective (C.X i)) (j : ℕ)
    (hH : ∀ i < j + 1, IsZero (C.homology i)) :
    Module.length R (Abelian.Ext.{0} (C.opcycles (j + 1)) Y (j + 1)) =
      Module.length R (Abelian.Ext.{0} (C.opcycles 0) Y 0 ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R Y (zero_add 0))) := by
  have step : ∀ i, IsZero (C.homology i) → ∀ n,
      Module.length R (Abelian.Ext.{0} (C.opcycles (i + 1)) Y (n + 1)) =
      Module.length R (Abelian.Ext.{0} (C.opcycles i) Y n ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles i (i + 1))).precompOfLinear R Y (zero_add n))) := by
    intro i hi n
    have hS := opcyclesShortComplex_shortExact C i hi
    let δ : Abelian.Ext.{0} (C.opcycles i) Y n →ₗ[R]
        Abelian.Ext.{0} (C.opcycles (i + 1)) Y (n + 1) :=
      hS.extClass.precompOfLinear R Y (add_comm 1 n)
    have hsurj : Function.Surjective δ := fun x => by
      have : Projective (opcyclesShortComplex C i).X₂ := hP (i + 1)
      exact Ext.contravariant_sequence_exact₃ hS Y x (Ext.eq_zero_of_projective _) (add_comm 1 n)
    have hker : LinearMap.ker δ = LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles i (i + 1))).precompOfLinear R Y (zero_add n)) := by
      ext x
      refine ⟨fun hx => Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 n) hx, ?_⟩
      rintro ⟨y, rfl⟩
      exact hS.extClass_comp_assoc y (h := add_comm 1 n)
    rw [← hker]
    exact (δ.quotKerEquivOfSurjective hsurj).length_eq.symm
  induction j with
  | zero => exact step 0 (hH 0 (by omega)) 0
  | succ j ih =>
    rw [step (j + 1) (hH _ (by omega)) (j + 1), ← ih fun i hi => hH i (by omega)]
    refine (Submodule.quotEquivOfEqBot _ ?_).length_eq
    rw [LinearMap.range_eq_bot]
    ext x
    have := hP (j + 1 + 1)
    rw [Ext.eq_zero_of_projective x]
    simp

theorem length_ext_zero_quot :
    Module.length R (Abelian.Ext.{0} (C.opcycles 0) (ModuleCat.of R R) 0 ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R (ModuleCat.of R R) (zero_add 0))) =
      Module.length R (Module.Dual R (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) := by
  have := isIso_pOpcycles_zero C
  let e (X : ModuleCat.{0} R) : Abelian.Ext.{0} X (ModuleCat.of R R) 0 ≃ₗ[R] Module.Dual R X :=
    (Ext.linearEquiv₀ (R := R)).trans ModuleCat.homLinearEquiv
  have he (X : ModuleCat.{0} R) (f : X ⟶ ModuleCat.of R R) : e X (Ext.mk₀ f) = f.hom := by
    rw [← LinearEquiv.eq_symm_apply]
    rfl
  let φ := (extCongrLeft (asIso (C.pOpcycles 0)) (ModuleCat.of R R) 0).trans (e (C.X 0))
  have hφ (f : C.X 1 ⟶ ModuleCat.of R R) :
      φ ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R (ModuleCat.of R R) (zero_add 0)
        (Ext.mk₀ f)) = (C.d 0 1).hom.dualMap f.hom := by
    change e _ ((Ext.mk₀ (C.pOpcycles 0)).comp
      ((Ext.mk₀ _).comp (Ext.mk₀ f) (zero_add 0)) (zero_add 0)) = _
    rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, he, HomologicalComplex.p_fromOpcycles_assoc]
    rfl
  refine (Submodule.Quotient.equiv _ _ φ ?_).length_eq
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    exact ⟨f.hom, (hφ f).symm⟩
  · rintro _ ⟨f, rfl⟩
    exact ⟨_, ⟨Ext.mk₀ (ModuleCat.ofHom f), rfl⟩, hφ (ModuleCat.ofHom f)⟩

end Complex

end FiniteLengthComplex

open FiniteLengthComplex in

theorem homology_of_free_complex_of_isFiniteLength :
    ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g →
      ∀ C : CochainComplex (ModuleCat.{0} O) ℕ,
        (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, g < i → IsZero (C.X i)) →
        (∀ i, IsFiniteLength O (C.homology i)) →
        Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O]
          IsLocalRing.ResidueField O) →
        (∀ i, i ≠ g → IsZero (C.homology i)) ∧ Module.length O (C.homology g) = 1 := by
  intro O _ _ g hg C hF hZ hH ⟨e⟩
  have hk := subsingleton_ext_residue g hg
  have hlt : ∀ i < g, IsZero (C.homology i) := fun i hi =>
    (acyclicityLemma_depth_differentialCokernels_finiteLength C g (fun j n hn => by
      have := (hF j).1
      have := (hF j).2
      exact subsingleton_ext_free _ n (hk n hn.ne) _) hH i).2 hi
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hi with h | h
    · exact hlt i h
    · exact IsZero.of_mono (C.homologyι i) (IsZero.of_epi (C.pOpcycles i) (hZ i h))
  have hres : Module.length O (IsLocalRing.ResidueField O) = 1 := by
    have : IsSimpleModule O (IsLocalRing.ResidueField O) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal O, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have h0 := (length_ext_zero_quot C).trans (e.length_eq.trans hres)
  have h1 : Module.length O (Abelian.Ext.{0} (C.opcycles g) (ModuleCat.of O O) g) = 1 := by
    cases g with
    | zero =>
      rw [← h0]
      refine (Submodule.quotEquivOfEqBot _ ?_).length_eq.symm
      rw [LinearMap.range_eq_bot]
      ext x
      have := subsingleton_ext_of_isZero_left (hZ 1 one_pos) (ModuleCat.of O O) 0
      rw [Subsingleton.elim x 0]
      simp
    | succ j =>
      rw [length_ext_opcycles C _ (fun i => by
        have := (hF i).1
        infer_instance) j hlt, h0]
  have := C.isIso_homologyι g (g + 1) (by simp) ((hZ _ (by omega)).eq_zero_of_tgt _)
  rw [(extCongrLeft (asIso (C.homologyι g)) _ g).length_eq] at h1
  have h2 : 1 = Module.length O (C.homology g) * Module.length O (Abelian.Ext.{0}
      (ModuleCat.of O (O ⧸ maximalIdeal O)) (ModuleCat.of O O) g) :=
    h1.symm.trans (length_ext_of_isFiniteLength _ g hk _ (hH g))
  generalize Module.length O (C.homology g) = a at h2 ⊢
  generalize Module.length O (Abelian.Ext.{0} (ModuleCat.of O (O ⧸ maximalIdeal O))
    (ModuleCat.of O O) g) = b at h2
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h2
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h2
  refine le_antisymm ?_ (Order.one_le_iff_ne_zero.mpr ha)
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * b := by gcongr; exact Order.one_le_iff_ne_zero.mpr hb
    _ = 1 := h2.symm

end GlobalTheory
