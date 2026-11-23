import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot

noncomputable section

namespace GlobalTheory.NL.Model

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.NL.Model.conv_finite (e : PowerSeries L) {u : ℤ → M} {m : ℤ}
    (hm : ∀ k < m, u k = 0) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j e • u (k - (j : ℤ))).Finite := by
  refine (Set.finite_Iic (k - m).toNat).subset fun j hj => ?_
  simp only [Function.mem_support] at hj
  simp only [Set.mem_Iic]
  by_contra hlt
  push_neg at hlt
  exact hj (by rw [hm _ (by omega), smul_zero])

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.NL.Model.conv_one (u : ℤ → M) :
    _root_.GlobalTheory.NL.conv (1 : PowerSeries L) u = u := by
  funext k
  rw [_root_.GlobalTheory.NL.conv, finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem conv_X (u : ℤ → M) (k : ℤ) : conv (PowerSeries.X : PowerSeries L) u k = u (k - 1) := by
  unfold conv
  rw [finsum_eq_single _ 1]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_X, hj]

theorem conv_single (e : PowerSeries L) (a : ℤ) (d : M) (k : ℤ) :
    conv e (Pi.single a d : ℤ → M) k =
      if a ≤ k then PowerSeries.coeff (k - a).toNat e • d else 0 := by
  unfold conv
  split_ifs with h
  · rw [finsum_eq_single _ (k - a).toNat]
    · have : k - ((k - a).toNat : ℤ) = a := by omega
      rw [this, Pi.single_eq_same]
    · intro j hj
      have : k - (j : ℤ) ≠ a := by omega
      rw [Pi.single_eq_of_ne this, smul_zero]
  · apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have : k - (j : ℤ) ≠ a := by omega
    rw [Pi.single_eq_of_ne this, smul_zero]

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.NL.Model.mem_latSpan {ι : Type} (ex : ι → ℤ → M) (x : ι) :
    ex x ∈ _root_.GlobalTheory.NL.latSpan (LL := L) ex :=
  Submodule.subset_span ⟨1, x, (_root_.GlobalTheory.NL.Model.conv_one _).symm⟩

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
private theorem conv_mem_and_vanish_below (e : PowerSeries L) (D : Submodule L M)
    {u : ℤ → M} (hu : ∀ k, u k ∈ D) {m : ℤ} (hm : ∀ k < m, u k = 0) :
    (∀ k, _root_.GlobalTheory.NL.conv e u k ∈ D) ∧
      ∀ k < m, _root_.GlobalTheory.NL.conv e u k = 0 := by
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · rw [_root_.GlobalTheory.NL.conv,
      finsum_eq_sum _ (_root_.GlobalTheory.NL.Model.conv_finite e hm k)]
    exact Submodule.sum_mem _ fun j _ => D.smul_mem _ (hu _)
  · rw [_root_.GlobalTheory.NL.conv]
    refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
    rw [hm _ (by omega), smul_zero]

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in

theorem _root_.GlobalTheory.NL.Model.latSpan_coeff {ι : Type} (ex : ι → ℤ → M)
    (D : Submodule L M) (hD : ∀ x k, ex x k ∈ D) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, ex x k = 0)
    (f : ℤ → M) (hf : f ∈ _root_.GlobalTheory.NL.latSpan (LL := L) ex) :
    (∀ k, f k ∈ D) ∧ ∃ m : ℤ, ∀ k < m, f k = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨e, x, rfl⟩ := hg
    obtain ⟨m, hm⟩ := hs x
    obtain ⟨h1, h2⟩ := conv_mem_and_vanish_below e D (hD x) hm
    exact ⟨h1, m, h2⟩
  | zero => exact ⟨fun _ => D.zero_mem, 0, fun _ _ => rfl⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨h1, m, hm⟩ := hg
    obtain ⟨h1', m', hm'⟩ := hg'
    refine ⟨fun k => D.add_mem (h1 k) (h1' k), min m m', fun k hk => ?_⟩
    simp [hm k (lt_of_lt_of_le hk (min_le_left _ _)), hm' k (lt_of_lt_of_le hk (min_le_right _ _))]
  | smul c g _ hg =>
    obtain ⟨h1, m, hm⟩ := hg
    exact ⟨fun k => D.smul_mem c (h1 k), m, fun k hk => by simp [hm k hk]⟩

theorem mem_latSpan_single (a : ℤ) (f : ℤ → L) :
    f ∈ latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L)) ↔ ∀ k < a, f k = 0 := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨e, x, rfl⟩ := hf
      intro k hk
      rw [conv_single, if_neg (by omega)]
    | zero => exact fun _ _ => rfl
    | add f g _ _ hf hg => intro k hk; simp [hf k hk, hg k hk]
    | smul c f _ hf => intro k hk; simp [hf k hk]
  · intro hf
    refine Submodule.subset_span ⟨PowerSeries.mk fun j => f (a + j), (), ?_⟩
    funext k
    rw [conv_single]
    split_ifs with h
    · have : a + ((k - a).toNat : ℤ) = k := by omega
      rw [PowerSeries.coeff_mk, this, smul_eq_mul, mul_one]
    · exact hf k (by omega)

theorem Std.full {D : Submodule L M} {Λ : Submodule L (ℤ → M)} (h : Std D Λ) : Full D Λ :=
  ⟨0, fun f h1 h2 => (h f).2 ⟨h1, by simpa using h2⟩⟩

theorem Std.graded {D : Submodule L M} {Λ : Submodule L (ℤ → M)} (h : Std D Λ) : Graded Λ := by
  intro f
  constructor
  · intro hf
    obtain ⟨h1, h2⟩ := (h f).1 hf
    refine ⟨⟨0, h2⟩, fun k => (h _).2 ⟨fun j => ?_, fun j hj => ?_⟩⟩
    · by_cases hjk : j = k
      · subst hjk; simpa using h1 j
      · simp [Pi.single_eq_of_ne hjk]
    · by_cases hjk : j = k
      · subst hjk; simpa using h2 j hj
      · simp [Pi.single_eq_of_ne hjk]
  · rintro ⟨-, hf⟩
    refine (h f).2 ⟨fun k => ?_, fun k hk => ?_⟩
    · simpa using ((h _).1 (hf k)).1 k
    · simpa using ((h _).1 (hf k)).2 k hk

theorem line_tests (a : ℤ) :
    Full (⊤ : Submodule L L) (latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L))) ∧
    Graded (latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L))) ∧
    (Std (⊤ : Submodule L L) (latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L))) ↔ a = 0) := by
  refine ⟨⟨a.toNat, fun f _ hf => (mem_latSpan_single a f).2 fun k hk => hf k (by omega)⟩, ?_, ?_⟩
  · intro f
    simp only [mem_latSpan_single]
    constructor
    · intro hf
      refine ⟨⟨a, hf⟩, fun k j hj => ?_⟩
      by_cases hjk : j = k
      · subst hjk; simpa using hf j hj
      · simp [Pi.single_eq_of_ne hjk]
    · rintro ⟨-, hf⟩ k hk
      simpa using hf k k hk
  · constructor
    · intro h
      have h1 := ((h _).1 (mem_latSpan (L := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L)) ())).2
      have h2 := (mem_latSpan_single a _).1 ((h (Pi.single 0 1)).2
        ⟨fun _ => trivial, fun k hk => Pi.single_eq_of_ne hk.ne _⟩)
      by_contra hne
      rcases lt_or_gt_of_ne hne with h' | h'
      · simpa using h1 a h'
      · simpa using h2 0 h'
    · rintro rfl f
      simp [mem_latSpan_single]

theorem not_graded :
    ¬ Graded (latSpan (LL := L) (fun _ : Unit =>
      (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L))))) := by
  intro h
  have key : ∀ f ∈ latSpan (LL := L) (fun _ : Unit =>
      (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L)))), (f 0).1 = (f (-1)).2 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨e, x, rfl⟩ := hf
      have h1 : conv e (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L))) (-1)
          = PowerSeries.coeff 0 e • ((0, 1) : L × L) := by
        unfold conv
        rw [finsum_eq_single _ 0]
        · simp
        · intro j hj
          have h1 : (-1 : ℤ) - (j : ℤ) ≠ 0 := by omega
          have h2 : (-1 : ℤ) - (j : ℤ) ≠ -1 := by omega
          simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
      have h2 : conv e (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L))) 0
          = PowerSeries.coeff 0 e • ((1, 0) : L × L) + PowerSeries.coeff 1 e • ((0, 1) : L × L) := by
        unfold conv
        rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
        · simp
        · intro j hj
          by_contra hc
          apply hj
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff, not_or] at hc
          have h1 : (0 : ℤ) - (j : ℤ) ≠ 0 := by omega
          have h2 : (0 : ℤ) - (j : ℤ) ≠ -1 := by omega
          simp only [Pi.add_apply, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, add_zero, smul_zero]
      rw [h1, h2]
      simp
    | zero => rfl
    | add f g _ _ hf hg => simp [hf, hg]
    | smul c f _ hf => simp [hf]
  have h1 := ((h _).1 (mem_latSpan (L := L) (fun _ : Unit =>
      (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L)))) ())).2 0
  have h2 := key _ h1
  simp at h2

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
theorem _root_.GlobalTheory.NL.Model.mem_van (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (i : ZMod n) (ζ : LL)
    (k : ℕ) (a : _root_.Formalism.BasicNotions.LetA O n) :
    a ∈ _root_.GlobalTheory.NL.van W i ζ k ↔
      ∀ j < k, PowerSeries.coeff j (W.lev i ζ a) = 0 := by
  rw [_root_.GlobalTheory.NL.van, Ideal.mem_comap, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in

theorem _root_.GlobalTheory.NL.Model.pi_van_one (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (i : ZMod n) :
    (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) ∈ _root_.GlobalTheory.NL.van W i 1 1 ∧
      (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) ∉ _root_.GlobalTheory.NL.van W i 1 2 := by
  obtain ⟨E, h0, hd, hE⟩ := W.lev_π i 1 ⟨0, by simp⟩
  have hlev : W.lev i 1 _root_.Formalism.BasicNotions.letπ = E - 1 := by
    rw [map_one, one_mul] at hE
    rw [← hE]
    ring
  have h1 : PowerSeries.coeff 1 E = 1 := by
    have := congrArg (PowerSeries.coeff 0) hd
    simp only [PowerSeries.coeff_derivative] at this
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0] at this
    simpa using this
  simp only [_root_.GlobalTheory.NL.Model.mem_van, hlev]
  refine ⟨fun j hj => ?_, fun h => ?_⟩
  · obtain rfl : j = 0 := by omega
    simp [h0]
  · have := h 1 (by norm_num)
    simp [h1] at this

theorem pi_not_van (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) (j : ℕ)
    (hζ : IsPrimitiveRoot ζ (PD.p ^ j)) (h1 : ζ ≠ 1) : (letπ : LetA O n) ∉ van W i ζ 1 := by
  obtain ⟨E, h0, -, h2⟩ := W.lev_π i ζ ⟨j, hζ⟩
  rw [mem_van]
  intro h
  have h3 := h 0 (by omega)
  have h4 := congrArg (PowerSeries.coeff 0) h2
  rw [map_add, h3] at h4
  simp [h0] at h4
  exact h1 h4.symm

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
theorem _root_.GlobalTheory.NL.Model.FilAt_anti (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    _root_.GlobalTheory.NL.FilAt PD T τ (a + 1) ≤ _root_.GlobalTheory.NL.FilAt PD T τ a := by
  refine sup_le_sup_right ?_ _
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FildR _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  refine inf_le_inf_left _ ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul w b => exact ⟨w ⊗ₜ ⟨b, PD.Fil_anti a b.2⟩, rfl⟩
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz

theorem wachExpansion_smul_compatible (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (e : ↥(W.N T) → ℤ → T.V ⊗[Qp] B) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, e x k = 0)
    (he : ∀ x k, W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (e x k))
    (a : LetA O n) (x : ↥(W.N T)) : e (a • x) = conv (W.lev i ζ a) (e x) := by
  have hinj : Function.Injective (ιV PD (LL := LL) (V := T.V)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := T.V)
      (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj
  obtain ⟨m, hm⟩ := hs x
  funext k
  apply hinj
  rw [← he, W.levN_smul]
  unfold conv
  rw [map_finsum _ (conv_finite (W.lev i ζ a) hm k)]
  refine finsum_congr fun j => ?_
  rw [LinearMap.map_smul, he]

theorem ext_aux {k E E' Ω : Type} [Field k] [Field E] [Field E'] [Field Ω] [Algebra k E] [Algebra k E']
    [Algebra k Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic k E'] (τ : E →ₐ[k] E') (j : E →ₐ[k] Ω) :
    ∃ σ : E' →ₐ[k] Ω, ∀ y, σ (τ y) = j y := by
  letI : Algebra E E' := τ.toRingHom.toAlgebra
  haveI : IsScalarTower k E E' := IsScalarTower.of_algebraMap_eq fun x => (τ.commutes x).symm
  haveI : Algebra.IsAlgebraic E E' := Algebra.IsAlgebraic.tower_top (K := k) _
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := k) (L := E) (M := Ω) (E := E') j
  exact ⟨φ, fun x => DFunLike.congr_fun hφ x⟩

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}

open TensorProduct in
variable {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l} {AI : _root_.Formalism.BasicNotions.LocAinf l P} {H : _root_.Formalism.BasicNotions.LocHW l P}
  {F : _root_.Formalism.BasicNotions.LocFon l P AI H} {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {s : ℕ} {LL : _root_.Formalism.BasicNotions.Loc.FinExt l} in
theorem _root_.GlobalTheory.NL.Model.ex_mem_Lat (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) (h : _root_.Formalism.BasicNotions.Loc.Good K s LL)
    (T : _root_.GlobalTheory.NL.Lt K LL) (i : _root_.GlobalTheory.NL.Let K) (ζ : ↥LL.1)
    (x : ↥((H.W K s LL h).N T)) :
    _root_.GlobalTheory.NL.ex C h T i ζ x ∈ _root_.GlobalTheory.NL.Lat C h T i ζ :=
  _root_.GlobalTheory.NL.Model.mem_latSpan _ x

open TensorProduct in
variable {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l} {AI : _root_.Formalism.BasicNotions.LocAinf l P} {H : _root_.Formalism.BasicNotions.LocHW l P}
  {F : _root_.Formalism.BasicNotions.LocFon l P AI H} {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {s : ℕ} {LL : _root_.Formalism.BasicNotions.Loc.FinExt l} in

theorem _root_.GlobalTheory.NL.Model.Lat_coeff (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F)
    (h : _root_.Formalism.BasicNotions.Loc.Good K s LL) (T : _root_.GlobalTheory.NL.Lt K LL) (i : _root_.GlobalTheory.NL.Let K)
    (ζ : ↥LL.1) (f : ℤ → T.V ⊗[ℚ_[l]] P.R.B) (hf : f ∈ _root_.GlobalTheory.NL.Lat C h T i ζ) :
    (∀ k, f k ∈ _root_.GlobalTheory.NL.Di H h T i) ∧ ∃ m : ℤ, ∀ k < m, f k = 0 :=
  _root_.GlobalTheory.NL.Model.latSpan_coeff _ _
    (fun x k => (C.C K s LL h).tie.levB_mem T i ζ x k)
    (fun x => (C.C K s LL h).tie.levB_supp T i ζ x) f hf

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
private theorem periodTensor_ιV_injective (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) :
    Function.Injective (_root_.Formalism.WeaklyAdmissibleFiltrations.ιV PD : T.V ⊗[Qp] B →ₗ[LL] T.V ⊗[Qp] BdR) := by
  have hf : Function.Injective ((PD.ι.toLinearMap).restrictScalars Qp) := PD.ι_inj
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) _ hf

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
private theorem levB_smul_eq_powerSeriesSmul_lemma_2 {Zl Ai : Type} [CommRing Zl] [CommRing Ai]
    [Algebra Zl O] [Algebra Zl Ai] {W : _root_.Formalism.BasicNotions.LocWach PD LL O v n} {RW : Type} [CommRing RW]
    [Algebra O RW] {inclR : TensorProduct Zl O Ai →ₐ[O] RW} {φR : RW →ₐ[O] RW}
    {gR : G → RW →ₐ[O] RW} {πA : TensorProduct Zl O Ai}
    {E : _root_.Formalism.BasicNotions.EtTie W (TensorProduct Zl O Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai}
    {tS zS : BdR} (S : _root_.Formalism.BasicNotions.CmpTie W E ιdR p1 tS zS) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (a : _root_.Formalism.BasicNotions.LetA O n) (x : ↥(W.N T)) :
    S.levB T i ζ (a • x) = _root_.GlobalTheory.NL.conv (W.lev i ζ a) (S.levB T i ζ x) := by
  funext k
  refine periodTensor_ιV_injective (PD := PD) T ?_
  obtain ⟨m, hm⟩ := S.levB_supp T i ζ x
  rw [← S.levN_eq, W.levN_smul, _root_.GlobalTheory.NL.conv,
    map_finsum _ (_root_.GlobalTheory.NL.Model.conv_finite _ hm k)]
  simp only [map_smul, S.levN_eq]

open TensorProduct in
variable {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l} {AI : _root_.Formalism.BasicNotions.LocAinf l P} {H : _root_.Formalism.BasicNotions.LocHW l P}
  {F : _root_.Formalism.BasicNotions.LocFon l P AI H} {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {s : ℕ} {LL : _root_.Formalism.BasicNotions.Loc.FinExt l} in

theorem _root_.GlobalTheory.NL.Model.ex_smul (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) (h : _root_.Formalism.BasicNotions.Loc.Good K s LL)
    (T : _root_.GlobalTheory.NL.Lt K LL) (i : _root_.GlobalTheory.NL.Let K) (ζ : ↥LL.1) (a : _root_.GlobalTheory.NL.AA K LL)
    (x : ↥((H.W K s LL h).N T)) :
    _root_.GlobalTheory.NL.ex C h T i ζ (a • x) =
      _root_.GlobalTheory.NL.conv ((H.W K s LL h).lev i ζ a) (_root_.GlobalTheory.NL.ex C h T i ζ x) :=
  levB_smul_eq_powerSeriesSmul_lemma_2 _ T i ζ a x

theorem zetaQ_pow (P : LocPrime l) (s : ℕ) : P.ζQ s ^ (l ^ s) = 1 := by
  induction s with
  | zero => simp [P.ζQ_zero]
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem zetaQ_mem (P : LocPrime l) (K : FinExt l) (s : ℕ) : P.ζQ s ∈ Ks K s :=
  (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ (zetaQ_pow P s))

theorem unramifiedSubfield_le_cyclotomicExt (K : FinExt l) (s : ℕ) : K0 K ≤ Ks K s := le_sup_left

theorem comp_of_pt (h : Good K s LL) (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hp : Pt H h i ζ τ) : ∃ ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR, Comp H h i ζ τ ι := by
  obtain ⟨τs, ⟨h1, h2⟩, h3⟩ := hp
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨σ, hσ'⟩ := ext_aux τs (Ks K s).val
  have hσ : ∀ y : ↥(Ks K s), σ (τs y) = (y : Om l) := hσ'
  refine ⟨(IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp σ, ?_, ?_, ?_⟩
  · intro c
    rw [← h1 c ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩ rfl]
    change algebraMap (Om l) P.R.BdR (σ (τs _)) = _
    rw [hσ]; rfl
  · rw [← h2 ⟨_, zetaQ_mem P K s⟩ rfl]
    change algebraMap (Om l) P.R.BdR (σ (τs _)) = _
    rw [hσ]
  · intro c
    rw [h3 c ⟨c, h.2.2.1 c.2⟩ rfl]
    change algebraMap (Om l) P.R.BdR (σ (τs _)) = _
    rw [hσ]; rfl

theorem exists_pt (h : Good K s LL) (i : Let K) :
    ∃ (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), Pt H h i ζ τ := by
  let e : ↥(K0 K) →ₐ[ℚ_[l]] Om l := LL.1.val.comp ((H.W K s LL h).emb i)
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l, ∀ x : ↥(K0 K), φ ⟨x, unramifiedSubfield_le_cyclotomicExt K s x.2⟩ = e x := by
    letI : Algebra ↥(K0 K) ↥(Ks K s) := (IntermediateField.inclusion (unramifiedSubfield_le_cyclotomicExt K s)).toRingHom.toAlgebra
    haveI : IsScalarTower ℚ_[l] ↥(K0 K) ↥(Ks K s) := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Algebra.IsAlgebraic ↥(K0 K) ↥(Ks K s) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
    obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := ℚ_[l]) (L := ↥(K0 K)) (M := Om l) (E := ↥(Ks K s)) e
    exact ⟨φ, fun x => DFunLike.congr_fun hφ x⟩
  let τs : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := φ.codRestrict LL.1.toSubalgebra (h.2.2.2 φ)
  refine ⟨τs ⟨_, zetaQ_mem P K s⟩, τs.comp (IntermediateField.inclusion h.2.2.1), τs, ⟨?_, ?_⟩, ?_⟩
  · intro x y hy
    obtain rfl : y = ⟨x, unramifiedSubfield_le_cyclotomicExt K s x.2⟩ := Subtype.ext hy
    exact Subtype.ext (hφ x)
  · intro y hy
    obtain rfl : y = ⟨_, zetaQ_mem P K s⟩ := Subtype.ext hy
    rfl
  · intro x y hy
    obtain rfl : y = ⟨x, h.2.2.1 x.2⟩ := Subtype.ext hy
    rfl

theorem not_pt_one (h : Good K s LL) (i : Let K) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : ¬ Pt H h i 1 τ := by
  rintro ⟨τs, ⟨-, h2⟩, -⟩
  have h3 := h2 ⟨_, zetaQ_mem P K s⟩ rfl
  rw [← map_one τs] at h3
  have h4 : P.ζQ s = 1 := congrArg Subtype.val (τs.toRingHom.injective h3)
  have key : ∀ m, P.ζQ (m + 1) ≠ 1 := by
    intro m
    induction m with
    | zero => exact P.ζQ_one
    | succ m ih => intro h; apply ih; rw [← P.ζQ_succ (m + 1), h, one_pow]
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by have := h.1; omega⟩
  exact key m h4

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem comp_tie (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ)
    (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR)
    (hι : Comp H h i ζ τ ι) (x : ↥((H.W K s LL h).N T)) (k : ℕ) (y : TW (RA LL) T)
    (hy : TWincl (inclR LL) T y = (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁)) ^ k •
      (F.E K s LL h).tie.jD T (x : (H.W K s LL h).DD T))
    (a : ℕ) (ha : ∀ r : ℤ, r < -(a : ℤ) → (H.W K s LL h).levN T i ζ x r = 0) :
    ∃ c : ℤ, ∀ M : ℕ,
      mulVR T (tS P s ^ a) ((C.C K s LL h).tie.βdR T y) - mulVR T ((P.ιB (AI.ιA AI.π₁)) ^ k)
        (∑ r ∈ Finset.range M, mulVR T (tS P s ^ r) ((H.W K s LL h).levN T i ζ x ((r : ℤ) - (a : ℤ)))) ∈
      compKer T ι ⊔ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) ((M : ℤ) - c) :=
  (C.C K s LL h).tie.levN_dR T hT i ζ ι hι.1 hι.2.1 x k y hy a ha

end Concrete

end GlobalTheory.NL.Model
