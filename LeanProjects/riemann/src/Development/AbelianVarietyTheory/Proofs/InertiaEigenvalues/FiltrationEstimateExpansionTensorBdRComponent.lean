import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesTransport

noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

section Filt

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

end Filt

open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] in
private theorem tmul_mem_filV_of_mem_fil (n : ℤ) (v : V) {y : BdR} (hy : y ∈ PD.Fil n) :
    v ⊗ₜ[Qp] y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) n := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  exact ⟨v ⊗ₜ[Qp] (⟨y, hy⟩ : (PD.Fil n).restrictScalars Qp), by simp⟩

open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
private theorem fil_antitone' {a b : ℤ} (h : b ≤ a) : PD.Fil a ≤ PD.Fil b := by
  induction a, h using Int.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (PD.Fil_anti n).trans ih

open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] in
private theorem filV_antitone' {a b : ℤ} (h : b ≤ a) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a ≤ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b := by
  intro x hx
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV at hx
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simpa using tmul_mem_filV_of_mem_fil PD b v (fil_antitone' PD h y.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] in
private theorem exists_mem_filV' (x : V ⊗[Qp] BdR) : ∃ n, x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) n := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v y =>
    obtain ⟨n, hn⟩ := PD.Fil_exh y
    exact ⟨n, tmul_mem_filV_of_mem_fil PD n v hn⟩
  | add x y hx hy =>
    obtain ⟨n₁, h₁⟩ := hx
    obtain ⟨n₂, h₂⟩ := hy
    exact ⟨min n₁ n₂, add_mem (filV_antitone' PD (min_le_left _ _) h₁)
      (filV_antitone' PD (min_le_right _ _) h₂)⟩

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_tmul' (β : BdR) (v : T.V) (y : BdR) :
    _root_.Formalism.BasicNotions.mulVR T β (v ⊗ₜ[Qp] y) = v ⊗ₜ[Qp] (β * y) := by
  simp [_root_.Formalism.BasicNotions.mulVR]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_mulVR' (β γ : BdR) (x : T.V ⊗[Qp] BdR) :
    _root_.Formalism.BasicNotions.mulVR T β (_root_.Formalism.BasicNotions.mulVR T γ x) = _root_.Formalism.BasicNotions.mulVR T (β * γ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp only [mulVR_tmul', mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_mem_compKer (ι : LL →ₐ[Qp] BdR) (β : BdR) {x : T.V ⊗[Qp] BdR}
    (hx : x ∈ _root_.Formalism.BasicNotions.compKer T ι) : _root_.Formalism.BasicNotions.mulVR T β x ∈ _root_.Formalism.BasicNotions.compKer T ι := by
  unfold _root_.Formalism.BasicNotions.compKer at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, y, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨c, _root_.Formalism.BasicNotions.mulVR T β y, ?_⟩
    rw [map_sub, LinearMap.map_smul, mulVR_mulVR', mulVR_mulVR', mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ c hx

open TensorProduct in
private theorem mulRight_mem_filV_lemma_4 {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type}
    [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K]
    [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B]
    [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {p n : ℤ} {β : BdR}
    (hβ : β ∈ PD.Fil p) {x : T.V ⊗[Qp] BdR} (hx : x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) n) :
    _root_.Formalism.BasicNotions.mulVR T β x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (p + n) := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV at hx
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v y =>
    simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype,
      mulVR_tmul']
    exact tmul_mem_filV_of_mem_fil PD _ v (PD.Fil_mul _ _ _ _ hβ y.2)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_add' (β γ : BdR) (x : T.V ⊗[Qp] BdR) :
    _root_.Formalism.BasicNotions.mulVR T (β + γ) x = _root_.Formalism.BasicNotions.mulVR T β x + _root_.Formalism.BasicNotions.mulVR T γ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp only [mulVR_tmul', add_mul, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_zero' (x : T.V ⊗[Qp] BdR) : _root_.Formalism.BasicNotions.mulVR T 0 x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp only [mulVR_tmul', zero_mul, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem mulVR_sum {ι : Type} (s : Finset ι) (f : ι → BdR) (x : T.V ⊗[Qp] BdR) :
    _root_.Formalism.BasicNotions.mulVR T (∑ i ∈ s, f i) x = ∑ i ∈ s, _root_.Formalism.BasicNotions.mulVR T (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mulVR_zero']
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, mulVR_add', ih]

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
private theorem smul_sub_mulVR_mem_compKer (ι : LL →ₐ[Qp] BdR) (c : LL) (x : T.V ⊗[Qp] BdR) :
    c • x - _root_.Formalism.BasicNotions.mulVR T (ι c) x ∈ _root_.Formalism.BasicNotions.compKer T ι := by
  unfold _root_.Formalism.BasicNotions.compKer
  exact Submodule.subset_span ⟨c, x, rfl⟩

open TensorProduct in

theorem _root_.GlobalTheory.HWL.Cmp.filt_expansion_component : ∀ {G : Type} [Group G]
    [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀]
    [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B]
    [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR]
    [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR]
    [IsScalarTower Qp K₀ BdR] (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (tS pk : BdR), IsUnit tS → tS ∈ PD.Fil 1 →
    ∀ (r w : ℕ) (z : T.V ⊗[Qp] BdR) (D : Fin r → T.V ⊗[Qp] BdR) (b : Fin r → BdR)
    (e : Fin r → PowerSeries LL) (L : ℤ → T.V ⊗[Qp] BdR),
    _root_.Formalism.BasicNotions.mulVR T (tS ^ w) z - ∑ j, _root_.Formalism.BasicNotions.mulVR T (b j) (D j) ∈ _root_.Formalism.BasicNotions.compKer T ι →
    (∀ (j : Fin r) (m : ℕ), b j - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (e j)) * tS ^ k ∈
      PD.Fil (m : ℤ)) →
    (∀ k : ℤ, L k - ∑ j, _root_.GlobalTheory.HWL.Cmp.cz (e j) (k + (w : ℤ)) • D j ∈ _root_.Formalism.BasicNotions.compKer T ι) →
    ∀ a : ℕ, (∀ k : ℤ, k < -(a : ℤ) → L k = 0) → ∃ c : ℤ, ∀ M : ℕ,
      _root_.Formalism.BasicNotions.mulVR T (tS ^ a) (_root_.Formalism.BasicNotions.mulVR T pk z) -
        _root_.Formalism.BasicNotions.mulVR T pk (∑ k ∈ Finset.range M, _root_.Formalism.BasicNotions.mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) ∈
      _root_.Formalism.BasicNotions.compKer T ι ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ T ι tS pk
    hunit htS r w z D b e L hz hb hL a hLa
  classical
  set C := _root_.Formalism.BasicNotions.compKer T ι with hC

  set t : BdRˣ := hunit.unit with ht_def
  have htt : (t : BdR) = tS := hunit.unit_spec
  set τ : ℤ → BdR := fun n => ((t ^ n : BdRˣ) : BdR) with hτ_def
  have τ_add : ∀ m n : ℤ, τ (m + n) = τ m * τ n := fun m n => by
    simp only [hτ_def, zpow_add, Units.val_mul]
  have τ_nat : ∀ n : ℕ, τ n = tS ^ n := fun n => by
    simp only [hτ_def, zpow_natCast, Units.val_pow_eq_pow_val, htt]

  obtain ⟨q₁, hq₁⟩ := PD.Fil_exh (1 : BdR)
  have hpow : ∀ n : ℕ, tS ^ n ∈ PD.Fil (q₁ + n) := by
    intro n
    induction n with
    | zero => simpa using hq₁
    | succ n ih =>
      rw [pow_succ]
      convert PD.Fil_mul _ _ _ _ ih htS using 2
      push_cast
      ring
  obtain ⟨p, hp⟩ := PD.Fil_exh pk
  set β₀ : BdR := pk * τ ((a : ℤ) - w) with hβ₀_def
  obtain ⟨q₂, hq₂⟩ := PD.Fil_exh β₀
  choose dj hdj using fun j => exists_mem_filV' PD (LL := LL) (D j)
  set d : ℤ := -∑ j, |dj j| with hd_def
  have hDd : ∀ j, D j ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) d := fun j => by
    refine filV_antitone' PD ?_ (hdj j)
    have h1 : |dj j| ≤ ∑ i, |dj i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (dj i)) (Finset.mem_univ j)
    have h2 := neg_abs_le (dj j)
    linarith
  have hmulS : ∀ {β : BdR} {q n : ℤ} {x : T.V ⊗[Qp] BdR}, β ∈ PD.Fil q →
      x ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) n →
      _root_.Formalism.BasicNotions.mulVR T β x ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (q + n) := by
    intro β q n x hβ hx
    obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (mulVR_mem_compKer T ι β hy) (mulRight_mem_filV_lemma_4 PD T hβ hy')
  have hsupmono : ∀ {m n : ℤ}, n ≤ m → C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) m ≤
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) n := fun h => sup_le_sup_left (filV_antitone' PD h) _

  have hcoeff : ∀ (f : PowerSeries LL) (k : ℕ), _root_.GlobalTheory.HWL.Cmp.cz f (k : ℤ) = PowerSeries.coeff k f := by
    intro f k
    simp [_root_.GlobalTheory.HWL.Cmp.cz]
  have hLC : ∀ i : ℤ, i < -(w : ℤ) → L i ∈ C := by
    intro i hi
    have h := hL i
    simpa [_root_.GlobalTheory.HWL.Cmp.cz_neg _ (show i + (w : ℤ) < 0 by omega)] using h
  have hLF : ∀ i : ℤ, L i ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) d := by
    intro i
    have hs : ∑ j, _root_.GlobalTheory.HWL.Cmp.cz (e j) (i + (w : ℤ)) • D j ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) d :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hDd j)
    have h := Submodule.add_mem_sup (hL i) hs
    rwa [sub_add_cancel] at h

  set H : ℤ → T.V ⊗[Qp] BdR := fun i => _root_.Formalism.BasicNotions.mulVR T (pk * τ (i + a)) (L i) with hH_def
  have hH0 : ∀ i : ℤ, i < -(a : ℤ) → H i = 0 := fun i hi => by
    simp only [hH_def, hLa i hi, map_zero]
  have hHC : ∀ i : ℤ, i < -(w : ℤ) → H i ∈ C := fun i hi =>
    mulVR_mem_compKer T ι _ (hLC i hi)
  have hHF : ∀ (N : ℕ) (i : ℤ), (N : ℤ) ≤ i + a →
      H i ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (N + (p + q₁ + d)) := by
    intro N i hi
    obtain ⟨n, hn⟩ : ∃ n : ℕ, i + a = n := ⟨(i + a).toNat, by omega⟩
    have hβ : pk * τ (i + a) ∈ PD.Fil (p + (q₁ + n)) := by
      rw [hn, τ_nat]
      exact PD.Fil_mul _ _ _ _ hp (hpow n)
    refine hsupmono ?_ (hmulS hβ (hLF i))
    omega

  have hbase : ∑ k ∈ Finset.range w, H ((k : ℤ) - w) - ∑ k ∈ Finset.range a, H ((k : ℤ) - a) ∈ C := by
    have e1 : ∑ k ∈ Finset.range (a + w), H ((k : ℤ) - ((a + w : ℕ) : ℤ)) =
        ∑ k ∈ Finset.range a, H ((k : ℤ) - ((a + w : ℕ) : ℤ)) +
          ∑ k ∈ Finset.range w, H ((k : ℤ) - w) := by
      rw [Finset.sum_range_add]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      push_cast
      ring
    have e2 : ∑ k ∈ Finset.range (a + w), H ((k : ℤ) - ((a + w : ℕ) : ℤ)) =
        ∑ k ∈ Finset.range a, H ((k : ℤ) - a) := by
      rw [add_comm a w, Finset.sum_range_add, Finset.sum_eq_zero (fun k hk => hH0 _ ?_), zero_add]
      · refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        push_cast
        ring
      · have := Finset.mem_range.mp hk
        push_cast
        omega
    have hC1 : ∑ k ∈ Finset.range a, H ((k : ℤ) - ((a + w : ℕ) : ℤ)) ∈ C :=
      Submodule.sum_mem _ fun k hk => hHC _ (by have := Finset.mem_range.mp hk; push_cast; omega)
    have hrw : ∑ k ∈ Finset.range w, H ((k : ℤ) - w) - ∑ k ∈ Finset.range a, H ((k : ℤ) - a) =
        -∑ k ∈ Finset.range a, H ((k : ℤ) - ((a + w : ℕ) : ℤ)) := by
      rw [← e2, e1]
      abel
    rw [hrw]
    exact neg_mem hC1
  have hshift : ∀ N : ℕ, ∑ k ∈ Finset.range (N + w), H ((k : ℤ) - w) -
      ∑ k ∈ Finset.range (N + a), H ((k : ℤ) - a) ∈ C := by
    intro N
    induction N with
    | zero => simpa using hbase
    | succ N ih =>
      rw [show N + 1 + w = (N + w) + 1 by ring, show N + 1 + a = (N + a) + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
      have heq : H (((N + w : ℕ) : ℤ) - w) = H (((N + a : ℕ) : ℤ) - a) := by
        congr 1
        push_cast
        ring
      rw [heq]
      convert ih using 1
      abel

  refine ⟨-(min (p + q₁ + d) (q₂ + w + d)), fun M => ?_⟩
  have hmin1 := min_le_left (p + q₁ + d) (q₂ + w + d)
  have hmin2 := min_le_right (p + q₁ + d) (q₂ + w + d)
  have hbnd1 : C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (M + (p + q₁ + d)) ≤
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) ((M : ℤ) - -(min (p + q₁ + d) (q₂ + w + d))) :=
    hsupmono (by omega)
  have hbnd2 : C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (q₂ + ((M + w : ℕ) : ℤ) + d) ≤
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) ((M : ℤ) - -(min (p + q₁ + d) (q₂ + w + d))) :=
    hsupmono (by push_cast; omega)

  have hτw : τ ((a : ℤ) - w) * tS ^ w = tS ^ a := by
    rw [← τ_nat w, ← τ_add, sub_add_cancel, τ_nat]
  have eqB : _root_.Formalism.BasicNotions.mulVR T (tS ^ a) (_root_.Formalism.BasicNotions.mulVR T pk z) = _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) := by
    rw [mulVR_mulVR', mulVR_mulVR', hβ₀_def, mul_assoc, hτw, mul_comm]
  have eqC : _root_.Formalism.BasicNotions.mulVR T pk (∑ k ∈ Finset.range M, _root_.Formalism.BasicNotions.mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) =
      ∑ k ∈ Finset.range M, H ((k : ℤ) - a) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVR_mulVR', hH_def]
    dsimp only
    rw [sub_add_cancel, τ_nat]
  have m1 : _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) - ∑ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) ∈ C := by
    have h := mulVR_mem_compKer T ι β₀ hz
    rwa [map_sub, map_sum] at h
  have hstep : ∀ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) -
      (∑ k ∈ Finset.range (M + w), PowerSeries.coeff k (e j) • _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (D j) +
        _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
          ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j)) ∈ C := by
    intro j
    have hsplit : _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) =
        ∑ k ∈ Finset.range (M + w),
          _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (_root_.Formalism.BasicNotions.mulVR T (ι (PowerSeries.coeff k (e j))) (D j)) +
        _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
          ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j) := by
      rw [mulVR_mulVR']
      rw [show β₀ * b j = β₀ * (∑ k ∈ Finset.range (M + w), ι (PowerSeries.coeff k (e j)) * tS ^ k) +
          β₀ * (b j - ∑ k ∈ Finset.range (M + w), ι (PowerSeries.coeff k (e j)) * tS ^ k) by ring,
        mulVR_add', Finset.mul_sum, mulVR_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mulVR_mulVR']
      exact congrArg (fun β => _root_.Formalism.BasicNotions.mulVR T β (D j)) (by ring)
    rw [hsplit, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h := mulVR_mem_compKer T ι (β₀ * tS ^ k)
      (smul_sub_mulVR_mem_compKer T ι (PowerSeries.coeff k (e j)) (D j))
    rw [map_sub, LinearMap.map_smul] at h
    rw [← neg_sub]
    exact neg_mem h
  have m2 := Submodule.sum_mem C (t := Finset.univ) fun j _ => hstep j
  rw [Finset.sum_sub_distrib] at m2
  have hβk : ∀ k : ℕ, pk * τ ((k : ℤ) - w + a) = β₀ * tS ^ k := fun k => by
    rw [show (k : ℤ) - w + a = ((a : ℤ) - w) + k by ring, τ_add, τ_nat, hβ₀_def, mul_assoc]
  have hterm : ∀ k : ℕ, _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) -
      H ((k : ℤ) - w) ∈ C := by
    intro k
    have h := mulVR_mem_compKer T ι (β₀ * tS ^ k) (hL ((k : ℤ) - w))
    simp only [sub_add_cancel, hcoeff] at h
    have h' := neg_mem h
    rw [← map_neg, neg_sub] at h'
    rw [hH_def]
    dsimp only
    rw [hβk k, ← map_sub]
    exact h'
  have m3 := Submodule.sum_mem C (t := Finset.range (M + w)) fun k _ => hterm k
  rw [Finset.sum_sub_distrib] at m3
  have m4 := hshift M
  have eqD : ∑ k ∈ Finset.range (M + a), H ((k : ℤ) - a) =
      ∑ k ∈ Finset.range M, H ((k : ℤ) - a) + ∑ k ∈ Finset.range a, H (((M + k : ℕ) : ℤ) - a) :=
    Finset.sum_range_add _ _ _
  have m5 : ∑ k ∈ Finset.range a, H (((M + k : ℕ) : ℤ) - a) ∈
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (M + (p + q₁ + d)) :=
    Submodule.sum_mem _ fun k _ => hHF M _ (by push_cast; omega)
  have m6 : ∑ j, _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
      ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j) ∈
      _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (q₂ + ((M + w : ℕ) : ℤ) + d) :=
    Submodule.sum_mem _ fun j _ => mulRight_mem_filV_lemma_4 PD T (PD.Fil_mul _ _ _ _ hq₂ (hb j (M + w)))
      (hDd j)
  have eqA : ∑ j, ∑ k ∈ Finset.range (M + w), PowerSeries.coeff k (e j) • _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (D j) =
      ∑ k ∈ Finset.range (M + w), _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    simp only [LinearMap.map_smul]
  rw [Finset.sum_add_distrib, eqA] at m2
  rw [eqB, eqC]
  have hX : _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) - ∑ k ∈ Finset.range M, H ((k : ℤ) - a) =
      (_root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) - ∑ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j))) +
      (∑ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) -
        (∑ k ∈ Finset.range (M + w), _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) +
          ∑ j, _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
            ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j))) +
      (∑ k ∈ Finset.range (M + w), _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) -
        ∑ k ∈ Finset.range (M + w), H ((k : ℤ) - w)) +
      (∑ k ∈ Finset.range (M + w), H ((k : ℤ) - w) - ∑ k ∈ Finset.range (M + a), H ((k : ℤ) - a)) +
      ∑ k ∈ Finset.range a, H (((M + k : ℕ) : ℤ) - a) +
      ∑ j, _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
        ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j) := by
    rw [eqD]
    abel
  rw [hX]
  refine add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) (hbnd1 m5))
    (hbnd2 (Submodule.mem_sup_right m6))
  · exact Submodule.mem_sup_left m1
  · exact Submodule.mem_sup_left m2
  · exact Submodule.mem_sup_left m3
  · exact Submodule.mem_sup_left m4

end GlobalTheory.HWL.Cmp
