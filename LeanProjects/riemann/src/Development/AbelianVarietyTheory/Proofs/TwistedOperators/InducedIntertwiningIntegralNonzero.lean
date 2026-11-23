import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedKFiniteRestrictionStatement

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.IntertwiningDense
variable {n : ℕ} {ε : Fin n → Bool}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem inG_of_exp_mem {X : Matrix (Fin n) (Fin n) ℂ} (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ UJset ε) :
    inG ε X := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * Jm ε * NormedSpace.exp (t • X)) _ 0 :=
    (h1.mul_const (Jm ε)).mul h2
  have hc : (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * Jm ε * NormedSpace.exp (t • X)) = fun _ => Jm ε := by
    funext t
    have := h t
    rw [show t • Xᴴ = (t • X)ᴴ by rw [conjTranspose_smul, star_trivial], Matrix.exp_conjTranspose]
    exact this
  rw [hc] at h3
  have := h3.unique (hasDerivAt_const (0 : ℝ) (Jm ε))
  simpa [inG] using this
end

section Finite

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def transl (f : UJ ε → V) : Submodule ℂ (UJ ε → V) :=
  Submodule.span ℂ {φ | ∃ k ∈ KG ε, φ = fun g => f (g * k)}

theorem transl_mem (f : UJ ε → V) {k : UJ ε} (hk : k ∈ KG ε) : (fun g => f (g * k)) ∈ transl f :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem isKFinFun_of_mem {f : UJ ε → V} (U : Submodule ℂ (UJ ε → V)) [FiniteDimensional ℂ U]
    (h : ∀ k ∈ KG ε, (fun g => f (g * k)) ∈ U) : IsKFinFun f :=
  Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro φ ⟨k, hk, rfl⟩; exact h k hk))

theorem isKFinFun_add {f f' : UJ ε → V} (h : IsKFinFun f) (h' : IsKFinFun f') : IsKFinFun (f + f') := by
  haveI : FiniteDimensional ℂ (transl f) := h
  haveI : FiniteDimensional ℂ (transl f') := h'
  exact isKFinFun_of_mem (transl f ⊔ transl f') fun k hk =>
    Submodule.add_mem_sup (transl_mem f hk) (transl_mem f' hk)

theorem isKFinFun_smul {f : UJ ε → V} (h : IsKFinFun f) (c : ℂ) : IsKFinFun (c • f) := by
  haveI : FiniteDimensional ℂ (transl f) := h
  exact isKFinFun_of_mem (transl f) fun k hk => (transl f).smul_mem c (transl_mem f hk)

theorem isKFinFun_transl {f : UJ ε → V} (h : IsKFinFun f) {k₀ : UJ ε} (hk₀ : k₀ ∈ KG ε) :
    IsKFinFun fun g => f (g * k₀) := by
  haveI : FiniteDimensional ℂ (transl f) := h
  exact isKFinFun_of_mem (transl f) fun k hk => by
    simpa only [mul_assoc] using transl_mem f ((KG ε).mul_mem hk hk₀)

end Finite

section Integral

variable (D : Datum ε) (ν : Measure (UJ ε))

theorem isIntegral_zero : D.IsIntegral ν 0 0 := fun x v _ => by simp

variable {D ν}

theorem IsIntegral.add {f h f' h' : UJ ε → D.V} (a : D.IsIntegral ν f h) (b : D.IsIntegral ν f' h') :
    D.IsIntegral ν (f + f') (h + h') := fun x v hv => by
  obtain ⟨i1, e1⟩ := a x v hv
  obtain ⟨i2, e2⟩ := b x v hv
  refine ⟨by simp only [Pi.add_apply, inner_add_right]; exact i1.add i2, ?_⟩
  simp only [Pi.add_apply, inner_add_right, e1, e2]
  exact (integral_add i1 i2).symm

theorem IsIntegral.smul {f h : UJ ε → D.V} (a : D.IsIntegral ν f h) (c : ℂ) :
    D.IsIntegral ν (c • f) (c • h) := fun x v hv => by
  obtain ⟨i1, e1⟩ := a x v hv
  refine ⟨by simpa only [Pi.smul_apply, inner_smul_right] using i1.const_mul c, ?_⟩
  simp only [Pi.smul_apply, inner_smul_right, e1]
  exact (integral_const_mul c _).symm

theorem IsIntegral.transl {f h : UJ ε → D.V} (a : D.IsIntegral ν f h) (k : UJ ε) :
    D.IsIntegral ν (fun g => f (g * k)) (fun g => h (g * k)) := fun x v hv => by
  simpa only [mul_assoc] using a (x * k) v hv

end Integral

def oppDatum (D : Datum ε) : Datum ε where
  a := D.a
  j := D.j
  W := opp ε D.W
  flag := isIsoFlag_opp D.flag
  pos := D.pos
  V := D.V
  σ := D.σ
  temp := by rw [leviOne_opp]; exact D.temp
  s := -D.s

theorem oppDatum_M (D : Datum ε) : (oppDatum D).M = D.M := leviOne_opp

theorem isKFinIn_one {D : Datum ε} {h : UJ ε → D.V} (hh : h ∈ D.oppFns) (hk : IsKFinFun h) :
    IsKFinIn D.M D.σ (h 1) := by
  have := (GlobalTheory.T.induced_k_finite_restriction n ε (oppDatum D) h hh hk).2.1
  rwa [oppDatum_M] at this

theorem exists_ne_zero_K {D : Datum ε} {h : UJ ε → D.V} (hh : h ∈ D.oppFns) (hk : IsKFinFun h) (h0 : h ≠ 0) :
    ∃ k ∈ KG ε, h k ≠ 0 :=
  (GlobalTheory.T.induced_k_finite_restriction n ε (oppDatum D) h hh hk).2.2 h0

theorem eq_zero_of_K {D : Datum ε} {φ : UJ ε → D.V} (hφ : φ ∈ D.fns) (h : ∀ k ∈ KG ε, φ k = 0) : φ = 0 := by
  funext g
  obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact D.flag g
  obtain ⟨u, hu, m, hm, x, t, ht, e⟩ := exists_langlands_decomp D.flag D.pos hp
  have hkK : k ∈ KG ε := by rw [← SetLike.mem_coe, KG_eq]; exact hk
  have : g = u * m * t * k := by rw [← e]; group
  rw [this, (mem_indFun_top.1 hφ).2 u hu m hm x t ht k, h k hkK, map_zero, smul_zero]
  rfl

theorem ι_injective (I : IndModule ε) : Function.Injective I.ι := by
  haveI : IsProbabilityMeasure (muK ε) := ⟨Measure.haarMeasure_self⟩
  intro a b hab
  have h0 : I.ι (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hn := I.model.norm_sq (a - b)
  rw [h0, norm_zero] at hn
  have hc : Continuous fun k : KG ε => ‖(a - b).1 k‖ ^ 2 :=
    (((mem_indFun_top.1 (a - b).2).1.comp continuous_subtype_val).norm.pow 2)
  have hK : ∀ k ∈ KG ε, (a - b).1 k = 0 := fun k hk => by
    by_contra hne
    have := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := muK ε) (x := ⟨k, hk⟩)
      (isClosed_tsupport _).isCompact (fun _ => by positivity) (by simpa using hne)
    linarith
  have := eq_zero_of_K (D := I.toDatum) (a - b).2 hK
  exact sub_eq_zero.1 (Subtype.ext this)

def valSpace (I : IndModule ε) (ν : Measure (UJ ε)) : Submodule ℂ I.V where
  carrier := {w | ∃ f ∈ I.fns, IsKFinFun f ∧ ∃ h ∈ I.oppFns, IsKFinFun h ∧ I.IsIntegral ν f h ∧ h 1 = w}
  zero_mem' := ⟨0, zero_mem _, isKFinFun_of_mem ⊥ fun _ _ => (Submodule.mem_bot ℂ).2 (funext fun _ => rfl),
    0, zero_mem _, isKFinFun_of_mem ⊥ fun _ _ => (Submodule.mem_bot ℂ).2 (funext fun _ => rfl),
    isIntegral_zero _ _, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, hfk, h, hh, hhk, hi, rfl⟩ ⟨f', hf', hfk', h', hh', hhk', hi', rfl⟩
    exact ⟨f + f', add_mem hf hf', isKFinFun_add hfk hfk', h + h', add_mem hh hh', isKFinFun_add hhk hhk',
      IsIntegral.add hi hi', rfl⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, hfk, h, hh, hhk, hi, rfl⟩
    exact ⟨c • f, Submodule.smul_mem _ c hf, isKFinFun_smul hfk c, c • h, Submodule.smul_mem _ c hh,
      isKFinFun_smul hhk c, IsIntegral.smul hi c, rfl⟩

theorem one_mem_flagN {a : ℕ} (W : Flag n a) : (1 : UJ ε) ∈ flagN ε W :=
  have h1 : uMat (1 : UJ ε) = 1 := rfl
  ⟨fun i y _ => by simp [h1], fun y _ => by simp [h1]⟩

theorem intertwining_values_dense : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification →
    ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), I.Positive → ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν →
      ∀ v : I.V, v ≠ 0 → ∃ f ∈ I.fns, IsKFinFun f ∧ ∃ h ∈ I.oppFns, I.IsIntegral ν f h ∧ ⟪v, h 1⟫_ℂ ≠ 0 := by
  intro hHC hLC n ε I hpos ν hν v hv
  obtain ⟨hInd, hQuot, -⟩ := hLC
  obtain ⟨-, -, hgk, hiff, hder, -⟩ := hInd n ε I
  obtain ⟨hex, hrd, Z, hZ, hZgk, hZne, -, -⟩ := hQuot n ε I hpos ν hν
  have hS0 : valSpace I ν ≠ ⊥ := by
    obtain ⟨w, hw, hwZ⟩ : ∃ w ∈ kFinVec ε I.ρ, w ∉ Z := by
      by_contra hcon
      push_neg at hcon
      exact hZne (le_antisymm (fun w hw => hZgk.kFin w hw) hcon)
    obtain ⟨f, hfk, rfl⟩ := (hiff w).1 hw
    obtain ⟨h, hh, hhk, hi⟩ := hex f.1 f.2 hfk
    have hne : h ≠ 0 := by
      rintro rfl
      apply hwZ
      have : I.ι f ∈ (Z : Set I.H) := by rw [hZ]; exact ⟨f, hfk, rfl, hi⟩
      exact this
    obtain ⟨k, hk, hhk0⟩ := exists_ne_zero_K hh hhk hne
    intro hbot
    have hmem : h k ∈ valSpace I ν := ⟨fun g => f.1 (g * k), indFun_mul_right f.2 trivial,
      isKFinFun_transl hfk hk, fun g => h (g * k), indFun_mul_right hh trivial, isKFinFun_transl hhk hk,
      IsIntegral.transl hi k, by simp⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hhk0 hmem
  have hlie : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε I.W)) →
      ∀ w ∈ valSpace I ν, ∃ w' ∈ valSpace I ν,
        HasDerivAt (fun t : ℝ => I.σ (NormedSpace.exp (t • X)) w) w' 0 := by
    rintro X hX _ ⟨f, hf, hfk, h, hh, hhk, hi, rfl⟩
    have hXg : X ∈ lieSet ε := inG_of_exp_mem fun t => by
      obtain ⟨y, -, hy⟩ := hX t
      rw [← hy]
      exact y.2
    obtain ⟨f', hrf, hdf⟩ := hder ⟨f, hf⟩ hfk X hXg
    have hf'k : IsKFinFun f'.1 := by
      have h1 : IsKFin ε I.ρ (I.ι ⟨f, hf⟩) := (hiff _).2 ⟨⟨f, hf⟩, hfk, rfl⟩
      have h2 : IsKFin ε I.ρ (I.ι f') := by rw [← hdf]; exact hgk.lieStable X hXg _ h1
      obtain ⟨f'', hk'', he⟩ := (hiff _).1 h2
      rwa [ι_injective I he] at hk''
    obtain ⟨h', hh', hh'k, hi'⟩ := hex f'.1 f'.2 hf'k
    have hrh := hrd f hf hfk X hXg f'.1 h h' hrf hi hi'
    refine ⟨h' 1, ⟨f'.1, f'.2, hf'k, h', hh', hh'k, hi', rfl⟩, ?_⟩
    have e : (fun t : ℝ => h (1 * expG ε X t)) = fun t : ℝ => I.σ (NormedSpace.exp (t • X)) (h 1) := by
      funext t
      obtain ⟨y, hy, hyX⟩ := hX t
      have hyt : expG ε X t = y := by
        apply Subtype.ext
        apply Units.ext
        have := toM_expG ε X t hXg
        rw [Complex.coe_smul] at this
        exact this.trans hyX.symm
      rw [one_mul, hyt, ← hyX]
      have hy' : y ∈ leviOne ε (opp ε I.W) := by rw [leviOne_opp]; exact hy
      have := (mem_indFun_top.1 hh).2 1 (one_mem_flagN _) y hy' 0 1 isSplit_one 1
      simpa [pairing] using this
    have := hrh 1
    rwa [e] at this
  have hd := hHC.2 n ε I.a I.j I.W I.flag I.pos I.V I.σ I.temp.2.2.1 I.temp.2.1 (valSpace I ν) hS0
    (fun w ⟨f, hf, hfk, h, hh, hhk, hi, hw⟩ => hw ▸ isKFinIn_one hh hhk) hlie
  by_contra hcon
  push_neg at hcon
  have hz : ((valSpace I ν : Submodule ℂ I.V) : Set I.V) ⊆ {w | ⟪v, w⟫_ℂ = 0} :=
    fun w ⟨f, hf, hfk, h, hh, hhk, hi, hw⟩ => hw ▸ hcon f hf hfk h hh hi
  have hcl : IsClosed {w : I.V | ⟪v, w⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have : ⟪v, v⟫_ℂ = 0 := closure_minimal hz hcl (hd v)
  exact hv (inner_self_eq_zero.1 this)

end GlobalTheory.IntertwiningDense

end
