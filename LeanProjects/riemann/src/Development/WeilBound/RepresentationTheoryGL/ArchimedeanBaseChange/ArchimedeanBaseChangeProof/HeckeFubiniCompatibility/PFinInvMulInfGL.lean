import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenformsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateRationalEntriesBounded

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH)
open PositivityTheory.RgBcC.Bridge (along BridgeSt)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG.PAut

section Eig

variable {n : ℕ}

theorem rd_smul (c : ℂ) (X : Mat n) (F : Mat n → ℂ) : Rd X (c • F) = c • Rd X F := by
  funext g
  have e : fderiv ℝ (c • F) = c • fderiv ℝ F := fderiv_const_smul_field c
  simp only [Rd, e, Pi.smul_apply]
  rfl

theorem eu_smul (c : ℂ) (s : Bool) (i j : Fin n) (F : Mat n → ℂ) : Eu s i j (c • F) = c • Eu s i j F := by
  simp only [Eu, rd_smul]
  module

theorem epow_smul (c : ℂ) (s : Bool) (m : ℕ) (i j : Fin n) (F : Mat n → ℂ) :
    Epow s m i j (c • F) = c • Epow s m i j F := by
  induction m generalizing i j with
  | zero =>
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    simp only [Epow, ih, eu_smul, Finset.smul_sum]

theorem gel_smul' (c : ℂ) (s : Bool) (m : ℕ) (F : Mat n → ℂ) : gel s m (c • F) = c • gel s m F := by
  simp only [gel, epow_smul, Finset.smul_sum]

theorem isEig_smul {χ : Inf n} {F : Mat n → ℂ} (h : IsEig χ F) (c : ℂ) : IsEig χ (c • F) := by
  intro s m g hg
  rw [gel_smul', Pi.smul_apply, h s m g hg, Pi.smul_apply]
  exact smul_comm _ _ _

end Eig

section Tc

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem along_smul' (w : InfinitePlace E) (g : GA E a) (c : ℂ) (φ : GA E a → ℂ) :
    along w g (c • φ) = c • along w g φ := by
  funext x
  simp only [along, chart, Pi.smul_apply]
  split_ifs <;> simp

theorem zfin_of (φ : Sm E a) (c : (E →+* ℂ) → ℂ → ℂ) (hc : ∀ τ u, cap τ u φ = c τ u • φ) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' (Zalg E a : Set _))) := by
  have : FiniteDimensional ℂ (Submodule.span ℂ {φ}) := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton φ)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨s, hs⟩ := GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz
  show z φ ∈ _
  rw [hs φ hc]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self φ)

theorem kfin_of (φ : Sm E a) (W : Submodule ℂ (Kinf E a → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ z, (fun k : Kinf E a => φ.1 (z * infGL E a (Unitary.toUnits k))) ∈ W) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := by
  let Λ : Module.Dual ℂ W →ₗ[ℂ] (GA E a → ℂ) :=
    { toFun := fun l z => l ⟨_, hW z⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (Sm E a).subtype ≤ LinearMap.range Λ := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨(LinearMap.proj k).comp W.subtype, ?_⟩
    funext z
    rfl
  have := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective (Sm E a).subtype Subtype.val_injective _).symm

theorem level_of (φ : Sm E a) (K : Subgroup (GL (Fin a) (Af E))) (hK : IsOpen (K : Set (GL (Fin a) (Af E))))
    (h : ∀ u ∈ K, ∀ z, φ.1 (z * finGL E a u) = φ.1 z) : IsOpen {k | finRep E a k φ = φ} := by
  have hu : ∀ u ∈ K, finRep E a u φ = φ := fun u hu => Subtype.ext (funext fun z => h u hu z)
  rw [isOpen_iff_forall_mem_open]
  intro k hk
  have hk' : finRep E a k φ = φ := hk
  refine ⟨(fun u => k * u) '' (K : Set (GL (Fin a) (Af E))), ?_, isOpenMap_mul_left k _ hK, ⟨1, K.one_mem, mul_one k⟩⟩
  rintro _ ⟨u, hu', rfl⟩
  change finRep E a (k * u) φ = φ
  rw [map_mul, Module.End.mul_apply, hu u hu', hk']

def infP (A : Matrix (Fin a) (Fin a) (Ad E)) : ℝ :=
  ∑ v, Real.posLog (⨆ p : Fin a × Fin a, ‖cV v (A p.1 p.2)‖ ^ 2)

def finP (A : Matrix (Fin a) (Fin a) (Ad E)) : ℝ :=
  ∑ᶠ w, Real.posLog (⨆ p : Fin a × Fin a, ‖cW w (A p.1 p.2)‖)

theorem logSizeM_eq (A : Matrix (Fin a) (Fin a) (Ad E)) : logSizeM A = infP A + finP A := rfl

theorem logSizeM_nonneg (A : Matrix (Fin a) (Fin a) (Ad E)) : 0 ≤ logSizeM A := by
  rw [logSizeM_eq]
  exact add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem logSize_nonneg (x : GA E a) : 0 ≤ logSize x :=
  add_nonneg (logSizeM_nonneg _) (logSizeM_nonneg _)

theorem infinitePart_le (A : Matrix (Fin a) (Fin a) (Ad E)) (B : ℝ) (hB : 1 ≤ B) (h : ∀ v i j, ‖cV v (A i j)‖ ≤ B) :
    infP A ≤ Fintype.card (InfinitePlace E) * (2 * Real.log B) := by
  have key : ∀ v, Real.posLog (⨆ p : Fin a × Fin a, ‖cV v (A p.1 p.2)‖ ^ 2) ≤ 2 * Real.log B := by
    intro v
    have h0 : 0 ≤ ⨆ p : Fin a × Fin a, ‖cV v (A p.1 p.2)‖ ^ 2 := Real.iSup_nonneg fun p => sq_nonneg _
    have hle : (⨆ p : Fin a × Fin a, ‖cV v (A p.1 p.2)‖ ^ 2) ≤ B ^ 2 :=
      Real.iSup_le (fun p => pow_le_pow_left₀ (norm_nonneg _) (h v p.1 p.2) 2) (sq_nonneg _)
    have hB2 : 1 ≤ |B ^ 2| := by
      rw [abs_of_nonneg (sq_nonneg B)]
      nlinarith
    calc _ ≤ Real.posLog (B ^ 2) := Real.monotoneOn_posLog h0 (sq_nonneg B) hle
      _ = Real.log (B ^ 2) := Real.posLog_eq_log hB2
      _ = 2 * Real.log B := by rw [Real.log_pow]; norm_num
  calc infP A ≤ ∑ _v : InfinitePlace E, 2 * Real.log B := Finset.sum_le_sum fun v _ => key v
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem cV_mul (v : InfinitePlace E) (A B : Matrix (Fin a) (Fin a) (Ad E)) (i j : Fin a) :
    cV v ((A * B) i j) = ∑ k, cV v (A i k) * cV v (B k j) := by
  rw [Matrix.mul_apply, map_sum]
  simp only [map_mul]

theorem cV_infGL (v : InfinitePlace E) (y : GL (Fin a) (Cinf E)) (k j : Fin a) :
    cV v ((infGL E a y).val k j) = y.val k j v := by
  have e := congrArg (fun h : GL (Fin a) (Cinf E) => h.val k j v) (pInf_infGL (E := E) y)
  exact e

theorem pFin_mul_infGL (g : GA E a) (y : GL (Fin a) (Cinf E)) (i j : Fin a) :
    pFin E ((g * infGL E a y).val i j) = pFin E (g.val i j) := by
  have e : GeneralLinearGroup.map (pFin E) (g * infGL E a y) = GeneralLinearGroup.map (pFin E) g := by
    rw [map_mul, pFin_infGL, mul_one]
  exact congrArg (fun h : GL (Fin a) (Af E) => h.val i j) e

theorem pFin_inv_mul_infGL (g : GA E a) (y : GL (Fin a) (Cinf E)) (i j : Fin a) :
    pFin E (((g * infGL E a y)⁻¹).val i j) = pFin E ((g⁻¹).val i j) := by
  have e : GeneralLinearGroup.map (pFin E) (g * infGL E a y)⁻¹ = GeneralLinearGroup.map (pFin E) g⁻¹ := by
    rw [map_inv, map_mul, pFin_infGL, mul_one, ← map_inv]
  exact congrArg (fun h : GL (Fin a) (Af E) => h.val i j) e

theorem finP_mul_infGL (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    finP (g * infGL E a y).val = finP g.val := by
  unfold finP
  refine finsum_congr fun w => ?_
  congr 2
  funext p
  simp only [cW, RingHom.comp_apply]
  rw [pFin_mul_infGL]

theorem finP_inv_mul_infGL (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    finP ((g * infGL E a y)⁻¹).val = finP (g⁻¹).val := by
  unfold finP
  refine finsum_congr fun w => ?_
  congr 2
  funext p
  simp only [cW, RingHom.comp_apply]
  rw [pFin_inv_mul_infGL]

theorem logSize_mul_infGL (g : GA E a) : ∃ D : ℝ, ∀ y : GL (Fin a) (Cinf E),
    logSize (g * infGL E a y) ≤ D + 4 * Fintype.card (InfinitePlace E) * Real.log (height y) := by
  let M : InfinitePlace E → Fin a → Fin a → ℝ := fun v i k => ‖cV v (g.val i k)‖ + ‖cV v ((g⁻¹).val i k)‖
  have hM0 : ∀ v i k, 0 ≤ M v i k := fun v i k => add_nonneg (norm_nonneg _) (norm_nonneg _)
  let T : ℝ := ∑ v, ∑ i, ∑ k, M v i k
  have hT0 : 0 ≤ T :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hM0 v i k
  have hrow0 : ∀ v, ∑ i, ∑ k, M v i k ≤ T := fun v =>
    Finset.single_le_sum (f := fun v => ∑ i, ∑ k, M v i k)
      (fun v _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hM0 v i k) (Finset.mem_univ v)
  have hrow : ∀ v i, ∑ k, M v i k ≤ T := fun v i =>
    (Finset.single_le_sum (f := fun i => ∑ k, M v i k) (fun i _ => Finset.sum_nonneg fun k _ => hM0 v i k)
      (Finset.mem_univ i)).trans (hrow0 v)
  have hcol : ∀ v j, ∑ k, M v k j ≤ T := fun v j =>
    (Finset.sum_le_sum fun k _ => Finset.single_le_sum (f := fun j => M v k j) (fun j _ => hM0 v k j)
      (Finset.mem_univ j)).trans (hrow0 v)
  refine ⟨finP g.val + finP (g⁻¹).val + 4 * Fintype.card (InfinitePlace E) * Real.log (1 + T), fun y => ?_⟩
  have h1 : 1 ≤ height y := one_le_height y
  have hB : 1 ≤ (1 + T) * height y := one_le_mul_of_one_le_of_one_le (by linarith) h1
  have hlogB : Real.log ((1 + T) * height y) = Real.log (1 + T) + Real.log (height y) :=
    Real.log_mul (by linarith) (by linarith)
  have e1 : ∀ v i j, ‖cV v ((g * infGL E a y).val i j)‖ ≤ (1 + T) * height y := by
    intro v i j
    rw [Units.val_mul, cV_mul]
    calc ‖∑ k, cV v (g.val i k) * cV v ((infGL E a y).val k j)‖
        ≤ ∑ k, ‖cV v (g.val i k)‖ * ‖cV v ((infGL E a y).val k j)‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
      _ ≤ ∑ k, M v i k * height y := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul (le_add_of_nonneg_right (norm_nonneg _)) ?_
            (norm_nonneg _) (hM0 v i k)
          rw [cV_infGL]
          exact (GlobalTheory.CompanionTheory.GrowthEntries.norm_entry_le_toL _ k j v).trans
            (GlobalTheory.CompanionTheory.GrowthEntries.norm_toL_le_height y)
      _ = (∑ k, M v i k) * height y := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + T) * height y := mul_le_mul_of_nonneg_right (by linarith [hrow v i]) (by linarith)
  have hinv : (g * infGL E a y)⁻¹ = infGL E a y⁻¹ * g⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
  have e2 : ∀ v i j, ‖cV v (((g * infGL E a y)⁻¹).val i j)‖ ≤ (1 + T) * height y := by
    intro v i j
    rw [hinv, Units.val_mul, cV_mul]
    calc ‖∑ k, cV v ((infGL E a y⁻¹).val i k) * cV v ((g⁻¹).val k j)‖
        ≤ ∑ k, ‖cV v ((infGL E a y⁻¹).val i k)‖ * ‖cV v ((g⁻¹).val k j)‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
      _ ≤ ∑ k, height y * M v k j := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul ?_ (le_add_of_nonneg_left (norm_nonneg _))
            (norm_nonneg _) (by linarith)
          rw [cV_infGL]
          exact (GlobalTheory.CompanionTheory.GrowthEntries.norm_entry_le_toL _ i k v).trans
            (GlobalTheory.CompanionTheory.GrowthEntries.norm_toL_inv_le_height y)
      _ = height y * ∑ k, M v k j := (Finset.mul_sum _ _ _).symm
      _ ≤ (1 + T) * height y := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (by linarith [hcol v j]) (by linarith)
  have i1 := infinitePart_le _ _ hB e1
  have i2 := infinitePart_le _ _ hB e2
  have f1 := finP_mul_infGL g y
  have f2 := finP_inv_mul_infGL g y
  have hs : logSize (g * infGL E a y) = infP (g * infGL E a y).val + finP (g * infGL E a y).val +
      (infP ((g * infGL E a y)⁻¹).val + finP ((g * infGL E a y)⁻¹).val) := rfl
  rw [hs, f1, f2]
  rw [hlogB] at i1 i2
  nlinarith

theorem growth_of_bound (F : GA E a → ℂ) (C N L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (N * (logSize x + L))) (z : GA E a) :
    ∃ (C' : ℝ) (M : ℕ), ∀ y : GL (Fin a) (Cinf E), ‖F (z * infGL E a y)‖ ≤ C' * height y ^ M := by
  obtain ⟨D, hD⟩ := logSize_mul_infGL z
  set P : ℝ := 4 * Fintype.card (InfinitePlace E)
  refine ⟨max C 0 * Real.exp (max N 0 * (D + L)), ⌈max N 0 * P⌉₊, fun y => ?_⟩
  have h1 : 1 ≤ height y := one_le_height y
  have hs0 : 0 ≤ logSize (z * infGL E a y) + L := add_nonneg (logSize_nonneg _) hL
  have hs : logSize (z * infGL E a y) + L ≤ D + L + P * Real.log (height y) := by linarith [hD y]
  have he : Real.exp (max N 0 * (D + L + P * Real.log (height y))) =
      Real.exp (max N 0 * (D + L)) * height y ^ (max N 0 * P) := by
    rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
    congr 1
    ring
  have hr : height y ^ (max N 0 * P) ≤ height y ^ ⌈max N 0 * P⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
  calc ‖F (z * infGL E a y)‖ ≤ C * Real.exp (N * (logSize (z * infGL E a y) + L)) := hF _
    _ ≤ max C 0 * Real.exp (max N 0 * (D + L + P * Real.log (height y))) := by
        refine mul_le_mul (le_max_left _ _) ?_ (Real.exp_pos _).le (le_max_right _ _)
        refine Real.exp_le_exp.2 ?_
        calc N * (logSize (z * infGL E a y) + L) ≤ max N 0 * (logSize (z * infGL E a y) + L) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
          _ ≤ _ := mul_le_mul_of_nonneg_left hs (le_max_right _ _)
    _ = max C 0 * (Real.exp (max N 0 * (D + L)) * height y ^ (max N 0 * P)) := by rw [he]
    _ ≤ max C 0 * (Real.exp (max N 0 * (D + L)) * height y ^ ⌈max N 0 * P⌉₊) := by
        gcongr
    _ = _ := by ring

end Tc

section Cm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem card_mOf (χ : InfinitePlace E → Inf a) (τ : E →+* ℂ) : Multiset.card (mOf χ τ) = a := by
  unfold mOf
  simp

theorem hasInf_single (hB : BridgeSt) (χ : InfinitePlace E → Inf a) (φ : Sm E a)
    (hφ : ∀ v g, IsEig (χ v) (along v g φ.1)) (τ : E →+* ℂ) :
    HasInfCharGL (Submodule.span ℂ {φ}) τ (mOf χ τ) := by
  classical
  have key := (hB E a (Submodule.span ℂ {φ}) (InfinitePlace.mk τ) (χ (InfinitePlace.mk τ))).1 (by
    intro ψ hψ g
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hψ
    have e : ((c • φ : Sm E a) : GA E a → ℂ) = c • (φ : GA E a → ℂ) := rfl
    rw [e, along_smul']
    exact isEig_smul (hφ _ g) c)
  by_cases h : τ = (InfinitePlace.mk τ).embedding
  · have e : mOf χ τ = Multiset.map (χ (InfinitePlace.mk τ) true) Finset.univ.val := by
      have hd : decide (τ = (InfinitePlace.mk τ).embedding) = true := decide_eq_true h
      unfold mOf
      rw [hd]
    rw [e]
    have k1 := key.1
    rwa [← h] at k1
  · have h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ :=
      (InfinitePlace.embedding_mk_eq τ).resolve_left fun e' => h e'.symm
    have h3 : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h2]
      exact star_star τ
    have e : mOf χ τ = Multiset.map (χ (InfinitePlace.mk τ) false) Finset.univ.val := by
      have hd : decide (τ = (InfinitePlace.mk τ).embedding) = false := decide_eq_false h
      unfold mOf
      rw [hd]
    rw [e]
    have k2 := key.2
    rwa [h3] at k2

theorem hasInf_span (S : Set (Sm E a)) (τ : E →+* ℂ) (m : Multiset ℂ) (hm : Multiset.card m = a)
    (h : ∀ φ ∈ S, HasInfCharGL (Submodule.span ℂ {φ}) τ m) : HasInfCharGL (Submodule.span ℂ S) τ m := by
  refine ⟨hm, fun u ψ hψ => ?_⟩
  induction hψ using Submodule.span_induction with
  | mem x hx => exact (h x hx).2 u x (Submodule.mem_span_singleton_self x)
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

theorem isAutForm_of (hB : BridgeSt) (φ : Sm E a) (K : Subgroup (GL (Fin a) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin a) (Af E)))) (W : Submodule ℂ (Kinf E a → ℂ)) [FiniteDimensional ℂ W]
    (χ : InfinitePlace E → Inf a) (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hk : ∀ u ∈ K, ∀ z, φ.1 (z * finGL E a u) = φ.1 z)
    (hw : ∀ z, (fun k : Kinf E a => φ.1 (z * infGL E a (Unitary.toUnits k))) ∈ W)
    (he : ∀ v g, IsEig (χ v) (along v g φ.1))
    (hg : ∀ z, ∃ (C : ℝ) (M : ℕ), ∀ y, ‖φ.1 (z * infGL E a y)‖ ≤ C * height y ^ M) : IsAutForm φ :=
  ⟨hl, level_of φ K hK hk, kfin_of φ W hw,
    zfin_of φ _ fun τ u => (hasInf_single hB χ φ he τ).2 u φ (Submodule.mem_span_singleton_self φ), hg⟩

theorem typeW₁ {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (z : GA E a) (m₂ : GA E b) :
    (fun k : Kinf E a => F (z * infGL E a (Unitary.toUnits k), m₂)) ∈ W₁ := by
  let ev : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun k : Kinf E a => (k, (1 : Kinf E b)))
  have hle : (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}).map
      ev ≤ W₁ := by
    rw [Submodule.map_span_le]
    rintro _ ⟨w₁, hw₁, w₂, -, rfl⟩
    have e : ev (fun k => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
      funext k
      simp [ev, LinearMap.funLeft_apply, mul_comm]
    rw [e]
    exact W₁.smul_mem _ hw₁
  have := hle (Submodule.mem_map_of_mem (f := ev) (hF.2 (z, m₂)))
  convert this using 1
  funext k
  simp [ev, LinearMap.funLeft_apply]

theorem typeW₂ {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : TypeH K₁ K₂ W₁ W₂ F) (m₁ : GA E a) (z : GA E b) :
    (fun k : Kinf E b => F (m₁, z * infGL E b (Unitary.toUnits k))) ∈ W₂ := by
  let ev : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun k : Kinf E b => ((1 : Kinf E a), k))
  have hle : (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}).map
      ev ≤ W₂ := by
    rw [Submodule.map_span_le]
    rintro _ ⟨w₁, -, w₂, hw₂, rfl⟩
    have e : ev (fun k => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
      funext k
      simp [ev, LinearMap.funLeft_apply]
    rw [e]
    exact W₂.smul_mem _ hw₂
  have := hle (Submodule.mem_map_of_mem (f := ev) (hF.2 (m₁, z)))
  convert this using 1
  funext k
  simp [ev, LinearMap.funLeft_apply]

theorem slice₁_aut (hB : BridgeSt) {ι : Type} {f : ι → H E a b → ℂ}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {χa : InfinitePlace E → Inf a}
    {χb : InfinitePlace E → Inf b} {C N : ℝ} (hK₁ : IsOpen (K₁ : Set (GL (Fin a) (Af E))))
    (hW₁ : FiniteDimensional ℂ W₁) (hL : LeftInv f) (hT : ∀ i, TypeH K₁ K₂ W₁ W₂ (f i))
    (hG : ∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))) (hE : EigAll χa χb f)
    (φ : Sm E a) (i : ι) (m₂ : GA E b) (hφ : φ.1 = fun x => f i (x, m₂)) : IsAutForm φ := by
  refine isAutForm_of hB φ K₁ hK₁ W₁ χa ?_ ?_ ?_ ?_ ?_
  · intro γ g
    rw [hφ]
    have := hL i ⟨(ratGL E a γ, ratGL E b 1), ⟨(γ, 1), rfl⟩⟩ (g, m₂)
    simpa using this
  · intro u hu z
    rw [hφ]
    have := (hT i).1 u hu 1 (Subgroup.one_mem _) (z, m₂)
    simpa using this
  · intro z
    rw [hφ]
    exact typeW₁ (hT i) z m₂
  · intro v g
    rw [hφ]
    exact hE.1 i v g m₂
  · intro z
    refine growth_of_bound φ.1 C N (logSize m₂) (logSize_nonneg m₂) (fun x => ?_) z
    rw [hφ]
    exact hG i (x, m₂)

theorem slice₂_aut (hB : BridgeSt) {ι : Type} {f : ι → H E a b → ℂ}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {χa : InfinitePlace E → Inf a}
    {χb : InfinitePlace E → Inf b} {C N : ℝ} (hK₂ : IsOpen (K₂ : Set (GL (Fin b) (Af E))))
    (hW₂ : FiniteDimensional ℂ W₂) (hL : LeftInv f) (hT : ∀ i, TypeH K₁ K₂ W₁ W₂ (f i))
    (hG : ∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))) (hE : EigAll χa χb f)
    (φ : Sm E b) (i : ι) (m₁ : GA E a) (hφ : φ.1 = fun x => f i (m₁, x)) : IsAutForm φ := by
  refine isAutForm_of hB φ K₂ hK₂ W₂ χb ?_ ?_ ?_ ?_ ?_
  · intro γ g
    rw [hφ]
    have := hL i ⟨(ratGL E a 1, ratGL E b γ), ⟨(1, γ), rfl⟩⟩ (m₁, g)
    simpa using this
  · intro u hu z
    rw [hφ]
    have := (hT i).1 1 (Subgroup.one_mem _) u hu (m₁, z)
    simpa using this
  · intro z
    rw [hφ]
    exact typeW₂ (hT i) m₁ z
  · intro v g
    rw [hφ]
    exact hE.2 i v g m₁
  · intro z
    refine growth_of_bound φ.1 C N (logSize m₁) (logSize_nonneg m₁) (fun x => ?_) z
    rw [hφ, add_comm (logSize x)]
    exact hG i (m₁, x)

end Cm

theorem autOf (hB : BridgeSt) : AutOf := by
  intro E _ _ _ a b ι f K₁ K₂ W₁ W₂ χa χb C N hK₁ hK₂ hW₁ hW₂ hL hT hG hE
  refine ⟨?_, ?_, fun τ => ?_, fun τ => ?_⟩
  · rintro φ ⟨i, m₂, hφ⟩
    exact slice₁_aut hB hK₁ hW₁ hL hT hG hE φ i m₂ hφ
  · rintro φ ⟨i, m₁, hφ⟩
    exact slice₂_aut hB hK₂ hW₂ hL hT hG hE φ i m₁ hφ
  · refine hasInf_span _ τ _ (card_mOf χa τ) fun φ hφ => ?_
    obtain ⟨i, m₂, hφ⟩ := hφ
    exact hasInf_single hB χa φ (fun v g => by rw [hφ]; exact hE.1 i v g m₂) τ
  · refine hasInf_span _ τ _ (card_mOf χb τ) fun φ hφ => ?_
    obtain ⟨i, m₁, hφ⟩ := hφ
    exact hasInf_single hB χb φ (fun v g => by rw [hφ]; exact hE.2 i v g m₁) τ

end PositivityTheory.Rg.BcB.CG.PAut

end
