import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbDefs

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

theorem perm_of_map_eq {n : ℕ} (f g : Fin n → ℂ)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ σ : Equiv.Perm (Fin n), ∀ a, g (σ a) = f a := by
  have hc : ∀ c : ℂ, Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    intro c
    have h1 := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have e1 : (Finset.univ.filter fun a => f a = c) = (Finset.univ.filter fun a => c = f a) := by
      ext a; simp [eq_comm]
    have e2 : (Finset.univ.filter fun a => g a = c) = (Finset.univ.filter fun a => c = g a) := by
      ext a; simp [eq_comm]
    rw [e1, e2]
    exact_mod_cast h1
  let e : ∀ c, {a // f a = c} ≃ {b // g b = c} := fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv e, fun a => ?_⟩
  exact Equiv.ofFiberEquiv_map e a

theorem herm_of_realSym {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (χ : InfinitePlace E → Inf n)
    (h : RealSym (mOf χ)) (v : InfinitePlace E) : IsHerm (χ v) := by
  set τ := v.embedding with hτ
  obtain ⟨hre, hsym⟩ := h τ
  have hv : InfinitePlace.mk τ = v := InfinitePlace.mk_embedding v
  have hcv : InfinitePlace.mk ((starRingEnd ℂ).comp τ) = v := by
    have := InfinitePlace.mk_conjugate_eq τ
    rw [← hv]; exact this
  have hne : ((starRingEnd ℂ).comp τ) ≠ v.embedding := by
    intro e
    have hr : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      exact e
    exact (IsTotallyComplex.complexEmbedding_not_isReal τ) hr
  have m1 : mOf χ τ = Multiset.map (χ v true) Finset.univ.val := by
    unfold mOf
    rw [hv]
    simp [hτ]
  have m2 : mOf χ ((starRingEnd ℂ).comp τ) = Multiset.map (χ v false) Finset.univ.val := by
    unfold mOf
    rw [hcv]
    simp [hne]
  rw [m1, m2, Multiset.map_map] at hsym
  obtain ⟨σ, hσ⟩ := perm_of_map_eq _ _ hsym.symm
  refine ⟨σ, fun a => ?_⟩
  rw [hσ a]
  have ha : (χ v true a).im = 0 := by
    rw [m1] at hre
    exact hre _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val a))
  have hc : starRingEnd ℂ (χ v true a) = χ v true a := Complex.conj_eq_iff_im.2 ha
  simp [hc]

theorem smul_cancel {ι X : Type} {f : ι → X → ℂ} (hf : f ≠ 0) {c d : ℂ} (h : c • f = d • f) : c = d :=
  smul_left_injective ℂ hf h

theorem conv_smul {a b : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {ι : Type} [Fintype ι]
    (μ : Measure (H E a b)) (Φ : Matrix ι ι (H E a b → ℂ)) (c : ℂ) (f : ι → H E a b → ℂ) :
    PositivityTheory.Rg.BcB.E.conv μ Φ (c • f) = c • PositivityTheory.Rg.BcB.E.conv μ Φ f := by
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  congr 1; funext y; ring

theorem mclose_of (hIC : InfConv) {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (χk : ℕ → InfinitePlace E → Inf n) (χ₀ : InfinitePlace E → Inf n)
    (h : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χk k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χ₀ v s) m)))
    (τ : E →+* ℂ) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop, MClose ε (mOf (χk k) τ) (mOf χ₀ τ) := by
  unfold MClose mOf
  exact hIC n _ _ (h _ _) ε hε

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isKer_smul_rank {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (g : ℝ → ℝ)
    (k : Mat n → (M.V →L[ℂ] M.V)) (s : Bool) (hk : IsKer μ M [] g k) : IsKer μ M [(s, 0)] g ((n : ℂ) • k) := by
  obtain ⟨h1, ⟨R, hR⟩, h3, h4⟩ := hk
  refine ⟨h1.const_smul (n : ℂ), ⟨R, fun y hy hl => by simp [hR y hy hl]⟩, fun y hy k₁ k₂ => ?_, fun u hu x hx => ?_⟩
  · simp only [Pi.smul_apply, h3 y hy k₁ k₂, smul_mul_assoc, mul_smul_comm]
  · have e := h4 u hu x hx
    simp only [PositivityTheory.RgBcC.act, Pi.smul_apply, _root_.smul_apply] at e ⊢
    rw [integral_smul, e]
    simp only [zOp, gel, Epow, id, if_true, Finset.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_smul_eq_nsmul]

theorem isKer_zero_rank {n : ℕ} (hn : n = 0) [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (g : ℝ → ℝ)
    (s : Bool) (m : ℕ) : IsKer μ M [(s, m)] g 0 := by
  subst hn
  refine ⟨contDiffOn_const, ⟨0, fun _ _ _ => rfl⟩, fun y _ k₁ k₂ => by simp, fun u _ x _ => ?_⟩
  simp [PositivityTheory.RgBcC.act, zOp, gel]

theorem ent_smul {n : ℕ} (M : KMod n) (c : ℂ) (A : M.V →L[ℂ] M.V) (i j : Ix M) : ent M (c • A) i j = c * ent M A i j := by
  simp [ent, inner_smul_right]

theorem tens_update_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Ma : Mods E a} {Mb : Mods E b}
    {κ : Type} (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (v : InfinitePlace E) (c : ℂ) :
    tens (Function.update ka v (c • ka v)) kb ψ = c • tens ka kb ψ := by
  funext i j y
  simp only [tens, entA, Pi.smul_apply, smul_eq_mul]
  have e : ∀ w, ent (Ma w) (Function.update ka v (c • ka v) w (gInf w y.1).val) (i.1.1 w) (j.1.1 w) =
      (if w = v then c else 1) * ent (Ma w) (ka w (gInf w y.1).val) (i.1.1 w) (j.1.1 w) := by
    intro w
    by_cases h : w = v
    · subst h; simp [ent_smul]
    · simp [Function.update_of_ne h, h]
  simp only [e, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, tens, entA]
  ring

theorem tens_update_smul_b {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Ma : Mods E a}
    {Mb : Mods E b} {κ : Type} (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (v : InfinitePlace E)
    (c : ℂ) : tens ka (Function.update kb v (c • kb v)) ψ = c • tens ka kb ψ := by
  funext i j y
  simp only [tens, entA, Pi.smul_apply, smul_eq_mul]
  have e : ∀ w, ent (Mb w) (Function.update kb v (c • kb v) w (gInf w y.2).val) (i.1.2 w) (j.1.2 w) =
      (if w = v then c else 1) * ent (Mb w) (kb w (gInf w y.2).val) (i.1.2 w) (j.1.2 w) := by
    intro w
    by_cases h : w = v
    · subst h; simp [ent_smul]
    · simp [Function.update_of_ne h, h]
  simp only [e, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, tens, entA]
  ring

theorem tens_update_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Ma : Mods E a} {Mb : Mods E b}
    {κ : Type} (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (v : InfinitePlace E) :
    tens (Function.update ka v 0) kb ψ = 0 := by
  funext i j y
  simp only [tens, entA, Matrix.zero_apply, Pi.zero_apply]
  rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [ent_zero])]
  ring

theorem tens_update_zero_b {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Ma : Mods E a}
    {Mb : Mods E b} {κ : Type} (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (v : InfinitePlace E) :
    tens ka (Function.update kb v 0) ψ = 0 := by
  funext i j y
  simp only [tens, entA, Matrix.zero_apply, Pi.zero_apply]
  rw [Finset.prod_eq_zero (f := fun w => ent (Mb w) (Function.update kb v 0 w (gInf w y.2).val) (i.1.2 w) (j.1.2 w))
    (Finset.mem_univ v) (by simp [ent_zero])]
  ring

theorem conv_smulM {a b : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {ι : Type} [Fintype ι]
    (μ : Measure (H E a b)) (Φ : Matrix ι ι (H E a b → ℂ)) (c : ℂ) (f : ι → H E a b → ℂ) :
    PositivityTheory.Rg.BcB.E.conv μ (c • Φ) f = c • PositivityTheory.Rg.BcB.E.conv μ Φ f := by
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  congr 1; funext y; ring

theorem conv_zeroM {a b : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {ι : Type} [Fintype ι]
    (μ : Measure (H E a b)) (f : ι → H E a b → ℂ) :
    PositivityTheory.Rg.BcB.E.conv μ (0 : Matrix ι ι (H E a b → ℂ)) f = 0 := by
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, Matrix.zero_apply, Pi.zero_apply, zero_mul, integral_zero, Finset.sum_const_zero]

theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop}
    (hPQ : ∀ M V, P M V → Q M V) : ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → t.AllLeaves Q
  | _, .leaf V _, h => hPQ _ V h
  | _, .node t₁ t₂, h => ⟨allLeaves_mono hPQ t₁ h.1, allLeaves_mono hPQ t₂ h.2⟩

theorem typeH_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {K₁ : Subgroup (GL (Fin a) (Af E))}
    {K₂ : Subgroup (GL (Fin b) (Af E))} {W₁ W₁' : Submodule ℂ (Kinf E a → ℂ)} {W₂ W₂' : Submodule ℂ (Kinf E b → ℂ)}
    (h₁ : W₁ ≤ W₁') (h₂ : W₂ ≤ W₂') {F : H E a b → ℂ} (hF : TypeH K₁ K₂ W₁ W₂ F) : TypeH K₁ K₂ W₁' W₂' F := by
  refine ⟨hF.1, fun x => Submodule.span_mono ?_ (hF.2 x)⟩
  rintro f ⟨w₁, hw₁, w₂, hw₂, rfl⟩
  exact ⟨w₁, h₁ hw₁, w₂, h₂ hw₂, rfl⟩

def PackAt (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b)
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) : Prop :=
  ∀ (D : Dom E a b) [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
    [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
    (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure] (κ : Type) [Fintype κ]
    (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (g : ℝ → ℝ)
    (ka' : Bool → ℕ → Kers Ma) (kb' : Bool → ℕ → Kers Mb) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (M : ℕ) (f : Io Ma Mb κ → H E a b → ℂ) (c : ℂ)
    (ca cb : InfinitePlace E → Bool → ℕ → ℂ), Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
    IsBump g T → (∀ v, IsKer μa (Ma v) [] g (ka v)) → (∀ v, IsKer μb (Mb v) [] g (kb v)) →
    (∀ s m v, IsKer μa (Ma v) [(s, m)] g (ka' s m v)) → (∀ s m v, IsKer μb (Mb v) [(s, m)] g (kb' s m v)) →
    IsOpen (K₁ : Set (GL (Fin a) (Af E))) → IsOpen (K₂ : Set (GL (Fin b) (Af E))) →
    (∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, ψ x y ((u₁, u₂) * h) = ψ x y h) →
    (∀ i, Continuous (f i)) → f ≠ 0 → LeftInv f → WL2 D M f → c ≠ 0 →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update ka v (ka' s m v)) kb ψ) f = ca v s m • f) →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens ka (Function.update kb v (kb' s m v)) ψ) f = cb v s m • f) →
    ∃ (χa : InfinitePlace E → Inf a) (χb : InfinitePlace E → Inf b),
      (∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m = ca v s m / c) ∧ (∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m = cb v s m / c) ∧
      EigAll χa χb f ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) ∧
      (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ (∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) ∧
      (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
      ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ)

def EFinalAt (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
    (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ (D : Dom E a b) (ι : Type) [Fintype ι] (M : ℕ)
  (m₁ : ℕ → (E →+* ℂ) → Multiset ℂ) (m₂ : ℕ → (E →+* ℂ) → Multiset ℂ) (n₁ n₂ : (E →+* ℂ) → Multiset ℂ)
  (C : Set (HeckeM E a b ι)) (lam : ℕ → HeckeM E a b ι → ℂ) (lam₀ : HeckeM E a b ι → ℂ)
  (f : ℕ → ι → H E a b → ℂ), C.Countable →

  (∀ (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin N) (Af E))) (W' : Submodule ℂ (Kinf E N → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R') →

  (∀ k i, Continuous (f k i)) → (∀ k, f k ≠ 0) → (∀ k, LeftInv (f k)) → (∀ k, WL2 D M (f k)) →
  (∀ k i, TypeH K₁ K₂ W₁ W₂ (f k i)) →
  (∀ k i (m₂ : GA E b), ∃ φ : Sm E a, φ.1 = fun x => f k i (x, m₂)) →
  (∀ k i (m₁ : GA E a), ∃ φ : Sm E b, φ.1 = fun x => f k i (m₁, x)) →
  (∀ k, ∀ φ ∈ slices₁ (f k), IsAutForm φ) → (∀ k, ∀ φ ∈ slices₂ (f k), IsAutForm φ) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₁ (f k))) τ (m₁ k τ)) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₂ (f k))) τ (m₂ k τ)) →
  (∀ k, ∀ h ∈ C, heckeAct h (f k) = lam k h • f k) →

  (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, MClose ε (m₁ k τ) (n₁ τ) ∧ MClose ε (m₂ k τ) (n₂ τ)) →
  RealSym n₁ → RealSym n₂ → (∀ τ, GapM (n₁ τ) ∧ GapM (n₂ τ)) →
  (∀ h ∈ C, Tendsto (fun k => lam k h) atTop (𝓝 (lam₀ h))) →
  ∃ (s₁ : Tr E a) (s₂ : Tr E b) (F : ι → H E a b → ℂ), s₁.Good ∧ s₂.Good ∧ s₁.Untw ∧ s₂.Untw ∧
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₁ M, ∃ W' ∈ Ω₁ M, HasType K' W' V) ∧
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₂ M, ∃ W' ∈ Ω₂ M, HasType K' W' V) ∧
    (∀ τ, HasInfCharGL s₁.space τ (n₁ τ)) ∧ (∀ τ, HasInfCharGL s₂.space τ (n₂ τ)) ∧
    F ≠ 0 ∧ (∀ i, F i ∈ pairSpace s₁.space s₂.space) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (F i)) ∧
    ∀ h ∈ C, heckeAct h F = lam₀ h • F

def PerKOut {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E) (W₁ : Submodule ℂ (Kinf E B.a → ℂ))
    (W₂ : Submodule ℂ (Kinf E B.b → ℂ)) (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    {Γ : Type} (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (der : InfinitePlace E → Bool → ℕ → Γ × Γ)
    (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (jX : ℕ) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ) : Prop :=
  ∃ (M : ℕ) (sk : ℕ → ChAlg g X → ℂ) (f : ℕ → B.I → H E B.a B.b → ℂ) (χak : ℕ → InfinitePlace E → Inf B.a)
    (χbk : ℕ → InfinitePlace E → Inf B.b),
    (∀ y, Tendsto (fun k => sk k (genE g X y)) atTop (𝓝 (χ (genE g X y)))) ∧
    Tendsto (fun k => sk k (XE g X)) atTop (𝓝 (χ (XE g X))) ∧
    (∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop
      (𝓝 (if 1 ≤ m ∧ 0 < B.a then χ (genE g X (der v s m).1) / χ (genE g X a₀) else if m = 0 then (B.a : ℂ) else 0))) ∧
    (∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop
      (𝓝 (if 1 ≤ m ∧ 0 < B.b then χ (genE g X (der v s m).2) / χ (genE g X a₀) else if m = 0 then (B.b : ℂ) else 0))) ∧
    ∀ k, sk k (genE g X a₀) ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 B.D M (f k) ∧
      (∀ i, TypeH K₁ K₂ W₁ W₂ (f k i)) ∧
      (∀ i (m₂ : GA E B.b), ∃ φ : Sm E B.a, φ.1 = fun x => f k i (x, m₂)) ∧
      (∀ i (m₁ : GA E B.a), ∃ φ : Sm E B.b, φ.1 = fun x => f k i (m₁, x)) ∧
      (∀ φ ∈ slices₁ (f k), IsAutForm φ) ∧ (∀ φ ∈ slices₂ (f k), IsAutForm φ) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ (f k))) τ (mOf (χak k) τ)) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ (f k))) τ (mOf (χbk k) τ)) ∧
      (∀ y (t : PT B), g y = Sum.inr t → FinType t₀ t →
        convF B.ν t.ψ (f k) = (sk k (genE g X y) / sk k (genE g X a₀)) • f k) ∧
      convF B.ν tX.ψ (f k) = (sk k (XE g X) / sk k (genE g X a₀) ^ jX) • f k ∧
      (∀ y (t : PT B), g y = Sum.inr t → ArchType t₀ t → t.val (χak k) (χbk k) = sk k (genE g X y))

end PositivityTheory.Rg.BcB.F.Rd.B

end
