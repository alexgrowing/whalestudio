import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GL2CharacterZeros
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitDict

section Partial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}

theorem bijOn_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Set.BijOn (fun f : Y → ℂ => f ∘ e) {f | f ∈ SB Y} {f | f ∈ SB X} := by
  refine ⟨fun f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩,
    fun f _ g _ hfg => ?_, fun g hg => ⟨g ∘ e.symm, ⟨hg.1.comp_continuous e.symm.continuous,
      hg.2.comp_homeomorph e.symm⟩, ?_⟩⟩
  · funext y
    simpa using congrFun hfg (e.symm y)
  · funext x
    simp

omit [DecidableEq n] [T2Space T] in

theorem exists_box_invariant_snd {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) :
    ∃ s : kˣ, ∀ u ∈ box n s, ∀ z : T × (n → k), f (z.1, z.2 + u) = f z := by
  obtain ⟨hlc, hcs⟩ := hf
  have hlc2 : IsLocallyConstant fun p : (T × (n → k)) × (n → k) => f (p.1.1, p.1.2 + p.2) - f p.1 :=
    (hlc.comp_continuous (by fun_prop)).sub (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
    hlc2.isOpen_fiber 0
  obtain ⟨U, V, -, hV, hKU, h0V, hUV⟩ := generalized_tube_lemma hcs.isCompact (isCompact_singleton (x := (0 : n → k))) hW (by
    rintro ⟨z, u⟩ ⟨-, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    simp [hu])
  obtain ⟨s, hs⟩ := exists_box_subset (hV.mem_nhds (h0V rfl))
  have key : ∀ z ∈ tsupport f, ∀ u ∈ box n s, f (z.1, z.2 + u) = f z := by
    intro z hz u hu
    have hm : (z, u) ∈ {p : (T × (n → k)) × (n → k) | f (p.1.1, p.1.2 + p.2) - f p.1 = 0} :=
      hUV ⟨hKU hz, hs hu⟩
    exact sub_eq_zero.mp hm
  refine ⟨s, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact key z hz u hu
  · by_cases hz' : (z.1, z.2 + u) ∈ tsupport f
    · have hneg : -u ∈ box n s := fun i _ => neg_mem_cball (hu i (Set.mem_univ i))
      have := key _ hz' (-u) hneg
      simp only [add_neg_cancel_right, Prod.mk.eta] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

omit [DecidableEq n] [T2Space T] [Fintype n] in
theorem slice_mem_SB {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t : T) :
    (fun x => f (t, x)) ∈ SB (n → k) := by
  haveI := t2Space k
  refine ⟨hf.1.comp_continuous (by fun_prop),
    HasCompactSupport.intro (hf.2.isCompact.image continuous_snd) fun x hx => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩

variable [MeasurableSpace k] [BorelSpace k]

def pf (ψ : AddChar k Circle) (μ : Measure (n → k)) (f : T × (n → k) → ℂ) : T × (n → k) → ℂ :=
  fun z => ∫ x, f (z.1, x) * (ψ (x ⬝ᵥ z.2) : ℂ) ∂μ

private theorem exists_isOpen_nhd_eq_of_mem_SB {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t₀ : T) :
    ∃ V : Set T, IsOpen V ∧ t₀ ∈ V ∧ ∀ t ∈ V, ∀ x, f (t, x) = f (t₀, x) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hW : IsOpen {p : T × (n → k) | f p - f (t₀, p.2) = 0} :=
    (hlc.sub (hlc.comp_continuous (by fun_prop))).isOpen_fiber 0
  obtain ⟨U, V, hU, -, ht₀U, hLV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := t₀))
    (hcs.isCompact.image continuous_snd) hW (by
      rintro ⟨t, x⟩ ⟨ht, -⟩
      simp only [Set.mem_singleton_iff] at ht
      simp [ht])
  refine ⟨U, hU, ht₀U rfl, fun t ht x => ?_⟩
  by_cases hx : x ∈ Prod.snd '' tsupport f
  · have hm : (t, x) ∈ {p : T × (n → k) | f p - f (t₀, p.2) = 0} := hUV ⟨ht, hLV hx⟩
    exact sub_eq_zero.mp hm
  · have h1 : (t, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    have h2 : (t₀, x) ∉ tsupport f := fun h => hx ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem pf_mem_SB (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) : pf ψ μ f ∈ SB (T × (n → k)) := by
  obtain ⟨s, hs⟩ := exists_box_invariant_snd hf
  have hslice : ∀ t, (fun y => ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) :=
    fun t => fourier_mem_SB μ h (slice_mem_SB hf t)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    rintro ⟨t₀, y₀⟩
    obtain ⟨V, hV, ht₀, hVf⟩ := exists_isOpen_nhd_eq_of_mem_SB hf t₀
    obtain ⟨O, hO, hy₀, hOf⟩ := (IsLocallyConstant.iff_exists_open _).mp (hslice t₀).1 y₀
    refine ⟨V ×ˢ O, hV.prod hO, ⟨ht₀, hy₀⟩, ?_⟩
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have e1 : pf ψ μ f (t, y) = pf ψ μ f (t₀, y) := by
      simp only [pf]
      congr 1
      funext x
      rw [hVf t ht x]
    rw [e1]
    exact hOf y hy
  · haveI := t2Space k
    refine HasCompactSupport.intro
      ((hf.2.isCompact.image continuous_fst).prod (isCompact_box (c * s⁻¹))) ?_
    rintro ⟨t, y⟩ hty
    rw [Set.mem_prod, not_and_or] at hty
    rcases hty with ht | hy
    · have h0 : ∀ x, f (t, x) = 0 := fun x =>
        image_eq_zero_of_notMem_tsupport fun hx => ht ⟨_, hx, rfl⟩
      simp [pf, h0]
    · show ∫ x, f (t, x) * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0
      exact fourier_eq_zero_pi μ h (f := fun x => f (t, x)) (fun u hu x => hs u hu (t, x)) hy

theorem inversion_const (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => m)) ∂(Measure.pi fun _ => m) =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  obtain ⟨s, hs⟩ := fourier_inversion_pi (Measure.pi fun _ : n => m) h hf
  have hbox : ∀ r : kˣ, (Measure.pi fun _ : n => m).real (box n r) =
      (nabs k r * m.real (𝒪[k] : Set k)) ^ Fintype.card n := by
    intro r
    have hc := measureReal_cball m r
    simp only [Measure.real] at hc ⊢
    rw [box, Measure.pi_pi, ENNReal.toReal_prod, hc, Finset.prod_const, Finset.card_univ]
  have h1 : nabs k s * nabs k (c * s⁻¹) = nabs k c := by
    rw [nabs_mul k, mul_left_comm, ← nabs_mul k, mul_inv_cancel, nabs_one k, mul_one]
  have h2 : nabs k s * m.real (𝒪[k] : Set k) * (nabs k (c * s⁻¹) * m.real (𝒪[k] : Set k)) =
      m.real (𝒪[k] : Set k) ^ 2 * nabs k c := by
    rw [← h1]; ring
  rw [hs, hbox, hbox, ← mul_pow, h2]

omit [T2Space T] in
theorem pf_pf (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (z : T × (n → k)) :
    pf ψ (Measure.pi fun _ => m) (pf ψ (Measure.pi fun _ => m) f) z =
      (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) * f (z.1, -z.2) := by
  haveI := secondCountable k
  obtain ⟨t, y⟩ := z
  have hsl := slice_mem_SB hf t
  have hg : (fun w => f (t, w - y)) ∈ SB (n → k) :=
    ⟨hsl.1.comp_continuous (continuous_sub_right y), hsl.2.comp_homeomorph (Homeomorph.subRight y)⟩
  have hinv := inversion_const m h hg
  simp only [zero_sub] at hinv
  show ∫ x, (∫ w, f (t, w) * (ψ (w ⬝ᵥ x) : ℂ) ∂(Measure.pi fun _ => m)) * (ψ (x ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => m) = _ * f (t, -y)
  rw [← hinv]
  congr 1
  funext x
  rw [← integral_mul_const]
  have e := integral_sub_right_eq_self (μ := Measure.pi fun _ : n => m)
    (fun u => f (t, u) * (ψ ((u + y) ⬝ᵥ x) : ℂ)) y
  simp only [sub_add_cancel] at e
  rw [e]
  congr 1
  funext u
  rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm y x]
  ring

theorem pf_bijOn (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c) :
    Set.BijOn (pf ψ (Measure.pi fun _ => m)) {f | f ∈ SB (T × (n → k))} {f | f ∈ SB (T × (n → k))} := by
  haveI := secondCountable k
  set C : ℂ := (((m.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ Fintype.card n : ℝ) : ℂ) with hC
  have hC0 : C ≠ 0 := by
    have h1 : 0 < m.real (𝒪[k] : Set k) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos ((isOpen_int k).measure_ne_zero m ⟨0, by simp⟩)
        (isCompact_int k).measure_lt_top.ne
    have h2 := nabs_pos k c
    rw [hC]
    exact Complex.ofReal_ne_zero.mpr (pow_pos (mul_pos (pow_pos h1 2) h2) _).ne'
  have hsmul : ∀ (a : ℂ) (g : T × (n → k) → ℂ), pf ψ (Measure.pi fun _ : n => m) (a • g) = a • pf ψ (Measure.pi fun _ : n => m) g := by
    intro a g
    funext z
    simp only [pf, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul a _
  have hpp : ∀ g ∈ SB (T × (n → k)), ∀ z, pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g) z = C * g (z.1, -z.2) :=
    fun g hg z => pf_pf m h hg z
  refine ⟨fun g hg => pf_mem_SB (Measure.pi fun _ : n => m) h hg, fun g hg g' hg' hgg => ?_, fun g hg => ?_⟩
  · funext z
    have e1 := hpp g hg (z.1, -z.2)
    have e2 := hpp g' hg' (z.1, -z.2)
    rw [hgg] at e1
    simp only [neg_neg, Prod.mk.eta] at e1 e2
    exact mul_left_cancel₀ hC0 (e1.symm.trans e2)
  · have h2 := pf_mem_SB (Measure.pi fun _ : n => m) h (pf_mem_SB (Measure.pi fun _ : n => m) h hg)
    refine ⟨(C ^ 2)⁻¹ • pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) (pf ψ (Measure.pi fun _ : n => m) g)), (SB _).smul_mem _ (pf_mem_SB (Measure.pi fun _ : n => m) h h2), ?_⟩
    rw [hsmul]
    funext z
    rw [Pi.smul_apply, hpp _ h2, hpp _ hg]
    simp only [neg_neg, Prod.mk.eta, smul_eq_mul]
    field_simp

end Partial

section Matrices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def curryH (k : Type) [TopologicalSpace k] (a b : Type) : (a × b → k) ≃ₜ Matrix a b k where
  toFun y := Matrix.of (Function.curry y)
  invFun x := fun p => x p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_matrix fun i j => continuous_apply (i, j)
  continuous_invFun := continuous_pi fun p => continuous_id.matrix_elem p.1 p.2

def curryT (k : Type) [TopologicalSpace k] (a b : Type) : Matrix b a k ≃ₜ (a × b → k) where
  toFun x := fun p => x p.2 p.1
  invFun y := Matrix.of fun j i => y (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun p => continuous_id.matrix_elem p.2 p.1
  continuous_invFun := continuous_matrix fun j i => continuous_apply (i, j)

variable [MeasurableSpace k] [BorelSpace k]

end Matrices

section Homeos

variable (k : Type) [TopologicalSpace k] (ρ v τ w W : Type)

def colsH : (Matrix W ρ k × Matrix W v k) × Matrix W ρ k ≃ₜ Matrix W (ρ ⊕ v ⊕ ρ) k where
  toFun z := glueCols z.1.1 z.1.2 z.2
  invFun x := ((Matrix.of fun i j => x i (.inl j), Matrix.of fun i j => x i (.inr (.inl j))),
    Matrix.of fun i j => x i (.inr (.inr j)))
  left_inv _ := rfl
  right_inv x := by ext i (j | j | j) <;> rfl
  continuous_toFun := continuous_matrix fun i j => by
    rcases j with j | j | j
    · exact (continuous_fst.comp continuous_fst).matrix_elem i j
    · exact (continuous_snd.comp continuous_fst).matrix_elem i j
    · exact continuous_snd.matrix_elem i j
  continuous_invFun :=
    ((continuous_matrix fun _ _ => continuous_id.matrix_elem _ _).prodMk
      (continuous_matrix fun _ _ => continuous_id.matrix_elem _ _)).prodMk
      (continuous_matrix fun _ _ => continuous_id.matrix_elem _ _)

def mixH₁ : Mix₁ k ρ v W ≃ₜ (Matrix W ρ k × Matrix W v k) × Matrix ρ W k where
  toFun z := ((z.1, z.2.2), z.2.1)
  invFun z := (z.1.1, z.2, z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

abbrev Kept := Matrix (τ ⊕ w ⊕ τ) ρ k × Matrix ρ (τ ⊕ w ⊕ τ) k × Matrix τ v k × Matrix w v k

def rowsH : Kept k ρ v τ w × Matrix τ v k ≃ₜ Mix₁ k ρ v (τ ⊕ w ⊕ τ) where
  toFun z := (z.1.1, z.1.2.1, glueRows z.2 z.1.2.2.2 z.1.2.2.1)
  invFun x := ((x.1, x.2.1, Matrix.of fun i j => x.2.2 (.inr (.inr i)) j,
    Matrix.of fun i j => x.2.2 (.inr (.inl i)) j), Matrix.of fun i j => x.2.2 (.inl i) j)
  left_inv _ := rfl
  right_inv x := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    ext (i | i | i) j <;> rfl
  continuous_toFun := by
    refine Continuous.prodMk (by fun_prop) (Continuous.prodMk (by fun_prop) ?_)
    refine continuous_matrix fun i j => ?_
    rcases i with i | i | i
    · exact continuous_snd.matrix_elem i j
    · exact (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_fst))).matrix_elem i j
    · exact (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_fst))).matrix_elem i j
  continuous_invFun :=
    (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      ((continuous_matrix fun _ _ => (continuous_snd.comp continuous_snd).matrix_elem _ _).prodMk
      (continuous_matrix fun _ _ => (continuous_snd.comp continuous_snd).matrix_elem _ _)))).prodMk
      (continuous_matrix fun _ _ => (continuous_snd.comp continuous_snd).matrix_elem _ _)

def mixH₂ : Mix₂ k ρ v τ w ≃ₜ Kept k ρ v τ w × Matrix v τ k where
  toFun z := ((z.1, z.2.1, z.2.2.1, z.2.2.2.2), z.2.2.2.1)
  invFun z := (z.1.1, z.1.2.1, z.1.2.2.1, z.2, z.1.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Homeos

section Main

variable {k : Type} [Field k]

theorem chr_add (ψ : AddChar k Circle) (s : ℤˣ) (x y : k) : chr ψ s (x + y) = chr ψ s x * chr ψ s y := by
  simp only [chr, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem integral_shift (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (s : ℤˣ)
    {a b : Type} [Fintype a] [Fintype b] (G : Matrix a b k → ℂ) (L : Matrix a b k → k)
    (hL : ∀ x y, L (x + y) = L x + L y) (d : Matrix a b k) :
    ∫ c, G (c + d) * chr ψ (-s) (L c) ∂(volM m a b) =
      chr ψ s (L d) * ∫ c, G c * chr ψ (-s) (L c) ∂(volM m a b) := by
  haveI := secondCountable k
  have hsub : ∀ c, L (c - d) = L c - L d := fun c =>
    eq_sub_of_add_eq (by rw [← hL, sub_add_cancel])
  have hchr : ∀ c, chr ψ (-s) (L (c - d)) = chr ψ (-s) (L c) * chr ψ s (L d) := by
    intro c
    rw [hsub, sub_eq_add_neg, chr_add]
    congr 1
    simp [chr]
  haveI : (volM m a b).IsAddRightInvariant := Measure.pi.isAddRightInvariant _
  haveI : MeasurableAdd (Matrix a b k) := inferInstanceAs (MeasurableAdd (a → b → k))
  have e : ∫ c, G (c + d) * chr ψ (-s) (L c) ∂(volM m a b) =
      ∫ c, G c * chr ψ (-s) (L (c - d)) ∂(volM m a b) := by
    have := integral_add_right_eq_self (μ := volM m a b)
      (fun c : Matrix a b k => G c * chr ψ (-s) (L (c - d))) d
    simp only [add_sub_cancel_right] at this
    exact this
  rw [e]
  simp_rw [hchr, ← mul_assoc]
  rw [integral_mul_const, mul_comm]

variable (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] [Fintype W] [DecidableEq W]

theorem four₁_om (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k)
    (ξ : Matrix W ρ k) (η : Matrix ρ W k) (x₀ : Matrix W v k) :
    four₁ ψ m s₁ (om μ (uGL ν ν' b) 1 Φ) (ξ, η, x₀) =
      chr ψ s₁ (trace (η * (ξ * b + x₀ * ν))) * four₁ ψ m s₁ Φ (ξ, η, x₀ + ξ * ν') := by
  simp only [four₁, om_uGL, glueCols_mul_uMat, add_assoc]
  exact integral_shift ψ m s₁ (fun c => Φ (glueCols ξ (x₀ + ξ * ν') c)) (fun c => trace (η * c))
    (fun x y => by rw [Matrix.mul_add, Matrix.trace_add]) (ξ * b + x₀ * ν)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v] [DecidableEq τ] [DecidableEq w] in
theorem glueFun_mul_glueRows (η' : Matrix ρ τ k) (η₀ : Matrix ρ w k) (ηd : Matrix ρ τ k)
    (r : Matrix τ v k) (x : Matrix w v k) (ys : Matrix τ v k) :
    glueFun η' η₀ ηd * glueRows r x ys = η' * r + (η₀ * x + ηd * ys) := by
  simp only [glueFun, glueRows, Matrix.fromCols_mul_fromRows]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  [DecidableEq ρ] [Fintype v] [DecidableEq v] [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] in
theorem glueRows_add_mul (r : Matrix τ v k) (x : Matrix w v k) (ys : Matrix τ v k)
    (ξ' : Matrix τ ρ k) (ξ₀ : Matrix w ρ k) (ν' : Matrix ρ v k) :
    glueRows r x ys + glueRows ξ' ξ₀ 0 * ν' = glueRows (r + ξ' * ν') (x + ξ₀ * ν') ys := by
  ext (i | i | i) j <;> simp [glueRows, Matrix.fromRows_mul]

theorem four₁_n (Φ : Matrix (τ ⊕ w ⊕ τ) (ρ ⊕ v ⊕ ρ) k → ℂ) (ν : Matrix v ρ k) (ν' : Matrix ρ v k)
    (ξ' : Matrix τ ρ k) (ξ₀ : Matrix w ρ k) (η₀ : Matrix ρ w k) (ηd : Matrix ρ τ k)
    (r ys : Matrix τ v k) (x₀₀ : Matrix w v k) :
    four₁ ψ m s₁ (om μ (nGL ν ν') 1 Φ) (glueRows ξ' ξ₀ 0, glueFun 0 η₀ ηd, glueRows r x₀₀ ys) =
      chr ψ s₁ (trace ((η₀ * x₀₀ + ηd * ys) * ν)) *
        four₁ ψ m s₁ Φ (glueRows ξ' ξ₀ 0, glueFun 0 η₀ ηd, glueRows (r + ξ' * ν') (x₀₀ + ξ₀ * ν') ys) := by
  have := four₁_om ψ m μ s₁ Φ ν ν' 0 (glueRows ξ' ξ₀ 0) (glueFun 0 η₀ ηd) (glueRows r x₀₀ ys)
  rw [Matrix.mul_zero, zero_add, ← Matrix.mul_assoc, glueFun_mul_glueRows, Matrix.zero_mul, zero_add,
    glueRows_add_mul] at this
  exact this

theorem four₁_om_zGL_eq_chr_trace_mul (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) (b : Matrix ρ ρ k)
    (ξ : Matrix W ρ k) (η : Matrix ρ W k) (x₀ : Matrix W v k) :
    four₁ ψ m s₁ (om μ (zGL v b) 1 Φ) (ξ, η, x₀) =
      chr ψ s₁ (∑ p, ∑ q, (η * ξ) p q * b q p) * four₁ ψ m s₁ Φ (ξ, η, x₀) := by
  have := four₁_om ψ m μ s₁ Φ (0 : Matrix v ρ k) 0 b ξ η x₀
  simp only [Matrix.mul_zero, add_zero] at this
  rw [← Matrix.mul_assoc] at this
  show four₁ ψ m s₁ (om μ (uGL (0 : Matrix v ρ k) 0 b) 1 Φ) (ξ, η, x₀) = _
  rw [this, show trace (η * ξ * b) = ∑ p, ∑ q, (η * ξ) p q * b q p by
    simp [Matrix.trace, Matrix.mul_apply]]

end Main

end GlobalTheory.SplitDict
