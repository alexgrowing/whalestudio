import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

open Filter Topology

noncomputable section
namespace GlobalTheory.LocFlat

theorem flatSB_isLocallyConstant_indicator {X : Type*} [TopologicalSpace X] {W : Set X} (hW : IsClopen W)
    (a : ℂ) : IsLocallyConstant (W.indicator fun _ => a) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

section Gen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

open Classical in

def freeMat (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if h : Free p (r, s) then e ⟨(r, s), h⟩ else 0

theorem affPt_eq_basePt_add_freeMat (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p x₀ e = basePt c x₀ + freeMat p e := rfl

theorem ch_add' (a b : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (a + b) = ch a + ch b := by
  simp [ch, Finset.sum_add_distrib]

theorem ch_basePt' (x₀ : Matrix n n' k) : ch (basePt c x₀) = 0 := by
  simp [ch, basePt, Fin.ext_iff]

theorem ch_affPt_zero_eq (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (affPt p (0 : Matrix n n' k) e) = ch (freeMat p e) := by
  rw [affPt_eq_basePt_add_freeMat, ch_add', ch_basePt', zero_add]

theorem freeMat_apply_free (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    freeMat p e rs.1.1 rs.1.2 = e rs := by
  simp [freeMat, rs.2]

theorem continuous_freeMat (p : ℕ) :
    Continuous (freeMat (k := k) (n := n) (n' := n') (c := c) p) := by
  refine continuous_matrix fun r s => ?_
  by_cases h : Free p (r, s)
  · simp only [freeMat, Matrix.of_apply, dif_pos h]; fun_prop
  · simp only [freeMat, Matrix.of_apply, dif_neg h]; exact continuous_const

theorem isClosedEmbedding_freeMat (p : ℕ) :
    Topology.IsClosedEmbedding (freeMat (k := k) (n := n) (n' := n') (c := c) p) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
      fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} => z rs.1.1 rs.1.2)
    (fun e => funext fun rs => freeMat_apply_free p e rs) ?_ (continuous_freeMat p)
  exact continuous_pi fun rs => continuous_id.matrix_elem _ _

theorem exists_clopen_ch_near (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ W : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsClopen W ∧ IsCompact W ∧
      (0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) ∈ W ∧
      ∀ z ∈ W, ‖((ψ (-ch z) : Circle) : ℂ) - 1‖ < 1 / 2 := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hU : {y : k | ‖((ψ (-y) : Circle) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : k) := by
    refine (isOpen_lt ?_ continuous_const).mem_nhds ?_
    · exact (continuous_subtype_val.comp (hψ.comp continuous_neg)).sub continuous_const |>.norm
    · simp
  obtain ⟨s₀, hs₀⟩ := exists_cball_subset hU
  let W : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => cball s₀
  have hWc : IsCompact W := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s₀
  have hWo : IsOpen W :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball s₀
  refine ⟨W, ⟨hWc.isClosed, hWo⟩, hWc, ?_, ?_⟩
  · intro r _ s _
    simp [cball]
  · intro z hz
    apply hs₀
    show valuation k (ch z) ≤ valuation k (s₀ : k)
    exact Valuation.map_sum_le _ fun i _ => hz _ (Set.mem_univ _) _ (Set.mem_univ _)

end Gen
end GlobalTheory.LocFlat

namespace GlobalTheory.LocFlat
open Filter Topology
section Gen2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

open Classical in

theorem flatSB_generic {X : Type} [TopologicalSpace X] [T2Space X] (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    (A : X → ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hA : Continuous fun q : X × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) => A q.1 q.2)
    (R : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → X) (hR : Continuous R)
    (Q : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hQ : Continuous Q)
    (hRA : ∀ x e, R (A x e) = x) (hQA : ∀ x e, Q (A x e) = freeMat p e)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    (fun x => ∫ e, Φ (A x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB X := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hemb : Topology.IsClosedEmbedding fun q : X × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      A q.1 q.2 := by
    refine Function.LeftInverse.isClosedEmbedding
      (f := fun z => (R z, fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} => Q z rs.1.1 rs.1.2))
      ?_ ?_ hA
    · rintro ⟨x, e⟩
      simp only [hRA, hQA]
      exact Prod.ext rfl (funext fun rs => freeMat_apply_free p e rs)
    · exact hR.prodMk (continuous_pi fun rs => hQ.matrix_elem _ _)
  exact integral_mul_mem_SB (Measure.pi fun _ => ν) (fun q => Φ (A q.1 q.2))
    ⟨hΦ.1.comp_continuous hA, hΦ.2.comp_isClosedEmbedding hemb⟩ (fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))

open Classical in

theorem flatOnto_generic {X : Type} [TopologicalSpace X] [T2Space X] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (ν : Measure k) (hν : ν.IsAddHaarMeasure) (p : ℕ)
    (A : X → ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (R : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → X) (hR : Continuous R)
    (Q : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hQ : Continuous Q)
    (G : X × Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hG : Continuous G)
    (hGRQ : ∀ z, G (R z, Q z) = z)
    (hRA : ∀ x e, R (A x e) = x) (hQA : ∀ x e, Q (A x e) = freeMat p e)
    (Ψ : X → ℂ) (hΨ : Ψ ∈ SB X) :
    ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x,
      ∫ e, Φ (A x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ) ∂(Measure.pi fun _ => ν) = Ψ x := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := hν
  obtain ⟨W, hWcl, hWc, hW0, hWψ⟩ := exists_clopen_ch_near (n := n) (n' := n') (c := c) ψ hψ
  set μ : Measure ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) := Measure.pi fun _ => ν
  set f : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ :=
    fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ) with hf
  set K := freeMat (k := k) (n := n) (n' := n') (c := c) p ⁻¹' W with hK
  set I : ℂ := ∫ e, W.indicator (fun _ => (1 : ℂ)) (freeMat p e) * f e ∂μ with hI
  have hfc : Continuous f := by
    refine continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_))
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_affPt_uncurry p).comp (Continuous.prodMk_right (0 : Matrix n n' k))).matrix_elem _ _
  have hKo : IsOpen K := hWcl.isOpen.preimage (continuous_freeMat p)
  have hKc : IsCompact K := (isClosedEmbedding_freeMat p).isCompact_preimage hWc
  have hK0 : (0 : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) ∈ K := by
    show freeMat p 0 ∈ W
    convert hW0 using 1
    ext r s; simp [freeMat]
  have hμK : 0 < μ.real K := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hKo.measure_pos μ ⟨0, hK0⟩).ne' hKc.measure_lt_top.ne
  have hIK : I = ∫ e in K, f e ∂μ := by
    rw [hI, ← integral_indicator hKo.measurableSet]
    congr 1; funext e
    by_cases he : e ∈ K
    · have : freeMat p e ∈ W := he
      simp [Set.indicator_of_mem he, Set.indicator_of_mem this]
    · have : freeMat p e ∉ W := he
      simp [Set.indicator_of_notMem he, Set.indicator_of_notMem this]
  have hInt : IntegrableOn f K μ := hfc.continuousOn.integrableOn_compact hKc
  have hI0 : I ≠ 0 := by
    intro h0
    have hb : ‖∫ e in K, (f e - 1) ∂μ‖ ≤ 1 / 2 * μ.real K := by
      refine norm_setIntegral_le_of_norm_le_const hKc.measure_lt_top fun e he => ?_
      have := hWψ _ he
      rw [← ch_affPt_zero_eq] at this
      exact this.le
    rw [integral_sub hInt (integrableOn_const hKc.measure_lt_top.ne), ← hIK, h0, setIntegral_const] at hb
    simp only [zero_sub, norm_neg, Complex.real_smul, mul_one] at hb
    rw [Complex.norm_real, Real.norm_of_nonneg hμK.le] at hb
    linarith
  refine ⟨fun z => I⁻¹ * (Ψ (R z) * W.indicator (fun _ => (1 : ℂ)) (Q z)), ?_, fun x => ?_⟩
  · have hH : (fun q : X × Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
        Ψ q.1 * W.indicator (fun _ => (1 : ℂ)) q.2) ∈ SB _ := by
      refine ⟨(hΨ.1.comp_continuous continuous_fst).mul
        ((flatSB_isLocallyConstant_indicator hWcl 1).comp_continuous continuous_snd), ?_⟩
      refine HasCompactSupport.intro (hΨ.2.isCompact.prod hWc) fun q hq => ?_
      by_cases h1 : q.1 ∈ tsupport Ψ
      · have h2 : q.2 ∉ W := fun h2 => hq ⟨h1, h2⟩
        simp [Set.indicator_of_notMem h2]
      · simp [image_eq_zero_of_notMem_tsupport h1]
    have hemb : Topology.IsClosedEmbedding fun z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => (R z, Q z) :=
      Function.LeftInverse.isClosedEmbedding (f := G) hGRQ hG (hR.prodMk hQ)
    exact ⟨(IsLocallyConstant.const I⁻¹).mul (hH.1.comp_continuous (hR.prodMk hQ)),
      (hH.2.comp_isClosedEmbedding hemb).mul_left⟩
  · have : ∀ e, I⁻¹ * (Ψ (R (A x e)) * W.indicator (fun _ => (1 : ℂ)) (Q (A x e))) * f e =
        (I⁻¹ * Ψ x) * (W.indicator (fun _ => (1 : ℂ)) (freeMat p e) * f e) := by
      intro e; rw [hRA, hQA]; ring
    simp only [hf] at this
    rw [integral_congr_ae (Eventually.of_forall this), integral_const_mul, ← hI]
    field_simp

end Gen2
end GlobalTheory.LocFlat

namespace GlobalTheory.LocFlat
section Spec
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def restOf (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if rd r s then 0 else z r s - basePt c (0 : Matrix n n' k) r s

def glue {X : Type} (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool) (E : X → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (q : X × Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if rd r s then E q.1 r s else q.2 r s + basePt c (0 : Matrix n n' k) r s

theorem continuous_restOf (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool) :
    Continuous (restOf (k := k) (n := n) (n' := n') rd) := by
  refine continuous_matrix fun r s => ?_
  cases h : rd r s
  · simp only [restOf, Matrix.of_apply, h, Bool.false_eq_true, ↓reduceIte]; fun_prop
  · simp only [restOf, Matrix.of_apply, h]; exact continuous_const

theorem continuous_glue {X : Type} [TopologicalSpace X] (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool)
    {E : X → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k} (hE : Continuous E) :
    Continuous (glue (k := k) rd E) := by
  refine continuous_matrix fun r s => ?_
  cases h : rd r s
  · simp only [glue, Matrix.of_apply, h, Bool.false_eq_true, ↓reduceIte]; fun_prop
  · simp only [glue, Matrix.of_apply, h]; exact (hE.comp continuous_fst).matrix_elem _ _

theorem glue_restOf {X : Type} (rd : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool)
    (E : X → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (R : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → X)
    (hER : ∀ z r s, rd r s = true → E (R z) r s = z r s) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    glue rd E (R z, restOf rd z) = z := by
  ext r s
  cases h : rd r s
  · simp [glue, restOf, h]
  · simp [glue, h, hER z r s h]

def rdCol (p : ℕ) : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool
  | .inl _, .inl _ => true
  | .inl _, .inr i => decide (i.val + 1 = p)
  | .inr _, _ => false

def readCol (p : ℕ) (hp : p - 1 < c + 1) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix n (n' ⊕ Unit) k :=
  Matrix.of fun r s => Sum.elim (fun s => z (.inl r) (.inl s)) (fun _ => z (.inl r) (.inr ⟨p - 1, hp⟩)) s

def extCol (x : Matrix n (n' ⊕ Unit) k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => match r, s with
    | .inl r, .inl s => x r (.inl s)
    | .inl r, .inr _ => x r (.inr ())
    | .inr _, _ => 0

theorem continuous_readCol (p : ℕ) (hp : p - 1 < c + 1) :
    Continuous (readCol (k := k) (n := n) (n' := n') p hp) := by
  refine continuous_matrix fun r s => ?_
  rcases s with s | s
  · exact continuous_id.matrix_elem _ _
  · exact continuous_id.matrix_elem _ _

theorem continuous_extCol : Continuous (extCol (k := k) (n := n) (n' := n') (c := c)) := by
  refine continuous_matrix fun r s => ?_
  rcases r with r | r <;> rcases s with s | s
  · exact continuous_id.matrix_elem _ _
  · exact continuous_id.matrix_elem _ _
  · exact continuous_const
  · exact continuous_const

theorem extCol_readCol (p : ℕ) (hp : p - 1 < c + 1) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s)
    (h : rdCol p r s = true) : extCol (readCol p hp z) r s = z r s := by
  rcases r with r | r <;> rcases s with s | s
  · rfl
  · simp only [rdCol, decide_eq_true_eq] at h
    simp only [extCol, readCol, Matrix.of_apply, Sum.elim_inr]
    congr 2; ext; simp; omega
  · simp [rdCol] at h
  · simp [rdCol] at h

def ptCol (p : ℕ) (x : Matrix n (n' ⊕ Unit) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  affPt p x.toCols₁ e + colAt n' c p fun r => x r (Sum.inr ())

theorem readCol_ptCol (p : ℕ) (hp1 : 1 ≤ p) (hp : p - 1 < c + 1) (x : Matrix n (n' ⊕ Unit) k) e :
    readCol p hp (ptCol p x e) = x := by
  ext r s
  rcases s with s | s
  · simp [readCol, ptCol, affPt, basePt, colAt, Free, Matrix.toCols₁]
  · simp [readCol, ptCol, affPt, basePt, colAt, Free]
    have h1 : ¬ p < p - 1 + 1 := by omega
    have h2 : p - 1 + 1 = p := by omega
    simp [h1, h2]

theorem restOf_ptCol (p : ℕ) (x : Matrix n (n' ⊕ Unit) k) e :
    restOf (rdCol p) (ptCol (c := c) p x e) = freeMat p e := by
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [restOf, rdCol, freeMat, Free]
  · by_cases h : s.val + 1 = p
    · simp [restOf, rdCol, freeMat, Free, h]
    · simp [restOf, rdCol, freeMat, ptCol, affPt, basePt, colAt, Free, h]
  · simp [restOf, rdCol, freeMat, ptCol, affPt, basePt, colAt]
  · simp [restOf, rdCol, freeMat, ptCol, affPt, basePt, colAt]

end Spec
end GlobalTheory.LocFlat

namespace GlobalTheory.LocFlat
section SpecRow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def rdRow (p : ℕ) : n ⊕ Fin c → n' ⊕ Fin (c + 1) → Bool
  | .inl _, .inl _ => true
  | .inr l, .inl _ => decide (l.val + 1 = p)
  | _, .inr _ => false

def readRow (p : ℕ) (hp : p - 1 < c) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix (n ⊕ Unit) n' k :=
  Matrix.of fun r s => Sum.elim (fun r => z (.inl r) (.inl s)) (fun _ => z (.inr ⟨p - 1, hp⟩) (.inl s)) r

def extRow (x : Matrix (n ⊕ Unit) n' k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => match r, s with
    | .inl r, .inl s => x (.inl r) s
    | .inr _, .inl s => x (.inr ()) s
    | _, .inr _ => 0

theorem continuous_readRow (p : ℕ) (hp : p - 1 < c) :
    Continuous (readRow (k := k) (n := n) (n' := n') p hp) := by
  refine continuous_matrix fun r s => ?_
  rcases r with r | r
  · exact continuous_id.matrix_elem _ _
  · exact continuous_id.matrix_elem _ _

theorem continuous_extRow : Continuous (extRow (k := k) (n := n) (n' := n') (c := c)) := by
  refine continuous_matrix fun r s => ?_
  rcases r with r | r <;> rcases s with s | s
  · exact continuous_id.matrix_elem _ _
  · exact continuous_const
  · exact continuous_id.matrix_elem _ _
  · exact continuous_const

theorem extRow_readRow (p : ℕ) (hp : p - 1 < c) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s)
    (h : rdRow p r s = true) : extRow (readRow p hp z) r s = z r s := by
  rcases r with r | r <;> rcases s with s | s
  · rfl
  · simp [rdRow] at h
  · simp only [rdRow, decide_eq_true_eq] at h
    simp only [extRow, readRow, Matrix.of_apply, Sum.elim_inr]
    congr 2; ext; simp; omega
  · simp [rdRow] at h

def ptRow (p : ℕ) (x : Matrix (n ⊕ Unit) n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  affPt p x.toRows₁ e + rowAt n c p (x (Sum.inr ()))

theorem readRow_ptRow (p : ℕ) (hp1 : 1 ≤ p) (hp : p - 1 < c) (x : Matrix (n ⊕ Unit) n' k) e :
    readRow p hp (ptRow p x e) = x := by
  ext r s
  rcases r with r | r
  · simp [readRow, ptRow, affPt, basePt, rowAt, Free, Matrix.toRows₁]
  · have h1 : ¬ p - 1 + 1 < p := by omega
    have h2 : p - 1 + 1 = p := by omega
    simp [readRow, ptRow, affPt, basePt, rowAt, Free, h1, h2]

theorem restOf_ptRow (p : ℕ) (x : Matrix (n ⊕ Unit) n' k) e :
    restOf (rdRow p) (ptRow (c := c) p x e) = freeMat p e := by
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [restOf, rdRow, freeMat, Free]
  · simp [restOf, rdRow, freeMat, ptRow, affPt, basePt, rowAt]
  · by_cases h : r.val + 1 = p
    · simp [restOf, rdRow, freeMat, Free, h]
    · simp [restOf, rdRow, freeMat, ptRow, affPt, basePt, rowAt, Free, h]
  · simp [restOf, rdRow, freeMat, ptRow, affPt, basePt, rowAt]

end SpecRow
end GlobalTheory.LocFlat

namespace GlobalTheory.LocFlat
section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem continuous_ptCol (p : ℕ) :
    Continuous fun q : Matrix n (n' ⊕ Unit) k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      ptCol p q.1 q.2 := by
  refine ((continuous_affPt_uncurry p).comp (Continuous.prodMk ?_ continuous_snd)).add ?_
  · exact continuous_matrix fun r s => continuous_fst.matrix_elem _ _
  · refine continuous_matrix fun r s => ?_
    rcases r with r | r <;> rcases s with s | s
    · simp only [colAt, fromBlocks_apply₁₁, Matrix.zero_apply]; exact continuous_const
    · by_cases h : s.val + 1 = p
      · simp only [colAt, fromBlocks_apply₁₂, Matrix.of_apply, h, if_true]
        exact continuous_fst.matrix_elem _ _
      · simp only [colAt, fromBlocks_apply₁₂, Matrix.of_apply, h, if_false]; exact continuous_const
    · simp only [colAt, fromBlocks_apply₂₁, Matrix.zero_apply]; exact continuous_const
    · simp only [colAt, fromBlocks_apply₂₂, Matrix.zero_apply]; exact continuous_const

theorem continuous_ptRow (p : ℕ) :
    Continuous fun q : Matrix (n ⊕ Unit) n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      ptRow p q.1 q.2 := by
  refine ((continuous_affPt_uncurry p).comp (Continuous.prodMk ?_ continuous_snd)).add ?_
  · exact continuous_matrix fun r s => continuous_fst.matrix_elem _ _
  · refine continuous_matrix fun r s => ?_
    rcases r with r | r <;> rcases s with s | s
    · simp only [rowAt, fromBlocks_apply₁₁, Matrix.zero_apply]; exact continuous_const
    · simp only [rowAt, fromBlocks_apply₁₂, Matrix.zero_apply]; exact continuous_const
    · by_cases h : r.val + 1 = p
      · simp only [rowAt, fromBlocks_apply₂₁, Matrix.of_apply, h, if_true]
        exact continuous_fst.matrix_elem _ _
      · simp only [rowAt, fromBlocks_apply₂₁, Matrix.of_apply, h, if_false]; exact continuous_const
    · simp only [rowAt, fromBlocks_apply₂₂, Matrix.zero_apply]; exact continuous_const

variable [MeasurableSpace k] [BorelSpace k]

open Classical in
theorem flCol_eq_integral (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) :
    flCol ψ ν p Φ = fun x => ∫ e, Φ (ptCol p x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ)
      ∂(Measure.pi fun _ => ν) := rfl

open Classical in
theorem flRow_eq_integral (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) :
    flRow ψ ν p Φ = fun x => ∫ e, Φ (ptRow p x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ)
      ∂(Measure.pi fun _ => ν) := rfl

end Main

theorem flat_SB_onto : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → (p ≤ c + 1 → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix n (n' ⊕ Unit) k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ = Ψ) ∧ (p ≤ c → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix (n ⊕ Unit) n' k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ = Ψ) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine ⟨fun hpc => ?_, fun hpc => ?_⟩
  · have hp : p - 1 < c + 1 := by omega
    refine ⟨fun Φ hΦ => ?_, fun Ψ hΨ => ?_⟩
    · rw [flCol_eq_integral]
      exact flatSB_generic ψ ν p (ptCol p) (continuous_ptCol p) (readCol p hp) (continuous_readCol p hp)
        (restOf (rdCol p)) (continuous_restOf _) (readCol_ptCol p hp1 hp) (restOf_ptCol p) Φ hΦ
    · obtain ⟨Φ, hΦ, h⟩ := flatOnto_generic ψ hψ ν hν p (ptCol p) (readCol p hp) (continuous_readCol p hp)
        (restOf (rdCol p)) (continuous_restOf _) (glue (rdCol p) extCol) (continuous_glue _ continuous_extCol)
        (glue_restOf _ _ _ (extCol_readCol p hp)) (readCol_ptCol p hp1 hp) (restOf_ptCol p) Ψ hΨ
      exact ⟨Φ, hΦ, by rw [flCol_eq_integral]; exact funext h⟩
  · have hp : p - 1 < c := by omega
    refine ⟨fun Φ hΦ => ?_, fun Ψ hΨ => ?_⟩
    · rw [flRow_eq_integral]
      exact flatSB_generic ψ ν p (ptRow p) (continuous_ptRow p) (readRow p hp) (continuous_readRow p hp)
        (restOf (rdRow p)) (continuous_restOf _) (readRow_ptRow p hp1 hp) (restOf_ptRow p) Φ hΦ
    · obtain ⟨Φ, hΦ, h⟩ := flatOnto_generic ψ hψ ν hν p (ptRow p) (readRow p hp) (continuous_readRow p hp)
        (restOf (rdRow p)) (continuous_restOf _) (glue (rdRow p) extRow) (continuous_glue _ continuous_extRow)
        (glue_restOf _ _ _ (extRow_readRow p hp)) (readRow_ptRow p hp1 hp) (restOf_ptRow p) Ψ hΨ
      exact ⟨Φ, hΦ, by rw [flRow_eq_integral]; exact funext h⟩

end GlobalTheory.LocFlat
