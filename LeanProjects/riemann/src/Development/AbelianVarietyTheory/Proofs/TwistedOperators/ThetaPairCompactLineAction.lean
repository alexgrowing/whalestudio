import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaSpanFiniteDimensionalDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactArchOperatorPreservesFockVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIntertwinesFockDerivatiStatement

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KExpLineW

section Abstract

variable {α : Type}

def zeroOnF (C : Submodule ℂ (α → ℂ)) (P : Finset α) : Submodule ℂ C where
  carrier := {s | ∀ y ∈ P, (s : α → ℂ) y = 0}
  add_mem' := by
    intro a b ha hb y hy
    simp [ha y hy, hb y hy]
  zero_mem' := by
    intro y _
    simp
  smul_mem' := by
    intro c a ha y hy
    simp [ha y hy]

theorem exists_finset_sep (C : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ C] :
    ∃ P : Finset α, ∀ s ∈ C, (∀ y ∈ P, s y = 0) → s = 0 := by
  classical
  obtain ⟨P, -, hmin⟩ := (measure fun P : Finset α => Module.finrank ℂ (zeroOnF C P)).wf.has_min Set.univ
    ⟨∅, trivial⟩
  refine ⟨P, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, s y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hlt : zeroOnF C (insert y P) < zeroOnF C P := by
    refine lt_of_le_of_ne (fun a ha z hz => ha z (Finset.mem_insert_of_mem hz)) fun heq => ?_
    have hmem : (⟨s, hs⟩ : C) ∈ zeroOnF C P := h0
    rw [← heq] at hmem
    exact hy (hmem y (Finset.mem_insert_self y P))
  exact hmin (insert y P) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem ode_mem {ι : Type} [Fintype ι] (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (Z : Submodule ℂ (ι → ℂ))
    (hA : ∀ z ∈ Z, A z ∈ Z) (y : ℝ → ι → ℂ) (hy : ∀ t, HasDerivAt y (A (y t)) t) (h0 : y 0 ∈ Z) (t : ℝ) :
    y t ∈ Z := by
  obtain ⟨Z', hc⟩ := Submodule.exists_isCompl Z
  let q : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) := Z'.projection Z hc.symm
  have hq0 : ∀ z, q z = 0 ↔ z ∈ Z := fun z => Submodule.projection_apply_eq_zero_iff hc.symm
  have hqq : ∀ z, q (q z) = q z := fun z =>
    Submodule.projection_apply_of_mem_left hc.symm (Submodule.projection_apply_mem hc.symm z)
  have hkill : ∀ z, q (A z) = q (A (q z)) := by
    intro z
    have hz : z - q z ∈ Z := (hq0 _).1 (by rw [map_sub, hqq, sub_self])
    have h2 := (hq0 _).2 (hA _ hz)
    rw [map_sub, map_sub, sub_eq_zero] at h2
    exact h2
  let Bc : (ι → ℂ) →L[ℝ] (ι → ℂ) := ((q ∘ₗ A).restrictScalars ℝ).toContinuousLinearMap
  let qc : (ι → ℂ) →L[ℝ] (ι → ℂ) := (q.restrictScalars ℝ).toContinuousLinearMap
  have hu : ∀ t, HasDerivAt (fun s => q (y s)) (Bc (q (y t))) t := by
    intro t
    have h := qc.hasFDerivAt.comp_hasDerivAt t (hy t)
    have e : Bc (q (y t)) = qc (A (y t)) := (hkill (y t)).symm
    rw [e]
    exact h
  have hv : ∀ t : ℝ, HasDerivAt (fun _ : ℝ => (0 : ι → ℂ)) (Bc 0) t := by
    intro t
    rw [map_zero]
    exact hasDerivAt_const t 0
  have heq := ODE_solution_unique_univ (v := fun _ => Bc) (s := fun _ => Set.univ) (K := ‖Bc‖₊) (t₀ := 0)
    (fun _ => Bc.lipschitz.lipschitzOnWith) (fun t => ⟨hu t, trivial⟩) (fun t => ⟨hv t, trivial⟩)
    ((hq0 _).2 h0)
  exact (hq0 _).1 (congrFun heq t)

end Abstract

end GlobalTheory.KExpLineW

namespace GlobalTheory.KExpLineW

section Orbit

variable {α : Type}

theorem orbit_mem (U : Multiplicative ℝ →* Module.End ℂ (α → ℂ)) (P N C : Submodule ℂ (α → ℂ))
    [FiniteDimensional ℂ C] (hCP : C ≤ P)
    (hN : ∀ Ψ ∈ N, ∀ Ψ₁ ∈ P, (∀ x, HasDerivAt (fun t : ℝ => U (Multiplicative.ofAdd t) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N)
    (Φ : α → ℂ) (hΦ : Φ ∈ N) (hC : ∀ t : ℝ, U (Multiplicative.ofAdd t) Φ ∈ C)
    (hd : ∀ x (t : ℝ), DifferentiableAt ℝ (fun s : ℝ => U (Multiplicative.ofAdd s) Φ x) t) (t : ℝ) :
    U (Multiplicative.ofAdd t) Φ ∈ N := by
  classical
  let c : ℝ → α → ℂ := fun t => U (Multiplicative.ofAdd t) Φ
  have hcadd : ∀ s t, U (Multiplicative.ofAdd s) (c t) = c (s + t) := by
    intro s t
    show U _ (U _ Φ) = U _ Φ
    rw [ofAdd_add, map_mul, Module.End.mul_apply]
  let C' : Submodule ℂ (α → ℂ) := Submodule.span ℂ (Set.range c)
  have hC'C : C' ≤ C := Submodule.span_le.2 (by rintro _ ⟨t, rfl⟩; exact hC t)
  haveI : FiniteDimensional ℂ C' := Submodule.finiteDimensional_of_le hC'C
  have hcC' : ∀ t, c t ∈ C' := fun t => Submodule.subset_span ⟨t, rfl⟩
  have hUC : ∀ s, ∀ Ψ ∈ C', U (Multiplicative.ofAdd s) Ψ ∈ C' := by
    intro s Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      rw [hcadd]
      exact hcC' _
    | zero => rw [map_zero]; exact C'.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact C'.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact C'.smul_mem a hx
  have hdiff : ∀ Ψ ∈ C', ∀ x, ∀ t : ℝ, DifferentiableAt ℝ (fun s : ℝ => U (Multiplicative.ofAdd s) Ψ x) t := by
    intro Ψ hΨ x
    induction hΨ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t', rfl⟩ := hy
      intro t
      have e : (fun s : ℝ => U (Multiplicative.ofAdd s) (c t') x) = fun s => c (s + t') x := by
        funext s
        rw [hcadd]
      rw [e]
      exact (hd x (t + t')).comp t (differentiableAt_id.add_const t')
    | zero =>
      intro t
      simp only [map_zero, Pi.zero_apply]
      exact differentiableAt_const _
    | add y z _ _ hy hz =>
      intro t
      simp only [map_add, Pi.add_apply]
      exact (hy t).add (hz t)
    | smul a y _ hy =>
      intro t
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hy t).const_mul a
  let D : C' →ₗ[ℂ] (α → ℂ) :=
    { toFun := fun Ψ x => deriv (fun s : ℝ => U (Multiplicative.ofAdd s) (Ψ : α → ℂ) x) 0
      map_add' := by
        intro a b
        funext x
        simp only [Submodule.coe_add, map_add, Pi.add_apply]
        exact deriv_add (hdiff a a.2 x 0) (hdiff b b.2 x 0)
      map_smul' := by
        intro a b
        funext x
        simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact deriv_const_mul a (hdiff b b.2 x 0) }
  have hD : ∀ Ψ : C', ∀ x, HasDerivAt (fun s : ℝ => U (Multiplicative.ofAdd s) (Ψ : α → ℂ) x) (D Ψ x) 0 :=
    fun Ψ x => (hdiff _ Ψ.2 x 0).hasDerivAt
  obtain ⟨P0, hP0⟩ := exists_finset_sep C'
  let Ev : C' →ₗ[ℂ] (P0 → ℂ) :=
    { toFun := fun s p => (s : α → ℂ) p
      map_add' := by intro a b; funext p; simp
      map_smul' := by intro a b; funext p; simp }
  have hEv : LinearMap.ker Ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    exact Subtype.ext (hP0 s s.2 fun y hy => congrFun hs ⟨y, hy⟩)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Ev hEv
  have hLE : ∀ w : C', L (Ev w) = w := fun w => LinearMap.congr_fun hL w
  have hDC : ∀ Ψ : C', D Ψ ∈ C' := by
    intro Ψ
    let z : ℝ → P0 → ℂ := fun s => Ev ⟨U (Multiplicative.ofAdd s) (Ψ : α → ℂ), hUC s _ Ψ.2⟩
    have hz : HasDerivAt z (fun p => D Ψ p) 0 := hasDerivAt_pi.2 fun p => hD Ψ p
    have key : D Ψ = ((L (fun p => D Ψ p) : C') : α → ℂ) := by
      funext x
      let evx : C' →ₗ[ℂ] ℂ :=
        { toFun := fun s => (s : α → ℂ) x
          map_add' := by intro a b; simp
          map_smul' := by intro a b; simp }
      let g : (P0 → ℂ) →L[ℝ] ℂ := ((evx ∘ₗ L).restrictScalars ℝ).toContinuousLinearMap
      have h1 := g.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
      have e : (g ∘ z) = fun s : ℝ => U (Multiplicative.ofAdd s) (Ψ : α → ℂ) x := by
        funext s
        show evx (L (Ev _)) = _
        rw [hLE]
        rfl
      rw [e] at h1
      exact (hD Ψ x).unique h1
    rw [key]
    exact (L _).2
  let D' : C' →ₗ[ℂ] C' := LinearMap.codRestrict C' D hDC
  let A : (P0 → ℂ) →ₗ[ℂ] (P0 → ℂ) := Ev ∘ₗ D' ∘ₗ L
  let Z : Submodule ℂ (P0 → ℂ) := (N.comap C'.subtype).map Ev
  let y : ℝ → P0 → ℂ := fun s => Ev ⟨c s, hcC' s⟩
  have hct : ∀ t x, HasDerivAt (fun s => c s x) (D ⟨c t, hcC' t⟩ x) t := by
    intro t x
    have h0 := hD ⟨c t, hcC' t⟩ x
    have e1 : (fun s : ℝ => U (Multiplicative.ofAdd s) ((⟨c t, hcC' t⟩ : C') : α → ℂ) x) = fun s => c (s + t) x := by
      funext s
      exact congrFun (hcadd s t) x
    rw [e1] at h0
    have h2 : HasDerivAt (fun s => c (s - t + t) x) (D ⟨c t, hcC' t⟩ x) t := by
      rw [show (0 : ℝ) = t - t from (sub_self t).symm] at h0
      exact h0.comp_sub_const t t
    simpa only [sub_add_cancel] using h2
  have hy : ∀ t, HasDerivAt y (A (y t)) t := by
    intro t
    have e : A (y t) = Ev (D' ⟨c t, hcC' t⟩) := by
      show Ev (D' (L (Ev _))) = _
      rw [hLE]
    rw [e]
    exact hasDerivAt_pi.2 fun p => hct t p
  have hA : ∀ z ∈ Z, A z ∈ Z := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨D' w, ?_, ?_⟩
    · show D w ∈ N
      exact hN _ hw _ (hCP (hC'C (hDC w))) (hD w)
    · show Ev (D' w) = Ev (D' (L (Ev w)))
      rw [hLE]
  have h0 : y 0 ∈ Z := by
    refine ⟨⟨c 0, hcC' 0⟩, ?_, rfl⟩
    show c 0 ∈ N
    show U (Multiplicative.ofAdd (0 : ℝ)) Φ ∈ N
    rw [ofAdd_zero, map_one]
    exact hΦ
  obtain ⟨w, hw, hwe⟩ := ode_mem A Z hA y hy h0 t
  have : w = ⟨c t, hcC' t⟩ := by
    have := congrArg L hwe
    rwa [hLE, hLE] at this
  have hw' : (w : α → ℂ) ∈ N := hw
  rw [this] at hw'
  exact hw'

end Orbit

end GlobalTheory.KExpLineW

namespace GlobalTheory.KExpLineW

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem map_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    (T : Fn F n d → Fn F n d) (f f₁ : SInf F (Fin n × Fin d)) (hA : Acts (evI F) T ⇑f ⇑f₁)
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) : T (pure f φ) = pure f₁ φ :=
  hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hφ ((hvac.and hM.std).mono fun _ h => h.1.trans h.2))

theorem polData_kfin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ Φ ∈ GlobalTheory.ThK.PolData B M,
      ∃ S : Submodule ℂ (GlobalTheory.ThK.Fn F n d), FiniteDimensional ℂ S ∧ S ≤ GlobalTheory.ThK.PolData B M ∧
        ∀ k ∈ KInf σ W B.emb, om (1, k) Φ ∈ S := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have hψ : IsStd B.ψ := hP.base.std
  have hfin : ∀ m, FiniteDimensional ℂ (GlobalTheory.FockKFin.polLe M B.emb m) := by
    intro m
    induction m with
    | zero => exact GlobalTheory.T.fockVacua_span_finiteDimensional_dualPair F E σ B n d X W M χX χW om r s r' s' hP
    | succ m ih =>
      rw [GlobalTheory.FockKFin.polLe_succ]
      haveI := ih
      haveI := GlobalTheory.T.finiteDimensional_archimedeanSchwartzFockOperatorSpan F _ _ ih
      infer_instance
  have hle : ∀ m, GlobalTheory.FockKFin.polLe M B.emb m ≤ M.Pol B.ψ B.emb := by
    intro m
    induction m with
    | zero => exact Submodule.span_le.2 fun g hg => GlobalTheory.ThK.EvAt0.PolEv.gauss_mem hψ M B.emb hg
    | succ m ih =>
      rw [GlobalTheory.FockKFin.polLe_succ]
      refine sup_le ih (Submodule.span_le.2 ?_)
      rintro _ ⟨a, b, f, hf, rfl⟩
      exact GlobalTheory.ThK.EvAt0.PolEv.dOp_mem hψ M B.emb a b (ih hf)
  have hdir : Directed (· ≤ ·) (GlobalTheory.FockKFin.polLe M B.emb) := (GlobalTheory.FockKFin.polLe_mono M B.emb).directed_le
  have hcov : ∀ f ∈ M.Pol B.ψ B.emb, ∃ m, f ∈ GlobalTheory.FockKFin.polLe M B.emb m := by
    intro f hf
    have hsub : M.Pol B.ψ B.emb ≤ ⨆ m, GlobalTheory.FockKFin.polLe M B.emb m := by
      rw [GlobalTheory.ThK.EvAt0.PolEv.pol_eq hψ]
      refine sInf_le ⟨fun g hg => Submodule.mem_iSup_of_mem 0 (Submodule.subset_span hg), fun a b g hg => ?_⟩
      obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hg
      refine Submodule.mem_iSup_of_mem (m + 1) ?_
      rw [GlobalTheory.FockKFin.polLe_succ]
      exact Submodule.mem_sup_right (GlobalTheory.FockKFin.dOp_mem_dStep _ a b hm)
    exact (Submodule.mem_iSup_of_directed _ hdir).1 (hsub hf)
  have hst : ∀ k ∈ KInf σ W B.emb, ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
      ∀ m, ∀ f ∈ GlobalTheory.FockKFin.polLe M B.emb m, A f ∈ GlobalTheory.FockKFin.polLe M B.emb m := by
    intro k hk A hA m
    induction m with
    | zero =>
      intro f hf
      rw [GlobalTheory.FockKFin.polLe_zero] at hf ⊢
      refine Submodule.span_induction (fun g hg => Submodule.subset_span (GlobalTheory.T.maximalCompact_archOperator_preserves_fockVacua F E σ B n d X W M χX χW om r s r' s' hP k hk A hA g hg))
        (by rw [map_zero]; exact Submodule.zero_mem _) (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
        (fun c x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) hf
    | succ m ih =>
      intro f hf
      rw [GlobalTheory.FockKFin.polLe_succ] at hf ⊢
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      rw [map_add]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (ih y hy)) (Submodule.mem_sup_right ?_)
      refine Submodule.span_induction (fun g hg => ?_)
        (by rw [map_zero]; exact Submodule.zero_mem _) (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
        (fun c x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) hz
      obtain ⟨a, b, g₀, hg₀, rfl⟩ := hg
      obtain ⟨a', b', hab⟩ := GlobalTheory.T.archimedeanMaximalCompact_intertwines_fockDerivativeOps F E σ B n d X W M χX χW om r s r' s' hP k hk A hA a b
      rw [hab]
      exact GlobalTheory.FockKFin.dOp_mem_dStep _ a' b' (ih g₀ hg₀)
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hx
    obtain ⟨m, hm⟩ := hcov f hf
    haveI := hfin m
    refine ⟨(GlobalTheory.FockKFin.polLe M B.emb m).map (GlobalTheory.FockKFin.pureL φ), inferInstance, ?_, fun k hk => ?_⟩
    · rw [Submodule.map_le_iff_le_comap]
      intro g hg
      exact Submodule.subset_span ⟨g, hle m hg, φ, hφ, hvac, rfl⟩
    · obtain ⟨A, hA⟩ := GlobalTheory.ArchLocalAct.exists_op_of_KInf F E σ B n d X W M om χX χW hP.base hP.good hP.weil k hk
      rw [map_pure M B.ψ hP.good _ f (A f) (hA f) φ hφ hvac]
      exact Submodule.mem_map_of_mem (hst k hk A hA m f hm)
  | zero =>
    exact ⟨⊥, inferInstance, bot_le, fun k _ => by rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h₁, l₁, k₁⟩ := hx
    obtain ⟨S₂, h₂, l₂, k₂⟩ := hy
    exact ⟨S₁ ⊔ S₂, inferInstance, sup_le l₁ l₂, fun k hk => by
      rw [map_add]; exact Submodule.add_mem_sup (k₁ k hk) (k₂ k hk)⟩
  | smul c x _ hx =>
    obtain ⟨S, h, l, k₁⟩ := hx
    exact ⟨S, h, l, fun k hk => by rw [map_smul]; exact Submodule.smul_mem _ c (k₁ k hk)⟩

end GlobalTheory.KExpLineW

namespace GlobalTheory.KExpLineW

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem stab_line : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, (∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb) →
    ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F n d),
      (∀ Ψ ∈ N, ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B M,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N) →
      ∀ Φ ∈ N, Φ ∈ GlobalTheory.ThK.PolData B M → om (1, γ (Multiplicative.ofAdd (1 : ℝ))) Φ ∈ N := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγL hγK N hN Φ hΦN hΦ
  obtain ⟨-, -, hDer, hOp⟩ := GlobalTheory.T.polynomial_datum_action_of_pair hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let U : Multiplicative ℝ →* Module.End ℂ (Fn F n d) := om.comp ((MonoidHom.inr (UA σ X.J) (UA σ W.J)).comp γ)
  have hdiff : ∀ Ψ ∈ PolData B M, ∀ x (t : ℝ),
      DifferentiableAt ℝ (fun s : ℝ => U (Multiplicative.ofAdd s) Ψ x) t := by
    intro Ψ hΨ x
    induction hΨ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hy
      intro t
      have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
        (hvac.and hP.good.std).mono fun _ h => h.1.trans h.2
      have hpt : ∀ u : ℝ, U (Multiplicative.ofAdd u) (pure f φ) = pure (D u f) φ := fun u =>
        map_pure M B.ψ hP.good _ f (D u f) ((hD u f hf (D u f)).2 rfl) φ hφ hvac
      have hshift : ∀ s', U (Multiplicative.ofAdd (s' + t)) (pure f φ) =
          U (Multiplicative.ofAdd s') (pure (D t f) φ) := by
        intro s'
        rw [ofAdd_add, map_mul, Module.End.mul_apply, hpt t]
      have h0 := (hDg (D t f) (hDP t f hf) (Dg (D t f))).2 rfl _
        (GlobalTheory.ThK.EvUniqInf.rest_pure (D t f) φ hφ hstd) x
      have h0' : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) 0 :=
        h0.differentiableAt
      have e : (fun s : ℝ => U (Multiplicative.ofAdd s) (pure f φ) x) =
          (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) ∘ fun s => s - t := by
        funext s
        show _ = U (Multiplicative.ofAdd (s - t)) (pure (D t f) φ) x
        rw [← hshift, sub_add_cancel]
      have h4 : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x)
          ((fun s : ℝ => s - t) t) := by
        simp only [sub_self]
        exact h0'
      rw [e]
      exact DifferentiableAt.comp (f := fun s : ℝ => s - t) t h4 (differentiableAt_id.sub_const t)
    | zero =>
      intro t
      simp only [map_zero, Pi.zero_apply]
      exact differentiableAt_const _
    | add y z _ _ hy hz =>
      intro t
      simp only [map_add, Pi.add_apply]
      exact (hy t).add (hz t)
    | smul a y _ hy =>
      intro t
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hy t).const_mul a
  obtain ⟨C, hCfin, hCP, hCk⟩ := polData_kfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  haveI := hCfin
  exact orbit_mem U (PolData B M) N C hCP (fun Ψ h Ψ₁ h₁ hd => hN Ψ h Ψ₁ h₁ hd) Φ hΦN
    (fun t => hCk _ (hγK _)) (hdiff Φ hΦ) 1

end GlobalTheory.KExpLineW

end
