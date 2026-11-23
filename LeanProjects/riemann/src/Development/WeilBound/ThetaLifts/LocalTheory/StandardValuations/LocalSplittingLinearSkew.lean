import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.SplitProd
import Development.WeilBound.ThetaLifts.LocalTheory.IsArchimedeanLocalEquivariantMap
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.ValIffNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁}
  {ψ : AddChar (AF F) ℂ}

open Classical Filter in
theorem pure_cancel {κ : Type} [Fintype κ] {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, w v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (v : Pl F) {g : SInf F κ}
    (hg : g ≠ 0) {a b : (κ → Fv F v) → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v a) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v b)) : a = b := by
  have := PositivityTheory.ThKF.tensInj F κ w hne hstd {v} 2 ![1, -1] ![g, g] ![Function.update w v a, Function.update w v b]
    (fun i u hu => by
      have : u ≠ v := fun e => hu (Finset.mem_singleton.2 e)
      fin_cases i <;> simp [Function.update_of_ne this]) (by simp [Fin.sum_univ_two, h])
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hg (SchwartzMap.ext hn)
  funext y
  let y' : ∀ u : ({v} : Finset (Pl F)), κ → Fv F u := fun u => (Finset.mem_singleton.1 u.2).symm ▸ y
  let m : MultilinearMap ℂ (fun u : ({v} : Finset (Pl F)) => (κ → Fv F u) → ℂ) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ _ ℂ).compLinearMap fun u => LinearMap.proj (y' u)
  let ez : SInf F κ →ₗ[ℂ] ℂ := ⟨⟨fun f => f z, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have h2 := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ ez (PiTensorProduct.lift m))) this
  have hm : ∀ c : (κ → Fv F v) → ℂ, m (fun u => Function.update w v c u) = c y := fun c => by
    simp only [m, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.proj_apply]
    rw [Fintype.prod_eq_single (⟨v, Finset.mem_singleton_self v⟩ : ({v} : Finset (Pl F)))
      fun u hu => absurd (Subtype.ext (Finset.mem_singleton.1 u.2)) hu]
    simp [y']
  simp only [Fin.sum_univ_two, map_add, map_smul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, PiTensorProduct.lift.tprod,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, LinearMap.mul_apply', hm] at h2
  have h3 : g z * (a y - b y) = 0 := by
    change (1 : ℂ) • (g z * a y) + (-1 : ℂ) • (g z * b y) = 0 at h2
    simp only [smul_eq_mul] at h2
    linear_combination h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hz)

theorem opF_eq {κ : Type} [Fintype κ] {T} {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : φ₁ ∈ SB _) (h : Acts (evFin F v) T φ φ₁) :
    opF v T φ = φ₁ := by
  have ex : ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ φ₁ := ⟨φ₁, h₁, h⟩
  rw [opF, dif_pos ex]
  exact action_uniqueness F κ v T φ hφ _ _ ex.choose_spec.2 h

def dm {k : Type} [Field k] (Y Z : Matrix (Fin n) (Fin d) k) : k := ofM Y ⬝ᵥ ofM Z

def Hv (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) (u : Matrix (Fin n) (Fin d) (AE F E)) (φ : Fl F v n d) : Fl F v n d :=
  schr (psiV ψ v) (locW v (M.co.e u)) φ

theorem acts_Hv {u} (hu : At (evFin F v) u) (φ : Fl F v n d) : Acts (evFin F v) (M.co.rho ψ u) φ (Hv M ψ v u φ) :=
  adjoint_statement.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ

theorem Hv_mem (hψ : IsStd ψ) (u) {φ : Fl F v n d} (h : φ ∈ SB _) : Hv M ψ v u φ ∈ SB _ :=
  PositivityTheory.ThKH.Evl.schr_mem ((adjoint_statement.psi F ψ hψ).2 v).1 _ h

structure Lin (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (c₁ c₂ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (Fv F v))
    (ι : Fl F v n d →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) : Prop where
  bij : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _)
  act : ∀ u, At (evFin F v) u → dm (c₁ u) (c₂ u) = 0 → ∀ φ ∈ SB _,
    ι (Hv M ψ v u φ) = fun Y => psiV ψ v (dm Y (c₂ u)) * ι φ (Y + c₁ u)
  sur : ∀ P Q, ∃ u, At (evFin F v) u ∧ c₁ u = P ∧ c₂ u = Q
  vac : ι (M.vac v) = intInd v

theorem lin_of (hψ : IsStd ψ) {π₁ π₀ : AE F E →+* Fv F v} {c₁ c₂ ι} (hι : M.IsLin ψ π₁ π₀ c₁ ι) (hv : ι (M.vac v) = intInd v)
    (hs : ∀ x u, At (evFin F v) x → x.map π₀ = 0 →
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u = sgl v (dm (c₁ x) (c₂ u)))
    (dec : ∀ u, At (evFin F v) u → ∃ u₁ u₀, At (evFin F v) u₁ ∧ At (evFin F v) u₀ ∧ u = u₁ + u₀ ∧ u₁.map π₀ = 0 ∧ u₀.map π₁ = 0 ∧
      c₁ u₁ = c₁ u ∧ c₂ u₀ = c₂ u)
    (sur : ∀ P Q, ∃ u, At (evFin F v) u ∧ c₁ u = P ∧ c₂ u = Q) : Lin M ψ v c₁ c₂ ι := by
  refine ⟨hι.bij, fun u hu h0 φ hφ => funext fun Y => ?_, sur, hv⟩
  obtain ⟨u₁, u₀, a1, a0, rfl, b1, b0, e1, e0⟩ := dec u hu
  have e : Hv M ψ v (u₁ + u₀) φ = Hv M ψ v u₁ (Hv M ψ v u₀ φ) := by
    have f := congrArg (evFin F v) ((M.co.form u₁ u₀).symm.trans (hs u₁ u₀ a1 b1))
    rw [ev_sgl, e1, e0, h0, map_sub, ev_dot, ev_dot] at f
    rw [Hv, Hv, Hv, KCo.schr_schr, map_add, locW_add]
    erw [f]
    simp
  obtain ⟨x, hx, x1, -⟩ := sur (Y + c₁ u₁) 0
  obtain ⟨x₁, x₀, xa, -, -, xb, -, xe, -⟩ := dec x hx
  rw [e, hι.trans u₁ a1 b1 _ (Hv_mem hψ _ hφ) _ (Hv_mem hψ _ (Hv_mem hψ _ hφ)) (acts_Hv a1 _), ← x1, ← xe,
    hι.mult u₀ a0 b0 φ hφ _ (Hv_mem hψ _ hφ) (acts_Hv a0 _) x₁ xa xb, hs x₁ u₀ xa xb, xe, x1, e1, e0]
  congr 1
  show psiV ψ v _ = _
  congr 1
  rw [dm, show ofM (Y + c₁ (u₁ + u₀)) = ofM Y + ofM (c₁ (u₁ + u₀)) from rfl, add_dotProduct]
  rw [show ofM (c₁ (u₁ + u₀)) ⬝ᵥ ofM (c₂ (u₁ + u₀)) = 0 from h0, add_zero]; rfl

variable (t) in

def cW (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (u : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin d) (Fv F v) :=
  (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ

variable (σ t X W) in

def cB (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (u : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin d) (Fv F v) :=
  -(b.1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ * c.1)

variable {b : GL (Fin n) (Fv F v)} {c : GL (Fin d) (Fv F v)}

theorem symp_c (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {u} (hu : At (evFin F v) u) (u') :
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u u' =
      sgl v (dm (cW t b c u) (cB σ t X W b c u') - dm (cW t b c u') (cB σ t X W b c u)) := by
  have key : ∀ U N : Matrix (Fin n) (Fin d) (Fv F v), dm ((b⁻¹).1 * U * (c⁻¹).1ᵀ) (-(b.1ᵀ * N * c.1)) = -(ofM (-N) ⬝ᵥ ofM (-U)) := by
    intro U N
    rw [dm, dotProduct_comm (ofM (-N)), dot_ofM, dot_ofM]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, transpose_neg, neg_neg, trace_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (b⁻¹).1ᵀ, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul, trace_mul_comm]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [symp_eq h hG hu, coord, coord, incM_map h, incM_map h]
  congr 1
  have e : ∀ w : Matrix (Fin n) (Fin d) (AE F E), cB σ t X W b c w =
      -(b.1ᵀ * (X.J.map t * w.map (piW (t.comp σ)) * (W.J.map t)ᵀ) * c.1) := fun w => by simp only [cB, Matrix.mul_assoc]
  rw [e, e, cW, cW, key, key]
  ring

theorem dec_c (h : IsSec σ t sec) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u) :
    u = secM sec (u.map (piW t)) 0 + secM sec 0 (u.map (piW (t.comp σ))) :=
  h.extM (hu.kd_sub ((h.atM _ _).kd_add (h.atM _ _))) (by rw [Matrix.map_add _ (map_add _), h.fstM, h.fstM, add_zero])
    (by rw [Matrix.map_add _ (map_add _), h.sndM, h.sndM, zero_add])

theorem sur_c (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) (P Q) :
    ∃ u, At (evFin F v) u ∧ cW t b c u = P ∧ cB σ t X W b c u = Q := by
  obtain ⟨A, hA⟩ := hG.uA
  obtain ⟨B, hB⟩ := hG.uB
  rw [incM_map h] at hA hB
  refine ⟨secM sec (b.1 * P * c.1ᵀ) (-((A⁻¹).1 * (b⁻¹).1ᵀ * Q * (c⁻¹).1 * (B⁻¹).1ᵀ)), h.atM _ _, ?_, ?_⟩
  · rw [cW, h.fstM, cancel_lr]
  · rw [cB, h.sndM, ← hA, ← hB]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A.1, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc b.1ᵀ, ← transpose_mul, Units.inv_mul, transpose_one,
      Matrix.one_mul, ← Matrix.mul_assoc (B⁻¹).1ᵀ, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul, Units.inv_mul,
      Matrix.mul_one]

theorem local_splitting_linear_skew (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι} (hι : M.IsLinW ψ t b c ι)
    (hv : ι (M.vac v) = intInd v) : Lin M ψ v (cW t b c) (cB σ t X W b c) ι :=
  lin_of hψ hι hv (fun x u hx h0 => by
      rw [symp_c (b := b) (c := c) h hG hx, show cB σ t X W b c x = 0 by simp [cB, h0],
        show dm (cW t b c u) 0 = 0 from dotProduct_zero _, sub_zero])
    (fun u hu => ⟨_, _, h.atM _ _, h.atM _ _, dec_c h hu, h.sndM _ _, h.fstM _ _, by simp only [cW, h.fstM], by simp only [cB, h.sndM]⟩)
    (sur_c h hG)

theorem lin_Bar (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι} (hι : M.IsLinBar ψ t b c ι)
    (hv : ι (M.vac v) = intInd v) : Lin M ψ v (cB σ t X W b c) (fun u => -cW t b c u) ι :=
  lin_of hψ hι hv (fun x u hx h0 => by
      rw [symp_c (b := b) (c := c) h hG hx, show cW t b c x = 0 by simp [cW, h0]]
      congr 1
      show (0 : Fin n × Fin d → Fv F v) ⬝ᵥ _ - _ = ofM (cB σ t X W b c x) ⬝ᵥ (-ofM (cW t b c u))
      rw [zero_dotProduct, zero_sub, dotProduct_neg, dotProduct_comm]; rfl)
    (fun u hu => ⟨_, _, h.atM _ _, h.atM _ _, (dec_c h hu).trans (add_comm _ _), h.fstM _ _, h.sndM _ _, by simp only [cB, h.sndM],
      by simp only [cW, h.fstM]⟩)
    fun P Q => let ⟨u, a, b, c⟩ := sur_c h hG (-Q) P; ⟨u, a, c, by rw [b, neg_neg]⟩

open Classical in
theorem ev_loc {B : Base F E} (hψ : IsStd B.ψ) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev} (hl : IsEvLoc M M₁ e ei ev)
    {u u₁} (hu : At (evFin F v) u) (hu₁ : At (evFin F v) u₁)
    (H : ∀ Φ ∈ schA F _, e (M.co.rho B.ψ u Φ) = M₁.co.rho B.ψ u₁ (e Φ)) {φ : Fl F v n d} (hφ : φ ∈ SB _) :
    ev v (Hv M B.ψ v u φ) = Hv M₁ B.ψ v u₁ (ev v φ) := by
  obtain ⟨f, hf⟩ := DFunLike.ne_iff.1 hl.ne
  have sb : ∀ {x : Fl F v n d}, x ∈ SB _ → ∀ w, Function.update M.vac v x w ∈ SB _ := fun {x} hx w => by
    rcases eq_or_ne w v with rfl | h
    · rwa [Function.update_self]
    · rw [Function.update_of_ne h]; exact (g.vac w).1
  have cf : ∀ x : Fl F v n d, ∀ᶠ w in Filter.cofinite, Function.update M.vac v x w = M.vac w := fun x => by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw using Function.update_of_ne hw _ _
  have st : ∀ x : Fl F v n d, ∀ᶠ w in Filter.cofinite, Function.update M.vac v x w =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := fun x => by
    filter_upwards [cf x, g.std] with w h1 h2 using h1.trans h2
  have pe : ∀ {x : Fl F v n d}, x ∈ SB _ → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update M.vac v x)) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (Function.update M₁.vac v (ev v x)) := fun {x} hx => by
    rw [hl.pure f _ (sb hx) (cf x)]
    congr 1
    funext w
    rcases eq_or_ne w v with rfl | h
    · simp
    · rw [Function.update_of_ne h, Function.update_of_ne h, (hl.vac w).1]
  have em : ev v φ ∈ SB _ := (hl.vac v).2 ▸ Submodule.mem_map_of_mem hφ
  have a1 := (PositivityTheory.ThKF.pureAct F _ v (M.co.rho B.ψ u) f _ (sb hφ) (st φ)).2.2 (Hv M B.ψ v u φ)
    (by rw [Function.update_self]; exact acts_Hv hu φ)
  have a2 := (PositivityTheory.ThKF.pureAct F _ v (M₁.co.rho B.ψ u₁) (ei f) (Function.update M₁.vac v (ev v φ)) (fun w => by
      rcases eq_or_ne w v with rfl | h
      · rwa [Function.update_self]
      · rw [Function.update_of_ne h]; exact (g₁.vac w).1) (by
      filter_upwards [(Set.finite_singleton v).compl_mem_cofinite, g₁.std] with w hw h2 using
        (Function.update_of_ne hw _ _).trans h2)).2.2 (Hv M₁ B.ψ v u₁ (ev v φ)) (by rw [Function.update_self]; exact acts_Hv hu₁ _)
  rw [Function.update_idem] at a1 a2
  refine pure_cancel (fun w => (g₁.vac w).2.1) g₁.std v hf ?_
  rw [← pe (Hv_mem hψ u hφ), ← a2, ← pe hφ, ← H _ (pure_mem_schA f _ (sb hφ) (st φ)), a1]

theorem Hv_zero (φ : Fl F v n d) : Hv M ψ v 0 φ = φ := by
  rw [Hv, map_zero, show locW v (0 : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = (0, 0) from
    Prod.ext (funext fun _ => map_zero _) (funext fun _ => map_zero _), schr_zero']

def tmH {k : Type} [TopologicalSpace k] : (Fin n × Fin d → k) ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Z := Matrix.of fun i j => Z (i, j)
  invFun Y p := Y p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_id.matrix_elem _ _

theorem sb_comp {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) {Φ : B → ℂ} (h : Φ ∈ SB B) : Φ ∘ e ∈ SB A :=
  ⟨h.1.comp_continuous e.continuous, h.2.comp_homeomorph e⟩

theorem isPsi (hψ : IsStd ψ) (hu : PsiUnr ψ v) : IsPsi (psiV ψ v) :=
  ⟨((adjoint_statement.psi F ψ hψ).2 v).1, fun _ => GlobalTheory.StdCharFromIsStd.norm_psi hψ _, fun x => by
    have := hu x
    simp only [int_iff] at this
    exact this⟩

theorem intInd_eq (Z : Fin n × Fin d → Fv F v) : intInd v (tmH Z) = one _ Z := by
  classical
  simp only [intInd, one, ind, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, true_imp_iff, Set.indicator, map_one,
    Set.mem_setOf_eq, int_iff, Prod.forall]
  rfl

theorem ext_single {k : Type} [Field k] (jr : Fin n₁ → Fin n) (jc : Fin d₁ → Fin d) (i j) (s : k) :
    emb k jr * single i j s * (emb k jc)ᵀ = single (jr i) (jc j) s := by
  ext p q
  simp only [emb, Matrix.mul_apply, single_apply, ite_and, of_apply, transpose_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j (fun x _ hx => by simp [hx.symm]) (by simp)]
  simp only [eq_comm, if_true, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
  split_ifs <;> rfl

theorem ev_model [SecondCountableTopology (Fv F v)] [MeasurableSpace (Fv F v)] [BorelSpace (Fv F v)] {m : Measure (Fv F v)}
    (hm : IsVol m) {B : Base F E} (hψ : IsStd B.ψ) (hu : PsiUnr B.ψ v) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {i i' I e ei ev}
    (he : IsEv B M M₁ i i' I e) (hl : IsEvLoc M M₁ e ei ev) {c₁ c₂ ι c₁' c₂' ι₁} (L : Lin M B.ψ v c₁ c₂ ι)
    (L₁ : Lin M₁ B.ψ v c₁' c₂' ι₁) (jr : Fin n₁ → Fin n) (jc : Fin d₁ → Fin d) (P : Finset (Fin n × Fin d))
    (hE : ∀ z, c₁ (incM F i * z * (incM F i')ᵀ) = ext jr jc (c₁' z) ∧ c₂ (incM F i * z * (incM F i')ᵀ) = ext jr jc (c₂' z))
    (hT : ∀ p ∈ P, ∀ s, ∃ u ∈ I, At (evFin F v) u ∧ c₁ u = single p.1 p.2 s ∧ c₂ u = 0)
    (hM : ∀ p ∉ P, (∃ a b, p = (jr a, jc b)) ∨ ∀ s, ∃ u ∈ I, At (evFin F v) u ∧ c₁ u = 0 ∧ c₂ u = single p.1 p.2 s)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) :
    ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut P Z) + ext jr jc y) * wt P Z ∂(Measure.pi fun _ => m) := by
  obtain ⟨j, hj, hj'⟩ := kd_exists_inv L.bij
  have em : ∀ {φ : Fl F v n d}, φ ∈ SB _ → ev v φ ∈ SB _ := fun h => (hl.vac v).2 ▸ Submodule.mem_map_of_mem h
  let l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 0 ∘ₗ ι₁ ∘ₗ ev v ∘ₗ j ∘ₗ LinearMap.funLeft ℂ ℂ tmH.symm
  have hl1 : ∀ φ ∈ SB _, l (ι φ ∘ tmH) = ι₁ (ev v φ) 0 := fun φ h => by
    show ι₁ (ev v (j (ι φ))) 0 = _
    rw [hj' φ h]
  have d0 : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), dm Y 0 = 0 ∧ dm 0 Y = 0 := fun Y => ⟨dotProduct_zero _, zero_dotProduct _⟩
  have d1 : ∀ Y : Matrix (Fin n₁) (Fin d₁) (Fv F v), dm Y 0 = 0 ∧ dm 0 Y = 0 := fun Y => ⟨dotProduct_zero _, zero_dotProduct _⟩
  have x0 : ext jr jc (0 : Matrix _ _ (Fv F v)) = 0 := by simp [ext]
  have ae : ∀ {z : Matrix (Fin n₁) (Fin d₁) (AE F E)}, At (evFin F v) z → At (evFin F v) (incM F i * z * (incM F i')ᵀ) :=
    fun h => (h.kd_mul_left _).kd_mul_right _
  have inv : ∀ u, At (evFin F v) u → dm (c₁ u) (c₂ u) = 0 → (∀ φ ∈ SB _, ι₁ (ev v (Hv M B.ψ v u φ)) 0 = ι₁ (ev v φ) 0) →
      ∀ Φ ∈ SB (Fin n × Fin d → Fv F v), l (fun Y => psiV B.ψ v (Y ⬝ᵥ ofM (c₂ u)) * Φ (Y + ofM (c₁ u))) = l Φ := fun u a b c Φ hΦ => by
    obtain ⟨φ, h1, h2⟩ := L.bij.2.2 (sb_comp tmH.symm hΦ)
    have e1 : Φ = ι φ ∘ tmH := by rw [h2]; rfl
    rw [e1, hl1 φ h1, ← c φ h1, ← hl1 _ (Hv_mem hψ u h1), L.act u a b φ h1]
    rfl
  have invI : ∀ u ∈ I, At (evFin F v) u → ∀ φ ∈ SB _, ι₁ (ev v (Hv M B.ψ v u φ)) 0 = ι₁ (ev v φ) 0 := fun u hI a φ h => by
    rw [ev_loc hψ g g₁ hl a (u₁ := 0) (fun _ _ => smul_zero _) (fun Φ hΦ => by
      rw [he.inv u hI Φ hΦ, Darboux.rho, map_zero]; exact (schr_zero' _ _).symm) h, Hv_zero]
  have sg : ∀ (p : Fin n × Fin d) (s : Fv F v), ofM (single p.1 p.2 s) = Pi.single p s := fun p s => funext fun q => by
    simp [ofM, single_apply, Pi.single_apply, Prod.ext_iff, eq_comm]
  have hp := isPsi hψ hu
  have key := evInt hm hp P l (fun Z hZ => ?_) (fun Z hZ => ?_) (by
    rw [← funext intInd_eq, ← L.vac]
    refine (hl1 _ (g.vac v).1).trans ?_
    rw [(hl.vac v).1, L₁.vac]
    simp [intInd, Set.indicator, zero_mem])
  · obtain ⟨z, a, b, c⟩ := L₁.sur y 0
    have e1 := congrFun (L₁.act z a (by rw [c, (d1 _).1]) _ (em hφ)) 0
    rw [c, (d1 _).1, b, zero_add, AddChar.map_zero_eq_one, one_mul] at e1
    rw [← e1, ← ev_loc hψ g g₁ hl (ae a) a (he.Heisenberg₂ z) hφ, ← hl1 _ (Hv_mem hψ _ hφ),
      key _ (sb_comp tmH (L.bij.1 (Hv_mem hψ _ hφ))), L.act _ (ae a) (by rw [(hE z).2, c, x0, (d0 _).1]) φ hφ, (hE z).1, (hE z).2, b, c, x0]
    simp only [Function.comp, (d0 _).1, AddChar.map_zero_eq_one, one_mul]
    rfl
  · let S : AddSubmonoid (Fin n × Fin d → Fv F v) :=
      { carrier := {Z | ∀ Φ ∈ SB (Fin n × Fin d → Fv F v), l (fun Y => Φ (Y + Z)) = l Φ}
        zero_mem' := fun Φ _ => by simp
        add_mem' := fun {a b} ha hb Φ hΦ => by
          rw [← hb Φ hΦ, ← ha (fun Y => Φ (Y + b)) (sb_comp (Homeomorph.addRight b) hΦ)]
          simp [add_assoc] }
    show Z ∈ S
    rw [← Finset.univ_sum_single Z]
    refine S.sum_mem fun p _ => ?_
    by_cases hP : p ∈ P
    · obtain ⟨u, hI, a, b, c⟩ := hT p hP (Z p)
      intro Φ hΦ
      have := inv u a (by rw [c, (d0 _).1]) (invI u hI a) Φ hΦ
      rw [b, c, sg, show ofM (0 : Matrix (Fin n) (Fin d) (Fv F v)) = 0 from rfl] at this
      simpa using this
    · rw [hZ p hP, Pi.single_zero]; exact S.zero_mem
  · let S : AddSubmonoid (Fin n × Fin d → Fv F v) :=
      { carrier := {Z | ∀ Φ ∈ SB (Fin n × Fin d → Fv F v), l (fun Y => psiV B.ψ v (Y ⬝ᵥ Z) * Φ Y) = l Φ}
        zero_mem' := fun Φ _ => by simp
        add_mem' := fun {a b} ha hb Φ hΦ => by
          have := PositivityTheory.ThKH.Evl.schr_mem hp.cont (0, b) hΦ
          rw [show schr (psiV B.ψ v) (0, b) Φ = fun Y => psiV B.ψ v (Y ⬝ᵥ b) * Φ Y from funext fun _ => by simp [schr]] at this
          rw [← hb Φ hΦ, ← ha _ this]
          simp [AddChar.map_add_eq_mul, mul_assoc] }
    show Z ∈ S
    rw [← Finset.univ_sum_single Z]
    refine S.sum_mem fun p _ => ?_
    by_cases hP : p ∈ P
    · rw [hZ p hP, Pi.single_zero]; exact S.zero_mem
    intro Φ hΦ
    have o0 : ofM (0 : Matrix (Fin n) (Fin d) (Fv F v)) = 0 := rfl
    rcases hM p hP with ⟨a, b, rfl⟩ | h
    · obtain ⟨z, x1, x2, x3⟩ := L₁.sur 0 (single a b (Z (jr a, jc b)))
      have := inv _ (ae x1) (by rw [(hE z).1, x2, x0, (d0 _).2]) (fun φ h => by
        rw [ev_loc hψ g g₁ hl (ae x1) x1 (he.Heisenberg₂ z) h, L₁.act z x1 (by rw [x2, (d1 _).2]) _ (em h), x2]
        simp [(d1 _).2]) Φ hΦ
      rw [(hE z).1, (hE z).2, x2, x3, x0, ext, ext_single, sg (jr a, jc b), o0] at this
      simpa using this
    · obtain ⟨u, hI, a, b, c⟩ := h (Z p)
      have := inv u a (by rw [b, (d0 _).2]) (invI u hI a) Φ hΦ
      rw [b, c, sg, o0] at this
      simpa using this

end PositivityTheory.ThKG.Std
