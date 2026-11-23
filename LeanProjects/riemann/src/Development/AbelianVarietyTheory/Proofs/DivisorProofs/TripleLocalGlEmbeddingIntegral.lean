import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2IsometryStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblDiag

section Groups

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {β : Type} [Fintype β] [DecidableEq β]
  {J : Matrix β β E}

theorem fromBlocks_unit_left (k : UG c J) : (Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
    (Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1).map c = dbl J := by
  have hk : ((k : GL β E) : Matrix β β E)ᵀ * J * ((k : GL β E) : Matrix β β E).map c = J := k.2
  have h1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.map_zero _ (map_zero c), h1, Matrix.one_mul, Matrix.mul_one, hk]

theorem fromBlocks_unit_right (k : UG c J) : (Matrix.fromBlocks 1 0 0 ((k : GL β E) : Matrix β β E))ᵀ * dbl J *
    (Matrix.fromBlocks 1 0 0 ((k : GL β E) : Matrix β β E)).map c = dbl J := by
  have hk : ((k : GL β E) : Matrix β β E)ᵀ * J * ((k : GL β E) : Matrix β β E).map c = J := k.2
  have hn : ((k : GL β E) : Matrix β β E)ᵀ * (-J) * ((k : GL β E) : Matrix β β E).map c = -J := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hk]
  have h1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.map_zero _ (map_zero c), h1, Matrix.one_mul, Matrix.mul_one, hn]

def diagL (k : UG c J) : UG c (dbl J) :=
  ⟨⟨Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1, Matrix.fromBlocks (((k : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1,
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]⟩, fromBlocks_unit_left c k⟩

def diagR (k : UG c J) : UG c (dbl J) :=
  ⟨⟨Matrix.fromBlocks 1 0 0 ((k : GL β E) : Matrix β β E), Matrix.fromBlocks 1 0 0 (((k : GL β E)⁻¹ : GL β E) : Matrix β β E),
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]⟩, fromBlocks_unit_right c k⟩

end Groups

section Local

variable {F : Type} [Field F] [NumberField F]

theorem boxFun_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem conj_mem_SB {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => starRingEnd ℂ (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (map_zero _)⟩

theorem tens_boxFun (v : Pl F) {κ κ' : Type} (φ₁ : (κ → Fv F v) → ℂ) (φ₂ : (κ' → Fv F v) → ℂ)
    (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens (evFin F v) φ₁ r₁) (tens (evFin F v) φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem rest_boxFun (v : Pl F) {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ}
    {r₁ : (κ → AF F) → ℂ} {r₂ : (κ' → AF F) → ℂ} (h₁ : Rest (evFin F v) φ₁ r₁) (h₂ : Rest (evFin F v) φ₂ r₂) :
    Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inr i)
    show r₁ ((x + z) ∘ Sum.inl) * r₂ ((x + z) ∘ Sum.inr) = r₁ (x ∘ Sum.inl) * r₂ (x ∘ Sum.inr)
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h₁.1 _ _ hz1, h₂.1 _ _ hz2]
  · rw [tens_boxFun]
    exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h₁.2 _ h₂.2

theorem eq_of_tens_eq_of_ne (v : Pl F) {κ : Type} {ψ₁ ψ₂ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h0 : r x₀ ≠ 0)
    (h : tens (evFin F v) ψ₁ r = tens (evFin F v) ψ₂ r) : ψ₁ = ψ₂ := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hz : At (evFin F v) z := by
    intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [Pi.add_apply, z, map_add, GlobalTheory.LatVac.evFin_liftV]
    abel
  have e := congrFun h (x₀ + z)
  simp only [tens, hev, hr x₀ z hz] at e
  exact mul_right_cancel₀ h0 e

theorem acts_comp (v : Pl F) {κ : Type} [Fintype κ] {T₁ T₂ : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hT₂ : ∀ f ∈ schA F κ, T₂ f ∈ schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h₂ : Acts (evFin F v) T₂ φ φ₁) (h₁ : Acts (evFin F v) T₁ φ₁ φ₂) :
    Acts (evFin F v) (fun f => T₁ (T₂ f)) φ φ₂ := by
  intro r hr
  have e := h₂ r hr
  have hr₁ : Rest (evFin F v) φ₁ r := ⟨hr.1, e ▸ hT₂ _ hr.2⟩
  show T₁ (T₂ _) = _
  rw [e, h₁ r hr₁]

end Local

end GlobalTheory.DblDiag

namespace GlobalTheory.DblDiag

open Matrix

theorem diag_integral : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (cA σ) (dbl (incM F G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (p : UG (cA σ) (dbl (incM F G.V'.J))),
      ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks (mat (K g)) 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ'' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) (boxFun φ₁ φ₂) φ'' →
    ∀ μ : @MeasureTheory.Measure ((Fin a' × Fin (a + a')) → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫ x, φ'' (Sum.elim x x) ∂μ =
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) * ∫ x, φ₁ x * φ₂ x ∂μ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl hres g p hp
    φ₁ h₁ φ₂ h₂ φ'' h'' hact μ hμ
  set k := K g with hk
  let gd := diagL (cA σ) k
  let gd' := diagR (cA σ) k
  have hgd : ((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks (mat k) 0 0 1 := rfl
  have hgd' : ((gd' : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks 1 0 0 (mat k) := rfl
  have hpq : p = gd * gd' := by
    apply Subtype.ext; apply Units.ext
    rw [hp]
    show _ = Matrix.fromBlocks (mat k) 0 0 1 * Matrix.fromBlocks 1 0 0 (mat k)
    rw [Matrix.fromBlocks_multiply]; simp
  have hAt : At (evFin F v) (((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
    intro u hu
    have hk1 : u • (mat k - 1) = 0 := (hK g).1 u hu
    have e : Matrix.fromBlocks (mat k) 0 0 (1 : Matrix (Fin a') (Fin a') (AE F E)) - 1 =
        Matrix.fromBlocks (mat k - 1) 0 0 0 := by
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]; simp [sub_eq_add_neg]
    rw [hgd, e, Matrix.fromBlocks_smul]
    simp [hk1]

  have hSsb : ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ := fun φ hφ => (hS g φ hφ).1
  have hSlin : ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ' ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro φ hφ φ' hφ' c
    have hm : c • φ + φ' ∈ SB ((Fin a' × Fin (a + a')) → Fv F v) := (SB _).add_mem ((SB _).smul_mem c hφ) hφ'
    refine hι.bij.injOn (hSsb _ hm) ((SB _).add_mem ((SB _).smul_mem c (hSsb φ hφ)) (hSsb φ' hφ')) ?_
    rw [hint g _ hm, map_add, map_smul, map_add, map_smul, hint g φ hφ, hint g φ' hφ']
    funext Y
    simp only [GlobalTheory.SplitFlip.omB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hSnorm : ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun φ hφ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hT v k (hK g).1 φ (S g φ) hφ (hS g φ hφ).1 (hS g φ hφ).2 μ hμ

  have hL : ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd gd) (boxFun ψ₁ ψ₂) (boxFun (S g ψ₁) ψ₂) := by
    intro ψ₁ hψ₁ ψ₂ hψ₂
    obtain ⟨φ', -, hA⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v gd hAt _ (boxFun_mem_SB hψ₁ hψ₂)
    obtain ⟨r₁, hr₁, x₁, hx₁⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v ψ₁ hψ₁
    obtain ⟨r₂, hr₂, x₂, hx₂⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v ψ₂ hψ₂
    have hR := rest_boxFun v hr₁ hr₂
    have e := hA _ hR
    rw [tens_boxFun, hres k gd hgd _ hr₁.2 _ hr₂.2, (hS g ψ₁ hψ₁).2 r₁ hr₁, ← tens_boxFun] at e
    have h0 : boxFun r₁ r₂ (Sum.elim x₁ x₂) ≠ 0 := by
      simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]; exact mul_ne_zero hx₁ hx₂
    have e2 : φ' = boxFun (S g ψ₁) ψ₂ := eq_of_tens_eq_of_ne v hR.1 h0 e.symm
    rw [e2] at hA; exact hA

  set c : ℂ := (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) with hc
  set T₂ : ((Fin a' × Fin (a + a')) → Fv F v) → ℂ := fun x => c * starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x)
    with hT₂
  have hR' : Acts (evFin F v) (omd gd') (boxFun φ₁ φ₂) (boxFun φ₁ T₂) :=
    GlobalTheory.T.triple_local_gl_embedding_theta hP F E σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl hres g gd' hgd' φ₁ h₁ φ₂ h₂
  have hT₂sb : T₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v) :=
    (SB _).smul_mem c (conj_mem_SB (hSsb _ (conj_mem_SB h₂)))
  have hcomp : Acts (evFin F v) (fun f => omd gd (omd gd' f)) (boxFun φ₁ φ₂) (boxFun (S g φ₁) T₂) :=
    acts_comp v (fun f hf => hspl.pres gd' f hf) hR' (hL φ₁ h₁ T₂ hT₂sb)
  have hφ'' : φ'' = boxFun (S g φ₁) T₂ := by
    refine GlobalTheory.TensUniq.eq_of_tens_eq v (boxFun φ₁ φ₂) _ _ (boxFun_mem_SB h₁ h₂) fun r hr => ?_
    rw [← hact r hr, hpq, map_mul]
    exact hcomp r hr
  subst hφ''
  have e : (fun x => boxFun (S g φ₁) T₂ (Sum.elim x x)) =
      fun x => c * (S g φ₁ x * starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x)) := by
    funext x
    simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, hT₂]
    ring
  rw [show (∫ x, boxFun (S g φ₁) T₂ (Sum.elim x x) ∂μ) =
      ∫ x, c * (S g φ₁ x * starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x)) ∂μ from congrArg (fun f => ∫ x, f x ∂μ) e,
    MeasureTheory.integral_const_mul]
  rw [GlobalTheory.T.local_linear_operator_l2_isometry v (S g) hSsb hSlin μ hμ hSnorm φ₁ h₁ φ₂ h₂]

end GlobalTheory.DblDiag
