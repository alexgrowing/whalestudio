import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDerivativeExistence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGaussianVacuaSpanOfVacuumEquations
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblPolArch

open scoped Classical
open GlobalTheory.HeisDer GlobalTheory.RealLift GlobalTheory.ThK.PlaneEv

section Gen

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Dop (a b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →L[ℂ] SInf F κ :=
  LineDeriv.lineDerivOpCLM ℂ (SInf F κ) a -
    (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((trL b x : ℝ) : ℂ))

theorem Dop_apply (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) :
    Dop a b f x = dH a b f x := by
  have htg : Function.HasTemperateGrowth fun x : κ → mixedEmbedding.mixedSpace F => ((trL b x : ℝ) : ℂ) :=
    (Complex.ofRealCLM.comp (trL b)).hasTemperateGrowth
  simp only [Dop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, SchwartzMap.sub_apply,
    SchwartzMap.smul_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul]
  simp only [trL_apply, dotProduct, dH]
  ring

theorem sd_schr {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) :
    SD (fun t => schr ψ (realAd F t • w)) f (Dop (fun i => evI F (w.1 i)) (fun i => evI F (w.2 i)) f) := by
  intro g hg l hl
  obtain ⟨T, hT⟩ := hl g hg
  let d : Darboux (fun w w' : (κ → AF F) × (κ → AF F) => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ :=
    ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩
  have h := hasDerivAt_heis (fun i => evI F (w.1 i)) (trL (fun i => evI F (w.2 i)))
    (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((fun i => evI F (w.1 i)) ⬝ᵥ (fun i => evI F (w.2 i)))) f T
  rw [hT]
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · simp only [Dop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  · have := rho_pureA d ψ hψ w t f g
    change l (d.rho ψ (realAd F t • w) (pureA F f g)) = _
    rw [this, hT]
    rfl

def bx (f₁ f₂ : SInf F κ) : SInf F (κ ⊕ κ) :=
  (GlobalTheory.SchwartzBox.exists_schwartz_box f₁ (GlobalTheory.ConjSch.conjSchwartz f₂)).choose

theorem bx_apply (f₁ f₂ : SInf F κ) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    bx f₁ f₂ x = f₁ (x ∘ Sum.inl) * starRingEnd ℂ (f₂ (x ∘ Sum.inr)) :=
  (GlobalTheory.SchwartzBox.exists_schwartz_box f₁ (GlobalTheory.ConjSch.conjSchwartz f₂)).choose_spec x

theorem bx_add_left (f f' g : SInf F κ) : bx (f + f') g = bx f g + bx f' g := by
  ext x; simp only [SchwartzMap.add_apply, bx_apply]; ring

theorem bx_smul_left (c : ℂ) (f g : SInf F κ) : bx (c • f) g = c • bx f g := by
  ext x; simp only [SchwartzMap.smul_apply, bx_apply, smul_eq_mul]; ring

theorem bx_add_right (f g g' : SInf F κ) : bx f (g + g') = bx f g + bx f g' := by
  ext x; simp only [SchwartzMap.add_apply, bx_apply, map_add]; ring

theorem bx_smul_right (c : ℂ) (f g : SInf F κ) : bx f (c • g) = starRingEnd ℂ c • bx f g := by
  ext x; simp only [SchwartzMap.smul_apply, bx_apply, smul_eq_mul, map_mul]; ring

theorem bx_zero_left (g : SInf F κ) : bx 0 g = 0 := by
  ext x; simp [bx_apply]

theorem bx_zero_right (f : SInf F κ) : bx f 0 = 0 := by
  ext x; simp [bx_apply]

theorem hasFDerivAt_restr {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) (f : SchwartzMap (κ → V) ℂ) (x : ι → V) :
    HasFDerivAt (fun y : ι → V => f (y ∘ e)) ((fderiv ℝ f (x ∘ e)).comp (GlobalTheory.SchwartzBox.restr V e)) x :=
  HasFDerivAt.comp (g := f) (f := GlobalTheory.SchwartzBox.restr V e) x
    f.differentiableAt.hasFDerivAt (GlobalTheory.SchwartzBox.restr V e).hasFDerivAt

theorem Dop_bx (a₁ a₂ b₁ b₂ : κ → mixedEmbedding.mixedSpace F) (f₁ f₂ : SInf F κ) :
    Dop (Sum.elim a₁ a₂) (Sum.elim b₁ (-b₂)) (bx f₁ f₂) = bx (Dop a₁ b₁ f₁) f₂ + bx f₁ (Dop a₂ b₂ f₂) := by
  ext x
  have e : ⇑(bx f₁ f₂) = fun x => f₁ (x ∘ Sum.inl) * starRingEnd ℂ (f₂ (x ∘ Sum.inr)) := funext (bx_apply f₁ f₂)
  have h1 : HasFDerivAt (fun y : κ ⊕ κ → mixedEmbedding.mixedSpace F => f₁ (y ∘ Sum.inl))
      ((fderiv ℝ f₁ (x ∘ Sum.inl)).comp (GlobalTheory.SchwartzBox.restr _ Sum.inl)) x :=
    hasFDerivAt_restr Sum.inl f₁ x
  have h2 : HasFDerivAt (fun y : κ ⊕ κ → mixedEmbedding.mixedSpace F => starRingEnd ℂ (f₂ (y ∘ Sum.inr)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f₂ (x ∘ Sum.inr)).comp (GlobalTheory.SchwartzBox.restr _ Sum.inr))) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x
      (hasFDerivAt_restr Sum.inr f₂ x)
  have h3 := (h1.mul h2).fderiv
  rw [SchwartzMap.add_apply, bx_apply, bx_apply, Dop_apply, Dop_apply, Dop_apply, dH, dH, dH, bx_apply, e]
  erw [h3]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    GlobalTheory.SchwartzBox.restr_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, smul_eq_mul, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, map_add, map_neg, map_sub, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Function.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    map_ofNat]
  push_cast
  ring

theorem Dop_neg (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) : Dop (-a) (-b) f = -Dop a b f := by
  ext x
  rw [SchwartzMap.neg_apply, Dop_apply, Dop_apply]
  simp only [dH, map_neg, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  push_cast
  ring

theorem Dop_zero (f : SInf F κ) : Dop 0 0 f = 0 := by
  ext x
  rw [Dop_apply]
  simp [dH]

theorem pureA_add (f f' : SInf F κ) (g : (κ → Af F) → ℂ) : pureA F (f + f') g = pureA F f g + pureA F f' g := by
  funext x; simp [pureA, add_mul]

theorem pureA_smul (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) : pureA F (c • f) g = c • pureA F f g := by
  funext x; simp [pureA, mul_assoc]

theorem pureA_mem (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

end Gen

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def Dm (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
  Dop (fun i => evI F ((M.co.e u).1 i)) (fun i => evI F ((M.co.e u).2 i))

theorem sd_Dm (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : SInf F (Fin n × Fin d)) : SD (M.heisLine ψ u) f (Dm M u f) := by
  have e : M.heisLine ψ u = fun t => schr ψ (realAd F t • M.co.e u) := by
    funext t; simp only [Model.heisLine, Darboux.rho, map_smul]
  rw [e]
  exact sd_schr hψ _ f

theorem actsD_Dm (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : SInf F (Fin n × Fin d)) : ActsD (evI F) (M.heisLine ψ u) f (Dm M u f) :=
  (actsLaws F _ f (Dm M u f) f).1 _ (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr]) (sd_Dm M hψ u f)

theorem eq_Dm (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {u : Matrix (Fin n) (Fin d) (AE F E)}
    {f f₁ : SInf F (Fin n × Fin d)} (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ = Dm M u f :=
  (actsLaws F _ f f₁ (Dm M u f)).2.2.1 _ h (actsD_Dm M hψ u f)

theorem Dm_neg (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    Dm M (-u) f = -Dm M u f := by
  rw [Dm, Dm, ← Dop_neg, map_neg]
  congr 2 <;> funext i <;> exact map_neg (evH F) _

theorem Dm_zero (M : Model σ X W) (f : SInf F (Fin n × Fin d)) : Dm M 0 f = 0 := by
  rw [Dm, map_zero, ← Dop_zero f]
  congr 2 <;> funext i <;> exact map_zero (evH F)

def algN (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ' | ∃ (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → Af F) → ℂ),
    f ∈ M.Pol ψ τ ∧ g ∈ SB (Fin n × Fin d → Af F) ∧ Φ' = pureA F f g}

theorem algN_deriv (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) {Ψ Ψ' : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ algN M ψ τ)
    (h : ∀ x, HasDerivAt (fun t => M.heisLine ψ u t Ψ x) (Ψ' x) 0) : Ψ' ∈ algN M ψ τ := by
  have key : ∃ Ψ₁ ∈ algN M ψ τ, ∀ x, HasDerivAt (fun t => M.heisLine ψ u t Ψ x) (Ψ₁ x) 0 := by
    clear h
    induction hΨ using Submodule.span_induction with
    | mem Ψ hm =>
      obtain ⟨f, g, hf, hg, rfl⟩ := hm
      refine ⟨pureA F (Dm M u f) g, Submodule.subset_span ⟨_, g, ?_, hg, rfl⟩, fun x => ?_⟩
      · exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (actsD_Dm M hψ u f)
      · exact sd_Dm M hψ u f g hg _ (eval_mem_adm x)
    | zero =>
      refine ⟨0, zero_mem _, fun x => ?_⟩
      simpa [Model.heisLine, Darboux.rho, schr] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    | add a b _ _ ha hb =>
      obtain ⟨a₁, ha₁, ha⟩ := ha
      obtain ⟨b₁, hb₁, hb⟩ := hb
      refine ⟨a₁ + b₁, add_mem ha₁ hb₁, fun x => ?_⟩
      refine ((ha x).add (hb x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp [Model.heisLine, Darboux.rho, schr, mul_add]
    | smul c a _ ha =>
      obtain ⟨a₁, ha₁, ha⟩ := ha
      refine ⟨c • a₁, Submodule.smul_mem _ c ha₁, fun x => ?_⟩
      refine ((ha x).const_mul c).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [Model.heisLine, Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
      ring
  obtain ⟨Ψ₁, h₁, h₂⟩ := key
  rwa [show Ψ' = Ψ₁ from funext fun x => (h x).unique (h₂ x)]

theorem algN_sum (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ algN M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (g : Fin m → ((Fin n × Fin d → Af F) → ℂ)),
      (∀ i, f i ∈ M.Pol ψ τ ∧ g i ∈ SB (Fin n × Fin d → Af F)) ∧ Ψ = ∑ i, pureA F (f i) (g i) := by
  obtain ⟨m, c, p, hp⟩ := Submodule.mem_span_set'.mp hΨ
  choose f g hf hg hp₀ using fun i => (p i).2
  refine ⟨m, fun i => c i • f i, g, fun i => ⟨Submodule.smul_mem _ _ (hf i), hg i⟩, ?_⟩
  rw [← hp]
  exact Finset.sum_congr rfl fun i _ => by rw [hp₀ i, pureA_smul]

theorem topC_smul (a : AF F) (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : topC (a • u) = a • topC u := rfl

theorem botC_smul (a : AF F) (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : botC (a • u) = a • botC u := rfl

theorem dblE_smul (M : Model σ X W) (a : AF F) (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) :
    dblE M.co (a • u) = a • dblE M.co u := by
  simp only [dblE, topC_smul, botC_smul, map_smul]
  refine Prod.ext ?_ ?_ <;> funext i <;> rcases i with i | i <;> simp

theorem at_topC {u : Matrix (Fin n) (Fin (d + d)) (AE F E)} (hu : At (evI F) u) : At (evI F) (topC u) :=
  fun a ha => by rw [← topC_smul, hu a ha]; rfl

theorem at_botC {u : Matrix (Fin n) (Fin (d + d)) (AE F E)} (hu : At (evI F) u) : At (evI F) (botC u) :=
  fun a ha => by rw [← botC_smul, hu a ha]; rfl

def glue (u₁ u₂ : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin (d + d)) (AE F E) :=
  (Matrix.fromCols u₁ u₂).submatrix id finSumFinEquiv.symm

theorem topC_glue (u₁ u₂ : Matrix (Fin n) (Fin d) (AE F E)) : topC (glue u₁ u₂) = u₁ := by
  ext i j; simp [topC, glue]

theorem botC_glue (u₁ u₂ : Matrix (Fin n) (Fin d) (AE F E)) : botC (glue u₁ u₂) = u₂ := by
  ext i j; simp [botC, glue, -Fin.natAdd_eq_addNat]

theorem at_glue {u₁ u₂ : Matrix (Fin n) (Fin d) (AE F E)} (h₁ : At (evI F) u₁) (h₂ : At (evI F) u₂) :
    At (evI F) (glue u₁ u₂) := by
  intro a ha
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j
  · simpa [glue] using congrFun (congrFun (h₁ a ha) i) j
  · simpa [glue, -Fin.natAdd_eq_addNat] using congrFun (congrFun (h₂ a ha) i) j

theorem mul_blk_inl (A : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin (d + d)) ℂ) (θ θ' : Matrix (Fin d) (Fin d) ℂ) :
    (A * U * (blkMat finSumFinEquiv θ θ')ᵀ).submatrix id (finSumFinEquiv ∘ Sum.inl) =
      A * U.submatrix id (finSumFinEquiv ∘ Sum.inl) * θᵀ := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.mul_apply]
  simp [blkMat, Matrix.mul_apply, -Fin.natAdd_eq_addNat]

theorem mul_blk_inr (A : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin (d + d)) ℂ) (θ θ' : Matrix (Fin d) (Fin d) ℂ) :
    (A * U * (blkMat finSumFinEquiv θ θ')ᵀ).submatrix id (finSumFinEquiv ∘ Sum.inr) =
      A * U.submatrix id (finSumFinEquiv ∘ Sum.inr) * θ'ᵀ := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.mul_apply]
  simp [blkMat, Matrix.mul_apply, -Fin.natAdd_eq_addNat]

end Model

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {W₂ : Spc F E (d + d)} (M : Model σ X W) (M₂ : Model σ X W₂) {ψ : AddChar (AF F) ℂ}
  (τ : ∀ w : InfinitePlace F, EmbOver E w)
  (e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ))

theorem hasDerivAt_e (hψ : IsStd ψ)
    (hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d))
    (hint : ∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr ψ (dblE M.co u) Ψ) = M₂.co.rho ψ u (e Ψ))
    (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) (f₁ f₂ : SInf F (Fin n × Fin d))
    {g : (Fin n × Fin d ⊕ Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) (x : Fin n × Fin (d + d) → AF F) :
    HasDerivAt (fun t => M₂.heisLine ψ u t (e (pureA F (bx f₁ f₂) g)) x)
      (e (pureA F (bx (Dm M (topC u) f₁) f₂ + bx f₁ (Dm M (botC u) f₂) : SInf F _) g) x) 0 := by
  have h := sd_schr hψ (dblE M.co u) (bx f₁ f₂) g hg _ (hadm _ (eval_mem_adm x))
  have e1 : (fun i => evI F ((dblE M.co u).1 i)) =
      Sum.elim (fun i => evI F ((M.co.e (topC u)).1 i)) (fun i => evI F ((M.co.e (botC u)).1 i)) := by
    funext i; rcases i with i | i <;> rfl
  have e2 : (fun i => evI F ((dblE M.co u).2 i)) =
      Sum.elim (fun i => evI F ((M.co.e (topC u)).2 i)) (-fun i => evI F ((M.co.e (botC u)).2 i)) := by
    funext i
    rcases i with i | i
    · rfl
    · exact map_neg (evH F) _
  rw [e1, e2, Dop_bx] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, Model.heisLine]
  rw [← dblE_smul, hint _ _ (pureA_mem _ hg)]

theorem gauss_mem (hσ : IsCMExt F E σ) (hψ : IsStd ψ) (hX : ∀ w, X.θ w * X.θ w = 1) (hW : ∀ w, W.θ w * W.θ w = 1)
    (hθ : ∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w))
    (hmap : ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e Ψ ∈ schA F (Fin n × Fin (d + d)))
    (hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d))
    (hint : ∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr ψ (dblE M.co u) Ψ) = M₂.co.rho ψ u (e Ψ))
    {f₁ f₂ : SInf F (Fin n × Fin d)} (h₁ : M.IsGauss ψ τ f₁) (h₂ : M.IsGauss ψ τ f₂)
    {g : (Fin n × Fin d ⊕ Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) :
    e (pureA F (bx f₁ f₂) g) ∈ algN M₂ ψ τ := by
  by_cases h0 : f₁ = 0
  · have : pureA F (bx f₁ f₂) g = 0 := by
      rw [h0, bx_zero_left]; funext x; simp [pureA]
    rw [this, map_zero]
    exact zero_mem _
  obtain ⟨z, rfl⟩ := GlobalTheory.RealDict.FockMap.gauss_line M ψ τ hσ hψ hX hW f₂ f₁ h₁ h0 h₂
  rw [bx_smul_right, pureA_smul, map_smul]
  refine Submodule.smul_mem _ _ ?_
  refine GlobalTheory.VacFactor.mem_span_of_isGaussEq M₂ ψ τ hψ _ (hmap _ (pureA_mem _ hg)) ?_
  obtain ⟨ε, hε⟩ := h₁
  refine ⟨ε, fun u u' hu hu' huu x => ?_⟩
  rw [(hasDerivAt_e M M₂ e hψ hadm hint u f₁ f₁ hg x).deriv, (hasDerivAt_e M M₂ e hψ hadm hint u' f₁ f₁ hg x).deriv]
  have a1 : Dm M (topC u') f₁ = Complex.I • Dm M (topC u) f₁ := by
    refine hε _ _ (at_topC hu) (at_topC hu') (fun w => ?_) _ _ (actsD_Dm M hψ _ _) (actsD_Dm M hψ _ _)
    have := congrArg (fun A : Matrix (Fin n) (Fin (d + d)) ℂ => A.submatrix id (finSumFinEquiv ∘ Sum.inl)) (huu w)
    simp only [hθ w, Matrix.submatrix_smul, Pi.smul_apply, mul_blk_inl] at this
    exact this
  have a2 : Dm M (-botC u') f₁ = Complex.I • Dm M (botC u) f₁ := by
    refine hε _ _ (at_botC hu) (fun a ha => by rw [smul_neg, at_botC hu' a ha, neg_zero]) (fun w => ?_) _ _
      (actsD_Dm M hψ _ _) (actsD_Dm M hψ _ _)
    have := congrArg (fun A : Matrix (Fin n) (Fin (d + d)) ℂ => A.submatrix id (finSumFinEquiv ∘ Sum.inr)) (huu w)
    simp only [hθ w, Matrix.submatrix_smul, Pi.smul_apply, mul_blk_inr, Matrix.transpose_neg, Matrix.mul_neg,
      smul_neg] at this
    rw [Matrix.map_neg _ (map_neg (piInf (τ w))), neg_eq_iff_eq_neg]
    exact this
  have a3 : Dm M (botC u') f₁ = (-Complex.I) • Dm M (botC u) f₁ := by
    rw [Dm_neg, neg_eq_iff_eq_neg] at a2
    rw [a2, neg_smul]
  rw [a1, a3, bx_smul_left, bx_smul_right, map_neg, Complex.conj_I, neg_neg, ← smul_add, pureA_smul, map_smul]
  rfl

theorem pol_mem (hσ : IsCMExt F E σ) (hψ : IsStd ψ) (hX : ∀ w, X.θ w * X.θ w = 1) (hW : ∀ w, W.θ w * W.θ w = 1)
    (hθ : ∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w))
    (hmap : ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e Ψ ∈ schA F (Fin n × Fin (d + d)))
    (hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d))
    (hint : ∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr ψ (dblE M.co u) Ψ) = M₂.co.rho ψ u (e Ψ))
    {g : (Fin n × Fin d ⊕ Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _)
    {f₁ f₂ : SInf F (Fin n × Fin d)} (h₁ : f₁ ∈ M.Pol ψ τ) (h₂ : f₂ ∈ M.Pol ψ τ) :
    e (pureA F (bx f₁ f₂) g) ∈ algN M₂ ψ τ := by
  have z0 : e (pureA F (0 : SInf F (Fin n × Fin d ⊕ Fin n × Fin d)) g) ∈ algN M₂ ψ τ := by
    have : pureA F (0 : SInf F (Fin n × Fin d ⊕ Fin n × Fin d)) g = 0 := by funext x; simp [pureA]
    rw [this, map_zero]
    exact zero_mem _
  have der : ∀ u₁ u₂, At (evI F) u₁ → At (evI F) u₂ → ∀ a b, e (pureA F (bx a b) g) ∈ algN M₂ ψ τ →
      e (pureA F (bx (Dm M u₁ a) b + bx a (Dm M u₂ b) : SInf F _) g) ∈ algN M₂ ψ τ := by
    intro u₁ u₂ hu₁ hu₂ a b hab
    refine algN_deriv M₂ hψ τ (at_glue hu₁ hu₂) hab fun x => ?_
    have := hasDerivAt_e M M₂ e hψ hadm hint (glue u₁ u₂) a b hg x
    rwa [topC_glue, botC_glue] at this
  have at0 : At (evI F) (0 : Matrix (Fin n) (Fin d) (AE F E)) := fun a _ => smul_zero a
  have step : ∀ a, M.IsGauss ψ τ a → e (pureA F (bx a f₂) g) ∈ algN M₂ ψ τ := by
    intro a ha
    let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
      { carrier := {b | e (pureA F (bx a b) g) ∈ algN M₂ ψ τ}
        add_mem' := fun {b b'} hb hb' => by
          change e (pureA F (bx a (b + b')) g) ∈ algN M₂ ψ τ
          rw [bx_add_right, pureA_add, map_add]
          exact add_mem hb hb'
        zero_mem' := by
          change e (pureA F (bx a 0) g) ∈ algN M₂ ψ τ
          rw [bx_zero_right]; exact z0
        smul_mem' := fun c b hb => by
          change e (pureA F (bx a (c • b)) g) ∈ algN M₂ ψ τ
          rw [bx_smul_right, pureA_smul, map_smul]
          exact Submodule.smul_mem _ _ hb }
    refine Submodule.mem_sInf.1 h₂ N ⟨fun b hb => gauss_mem M M₂ τ e hσ hψ hX hW hθ hmap hadm hint ha hb hg,
      fun u hu b hb b₁ hb₁ => ?_⟩
    have := der 0 u at0 hu a b hb
    rw [Dm_zero, bx_zero_left, zero_add, ← eq_Dm M hψ hb₁] at this
    exact this
  let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {a | e (pureA F (bx a f₂) g) ∈ algN M₂ ψ τ}
      add_mem' := fun {b b'} hb hb' => by
        change e (pureA F (bx (b + b') f₂) g) ∈ algN M₂ ψ τ
        rw [bx_add_left, pureA_add, map_add]
        exact add_mem hb hb'
      zero_mem' := by
        change e (pureA F (bx 0 f₂) g) ∈ algN M₂ ψ τ
        rw [bx_zero_left]; exact z0
      smul_mem' := fun c b hb => by
        change e (pureA F (bx (c • b) f₂) g) ∈ algN M₂ ψ τ
        rw [bx_smul_left, pureA_smul, map_smul]
        exact Submodule.smul_mem _ _ hb }
  refine Submodule.mem_sInf.1 h₁ N ⟨step, fun u hu a ha a₁ ha₁ => ?_⟩
  have := der u 0 hu at0 a f₂ ha
  rw [Dm_zero, bx_zero_right, add_zero, ← eq_Dm M hψ ha₁] at this
  exact this

end Main

theorem dbl_pol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ),
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) →
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE M.co u) Ψ) = co.rho B.ψ u (e Ψ)) →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin (d + d))) (g : Fin m → ((Fin n × Fin (d + d) → Af F) → ℂ)),
        (∀ i, f i ∈ Model.Pol ({ co := co, vac := fun _ _ => 0, μ := 0, dom := ∅ } : Model σ Xs W₂) B.ψ B.emb ∧
          g i ∈ SB (Fin n × Fin (d + d) → Af F)) ∧
        e (boxC Φ₁ Φ₂) = ∑ i, pureA F (f i) (g i) := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ _ _ hθ co _ _ _ e hbij hadm hint Φ₁ h₁ Φ₂ h₂
  set M₂ : Model σ Xs W₂ := { co := co, vac := fun _ _ => 0, μ := 0, dom := ∅ } with hM₂
  refine algN_sum M₂ B.ψ B.emb ?_
  have hfin : ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      (fun y : Fin n × Fin d → Af F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈ SB _ := fun φ hφ hv =>
    have hstd := (hv.and hP.good.std).mono fun v h => h.1.trans h.2
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hstd⟩
  induction h₁ using Submodule.span_induction with
  | mem Φ₁ h₁ =>
    obtain ⟨f₁, hf₁, φ₁, hφ₁, hv₁, rfl⟩ := h₁
    induction h₂ using Submodule.span_induction with
    | mem Φ₂ h₂ =>
      obtain ⟨f₂, hf₂, φ₂, hφ₂, hv₂, rfl⟩ := h₂
      have g₁ := hfin φ₁ hφ₁ hv₁
      have g₂ := hfin φ₂ hφ₂ hv₂
      have g₂' : (fun y : Fin n × Fin d → Af F => starRingEnd ℂ (∏ᶠ v, φ₂ v fun i => evalV F v (y i))) ∈ SB _ :=
        ⟨g₂.1.comp _, g₂.2.comp_left (map_zero _)⟩
      have key := pol_mem M M₂ B.emb e hP.base.cm hP.base.std (fun w => (hP.herm.cartan w).1)
        (fun w => (hP.skew.cartan w).1) hθ (fun Ψ hΨ => hbij.mapsTo hΨ) hadm hint (GlobalTheory.SchwartzBox.sb_box g₁ g₂') hf₁ hf₂
      convert key using 2
      funext x
      simp only [boxC, boxFun, pureA, bx_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Complex.star_def, map_mul]
      rw [mul_mul_mul_comm]
      rfl
    | zero =>
      have : boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) 0 = 0 := by funext x; simp [boxC, boxFun]
      rw [this, map_zero]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) (a + b) =
          boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) a + boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) b := by
        funext x; simp [boxC, boxFun, mul_add]
      rw [this, map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have : boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) (c • a) = star c • boxC (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ₁) a := by
        funext x; simp only [boxC, boxFun, Pi.smul_apply, smul_eq_mul, star_mul']; ring
      rw [this, map_smul]; exact Submodule.smul_mem _ _ ha
  | zero =>
    have : boxC 0 Φ₂ = 0 := by funext x; simp [boxC, boxFun]
    rw [this, map_zero]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : boxC (a + b) Φ₂ = boxC a Φ₂ + boxC b Φ₂ := by funext x; simp [boxC, boxFun, add_mul]
    rw [this, map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    have : boxC (c • a) Φ₂ = c • boxC a Φ₂ := by funext x; simp [boxC, boxFun, mul_assoc]
    rw [this, map_smul]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.DblPolArch

end
