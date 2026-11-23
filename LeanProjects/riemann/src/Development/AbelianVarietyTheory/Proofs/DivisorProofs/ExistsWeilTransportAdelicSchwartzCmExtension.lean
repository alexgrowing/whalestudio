import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CtxExists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalCoordsCMStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTransformEqOrientedThetaFunctionCMStatement

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TransportF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ

theorem exists_transport {V W G : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Monoid G]
    (p : Submodule ℂ V) (Θ : p →ₗ[ℂ] W) (hΘ : Function.Injective Θ) (ω : G →* Module.End ℂ W)
    (hω : ∀ g, ∀ x ∈ LinearMap.range Θ, ω g x ∈ LinearMap.range Θ) :
    ∃ om : G →* Module.End ℂ V, ∀ g (x : p), ∃ h : om g x ∈ p, Θ ⟨om g x, h⟩ = ω g (Θ x) := by
  obtain ⟨q, hq⟩ := p.exists_isCompl
  let E := LinearEquiv.ofInjective Θ hΘ
  let A := Submodule.prodEquivOfIsCompl p q hq
  let r : G → Module.End ℂ p := fun g => E.symm.conj ((ω g).restrict (hω g))
  have hr : ∀ g x, Θ (r g x) = ω g (Θ x) := fun g x => by
    have : ∀ y : LinearMap.range Θ, Θ (E.symm y) = y := fun y => by
      conv_rhs => rw [← E.apply_symm_apply y]
      rfl
    simp only [r, LinearEquiv.conj_apply_apply, this]
    rfl
  have r1 : r 1 = 1 := LinearMap.ext fun x => hΘ (by rw [hr, map_one]; rfl)
  have rm : ∀ g h, r (g * h) = r g * r h := fun g h => LinearMap.ext fun x => hΘ (by
    rw [hr, map_mul, Module.End.mul_apply, Module.End.mul_apply, hr, hr])
  refine ⟨⟨⟨fun g => A.conj ((r g).prodMap LinearMap.id), ?_⟩, fun g h => ?_⟩, fun g x => ?_⟩
  · ext v
    simp [r1, LinearEquiv.conj_apply_apply, Module.End.one_eq_id]
  · ext v
    simp [rm, LinearEquiv.conj_apply_apply]
  · have h : A.conj ((r g).prodMap LinearMap.id) (x : V) = r g x := by
      simp [A, LinearEquiv.conj_apply_apply]
    refine ⟨by rw [MonoidHom.coe_mk, OneHom.coe_mk, h]; exact (r g x).2, ?_⟩
    rw [← hr]
    congr 1
    exact Subtype.ext h

theorem exists_transport' {V W G : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Monoid G]
    (p : Submodule ℂ V) (Θ : V → W) (P : W → Prop) (hadd : ∀ x ∈ p, ∀ y ∈ p, Θ (x + y) = Θ x + Θ y)
    (hsm : ∀ (c : ℂ) x, Θ (c • x) = c • Θ x) (hinj : ∀ x ∈ p, ∀ y ∈ p, Θ x = Θ y → x = y)
    (hon : ∀ f, P f ↔ ∃ x ∈ p, Θ x = f) (ω : G →* Module.End ℂ W) (hω : ∀ g f, P f → P (ω g f)) :
    ∃ om : G →* Module.End ℂ V, ∀ g, ∀ x ∈ p, om g x ∈ p ∧ Θ (om g x) = ω g (Θ x) := by
  let L : p →ₗ[ℂ] W :=
    { toFun := fun x => Θ x.1
      map_add' := fun x y => hadd _ x.2 _ y.2
      map_smul' := fun c x => hsm c x.1 }
  have hmem : ∀ f, f ∈ LinearMap.range L ↔ P f := fun f =>
    ⟨fun ⟨x, h⟩ => (hon f).2 ⟨x.1, x.2, h⟩, fun hf => let ⟨x, hx, h⟩ := (hon f).1 hf; ⟨⟨x, hx⟩, h⟩⟩
  obtain ⟨om, hom⟩ := exists_transport p L (fun x y h => Subtype.ext (hinj _ x.2 _ y.2 h)) ω
    fun g f hf => (hmem _).2 (hω g f ((hmem f).1 hf))
  exact ⟨om, fun g x hx => let ⟨h1, h2⟩ := hom g ⟨x, hx⟩; ⟨h1, h2⟩⟩

open scoped Classical in

theorem comp_mem_schA {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : (fun x : κ' → AF F => Φ (x ∘ σ)) ∈ GlobalTheory.WeilM.schA F κ' := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
      (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv
    let B : (κ' → Af F) ≃ₜ (κ → Af F) := (Homeomorph.piCongrLeft (Y := fun _ => Af F) σ).symm
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B,
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩
    rfl
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

theorem thV_add {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} {N : ℕ}
    (hR : IsTotallyReal F) (hψ : IsCharAF F ψ) {Φ Φ' : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (hΦ' : Decay Φ') :
    thV ψ (Φ + Φ') = thV ψ Φ + thV ψ Φ' := by
  funext w
  have hs : ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      Summable fun ξ : Fin N → F => GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i) := fun Φ hΦ => by
    refine Summable.of_norm ?_
    simp only [GlobalTheory.WeilM.schr, norm_mul, hψ.2.1, one_mul]
    exact (GlobalTheory.decay_integrable_periodise F N hR Φ hΦ).2.1 w.1
  rw [Pi.add_apply, thV, thV, thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.thetaSum,
    ← (hs Φ hΦ).tsum_add (hs Φ' hΦ')]
  exact tsum_congr fun ξ => mul_add _ _ _

theorem thV_injOn {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} {N : ℕ}
    (hR : IsTotallyReal F) (hψ : IsCharAF F ψ) {Φ Φ' : (Fin N → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N))
    (hΦ' : Φ' ∈ GlobalTheory.WeilM.schA F (Fin N)) (h : thV ψ Φ = thV ψ Φ') : Φ = Φ' := by
  obtain ⟨lam, ν, hC⟩ := GlobalTheory.SWQ.ctx_exists F hR ψ hψ N (half F N) half_ne_zero
  refine eq_of_theta_rho F N ψ lam ν _ hC Φ Φ' (GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ hΦ)
    (GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦ') fun x y => ?_
  have := congrFun h (x, y)
  rwa [thV_eq_th, thV_eq_th] at this

def contra {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] : GL n A →* GL n A where
  toFun g := ⟨(g⁻¹).1ᵀ, g.1ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp only [mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

theorem contra_rel {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (c : A →+* A) {G H J : Matrix n n A} {ξ x : A}
    (hGH : G * H = 1) (hx : IsUnit x) (hJ : ξ • J = x • H) (b : GL n A) (h0 : b.1ᵀ * J * b.1.map c = J) :
    (b⁻¹).1.map c * G * (b⁻¹).1ᵀ = G := by
  have hHG : H * G = 1 := mul_eq_one_comm.1 hGH
  have h1 : b.1ᵀ * H * b.1.map c = H := by
    have h2 : b.1ᵀ * (ξ • J) * b.1.map c = ξ • J := by rw [Matrix.mul_smul, Matrix.smul_mul, h0]
    rw [hJ, Matrix.mul_smul, Matrix.smul_mul] at h2
    exact hx.smul_left_cancel.1 h2
  have h3 : (b⁻¹).1.map c * b.1.map c = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h4 : (b⁻¹).1ᵀ * b.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h5 : (b⁻¹).1.map c * G * (b⁻¹).1ᵀ * H = 1 := by
    conv_lhs => rw [← h1]
    calc _ = (b⁻¹).1.map c * (G * (((b⁻¹).1ᵀ * b.1ᵀ) * H)) * b.1.map c := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h4, Matrix.one_mul, hGH, Matrix.mul_one, h3]
  calc _ = (b⁻¹).1.map c * G * (b⁻¹).1ᵀ * H * G := by rw [Matrix.mul_assoc _ H G, hHG, Matrix.mul_one]
    _ = G := by rw [h5, Matrix.one_mul]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) : cA σ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E} {ξ : AF F ⊗[F] E}

theorem symplOF_eq_symp (hA : JA = JTᵀ) (hB : ξ • incM F JB = incM F (ξ₀ • JS⁻¹)) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x y = symp (cA σ) ξ (incM F JA) (incM F JB) x y := by
  unfold symplOF symp hOF hTens
  congr 1
  have h : ∀ j l, ξ * incM F JB j l = incAF F E ξ₀ * incAF F E (JS⁻¹ j l) := fun j l => by
    have := congrFun (congrFun hB j) l
    rw [← map_mul]
    exact this
  simp only [Finset.mul_sum, cA_eq]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
  have h' : incM F JA d c = incAF F E (JT c d) := by rw [hA]; rfl
  rw [h']
  linear_combination (-(x d a * incAF F E (JT c d) * cAF σ (y c b))) * h a b

theorem mem_HR_target (hA : JA = JTᵀ) (a : UG (cA σ) (incM F JA)) : a.1 ∈ HR (AF F) σ JT := by
  have h := congrArg Matrix.transpose a.2
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h
  subst hA
  have e : ((a : GL (Fin nT) (AF F ⊗[F] E)) : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E)).map (cA σ) =
      ((a : GL (Fin nT) (AF F ⊗[F] E)) : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E)).map (sigR (AF F) σ) := by
    ext i j
    exact cA_eq σ _
  rw [e] at h
  exact h

theorem mem_HR_source (hS : IsHermND σ JS) (hξ0 : ξ₀ ≠ 0) (hB : ξ • incM F JB = incM F (ξ₀ • JS⁻¹))
    (b : UG (cA σ) (incM F JB)) : contra b.1 ∈ HR (AF F) σ JS := by
  have hdet : IsUnit JS.det := (Ne.isUnit hS.2)
  have hGH : JS.map (incAF F E) * (JS⁻¹).map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hx : IsUnit (incAF F E ξ₀) := (IsUnit.mk0 _ hξ0).map _
  have hB' : ξ • incM F JB = incAF F E ξ₀ • (JS⁻¹).map (incAF F E) := by
    rw [hB]
    ext i j
    exact map_mul (incAF F E) _ _
  have h := contra_rel (cA σ : AF F ⊗[F] E →+* AF F ⊗[F] E) hGH hx hB' b.1 b.2
  have e : ∀ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E),
      M.map (cA σ : AF F ⊗[F] E →+* AF F ⊗[F] E) = M.map (sigR (AF F) σ) := fun M => by
    ext i j
    exact cA_eq σ _
  rw [e] at h
  show Formalism.UG.cT (sigR (AF F) σ) (((b⁻¹ : GL (Fin nS) _)).1ᵀ) * JR (AF F) JS * (b⁻¹ : GL (Fin nS) _).1ᵀ = JR (AF F) JS
  unfold Formalism.UG.cT
  rw [Matrix.transpose_map, Matrix.transpose_transpose]
  exact h

def pairHomF (hS : IsHermND σ JS) (hξ0 : ξ₀ ≠ 0) (hA : JA = JTᵀ) (hB : ξ • incM F JB = incM F (ξ₀ • JS⁻¹)) :
    UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* GAF σ JS × GAF σ JT where
  toFun p := ((⟨contra p.2.1, mem_HR_source hS hξ0 hB p.2⟩ : HR (AF F) σ JS),
    (⟨p.1.1, mem_HR_target hA p.1⟩ : HR (AF F) σ JT))
  map_one' := Prod.ext (Subtype.ext (map_one contra)) rfl
  map_mul' p q := Prod.ext (Subtype.ext (map_mul contra p.2.1 q.2.1)) rfl

theorem pairHomF_eq (hS : IsHermND σ JS) (hξ0 : ξ₀ ≠ 0) (hA : JA = JTᵀ) (hB : ξ • incM F JB = incM F (ξ₀ • JS⁻¹))
    (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)) (g : GAF σ JS) (h : GAF σ JT)
    (hh : mtF σ JT h = a.1.1) (hg : mtF σ JS g = (b⁻¹).1.1ᵀ) : pairHomF hS hξ0 hA hB (a, b) = (g, h) :=
  Prod.ext (Subtype.ext (Units.ext hg.symm)) (Subtype.ext (Units.ext hh.symm))

variable {κ : Type} [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)

def numCoordF {N : ℕ} (τ : κ ≃ Fin N) : WOF F E nS nT ≃ₗ[AF F] VA F N :=
  co.e.trans ((LinearEquiv.funCongrLeft _ _ τ.symm).prodCongr (LinearEquiv.funCongrLeft _ _ τ.symm))

theorem numCoordF_apply {N : ℕ} (τ : κ ≃ Fin N) (w : WOF F E nS nT) :
    numCoordF co τ w = ((co.e w).1 ∘ τ.symm, (co.e w).2 ∘ τ.symm) := rfl

theorem thetaTr_eqF {ψ : AddChar (AF F) ℂ} {N : ℕ} (τ : κ ≃ Fin N) (Φ : (κ → AF F) → ℂ) :
    GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ = thV ψ (fun x => Φ (x ∘ τ)) ∘ numCoordF co τ := by
  funext w
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, thV, Function.comp_apply, GlobalTheory.WeilM.thetaSum, numCoordF_apply]
  rw [← (Equiv.arrowCongr τ (Equiv.refl F)).tsum_eq]
  refine tsum_congr fun η => ?_
  have e : (fun i => algebraMap F (AF F) (Equiv.arrowCongr τ (Equiv.refl F) η i)) =
      (fun i => algebraMap F (AF F) (η i)) ∘ τ.symm := rfl
  rw [e]
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, comp_equiv_dotProduct_comp_equiv]
  congr 2
  funext i
  simp

theorem thetaTr_smulF {ψ : AddChar (AF F) ℂ} (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    GlobalTheory.WeilSchrodinger.thetaTr F co ψ (c • Φ) = c • GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ := by
  funext w
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr,
    Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

theorem exists_isTransportF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∃ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hω.std.1
  let τ := Fintype.equivFin κ
  have he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (numCoordF co τ w) (numCoordF co τ w') := fun w w' => by
    rw [symplOF_eq_symp hA hB', co.form]
    simp only [symV, numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      numCoordF co τ (ratWF x) = (rat y, rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [numCoordF_apply]; erw [h]; rfl⟩
  have hadd : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (Φ + Φ') =
        GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ + GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ' := fun Φ hΦ Φ' hΦ' => by
    simp only [thetaTr_eqF co τ]
    exact congrArg (· ∘ numCoordF co τ) (thV_add hR hψ
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ))
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ')))
  have hinj : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ' → Φ = Φ' :=
    fun Φ hΦ Φ' hΦ' h => by
    simp only [thetaTr_eqF co τ] at h
    have h2 := thV_injOn hR hψ (comp_mem_schA τ hΦ) (comp_mem_schA τ hΦ')
      ((numCoordF co τ).surjective.injective_comp_right h)
    funext x
    simpa [Function.comp_def] using congrFun h2 (x ∘ τ.symm)
  have hon : ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f ↔
      ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ = f := fun f => by
    constructor
    · intro hf
      obtain ⟨Φ, hΦ, h⟩ := GlobalTheory.T.exists_thetaTransform_eq_orientedThetaFunction_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (numCoordF co τ) he hr f hf
      refine ⟨_, comp_mem_schA τ.symm hΦ, ?_⟩
      rw [thetaTr_eqF co τ, ← h]
      congr 2
      funext x
      simp [Function.comp_def]
    · rintro ⟨Φ, hΦ, rfl⟩
      rw [thetaTr_eqF co τ]
      exact GlobalTheory.T.isThetaFunction_thetaTransform_rational_coords_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (numCoordF co τ) he hr _
        (comp_mem_schA τ hΦ)
  obtain ⟨om, hom⟩ := exists_transport' _ _ _ hadd (thetaTr_smulF co) hinj hon
    (ω.comp (pairHomF hS hξ0 hA hB')) fun p f hf => hω.om_pres _ f hf
  refine ⟨om, ?_⟩
  intro a b g h hh hg Φ hΦ
  have e : (ω.comp (pairHomF hS hξ0 hA hB')) (a, b) = ω (g, h) :=
    congrArg ω (pairHomF_eq hS hξ0 hA hB' a b g h hh hg)
  have h2 := hom (a, b) Φ hΦ
  exact ⟨h2.1, h2.2.trans (LinearMap.congr_fun e _)⟩

end GlobalTheory.TransportF

end
