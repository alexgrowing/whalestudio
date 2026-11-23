import Formalism.LocalToGlobal.Columns.Record
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Unf

variable {X : Fields}

def frCo (σ₀ : X.K →+* ℂ) (n : ℕ) : FrS X σ₀ n → X.Tau → Matrix (Fin n) (Fin n) ℂ := fun y τ => y.1 τ

def polFn (σ₀ : X.K →+* ℂ) (n : ℕ) : Pol ℂ X.Tau n →ₗ[ℂ] (FrS X σ₀ n → ℂ) := frPolyG (frCo σ₀ n)

theorem polFn_apply (σ₀ : X.K →+* ℂ) (n : ℕ) (Q : Pol ℂ X.Tau n) (y : FrS X σ₀ n) :
    polFn σ₀ n Q y = eval (fun x : X.Tau × Fin n × Fin n => y.1 x.1 x.2.1 x.2.2) Q := rfl

theorem polFn_injective (σ₀ : X.K →+* ℂ) (n : ℕ) : Function.Injective (polFn (X := X) σ₀ n) :=
  frPolyG_inj (frCo σ₀ n) fun f hf => ⟨⟨f, fun τ => (hf τ).isUnit⟩, rfl⟩

def polInv (σ₀ : X.K →+* ℂ) (n : ℕ) : (FrS X σ₀ n → ℂ) →ₗ[ℂ] Pol ℂ X.Tau n := frInvG (frCo σ₀ n)

theorem polInv_polFn (σ₀ : X.K →+* ℂ) (n : ℕ) (Q : Pol ℂ X.Tau n) : polInv σ₀ n (polFn σ₀ n Q) = Q :=
  LinearMap.congr_fun (frInvG_spec (polFn_injective σ₀ n)) Q

def unfTh (σ₀ : X.K →+* ℂ) (cD : X.Tau → ℂ) {a b : ℕ} (Θ : VCx X.Tau a b → ℂ) : (FrS X σ₀ a → ℂ) →ₗ[ℂ] (FrS X σ₀ b → ℂ) :=
  unfG (frCo σ₀ a) (frCo σ₀ b) cD Θ

theorem unfTh_eq (σ₀ : X.K →+* ℂ) (cD : X.Tau → ℂ) {a b : ℕ} (Θ : VCx X.Tau a b → ℂ) :
    unfTh σ₀ cD Θ = polFn σ₀ b ∘ₗ jetMap (ι := X.Tau) (jetC cD Θ) (fun _ => 0) ∘ₗ polInv σ₀ a := rfl

theorem unfTh_polFn (σ₀ : X.K →+* ℂ) (cD : X.Tau → ℂ) {a b : ℕ} (Θ : VCx X.Tau a b → ℂ) (Q : Pol ℂ X.Tau a) :
    unfTh σ₀ cD Θ (polFn σ₀ a Q) = polFn σ₀ b (jetMap (ι := X.Tau) (jetC cD Θ) (fun _ => 0) Q) := by
  simp only [unfTh_eq, LinearMap.comp_apply, polInv_polFn]

theorem unfTh_apply (σ₀ : X.K →+* ℂ) (cD : X.Tau → ℂ) {a b : ℕ} (Θ : VCx X.Tau a b → ℂ) (Q : Pol ℂ X.Tau a) (y' : FrS X σ₀ b) :
    unfTh σ₀ cD Θ (polFn σ₀ a Q) y' =
      ∑ α ∈ (polDx cD (fun x : X.Tau × Fin b × Fin b => y'.1 x.1 x.2.1 x.2.2) Q).support,
        coeff α (polDx cD (fun x : X.Tau × Fin b × Fin b => y'.1 x.1 x.2.1 x.2.2) Q) * derivAt0 Θ α := by
  rw [unfTh_polFn, polFn_apply, jetMap_eval]

theorem jetC_zero {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) (Θ : VCx ι a b → ℂ) : jetC cD Θ 0 = Θ 0 := by
  have gen : ∀ (n : ℕ) (_ : n = 0) (v : Fin n → VCx ι a b), iteratedFDeriv ℂ n Θ 0 v = Θ 0 := by
    rintro n rfl v
    exact iteratedFDeriv_zero_apply _
  unfold jetC derivAt0
  rw [Finsupp.prod_zero_index, one_mul]
  exact gen _ (by simp) _

theorem unfTh_one (σ₀ : X.K →+* ℂ) (cD : X.Tau → ℂ) {a b : ℕ} (Θ : VCx X.Tau a b → ℂ) :
    unfTh σ₀ cD Θ (fun _ : FrS X σ₀ a => (1 : ℂ)) = fun _ => Θ 0 := by
  have h : (fun _ : FrS X σ₀ a => (1 : ℂ)) = polFn σ₀ a 1 := by
    funext y
    rw [polFn_apply, map_one]
  rw [h, unfTh_polFn, jetMap_one, jetC_zero]
  funext y'
  rw [polFn_apply, eval_C]

end Unf

section BaseChange

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {a b : ℕ}

theorem map_jetLin (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    MvPolynomial.map σ (jetLin J Q) = jetLin (fun m => σ (J m)) (MvPolynomial.map σ Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c => rw [jetLin_monomial, map_monomial, map_monomial, jetLin_monomial, map_mul]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

theorem map_subD (σ : K →+* L) (P : Pol K ι a) :
    MvPolynomial.map σ (subD K ι a b P) = subD L ι a b (MvPolynomial.map σ P) := by
  have h : (MvPolynomial.map σ).comp (subD K ι a b).toRingHom =
      (subD L ι a b).toRingHom.comp (MvPolynomial.map σ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [subD]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, subD, aeval_X, map_X]
      split_ifs with hv
      · simp
      · simp
  exact RingHom.congr_fun h P

theorem map_frDet (σ : K →+* L) (τ : ι) : MvPolynomial.map σ (frDet K a τ) = frDet L a τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp

theorem map_jetMap (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    MvPolynomial.map σ (jetMap J n P) = jetMap (fun m => σ (J m)) n (MvPolynomial.map σ P) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  rw [map_jetLin, map_subD, map_mul, map_prod]
  simp only [map_pow, map_frDet]

theorem jetMap_smul (c : K) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (fun m => c * J m) n P = c • jetMap J n P := by
  unfold jetMap
  rw [jetLin_smul]
  rfl

theorem jetMap_shift (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap J (fun _ => 0) (P * ∏ τ, frDet K a τ ^ n τ) = jetMap J n P := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_zero, Finset.prod_const_one, mul_one]

theorem eval_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    eval (fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) (frDet ℂ a τ) = (y τ).det := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp

end BaseChange

section Ev

variable {X : Fields} {a b : ℕ}

theorem sharp_evV (σ₀ : X.K →+* ℂ) (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ) (s' : X.Tau → ℤ)
    (hn : ∀ τ, s' τ + (lam τ).detShift = (n τ : ℤ)) (P : VV X.K lam) :
    mulFun (dePow σ₀ a s') (evV X.emb 1 lam σ₀ P) = polFn σ₀ a (MvPolynomial.map σ₀ P.1 * ∏ τ, frDet ℂ a τ ^ n τ) := by
  funext y
  rw [polFn_apply, map_mul, map_prod]
  simp only [map_pow, eval_frDet (fun τ => y.1 τ)]
  show dePow σ₀ a s' y * evFr _ (shiftOf lam) σ₀ P.1 y = _
  rw [evFr_apply, ← mul_assoc, eval_map, mul_comm]
  congr 1
  unfold dePow
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  show (y.1 τ).det ^ s' τ * (y.1 τ).det ^ (lam τ).detShift = _
  rw [← zpow_add₀ (y.2 τ).ne_zero, hn, zpow_natCast]

theorem unfTh_ev (σ₀ : X.K →+* ℂ) (cD : X.Tau → ℂ) (Θ : VCx X.Tau a b → ℂ) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b)
    (n : X.Tau → ℕ) (s' s : X.Tau → ℤ) (hn : ∀ τ, s' τ + (lam τ).detShift = (n τ : ℤ)) (hs : ∀ τ, (lam' τ).detShift = -s τ)
    (hV : JetInVV X.K lam lam' n) (J : (DVar X.Tau a b →₀ ℕ) → X.K) (c : ℂ) (hJ : ∀ m, σ₀ (J m) = c * jetC cD Θ m) (P : VV X.K lam) :
    evV X.emb 1 lam' σ₀ (jetOp lam lam' J n P) =
      c • mulFun (fun y' => (dePow σ₀ b s y')⁻¹) (unfTh σ₀ cD Θ (mulFun (dePow σ₀ a s') (evV X.emb 1 lam σ₀ P))) := by
  rw [sharp_evV σ₀ lam n s' hn P, unfTh_polFn, jetMap_shift]
  funext y'
  show evFr _ (shiftOf lam') σ₀ (jetOp lam lam' J n P).1 y' = c * ((dePow σ₀ b s y')⁻¹ * polFn σ₀ b _ y')
  rw [evFr_apply, jetOp_coe lam lam' n hV, ← eval_map, map_jetMap, funext hJ, jetMap_smul, smul_eval, polFn_apply]
  have hd : (∏ τ, (y'.1 τ).det ^ shiftOf lam' τ) = (dePow σ₀ b s y')⁻¹ := by
    unfold dePow
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    show (y'.1 τ).det ^ (lam' τ).detShift = ((y'.1 τ).det ^ s τ)⁻¹
    rw [hs, _root_.zpow_neg]
  rw [hd]
  ring

theorem unfTh_kerOf (Am : Amb X) (σ₀ : X.K →+* ℂ) (hσ : Am.σ₀ = σ₀) (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (hA : 0 < cA) (hB : 0 < cB)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) (s' s : X.Tau → ℤ)
    (hn : ∀ τ, s' τ + (lam τ).detShift = (n τ : ℤ)) (hs : ∀ τ, (lam' τ).detShift = -s τ) (hV : JetInVV X.K lam lam' n)
    (hsm : Am.ESmooth a b) (hrat : Am.JetsRat a b Sall (cA * cB))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB) (hN : IsSdLat N) (hN' : IsSdLat N')
    (Ξ : HomE X.E a b → X.K) (P : VV X.K lam) :
    evV X.emb 1 lam' σ₀ (kerOf (thDistC Am Sall SB (cA * cB) sel mU mI lam lam' n) Sall cA cB N fr N' fr' Ξ P) =
      (σ₀ (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) * (Am.chiF a b N N')⁻¹) •
        mulFun (fun y' => (dePow σ₀ b s y')⁻¹)
          (unfTh σ₀ Am.cD (Am.thDat Sall cA cB N N' Ξ) (mulFun (dePow σ₀ a s') (evV X.emb 1 lam σ₀ P))) := by
  subst hσ
  rw [kerOf_tab Am Sall SB cA cB hA hB sel mU mI lam lam' n N fr N' fr' hN hN' Ξ, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    unfTh_ev Am.σ₀ Am.cD (Am.thDat Sall cA cB N N' Ξ) lam lam' n s' s hn hs hV _ (Am.chiF a b N N')⁻¹
      (tabK_spec Am Sall cA cB hA hB hsm hrat N N' hN hN' Ξ) P, smul_smul]

end Ev

section Arg

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

structure ThetaDat (u : Pr.Word) where
  cD : X.Tau → ℂ
  Th : ∀ i, StCl W Λ u i → StCl W Λ u (i + 1) → VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ

variable {W Λ}

def ThetaDat.Comparison₂ {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) {u : Pr.Word} (T : ThetaDat W Λ u)
    (kk : ∀ i, ClsKer (stepGSD W Λ u i) (stepGSD W Λ u (i + 1))) : Prop :=
  ∀ i (L : StCl W Λ u i) (L' : StCl W Λ u (i + 1)) (x : (stepGSD W Λ u i).V),
    mulFun (fun y' => (dePow σ₀ (R.N (i + 1)) (sDivC W u i) y')⁻¹)
        (unfTh σ₀ T.cD (T.Th i L L') (mulFun (dePow σ₀ (R.N i) (sSharpC W u i)) ((stepEv W Λ σ₀ G.hσ u i).ev x))) =
      (σ₀ (rhoK W Λ G.chr u i L : X.K) * σ₀ (rhoK' W Λ G.chr u i L' : X.K))⁻¹ •
        (stepEv W Λ σ₀ G.hσ u (i + 1)).ev
          ((kk i).k ((stepGSD W Λ u i).outSec.rep L) ((stepGSD W Λ u (i + 1)).outSec.rep L') x)

def ChainArg.ofTheta {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {u : Pr.Word} (kk : ∀ i, ClsKer (stepGSD W Λ u i) (stepGSD W Λ u (i + 1)))
    (T : ThetaDat W Λ u) (h : T.Comparison₂ G kk) : ChainArg W Λ G u where
  kk := kk
  unf i L L' := unfTh σ₀ T.cD (T.Th i L L')
  unf_ev := h

theorem recChain_unf_pol (hX : X.Ok) (σ₀ : X.K →+* ℂ) (G : ChainGlob W σ₀) (u : Pr.Word) (kk : ∀ i, ClsKer (stepGSD W Λ u i) (stepGSD W Λ u (i + 1)))
    (T : ThetaDat W Λ u) (h : T.Comparison₂ G kk) (i : ℕ) (L : StCl W Λ u i) (L' : StCl W Λ u (i + 1)) (Q : Pol ℂ X.Tau (R.N i)) :
    (recChain hX σ₀ G u (ChainArg.ofTheta kk T h)).unf i L L' (polFn σ₀ (R.N i) Q) =
      polFn σ₀ (R.N (i + 1)) (jetMap (ι := X.Tau) (jetC T.cD (T.Th i L L')) (fun _ => 0) Q) :=
  unfTh_polFn σ₀ T.cD (T.Th i L L') Q

theorem recChain_unf_one (hX : X.Ok) (σ₀ : X.K →+* ℂ) (G : ChainGlob W σ₀) (u : Pr.Word) (kk : ∀ i, ClsKer (stepGSD W Λ u i) (stepGSD W Λ u (i + 1)))
    (T : ThetaDat W Λ u) (h : T.Comparison₂ G kk) (i : ℕ) (L : StCl W Λ u i) (L' : StCl W Λ u (i + 1)) :
    (recChain hX σ₀ G u (ChainArg.ofTheta kk T h)).unf i L L' (fun _ => 1) = fun _ => T.Th i L L' 0 :=
  unfTh_one σ₀ T.cD (T.Th i L L')

end Arg

section Wt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem sSharpC_cast (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    ((sSharpC W u i τ : ℤ) : ℚ) = sExp' R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := by
  obtain ⟨a, ha⟩ := (rec_sInt R (W.hc u τ) ⟨i, hi⟩).2
  unfold sSharpC
  rw [RowPar.eAt_of _ hi]
  simp only at ha
  rw [ha, Int.floor_intCast]

theorem sDivC_cast (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    ((sDivC W u i τ : ℤ) : ℚ) = sExp R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := by
  obtain ⟨a, ha⟩ := (rec_sInt R (W.hc u τ) ⟨i, hi⟩).1
  unfold sDivC
  rw [RowPar.eAt_of _ hi]
  simp only at ha
  rw [ha, Int.floor_intCast]

theorem sSharpC_add (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    sSharpC W u i τ + (W.lamTrue u i τ).detShift = (nuLast W u i τ : ℤ) := by
  have hN : 0 < R.N i := R.N_pos i
  rw [nuLast_eq W u i hi τ]
  have h1 : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w (⟨R.N i - 1, by omega⟩ : Fin (R.N i)) := by
    unfold DomWeight.detShift
    exact dif_pos hN
  have h2 : (W.lamTrue u i τ).detShift = (W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ := by
    unfold DomWeight.detShift
    exact dif_pos hN
  rw [h1, h2]
  have h3 := Wts.nuW_eq_true W u hi τ ⟨R.N i - 1, by omega⟩
  rw [← sSharpC_cast W u hi τ] at h3
  have h4 : (W.nuW u (i + 1) τ).w (⟨R.N i - 1, by omega⟩ : Fin (R.N i)) = (W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ + sSharpC W u i τ := by
    exact_mod_cast h3
  rw [h4, add_comm]

theorem lamTrue_last (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    (W.lamTrue u (i + 1) τ).detShift = -sDivC W u i τ := by
  have hN : 0 < R.N (i + 1) := R.N_pos (i + 1)
  have hlt : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  have h2 : (W.lamTrue u (i + 1) τ).detShift = (W.lamTrue u (i + 1) τ).w ⟨R.N (i + 1) - 1, by omega⟩ := by
    unfold DomWeight.detShift
    exact dif_pos hN
  rw [h2]
  have h3 := Wts.lamTrue_new W u hi τ ⟨R.N (i + 1) - 1, by omega⟩ (by simp only; omega)
  rw [← sDivC_cast W u hi τ] at h3
  exact_mod_cast h3

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem unfTh_stepC (Am : Amb X) (σ₀ : X.K →+* ℂ) (hσ : Am.σ₀ = σ₀) (u : Pr.Word) (hT : 0 < Pr.T u) {i : ℕ} (hi : i < R.m)
    (hV : JetInVVStep W u i (W.lamTrue u (i + 1))) (hsm : Am.ESmooth (R.N i) (R.N (i + 1)))
    (hrat : Am.JetsRat (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (N : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (N' : Submodule (𝓞 X.E) (Sp X.E (R.N (i + 1))))
    (fr' : Frs X.E (R.N (i + 1)) (rowSG Pr sel mu)) (hN : IsSdLat N) (hN' : IsSdLat N') (Ξ : HomE X.E (R.N i) (R.N (i + 1)) → X.K)
    (P : VV X.K (W.lamTrue u i)) :
    evV X.emb 1 (W.lamTrue u (i + 1)) σ₀
        (kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N fr N' fr' Ξ P) =
      (σ₀ (scalK Ch sel mu cst i N fr N' fr') * (Am.chiF (R.N i) (R.N (i + 1)) N N')⁻¹) •
        mulFun (fun y' => (dePow σ₀ (R.N (i + 1)) (sDivC W u i) y')⁻¹)
          (unfTh σ₀ Am.cD (Am.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ)
            (mulFun (dePow σ₀ (R.N i) (sSharpC W u i)) (evV X.emb 1 (W.lamTrue u i) σ₀ P))) :=
  unfTh_kerOf Am σ₀ hσ (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) (cAof_pos sel mu cst) (cBof_pos sel mu cst u hT) sel
    (mUof Ch mu i) (muAt Ch sel mu cst i) (W.lamTrue u i) (W.lamTrue u (i + 1)) (nuLast W u i) (sSharpC W u i) (sDivC W u i)
    (sSharpC_add W u hi) (lamTrue_last W u hi) hV hsm hrat N fr N' fr' hN hN' Ξ P

end Wt

section Zero

variable {X : Fields}

theorem jetC_zero_fun {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) (m : DVar ι a b →₀ ℕ) : jetC cD (fun _ : VCx ι a b => (0 : ℂ)) m = 0 := by
  unfold jetC derivAt0
  rw [iteratedFDeriv_fun_zero]
  simp

theorem unfTh_zero (σ₀ : X.K →+* ℂ) (cD : X.Tau → ℂ) {a b : ℕ} : unfTh σ₀ cD (fun _ : VCx X.Tau a b => (0 : ℂ)) = 0 := by
  have h : jetLin (jetC cD (fun _ : VCx X.Tau a b => (0 : ℂ))) = 0 := by
    have h1 : jetC cD (fun _ : VCx X.Tau a b => (0 : ℂ)) = fun m => (0 : ℂ) * (0 : ℂ) := by
      funext m
      rw [jetC_zero_fun, zero_mul]
    rw [h1, jetLin_smul, zero_smul]
  rw [unfTh_eq]
  unfold jetMap
  rw [h, LinearMap.zero_comp, LinearMap.zero_comp, LinearMap.comp_zero]

end Zero

section Rho

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

open Classical in

def frsD {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet X.E n ST Pr.vGs) : Frs X.E n (rowSG Pr sel mu) := fun P =>
  if h : P.1 ∈ Pr.vGs then p.1.liftFr ⟨P.1, h⟩ else 1

def repN (u : Pr.Word) (j : ℕ) (c : StCl W Λ u j) : Submodule (𝓞 X.E) (Sp X.E (R.N j)) := ((stepGSD W Λ u j).outSec.rep c).1.N

def repFr (u : Pr.Word) (j : ℕ) (c : StCl W Λ u j) : Frs X.E (R.N j) (rowSG Pr sel mu) := frsD sel mu ((stepGSD W Λ u j).outSec.rep c)

def RhoScal {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (Am : Amb X) (u : Pr.Word) : Prop :=
  ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
    σ₀ (rhoK W Λ G.chr u i c : X.K) * σ₀ (rhoK' W Λ G.chr u i c' : X.K) * Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') =
      σ₀ (scalK Ch sel mu cst i (repN W Λ u i c) (repFr W Λ sel mu u i c) (repN W Λ u (i + 1) c') (repFr W Λ sel mu u (i + 1) c'))

def MuDetTie (Dc : DetChr X R.m) (hc : Formalism.BasicNotions.CMData X.F X.E) (u : Pr.Word) : Prop :=
  ∀ i, i < R.m → ∀ n, (n = i ∨ n = i + 1) → ∀ c : StCl W Λ u n,
    (((Formalism.L2.DIV.detTw hc.sig (Dc.muAt i) (repPt W Λ hc u n c))⁻¹ : X.Kˣ) : X.K) =
      muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (repN W Λ u n c) (repFr W Λ sel mu u n c)

def ChiDetTie (σ₀ : X.K →+* ℂ) (Dc : DetChr X R.m) (hc : Formalism.BasicNotions.CMData X.F X.E) (Am : Amb X) (u : Pr.Word) : Prop :=
  ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
    σ₀ (((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u i c)) ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ)) *
        (Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u (i + 1) c')) ^ (((R.N i / 2 : ℕ) : ℤ)) : X.Kˣ) : X.K) *
      Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') = 1

variable {W Λ Ch sel mu cst}

theorem rhoScal_of {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (Am : Amb X) (u : Pr.Word) (hc : Formalism.BasicNotions.CMData X.F X.E)
    (h1 : MuDetTie W Λ Ch sel mu cst G.chr hc u) (h2 : ChiDetTie W Λ σ₀ G.chr hc Am u) : RhoScal W Λ Ch sel mu cst G Am u := by
  intro i hi c c'
  have a := h1 i hi i (Or.inl rfl) c
  have b := h1 i hi (i + 1) (Or.inr rfl) c'
  have e := h2 i hi c c'
  unfold scalK
  rw [← a, ← b]
  unfold rhoK rhoK'
  rw [dif_pos hc, dif_pos hc]
  set A := Formalism.L2.DIV.detTw hc.sig (G.chr.muAt i) (repPt W Λ hc u i c)
  set B := Formalism.L2.DIV.detTw hc.sig (G.chr.muAt i) (repPt W Λ hc u (i + 1) c')
  set C := (Formalism.L2.DIV.detTw hc.sig G.chr.chi (repPt W Λ hc u i c)) ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ))
  set D := (Formalism.L2.DIV.detTw hc.sig G.chr.chi (repPt W Λ hc u (i + 1) c')) ^ (((R.N i / 2 : ℕ) : ℤ))
  have e' : σ₀ (C : X.K) * σ₀ (D : X.K) * Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') = 1 := by
    rw [← map_mul, ← Units.val_mul]
    exact e
  have hB : (((B⁻¹ : X.Kˣ) : X.K))⁻¹ = (B : X.K) := by
    rw [Units.val_inv_eq_inv_val, inv_inv]
  rw [hB, Units.val_mul, Units.val_mul, map_mul, map_mul, map_mul]
  calc σ₀ ((A⁻¹ : X.Kˣ) : X.K) * σ₀ (C : X.K) * (σ₀ (B : X.K) * σ₀ (D : X.K)) *
        Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c')
      = σ₀ ((A⁻¹ : X.Kˣ) : X.K) * σ₀ (B : X.K) *
          (σ₀ (C : X.K) * σ₀ (D : X.K) * Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c')) := by ring
    _ = σ₀ ((A⁻¹ : X.Kˣ) : X.K) * σ₀ (B : X.K) := by rw [e', mul_one]

end Rho

section Xi

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word)

abbrev XiFam (Pr : Primes X) (R : Ranks) (u : Pr.Word) : Type :=
  ∀ i, DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs → DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs → HomE X.E (R.N i) (R.N (i + 1)) → X.K

variable (Ξ : XiFam Pr R u)

def xiKer (i : ℕ) (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) (p' : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs) :
    (stepGSD W Λ u i).V →ₗ[X.K] (stepGSD W Λ u (i + 1)).V :=
  kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    p.1.N (frsD sel mu p) p'.1.N (frsD sel mu p') (Ξ i p p')

def XiEquiv : Prop :=
  ∀ i, ClsEq (S := stepGSD W Λ u i) (S' := stepGSD W Λ u (i + 1)) (xiKer W Λ Ch sel mu cst Am u Ξ i)

variable {W Λ Ch sel mu cst Am u Ξ} in

def xiKK (h : XiEquiv W Λ Ch sel mu cst Am u Ξ) : ∀ i, ClsKer (stepGSD W Λ u i) (stepGSD W Λ u (i + 1)) :=
  fun i => ⟨xiKer W Λ Ch sel mu cst Am u Ξ i, h i⟩

def xiTheta : ThetaDat W Λ u where
  cD := Am.cD
  Th i c c' := Am.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (repN W Λ u i c) (repN W Λ u (i + 1) c')
    (Ξ i ((stepGSD W Λ u i).outSec.rep c) ((stepGSD W Λ u (i + 1)).outSec.rep c'))

structure XiHyp {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) : Prop where
  sig : Am.σ₀ = σ₀
  T_pos : 0 < Pr.T u
  smooth : ∀ i, i < R.m → Am.ESmooth (R.N i) (R.N (i + 1))
  rat : ∀ i, i < R.m → Am.JetsRat (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
  chi_ne : ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
    Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') ≠ 0
  rho : RhoScal W Λ Ch sel mu cst G Am u
  above : ∀ i, R.m ≤ i → ∀ p p' x, Ξ i p p' x = 0

variable {W Λ Ch sel mu cst Am u Ξ}

theorem kerOf_zero {E K : Type} [Field E] [NumberField E] [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
    {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V')
    (Sa : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b))
    (fr' : Frs E b SB) (Ξ₀ : HomE E a b → K) (h : ∀ x, Ξ₀ x = 0) : kerOf th Sa cA cB N fr N' fr' Ξ₀ = 0 := by
  unfold kerOf latSum
  simp only [h, zero_smul]
  exact finsum_zero

theorem thDat_zero (A : Amb X) {a b : ℕ} (Sa : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ₀ : HomE X.E a b → X.K) (h : ∀ x, Ξ₀ x = 0) : A.thDat Sa cA cB N N' Ξ₀ = fun _ => 0 := by
  funext z
  unfold Amb.thDat latSum
  simp only [h, map_zero, zero_mul]
  exact finsum_zero

theorem xiTheta_tie {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (hE : XiEquiv W Λ Ch sel mu cst Am u Ξ) (H : XiHyp W Λ Ch sel mu cst Am u Ξ G) :
    (xiTheta W Λ sel mu cst Am u Ξ).Comparison₂ G (xiKK hE) := by
  intro i c c' x
  by_cases hi : i < R.m
  · have hp := ((stepGSD W Λ u i).outSec.rep c).2
    have hp' := ((stepGSD W Λ u (i + 1)).outSec.rep c').2
    have h := unfTh_stepC W Ch sel mu cst Am σ₀ H.sig u H.T_pos hi (jet_in_weight_space_chain W u hi) (H.smooth i hi) (H.rat i hi)
      (repN W Λ u i c) (repFr W Λ sel mu u i c) (repN W Λ u (i + 1) c') (repFr W Λ sel mu u (i + 1) c')
      ⟨hp.lat, hp.uni⟩ ⟨hp'.lat, hp'.uni⟩
      (Ξ i ((stepGSD W Λ u i).outSec.rep c) ((stepGSD W Λ u (i + 1)).outSec.rep c')) x
    have hr := H.rho i hi c c'
    have hx := H.chi_ne i hi c c'
    set r := σ₀ (rhoK W Λ G.chr u i c : X.K) * σ₀ (rhoK' W Λ G.chr u i c' : X.K) with hrdef
    have h0 : r ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · intro h; have := rhoK_norm G u i c; rw [h, norm_zero] at this; exact zero_ne_one this
      · intro h; have := rhoK'_norm G u i c'; rw [h, norm_zero] at this; exact zero_ne_one this
    have hs : σ₀ (scalK Ch sel mu cst i (repN W Λ u i c) (repFr W Λ sel mu u i c) (repN W Λ u (i + 1) c') (repFr W Λ sel mu u (i + 1) c')) *
        (Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c'))⁻¹ = r := by
      rw [← hr, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    rw [hs] at h
    funext (y' : FrS X σ₀ (R.N (i + 1)))
    have hy := congrFun h y'
    refine Eq.trans ?_ (congrArg (fun z : ℂ => r⁻¹ * z) hy).symm
    show _ = r⁻¹ * (r * _)
    rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    rfl
  · have hi' : R.m ≤ i := Nat.le_of_not_lt hi
    have hk : (xiKK hE i).k ((stepGSD W Λ u i).outSec.rep c) ((stepGSD W Λ u (i + 1)).outSec.rep c') = 0 :=
      kerOf_zero _ _ _ _ _ _ _ _ _ (H.above i hi' _ _)
    have ht : (xiTheta W Λ sel mu cst Am u Ξ).Th i c c' = fun _ => 0 := thDat_zero Am _ _ _ _ _ _ (H.above i hi' _ _)
    rw [hk, ht, unfTh_zero]
    simp
    rfl

def ChainArg.ofXi {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} (hE : XiEquiv W Λ Ch sel mu cst Am u Ξ) (H : XiHyp W Λ Ch sel mu cst Am u Ξ G) :
    ChainArg W Λ G u :=
  ChainArg.ofTheta (xiKK hE) (xiTheta W Λ sel mu cst Am u Ξ) (xiTheta_tie G hE H)

end Xi

end Formalism.L2.Col
