import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutFormUCoef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryRationalPointSplitFiniteInfiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRealPointsWeightRepresentationEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorFormValuesMemISupFixedPartsStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer.RangeLe

theorem contW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)), Continuous fun g : UA E n => ℓ (wInf lam g u) := GlobalTheory.T.continuous_matrixCoeff_infinitePlacesWeightRep

theorem ratSplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n, ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧ ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := GlobalTheory.T.definiteUnitaryRationalPoint_split_finite_infinite

theorem spanW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := GlobalTheory.T.span_realPoints_weightRepresentation_eq_top

theorem semis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := GlobalTheory.T.fixedVectorForm_values_mem_iSup_fixedParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def dualW (lam : InfinitePlace E → DomWeight n) : UA E n →* Module.End ℂ (Module.Dual ℂ (Wsp lam)) where
  toFun g := (wInf lam g⁻¹).dualMap
  map_one' := by
    refine LinearMap.ext fun φ => LinearMap.ext fun w => ?_
    simp [LinearMap.dualMap_apply]
  map_mul' a b := by
    refine LinearMap.ext fun φ => LinearMap.ext fun w => ?_
    simp [LinearMap.dualMap_apply, _root_.mul_inv_rev, map_mul]

theorem dualW_apply (lam : InfinitePlace E → DomWeight n) (g : UA E n) (φ : Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    dualW lam g φ w = φ (wInf lam g⁻¹ w) := rfl

theorem wInf_inv_rat (lam : InfinitePlace E → DomWeight n) (γ : UA E n) (γ₀ : UE E n)
    (h : ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1) :
    wInf lam γ⁻¹ = wAt lam γ₀⁻¹ := by
  have e : ∀ v : InfinitePlace E, cEmb v.embedding γ⁻¹ = GeneralLinearGroup.map v.embedding (γ₀⁻¹ : UE E n).1 :=
    fun v => by rw [map_inv, h v, InvMemClass.coe_inv, map_inv]
  unfold wInf wAt
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, e]

theorem phiFun_wInf (lam : InfinitePlace E → DomWeight n) (F : finU E n → Module.Dual ℂ (Wsp lam)) (x : infU E n)
    (w : Wsp lam) : phiFun lam F (wInf lam x.1 w) = RU E n x.1 (phiFun lam F w) := by
  funext g
  change F (splitFin E n g) (wInf lam g (wInf lam x.1 w)) = F (splitFin E n (g * x.1)) (wInf lam (g * x.1) w)
  rw [map_mul (splitFin E n), splitFin_inf x, mul_one, map_mul (wInf lam), Module.End.mul_apply]

theorem phiFun_mem_fixed (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (F : finU E n → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    phiFun lam F w ∈ fixed (RF E n) (globLev S K') := by
  intro k
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  funext g
  change phiFun lam F w (g * ((k : finU E n) : UA E n)) = phiFun lam F w g
  rw [phiFun_mul_fin]
  have e : rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) (k : finU E n) F = F := funext fun x => hF.2 k k.2 x
  rw [e]

theorem isAutFormU_phiFun (hU : Unr E) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    (F : finU E n → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    IsAutFormU (phiFun lam F w) := by
  have hfin : ∀ k ∈ finU E n, dualW lam k = 1 := by
    intro k hk
    refine LinearMap.ext fun φ => LinearMap.ext fun u => ?_
    rw [dualW_apply, wInf_fin lam ⟨k⁻¹, (finU E n).inv_mem hk⟩]
    rfl
  have hcont : ∀ (u : Module.Dual ℂ (Wsp lam)) (ℓ : Module.Dual ℂ (Module.Dual ℂ (Wsp lam))),
      Continuous fun g => ℓ (dualW lam g u) := by
    intro u ℓ
    obtain ⟨w', rfl⟩ := (Module.evalEquiv ℂ (Wsp lam)).surjective ℓ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, dualW_apply]
    exact (contW E n lam w' u).comp continuous_inv
  have hinf : ∀ y ∈ infU E n, ∀ g, (fun g => F (splitFin E n g)) (g * y) = F (splitFin E n g) := by
    intro y hy g
    simp only [map_mul, splitFin_inf ⟨y, hy⟩, mul_one]
  have hrat : ∀ γ ∈ ratU E n, ∀ g, (fun g => F (splitFin E n g)) (γ * g) = dualW lam γ (F (splitFin E n g)) := by
    intro γ hγ g
    obtain ⟨γ₀, h1, h2⟩ := ratSplit E n γ hγ
    simp only [map_mul, h1]
    rw [hF.1 γ₀ (splitFin E n g)]
    refine LinearMap.ext fun u => ?_
    rw [dualW_apply, wInf_inv_rat lam γ γ₀ h2]
    rfl
  have hsm : ∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, (fun g => F (splitFin E n g)) (g * y) = F (splitFin E n g) := by
    have ho : IsOpen ((splitFin E n) ⁻¹' (globLev S K' : Set (finU E n))) :=
      (isOpen_globLev E hU n S K' hK).preimage continuous_splitFin
    filter_upwards [ho.mem_nhds (by simp [(globLev S K').one_mem])] with y hy g
    simp only [map_mul]
    exact hF.2 _ hy _
  have h := GlobalTheory.EquivCoef.isAutFormU_coef E n (Module.Dual ℂ (Wsp lam)) (dualW lam) (fun g => F (splitFin E n g))
    hfin hcont hinf hrat hsm (Module.Dual.eval ℂ (Wsp lam) w)
  convert h using 1
  funext g
  simp [dualW_apply]

theorem hasWeightAt_of_wInf (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ))
    (f' : Wsp lam →ₗ[ℂ] (UA E n → ℂ)) (h0 : f' ≠ 0) (hπ : ∀ u, f' u ∈ π)
    (heq : ∀ (x : infU E n) u, f' (wInf lam x.1 u) = RU E n x.1 (f' u)) (v : InfinitePlace E) :
    HasWeightAt π v.embedding (lam v) := by
  obtain ⟨e, he⟩ : ∃ e : ∀ v, nablaSq ℂ n (lam v), f' (PiTensorProduct.tprod ℂ e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (PiTensorProduct.ext (MultilinearMap.ext fun e => by simpa using hc e))
  refine ⟨GlobalTheory.DefU.isIrreducible_sqRep n (lam v), f' ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap e v, ?_,
    fun a => hπ _, fun x a => ?_⟩
  · intro h
    apply he
    have := LinearMap.congr_fun h (e v)
    simpa [MultilinearMap.toLinearMap] using this
  · have hx : x.1 ∈ infU E n := GlobalTheory.DefU.embU_le_infU _ x.2
    have h2 := heq ⟨x.1, hx⟩ (PiTensorProduct.tprod ℂ (Function.update e v a))
    have h3 : wInf lam x.1 (PiTensorProduct.tprod ℂ (Function.update e v a)) =
        PiTensorProduct.tprod ℂ (Function.update e v (GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x.1) a)) := by
      change PiTensorProduct.map _ _ = _
      rw [PiTensorProduct.map_tprod]
      congr 1
      funext u
      by_cases h : u = v
      · subst h
        simp
      · have h1 := (Subgroup.mem_inf.1 x.2).2
        rw [Subgroup.mem_iInf] at h1
        have h4 := h1 u.embedding
        rw [Subgroup.mem_iInf] at h4
        have h5 : cEmb u.embedding x.1 = 1 := MonoidHom.mem_ker.1 (h4 (by simpa using h))
        simp only [Function.update_of_ne h, h5, map_one, Module.End.one_apply]
    rw [h3] at h2
    simpa [MultilinearMap.toLinearMap] using h2

theorem phiFun_mem_forms (hU : Unr E) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    (F : finU E n → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    phiFun lam F w ∈ forms S lam K' := by
  have h := semis E n (Wsp lam) ((wInf lam).comp (infU E n).subtype) (spanW E n lam) (globLev S K')
    (isOpen_globLev E hU n S K' hK) (phiFun lam F) (fun u => isAutFormU_phiFun hU S lam K' hK F hF u)
    (fun x u => phiFun_wInf lam F x u) (fun u => phiFun_mem_fixed S lam K' F hF u) w
  refine SetLike.le_def.1 ?_ h
  refine iSup_mono fun π => iSup_mono' fun hP => ⟨⟨hP.1, fun v => ?_⟩, le_rfl⟩
  obtain ⟨f', h0, hπ, heq⟩ := hP.2
  exact hasWeightAt_of_wInf lam π f' h0 hπ (fun x u => heq x u) v

end GlobalTheory.BCT.TrKer.RangeLe

namespace GlobalTheory.BCT.TrKer

open GlobalTheory.BCT.TrKer.RangeLe in

theorem range_Phi_le_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → LinearMap.range (Phi S lam K') ≤ forms S lam K' := by
  intro E _ _ _ hU n _ S _ lam K' hK
  rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨F, w, rfl⟩, rfl⟩
  rw [Phi_tmul]
  exact phiFun_mem_forms hU S lam K' hK F.1 F.2 w

end GlobalTheory.BCT.TrKer
