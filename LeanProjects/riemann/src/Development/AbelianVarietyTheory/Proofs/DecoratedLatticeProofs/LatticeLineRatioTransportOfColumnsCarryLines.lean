import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RatioAA

variable {D : D7}

theorem incA_mul_tmul (b : D.host.E) (p : AF D.host.F) (z : D.host.E) :
    incA D b * (p ⊗ₜ[D.host.F] z) = p ⊗ₜ[D.host.F] (b * z) := by
  show (1 ⊗ₜ[D.host.F] b) * (p ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem colMul_add {m n : ℕ} (x : Mx D m n) (l : Fin n) (c c' : AE D) :
    colMul x l (c + c') = colMul x l c + colMul x l c' := by
  funext k; simp [colMul, add_mul]

theorem colMul_mul {m n : ℕ} (x : Mx D m n) (l : Fin n) (b c : AE D) :
    (fun k => b * colMul x l c k) = colMul x l (b * c) := by
  funext k; simp [colMul, mul_assoc]

theorem mul_mem_latMul {S : HSp D} {𝔞 𝔟 : Set D.host.E} {L L' : Lat S} {P : Pl D → Prop} (b : D.host.E)
    (h : ∀ a ∈ 𝔞, ∀ x ∈ L, ∃ a' ∈ 𝔟, ∃ x' ∈ L', ∀ i, b * (a * x i) = a' * x' i)
    {y : Fin S.rank → AE D} (hy : y ∈ latMul S 𝔞 L P) : (fun i => incA D b * y i) ∈ latMul S 𝔟 L' P := by
  let f : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := (AddMonoidHom.mulLeft (incA D b)).compLeft (Fin S.rank)
  have hle : latMul S 𝔞 L P ≤ (latMul S 𝔟 L' P).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hs, a, ha, x, hx, rfl⟩
    obtain ⟨a', ha', x', hx', e⟩ := h a ha x hx
    refine AddSubgroup.subset_closure ⟨α, hα, hs, a', ha', x', hx', ?_⟩
    funext i
    show incA D b * _ = _
    rw [incA_mul_tmul, e]
  exact hle hy

theorem latV_to_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {α : D.host.E} (hα : α ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => incA D α * y i) ∈ latA S L P :=
  mul_mem_latMul α (fun a ha x hx => ⟨α, hα, x, hx, fun i => by rw [Set.mem_singleton_iff.1 ha]; ring⟩) hy

theorem latA_to_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} (hAA : D.host.AA ≠ 0) {β : D.host.E}
    (hβ : β ∈ D.host.AA⁻¹) {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : (fun i => incA D β * y i) ∈ latV S L P := by
  refine mul_mem_latMul β (fun a ha x hx => ?_) hy
  have hm : β * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [← inv_mul_cancel₀ hAA]; exact FractionalIdeal.mul_mem_mul hβ ha
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  refine ⟨1, rfl, o • x, L.smul_mem o hx, fun i => ?_⟩
  rw [Pi.smul_apply, Algebra.smul_def, ho]; ring

theorem latA_eq_zero (hAA : D.host.AA = 0) {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latA S L P) : y = 0 := by
  have hle : latA S L P ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hs, a, ha, x, hx, rfl⟩
    have ha0 : a = 0 := by
      have : a ∈ D.host.AA := ha
      rw [hAA] at this; exact (FractionalIdeal.mem_zero_iff _).1 this
    funext i
    simp [ha0]
  simpa using hle hy

theorem idAt_eq_zero_of_AA (hAA : D.host.AA = 0) {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ)
    (LV : Lat V) (LW : Lat W) (v : Pl D) (hsdV : IsSelfDualC V LV) (hC : ColsAt dV dW.jX LV LW v) (i : Fin ρ)
    (a : AE D) (ha : a ∈ idAt D (· = v)) : a = 0 := by
  have hs := GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)
  rw [mul_one] at hs
  have hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩
  set ε := pairA D.host.F 0 (singleV D.host.F v 1) with hεdef
  obtain ⟨N, hN, -, hNL⟩ := GlobalTheory.LatAlmostStd.exists_commensurable LV hsdV.1
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 D.host.E))
    (fun k => dV.e k i)
  choose o ho using hb
  set x : Fin V.rank → D.host.E := ∑ k, Pi.single k (N • ((o k : 𝓞 D.host.E) : D.host.E)) with hxdef
  have hx : x ∈ LV := sum_mem fun k _ => hNL k (o k)
  have hxk : ∀ k, x k = N • (((b : 𝓞 D.host.E) : D.host.E) * dV.e k i) := by
    intro k
    rw [hxdef, Finset.sum_apply, Finset.sum_eq_single k (fun l _ hl => Pi.single_eq_of_ne' hl _)
      (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same]
    congr 1
    rw [show ((o k : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (o k) from rfl, ho k]
    first | rfl | exact Algebra.smul_def _ _
  set t : D.host.E := N • ((b : 𝓞 D.host.E) : D.host.E) with htdef
  set c : AE D := ε ⊗ₜ[D.host.F] t with hcdef
  have hc : c ∈ idAt D (· = v) := GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _
  have hyc : colMul dV.jX i c ∈ latV V LV (· = v) := by
    refine AddSubgroup.subset_closure ⟨_, hs.1, hs.2, 1, rfl, x, hx, ?_⟩
    funext k
    rw [one_mul, hxk k]
    show c * incA D (dV.e k i) = _
    rw [mul_comm, incA_mul_tmul, htdef]
    congr 1
    rw [mul_smul_comm, mul_comm (dV.e k i)]
  have hW := latA_eq_zero hAA ((hC i c hc).1 hyc)
  have hc0 : c = 0 := by
    have h1 := congrFun (congrFun dW.pX_jX i) i
    rw [Matrix.one_apply_eq, Matrix.mul_apply] at h1
    rw [← mul_one c, ← h1, Finset.mul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := congrFun hW k
    simp only [colMul, Pi.zero_apply] at this
    rw [mul_comm (dW.pX i k), ← mul_assoc, this, zero_mul]
  have ht : t ≠ 0 := by
    rw [htdef]
    refine smul_ne_zero hN ?_
    exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have hεc : algebraMap (AF D.host.F) (AE D) ε = c * incA D t⁻¹ := by
    rw [hcdef, mul_comm, incA_mul_tmul, inv_mul_cancel₀ ht]; rfl
  rw [← ((placeIdem_acts D v ε hp).1 a).1 ha, hεc, hc0, zero_mul, zero_mul]

end GlobalTheory.FinPl.RatioAA

open GlobalTheory.FinPl.RatioAA in

theorem GlobalTheory.FinPl.ratio_of_colsAt : ∀ (D : D7) (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i j : Fin ρ) (r : AE D), r ∈ idAt D (· = v) → (∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (r * a) ∈ latV V LV (· = v)) → ∀ a ∈ idAt D (· = v), colMul dW.jX j a ∈ latV W LW (· = v) → colMul dW.jX i (r * a) ∈ latV W LW (· = v) := by
  intro D V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v _ hsdV _ _ _ hC i j r hr H a ha hja
  by_cases hAA : D.host.AA = 0
  · rw [idAt_eq_zero_of_AA hAA dV dW LV LW v hsdV hC i a ha, mul_zero]
    have : colMul dW.jX i (0 : AE D) = 0 := by funext k; simp [colMul]
    rw [this]; exact zero_mem _
  · have key : ∀ t ∈ D.host.AA * D.host.AA⁻¹, colMul dW.jX i (incA D t * (r * a)) ∈ latV W LW (· = v) := by
      intro t ht
      refine FractionalIdeal.mul_induction_on ht (fun α hα β hβ => ?_) (fun x y hx hy => ?_)
      · have h1 := latV_to_latA hα hja
        rw [colMul_mul] at h1
        have hαa : incA D α * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ha
        have h2 := (hC j _ hαa).2 h1
        have h3 := H _ h2
        have h4 := (hC i _ (Ideal.mul_mem_left _ r hαa)).1 h3
        have h5 := latA_to_latV hAA hβ h4
        rw [colMul_mul] at h5
        convert h5 using 2
        rw [map_mul]; ring
      · rw [map_add, add_mul, colMul_add]; exact add_mem hx hy
    have := key 1 (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)
    simpa using this
