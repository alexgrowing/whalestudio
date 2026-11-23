import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * y i) ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem mxAt_mul_left {P : Pl D → Prop} {a b c : ℕ} (y : Mx D a b) {x : Mx D b c} (hx : MxAt P x) :
    MxAt P (y ⬝ x) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem mxAt_mul_right {P : Pl D → Prop} {a b c : ℕ} {x : Mx D a b} (hx : MxAt P x) (y : Mx D b c) :
    MxAt P (x ⬝ y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem jX_pX_mem_latV {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {u : Fin T.rank → AE D} (hu : u ∈ latV T L (· = v)) :
    d.jX *ᵥ (d.pX *ᵥ u) ∈ latV T L (· = v) := by
  have h := ((hm u).1 hu).1
  have heq : d.jX *ᵥ (d.pX *ᵥ u) = ∑ i, colMul d.jX i ((d.pX *ᵥ u) i) := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [heq]
  exact sum_mem fun i _ => h i

theorem jX_pX_mem_latA {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin T.rank → AE D} (hz : z ∈ latA T L (· = v)) :
    d.jX *ᵥ (d.pX *ᵥ z) ∈ latA T L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin T.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV T L (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.jX *ᵥ (d.pX *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i))) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.jX *ᵥ (d.pX *ᵥ u)) k := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact smul_mem_latA ha (jX_pX_mem_latV d hm hu')
  | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add, Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg, Matrix.mulVec_neg]; exact neg_mem hz

theorem wittExtZero_inclusionX_mem_homLatticeCompletion {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {LS : Lat S}
    {LS₀ : Lat S₀} {LT : Lat T} {LT₀ : Lat T₀} {v : Pl D} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hS₀ : IsSelfDualC S₀ LS₀) (hmS : MonoAt dS LS LS₀ v) (hmT : MonoAt dT LT LT₀ v) {w : WO S₀ T}
    (hw : w ∈ latO S₀ T (LS₀ : Set _) (LT : Set _) (· = v)) :
    dS.ext0 T (dT.incX S₀ (dT.pX ⬝ w)) ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨?_, fun y hy => ?_⟩
  · rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply]
    exact mxAt_mul_right (mxAt_mul_left _ (mxAt_mul_left _ hx)) _
  · change (dT.jX * (dT.pX * w) * dS.p0) *ᵥ y ∈ latA T LT (· = v)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v) := ((hmS y).1 hy).2.2
    exact jX_pX_mem_latA dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem wittExtZero_inclusionX_smul {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) (c : AE D)
    (ξ : Mx D σ S₀.rank) : dS.ext0 T (dT.incX S₀ (c • ξ)) = c • dS.ext0 T (dT.incX S₀ ξ) := by
  rw [HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, HypDec.incX_apply, Matrix.mul_smul, Matrix.smul_mul]

theorem incAdj_smul {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (c : AE D) (y : Mx D S.rank ρ) :
    d.incAdj S (c • y) = cA D c • d.incAdj S y := by
  rw [HypDec.incAdj_apply, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incY_apply, adj_smul, Matrix.smul_mul,
    smul_comm (incA D (-D.host.xi0⁻¹)) (cA D c), Matrix.mul_smul]

theorem symplO_incAdj_proj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T) :
    symplO S T (d.incAdj S z) w = symplO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
  have key : hO S T (d.incAdj S z) w = hO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
    rw [d.hO_coordT S, d.hO_coordT S]
    simp only [HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, ← Matrix.mul_assoc, HypDec.pX_jY,
      HypDec.p0_jY, HypDec.pY_jY, HypDec.pX_jX, HypDec.p0_jX, HypDec.pY_jX, Matrix.zero_mul, Matrix.one_mul]
    simp [pairT, hO]
  rw [symplO, symplO, key]

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem half_smul_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : Pl D} (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) {u : WO S T} (hu : u ∈ latO S T LS LT (· = v)) :
    (pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) * algebraMap D.host.F (Af D.host.F) (2 : D.host.F)⁻¹)
      ⊗ₜ[D.host.F] (1 : D.host.E)) • u ∈ latO S T LS LT (· = v) := by
  classical
  set γ := GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) * algebraMap D.host.F (Af D.host.F) (2 : D.host.F)⁻¹ with hγ
  have hγi : γ ∈ intAf D.host.F := fun w => by
    rw [hγ, map_mul, AlgHom.commutes, GlobalTheory.FinPl.LatMem.evalV_indP]
    split_ifs with hw
    · subst hw; rw [one_mul]; exact GlobalTheory.LatVac.half_mem_adicCompletionIntegers _ _ h2
    · rw [zero_mul]; exact zero_mem _
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, s, hs, t, ht, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨γ * β, GlobalTheory.FinPl.LatMem.intAf_mul' hγi hβi,
      fun w hw => by rw [map_mul, hβ w hw, mul_zero], a, ha, s, hs, t, ht, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [show pairA D.host.F 0 γ * pairA D.host.F 0 β = pairA D.host.F 0 (γ * β) from Prod.ext (mul_zero _) rfl]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem exists_idemAt (D : D7) (v : Pl D) : ∃ e : AE D, e ∈ intAt D (· = v) ∧ (∀ a ∈ idAt D (· = v), a * e = a) ∧
    cA D e = e ∧ ((2 : 𝓞 D.host.F) ∉ v.asIdeal → ∃ c : AE D, c + c = e ∧ ∀ (S T : HSp D)
      (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (u : WO S T),
        u ∈ latO S T LS LT (· = v) → c • u ∈ latO S T LS LT (· = v)) := by
  have hid : pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ idAt D (· = v) :=
    GlobalTheory.FinPl.LatMem.tmul_mem_idAt (GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _) 1
  have hact : ∀ a ∈ idAt D (· = v),
      a * (pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E)) = a :=
    fun a ha => GlobalTheory.FinPl.LatMem.mul_indP ha
  refine ⟨_, ⟨hid, GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hact _ hid])⟩, hact,
    GlobalTheory.SelfDualAt.cA_alg _, fun h2 => ⟨_, ?_, fun S T LS LT u hu => half_smul_mem h2 hu⟩⟩
  rw [← TensorProduct.add_tmul]
  congr 1
  refine Prod.ext (add_zero _) ?_
  show _ * _ + _ * _ = _
  rw [← mul_add, ← map_add, show (2 : D.host.F)⁻¹ + 2⁻¹ = 1 by norm_num, map_one, mul_one]
  all_goals rfl

theorem fix_char {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
    {P : Pl D → Prop} {𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)} (h𝔉 : IsFlatBF s P 𝔉) {f : WO B.V J.W → ℂ}
    (hθ : IsThetaFunO ψ B.V J.W f) (t : GL (Fin ρ) (AE D)) (hne : 𝔉 (s.om (1, J.d.levi t) f) ≠ 0)
    (ξ : Mx D ρ B.V₀.rank) (hξ : MxAt P ξ) (hfix : heisO ψ B.V J.W (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) f = f) :
    ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) = 1 := by
  have hg : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hθ
  have hact : actO B.V J.W 1 (J.d.levi t) (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) =
      B.d.ext0 J.W (J.d.incX B.V₀ (t.1 ⬝ ξ)) := by
    rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply,
      HypDec.incX_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, HypDec.levi_jX]
  have h1 := s.weil.om_heis 1 (J.d.levi t) (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) f hθ
  rw [hfix, hact] at h1
  have h3 := h𝔉.Heisenberg₂.iso _ hg (t.1 ⬝ ξ) (mxAt_mul_left _ hξ)
  rw [← h1] at h3
  by_contra hc
  apply hne
  funext w
  have hw := congrFun h3 w
  rw [Pi.smul_apply, smul_eq_mul] at hw
  have h4 : (ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) - 1) *
      𝔉 (s.om (1, J.d.levi t) f) w = 0 := by
    rw [sub_mul, ← hw, one_mul, sub_self]
  exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hc)

theorem yZero_mul_diag (S : HSp D) {ρ : ℕ} (z : Fin S.rank → D.host.E) (t : Matrix (Fin ρ) (Fin ρ) (AE D))
    (ht : ∀ i j, i ≠ j → t i j = 0) (i : Fin ρ) (hi : i.1 + 1 = ρ) : yZero S ρ z ⬝ t = t i i • yZero S ρ z := by
  classical
  have hell : ∀ j : Fin ρ, ell D ρ j = if j = i then 1 else 0 := fun j => by
    by_cases hj : j = i
    · subst hj; simp [ell, hi]
    · have hj' : ¬ (j.1 + 1 = ρ) := fun h => hj (Fin.ext (by omega))
      simp [ell, hj', hj]
  ext k l
  have hy : ∀ j, yZero S ρ z k j = if j = i then -ratV z k else 0 := fun j => by
    simp only [yZero, zEll, Matrix.neg_apply, Matrix.vecMulVec_apply, hell]
    split_ifs <;> simp
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hy l]
  simp only [hy, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hl : l = i
  · subst hl; rw [if_pos rfl, mul_comm]
  · rw [if_neg hl, ht i l (Ne.symm hl), mul_zero, mul_zero]

theorem symplO_incAdj_eq {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T) :
    symplO S T (d.incAdj S z) w = -Algebra.trace (AF D.host.F) (AE D) (z ⬝ (d.pX ⬝ w)).trace := by
  rw [symplO_incAdj_proj, GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj]

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : MxAt P x) : MxAt P (c • x) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hx i j)

theorem smul_isHalf' {e : AE D} (he : e * e = e) {m n : ℕ} (u : Mx D m n) : IsHalf e (e • u) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

theorem smul_eq_self {P : Pl D → Prop} {e : AE D} (he : ∀ a ∈ idAt D P, e * a = a) {m n : ℕ} {x : Mx D m n}
    (hx : MxAt P x) : e • x = x := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact he _ (hx i j)

theorem add_smul_mx {m n : ℕ} (a b : AE D) (x : Mx D m n) : a • x + b • x = (a + b) • x := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul]

theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (t : Matrix (Fin ρ) (Fin ρ) (AE D)) (ξ₁ ξ₂ : Mx D ρ S.rank) :
    ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ (ξ₁ + ξ₂)))) =
      ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ ξ₁))) * ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ ξ₂))) := by
  rw [Matrix.mul_add, map_add, symplO_add_right', AddChar.map_add_eq_mul]

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

set_option maxHeartbeats 1000000 in

theorem last_diag_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG hne i hi
  obtain ⟨hθ, h2, hh⟩ := hf
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨eV, heV_int, heV_act, heV_cA, hhalf⟩ := exists_idemAt D v
  have heV_id : eV ∈ idAt D (· = v) := heV_int.1
  have hcA : ∀ c ∈ idAt D (· = v), cA D c ∈ idAt D (· = v) := fun c hc => by
    rw [← heV_act c hc, map_mul, heV_cA]; exact Ideal.mul_mem_left _ _ heV_id
  have hMx : ∀ c ∈ idAt D (· = v), MxAt (· = v) (J.d.incAdj B.V₀ (c • yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun c hc k l => by
      rw [incAdj_smul, Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (hcA c hc)

  have hcong := (GlobalTheory.IwaPlace.mem_congGrp_iff J.W (idAt D (· = v)) _).1 htG
  have hM : MxAt (· = v) (mt J.W (J.d.levi t) - 1) := fun k l => by rw [Matrix.sub_apply]; exact hcong k l
  have htM : t.1 - 1 = J.d.pX ⬝ (mt J.W (J.d.levi t) - 1) ⬝ J.d.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, J.d.pX_levi t, Matrix.mul_one, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have ha : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := mxAt_mul_right (mxAt_mul_left J.d.pX hM) J.d.jX i i
    rwa [← htM, Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hρ : 0 < ρ := by omega
  rw [← hG.last hρ _ ha]
  refine (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hstd B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ ha)).2 fun u' hu' => ?_
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = J.d.pX ⬝ u' := ⟨_, rfl⟩
  have hξ : MxAt (· = v) ξ := hξdef ▸ mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu')
  have hu : B.d.ext0 J.W (J.d.incX B.V₀ ξ) ∈ latO B.V J.W (LV : Set _) (LW : Set _) (· = v) :=
    hξdef ▸ wittExtZero_inclusionX_mem_homLatticeCompletion B.d J.d hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hu'
  have hξe : eV • ξ = ξ := smul_eq_self (fun a ha => (mul_comm eV a).trans (heV_act a ha)) hξ

  have hχ : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) = 1 := by
    rcases hG.tame.2 with h2v | ⟨e, ε, he, hε, hes⟩
    · obtain ⟨c, hcc, hcl⟩ := hhalf h2v
      have hcu := hcl _ _ _ _ _ hu
      rw [← wittExtZero_inclusionX_smul] at hcu
      have hfix := h2 _ hcu
      rw [← map_nsmul (B.d.ext0 J.W), ← map_nsmul (J.d.incX B.V₀)] at hfix
      have h2c : 2 • (c • ξ) = ξ := by
        rw [two_nsmul, add_smul_mx, hcc, hξe]
      rw [h2c] at hfix
      exact fix_char s h𝔉 hθ t hne ξ hξ hfix
    · have hact := (GlobalTheory.FinPl.placeIdem_acts D v ε hε).1
      have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
      have hfixE : ∀ e' : AE D, IsSplitIdem D e' →
          heisO ψ B.V J.W (B.d.ext0 J.W (J.d.incX B.V₀ (e' • ξ))) f = f := by
        intro e' he'
        have hmem := GlobalTheory.LatticeStable.smul_mem_latO D B.V J.W _ _ (· = v) e'
          (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he'.1])) _ hu
        rw [← wittExtZero_inclusionX_smul] at hmem
        refine hh e' he' _ hmem ?_
        rw [wittExtZero_inclusionX_smul]
        exact smul_isHalf' he'.1 _
      have hMe : ∀ e' : AE D, MxAt (· = v) (e' • ξ) := fun e' => mxAt_smul e' hξ
      have h1 := fix_char s h𝔉 hθ t hne _ (hMe e) (hfixE e he)
      have h2' := fix_char s h𝔉 hθ t hne _ (hMe (cA D e)) (hfixE _ hce)
      have hsum : e • ξ + cA D e • ξ = ξ := by
        rw [add_smul_mx, hes]
        exact smul_eq_self (fun a ha => (hact a).1 ha) hξ
      have hk := chi_add ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) t.1 (e • ξ) (cA D e • ξ)
      rw [hsum, h1, h2', mul_one] at hk
      exact hk
  have hε' := (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hstd B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ heV_id)).1
    ((hG.last hρ eV heV_id).2 heV_int) u' hu'
  rw [symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, ← Matrix.mul_smul, hξe] at hε'
  have hχ' := hχ
  rw [GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc,
    yZero_mul_diag _ _ t.1 ht i hi, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at hχ'
  have hT : ψ (Algebra.trace (AF D.host.F) (AE D) (yZero B.V₀ ρ (vecB B.o B.ζ) ⬝ ξ).trace) = 1 := by
    rw [AddChar.map_neg_eq_inv] at hε'
    exact inv_eq_one.1 hε'
  rw [symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sub_mul, one_mul, map_sub, neg_sub,
    sub_eq_add_neg, AddChar.map_add_eq_mul, hT, hχ', one_mul]

end GlobalTheory.FinPl.LastDiag
