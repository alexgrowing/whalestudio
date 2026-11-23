import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPoincareSeriesThetaVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourierStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteRationalPointsCompletedLattice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatTrace

open GlobalTheory.SplitScalar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem beta_iota_right (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (x : WO S T) (v : RW T S) :
    ψ (symplOH S T x (iotaW σ T S v)) = Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) v : ℝ)) := by
  rw [GlobalTheory.OrientedChar.char_symplOH D θ ψ hσ.inf hψ S T _ _ (Or.inr (hσ.real_iota T S v)), hσ.pi_iota]

theorem beta_iota_left (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (v : RW T S) (x : WO S T) :
    ψ (symplOH S T (iotaW σ T S v) x) = Complex.exp (-(Real.pi * Complex.I) * (omO S T v (piW θ T S x) : ℝ)) := by
  rw [GlobalTheory.OrientedChar.char_symplOH D θ ψ hσ.inf hψ S T _ _ (Or.inl (hσ.real_iota T S v)), hσ.pi_iota]

theorem beta_fin (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplOH S T (finRat S T x) (finRat S T y)) *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℝ)) = 1 := by
  obtain ⟨c, hc⟩ := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 (ratW T S x) ⟨x, rfl⟩ (ratW T S y) ⟨y, rfl⟩
  have h1 : ψ (symplOH S T (ratW T S x) (ratW T S y)) = 1 := by
    rw [hc]; exact hψ.1.2.2.1 c
  have h2 := beta_iota_left hψ hσ (infRat S T x) (ratW T S y)
  have h3 := beta_iota_right hψ hσ (finRat S T x) (infRat S T y)
  rw [piW_of_inf θ (finRat_inf S T x), LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at h3
  have d1 : symplOH S T (ratW T S x) (ratW T S y) =
      symplOH S T (iotaW σ T S (infRat S T x)) (ratW T S y) + symplOH S T (finRat S T x) (ratW T S y) :=
    (congrArg (fun w => symplOH S T w (ratW T S y)) (ratW_eq hσ S T x)).trans (symplOH_add_left S T _ _ _)
  have d2 : symplOH S T (finRat S T x) (ratW T S y) =
      symplOH S T (finRat S T x) (iotaW σ T S (infRat S T y)) + symplOH S T (finRat S T x) (finRat S T y) :=
    (congrArg (fun w => symplOH S T (finRat S T x) w) (ratW_eq hσ S T y)).trans (symplOH_add_right S T _ _ _)
  rw [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h2, h3, one_mul, mul_comm, piW_ratW hσ.inf] at h1
  exact h1

theorem fin_smul_iota (hσ : Chart θ σ) (v : RW T S) : (1 - realIdem D) • (iotaW σ T S v : WO S T) = 0 := by
  rw [sub_smul, one_smul, sub_eq_zero]
  exact (Matrix.ext fun i j => realIdem_mul_of_real (congrFun (congrFun (hσ.real_iota T S v) i) j)).symm

theorem fin_smul_XF (y : XF S T) : (1 - realIdem D) • (y : WO S T) = y := by
  rw [sub_smul, one_smul, mem_finSub_iff.1 y.fin, sub_zero]

theorem chiLat_add_iota (hσ : Chart θ σ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (x : WO S T) (v : RW T S) :
    chiLat ψ S T LS LT w (x + iotaW σ T S v) = chiLat ψ S T LS LT w x := by
  unfold chiLat
  rw [smul_add, fin_smul_iota hσ, add_zero]

theorem ratW_injective (hθ : IsInfFam θ) : Function.Injective (ratW T S) := fun x y h =>
  infRat_injective S T (by rw [← piW_ratW hθ, ← piW_ratW hθ, h])

def ratEquiv (hθ : IsInfFam θ) (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E ≃ ratL T S :=
  Equiv.ofBijective (fun y => ⟨ratW T S y, y, rfl⟩)
    ⟨fun _ _ h => ratW_injective hθ (congrArg Subtype.val h), by rintro ⟨_, y, rfl⟩; exact ⟨y, rfl⟩⟩

theorem coe_ratEquiv (hθ : IsInfFam θ) (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (ratEquiv hθ S T y : WO S T) = ratW T S y := rfl

theorem serO_eq (hθ : IsInfFam θ) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E))
    (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (a : RW T S) (x : WO S T) :
    serO ψ θ σ S T sS sT LS LT w a x = ∑' y : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      ψ (symplOH S T (ratW T S y) x) * ψ (symplOH S T (iotaW σ T S a) (ratW T S y + x)) *
        chiLat ψ S T LS LT w (ratW T S y + x) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (omO S T (infRat S T y + (a + piW θ T S x))
          (jO S T sS sT (infRat S T y + (a + piW θ T S x))) : ℝ)) := by
  unfold serO GlobalTheory.HeisenbergGaussianSeries.series
  rw [← (ratEquiv hθ S T).tsum_eq]
  simp only [coe_ratEquiv, piW_ratW hθ]

section Act

variable {g : GA D S} {h : GA D T} {a : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
  {b : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (hg : Formalism.L2.Theta.mt S g = a.map (incA D))
  (hh : Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D))
include hg hh

theorem act_eq (x : WO S T) : actO S T g⁻¹ h⁻¹ x =
    HMul.hMul (HMul.hMul (b.map (incA D)) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (a.map (incA D)) := by
  rw [actO, inv_inv, hg, hh]

theorem act_ratW (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    actO S T g⁻¹ h⁻¹ (ratW T S y) = ratW T S (b * y * a) := by
  rw [act_eq hg hh, ratW, ratW, Matrix.map_mul, Matrix.map_mul]

theorem act_finRat (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    actO S T g⁻¹ h⁻¹ (finRat S T y) = finRat S T (b * y * a) := by
  rw [finRat_eq, finRat_eq, actO_smul, act_ratW hg hh]

theorem piW_act (hθ : IsInfFam θ) (x : WO S T) : piW θ T S (actO S T g⁻¹ h⁻¹ x) =
    actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) (piW θ T S x) := by
  funext τ
  have hi : ∀ {n : ℕ} (m : Matrix (Fin n) (Fin n) D.host.E),
      (m.map (incA D)).map ((θ τ).comp (infPart D)) = m.map (tauE D τ) := fun m => by
    funext i j
    exact comp_incA hθ τ _
  rw [act_eq hg hh]
  show (HMul.hMul (HMul.hMul (b.map (incA D)) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (a.map (incA D))).map
      ((θ τ).comp (infPart D)) =
    HMul.hMul (HMul.hMul (b.map (tauE D τ)) (x.map ((θ τ).comp (infPart D)))) (a.map (tauE D τ))
  rw [Matrix.map_mul, Matrix.map_mul, hi, hi]

theorem act_iota (hσ : Chart θ σ) (v : RW T S) : actO S T g⁻¹ h⁻¹ (iotaW σ T S v) =
    iotaW σ T S (actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v) := by
  refine hσ.real_ext (V := T) (W := S) ?_ (hσ.real_iota T S _) ?_
  · have e : (iotaW σ T S v : WO S T) = realIdem D • iotaW σ T S v := by
      have := fin_smul_iota hσ v
      rwa [sub_smul, one_smul, sub_eq_zero] at this
    rw [e, actO_smul]
    exact real_smul_real _
  · rw [piW_act hg hh hσ.inf, hσ.pi_iota, hσ.pi_iota]

theorem omO_act (hσ : Chart θ σ) (u v : RW T S) :
    omO S T (actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) u)
      (actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v) = omO S T u v := by
  rw [← hσ.pi_iota T S u, ← hσ.pi_iota T S v, ← piW_act hg hh hσ.inf, ← piW_act hg hh hσ.inf, omO_apply, omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.OrientedChar.valTau_symplO hσ.inf, ← GlobalTheory.OrientedChar.valTau_symplO hσ.inf, GlobalTheory.T.symplecticForm_unitaryPairAction]

theorem actR_add_infRat (hσ : Chart θ σ) (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : RW T S) :
    actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) (infRat S T y + v) =
      infRat S T (b * y * a) + actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v := by
  rw [← piW_ratW hσ.inf, ← piW_ratW hσ.inf, ← act_ratW hg hh, ← hσ.pi_iota T S v, ← map_add,
    ← piW_act hg hh hσ.inf, ← piW_act hg hh hσ.inf, actO_add, map_add]

end Act

theorem phase_identity {W : AE D} (hW : W + cA D W = 1) (U Y : WO S T)
    (hi : symplOH S T (W • (U + Y)) (U + Y) = symplOH S T (W • Y) Y) :
    symplOH S T (W • U) U + symplOH S T (U + Y) Y = symplO S T (cA D W • U) Y := by
  have h1 : symplOH S T Y Y = 0 := by rw [symplOH, symplO_self, mul_zero]
  have h2 : symplOH S T U Y = symplOH S T (W • U) Y + symplOH S T (cA D W • U) Y := by
    rw [← symplOH_add_left, ← add_smul, hW, one_smul]
  have h3 : symplOH S T (W • Y) U = -symplOH S T (cA D W • U) Y := by
    rw [symplOH_smul, symplOH_skew]
  rw [smul_add, symplOH_add_left, symplOH_add_right, symplOH_add_right] at hi
  rw [symplOH_add_left, ← symplOH_add_self]
  linear_combination hi + h1 + h2 - h3

theorem gam_periodic {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {s : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (H : IsHeis s w γ W) {A : Submodule R X}
    (hA : SelfDual γ A) (φ : X →ₗ[R] X) (hφ : ∀ x y, γ (φ x) (φ y) = γ x y) (r : R) {y c : X} (hy : φ y - y ∈ A)
    (hc : c ∈ A) (hc' : φ c ∈ A) : γ (r • (φ (y + c) - (y + c))) (y + c) = γ (r • (φ y - y)) y := by
  have e1 : φ (y + c) - (y + c) = (φ y - y) + (φ c - c) := by rw [map_add]; abel
  have e2 : γ (r • c) y = γ (r • φ c) y := by
    rw [← hφ, map_smul, ← sub_add_cancel (φ y) y, H.add_right, H.iso hA (A.smul_mem r hc') hy, one_mul]
  have e3 : γ (r • (φ c - c)) y = 1 := by
    rw [smul_sub, sub_eq_add_neg, H.add_left, H.neg_left, e2, mul_inv_cancel₀ (H.ne_zero _ _)]
  rw [H.add_right, H.iso hA (A.smul_mem r (e1 ▸ A.add_mem hy (A.sub_mem hc' hc))) hc, mul_one, e1, smul_add,
    H.add_left, e3, mul_one]

def finX (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[𝓞 D.host.E] XF S T where
  toFun y := XF.mk (finRat S T y) (finRat_inf S T y)
  map_add' x y := XF.ext (map_add (finRat S T) x y)
  map_smul' r x := XF.ext (finRat_smul S T (r : D.host.E) x)

theorem gamQ_eq (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    gamQ ψ S T x y = gamF ψ S T (finX S T x) (finX S T y) := rfl

open Classical in

def gaussQ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E))
    (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℂ :=
  if b * y * a - y ∈ latQ S T LS LT then gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * y * a - y)) y else 0

section Left

variable {g : GA D S} {h : GA D T} {a : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
  {b : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (hg : Formalism.L2.Theta.mt S g = a.map (incA D))
  (hh : Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D))
include hg hh

theorem rhoF_finX (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    rhoF S T (g⁻¹, h⁻¹) (finX S T y) = finX S T (b * y * a) := XF.ext (act_finRat hg hh y)

theorem chiLat_mul_exp (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (LS : Set (Fin S.rank → D.host.E))
    (LT : Set (Fin T.rank → D.host.E)) {w : 𝓞 D.host.E} (hw : w + GlobalTheory.FinWeil.sgO D w = 1)
    (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    chiLat ψ S T LS LT w (ratW T S (b * y * a - y)) = gaussQ ψ S T LS LT w a b y *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (infRat S T (b * y * a)) (infRat S T y) : ℝ)) := by
  unfold chiLat gaussQ
  rw [← finRat_eq]
  by_cases hy : b * y * a - y ∈ latQ S T LS LT
  · rw [if_pos hy, if_pos (mem_latQ.1 hy)]
    have e : finRat S T (b * y * a - y) + finRat S T y = finRat S T (b * y * a) := by
      rw [← map_add, sub_add_cancel]
    have h1 := phase_identity (W := intA D w) (by rw [cA_intA, ← RingHom.map_add, hw, RingHom.map_one])
      (finRat S T (b * y * a - y)) (finRat S T y)
      (by rw [e, ← act_finRat hg hh, ← actO_smul, symplOH, symplOH, GlobalTheory.T.symplecticForm_unitaryPairAction])
    have h2 : gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * y * a - y)) y =
        ψ (symplO S T (cA D (intA D w) • finRat S T (b * y * a - y)) (finRat S T y)) := by
      rw [gamQ_eq, map_smul, cA_intA]
      rfl
    rw [h2, ← h1, e, AddChar.map_add_eq_mul, mul_assoc, beta_fin hψ hσ, mul_one]
  · rw [if_neg hy, if_neg (fun h => hy (mem_latQ.2 h)), zero_mul]

theorem left_side (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (halt : ∀ x y, omO S T x y = -omO S T y x)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) {w : 𝓞 D.host.E}
    (hw : w + GlobalTheory.FinWeil.sgO D w = 1)
    (hb : Function.Bijective fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) (v : RW T S) :
    serO ψ θ σ S T sS sT LS LT w (-v) (actO S T g⁻¹ h⁻¹ (iotaW σ T S v)) =
      ∑' y, gaussQ ψ S T LS LT w a b y *
        gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) (infRat S T y + v) := by
  rw [act_iota hg hh hσ, serO_eq hσ.inf, ← (Equiv.ofBijective _ hb).tsum_eq]
  refine tsum_congr fun y => ?_
  have h0 := omO_act hg hh hσ (infRat S T y) v
  have h1 := actR_add_infRat hg hh hσ y 0
  have h2 : actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) 0 = 0 := by
    funext τ
    exact (congrArg (· * a.map (tauE D τ)) (Matrix.mul_zero _)).trans (Matrix.zero_mul _)
  rw [h2, add_zero, add_zero] at h1
  rw [h1] at h0
  rw [Equiv.ofBijective_apply, chiLat_add_iota hσ, chiLat_mul_exp hg hh hψ hσ LS LT hw, beta_iota_right hψ hσ,
    beta_iota_left hψ hσ, gaussR, actR_add_infRat hg hh hσ, map_add (piW θ T S), hσ.pi_iota, piW_ratW hσ.inf,
    map_sub (infRat S T)]
  generalize actR S T (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v = u at h0 ⊢
  generalize infRat S T (b * y * a) = z at h0 ⊢
  generalize infRat S T y = x at h0 ⊢
  have e1 : z - x + (-v + u) = z + u - (x + v) := by abel
  have e2 : Complex.exp (-(Real.pi * Complex.I) * (omO S T (z - x) u : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (-v) (z - x + u) : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T z x : ℝ)) =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (z + u) (x + v) : ℝ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← mul_add, ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
    congr 3
    simp only [map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply]
    linarith [halt x u, halt v z, halt v x, halt v u]
  rw [e1, ← e2]
  ring

end Left

def coefQ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E))
    (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (u : XF S T) (y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℂ :=
  phase ψ w u * (ψ (symplOH S T (ratW T S y) u) * chiLat ψ S T LS LT w (ratW T S y + u) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omO S T (infRat S T y) (jO S T sS sT (infRat S T y)) : ℝ)))

theorem right_side (hψ : IsStdChar D ψ (-1)) (hσ : Chart θ σ) (halt : ∀ x y, omO S T x y = -omO S T y x)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (u : XF S T) (v : RW T S) :
    (phase ψ w u • heisO ψ S T u (serO ψ θ σ S T sS sT LS LT w (-v))) (iotaW σ T S v) =
      ∑' y, coefQ ψ S T sS sT LS LT w u y *
        Complex.exp (2 * Real.pi * Complex.I * ((-omO S T (infRat S T y)) v : ℝ)) := by
  have hu : piW θ T S (u : WO S T) = 0 := piW_of_inf θ u.fin
  rw [Pi.smul_apply, smul_eq_mul, heisO, beta_iota_left hψ hσ, hu, LinearMap.map_zero, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, serO_eq hσ.inf, ← tsum_mul_left]
  refine tsum_congr fun y => ?_
  have e1 : ratW T S y + (iotaW σ T S v + (u : WO S T)) = (ratW T S y + (u : WO S T)) + iotaW σ T S v := by abel
  have e2 : omO S T v v = 0 := by linarith [halt v v]
  have e3 : Complex.exp (-(Real.pi * Complex.I) * (omO S T (infRat S T y) v : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (-v) (infRat S T y + v) : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((-omO S T (infRat S T y)) v : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [map_add, map_neg, LinearMap.neg_apply, e2, halt v (infRat S T y)]
    push_cast
    ring
  rw [coefQ, symplOH_add_right, AddChar.map_add_eq_mul, beta_iota_right hψ hσ, beta_iota_left hψ hσ,
    map_add (piW θ T S), map_add (piW θ T S), hu, hσ.pi_iota, piW_ratW hσ.inf, add_zero, neg_add_cancel, add_zero, e1,
    chiLat_add_iota hσ, ← e3]
  ring

theorem finite_latQ {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) (R : ℝ) :
    {y | y ∈ latQ S T ΛS ΛT ∧ ‖infRat S T y‖ ≤ R}.Finite := by
  refine (GlobalTheory.CompletedLatticeFinite.finite_rational_points D S T ΛS ΛT dS dT R).subset ?_
  rintro y ⟨h1, h2⟩
  refine ⟨⟨_, h1, ?_⟩, fun τ i j => ?_⟩
  · funext i j
    have e1 : finPart D (finRat S T y i j) = finPart D (ratW T S y i j) := rfl
    show finPart D (ratW T S y i j - finRat S T y i j) = 0
    rw [RingHom.map_sub, e1, sub_self]
  · let z : RW T S := infRat S T y
    exact ((norm_le_pi_norm (z τ i) j).trans ((norm_le_pi_norm (z τ) i).trans (norm_le_pi_norm z τ))).trans h2

theorem summable_coefQ (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hpos : ∀ v, v ≠ 0 → 0 < omO S T v (jO S T sS sT v)) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (w : 𝓞 D.host.E) (u : XF S T) : Summable fun y => ‖coefQ ψ S T sS sT ΛS ΛT w u y‖ := by
  have h := GlobalTheory.HeisenbergGaussianSeries.summable_coeff (G := WO S T) (piW θ T S) (omO S T) (jO S T sS sT) (ratL T S)
    ((latO S T ΛS ΛT fun _ => True).comap (DistribSMul.toAddMonoidHom (WO S T) (1 - realIdem D)))
    (chiLat ψ S T ΛS ΛT w) hpos
    (by
      rintro _ ⟨y, rfl⟩ hy
      have : y = 0 := infRat_injective S T (((piW_ratW hθ S T y).symm.trans hy).trans (map_zero _).symm)
      rw [this, map_zero])
    (fun R => by
      refine ((finite_latQ dS dT R).image (ratW T S)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      exact ⟨y, ⟨mem_latQ.2 (by rw [finRat_eq]; exact h1), by rw [← piW_ratW hθ]; exact h2⟩, rfl⟩)
    (fun x hx => if_neg hx)
    (fun x => by
      unfold chiLat
      split_ifs
      · exact (hψ.1.2.1 _).le
      · simp)
    (fun y => ψ (symplOH S T y u)) (fun y => hψ.1.2.1 _) u 0 0 0
  rw [← (ratEquiv hθ S T).summable_iff] at h
  refine h.congr fun y => ?_
  have e : ‖phase ψ w u‖ = 1 := hψ.1.2.1 _
  simp only [Function.comp_apply, coe_ratEquiv, piW_ratW hθ, add_zero, zero_mul, Real.exp_zero, mul_one]
  rw [coefQ, norm_mul (phase ψ w u), e, one_mul]

theorem mem_of_coefQ_ne_zero {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {w : 𝓞 D.host.E} {u : XF S T} {y : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (h : coefQ ψ S T sS sT LS LT w u y ≠ 0) : finX S T y + u ∈ latF S T LS LT := by
  by_contra hn
  apply h
  have e : chiLat ψ S T LS LT w (ratW T S y + u) = 0 := by
    unfold chiLat
    rw [smul_add, ← finRat_eq, fin_smul_XF]
    exact if_neg hn
  rw [coefQ, e, mul_zero, zero_mul, mul_zero]

theorem coefQ_zero (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} (w : 𝓞 D.host.E) {u : XF S T} (hu : u ∈ latF S T LS LT) :
    coefQ ψ S T sS sT LS LT w u 0 = 1 := by
  have e : ratW T S 0 = 0 := Matrix.map_zero _ (incA D).map_zero
  rw [coefQ, e, zero_add, map_zero, symplOH, symplO_zero_left, mul_zero, AddChar.map_zero_eq_one, one_mul, map_zero,
    LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, chiLat, fin_smul_XF,
    if_pos (mem_latF.1 hu), phase, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem gauss_mul_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → Function.Bijective (fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) → Integrable (gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ))) volume → ∀ κ : ℂ, (∀ f : thetaSub ψ S T, Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x, (f : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x) = κ * ((sumOp (opF hψ.1 S T w) (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) f : thetaSub ψ S T) : WO S T → ℂ) x) → ∀ (n : ℕ) (t : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E), (∀ k, b * t k * a - t k ∈ latQ S T ΛS ΛT) → (∀ y, b * y * a - y ∈ latQ S T ΛS ΛT → ∃! k, y - t k ∈ latQ S T ΛS ΛT) → ∃ r : ℝ, 0 < r ∧ (∑ k, gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * t k * a - t k)) (t k)) * ∫ v, gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v = r * κ := by
  intro D ψ hψ θ hθ S T sS sT hS hT ΛS ΛT dS dT w hw g h a b hg hh hb hF κ hκ n t ht hu
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, halt, -, hneg⟩ := GlobalTheory.RealSymplForm.form_alt_inv_def D S T sS sT hS hT
  have hpos : ∀ v, v ≠ 0 → 0 < omO S T v (jO S T sS sT v) := fun v hv => by
    rw [halt]; exact neg_pos.2 (hneg v hv)
  have H := isHeis_opF hψ.1 S T hw
  obtain ⟨lam, hlam, -⟩ := exists_goodNorm D
  obtain ⟨w', Om, hL⟩ := exists_isLatRep hψ dS dT hlam
  have hA := hL.sd
  have hB := hL.sd' (g, h)
  obtain ⟨m, u, huB, huT⟩ := exists_transversal_of_idx_ne_zero _ _ (hL.fin (g, h))
  let C : AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    (latQ S T ΛS ΛT).toAddSubgroup ⊓ (latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom
  have hC : ∀ x, x ∈ C ↔ x ∈ latQ S T ΛS ΛT ∧ b * x * a ∈ latQ S T ΛS ΛT := fun x => Iff.rfl
  have hX : ∀ x, x ∈ latQ S T ΛS ΛT ↔ finX S T x ∈ latF S T ΛS ΛT := fun x => Iff.rfl
  have hQ : ∀ y, b * y * a - y ∈ latQ S T ΛS ΛT →
      gaussQ ψ S T ΛS ΛT w a b y = gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * y * a - y)) y := fun y hy => if_pos hy
  have hQ0 : ∀ y, b * y * a - y ∉ latQ S T ΛS ΛT → gaussQ ψ S T ΛS ΛT w a b y = 0 := fun y hy => if_neg hy
  have h0 : κ * ∑ i, coefQ ψ S T sS sT ΛS ΛT w (u i) 0 = κ := by
    obtain ⟨i, hi, hi'⟩ := huT 0 (zero_mem _)
    rw [Finset.sum_eq_single i, coefQ_zero sS sT w (by simpa using hi), mul_one]
    · intro j _ hj
      by_contra hn
      exact hj (hi' j (by simpa using mem_of_coefQ_ne_zero hn))
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  haveI : (volume : Measure (Fin S.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin T.rank → Fin S.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (RW T S)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have key := GlobalTheory.T.unfold_poincareSeries_lattice_fourier (RW T S) volume _ (infRat S T) (infRat_injective S T) C
    (fun R => (finite_latQ dS dT R).subset fun c hc => ⟨hc.1.1, hc.2⟩) ?_ n t (gaussQ ψ S T ΛS ΛT w a b) ?_ ?_ ?_ _ hF
    (fun y => κ * ∑ i, coefQ ψ S T sS sT ΛS ΛT w (u i) y) (fun y => -omO S T (infRat S T y)) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨r, hr, e⟩ := key
    refine ⟨r, hr, ?_⟩
    rw [h0, Finset.sum_congr rfl fun k _ => hQ _ (ht k)] at e
    exact e
  · rw [eq_top_iff]
    have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
      simpa only [piW_ratW hθ] using span_piW_ratW_eq_top D θ σ hσ T S
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨N, hN, h1⟩ := GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT dS.1 dT.1 y
    obtain ⟨M, hM, h2⟩ := GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT dS.1 dT.1 (b * y * a)
    have h3 : (M * N) • y ∈ C := by
      refine ⟨?_, ?_⟩
      · show finRat S T ((M * N) • y) ∈ latO S T ΛS ΛT fun _ => True
        rw [map_nsmul, mul_smul]
        exact nsmul_mem h1 M
      · show finRat S T (sandw b a ((M * N) • y)) ∈ latO S T ΛS ΛT fun _ => True
        rw [map_nsmul, map_nsmul, mul_comm, mul_smul]
        exact nsmul_mem h2 N
    have h4 : infRat S T y = ((M * N : ℕ) : ℝ)⁻¹ • infRat S T ((M * N) • y) := by
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.2 (Nat.mul_pos hM hN).ne')]
    rw [h4]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h3, rfl⟩)
  · intro y hy
    have h1 : b * y * a - y ∈ latQ S T ΛS ΛT := by_contra fun hn => hy (hQ0 y hn)
    obtain ⟨k, hk, -⟩ := hu y h1
    refine ⟨k, hk, ?_⟩
    have e : b * (y - t k) * a = (b * y * a - y) - (b * t k * a - t k) + (y - t k) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]; abel
    show b * (y - t k) * a ∈ latQ S T ΛS ΛT
    rw [e]
    exact add_mem (sub_mem h1 (ht k)) hk
  · intro k k' hk
    exact ((hu (t k) (ht k)).unique (by rw [sub_self]; exact zero_mem _) hk.1)
  · intro y c hc
    have e : b * (y + c) * a - (y + c) = (b * y * a - y) + (b * c * a - c) := by
      rw [Matrix.mul_add, Matrix.add_mul]; abel
    have hc' : b * c * a - c ∈ latQ S T ΛS ΛT := sub_mem ((hC c).1 hc).2 hc.1
    by_cases hy : b * y * a - y ∈ latQ S T ΛS ΛT
    · rw [hQ _ hy, hQ _ (e ▸ add_mem hy hc'), gamQ_eq, gamQ_eq, map_smul, map_smul, map_sub, map_sub,
        ← rhoF_finX hg hh, ← rhoF_finX hg hh, map_add (finX S T)]
      refine gam_periodic H hA _ (gamF_rhoF _) _ ?_ ((hX c).1 hc.1) ?_
      · rw [rhoF_finX hg hh, ← map_sub]; exact hy
      · rw [rhoF_finX hg hh]; exact hc.2
    · rw [hQ0 _ hy, hQ0]
      intro hn
      rw [e] at hn
      exact hy ((add_mem_cancel_right hc').1 hn)
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_)
      ((summable_sum fun i (_ : i ∈ Finset.univ) => summable_coefQ hψ hθ hpos dS dT w (u i)).mul_left ‖κ‖)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
  · simp
  · intro y hy hn
    have h1 : infRat S T y ≠ 0 := fun h => hy (infRat_injective S T (h.trans (map_zero _).symm))
    have h2 := hpos _ h1
    rw [neg_eq_zero.1 hn] at h2
    exact lt_irrefl _ h2
  · intro y hy c hc
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hy)
    have h1 : finX S T c ∈ (latF S T ΛS ΛT).map (rhoF S T (g, h)) := by
      refine ⟨finX S T (b * c * a), hc.2, ?_⟩
      rw [← rhoF_finX hg hh, ← Module.End.mul_apply, ← map_mul,
        show ((g, h) : GA D S × GA D T) * (g⁻¹, h⁻¹) = 1 from mul_inv_cancel (g, h), map_one, Module.End.one_apply]
    have h2 := H.iso hA (mem_of_coefQ_ne_zero hi) ((hX c).1 hc.1)
    rw [H.add_left, H.iso hB (huB i) h1, mul_one] at h2
    obtain ⟨z, hz⟩ := (GlobalTheory.RatSelfDual.psi_fin_iff hψ S T y c).1 h2
    exact ⟨-z, by rw [LinearMap.neg_apply, hz, Int.cast_neg]⟩
  · intro v
    obtain ⟨hf, hfix, hvac⟩ := GlobalTheory.T.gaussian_poincare_series_theta_vacuum D ψ hψ θ σ hσ S T sS sT hS hT ΛS ΛT dS dT w hw (-v)
    have e := hκ ⟨_, hf⟩ hfix hvac (iotaW σ T S v)
    rw [(sumOp_eq_sum_transversal H _ _ hB _ hfix _ u huB huT).1, Submodule.coe_sum, Finset.sum_apply] at e
    simp only [coe_opF, right_side hψ hσ halt, left_side hg hh hψ hσ halt sS sT _ _ hw hb] at e
    rw [e, ← Summable.tsum_finsetSum, ← tsum_mul_left]
    · refine tsum_congr fun y => ?_
      beta_reduce
      rw [← Finset.sum_mul, mul_assoc κ]
    · intro i _
      refine Summable.of_norm ((summable_coefQ hψ hθ hpos dS dT w (u i)).congr fun y => ?_)
      have e1 : (2 * Real.pi * Complex.I * ((-omO S T (infRat S T y)) v : ℝ) : ℂ) =
          ((2 * Real.pi * (-omO S T (infRat S T y)) v : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [norm_mul, e1, Complex.norm_exp_ofReal_mul_I, mul_one]

end GlobalTheory.RatTrace

end
