import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.Splitting
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.ExistsAtPlace
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FirstFrameHalfEqMul

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

def Tl (d : SD σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Ψ := funext fun X => by
    simp only [SD.T, Pi.add_apply, ← map_add]
    congr 1
    funext z
    exact mul_add _ _ _
  map_smul' c Φ := funext fun X => by
    simp only [SD.T, Pi.smul_apply, RingHom.id_apply, ← map_smul]
    congr 1
    funext z
    exact mul_left_comm _ _ _

def TK (d : SD σ) : Submodule ℂ (Mx F E d.m d.n → ℂ) := (kfS d).map (Tl d)

theorem mem_TK {f : Mx F E d.m d.n → ℂ} : f ∈ TK d ↔ ∃ Φ ∈ kfS d, d.T Φ = f := Iff.rfl

theorem D_dg_mem {Φ : d.Fn} (hΦ : Φ ∈ kfS d) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) :
    Box.D (d.dd.e (Z * (dg d)ᵀ)) Φ ∈ kfS d :=
  D_kfS (fun c hc => by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]) hΦ

theorem mul_var (R : RD d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ TK d) : (fun X => evX (MvPolynomial.X k) (R.loc w X) * f X) ∈ TK d := by
  obtain ⟨Φ, hΦ, rfl⟩ := hf
  obtain ⟨Z₁, Z₂, c₁, c₂, h1, h2, e⟩ := var_span' R w k
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (dg d)ᵀ)) Φ +
    (c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (dg d)ᵀ)) Φ,
    add_mem (Submodule.smul_mem _ _ (D_dg_mem hΦ h1)) (Submodule.smul_mem _ _ (D_dg_mem hΦ h2)), funext fun X => ?_⟩
  have t := congrFun ((Tl d).map_add ((c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (dg d)ᵀ)) Φ)
    ((c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (dg d)ᵀ)) Φ)) X
  simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = _ at t
  change d.T _ X = _ * d.T Φ X
  rw [t]
  change _ * d.T _ X + _ * d.T _ X = _
  rw [T_D_dg (mem_sch hΦ) h1, T_D_dg (mem_sch hΦ) h2, e X]
  field_simp

theorem mul_pol (R : RD d) (w : InfinitePlace F) (Q : PX d.m d.n) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ TK d) :
    (fun X => evX Q (R.loc w X) * f X) ∈ TK d := by
  induction Q using MvPolynomial.induction_on generalizing f with
  | C a =>
    have : (fun X => evX (MvPolynomial.C a) (R.loc w X) * f X) = a • f := funext fun X => by
      simp [evX]
    rw [this]; exact Submodule.smul_mem _ _ hf
  | add p q hp hq =>
    have : (fun X => evX (p + q) (R.loc w X) * f X) = (fun X => evX p (R.loc w X) * f X) + fun X => evX q (R.loc w X) * f X :=
      funext fun X => by simp [evX, add_mul]
    rw [this]; exact add_mem (hp hf) (hq hf)
  | mul_X p k hp =>
    have : (fun X => evX (p * MvPolynomial.X k) (R.loc w X) * f X) =
        fun X => evX (MvPolynomial.X k) (R.loc w X) * (evX p (R.loc w X) * f X) := funext fun X => by
      simp only [evX, map_mul]; ring
    rw [this]; exact mul_var R w k (hp hf)

theorem mul_prod (R : RD d) (P : InfinitePlace F → PX d.m d.n) (s : Finset (InfinitePlace F)) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ TK d) : (fun X => (∏ w ∈ s, evX (P w) (R.loc w X)) * f X) ∈ TK d := by
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert w s hw ih =>
    have : (fun X => (∏ w ∈ insert w s, evX (P w) (R.loc w X)) * f X) =
        fun X => evX (P w) (R.loc w X) * ((∏ w ∈ s, evX (P w) (R.loc w X)) * f X) := funext fun X => by
      rw [Finset.prod_insert hw, mul_assoc]
    rw [this]; exact mul_pol R w (P w) ih

theorem vac_mem (hT : TAll) (hF : FockMem) (R : RD d) {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ}
    (hg : g ∈ SB _) : vacF R g ∈ TK d := by
  have hgen : vacF R g ∈ R.fock := Submodule.subset_span ⟨fun _ => 1, g, hg, funext fun X => by
    simp [vacF, fP, evX]⟩
  obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 hgen)
  refine ⟨Φ, vac_kfS (thA R) (thB d R.ε) (fun k hk w => commute_thB R hk w) (fun _ => 1) hΦ fun u u' hu hu' hr => ?_, e⟩
  have m1 : Box.D (d.dd.e u') Φ ∈ d.sch := Box.DP_mem hΦ _ _
  have m2 : Box.D (d.dd.e u) Φ ∈ d.sch := Box.DP_mem hΦ _ _
  refine sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem m1 (Submodule.smul_mem _ _ m2)) (funext fun X => ?_))
  have t := congrFun ((Tl d).map_sub (Box.D (d.dd.e u') Φ) (Complex.I • Box.D (d.dd.e u) Φ)) X
  simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = d.T _ X - Complex.I * d.T _ X at t
  rw [t, vac_rel R g hΦ e hu hu' hr X, sub_self]
  rfl

theorem fock_le (hT : TAll) (hF : FockMem) (R : RD d) : R.fock ≤ TK d := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have e : (fun X => (∏ w ∈ Finset.univ, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w ∈ Finset.univ, evX (P w) (R.loc w X)) * vacF R g X := funext fun X => by
    simp only [fP, vacF, Finset.prod_mul_distrib]; ring
  rw [SetLike.mem_coe, e]
  exact mul_prod R P _ (vac_mem hT hF R hg)

theorem polyKFin_of : TAll → FockMem → PolyKFin := by
  intro hT hF F E _ _ _ _ _ σ d R Φ hΦ hf
  obtain ⟨Φ', h', e⟩ := fock_le hT hF R hf
  have : Φ = Φ' := (sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem hΦ (mem_sch h')) (by
    rw [show d.T (Φ - Φ') = Tl d (Φ - Φ') from rfl, map_sub]
    exact sub_eq_zero.2 e.symm))).symm ▸ rfl
  rw [this]
  exact kFin_of_mem h'

end PositivityTheory.SiegelWeilFormula.KK

end
