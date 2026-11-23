import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer.Check

variable {D : D7}

theorem sympl_left (S T : HSp D) (g : GA D T) (x y : WO S T) :
    symplOH S T (mt T g ⬝ x) (mt T g ⬝ y) = symplOH S T x y := by
  rw [symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, adj_mul, Matrix.mul_assoc, cancel₃ (mt_unitary T g)]

section Target

variable {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (n : GA D T) (β : Mx D ρ T₀.rank)
  (y : Mx D S.rank ρ)

def xiT : Mx D ρ S.rank := d.pX ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)

theorem splitT (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) :
    mt T n⁻¹ ⬝ d.incAdj S y = d.incX S (xiT d n y) + d.inc0 S (ptT d S y n) + d.incAdj S y := by
  have h : d.pY ⬝ (mt T n⁻¹ ⬝ d.incAdj S y) = incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S) := by
    rw [cancel₂ h3, d.incAdj_apply, d.incY_apply, cancel₂ d.pY_jY, Matrix.one_mul]
  have h' : d.incAdj S y = d.jY ⬝ (d.pY ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)) := by rw [h]; rfl
  conv_rhs => rw [d.incX_apply, d.wittDecomp_inclAnisotropicHom_apply, xiT, ptT]; arg 2; rw [h']
  rw [← Matrix.mul_assoc d.jX, ← Matrix.mul_assoc d.j0, ← Matrix.mul_assoc d.jY, ← Matrix.add_mul, ← Matrix.add_mul,
    d.sum_eq_one, Matrix.one_mul]

theorem symplectic_adjoint_inclusion_zero (v : WO S T₀) : symplOH S T (d.incAdj S y) (d.inc0 S v) = 0 := d.wittDecomp_sympl_inclDual_inclAnisotropic S _ v

theorem cenT_eq (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) :
    cenT d S y n = -symplOH S T (d.incX S (xiT d n y)) (d.incAdj S y) := by
  rw [cenT, splitT d n y h3, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, symplectic_adjoint_inclusion_zero,
    GlobalTheory.OrientedHeis.symplOH_self, add_zero, add_zero, symplOH_skew]

theorem moveT (h2 : mt T n⁻¹ ⬝ d.j0 = d.j0 + d.jX ⬝ β) (w₀ : WO S T₀) :
    mt T n⁻¹ ⬝ d.inc0 S w₀ = d.inc0 S w₀ + d.incX S (β ⬝ w₀) := by
  rw [d.wittDecomp_inclAnisotropicHom_apply, d.incX_apply, cancel₂ h2, Matrix.add_mul, Matrix.mul_assoc]

theorem crossT (h2 : mt T n⁻¹ ⬝ d.j0 = d.j0 + d.jX ⬝ β) (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) (w₀ : WO S T₀) :
    symplOH S T₀ w₀ (ptT d S y n) = -symplOH S T (d.incX S (β ⬝ w₀)) (d.incAdj S y) := by
  have h := sympl_left S T n⁻¹ (d.inc0 S w₀) (d.incAdj S y)
  have z : symplOH S T (d.inc0 S w₀) (d.incAdj S y) = 0 := by rw [symplOH_skew, symplectic_adjoint_inclusion_zero, neg_zero]
  have z' : symplOH S T (d.inc0 S w₀) (d.incX S (xiT d n y)) = 0 := by
    rw [symplOH_skew, d.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero]
  rw [splitT d n y h3, moveT d n β h2, z, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, z, z',
    d.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, d.symplOH_incX_incX, d.wittDecomp_sympl_inclIsotropic_inclAnisotropic, zero_add, add_zero, add_zero, zero_add] at h
  exact eq_neg_of_add_eq_zero_left h

theorem mixT_comp {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)} (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h1 : mt T n⁻¹ ⬝ d.jX = d.jX) (h2 : mt T n⁻¹ ⬝ d.j0 = d.j0 + d.jX ⬝ β) (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) :
    d.mixT S ψ μ 𝓕 (fun w => f (mt T n⁻¹ ⬝ w)) y = jacT ψ d S y n (d.mixT S ψ μ 𝓕 f y) := by
  funext w₀
  have e3 : ∀ ξ, mt T n⁻¹ ⬝ d.incX S ξ = d.incX S ξ := fun ξ => by rw [d.incX_apply, cancel₂ h1]
  have k := covolOne_integral_add hμ
    (fun ξ => heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S (w₀ + ptT d S y n)) f)) 0)
    (d.integrandT_periodic hf y (w₀ + ptT d S y n)) (xiT d n y + β ⬝ w₀)
  change d.mixT S ψ μ 𝓕 (fun w => f (mt T n⁻¹ ⬝ w)) y w₀ = ψ (cenT d S y n) * (ψ (symplOH S T₀ w₀ (ptT d S y n)) *
    d.mixT S ψ μ 𝓕 f y (w₀ + ptT d S y n))
  unfold HypDec.mixT
  rw [← k, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [d.integrandT_eq, d.integrandT_eq, Matrix.mul_add, Matrix.mul_add, splitT d n y h3, moveT d n β h2, e3,
    cenT_eq d n y h3, crossT d n β y h2 h3, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  simp only [map_add, GlobalTheory.OrientedHeis.symplOH_add_left]
  congr 2
  · ring
  · abel

end Target

theorem sympl_right (S T : HSp D) (g : GA D S) (x y : WO S T) :
    symplOH S T (x ⬝ mt S g) (y ⬝ mt S g) = symplOH S T x y := by
  have h : mt S g ⬝ (giA S ⬝ adj (mt S g)) = giA S := by
    have h1 := mt_mul_inv S g
    rw [mt_inv] at h1
    have h2 := congrArg (· ⬝ giA S) h1
    simpa only [Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one, Matrix.one_mul] using h2
  rw [symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, adj_mul, ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc _ _ (mt S g),
    ← Matrix.mul_assoc _ _ (mt S g), trace_mul_comm, Matrix.mul_assoc (adj (mt S g)), cancel₃ h]

section Source

variable {ψ : AddChar (AF D.host.F) ℂ} {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (n : GA D S) (β : Mx D S₀.rank ρ)
  (x : Mx D T.rank ρ)

def etaS : Mx D T.rank ρ := d.extX T x ⬝ mt S n ⬝ d.jY

theorem splitS (h1 : mt S n ⬝ d.jX = d.jX) :
    d.extX T x ⬝ mt S n = d.extY T (etaS d n x) + d.extX T x + d.ext0 T (ptS d T x n) := by
  refine d.mat_ext ?_ ?_ ?_
  · simp only [Matrix.add_mul, d.extX_apply, d.extY_apply, d.matrixExtendByZero_apply, Matrix.mul_assoc, h1, d.pX_jX, d.pY_jX, d.p0_jX,
      Matrix.mul_zero, zero_add, add_zero]
  · simp only [Matrix.add_mul, d.extX_apply, d.extY_apply, d.matrixExtendByZero_apply, Matrix.mul_assoc, d.pX_j0, d.pY_j0, d.p0_j0,
      Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one, ptS]
  · simp only [Matrix.add_mul, d.extX_apply, d.extY_apply, d.matrixExtendByZero_apply, Matrix.mul_assoc, d.pX_jY, d.pY_jY, d.p0_jY,
      Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one, etaS]

theorem cenS_eq (h1 : mt S n ⬝ d.jX = d.jX) :
    cenS d T x n = -symplOH S T (d.extY T (etaS d n x)) (d.extX T x) := by
  rw [cenS, splitS d n x h1, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, d.wittDecomp_sympl_extIsotropic_extAnisotropic,
    GlobalTheory.OrientedHeis.symplOH_self, add_zero, add_zero, symplOH_skew]

theorem moveS (h2 : d.p0 ⬝ mt S n = d.p0 + β ⬝ d.pY) (w₀ : WO S₀ T) :
    d.ext0 T w₀ ⬝ mt S n = d.ext0 T w₀ + d.extY T (w₀ ⬝ β) := by
  rw [d.matrixExtendByZero_apply, d.extY_apply, Matrix.mul_assoc, h2, Matrix.mul_add, Matrix.mul_assoc]

theorem crossS (h1 : mt S n ⬝ d.jX = d.jX) (h2 : d.p0 ⬝ mt S n = d.p0 + β ⬝ d.pY) (w₀ : WO S₀ T) :
    symplOH S₀ T w₀ (ptS d T x n) = -symplOH S T (d.extY T (w₀ ⬝ β)) (d.extX T x) := by
  have h := sympl_right S T n (d.ext0 T w₀) (d.extX T x)
  have z : symplOH S T (d.ext0 T w₀) (d.extX T x) = 0 := by rw [symplOH_skew, d.wittDecomp_sympl_extIsotropic_extAnisotropic, neg_zero]
  have z' : symplOH S T (d.ext0 T w₀) (d.extY T (etaS d n x)) = 0 := by
    rw [symplOH_skew, d.wittDecomp_sympl_extDual_extAnisotropic, neg_zero]
  rw [splitS d n x h1, moveS d n β h2, z, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, z, z',
    d.wittDecomp_sympl_extAnisotropic_extAnisotropic, d.symplOH_extY_extY, d.wittDecomp_sympl_extDual_extAnisotropic, zero_add, zero_add, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem mixS_comp {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h1 : mt S n ⬝ d.jX = d.jX) (h2 : d.p0 ⬝ mt S n = d.p0 + β ⬝ d.pY) (h3 : d.pY ⬝ mt S n = d.pY) :
    d.mixS T ψ μ 𝓕 (fun w => f (w ⬝ mt S n)) x = jacS ψ d T x n (d.mixS T ψ μ 𝓕 f x) := by
  funext w₀
  have e3 : ∀ a, d.extY T a ⬝ mt S n = d.extY T a := fun a => by rw [d.extY_apply, Matrix.mul_assoc, h3]
  have k := covolOne_integral_add hμ
    (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T (w₀ + ptS d T x n)) f)) 0)
    (d.integrandS_periodic hf x (w₀ + ptS d T x n)) (etaS d n x + w₀ ⬝ β)
  change d.mixS T ψ μ 𝓕 (fun w => f (w ⬝ mt S n)) x w₀ = ψ (cenS d T x n) * (ψ (symplOH S₀ T w₀ (ptS d T x n)) *
    d.mixS T ψ μ 𝓕 f x (w₀ + ptS d T x n))
  unfold HypDec.mixS
  rw [← k, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  beta_reduce
  rw [d.integrandS_eq, d.integrandS_eq, Matrix.add_mul, Matrix.add_mul, splitS d n x h1, moveS d n β h2, e3,
    cenS_eq d n x h1, crossS d n β x h1 h2, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  simp only [map_add, GlobalTheory.OrientedHeis.symplOH_add_left]
  congr 2
  · ring
  · abel

end Source

theorem om_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om)
    {g : GA D S} (hg : g ∈ GQ S) {h : GA D T} (hh : h ∈ GQ T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hpres : ∀ w, IsThetaFunO ψ S T (heisO ψ S T w f)) (w : WO S T) :
    om (g, h) f (actO S T g h w) = f w := by
  have h1 := congrFun (hom.om_heis g h w f hf) 0
  rw [hom.om_aut g hg h hh _ (hpres w)] at h1
  simpa only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add] using h1.symm

theorem psiE_half (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) : psiE ψ (t • half D) = ψ t := by
  rw [psiE, map_smul, half, GlobalTheory.BesselChar.trace_incA]
  have h2 : Module.finrank D.host.F D.host.E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have : (1 / 2 : D.host.E) = algebraMap D.host.F D.host.E (1 / 2) := by rw [map_div₀, map_one, map_ofNat]
  rw [this, Algebra.trace_algebraMap, h2]
  norm_num

theorem psiBes_three (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) :
    ∃ n ∈ flagN (hypDecThree D), psiBes ψ (hypDecThree D) 1 (fun _ => 1) n = ψ t := by
  refine ⟨(hypDecThree D).nB (Matrix.of fun _ _ => t • half D), (hypDecThree D).nB_mem_NFlag _, ?_⟩
  rw [psiBes_nB, map_one, one_mul, ← psiE_half]
  congr 1
  change ∑ i : Fin 1, ell D 1 i * ∑ j : Fin 1, t • half D * incA D 1 = _
  rw [Fin.sum_univ_one, Fin.sum_univ_one, show ell D 1 0 = 1 from rfl, one_mul, map_one, mul_one]

theorem unip_two {R : Type} [CommRing R] (s : R) : ∃ u : GL (Fin 2) R, u ∈ upperUni 2 R ∧ u.1 0 1 = s := by
  refine ⟨⟨!![1, s; 0, 1], !![1, -s; 0, 1], ?_, ?_⟩, ?_, rfl⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro i j; fin_cases i <;> fin_cases j <;> simp

theorem psiUni_two (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) : ∃ u ∈ UX D 2, psiUni ψ u = ψ t := by
  obtain ⟨u, hu, h⟩ := unip_two (t • half D)
  have e : ∀ T : Mx D 2 2, upSum T = T 0 1 := fun T => by simp [upSum, Fin.sum_univ_two]
  exact ⟨u, mem_UX.2 hu, by rw [psiUni, e, h, psiE_half]⟩

theorem UX_one (u : UX D 1) : u = 1 := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact ((mem_UX.1 u.2) 0 0).2

theorem isUnitU_one : IsUnitU D 1 (Measure.dirac 1) := by
  haveI : Unique (UX D 1) := ⟨⟨1⟩, UX_one⟩
  haveI : BorelSpace (UX D 1) := ⟨rfl⟩
  refine ⟨?_, Set.univ, ?_, measure_univ⟩
  · haveI : (Measure.dirac (1 : UX D 1)).IsMulLeftInvariant := ⟨fun g => by
      rw [UX_one g]; simp only [one_mul]; exact Measure.map_id⟩
    haveI : (Measure.dirac (1 : UX D 1)).IsOpenPosMeasure :=
      ⟨fun U _ hU => by rw [Subsingleton.eq_univ_of_nonempty hU, measure_univ]; exact one_ne_zero⟩
    exact @Measure.IsHaarMeasure.mk _ _ _ _ _ ⟨fun K _ => measure_lt_top _ _⟩ inferInstance inferInstance
  · exact ⟨MeasurableSet.univ.nullMeasurableSet, Filter.Eventually.of_forall fun x => ⟨1, trivial⟩,
      fun a b hab => absurd (Subtype.ext (Subsingleton.elim _ _)) hab⟩

theorem flat_one (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ A L : HSp D} (dV : HypDec V V₀ 1) (o : OrthDec V₀ A L) (ζ)
    (dW : HypDec W W₀ 1) (μS 𝓕S μT 𝓕T) (Ψ : WO V W → ℂ) :
    flat ψ dV o ζ dW μS 𝓕S μT 𝓕T (Measure.dirac 1) Ψ = evalZero ψ dV o ζ dW μS 𝓕S μT 𝓕T Ψ := by
  haveI : Unique (UX D 1) := ⟨⟨1⟩, UX_one⟩
  haveI : MeasurableSingletonClass (UX D 1) := ⟨fun x => by
    rw [Subsingleton.eq_univ_of_nonempty (Set.singleton_nonempty x)]; exact MeasurableSet.univ⟩
  funext w
  rw [flat, flatAt, integral_dirac, flatFun, psiUni, evalZero]
  simp [upSum_one, psiE_zero]

theorem fjKer_one (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ)
    (om : Om V₀ W₀) (Ξ) (h₀ : GA D A) (h : GA D W₀) :
    fjKer ψ dW o ζ om Ξ h₀ 1 h = thetaKO om (o.emb (h₀, 1)) h Ξ := by
  rw [fjKer, opA, jacT_one, id, thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem mixT_nB_nC {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)
    {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)} (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (b : Mx D ρ T₀.rank) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (fun w => f (mt T (d.nB b * d.nC c)⁻¹ ⬝ w)) y =
      jacT ψ d S y (d.nB b * d.nC c) (d.mixT S ψ μ 𝓕 f y) := by
  refine mixT_comp d _ (-b) y hμ hf ?_ ?_ ?_ <;> rw [_root_.mul_inv_rev, d.nB_inv, d.nC_inv, mt_mul]
  · rw [Matrix.mul_assoc, d.nB_jX, d.nC_jX]
  · rw [Matrix.mul_assoc, d.nB_j0, Matrix.mul_add, d.nC_j0, cancel₂ (d.nC_jX _)]
  · rw [← Matrix.mul_assoc, d.pY_nC, d.pY_nB]

end GlobalTheory.MixPer.Check

end
