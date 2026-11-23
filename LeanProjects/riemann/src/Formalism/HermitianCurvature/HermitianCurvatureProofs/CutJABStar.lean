import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv

namespace Formalism.FourierDecayAlt.P.CutMP.JA.BStar

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx2.Adj Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable (P : M.Par)

def evD (q : Qp P.r P.TT) : (DQ P).R →+* ℂ := evq q

def cjD (β : (DQ P).R) : (DQ P).R := cj β

theorem evD_cjD (β : (DQ P).R) (q : Qp P.r P.TT) : evD P q (cjD P β) = conj (evD P q β) := cj_apply β q

theorem extD {f g : (DQ P).R} (h : ∀ q, evD P q f = evD P q g) : f = g := S_ext h

theorem cjD_mul (f g : (DQ P).R) : cjD P (f * g) = cjD P f * cjD P g := cj_mul f g

theorem cjD_add (f g : (DQ P).R) : cjD P (f + g) = cjD P f + cjD P g := cj_add f g

theorem cjD_zero : cjD P 0 = 0 := extD P fun q => by rw [evD_cjD, map_zero, map_zero]

theorem cjD_one : cjD P 1 = 1 := extD P fun q => by rw [evD_cjD, map_one, map_one]

theorem cjD_cjD (f : (DQ P).R) : cjD P (cjD P f) = f := extD P fun q => by rw [evD_cjD, evD_cjD, Complex.conj_conj]

theorem evD_alg (c : ℂ) (q : Qp P.r P.TT) : evD P q (algebraMap ℂ (DQ P).R c) = c := rfl

theorem cjD_alg (c : ℂ) : cjD P (algebraMap ℂ (DQ P).R c) = algebraMap ℂ (DQ P).R (conj c) :=
  extD P fun q => by rw [evD_cjD, evD_alg, evD_alg]

theorem cjD_sum {ι : Type} (s : Finset ι) (f : ι → (DQ P).R) : cjD P (∑ i ∈ s, f i) = ∑ i ∈ s, cjD P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cjD_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cjD_add, ih]

theorem multiplierPair_fst (f fb g : (DQ P).R) : ((DQ P).fnP f fb).1 g = f * g := rfl

theorem multiplierPair_mul (f fb g gb : (DQ P).R) :
    (DQ P).fnP f fb * (DQ P).fnP g gb = (DQ P).fnP (f * g) (fb * gb) := by
  refine Prod.ext ?_ ?_
  · apply LinearMap.ext; intro x
    show f * (g * x) = f * g * x
    rw [mul_assoc]
  · apply MulOpposite.unop_injective; apply LinearMap.ext; intro x
    show gb * (fb * x) = fb * gb * x
    ring

theorem multiplierPair_add (f fb g gb : (DQ P).R) :
    (DQ P).fnP f fb + (DQ P).fnP g gb = (DQ P).fnP (f + g) (fb + gb) := by
  refine Prod.ext ?_ ?_
  · apply LinearMap.ext; intro x
    show f * x + g * x = (f + g) * x
    ring
  · apply MulOpposite.unop_injective; apply LinearMap.ext; intro x
    show fb * x + gb * x = (fb + gb) * x
    ring

theorem multiplierPair_zero : (DQ P).fnP 0 0 = 0 := by
  refine Prod.ext ?_ ?_
  · apply LinearMap.ext; intro x
    show (0 : (DQ P).R) * x = 0
    rw [zero_mul]
  · apply MulOpposite.unop_injective; apply LinearMap.ext; intro x
    show (0 : (DQ P).R) * x = 0
    rw [zero_mul]

theorem multiplierPair_one : (DQ P).fnP 1 1 = 1 := by
  refine Prod.ext ?_ ?_
  · apply LinearMap.ext; intro x
    show (1 : (DQ P).R) * x = x
    rw [one_mul]
  · apply MulOpposite.unop_injective; apply LinearMap.ext; intro x
    show (1 : (DQ P).R) * x = x
    rw [one_mul]

theorem algebraMap_eq_multiplierPair (c : ℂ) :
    algebraMap ℂ (DQ P).Pr c = (DQ P).fnP (algebraMap ℂ (DQ P).R c) (algebraMap ℂ (DQ P).R (conj c)) := by
  refine Prod.ext ?_ ?_
  · apply LinearMap.ext; intro x
    show c • x = algebraMap ℂ (DQ P).R c * x
    rw [Algebra.smul_def]
  · apply MulOpposite.unop_injective; apply LinearMap.ext; intro x
    show (starRingEnd ℂ c) • x = algebraMap ℂ (DQ P).R (conj c) * x
    rw [Algebra.smul_def]

theorem star_fnP (f fb : (DQ P).R) : star ((DQ P).fnP f fb) = (DQ P).fnP fb f := rfl

theorem multiplierPair_sum {ι : Type} (s : Finset ι) (f fb : ι → (DQ P).R) :
    ∑ i ∈ s, (DQ P).fnP (f i) (fb i) = (DQ P).fnP (∑ i ∈ s, f i) (∑ i ∈ s, fb i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty, multiplierPair_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, multiplierPair_add]

def FE (w : (DQ P).Pr) : Prop :=
  ∃ (β : (DQ P).R) (C : ℝ), w = (DQ P).fnP β (cjD P β) ∧ ∀ q, ‖evD P q β‖ ≤ C

def FM (a : A P (DQ P)) : Prop := ∀ π π', FE P (a π π')

theorem fe_zero : FE P 0 := ⟨0, 0, by rw [cjD_zero, multiplierPair_zero], fun q => by rw [map_zero, norm_zero]⟩

theorem fe_one : FE P 1 := ⟨1, 1, by rw [cjD_one, multiplierPair_one], fun q => by rw [map_one, norm_one]⟩

theorem fe_alg (c : ℂ) : FE P (algebraMap ℂ (DQ P).Pr c) :=
  ⟨algebraMap ℂ (DQ P).R c, ‖c‖, by rw [cjD_alg, algebraMap_eq_multiplierPair], fun q => by rw [evD_alg]⟩

theorem fm_diag (d : M.Ty P → (DQ P).Pr) (hd : ∀ π, FE P (d π)) : FM P (Matrix.diagonal d) := by
  intro π π'
  by_cases h : π = π'
  · subst h; rw [Matrix.diagonal_apply_eq]; exact hd π
  · rw [Matrix.diagonal_apply_ne _ h]; exact fe_zero P

theorem fm_one : FM P 1 := by
  rw [← Matrix.diagonal_one]
  exact fm_diag P _ fun _ => fe_one P

theorem fm_scalar (w : (DQ P).Pr) (hw : FE P w) : FM P (Matrix.scalar (M.Ty P) w) := by
  rw [Matrix.scalar_apply]; exact fm_diag P _ fun _ => hw

theorem fm_mul {a b : A P (DQ P)} (ha : FM P a) (hb : FM P b) : FM P (a * b) := by
  intro π π''
  choose βa Ca hpa hCa using ha
  choose βb Cb hpb hCb using hb
  refine ⟨∑ π', βa π π' * βb π' π'', ∑ π', max (Ca π π') 0 * max (Cb π' π'') 0, ?_, fun q => ?_⟩
  · rw [Matrix.mul_apply, cjD_sum, ← multiplierPair_sum]
    refine Finset.sum_congr rfl fun π' _ => ?_
    rw [hpa, hpb, multiplierPair_mul, cjD_mul]
  · rw [map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π' _ => ?_)
    rw [map_mul, norm_mul]
    exact mul_le_mul ((hCa π π' q).trans (le_max_left _ _)) ((hCb π' π'' q).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)

theorem fm_star {a : A P (DQ P)} (ha : FM P a) : FM P (star a) := by
  intro π π'
  obtain ⟨β, C, hp, hC⟩ := ha π' π
  refine ⟨cjD P β, C, ?_, fun q => ?_⟩
  · rw [Matrix.star_apply, hp, star_fnP, cjD_cjD]
  · rw [evD_cjD, Complex.norm_conj]; exact hC q

theorem smq_cont (f : SmQ P.r P.TT) : Continuous (f : Qp P.r P.TT → ℂ) := by
  have h := (f.2 : ContDiffOn ℝ sm (ext (f : Qp P.r P.TT → ℂ)) (Qset P.r P.TT)).continuousOn
  have e : (f : Qp P.r P.TT → ℂ) = ext (f : Qp P.r P.TT → ℂ) ∘ Subtype.val :=
    funext fun q => (ext_of_mem _ q.2).symm
  rw [e, continuous_iff_continuousAt]
  intro q
  exact (h.continuousAt ((Qset_open _ _).mem_nhds q.2)).comp continuous_subtype_val.continuousAt

theorem evD_cont (γ : (DQ P).R) : Continuous fun q => evD P q γ := smq_cont P γ

theorem evQ_cont (f : SmQ P.r P.TT) : Continuous fun q => evQ P f q := smq_cont P f

theorem actA_fm_apply {b : A P (DQ P)} {β : M.Ty P → M.Ty P → (DQ P).R}
    (hβ : ∀ π π', b π π' = (DQ P).fnP (β π π') (cjD P (β π π'))) (V : M.Ty P → SmQ P.r P.TT) (π : M.Ty P)
    (q : Qp P.r P.TT) : evQ P (actA P b V π) q = ∑ π', evD P q (β π π') * evQ P (V π') q := by
  show evD P q (∑ π', (b π π').1 (V π')) = ∑ π', evD P q (β π π') * evD P q (V π')
  rw [map_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [hβ π π']
  rfl

theorem ipA_fm {b : A P (DQ P)} (hb : FM P b) {ε : ℝ} (U V : M.Ty P → SmQ P.r P.TT)
    (hU0 : ∀ π q, Gq P q < ε → evQ P (U π) q = 0)
    (hU : ∀ π, IntegrableOn (fun q => ‖evQ P (U π) q‖ ^ 2) {q | ε ≤ Gq P q} (mu0 P.r P.TT))
    (hV : ∀ π, IntegrableOn (fun q => ‖evQ P (V π) q‖ ^ 2) {q | ε ≤ Gq P q} (mu0 P.r P.TT)) :
    ipA P U (actA P b V) = ipA P (actA P (star b) U) V := by
  choose β C hβ hC using hb
  have hS : ∀ π π', star b π π' = (DQ P).fnP (cjD P (β π' π)) (cjD P (cjD P (β π' π))) := fun π π' => by
    rw [Matrix.star_apply, hβ, star_fnP, cjD_cjD]
  have hCc : ∀ π π' q, ‖evD P q (cjD P (β π π'))‖ ≤ C π π' := fun π π' q => by
    rw [evD_cjD, Complex.norm_conj]; exact hC π π' q
  have hint : ∀ (π π' : M.Ty P) (γ : (DQ P).R) (Cγ : ℝ), (∀ q, ‖evD P q γ‖ ≤ Cγ) →
      Integrable (fun q => evQ P (U π) q * (evD P q γ * conj (evQ P (V π') q))) (mu0 P.r P.TT) := by
    intro π π' γ Cγ hγ
    have hsupp : Function.support (fun q => evQ P (U π) q * (evD P q γ * conj (evQ P (V π') q))) ⊆
        {q | ε ≤ Gq P q} := by
      intro q hq
      by_contra h
      simp only [Set.mem_ofPred_eq, not_le] at h
      exact hq (by simp only [hU0 π q h, zero_mul])
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
    refine Integrable.mono' (((hU π).add (hV π')).const_mul (max Cγ 0)) ?_ ?_
    · exact ((evQ_cont P (U π)).mul ((evD_cont P γ).mul
        (Complex.continuous_conj.comp (evQ_cont P (V π'))))).aestronglyMeasurable
    · filter_upwards with q
      simp only [Pi.add_apply]
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have h1 : ‖evD P q γ‖ ≤ max Cγ 0 := (hγ q).trans (le_max_left _ _)
      have h2 : 0 ≤ max Cγ 0 := le_max_right _ _
      have ha := norm_nonneg (evQ P (U π) q)
      have hc := norm_nonneg (evQ P (V π') q)
      have hg := norm_nonneg (evD P q γ)
      have h3 : ‖evQ P (U π) q‖ * ‖evQ P (V π') q‖ ≤ ‖evQ P (U π) q‖ ^ 2 + ‖evQ P (V π') q‖ ^ 2 := by
        nlinarith [sq_nonneg (‖evQ P (U π) q‖ - ‖evQ P (V π') q‖)]
      calc ‖evQ P (U π) q‖ * (‖evD P q γ‖ * ‖evQ P (V π') q‖)
          = ‖evD P q γ‖ * (‖evQ P (U π) q‖ * ‖evQ P (V π') q‖) := by ring
        _ ≤ max Cγ 0 * (‖evQ P (U π) q‖ ^ 2 + ‖evQ P (V π') q‖ ^ 2) :=
          mul_le_mul h1 h3 (mul_nonneg ha hc) h2
  have eL : ∀ π, ∫ q, evQ P (U π) q * conj (evQ P (actA P b V π) q) ∂mu0 P.r P.TT =
      ∑ π', ∫ q, evQ P (U π) q * (evD P q (cjD P (β π π')) * conj (evQ P (V π') q)) ∂mu0 P.r P.TT := by
    intro π
    rw [← integral_finsetSum _ (fun π' _ => hint π π' _ _ (hCc π π'))]
    congr 1; funext q
    rw [actA_fm_apply P hβ V π q, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π' _ => ?_
    rw [map_mul, evD_cjD]
  have eR : ∀ π, ∫ q, evQ P (actA P (star b) U π) q * conj (evQ P (V π) q) ∂mu0 P.r P.TT =
      ∑ π', ∫ q, evQ P (U π') q * (evD P q (cjD P (β π' π)) * conj (evQ P (V π) q)) ∂mu0 P.r P.TT := by
    intro π
    rw [← integral_finsetSum _ (fun π' _ => hint π' π _ _ (hCc π' π))]
    congr 1; funext q
    rw [actA_fm_apply P hS U π q, Finset.sum_mul]
    refine Finset.sum_congr rfl fun π' _ => ?_
    ring
  show ∑ π, ∫ q, evQ P (U π) q * conj (evQ P (actA P b V π) q) ∂mu0 P.r P.TT =
    ∑ π, ∫ q, evQ P (actA P (star b) U π) q * conj (evQ P (V π) q) ∂mu0 P.r P.TT
  rw [Finset.sum_congr rfl fun π _ => eL π, Finset.sum_congr rfl fun π _ => eR π, Finset.sum_comm]

theorem star_scalar_fnP (a b : (DQ P).R) :
    star (Matrix.scalar (M.Ty P) ((DQ P).fnP a b)) = Matrix.scalar (M.Ty P) ((DQ P).fnP b a) := by
  ext i j
  rw [Matrix.star_apply, Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases h : i = j
  · subst h; rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, star_fnP]
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, star_zero]

theorem prodFn : ∀ (n : ℕ) (f g : Fin n → (DQ P).R),
    (List.ofFn fun l => Matrix.scalar (M.Ty P) ((DQ P).fnP (f l) (g l))).prod =
      Matrix.scalar (M.Ty P) ((DQ P).fnP (∏ l, f l) (∏ l, g l))
  | 0, f, g => by rw [List.ofFn_zero, List.prod_nil, Fin.prod_univ_zero, Fin.prod_univ_zero, multiplierPair_one, map_one]
  | n + 1, f, g => by
    rw [List.ofFn_succ, List.prod_cons, prodFn n (fun i => f i.succ) (fun i => g i.succ), Fin.prod_univ_succ,
      Fin.prod_univ_succ, ← map_mul, multiplierPair_mul]

theorem scalar_mul_fnP (a b c d : (DQ P).R) :
    Matrix.scalar (M.Ty P) ((DQ P).fnP a b) * Matrix.scalar (M.Ty P) ((DQ P).fnP c d) =
      Matrix.scalar (M.Ty P) ((DQ P).fnP (a * c) (b * d)) := by
  rw [← map_mul, multiplierPair_mul]

theorem evaluation_of_coordinate_variable (v : M.Var P.r) (q : Qp P.r P.TT) : evD P q ((DQ P).x v) = coordE v q.1 := rfl

theorem evD_inv (hTT : 0 ≤ P.TT) (v : M.Var P.r) (q : Qp P.r P.TT) :
    evD P q ((DQ P).inv ((DQ P).x v)) = (coordE v q.1)⁻¹ :=
  inv_val _ (fun q => coordE_ne q.2 hTT v) q

section gens

variable {P} {L : LevelData (A P (DQ P)) P.r}

theorem rep_Dr (hc : L.c = cA P (DQ P)) : L.Dr = Matrix.scalar (M.Ty P) ((DQ P).fnP (∏ l, (DQ P).x (M.vc l)) (∏ l, (DQ P).x (M.vcb l))) := by
  rw [LevelData.Dr, hc]; exact prodFn P P.r _ _

theorem rep_Drb (hc : L.cb = cbA P (DQ P)) : L.Drb = Matrix.scalar (M.Ty P) ((DQ P).fnP (∏ l, (DQ P).x (M.vcb l)) (∏ l, (DQ P).x (M.vc l))) := by
  rw [LevelData.Drb, hc]; exact prodFn P P.r _ _

theorem rep_Dri (hc : L.ci = ciA P (DQ P)) :
    L.Dri = Matrix.scalar (M.Ty P) ((DQ P).fnP (∏ l, (DQ P).inv ((DQ P).x (M.vc l))) (∏ l, (DQ P).inv ((DQ P).x (M.vcb l)))) := by
  rw [LevelData.Dri, hc]; exact prodFn P P.r _ _

theorem rep_Drbi (hc : L.cbi = cbiA P (DQ P)) :
    L.Drbi = Matrix.scalar (M.Ty P) ((DQ P).fnP (∏ l, (DQ P).inv ((DQ P).x (M.vcb l))) (∏ l, (DQ P).inv ((DQ P).x (M.vc l)))) := by
  rw [LevelData.Drbi, hc]; exact prodFn P P.r _ _

theorem zeta_eq_scalar_matrix (hz : L.ζ = zA P (DQ P)) :
    L.ζ = Matrix.scalar (M.Ty P) ((DQ P).fnP ((DQ P).x M.vz) ((DQ P).x M.vzb)) := by rw [hz]; rfl

theorem rep_zb (hz : L.ζb = zbA P (DQ P)) :
    L.ζb = Matrix.scalar (M.Ty P) ((DQ P).fnP ((DQ P).x M.vzb) ((DQ P).x M.vz)) := by rw [hz]; rfl

theorem rep_zi (hz : L.ζi = ziA P (DQ P)) :
    L.ζi = Matrix.scalar (M.Ty P) ((DQ P).fnP ((DQ P).inv ((DQ P).x M.vz)) ((DQ P).inv ((DQ P).x M.vzb))) := by
  rw [hz]; rfl

theorem rep_zbi (hz : L.ζbi = zbiA P (DQ P)) :
    L.ζbi = Matrix.scalar (M.Ty P) ((DQ P).fnP ((DQ P).inv ((DQ P).x M.vzb)) ((DQ P).inv ((DQ P).x M.vz))) := by
  rw [hz]; rfl

end gens

def βD : (DQ P).R :=
  (∏ l, (DQ P).x (M.vc l)) * (DQ P).x M.vz * ((DQ P).inv ((DQ P).x M.vzb) * ∏ l, (DQ P).inv ((DQ P).x (M.vcb l)))

def βDb : (DQ P).R :=
  (∏ l, (DQ P).x (M.vcb l)) * (DQ P).x M.vzb * ((DQ P).inv ((DQ P).x M.vz) * ∏ l, (DQ P).inv ((DQ P).x (M.vc l)))

def βR : (DQ P).R := (∏ l, (DQ P).x (M.vcb l)) * ∏ l, (DQ P).inv ((DQ P).x (M.vc l))

def βRb : (DQ P).R := (∏ l, (DQ P).x (M.vc l)) * ∏ l, (DQ P).inv ((DQ P).x (M.vcb l))

section vals

variable {P}

theorem z_ne (hTT : 0 ≤ P.TT) (q : Qp P.r P.TT) : q.1.2 ≠ 0 := by
  have := coordE_ne q.2 hTT (M.vz : M.Var P.r); rwa [coordE_vz] at this

theorem cjD_βD (hTT : 0 ≤ P.TT) : cjD P (βD P) = βDb P := extD P fun q => by
  simp only [βD, βDb, evD_cjD, map_mul, map_prod, evaluation_of_coordinate_variable, evD_inv P hTT, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb,
    map_inv₀, Complex.conj_conj]

theorem cjD_βR (hTT : 0 ≤ P.TT) : cjD P (βR P) = βRb P := extD P fun q => by
  simp only [βR, βRb, evD_cjD, map_mul, map_prod, evaluation_of_coordinate_variable, evD_inv P hTT, coordE_vc, coordE_vcb, map_inv₀,
    Complex.conj_conj]

theorem cjD_βDb (hTT : 0 ≤ P.TT) : cjD P (βDb P) = βD P := by rw [← cjD_βD hTT, cjD_cjD]

theorem cjD_βRb (hTT : 0 ≤ P.TT) : cjD P (βRb P) = βR P := by rw [← cjD_βR hTT, cjD_cjD]

theorem prod_norm_ne (q : Qp P.r P.TT) : ∏ l, ‖q.1.1 l‖ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun l _ => norm_ne_zero_iff.2 (q.2.1 l)

theorem norm_βD (hTT : 0 ≤ P.TT) (q : Qp P.r P.TT) : ‖evD P q (βD P)‖ ≤ 1 := by
  have h1 := prod_norm_ne q
  have h2 : ‖q.1.2‖ ≠ 0 := norm_ne_zero_iff.2 (z_ne hTT q)
  simp only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, evD_inv P hTT, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb, norm_mul,
    norm_prod, norm_inv, Complex.norm_conj]
  rw [Finset.prod_inv_distrib]
  field_simp
  rfl

theorem norm_βR (hTT : 0 ≤ P.TT) (q : Qp P.r P.TT) : ‖evD P q (βR P)‖ ≤ 1 := by
  have h1 := prod_norm_ne q
  simp only [βR, map_mul, map_prod, evaluation_of_coordinate_variable, evD_inv P hTT, coordE_vc, coordE_vcb, norm_mul, norm_prod, norm_inv,
    Complex.norm_conj]
  rw [Finset.prod_inv_distrib]
  field_simp
  rfl

theorem cjD_izi (hTT : 0 ≤ P.TT) : cjD P ((DQ P).inv ((DQ P).x M.vz)) = (DQ P).inv ((DQ P).x M.vzb) :=
  extD P fun q => by simp only [evD_cjD, evD_inv P hTT, coordE_vz, coordE_vzb, map_inv₀]

theorem cjD_izbi (hTT : 0 ≤ P.TT) : cjD P ((DQ P).inv ((DQ P).x M.vzb)) = (DQ P).inv ((DQ P).x M.vz) := by
  rw [← cjD_izi hTT, cjD_cjD]

theorem norm_izi (hTT : 0 < P.TT) (q : Qp P.r P.TT) :
    ‖evD P q ((DQ P).inv ((DQ P).x M.vz))‖ ≤ (Real.sqrt P.TT)⁻¹ := by
  rw [evD_inv P hTT.le, coordE_vz, norm_inv]
  refine inv_anti₀ (Real.sqrt_pos.2 hTT) ((Real.sqrt_le_iff).2 ⟨norm_nonneg _, ?_⟩)
  rw [Complex.sq_norm]; exact q.2.2.le

theorem norm_izbi (hTT : 0 < P.TT) (q : Qp P.r P.TT) :
    ‖evD P q ((DQ P).inv ((DQ P).x M.vzb))‖ ≤ (Real.sqrt P.TT)⁻¹ := by
  rw [← cjD_izi hTT.le, evD_cjD, Complex.norm_conj]; exact norm_izi hTT q

end vals

section mem

variable {P} {L : LevelData (A P (DQ P)) P.r}

theorem kap_eq (g : M.Ty P → ℂ) : kap P (DQ P) g = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (g π) := rfl

theorem fm_SS (i : ℕ) : FM P (SS P (DQ P) i) := by
  intro π π'
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact fe_alg P _
  · exact fe_zero P

theorem fm_gen (hTT : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) {x : A P (DQ P)} (hx : x ∈ bddSet P L) :
    FM P x ∧ star x ∈ bddSet P L := by
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, -, -, -, -, -⟩ := hL
  have hT := hTT.le
  rcases hx with (((rfl | rfl | rfl | rfl) | ⟨g, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [rep_zi hzi]
      exact fm_scalar P _ ⟨_, _, by rw [cjD_izi hT], norm_izi hTT⟩
    · have : star L.ζi = L.ζbi := by rw [rep_zi hzi, rep_zbi hzbi, star_scalar_fnP]
      rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl))))
  · refine ⟨?_, ?_⟩
    · rw [rep_zbi hzbi]
      exact fm_scalar P _ ⟨_, _, by rw [cjD_izbi hT], norm_izbi hTT⟩
    · have : star L.ζbi = L.ζi := by rw [rep_zi hzi, rep_zbi hzbi, star_scalar_fnP]
      rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
  · have e1 : L.D * L.Dbi = Matrix.scalar (M.Ty P) ((DQ P).fnP (βD P) (βDb P)) := by
      rw [LevelData.D, LevelData.Dbi, rep_Dr hc, zeta_eq_scalar_matrix hz, rep_zbi hzbi, rep_Drbi hcbi, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    have e2 : L.Db * L.Di = Matrix.scalar (M.Ty P) ((DQ P).fnP (βDb P) (βD P)) := by
      rw [LevelData.Db, LevelData.Di, rep_Drb hcb, rep_zb hzb, rep_zi hzi, rep_Dri hci, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    refine ⟨?_, ?_⟩
    · rw [e1]; exact fm_scalar P _ ⟨_, _, by rw [cjD_βD hT], norm_βD hT⟩
    · have : star (L.D * L.Dbi) = L.Db * L.Di := by rw [e1, e2, star_scalar_fnP]
      rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr rfl)))))
  · have e1 : L.D * L.Dbi = Matrix.scalar (M.Ty P) ((DQ P).fnP (βD P) (βDb P)) := by
      rw [LevelData.D, LevelData.Dbi, rep_Dr hc, zeta_eq_scalar_matrix hz, rep_zbi hzbi, rep_Drbi hcbi, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    have e2 : L.Db * L.Di = Matrix.scalar (M.Ty P) ((DQ P).fnP (βDb P) (βD P)) := by
      rw [LevelData.Db, LevelData.Di, rep_Drb hcb, rep_zb hzb, rep_zi hzi, rep_Dri hci, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    refine ⟨?_, ?_⟩
    · rw [e2]
      refine fm_scalar P _ ⟨_, 1, by rw [cjD_βDb hT], fun q => ?_⟩
      rw [← cjD_βD hT, evD_cjD, Complex.norm_conj]; exact norm_βD hT q
    · have : star (L.Db * L.Di) = L.D * L.Dbi := by rw [e1, e2, star_scalar_fnP]
      rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
  · refine ⟨?_, ?_⟩
    · rw [kap_eq]; exact fm_diag P _ fun π => fe_alg P _
    · have : star (kap P (DQ P) g) = kap P (DQ P) fun π => starRingEnd ℂ (g π) := by
        rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
        congr 1; funext π
        exact (algebraMap_star_comm (g π)).symm
      rw [this]; exact Or.inl (Or.inl (Or.inr ⟨_, rfl⟩))
  · have e3 : L.Drb * L.Dri = Matrix.scalar (M.Ty P) ((DQ P).fnP (βR P) (βRb P)) := by
      rw [rep_Drb hcb, rep_Dri hci, scalar_mul_fnP]; rfl
    refine ⟨?_, ?_⟩
    · rw [e3]
      exact fm_mul P (fm_scalar P _ ⟨_, _, by rw [cjD_βR hT], norm_βR hT⟩) (fm_SS i)
    · exact Or.inr ⟨i, hi, rfl⟩
  · have e3 : L.Drb * L.Dri = Matrix.scalar (M.Ty P) ((DQ P).fnP (βR P) (βRb P)) := by
      rw [rep_Drb hcb, rep_Dri hci, scalar_mul_fnP]; rfl
    refine ⟨?_, ?_⟩
    · rw [e3]
      exact fm_star P (fm_mul P (fm_scalar P _ ⟨_, _, by rw [cjD_βR hT], norm_βR hT⟩) (fm_SS i))
    · rw [star_star]; exact Or.inl (Or.inr ⟨i, hi, rfl⟩)

end mem

end

end Formalism.FourierDecayAlt.P.CutMP.JA.BStar

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA BStar

theorem transfer_star_bound_holds : JABddStar := by
  intro P L hTT hL b hb
  have key : FM P b ∧ star b ∈ Submonoid.closure (MA.bddSet P L) := by
    induction hb using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨hf, hs⟩ := fm_gen hTT hL hx
      exact ⟨hf, Submonoid.subset_closure hs⟩
    | one => exact ⟨fm_one P, by rw [star_one]; exact one_mem _⟩
    | mul x y _ _ ihx ihy => exact ⟨fm_mul P ihx.1 ihy.1, by rw [star_mul]; exact mul_mem ihy.2 ihx.2⟩
  exact ⟨key.2, fun ε U V _ hU0 hU hV => ipA_fm P key.1 U V hU0 hU hV⟩

end Formalism.FourierDecayAlt.P.CutMP.JA
