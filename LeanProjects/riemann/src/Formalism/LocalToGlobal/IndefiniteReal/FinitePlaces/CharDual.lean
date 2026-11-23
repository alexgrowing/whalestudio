import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharStd
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharCompl

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Topology Filter
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tate

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem rat_of_perp (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F)
    (ha : ∀ q : D.host.F, ψ (algebraMap D.host.F (AF D.host.F) q * a) = 1) :
    ∃ q : D.host.F, a = algebraMap D.host.F (AF D.host.F) q := by
  classical
  let P : Set (AF D.host.F) := {c | ∀ q : D.host.F, ψ (algebraMap D.host.F (AF D.host.F) q * c) = 1}
  have hPF : ∀ q : D.host.F, algebraMap D.host.F (AF D.host.F) q ∈ P := fun q q' => by
    rw [← map_mul]; exact hψ.1.2.2.1 _
  have hPadd : ∀ c c', c ∈ P → c' ∈ P → c + c' ∈ P := fun c c' hc hc' q => by
    rw [mul_add, AddChar.map_add_eq_mul, hc q, hc' q, one_mul]
  have hPneg : ∀ c, c ∈ P → -c ∈ P := fun c hc q => by
    rw [mul_neg, AddChar.map_neg_eq_inv, hc q, inv_one]
  have hPsmul : ∀ (q : D.host.F) c, c ∈ P → algebraMap D.host.F (AF D.host.F) q * c ∈ P := fun q c hc q' => by
    rw [← mul_assoc, ← map_mul]; exact hc _
  have hPclosed : IsClosed P := by
    have : P = ⋂ q : D.host.F, (fun c => ψ (algebraMap D.host.F (AF D.host.F) q * c)) ⁻¹' {1} := by
      ext c; simp [P]
    rw [this]
    exact isClosed_iInter fun q => isClosed_singleton.preimage
      ((psi_cont hψ).comp (continuous_const.mul continuous_id))
  obtain ⟨K, hK, hF0K⟩ := Formalism.IndefR.PHeisFC.fundamental_set_subset_compact D.host.F

  have hN : ∀ᶠ c in 𝓝 (0 : AF D.host.F), ∀ k ∈ K, 1 / 2 < (ψ (c * k)).re := by
    refine hK.eventually_forall_of_forall_eventually fun k _ => ?_
    have hcont : Continuous fun p : AF D.host.F × AF D.host.F => (ψ (p.1 * p.2)).re :=
      Complex.continuous_re.comp ((psi_cont hψ).comp (continuous_fst.mul continuous_snd))
    have h0 : (1 / 2 : ℝ) < (ψ ((0, k).1 * (0, k).2)).re := by
      simp only [zero_mul, AddChar.map_zero_eq_one, Complex.one_re]; norm_num
    exact continuousAt_const.eventually_lt hcont.continuousAt h0

  have hdisc : ∀ᶠ c in 𝓝 (0 : AF D.host.F), c ∈ P → c = 0 := by
    filter_upwards [hN] with c hc hcP
    refine psi_nondeg hψ c fun y => ?_
    obtain ⟨q, hq, -⟩ := Formalism.IndefR.PHeisFC.ad_exU D.host.F y
    have hy : ∀ n : ℕ, ψ (c * (n • y)) = ψ (c * y) ^ n := fun n => by
      rw [mul_smul_comm, ← AddChar.map_nsmul_eq_pow]
    have hre : ∀ z : AF D.host.F, 1 / 2 < (ψ (c * z)).re := fun z => by
      obtain ⟨q', hq', -⟩ := Formalism.IndefR.PHeisFC.ad_exU D.host.F z
      have e : c * z = algebraMap D.host.F (AF D.host.F) (-q') * c + c * (algebraMap D.host.F (AF D.host.F) q' + z) := by
        rw [map_neg]; ring
      rw [e, AddChar.map_add_eq_mul, hcP (-q'), one_mul]
      exact hc _ (hF0K hq')
    refine Formalism.IndefR.PHeisTh.eq_one_of_re_pow_gt _ (psi_norm hψ _) fun n => ?_
    rw [← hy n]; exact hre _
  obtain ⟨N, hN0, hNP⟩ : ∃ N ∈ 𝓝 (0 : AF D.host.F), ∀ c ∈ N, c ∈ P → c = 0 := ⟨_, hdisc, fun c hc => hc⟩
  obtain ⟨U, hUN, hUo, hU0⟩ := mem_nhds_iff.1 hN0

  have hfin : (P ∩ K).Finite := by
    have hcpt : IsCompact (P ∩ K) := hK.inter_left hPclosed
    refine hcpt.finite ⟨?_⟩
    refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
    refine ⟨(fun z => z - (x : AF D.host.F)) ⁻¹' U, hUo.preimage (continuous_id.sub continuous_const), ?_⟩
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      have hyx : (y : AF D.host.F) - x ∈ P := by
        have := hPadd _ _ y.2.1 (hPneg _ x.2.1); rwa [← sub_eq_add_neg] at this
      exact Subtype.ext (sub_eq_zero.1 (hNP _ (hUN hy) hyx))
    · rintro rfl; simpa using hU0

  by_contra hnot
  push Not at hnot
  have hrep : ∀ q : D.host.F, ∃ r : D.host.F, algebraMap D.host.F (AF D.host.F) r + algebraMap D.host.F (AF D.host.F) q * a ∈ Formalism.IndefR.PHeisFC.F0 D.host.F :=
    fun q => (Formalism.IndefR.PHeisFC.ad_exU D.host.F _).exists
  choose r hr using hrep
  let g : D.host.F → AF D.host.F := fun q => algebraMap D.host.F (AF D.host.F) (r q) + algebraMap D.host.F (AF D.host.F) q * a
  have hgP : ∀ q, g q ∈ P ∩ K := fun q =>
    ⟨hPadd _ _ (hPF _) (hPsmul _ _ ha), hF0K (hr q)⟩
  have hginj : Function.Injective g := by
    intro q q' hqq
    by_contra hne
    apply hnot ((r q' - r q) / (q - q'))
    have hsub : q - q' ≠ 0 := sub_ne_zero.2 hne
    have e : algebraMap D.host.F (AF D.host.F) (q - q') * a = algebraMap D.host.F (AF D.host.F) (r q' - r q) := by
      simp only [g] at hqq
      rw [map_sub, map_sub, sub_mul]
      linear_combination hqq
    calc a = algebraMap D.host.F (AF D.host.F) (1 / (q - q')) * (algebraMap D.host.F (AF D.host.F) (q - q') * a) := by
          rw [← mul_assoc, ← map_mul, one_div_mul_cancel hsub, map_one, one_mul]
      _ = algebraMap D.host.F (AF D.host.F) (1 / (q - q')) * algebraMap D.host.F (AF D.host.F) (r q' - r q) := by rw [e]
      _ = algebraMap D.host.F (AF D.host.F) ((r q' - r q) / (q - q')) := by
          rw [← map_mul]; congr 1; field_simp
  exact (Set.infinite_of_injective_forall_mem hginj hgP) hfin

end Tate

section Matrix

variable {D : D7} (S T : HSp D)

theorem embedding_xi_zero_ne_zero : D.host.xi0 ≠ 0 := by
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hdpos : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hd
    have : (Real.sqrt D.host.d : ℂ) = 0 := by
      rcases mul_eq_zero.1 hd.symm with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    exact (Real.sqrt_pos.2 hdpos).ne' (by exact_mod_cast this)
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  unfold Host.xi0
  exact div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero hN hs)

def hE (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  ∑ a, ∑ b, ∑ c, ∑ d, S.gram⁻¹ a b * star (γ c b) * T.gram c d * e d a

def betaO (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.F :=
  Algebra.trace D.host.F D.host.E (D.host.xi0 * hE S T e γ)

theorem symplO_ratW_ratW (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (ratW T S e) (ratW T S γ) = algebraMap D.host.F (AF D.host.F) (betaO S T e γ) := by
  have h : hO S T (ratW T S e) (ratW T S γ) = incA D (hE S T e γ) := by
    unfold hO hE
    simp only [map_sum, map_mul, ratW, Matrix.map_apply, Brg.cA_inc]
  unfold symplO betaO
  rw [h, ← map_mul, trace_incA]

theorem symplO_smul_left (c : AF D.host.F) (x y : WO S T) : symplO S T (c • x) y = c * symplO S T x y := by
  have h : hO S T (c • x) y = algebraMap (AF D.host.F) (AE D) c * hO S T x y := by
    unfold hO
    simp only [Matrix.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring
  unfold symplO
  rw [h, mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

def symplLin (y : WO S T) : WO S T →ₗ[AF D.host.F] AF D.host.F where
  toFun x := symplO S T x y
  map_add' x x' := symplO_add_left S T x x' y
  map_smul' c x := symplO_smul_left S T c x y

theorem betaO_add_right (e γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    betaO S T e (γ + γ') = betaO S T e γ + betaO S T e γ' := by
  unfold betaO hE
  rw [← map_add, ← mul_add]
  congr 2
  simp only [Matrix.add_apply, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hE_smul_right (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hE S T e (q • γ) = algebraMap D.host.F D.host.E q * hE S T e γ := by
  unfold hE
  have h : ∀ c b, star ((q • γ) c b) = algebraMap D.host.F D.host.E q * star (γ c b) := fun c b => by
    rw [Matrix.smul_apply, Algebra.smul_def, star_mul', Eqv.star_algebraMapF, mul_comm]
  simp only [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem hE_smul_left (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hE S T (q • e) γ = algebraMap D.host.F D.host.E q * hE S T e γ := by
  unfold hE
  simp only [Matrix.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem trace_alg_mul (q : D.host.F) (z : D.host.E) :
    Algebra.trace D.host.F D.host.E (D.host.xi0 * (algebraMap D.host.F D.host.E q * z)) =
      q * Algebra.trace D.host.F D.host.E (D.host.xi0 * z) := by
  rw [mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem betaO_smul_right (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    betaO S T e (q • γ) = q * betaO S T e γ := by
  unfold betaO; rw [hE_smul_right, trace_alg_mul]

theorem betaO_add_left (e e' γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    betaO S T (e + e') γ = betaO S T e γ + betaO S T e' γ := by
  unfold betaO hE
  rw [← map_add, ← mul_add]
  congr 2
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem betaO_smul_left (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    betaO S T (q • e) γ = q * betaO S T e γ := by
  unfold betaO; rw [hE_smul_left, trace_alg_mul]

def epsO (a : Formalism.IndefR.PHeisTh.Ix T S) : Matrix (Fin T.rank) (Fin S.rank) D.host.E :=
  Matrix.single a.1 a.2.1 (Module.finBasis D.host.F D.host.E a.2.2)

theorem eV_eq (a : Formalism.IndefR.PHeisTh.Ix T S) : Formalism.IndefR.PHeisTh.eV T S a = ratW T S (epsO S T a) := by
  ext i j
  simp only [Formalism.IndefR.PHeisTh.eV, epsO, ratW, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem sum_epsO (e : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∑ a : Formalism.IndefR.PHeisTh.Ix T S, (Module.finBasis D.host.F D.host.E).repr (e a.1 a.2.1) a.2.2 • epsO S T a = e := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, epsO, Matrix.single_apply, Fintype.sum_prod_type, smul_ite,
    smul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (Module.finBasis D.host.F D.host.E).sum_repr (e i j)

def LamO : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F] (Formalism.IndefR.PHeisTh.Ix T S → D.host.F) where
  toFun γ a := betaO S T (epsO S T a) γ
  map_add' γ γ' := by funext a; exact betaO_add_right S T _ γ γ'
  map_smul' q γ := by funext a; exact betaO_smul_right S T q _ γ

theorem betaO_eq_zero_of (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (h : LamO S T γ = 0)
    (e : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : betaO S T e γ = 0 := by
  rw [← sum_epsO S T e]
  have hadd : ∀ (s : Finset (Formalism.IndefR.PHeisTh.Ix T S)) (f : Formalism.IndefR.PHeisTh.Ix T S → Matrix (Fin T.rank) (Fin S.rank) D.host.E),
      betaO S T (∑ a ∈ s, f a) γ = ∑ a ∈ s, betaO S T (f a) γ := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      have := betaO_smul_left S T 0 0 γ
      rwa [zero_smul, zero_mul] at this
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, betaO_add_left, ih]
  rw [hadd]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [betaO_smul_left]
  have := congrFun h a
  simp only [LamO, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
  rw [this, mul_zero]

theorem LamO_injective : Function.Injective (LamO S T) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro γ hγ
  have h0 := betaO_eq_zero_of S T γ hγ
  by_contra hne

  let M : Matrix (Fin S.rank) (Fin T.rank) D.host.E := S.gram⁻¹ * Matrix.transpose (γ.map (starRingEnd D.host.E)) * T.gram
  have hM : M ≠ 0 := by
    intro hM0
    apply hne
    have hS := Matrix.mul_nonsing_inv S.gram (isUnit_iff_ne_zero.2 (Formalism.L2.Theta.gram_det_ne S))
    have hT := Matrix.mul_nonsing_inv T.gram (isUnit_iff_ne_zero.2 (Formalism.L2.Theta.gram_det_ne T))
    have e1 : Matrix.transpose (γ.map (starRingEnd D.host.E)) = S.gram * M * T.gram⁻¹ := by
      simp only [M, ← Matrix.mul_assoc, hS, Matrix.one_mul]
      rw [Matrix.mul_assoc, hT, Matrix.mul_one]
    rw [hM0, Matrix.mul_zero, Matrix.zero_mul] at e1
    ext c b
    have := congrFun (congrFun e1 b) c
    simpa using this
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h; push Not at h; exact hM (Matrix.ext h)
  let e : Matrix (Fin T.rank) (Fin S.rank) D.host.E := Matrix.single j i (D.host.xi0⁻¹ * (M i j)⁻¹)
  have hE1 : hE S T e γ = D.host.xi0⁻¹ := by
    have htr : hE S T e γ = (M * e).trace := by
      unfold hE
      have := Brg.hO_tr (starRingEnd D.host.E) (S.gram⁻¹) T.gram e γ
      simpa [M, Matrix.mul_assoc, starRingEnd_apply] using this
    have key : ∀ c : D.host.E, (M * Matrix.single j i c).trace = M i j * c := by
      intro c
      rw [Matrix.trace, Finset.sum_eq_single i]
      · simp [Matrix.mul_apply, Matrix.single_apply]
      · intro b _ hb; simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hb]
      · simp
    rw [htr, key]
    field_simp
  have h1 := h0 e
  unfold betaO at h1
  rw [hE1, mul_inv_cancel₀ embedding_xi_zero_ne_zero, ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap,
    nsmul_eq_mul, mul_one] at h1
  have h2 : (Module.finrank D.host.F D.host.E : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  exact h2 h1

theorem LamO_surjective : Function.Surjective (LamO S T) := by
  have hdim : Module.finrank D.host.F (Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
      Module.finrank D.host.F (Formalism.IndefR.PHeisTh.Ix T S → D.host.F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_matrix]
    simp [Formalism.IndefR.PHeisTh.Ix, Formalism.IndefR.PHeisFC.nE, Fintype.card_prod, Fintype.card_fin]
    ring
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 (LamO_injective S T)

theorem smul_ratW (r : D.host.F) (e : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    algebraMap D.host.F (AF D.host.F) r • ratW T S e = ratW T S (r • e) := by
  ext i j
  show algebraMap D.host.F (AF D.host.F) r • incA D (e i j) = incA D (r • e i j)
  rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, Algebra.smul_def r (e i j), map_mul]
  congr 1
  exact (Algebra.TensorProduct.includeRight.commutes r).symm

theorem ratL_of_perp {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : WO S T)
    (hx : ∀ γ, ψ (symplO S T x (ratW T S γ)) = 1) : x ∈ ratL T S := by
  have hx' : x = ∑ a, Formalism.IndefR.PHeisTh.Co T S x a • ratW T S (epsO S T a) := by
    conv_lhs => rw [← Formalism.IndefR.PHeisTh.sum_eV T S x]
    simp only [eV_eq]
  have hcoord : ∀ γ, symplO S T x (ratW T S γ) =
      ∑ a, Formalism.IndefR.PHeisTh.Co T S x a * algebraMap D.host.F (AF D.host.F) (LamO S T γ a) := by
    intro γ
    have := congrArg (symplLin S T (ratW T S γ)) hx'
    rw [map_sum] at this
    simp only [map_smul, smul_eq_mul] at this
    rw [show symplO S T x (ratW T S γ) = symplLin S T (ratW T S γ) x from rfl, this]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ * symplO S T _ _ = _
    rw [symplO_ratW_ratW]; rfl
  have hrat : ∀ a, ∃ r : D.host.F, Formalism.IndefR.PHeisTh.Co T S x a = algebraMap D.host.F (AF D.host.F) r := by
    intro a
    refine rat_of_perp hψ _ fun q => ?_
    obtain ⟨γ, hγ⟩ := LamO_surjective S T (Pi.single a q)
    have := hx γ
    rw [hcoord, hγ, Finset.sum_eq_single a] at this
    · rwa [Pi.single_eq_same, mul_comm] at this
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, mul_zero]
    · simp
  choose r hr using hrat
  let ratWHom : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T :=
    ⟨⟨ratW T S, ratW_zero S T⟩, ratW_add S T⟩
  refine (mem_ratL_iff S T x).2 ⟨∑ a, r a • epsO S T a, ?_⟩
  rw [hx']
  show ratWHom (∑ a, r a • epsO S T a) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show ratW T S (r a • epsO S T a) = _
  rw [hr a, smul_ratW]

theorem charComplete (D : D7) : CharComplete D :=
  charComplete_of fun _ hψ S T x hx => ratL_of_perp S T hψ x hx

end Matrix

end Formalism.IndefR.Fin

end
