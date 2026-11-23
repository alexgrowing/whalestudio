import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

def bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun p : Fin m × Fin n => absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2)))

theorem absFin_le_bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (i : Fin m) (j : Fin n) : absFin D.host.F v (compFin D.host.F D.host.E v (Y i j)) ≤ bF Y v := by
  unfold bF
  refine le_trans ?_ (le_max_right _ _)
  have h := Finset.le_sup (f := fun p : Fin m × Fin n =>
    absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2))) (Finset.mem_univ (i, j))
  exact h

theorem le_vFin {n : ℕ} (x : Fin n → AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin n) :
    absFin D.host.F v (compFin D.host.F D.host.E v (x i)) ≤ vFin v x := by
  unfold vFin
  have h := Finset.le_sup (f := fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))) (Finset.mem_univ i)
  exact h

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem eventually_bF_eq_one {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) :
    ∀ᶠ v in Filter.cofinite, bF Y v = 1 := by
  have h : ∀ᶠ v in Filter.cofinite, ∀ p : Fin m × Fin n,
      absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2)) ≤ 1 :=
    Filter.eventually_all.2 fun p => eventually_absFin_le_one D.host.F (Y p.1 p.2)
  refine h.mono fun v hv => ?_
  unfold bF
  exact max_eq_left (Finset.sup_le fun p _ => hv p)

theorem finite_mulSupport_bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) :
    (Function.mulSupport (bF Y)).Finite :=
  (Filter.eventually_cofinite.1 (eventually_bF_eq_one Y)).subset fun _ hv => hv

theorem vFin_mulVec_le {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (x : Fin n → AE D)
    (v : HeightOneSpectrum (𝓞 D.host.F)) : vFin v (Y *ᵥ x) ≤ bF Y v * vFin v x := by
  rw [vFin]
  refine Finset.sup_le fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact absFin_sum_le D.host.F v _ _ fun j _ =>
    (absFin_mul_le D.host.F v _ _).trans (mul_le_mul' (absFin_le_bF Y v i j) (le_vFin x v j))

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

open Classical in

def bI {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (w : InfinitePlace D.host.F) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun p : EmbOver D.host.E w × Fin m =>
    ∑ j, ‖infEmb p.1 (compInf D.host.F D.host.E w (Y p.2 j))‖₊)

theorem sum_le_bI {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (w : InfinitePlace D.host.F)
    (τ : EmbOver D.host.E w) (i : Fin m) :
    ∑ j, ‖infEmb τ (compInf D.host.F D.host.E w (Y i j))‖₊ ≤ bI Y w := by
  classical
  unfold bI
  refine le_trans ?_ (le_max_right _ _)
  have h := Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin m =>
    ∑ j, ‖infEmb p.1 (compInf D.host.F D.host.E w (Y p.2 j))‖₊) (Finset.mem_univ (τ, i))
  exact h

theorem le_vInf {n : ℕ} (x : Fin n → AE D) (w : InfinitePlace D.host.F) (τ : EmbOver D.host.E w) (i : Fin n) :
    ‖infEmb τ (compInf D.host.F D.host.E w (x i))‖₊ ≤ vInf w x := by
  classical
  unfold vInf
  have h := Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin n =>
    ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊) (Finset.mem_univ (τ, i))
  exact h

theorem vInf_mulVec_le {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (x : Fin n → AE D)
    (w : InfinitePlace D.host.F) : vInf w (Y *ᵥ x) ≤ bI Y w * vInf w x := by
  rw [vInf]
  refine Finset.sup_le fun p _ => ?_
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine (nnnorm_sum_le _ _).trans ?_
  refine le_trans ?_ (mul_le_mul' (sum_le_bI Y w p.1 p.2) le_rfl)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [nnnorm_mul]
  exact mul_le_mul' le_rfl (le_vInf x w p.1 j)

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem eventually_vFin_seen_eq_one (V : HSp D) (g : GA D V) {ξ : Fin V.rank → D.host.E} (hξ : ξ ≠ 0) :
    ∀ᶠ v in Filter.cofinite, vFin v (seen V g ξ) = 1 := by
  set u : Fin V.rank → AE D := fun i => incA D (ξ i) with hu
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
  have h1 : ∀ᶠ v in Filter.cofinite, vFin v u ≤ 1 :=
    (Filter.eventually_all.2 fun i => eventually_absFin_le_one D.host.F (u i)).mono fun v hv =>
      Finset.sup_le fun i _ => hv i
  have h2 : ∀ᶠ v in Filter.cofinite, 1 ≤ absFin D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i))) := by
    refine (eventually_absFin_le_one D.host.F (incA D (ξ i)⁻¹)).mono fun v hv => ?_
    have e : incA D (ξ i) * incA D (ξ i)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hi, map_one]
    have := absFin_mul_le D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i)))
      (compFin D.host.F D.host.E v (incA D (ξ i)⁻¹))
    rw [← map_mul, e, map_one, absFin_one] at this
    exact this.trans (mul_le_of_le_one_right' hv)
  refine ((h1.and h2).and ((eventually_bF_eq_one (mt V g⁻¹)).and (eventually_bF_eq_one (mt V g)))).mono
    fun v hv => le_antisymm ?_ ?_
  · refine (vFin_mulVec_le _ u v).trans ?_
    rw [hv.2.1, one_mul]; exact hv.1.1
  · have e : u = mt V g *ᵥ seen V g ξ := by
      rw [seen, Matrix.mulVec_mulVec, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mulVec]
    refine hv.1.2.trans ((le_vFin u v i).trans ?_)
    rw [e]
    refine (vFin_mulVec_le _ _ v).trans ?_
    rw [hv.2.2, one_mul]

theorem seen_emb {S A B : HSp D} (o : GlobalTheory.MixModel.OrthDec S A B) (h : GA D A) (η : Fin A.rank → D.host.E) :
    seen S (o.emb (h, 1)) (o.iA *ᵥ η) = o.jA *ᵥ seen A h η := by
  have e1 : (o.emb (h, 1))⁻¹ = o.emb (h⁻¹, 1) := by rw [← map_inv, Prod.inv_mk, inv_one]
  have e2 : (fun i => incA D ((o.iA *ᵥ η) i)) = o.jA *ᵥ fun i => incA D (η i) := by
    funext i; exact RingHom.map_mulVec (incA D) o.iA η i
  rw [seen, seen, e1, e2, Matrix.mulVec_mulVec, GlobalTheory.MixModel.OrthDec.emb_jA, Matrix.mulVec_mulVec]

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem vsize_zero {n : ℕ} : vsize (0 : Fin n → AE D) = 0 := by
  have h : ∀ w : InfinitePlace D.host.F, vInf w (0 : Fin n → AE D) = 0 := fun w => by
    classical
    unfold vInf
    refine le_antisymm (Finset.sup_le fun p _ => ?_) zero_le
    simp
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace D.host.F))
  unfold vsize
  rw [Finset.prod_eq_zero (Finset.mem_univ w) (h w), zero_mul, NNReal.coe_zero]

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

theorem vsize_seen_emb_le : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ C : ℝ,
    ∀ (h : GA D A) (η : Fin A.rank → D.host.E),
      GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) ≤ C * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) := by
  intro D S A B o
  refine ⟨(((∏ w, bI o.jA w) * ∏ᶠ v, bF o.jA v : ℝ≥0) : ℝ), fun h η => ?_⟩
  by_cases hη : η = 0
  · subst hη
    have e : (o.iA *ᵥ (0 : Fin A.rank → D.host.E)) = 0 := Matrix.mulVec_zero _
    have z : ∀ (V : HSp D) (g : GA D V), seen V g 0 = 0 := fun V g => by
      have h0 : (fun i => incA D ((0 : Fin V.rank → D.host.E) i)) = 0 := funext fun i => map_zero _
      rw [seen, h0, Matrix.mulVec_zero]
    rw [e, z, z, vsize_zero]
    exact mul_nonneg (NNReal.coe_nonneg _) (vsize_nonneg _)
  have hη' : o.iA *ᵥ η ≠ 0 := fun e => hη (by
    have := congrArg (o.qA *ᵥ ·) e
    simpa [Matrix.mulVec_mulVec, GlobalTheory.MixModel.OrthDec.qA_iA] using this)
  have f1 := Filter.eventually_cofinite.1 (eventually_vFin_seen_eq_one A h hη)
  have f2 := Filter.eventually_cofinite.1 (eventually_vFin_seen_eq_one S (o.emb (h, 1)) hη')
  rw [seen_emb] at f2 ⊢
  have hf : (Function.mulSupport fun v => vFin v (seen A h η)).Finite := f1.subset fun v hv => hv
  have hf' : (Function.mulSupport fun v => vFin v (o.jA *ᵥ seen A h η)).Finite := f2.subset fun v hv => hv
  unfold vsize
  rw [← NNReal.coe_mul, NNReal.coe_le_coe]
  calc (∏ w, vInf w (o.jA *ᵥ seen A h η)) * ∏ᶠ v, vFin v (o.jA *ᵥ seen A h η)
      ≤ (∏ w, bI o.jA w * vInf w (seen A h η)) * ∏ᶠ v, bF o.jA v * vFin v (seen A h η) :=
        mul_le_mul' (Finset.prod_le_prod' fun w _ => vInf_mulVec_le o.jA _ w)
          (finprod_le_finprod' hf' (((finite_mulSupport_bF o.jA).union hf).subset (Function.mulSupport_mul _ _))
            fun v => vFin_mulVec_le o.jA _ v)
    _ = _ := by
        rw [Finset.prod_mul_distrib, finprod_mul_distrib (finite_mulSupport_bF o.jA) hf, mul_mul_mul_comm]

end GlobalTheory.HtOrth.Transp

end
