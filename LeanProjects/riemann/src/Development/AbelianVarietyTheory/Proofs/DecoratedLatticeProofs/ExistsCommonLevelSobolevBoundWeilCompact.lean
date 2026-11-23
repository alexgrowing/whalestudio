import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDens.WeilCompact

variable {D : D7}

theorem mt_mul_eq (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one_eq (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem continuous_mt_eq (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ x) = x := by
  unfold Formalism.IndefR.Datum.actO
  rw [inv_inv]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.Theta.mt T h), ← mt_mul_eq, ← mt_mul_eq, mul_inv_cancel, mul_inv_cancel,
    mt_one_eq, mt_one_eq, Matrix.one_mul, Matrix.mul_one]

open GlobalTheory.Size in

theorem dRho_om {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (g : GA D S) (h : GA D T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ
        (compAt θ τ (Formalism.L2.Theta.mt T h⁻¹) * z * compAt θ τ (Formalism.L2.Theta.mt S g)) f) := by
  rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ _ hf]
  congr 1
  have e1 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h
  have e2 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g
  simp only [Matrix.mul_assoc]
  rw [e2, Matrix.mul_one, ← Matrix.mul_assoc, e1, Matrix.one_mul]

def dirSize (θ : InfFam D) (S T : HSp D) (x : GA D S × GA D T) : ℝ :=
  ∑ a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, ∑ i, ∑ j,
    (|((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).re| +
     |((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).im|)

theorem continuous_dirSize {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) : Continuous (dirSize θ S T) := by
  unfold dirSize
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have h1 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq T).comp continuous_snd.inv)
  have h2 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt S x.1) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq S).comp continuous_fst)
  have h3 := ((h1.matrix_mul (continuous_const (y := Matrix.single a.2.1 a.2.2.1
    (if a.2.2.2 then Complex.I else 1)))).matrix_mul h2).matrix_elem i j
  exact (continuous_abs.comp (Complex.continuous_re.comp h3)).add (continuous_abs.comp (Complex.continuous_im.comp h3))

theorem actO_add' {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (x + y) = Formalism.IndefR.Datum.actO S T g h x + Formalism.IndefR.Datum.actO S T g h y := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_zero' {S T : HSp D} (g : GA D S) (h : GA D T) : Formalism.IndefR.Datum.actO S T g h 0 = 0 := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_zero, Matrix.zero_mul]

theorem actO_neg' {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (-x) = -Formalism.IndefR.Datum.actO S T g h x := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_neg, Matrix.neg_mul]

open GlobalTheory.Size in

theorem word_om_le {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {K : Set (GA D S × GA D T)}
    (B : ℝ≥0) (hB : ∀ x ∈ K, dirSize θ S T x ≤ B) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), l.length = k → ∀ x ∈ K,
      ∀ g, IsThetaFunO ψ S T g → l2O μ 𝓕 (wordAct (heisDer ψ θ) l (om x g)) ≤ C * sobO ψ θ μ 𝓕 k g := by
  induction k with
  | zero =>
    refine ⟨1, fun l hl x _ g hg => ?_⟩
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    rw [wordAct_nil, l2O_om_apply_eq_of_isThetaFunO hom hμ.1 hμ.2.1 hg, sobO_zero, ENNReal.coe_one, one_mul]
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * B, fun l hl x hx g hg => ?_⟩
    obtain ⟨g1, h1⟩ := x
    have hne : l ≠ [] := by rintro rfl; simp at hl
    rw [← List.dropLast_append_getLast hne, wordAct_append, wordAct_cons, wordAct_nil]
    set a := l.getLast hne
    have e := dRho_om hom hθ g1 h1 a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) hg
    have e' : heisDer ψ θ a (om (g1, h1) g) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1
        (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) (om (g1, h1) g) := rfl
    rw [e', e]
    have hg' := GlobalTheory.OrientedHeis.theta_dRho hθ hom.std a.1 (compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) hg
    have hs : ENNReal.ofReal (∑ i, ∑ j, (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
        |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        ≤ B := by
      rw [← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hB _ hx))
      unfold dirSize
      exact Finset.single_le_sum (f := fun a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool => ∑ i, ∑ j,
        (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
         |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        (fun b _ => by positivity) (Finset.mem_univ a)
    calc _ ≤ (C : ℝ≥0∞) * sobO ψ θ μ 𝓕 k _ := hC _ (by simp [hl]) _ hx _ hg'
      _ ≤ C * (ENNReal.ofReal _ * sobO ψ θ μ 𝓕 (k + 1) g) := by
          gcongr
          exact sobO_dRho_le hom.std hθ hg a.1 _ k
      _ ≤ C * (B * sobO ψ θ μ 𝓕 (k + 1) g) := by gcongr
      _ = ((C * B : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (k + 1) g := by push_cast; ring

end GlobalTheory.ThetaDens.WeilCompact

open GlobalTheory.ThetaDens.WeilCompact GlobalTheory.Size in

theorem GlobalTheory.ThetaDens.om_compact_sobCont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ K : Set (GA D S × GA D T), IsCompact K → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S T), IsOpen (U' : Set (WO S T)) ∧ (∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, om x f ∈ thetaLevel ψ S T U') ∧ ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, sobO ψ θ μ 𝓕 d (om x f) ≤ C * sobO ψ θ μ 𝓕 d' f := by
  intro D ψ S T χS χT om hom θ hθ μ 𝓕 hμ K hK U hU
  let U' : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ x ∈ K, Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U}
      add_mem' := fun {a b} ha hb x hx => by
        rw [Set.mem_setOf_eq] at ha hb
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (a + b) ∈ U
        rw [actO_add']; exact U.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
        rw [actO_zero']; exact U.zero_mem
      neg_mem' := fun {a} ha x hx => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (-a) ∈ U
        rw [actO_neg']; exact U.neg_mem (ha x hx) }
  have hU' : IsOpen (U' : Set (WO S T)) := by
    refine U'.isOpen_of_mem_nhds (g := 0) ?_
    refine hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T))
      (P := fun u x => Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U) fun x _ => ?_
    have hc : Continuous fun p : WO S T × (GA D S × GA D T) => Formalism.IndefR.Datum.actO S T p.2.1⁻¹ p.2.2⁻¹ p.1 := by
      unfold Formalism.IndefR.Datum.actO
      exact (((continuous_mt_eq T).comp continuous_snd.snd.inv).matrix_mul continuous_fst).matrix_mul
        ((continuous_mt_eq S).comp continuous_snd.fst.inv.inv)
    refine (hU.preimage hc).mem_nhds ?_
    show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
    rw [actO_zero']; exact U.zero_mem
  obtain ⟨B0, hB0⟩ := hK.bddAbove_image (continuous_dirSize hθ S T).continuousOn
  have hB : ∀ x ∈ K, dirSize θ S T x ≤ (B0.toNNReal : ℝ) := fun x hx =>
    (hB0 ⟨x, hx, rfl⟩).trans (Real.le_coe_toNNReal B0)
  refine ⟨U', hU', fun f hf x hx => ⟨hom.om_pres x f hf.1, fun u hu h0 => ?_⟩, fun d => ?_⟩
  · obtain ⟨g, h⟩ := x
    have hv : Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u ∈ U := hu (g, h) hx
    have hv0 : (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
      unfold Formalism.IndefR.Datum.actO
      rw [Matrix.map_mul, Matrix.map_mul, h0]; simp
    calc heisO ψ S T u (om (g, h) f)
        = heisO ψ S T (Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u)) (om (g, h) f) := by
          rw [actO_actO_inv]
      _ = om (g, h) (heisO ψ S T (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u) f) := (hom.om_heis g h _ f hf.1).symm
      _ = om (g, h) f := by rw [hf.2 _ hv hv0]
  · choose C hC using word_om_le hom hθ hμ _ hB
    refine ⟨d, ∑ k ∈ Finset.range (d + 1), ∑ _a : Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, C k,
      fun f hf x hx => ?_⟩
    show wordSum (heisDer ψ θ) (l2O μ 𝓕) d (om x f) ≤ _
    unfold wordSum
    rw [ENNReal.coe_finset_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [ENNReal.coe_finset_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    calc _ ≤ (C k : ℝ≥0∞) * sobO ψ θ μ 𝓕 k f := hC k _ (List.length_ofFn) x hx f hf.1
      _ ≤ C k * sobO ψ θ μ 𝓕 d f := by
          gcongr
          exact sobO_mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end
