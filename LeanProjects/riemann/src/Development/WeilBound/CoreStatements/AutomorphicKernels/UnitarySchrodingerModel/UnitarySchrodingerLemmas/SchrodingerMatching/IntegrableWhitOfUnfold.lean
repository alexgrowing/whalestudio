import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.HaarFam

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

private theorem conjH_cancel (a a' : GL (Fin n) (AE D)) (h : a * a' = 1) (b : hermA D n) :
    conjH a (conjH a' b) = b := by
  have h1 : a.1 * a'.1 = 1 := by rw [← Units.val_mul, h, Units.val_one]
  have h2 : adj a'.1 * adj a.1 = 1 := by rw [← adj_mul, h1, adj_one]
  refine Subtype.ext ?_
  change a.1 * (a'.1 * b.1 * adj a'.1) * adj a.1 = b.1
  calc a.1 * (a'.1 * b.1 * adj a'.1) * adj a.1 = (a.1 * a'.1) * b.1 * (adj a'.1 * adj a.1) := by
        simp only [mul_assoc]
    _ = b.1 := by rw [h1, h2, one_mul, mul_one]

private theorem conjH_add' (a : GL (Fin n) (AE D)) (b c : hermA D n) :
    conjH a (b + c) = conjH a b + conjH a c := by
  refine Subtype.ext ?_
  change a.1 * (b.1 + c.1) * adj a.1 = a.1 * b.1 * adj a.1 + a.1 * c.1 * adj a.1
  rw [mul_add, add_mul]

private theorem continuous_conjH' (a : GL (Fin n) (AE D)) : Continuous (conjH (D := D) a) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem integrable_comp_conjH (lam : Measure (hermA D n)) (hlam : lam.IsAddHaarMeasure) (a : GL (Fin n) (AE D))
    {f : hermA D n → ℂ} (hf : Integrable f lam) : Integrable (fun b => f (conjH a b)) lam := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  have : IsTopologicalAddGroup (Mx D n n) := i1
  have : LocallyCompactSpace (Mx D n n) := i2
  have : SecondCountableTopology (Mx D n n) := i3
  have : T2Space (Mx D n n) := i4
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  have : LocallyCompactSpace (hermA D n) := (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := n)).locallyCompactSpace
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  let e : hermA D n ≃+ hermA D n :=
    { toFun := conjH a, invFun := conjH a⁻¹
      left_inv := conjH_cancel a⁻¹ a (inv_mul_cancel a)
      right_inv := conjH_cancel a a⁻¹ (mul_inv_cancel a)
      map_add' := conjH_add' a }
  have hc : Continuous e := continuous_conjH' a
  have hc' : Continuous e.symm := continuous_conjH' a⁻¹
  have : (lam.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map lam hc hc'
  have h1 := Measure.isAddLeftInvariant_eq_smul (lam.map e) lam
  have h2 : Integrable f (lam.map e) := by
    rw [h1]
    exact hf.smul_measure_nnreal
  exact h2.comp_aemeasurable hc.measurable.aemeasurable

private theorem sect_wn {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (H : G D n → ℝ≥0) {nb : hermA D n → G D n} (hnb : IsNMap nb)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) (z : ℂ) (b : hermA D n) :
    sect ω H Φ z (w * nb b) = npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ Φ.1 b := by
  unfold sect
  congr 1
  rw [map_mul, Module.End.mul_apply, hω.weyl w hw]
  unfold Jt
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    ext i j
    simp [GlobalTheory.StdUnn.inner, adj, Matrix.mul_apply]
  beta_reduce
  rw [hω.unip (nb b) b.1 (hnb b), h0, Matrix.trace_zero, trA, map_zero, AddChar.map_zero_eq_one, mul_one, mul_comm]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem integrable_whit_of_unfold (hU : Unfold) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
    ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
    ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
    ∀ φ : Mx D V.rank n → ℂ, φ ∈ schwartzA θ V.rank n → φ ∈ fockA θ V n l s →
    ∀ (T : Mx D n n) (z : ℂ), (n : ℝ) / 2 < z.re →
      Integrable (fun b : hermA D n => npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ φ b *
        ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n)))) lam := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ φ hsch hfock T z hz
  have hS' : Std D n V ψ χ θ μ ω H l s ν ⟨φ, hsch⟩ :=
    ⟨hS.hψ, hS.hχ, hS.hη, hS.hθ, hS.hμ, hS.hω, hS.hH, hS.hl, hS.hs, hS.hν, hfock⟩
  have h1 := (hU D n V ψ χ θ μ ω H l s ν ⟨φ, hsch⟩ hS' hR nb lam 𝓖 hC w hw β hβ z hz 1).1
  have h2 : Integrable (fun b : hermA D n => npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ φ b) lam := by
    refine h1.congr (Filter.Eventually.of_forall fun b => ?_)
    beta_reduce
    rw [mul_one]
    exact sect_wn hS.hω H hC.1 hw ⟨φ, hsch⟩ z b
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  have : IsTopologicalAddGroup (Mx D n n) := i1
  have : SecondCountableTopology (Mx D n n) := i3
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hc : Continuous fun b : hermA D n => ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n))) := by
    unfold halfTr
    exact hS.hψ.1.comp (continuous_const.mul (ht.comp
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace))).neg
  exact h2.mul_bdd (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun b => (hS.hψ.2.1 _).le)

end PositivityTheory.PfSWUS.SwMatch

end
