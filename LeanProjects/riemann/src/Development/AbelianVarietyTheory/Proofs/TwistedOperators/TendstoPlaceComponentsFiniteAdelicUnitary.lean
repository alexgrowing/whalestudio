import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalVCutIdemOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Filter Topology

namespace GlobalTheory.PlaceLimit

theorem sum_placeIdem {D : D7} {ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F}
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∑ v ∈ A, ε v = pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  choose α h0 h1 h2 using hε
  refine Prod.ext ?_ ?_
  · change fstA D.host.F (∑ v ∈ A, ε v) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun v _ => by rw [h0]; rfl
  · change sndA D.host.F (∑ v ∈ A, ε v) = GlobalTheory.LevelClosure.cutIdem A
    rw [map_sum]
    refine RestrictedProduct.ext _ _ fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (∑ v ∈ A, sndA D.host.F (ε v)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (GlobalTheory.LevelClosure.cutIdem A)
    have e : ∀ v, sndA D.host.F (ε v) = α v := fun v => by rw [h0]; rfl
    rw [map_sum]
    simp only [e]
    by_cases hw : w ∈ A
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw,
        Finset.sum_eq_single w (fun v _ hv => h2 v w (Ne.symm hv)) (fun h => absurd hw h), h1]
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw]
      exact Finset.sum_eq_zero fun v hv => h2 v w fun h => hw (h ▸ hv)

theorem pair_cutIdem_mul_self {F : Type} [Field F] [NumberField F] (A : Finset (HeightOneSpectrum (𝓞 F))) :
    pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) * pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) =
      pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  refine Prod.ext (mul_zero _) ?_
  change GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A = GlobalTheory.LevelClosure.cutIdem A
  refine RestrictedProduct.ext _ _ fun w => ?_
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A) =
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A)
  rw [map_mul]
  by_cases hw : w ∈ A
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw, one_mul]
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw, zero_mul]

theorem tendsto_cut_mul {D : D7} {z : AE D} (hz : infPart D z = 0) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) * z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h : Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) atTop (𝓝 (pairA D.host.F 0 1)) := by
    have := GlobalTheory.LevelClosure.tendsto_cutIdem_mul (1 : Af D.host.F)
    simp only [mul_one] at this
    exact (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds this
  have h2 := h.smul_const z
  have e : pairA D.host.F 0 1 • z = z := by
    rw [Algebra.smul_def, mul_comm]
    exact GlobalTheory.PlaceDatum.mul_pair_one hz
  rw [e] at h2
  simpa only [Algebra.smul_def] using h2

theorem tendsto_mix {D : D7} (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) atTop (𝓝 (Formalism.L2.Theta.mt V g)) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h1 : infPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1 i j) (show infHom V g = 1 from hg)
  have h2 : infPart D (Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = 0 := by
    rw [RingHom.map_sub, h1, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (RingHom.map_one _).symm
    · exact (RingHom.map_zero _).symm
  have h3 := (tendsto_cut_mul h2).add_const ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
  rw [sub_add_cancel] at h3
  refine h3.congr fun A => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem eq_mix_of_mul {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {f : R} (hf : f * f = f)
    {a a' b b' : Matrix n n R} (ha : a * a' = 1) (hb : b' * b = 1)
    (h : b = f • a + (1 - f) • (1 : Matrix n n R)) : b' = f • a' + (1 - f) • (1 : Matrix n n R) := by
  have : b * (f • a' + (1 - f) • (1 : Matrix n n R)) = 1 := by
    rw [h, GlobalTheory.IdemSupport.mix_mul hf, ha, one_mul, GlobalTheory.IdemSupport.mix_self]
  calc b' = b' * (b * (f • a' + (1 - f) • (1 : Matrix n n R))) := by rw [this, mul_one]
    _ = _ := by rw [← mul_assoc, hb, one_mul]

theorem tendsto_components : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V → ∀ (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) → Filter.Tendsto gs Filter.atTop (nhds g) := by
  intro D V g hg ε hε gs hgs
  simp only [sum_placeIdem hε] at hgs
  have hinv : ∀ A, Formalism.L2.Theta.mt V (gs A)⁻¹ =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g⁻¹ +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := fun A =>
    eq_mix_of_mul (by rw [← RingHom.map_mul, pair_cutIdem_mul_self])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, inv_mul_cancel, GlobalTheory.IdemSupport.mt_one]) (hgs A)
  have h1 := (tendsto_mix V hg).congr fun A => (hgs A).symm
  have h2 := (tendsto_mix V (inv_mem hg)).congr fun A => (hinv A).symm
  refine tendsto_subtype_rng.2 (Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_)
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

end GlobalTheory.PlaceLimit

end
