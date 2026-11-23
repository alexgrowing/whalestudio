import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoPlaceComponentsFiniteAdelicUnitaryStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceProduct

theorem mix_orth {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {e f : A} (h : e * f = 0)
    (a : Matrix n n A) :
    (e • a + (1 - e) • (1 : Matrix n n A)) * (f • a + (1 - f) • (1 : Matrix n n A)) =
      (e + f) • a + (1 - (e + f)) • (1 : Matrix n n A) := by
  have h1 : e * (1 - f) = e := by linear_combination -h
  have h2 : (1 - e) * f = f := by linear_combination -h
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination h
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul]
  rw [h, h1, h2, h3, zero_smul, zero_add, add_smul]
  abel

theorem sum_idem {A ι : Type} [CommRing A] (e : ι → A) (h1 : ∀ i, e i * e i = e i)
    (h2 : ∀ i j, i ≠ j → e i * e j = 0) (B : Finset ι) : (∑ i ∈ B, e i) * (∑ i ∈ B, e i) = ∑ i ∈ B, e i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => h2 i j (Ne.symm hj)) (fun hn => absurd hi hn), h1]

theorem exists_components (D : D7) (V : HSp D) (g : GA D V)
    (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F) (hε : ∀ v, IsPlaceIdem D v (ε v)) :
    ∃ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V,
      (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      gs ∅ = 1 ∧ ∀ v B (h : v ∉ B), gs (Finset.cons v B h) = gs {v} * gs B := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hsum : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) = ∑ v ∈ A, algebraMap (AF D.host.F) (AE D) (ε v) :=
    fun A => map_sum _ _ _
  have hid : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) * algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) =
        algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) := by
    intro A
    rw [hsum]
    exact sum_idem (fun v => algebraMap (AF D.host.F) (AE D) (ε v))
      (fun v => GlobalTheory.IdemSupport.place_idem hΦ (hε v))
      (fun v w hvw => GlobalTheory.IdemSupport.place_orth hΦ (hε v) (hε w) hvw) A
  have hc := fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    GlobalTheory.IdemSupport.cA_algebraMap (D := D) (∑ v ∈ A, ε v)
  choose gs hgs using fun A => GlobalTheory.IdemSupport.exists_piece V (hid A) (hc A) g
  refine ⟨gs, hgs, ?_, ?_⟩
  · apply GlobalTheory.IdemSupport.mt_inj V
    rw [hgs, GlobalTheory.IdemSupport.mt_one, Finset.sum_empty, map_zero, zero_smul, sub_zero, one_smul, zero_add]
  · intro v B hvB
    apply GlobalTheory.IdemSupport.mt_inj V
    rw [GlobalTheory.IdemSupport.mt_mul, hgs, hgs, hgs, Finset.sum_cons, Finset.sum_singleton, map_add]
    refine (mix_orth ?_ _).symm
    rw [hsum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun w hw =>
      GlobalTheory.IdemSupport.place_orth hΦ (hε v) (hε w) (fun hvw => hvB (by rw [hvw]; exact hw))

theorem eigen_of_local_components : ∀ (D : D7) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), (∀ w, Continuous fun p : GA D S × GA D T => om p f w) → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) (s : HeightOneSpectrum (𝓞 D.host.F) → ℂ), (∀ v, v ∉ A → s v = 1) → (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (g' : GA D S) (h' : GA D T), Formalism.L2.Theta.mt S g' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt S g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → Formalism.L2.Theta.mt T h' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt T h + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → om (g', h') f = s v • f) → om (g, h) f = (∏ v ∈ A, s v) • f := by
  intro D S T om f hcont g hg h hh A s hs hloc
  choose ε hε using fun v : HeightOneSpectrum (𝓞 D.host.F) => GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  obtain ⟨gs, hgs, hgs0, hgsm⟩ := exists_components D S g ε hε
  obtain ⟨hs', hhs, hhs0, hhsm⟩ := exists_components D T h ε hε
  have key : ∀ B : Finset (HeightOneSpectrum (𝓞 D.host.F)), om (gs B, hs' B) f = (∏ v ∈ B, s v) • f := by
    intro B
    induction B using Finset.cons_induction with
    | empty =>
      rw [hgs0, hhs0, Finset.prod_empty, one_smul]
      show om 1 f = f
      rw [map_one]
      rfl
    | cons v B hvB ih =>
      have hv := hloc v (ε v) (hε v) (gs {v}) (hs' {v}) (by rw [hgs, Finset.sum_singleton])
        (by rw [hhs, Finset.sum_singleton])
      rw [hgsm v B hvB, hhsm v B hvB, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih, map_smul, hv,
        smul_smul, Finset.prod_cons, mul_comm]
  have hpair : Filter.Tendsto (fun B => (gs B, hs' B)) Filter.atTop (nhds (g, h)) :=
    (GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary D S g hg ε hε gs hgs).prodMk_nhds (GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary D T h hh ε hε hs' hhs)
  funext w
  rw [Pi.smul_apply, smul_eq_mul]
  have ht := ((hcont w).tendsto (g, h)).comp hpair
  refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop A] with B hB
  show _ = om (gs B, hs' B) f w
  rw [key, Pi.smul_apply, smul_eq_mul, Finset.prod_subset hB fun v _ hv => hs v hv]

end GlobalTheory.PlaceProduct
