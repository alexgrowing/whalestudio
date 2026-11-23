import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem map_eq_zero_of_repr {F A E R ι : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E] [CommRing R]
    [Fintype ι] (b : Module.Basis ι F E) (φ : A ⊗[F] E →+* R) (z : A ⊗[F] E)
    (hc : ∀ i, φ (((Algebra.TensorProduct.basis A b).repr z i) ⊗ₜ[F] 1) = 0) : φ z = 0 := by
  have hs : z = ∑ i, ((Algebra.TensorProduct.basis A b).repr z i ⊗ₜ[F] (1 : E)) * ((1 : A) ⊗ₜ[F] b i) := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis A b).sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      one_mul]
  rw [hs, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, hc i, zero_mul]

theorem ev_eq_zero {D : D7} {l : ℕ} [Fact l.Prime] {inc : D.host.E →+* PadicAlgCl l}
    {ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l} (hev : EvOk inc ev)
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 D.host.F), ((l : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal → GlobalTheory.HeckeRowsCompare.cmp D w z = 0) :
    ev z = 0 := by
  refine map_eq_zero_of_repr (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Module.finBasis D.host.F D.host.E) ev z fun i => ?_
  refine hev.2.2.1 _ fun w hw => ?_
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F w)
    (Module.finBasis D.host.F D.host.E)).repr z i) (hz w hw)
  simp only [GlobalTheory.HeckeRowsCompare.cmp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [GlobalTheory.HeckeRowsCompare.repr_map, map_zero] at e
  exact e

theorem map_eq_one_of_isLocEnv : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  have hloc : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V ((pl i.1).under (𝓞 D.host.F)) x :=
    GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 hx)
  ext a b
  have h0 : ev (x.1.1 a b - (1 : Matrix (Fin V.rank) (Fin V.rank) _) a b) = 0 := by
    refine ev_eq_zero hev _ fun w hw => ?_
    have hne : w ≠ (pl i.1).under (𝓞 D.host.F) := by
      rintro rfl
      apply hl
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hw
      rwa [map_natCast] at h2
    have h1 : x.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hloc w hne
    have h3 := congrFun (congrFun h1 a) b
    rw [Matrix.map_apply] at h3
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h0
  rw [Matrix.map_apply]
  refine h0.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.EvLocal

end
