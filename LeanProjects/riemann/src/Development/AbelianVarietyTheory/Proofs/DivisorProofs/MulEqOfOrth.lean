import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GammaMembershipConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker GlobalTheory.IndefiniteRowSideFullHecke Filter Topology
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.VacuumFrameCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem place_unique {v : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v ε') : ε = ε' := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨β, rfl, k1, k0⟩ := h'
  congr 1
  refine FiniteAdeleRing.ext _ fun w => ?_
  by_cases hw : w = v
  · subst hw; exact h1.trans k1.symm
  · exact (h0 w hw).trans (k0 w hw).symm

theorem af_ext {α β : Af D.host.F} (h : ∀ w, evalV D.host.F w α = evalV D.host.F w β) : α = β :=
  FiniteAdeleRing.ext _ h

theorem place_orth {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * β = 0 from af_ext fun w => ?_)
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · rw [k0 w (hw ▸ hv), mul_zero]
  · rw [h0 w hw, zero_mul]

theorem place_idem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * α = α from af_ext fun w => ?_)
  rw [map_mul]
  by_cases hw : w = v
  · rw [hw, h1, mul_one]
  · rw [h0 w hw, zero_mul]

theorem place_inf {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -, -⟩ := h
  exact TensorProduct.zero_tmul _ _

theorem place_int {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : IsPlaceIdem D v η) :
    finPart D (algebraMap (AF D.host.F) (AE D) η) ∈ intAE D := by
  obtain ⟨β, rfl, h1, h0⟩ := h
  refine AddSubgroup.subset_closure ⟨β, fun w => ?_, 1, rfl⟩
  by_cases hw : w = v
  · subst hw; rw [h1]; exact one_mem _
  · rw [h0 w hw]; exact zero_mem _

theorem eq_of_orth {R : Type} [CommRing R] {e c e' c' : R} (h : e + c = e' + c') (h1 : e * e' = 0) (h2 : c * c' = 0)
    (h3 : e * e = e) (h4 : e * c = 0) (h5 : c' * c' = c') (h6 : e' * c' = 0) : e = c' := by
  linear_combination (e + c') * h - h3 - h4 + h1 - h2 + h6 + h5

theorem eq_or_eq_conj {e e' : AE D} (he : IsSplitIdem D e) (he' : IsSplitIdem D e')
    (h : e + cA D e = e' + cA D e') : e = e' ∨ e = cA D e' := by
  rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he he' with h1 | h1
  · exact Or.inl h1
  · right
    have h2 : cA D e * cA D e' = 0 := by rw [← map_mul, h1, map_zero]
    exact eq_of_orth h h1 h2 he.1 he.2.1 (GlobalTheory.PlaceModelSum.isSplitIdem_cA he').1 he'.2.1

theorem splitDet_iff {T : HSp D} (k : GA D T) (x : (AE D)ˣ) : RealPointEmbeddings.IsSplitDet k x ↔ VacuumCharacterDeterminant.IsSplitDet T k x := by
  refine and_congr_right fun _ => ⟨fun ⟨h1, h2⟩ v ε hε => ?_, fun h => ⟨fun e he => ?_, fun ε hε => ?_⟩⟩
  · by_cases hs : ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε
    · obtain ⟨e, he, h3⟩ := hs
      rcases h1 e he with h4 | h4
      · exact Or.inl ⟨e, he, h3, h4⟩
      · refine Or.inl ⟨cA D e, GlobalTheory.PlaceModelSum.isSplitIdem_cA he, ?_, ?_⟩
        · rw [GlobalTheory.LatVac.cA_cA, add_comm, h3]
        · rw [GlobalTheory.LatVac.cA_cA]; exact h4
    · exact Or.inr ⟨hs, h2 ε ⟨⟨v, hε⟩, hs⟩⟩
  · obtain ⟨v, ε, hε, h3⟩ := he.2.2
    rcases h v ε hε with ⟨e', he', h4, h5⟩ | ⟨h4, -⟩
    · rcases eq_or_eq_conj he he' (h3.trans h4.symm) with rfl | rfl
      · exact Or.inl h5
      · rw [GlobalTheory.LatVac.cA_cA]; exact Or.inr h5
    · exact absurd ⟨e, he, h3⟩ h4
  · obtain ⟨⟨v, hv⟩, hn⟩ := hε
    rcases h v ε hv with ⟨e', he', h4, -⟩ | ⟨-, h4⟩
    · exact absurd ⟨e', he', h4⟩ hn
    · exact h4

def cut {R : Type} [CommRing R] (η : R) (h : η * η = η) (x : Rˣ) : Rˣ where
  val := 1 + η * ((x : R) - 1)
  inv := 1 + η * (((x⁻¹ : Rˣ) : R) - 1)
  val_inv := by
    have := x.mul_inv
    linear_combination ((x : R) - 1) * (((x⁻¹ : Rˣ) : R) - 1) * h + η * this
  inv_val := by
    have := x.mul_inv
    linear_combination ((x : R) - 1) * (((x⁻¹ : Rˣ) : R) - 1) * h + η * this

theorem cut_val {R : Type} [CommRing R] (η : R) (h : η * η = η) (x : Rˣ) :
    (cut η h x : R) = 1 + η * ((x : R) - 1) := rfl

theorem cut_inv {R : Type} [CommRing R] (η : R) (h : η * η = η) (x : Rˣ) :
    (((cut η h x)⁻¹ : Rˣ) : R) = 1 + η * (((x⁻¹ : Rˣ) : R) - 1) := rfl

theorem cut_add {R : Type} [CommRing R] {η a b : R} (h : η * η = η) (ha : a * a = a) (hb : b * b = b)
    (e1 : η = a + b) (e2 : a * b = 0) (x : Rˣ) : cut η h x = cut a ha x * cut b hb x := by
  refine Units.ext ?_
  rw [Units.val_mul, cut_val, cut_val, cut_val, e1]
  linear_combination (-((x : R) - 1) ^ 2) * e2

theorem cut_eq_one {R : Type} [CommRing R] {η a b : R} (h : η * η = η) (e1 : a + b = η) (x : Rˣ)
    (ha : a * x = a) (hb : b * x = b) : cut η h x = 1 := by
  refine Units.ext ?_
  rw [cut_val, ← e1, Units.val_one]
  linear_combination ha + hb

theorem cut_eq_self {R : Type} [CommRing R] {η : R} (h : η * η = η) (x : Rˣ) (hx : η * ((x : R) - 1) = x - 1) :
    cut η h x = x := by
  refine Units.ext ?_
  rw [cut_val, hx]
  ring

theorem cut_supp {R : Type} [CommRing R] {η : R} (h : η * η = η) (x : Rˣ) :
    η * ((cut η h x : R) - 1) = (cut η h x : R) - 1 := by
  rw [cut_val]
  linear_combination ((x : R) - 1) * h

theorem mul_eq_of_orth {R : Type} [CommRing R] {e c η x : R} (hx : η * (x - 1) = x - 1) (h4 : (e + c) * η = 0)
    (h5 : e * e = e) (h6 : e * c = 0) : e * x = e := by
  linear_combination (-e) * hx + (e * (x - 1)) * h4 - (η * (x - 1)) * (h5 + h6)

def offS (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Af D.host.F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 D.host.F) => v.adicCompletion D.host.F)
    (fun v : HeightOneSpectrum (𝓞 D.host.F) => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F)))
    cofinite fun v => if v ∈ S then (0 : v.adicCompletionIntegers D.host.F) else 1

theorem evalV_offS (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : HeightOneSpectrum (𝓞 D.host.F)) :
    evalV D.host.F w (offS D S) = if w ∈ S then 0 else 1 := by
  change (((if w ∈ S then (0 : w.adicCompletionIntegers D.host.F) else 1 : w.adicCompletionIntegers D.host.F)) :
    w.adicCompletion D.host.F) = _
  split_ifs <;> rfl

theorem tendsto_offS : Tendsto (offS D) atTop (𝓝 0) := by
  have h1 : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) => fun v : HeightOneSpectrum (𝓞 D.host.F) =>
      if v ∈ S then (0 : v.adicCompletionIntegers D.host.F) else 1) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({v} : Finset _)] with S hS
    rw [if_pos (hS (Finset.mem_singleton_self v))]
    rfl
  exact ((RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 D.host.F) => v.adicCompletion D.host.F)
    (A := fun v : HeightOneSpectrum (𝓞 D.host.F) =>
      (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F)))
    (𝓕 := cofinite)).continuous.tendsto _).comp h1

def offE (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (offS D S))

theorem offE_idem (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : offE D S * offE D S = offE D S := by
  rw [offE, ← map_mul]
  congr 1
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show offS D S * offS D S = offS D S from af_ext fun w => ?_)
  rw [map_mul, evalV_offS]
  split_ifs <;> simp

theorem offE_insert {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ S)
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    offE D S = offE D (insert v S) + algebraMap (AF D.host.F) (AE D) ε ∧
      offE D (insert v S) * algebraMap (AF D.host.F) (AE D) ε = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  constructor
  · rw [offE, offE, ← map_add]
    congr 1
    refine Prod.ext (add_zero (0 : Ainf D.host.F)).symm
      (show offS D S = offS D (insert v S) + α from af_ext fun w => ?_)
    rw [map_add, evalV_offS, evalV_offS]
    by_cases hw : w = v
    · subst hw; rw [h1]; simp [hv]
    · rw [h0 w hw]; simp [hw]
  · rw [offE, ← map_mul, ← map_zero (algebraMap (AF D.host.F) (AE D))]
    congr 1
    refine Prod.ext (mul_zero (0 : Ainf D.host.F))
      (show offS D (insert v S) * α = 0 from af_ext fun w => ?_)
    rw [map_mul, evalV_offS, map_zero]
    by_cases hw : w = v
    · subst hw; simp
    · rw [h0 w hw, mul_zero]

theorem offE_empty {y : AE D} (hy : infPart D y = 0) : offE D ∅ * y = y := by
  have h1 : offS D ∅ = 1 := af_ext fun w => by rw [evalV_offS, map_one]; simp
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_mul, hy, mul_zero]
  · rw [RingHom.map_mul, offE, h1]
    exact one_mul _

theorem tendsto_cut (x : (AE D)ˣ) : Tendsto (fun S => cut (offE D S) (offE_idem S) x) atTop (𝓝 1) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h0 : Tendsto (fun S => pairA D.host.F 0 (offS D S)) atTop (𝓝 (0 : AF D.host.F)) :=
    (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds tendsto_offS
  have h1 : ∀ y : AE D, Tendsto (fun S => 1 + offE D S * y) atTop (𝓝 1) := fun y => by
    have h2 := (h0.smul_const y).const_add 1
    rw [zero_smul, add_zero] at h2
    refine h2.congr fun S => ?_
    rw [offE, Algebra.smul_def]
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (h1 _).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (h1 _))

theorem one_mem_int : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩

theorem exists_place (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ ε, IsPlaceIdem D v ε :=
  ⟨_, singleV D.host.F v 1, rfl,
    Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) v 1,
    fun w hw => Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) hw 1⟩

theorem cut_int {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {y : AE D}
    (hy : finPart D y ∈ intAE D) : finPart D (1 + algebraMap (AF D.host.F) (AE D) ε * (y - 1)) ∈ intAE D := by
  rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
  exact add_mem one_mem_int (GlobalTheory.IdemPrime.mul_mem_int (place_int hε) (sub_mem hy one_mem_int))

theorem local_eq_one {χ : (AE D)ˣ →* Circle} (h : RealPointEmbeddings.UnramInert χ) {x : (AE D)ˣ}
    (hi : finPart D (x : AE D) ∈ intAE D) (hi' : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D)
    (hs : ∀ e, IsSplitIdem D e → e * (x : AE D) = e) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hid : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε =
      algebraMap (AF D.host.F) (AE D) ε) : χ (cut _ hid x) = 1 := by
  by_cases hsp : ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e, he, h3⟩ := hsp
    rw [cut_eq_one hid h3 x (hs e he) (hs _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA he)), map_one]
  · refine h ε ⟨⟨v, hε⟩, hsp⟩ _ (cut_supp hid x) ?_ ?_
    · rw [cut_val]; exact cut_int hε hi
    · rw [cut_inv]; exact cut_int hε hi'

theorem unram_global {χ : (AE D)ˣ →* Circle} (hχ : Continuous χ) (h : RealPointEmbeddings.UnramInert χ) :
    VacuumCharacterDeterminant.UnramInert χ := by
  intro x hinf hi hi' hs
  have key : ∀ S, χ (cut (offE D S) (offE_idem S) x) = χ x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [cut_eq_self _ x (offE_empty (by rw [RingHom.map_sub, hinf, RingHom.map_one, sub_self]))]
    | insert v S hv ih =>
      obtain ⟨ε, hε⟩ := exists_place v
      have hid : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε =
          algebraMap (AF D.host.F) (AE D) ε := by rw [← map_mul, place_idem hε]
      obtain ⟨e1, e2⟩ := offE_insert hv hε
      rw [← ih, cut_add (offE_idem S) (offE_idem _) hid e1 e2, map_mul, local_eq_one h hi hi' hs hε hid, mul_one]
  have h1 := (hχ.tendsto 1).comp (tendsto_cut x)
  rw [map_one] at h1
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun S => (key S).symm) h1

theorem unram_local {χ : (AE D)ˣ →* Circle} (h : VacuumCharacterDeterminant.UnramInert χ) : RealPointEmbeddings.UnramInert χ := by
  rintro ε ⟨⟨v, hε⟩, hn⟩ x hx hi hi'
  refine h x ?_ hi hi' fun e he => ?_
  · have := congrArg (infPart D) hx
    rw [RingHom.map_mul, place_inf hε, zero_mul, RingHom.map_sub, RingHom.map_one] at this
    exact (sub_eq_zero.1 this.symm)
  · obtain ⟨v', ε', hε', h3⟩ := he.2.2
    have hv : v' ≠ v := fun hv => hn ⟨e, he, by subst hv; rw [h3, place_unique hε' hε]⟩
    have h4 : (e + cA D e) * algebraMap (AF D.host.F) (AE D) ε = 0 := by
      rw [h3, ← map_mul, place_orth hε' hε hv, map_zero]
    exact mul_eq_of_orth hx h4 he.1 he.2.1

theorem unram_iff {χ : (AE D)ˣ →* Circle} (hχ : Continuous χ) : RealPointEmbeddings.UnramInert χ ↔ VacuumCharacterDeterminant.UnramInert χ :=
  ⟨unram_global hχ, unram_local⟩

end GlobalTheory.VacuumFrameCompare

end
