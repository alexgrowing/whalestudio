import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvFinSSOneNot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfComps

noncomputable section

namespace GlobalTheory.CompanionTheory.CellTop

open scoped Matrix Topology

section Mix

variable {R : Type*} [CommRing R]

theorem prod_mix {ι : Type*} (f : R) (hf : f * f = f) (s : Finset ι) (a b : ι → R) :
    ∏ i ∈ s, (f * a i + (1 - f) * b i) = f * ∏ i ∈ s, a i + (1 - f) * ∏ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, ih]
    linear_combination (a i * ∏ i ∈ s, a i - a i * ∏ i ∈ s, b i - b i * ∏ i ∈ s, a i + b i * ∏ i ∈ s, b i) * hf

theorem det_mix {n : Type*} [Fintype n] [DecidableEq n] (f : R) (hf : f * f = f) (X Y : Matrix n n R) :
    (f • X + (1 - f) • Y).det = f * X.det + (1 - f) * Y.det := by
  simp only [Matrix.det_apply', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, prod_mix f hf,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem inverse_eq {x w : R} (h : IsUnit x) (hw : x * w = 1) : Ring.inverse x = w :=
  left_inv_eq_right_inv (Ring.inverse_mul_cancel x h) hw

end Mix

theorem unit_of_basis {R A ι : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing A] [Algebra R A] [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology R A]
    [ContinuousSMul R A]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (f : R) (hf : f * f = f)
    (ho : IsOpen {a : R | IsUnit (1 - f + f * a)})
    (hi : ContinuousOn (fun a : R => Ring.inverse (1 - f + f * a)) {a : R | IsUnit (1 - f + f * a)}) :
    IsOpen {z : A | IsUnit (1 - algebraMap R A f + algebraMap R A f * z)} ∧
    ContinuousOn (fun z : A => Ring.inverse (1 - algebraMap R A f + algebraMap R A f * z))
      {z : A | IsUnit (1 - algebraMap R A f + algebraMap R A f * z)} := by
  classical
  set e := algebraMap R A f with he
  let L : A → Matrix ι ι R := fun z => Algebra.leftMulMatrix b z
  have hL : Continuous L := by
    refine continuous_matrix fun i j => ?_
    have : (fun z : A => L z i j) = (b.coord i) ∘ₗ (LinearMap.mulRight R (b j)) := by
      funext z
      simp [L, Algebra.leftMulMatrix_eq_repr_mul]
    rw [this]
    exact IsModuleTopology.continuous_of_linearMap _
  let N : A → R := fun z => (L z).det
  have hN : Continuous N := hL.matrix_det
  let y : A → A := fun z => ∑ i, ((L z).adjugate *ᵥ b.repr 1) i • b i
  have hy : Continuous y := by
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.smul ?_ continuous_const
    have : Continuous fun z => (L z).adjugate := hL.matrix_adjugate
    exact (continuous_apply i).comp (Continuous.matrix_mulVec this continuous_const)
  have hrep : ∀ z x : A, ⇑(b.repr (z * x)) = L z *ᵥ ⇑(b.repr x) := by
    intro z x
    have := LinearMap.toMatrix_mulVec_repr b b (Algebra.lmul R A z) x
    simpa [L, Algebra.leftMulMatrix_apply] using this.symm
  have hmul : ∀ z, z * y z = N z • (1 : A) := by
    intro z
    apply b.repr.injective
    apply DFunLike.coe_injective
    rw [hrep, map_smul]
    have h1 : ⇑(b.repr (y z)) = (L z).adjugate *ᵥ ⇑(b.repr 1) := by
      simp only [y]
      ext i
      rw [Module.Basis.repr_sum_self]
    rw [h1, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hLm : ∀ z w, L (z * w) = L z * L w := fun z w => map_mul (Algebra.leftMulMatrix b) z w
  have hL1 : L 1 = 1 := map_one (Algebra.leftMulMatrix b)
  let Nh : A →* R :=
    { toFun := N
      map_one' := by simp only [N, hL1, Matrix.det_one]
      map_mul' := fun z w => by simp only [N, hLm, Matrix.det_mul] }
  have hNmix : ∀ z, N (1 - e + e * z) = 1 - f + f * N z := by
    intro z
    have h1 : L (1 - e + e * z) = f • L z + (1 - f) • (1 : Matrix ι ι R) := by
      have h0 : (Algebra.leftMulMatrix b) e = f • (1 : Matrix ι ι R) := by
        rw [he, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      simp only [L, map_add, map_sub, map_one, map_mul, h0, smul_mul_assoc, one_mul, sub_smul, one_smul]
      abel
    simp only [N]
    rw [h1, det_mix f hf, Matrix.det_one]
    ring
  have hu : ∀ z, IsUnit z ↔ IsUnit (N z) := by
    intro z
    refine ⟨fun h => h.map Nh, fun h => ?_⟩
    obtain ⟨u, hu⟩ := h
    refine IsUnit.of_mul_eq_one (y z * algebraMap R A ((u⁻¹ : Rˣ) : R)) ?_
    rw [← mul_assoc, hmul, ← hu, Algebra.smul_def, mul_one, ← map_mul, Units.mul_inv, map_one]
  have hset : {z : A | IsUnit (1 - e + e * z)} = N ⁻¹' {a : R | IsUnit (1 - f + f * a)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [hu, hNmix]
  refine ⟨hset ▸ ho.preimage hN, ?_⟩
  have hc : Continuous fun z : A => 1 - e + e * z := by fun_prop
  have h2 : ContinuousOn (fun z : A => Ring.inverse (1 - f + f * N z) • y (1 - e + e * z))
      {z : A | IsUnit (1 - e + e * z)} := by
    refine ContinuousOn.smul (hi.comp hN.continuousOn ?_) (hy.comp hc).continuousOn
    intro z hz
    rw [hset] at hz
    exact hz
  refine h2.congr fun z hz => ?_
  refine inverse_eq hz ?_
  have h3 : IsUnit (1 - f + f * N z) := by
    rw [← hNmix, ← hu]; exact hz
  rw [mul_smul_comm, hmul, hNmix, smul_smul, Ring.inverse_mul_cancel _ h3, one_smul]

theorem unit_of_retract {A T : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing T] [TopologicalSpace T] (p : A →+* T) (s : T → A) (hp : Continuous p) (hs : Continuous s)
    (hadd : ∀ x y, s (x * y) = s x * s y) (hps : ∀ t, p (s t) = t) (hsp : ∀ a, s (p a) = s 1 * a)
    (ho : IsOpen {t : T | IsUnit t}) (hi : ContinuousOn (Ring.inverse : T → T) {t : T | IsUnit t}) :
    IsOpen {a : A | IsUnit (1 - s 1 + s 1 * a)} ∧
    ContinuousOn (fun a : A => Ring.inverse (1 - s 1 + s 1 * a)) {a : A | IsUnit (1 - s 1 + s 1 * a)} := by
  set f := s 1 with hfd
  have hf : f * f = f := by rw [hfd, ← hadd, one_mul]
  have hpf : p f = 1 := hps 1
  have key : ∀ (a : A) (v : T), p a * v = 1 → (1 - f + f * a) * (1 - f + s v) = 1 := by
    intro a v hv
    have h1 : f * a * s v = f := by rw [← hsp, ← hadd, hv]
    have h2 : f * s v = s v := by rw [hfd, ← hadd, one_mul]
    linear_combination h1 - h2 + (1 - a) * hf
  have hset : ∀ a, IsUnit (1 - f + f * a) ↔ IsUnit (p a) := by
    intro a
    constructor
    · intro h
      have := h.map p
      simpa [hpf] using this
    · rintro ⟨u, hu⟩
      exact IsUnit.of_mul_eq_one _ (key a ((u⁻¹ : Tˣ) : T) (by rw [← hu, Units.mul_inv]))
  have hset' : {a : A | IsUnit (1 - f + f * a)} = p ⁻¹' {t : T | IsUnit t} := by
    ext a
    exact hset a
  refine ⟨hset' ▸ ho.preimage hp, ?_⟩
  have h2 : ContinuousOn (fun a : A => 1 - f + s (Ring.inverse (p a))) {a : A | IsUnit (1 - f + f * a)} := by
    refine continuousOn_const.add (hs.comp_continuousOn (hi.comp hp.continuousOn ?_))
    intro a ha
    exact (hset a).1 ha
  refine h2.congr fun a ha => ?_
  exact inverse_eq ha (key a _ (Ring.mul_inverse_cancel _ ((hset a).1 ha)))

theorem unit_pi {ι : Type*} [Fintype ι] {K : ι → Type*} [∀ i, Field (K i)] [∀ i, TopologicalSpace (K i)]
    [∀ i, ContinuousInv₀ (K i)] [∀ i, T1Space (K i)] :
    IsOpen {x : ∀ i, K i | IsUnit x} ∧ ContinuousOn (Ring.inverse : (∀ i, K i) → ∀ i, K i) {x | IsUnit x} := by
  have hset : {x : ∀ i, K i | IsUnit x} = ⋂ i, (fun x : ∀ i, K i => x i) ⁻¹' {0}ᶜ := by
    ext x
    simp [Pi.isUnit_iff]
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact isOpen_iInter_of_finite fun i => isOpen_compl_singleton.preimage (continuous_apply i)
  · have h2 : ContinuousOn (fun x : ∀ i, K i => fun i => (x i)⁻¹) {x | IsUnit x} := by
      refine continuousOn_pi.2 fun i => ContinuousOn.inv₀ (continuous_apply i).continuousOn fun x hx => ?_
      exact (Pi.isUnit_iff.1 hx i).ne_zero
    refine h2.congr fun x hx => inverse_eq hx ?_
    funext i
    exact mul_inv_cancel₀ (Pi.isUnit_iff.1 hx i).ne_zero

theorem unit_prod {X Y : Type*} [CommRing X] [CommRing Y] [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IsOpen {x : X | IsUnit x}) (hX' : ContinuousOn (Ring.inverse : X → X) {x | IsUnit x})
    (hY : IsOpen {x : Y | IsUnit x}) (hY' : ContinuousOn (Ring.inverse : Y → Y) {x | IsUnit x}) :
    IsOpen {x : X × Y | IsUnit x} ∧ ContinuousOn (Ring.inverse : X × Y → X × Y) {x | IsUnit x} := by
  have hset : {x : X × Y | IsUnit x} = {x | IsUnit x} ×ˢ {y | IsUnit y} := by
    ext x
    simp [Prod.isUnit_iff]
  refine ⟨hset ▸ hX.prod hY, ?_⟩
  have h2 : ContinuousOn (fun x : X × Y => (Ring.inverse x.1, Ring.inverse x.2)) {x | IsUnit x} := by
    refine ContinuousOn.prodMk (hX'.comp continuousOn_fst ?_) (hY'.comp continuousOn_snd ?_)
    · exact fun x hx => (Prod.isUnit_iff.1 hx).1
    · exact fun x hx => (Prod.isUnit_iff.1 hx).2
  refine h2.congr fun x hx => inverse_eq hx ?_
  have h3 := Prod.isUnit_iff.1 hx
  exact Prod.ext (Ring.mul_inverse_cancel _ h3.1) (Ring.mul_inverse_cancel _ h3.2)

end GlobalTheory.CompanionTheory.CellTop

noncomputable section

namespace GlobalTheory.CompanionTheory.CellTop

open scoped Matrix

section MixMatrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem det_mix_one {e : R} (hee : e * e = e) (C : Matrix n n R) :
    ((1 - e) • (1 : Matrix n n R) + e • C).det = 1 - e + e * C.det := by
  rw [add_comm, det_mix e hee, Matrix.det_one]
  ring

theorem isUnit_mix_iff {e : R} (hee : e * e = e) (C : Matrix n n R) :
    IsUnit ((1 - e) • (1 : Matrix n n R) + e • C).det ↔ ∃ y : Matrix n n R, y * C = e • 1 := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by linear_combination hee
  have h2 : e * (1 - e) = 0 := by linear_combination -hee
  have h3 : (1 - e) * e = 0 := by linear_combination -hee
  constructor
  · intro hu
    have hu' : IsUnit ((1 - e) • (1 : Matrix n n R) + e • C) := (Matrix.isUnit_iff_isUnit_det _).2 hu
    obtain ⟨u, hu2⟩ := hu'
    refine ⟨e • ((u⁻¹ : (Matrix n n R)ˣ) : Matrix n n R), ?_⟩
    have h4 : e • ((1 - e) • (1 : Matrix n n R) + e • C) = e • C := by
      rw [smul_add, smul_smul, smul_smul, h2, hee, zero_smul, zero_add]
    rw [smul_mul_assoc, ← mul_smul_comm, ← h4, ← hu2, mul_smul_comm, Units.inv_mul]
  · rintro ⟨y, hy⟩
    have h5 : (e • y + (1 - e) • (1 : Matrix n n R)) * ((1 - e) • (1 : Matrix n n R) + e • C) = 1 := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, hy,
        h1, h2, h3, hee, zero_smul, add_zero, zero_add, smul_add]
      rw [← add_smul]
      simp
    exact (Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ (mul_eq_one_comm.1 h5))

theorem mix_solve {e : R} (hee : e * e = e) {C d x : Matrix n n R} (hu : IsUnit (1 - e + e * C.det))
    (hx : e • x = x) (hB : C * x = e • d) :
    Ring.inverse (1 - e + e * C.det) • (((1 - e) • (1 : Matrix n n R) + e • C).adjugate * (e • d)) = x := by
  have h1 : ((1 - e) • (1 : Matrix n n R) + e • C) * x = e • d := by
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hB, smul_smul, hee, sub_smul, one_smul, hx, sub_self,
      zero_add]
  rw [← h1, ← mul_assoc, Matrix.adjugate_mul, det_mix_one hee, smul_mul_assoc, one_mul, smul_smul,
    Ring.inverse_mul_cancel _ hu, one_smul]

end MixMatrix

end GlobalTheory.CompanionTheory.CellTop

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellTop

open GlobalTheory.CompanionTheory.SPartTensor

section Adelic

variable {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem continuous_pS : Continuous (pS S) :=
  continuous_fst.prodMk (continuous_pi fun v => (RestrictedProduct.continuous_eval v.1).comp continuous_snd)

theorem continuous_sS : Continuous (sS S) :=
  continuous_fst.prodMk (continuous_finsetSum _ fun v _ =>
    (continuous_singleFin v.1).comp ((continuous_apply v).comp continuous_snd))

theorem unit_RS : IsOpen {t : RS S | IsUnit t} ∧ ContinuousOn (Ring.inverse : RS S → RS S) {t | IsUnit t} := by
  have h1 := unit_pi (K := fun v : InfinitePlace F => v.Completion)
  have h2 := unit_pi (K := fun v : S => Fv F v.1)
  exact unit_prod h1.1 h1.2 h2.1 h2.2

theorem unit_AF : IsOpen {a : AF F | IsUnit (1 - sS S 1 + sS S 1 * a)} ∧
    ContinuousOn (fun a : AF F => Ring.inverse (1 - sS S 1 + sS S 1 * a)) {a : AF F | IsUnit (1 - sS S 1 + sS S 1 * a)} :=
  unit_of_retract (pS S : AF F →+* RS S) (sS S) (continuous_pS S) (continuous_sS S) sS_mul pS_sS sS_pS
    (unit_RS S).1 (unit_RS S).2

end Adelic

end GlobalTheory.CompanionTheory.CellTop

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellTop

open GlobalTheory.CompanionTheory.SPartTensor

variable {D : D7} {p : ℕ}

theorem idem_eq {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) (sS S 1) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D _ (fun w => ?_) (fun v => ?_)
  · rw [RingHom.map_sub, he.1 w, sub_eq_zero]
    change (1 : _) = evInf D.host.F w (sS S 1) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [evInf_sS_one]; rfl
  · rw [RingHom.map_sub, he.2 v, sub_eq_zero]
    change _ = evFin D.host.F v (sS S 1) ⊗ₜ[D.host.F] (1 : D.host.E)
    by_cases h : v ∈ S
    · rw [if_pos h, evFin_sS_one_mem h]; rfl
    · rw [if_neg h, evFin_sS_one_not h, TensorProduct.zero_tmul]

theorem unit_AE {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) :
    IsOpen {z : AE D | IsUnit (1 - e + e * z)} ∧
    ContinuousOn (fun z : AE D => Ring.inverse (1 - e + e * z)) {z : AE D | IsUnit (1 - e + e * z)} := by
  have : IsTopologicalRing (AE D) := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : ContinuousSMul (AF D.host.F) (AE D) := ModuleTopology.continuousSMul _ _
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hf : sS S (1 : RS S) * sS S 1 = sS S 1 := by rw [← sS_mul, one_mul]
  have h := unit_of_basis (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E))
    (sS S 1) hf (unit_AF S).1 (unit_AF S).2
  rw [← idem_eq he] at h
  exact h

end GlobalTheory.CompanionTheory.CellTop
