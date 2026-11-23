import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFibreMeasureLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensity
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneFiberMeasureBlockExtension

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.RgBase.ScalFib

section Gen

variable {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
  [LocallyCompactSpace V'] [SecondCountableTopology V'] [MeasurableSpace V'] [BorelSpace V']

theorem map_eq_of_semiconj (φ : V ≃ₜ+ V') (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V')
    [μ'.IsAddHaarMeasure] {e : V → V} {e' : V' → V'} (he : Continuous e) (he' : Continuous e')
    (h : ∀ v, φ (e v) = e' (φ v)) {c : ℝ≥0} (hc : μ'.map e' = c • μ') : μ.map e = c • μ := by
  haveI : (μ.map φ).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ φ
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, μ.map φ = t • μ' := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hφ : Measurable φ := φ.continuous.measurable
  have hφs : Measurable φ.symm := φ.symm.continuous.measurable
  have hback : ∀ ρ : Measure V, (ρ.map φ).map φ.symm = ρ := fun ρ => by
    rw [Measure.map_map hφs hφ, show (φ.symm ∘ φ : V → V) = id from funext φ.symm_apply_apply,
      Measure.map_id]
  have h1 : (μ.map e).map φ = c • μ.map φ := by
    rw [Measure.map_map hφ he.measurable, show (φ ∘ e) = e' ∘ φ from funext h,
      ← Measure.map_map he'.measurable hφ, ht, Measure.map_smul, hc, smul_comm]
  rw [← hback (μ.map e), h1, Measure.map_smul, hback]

end Gen

section Ring

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

def lmul (y : Aˣ) : A ≃ₜ+ A where
  toFun a := y * a
  invFun a := ((y⁻¹ : Aˣ) : A) * a
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := mul_add _ _ _
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

variable [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem factor_eq (κ : Measure A) [κ.IsAddHaarMeasure] (S : A ≃ₜ+ A) (x x' : Aˣ)
    (hS : ∀ a, S ((x' : A) * a) = (x : A) * S a) {a c : ℝ≥0}
    (ha : κ.map (fun y => (x : A) * y) = a • κ)
    (hc : κ.map (fun y => ((x' : A) * x) * y) = (c * c) • κ) : a = c := by
  have h1 : κ.map (fun y => (x' : A) * y) = a • κ :=
    map_eq_of_semiconj S κ κ (continuous_const.mul continuous_id)
      (continuous_const.mul continuous_id) hS ha
  have hm : ∀ z : A, Measurable fun y : A => z * y := fun z =>
    (continuous_const.mul continuous_id).measurable
  have h2 : κ.map (fun y => ((x' : A) * x) * y) = (a * a) • κ := by
    have e : (fun y : A => ((x' : A) * x) * y) = (fun y => (x' : A) * y) ∘ fun y => (x : A) * y :=
      funext fun y => mul_assoc _ _ _
    rw [e, ← Measure.map_map (hm _) (hm _), ha, Measure.map_smul, h1, smul_smul]
  have h3 : a * a = c * c :=
    GlobalTheory.CompanionTheory.SW.PiLocalization₂.nnreal_eq_of_smul_haar κ (h2.symm.trans hc)
  exact (mul_self_inj zero_le zero_le).1 h3

end Ring

theorem pi_two_map {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (lam : Measure R) [SigmaFinite lam]
    (u : R) {ρ : ℝ≥0} (h : lam.map (fun y => u * y) = ρ • lam) :
    (Measure.pi fun _ : Fin 2 => lam).map (fun p k => u * p k) =
      (ρ * ρ) • Measure.pi fun _ : Fin 2 => lam := by
  have hm : Measurable fun y : R => u * y := (continuous_const.mul continuous_id).measurable
  haveI : SigmaFinite (lam.map fun y => u * y) := by rw [h]; infer_instance
  rw [Measure.pi_map_pi (fun _ => hm.aemeasurable), h]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul]
  ring

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isUnit_of_tmul (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] (n : R)
    (hn : IsUnit (n ⊗ₜ[F] (1 : E))) : IsUnit n := by
  obtain ⟨w, hw⟩ := hn.exists_right_inv
  have h2 := hσ.2.2.1
  haveI : Module.Free R (R ⊗[F] E) := inferInstance
  have e : n ⊗ₜ[F] (1 : E) * w = n • w := by
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    simp
  have h1 := HaarCoord.half_trace_tmul (F := F) (E := E) R h2 (1 : R)
  rw [← Algebra.TensorProduct.one_def, ← hw, e, map_smul, smul_eq_mul, mul_left_comm] at h1
  exact IsUnit.of_mul_eq_one _ h1

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

theorem modulus_eq (hσ : IsCMExt F E σ) (b : Module.Basis (Fin 2) F E) (lam : Measure R)
    [lam.IsAddHaarMeasure] (x : (R ⊗[F] E)ˣ) (u : Rˣ)
    (hn : (u : R) ⊗ₜ[F] (1 : E) = sigR R σ x * x) {ρ a : ℝ≥0}
    (hρ : lam.map (fun y => (u : R) * y) = ρ • lam)
    (ha : (coordK R b lam).map (fun y => (x : R ⊗[F] E) * y) = a • coordK R b lam) : a = ρ := by
  obtain ⟨iTR, iLC, iSC, iT2, hsc, -, hrep, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hinv, -⟩ := HaarCoord.conj_facts hσ
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R 2 b lam inferInstance
  haveI := hK
  let S : (R ⊗[F] E) ≃ₜ+ (R ⊗[F] E) :=
    { toFun := sigR R σ
      invFun := sigR R σ
      left_inv := HaarCoord.sigR_sigR R hinv
      right_inv := HaarCoord.sigR_sigR R hinv
      map_add' := map_add _
      continuous_toFun := hsc
      continuous_invFun := hsc }
  let x' : (R ⊗[F] E)ˣ := Units.map (sigR R σ : R ⊗[F] E →* R ⊗[F] E) x
  have hx' : (x' : R ⊗[F] E) = sigR R σ x := rfl
  have hS : ∀ a, S ((x' : R ⊗[F] E) * a) = (x : R ⊗[F] E) * S a := fun a => by
    show sigR R σ ((x' : R ⊗[F] E) * a) = (x : R ⊗[F] E) * sigR R σ a
    rw [map_mul, hx', HaarCoord.sigR_sigR R hinv]
  refine factor_eq (coordK R b lam) S x x' hS ha ?_
  rw [hx', ← hn]
  let B := Algebra.TensorProduct.basis R b
  let h0 := (hrep 2 b).homeomorph
  let φ : (R ⊗[F] E) ≃ₜ+ (Fin 2 → R) :=
    { toFun := h0
      invFun := h0.symm
      left_inv := h0.symm_apply_apply
      right_inv := h0.apply_symm_apply
      map_add' := fun y z => by
        funext k
        show B.repr (y + z) k = B.repr y k + B.repr z k
        simp
      continuous_toFun := h0.continuous
      continuous_invFun := h0.symm.continuous }
  refine map_eq_of_semiconj φ _ (Measure.pi fun _ : Fin 2 => lam)
    (continuous_const.mul continuous_id)
    (continuous_pi fun k => continuous_const.mul (continuous_apply k)) (fun y => ?_)
    (pi_two_map lam (u : R) hρ)
  funext k
  show B.repr ((u : R) ⊗ₜ[F] (1 : E) * y) k = (u : R) * B.repr y k
  have e : (u : R) ⊗ₜ[F] (1 : E) * y = (u : R) • y := by
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    simp
  rw [e, map_smul]
  simp

theorem herm_modulus (hσ : IsCMExt F E σ) (lam : Measure R) [lam.IsAddHaarMeasure]
    (ν : Measure (HermR R σ 1)) [ν.IsAddHaarMeasure] (l : R) {ρ : ℝ≥0}
    (hρ : lam.map (fun y => l * y) = ρ • lam) :
    ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l) = ρ • ν := by
  obtain ⟨iTR, iLC, iSC, iT2, -, htr, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := iTR
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R 1
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  let φ : HermR R σ 1 ≃ₜ+ R :=
    { toFun := GlobalTheory.CompanionTheory.SW.ArchFibre.qR R σ
      invFun := hermScal R σ
      left_inv := GlobalTheory.CompanionTheory.SW.ArchFibre.hermScal_qR R hσ
      right_inv := GlobalTheory.CompanionTheory.SW.ArchFibre.qR_hermScal R hσ
      map_add' := fun S T => by
        simp [GlobalTheory.CompanionTheory.SW.ArchFibre.qR, mul_add]
      continuous_toFun := GlobalTheory.CompanionTheory.SW.ArchFibre.continuous_qR R htr
      continuous_invFun := GlobalTheory.CompanionTheory.SW.ArchFibre.continuous_hermScal R }
  have hc : Continuous (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (n := 1) l) :=
    Continuous.subtype_mk ((continuous_const_smul _).comp continuous_subtype_val) _
  refine map_eq_of_semiconj φ ν lam hc (continuous_const.mul continuous_id) (fun S => ?_) hρ
  show GlobalTheory.CompanionTheory.SW.ArchFibre.qR R σ _ = l * GlobalTheory.CompanionTheory.SW.ArchFibre.qR R σ S
  obtain ⟨r, rfl⟩ : ∃ r, hermScal R σ r = S := ⟨_, GlobalTheory.CompanionTheory.SW.ArchFibre.hermScal_qR R hσ S⟩
  rw [GlobalTheory.CompanionTheory.SW.MassSimil.scalH_hermScal, GlobalTheory.CompanionTheory.SW.ArchFibre.qR_hermScal R hσ,
    GlobalTheory.CompanionTheory.SW.ArchFibre.qR_hermScal R hσ]

def gl1 {A : Type} [CommRing A] (x : Aˣ) : GL (Fin 1) A :=
  Units.map (Matrix.scalar (Fin 1) : A →+* Matrix (Fin 1) (Fin 1) A).toMonoidHom x

theorem gl1_apply {A : Type} [CommRing A] (x : Aˣ) (i j : Fin 1) :
    (gl1 x : Matrix (Fin 1) (Fin 1) A) i j = x := by
  obtain rfl : i = j := Subsingleton.elim _ _
  simp [gl1]

end Main

theorem scal : PositivityTheory.Rg.Base1.Scal := by
  intro F E _ _ _ _ _ σ hσ J hJ R _ _ _ _ _ hR μ ν m hμ hν hm x n s hn hs
  obtain ⟨i1, i2, i3, i4, -⟩ := id hR
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  haveI := iB 1 1
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R 1
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  haveI := hμ
  haveI := hν
  have hnu : IsUnit n := isUnit_of_tmul hσ R n (by
    rw [hn]
    exact ((x.isUnit.map (sigR R σ))).mul x.isUnit)
  obtain ⟨u, rfl⟩ := hnu
  let lam : Measure R := Measure.addHaar
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hσ.2.2.1
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R 2 b lam inferInstance
  haveI := hK
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ≥0, lam.map (fun y => (u : R) * y) = ρ • lam := by
    haveI : (lam.map (lmul u)).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map lam (lmul u)
    exact ⟨_, Measure.isAddLeftInvariant_eq_smul (lam.map (lmul u)) lam⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, (coordK R b lam).map (fun y => (x : R ⊗[F] E) * y) = a • coordK R b lam := by
    haveI : ((coordK R b lam).map (lmul x)).IsAddHaarMeasure :=
      ContinuousAddEquiv.isAddHaarMeasure_map _ (lmul x)
    exact ⟨_, Measure.isAddLeftInvariant_eq_smul ((coordK R b lam).map (lmul x)) (coordK R b lam)⟩
  obtain rfl : a = ρ := modulus_eq R hσ b lam x u hn hρ ha
  have hscal := herm_modulus R hσ lam ν (u : R) hρ
  let φ : (Fin 1 → Fin 1 → R ⊗[F] E) ≃ₜ+ (R ⊗[F] E) :=
    { toFun := fun X => X 0 0
      invFun := fun y _ _ => y
      left_inv := fun X => by
        funext p i
        obtain rfl : p = 0 := Subsingleton.elim _ _
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rfl
      right_inv := fun y => rfl
      map_add' := fun X Y => rfl
      continuous_toFun := (continuous_apply 0).comp (continuous_apply 0)
      continuous_invFun := continuous_pi fun _ => continuous_pi fun _ => continuous_id }
  have hact : ∀ X : Fin 1 → Fin 1 → R ⊗[F] E, actTup R (gl1 x) X = fun p i => (x : R ⊗[F] E) * X p i := by
    intro X
    funext p i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [actTup, Matrix.mulVec, dotProduct, Fin.sum_univ_one, gl1_apply]
  have hactf : (actTup R (gl1 x) : (Fin 1 → Fin 1 → R ⊗[F] E) → _) = fun X p i => (x : R ⊗[F] E) * X p i :=
    funext hact
  have hcont : Continuous (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) (p : Fin 1) (i : Fin 1) => (x : R ⊗[F] E) * X p i) :=
    continuous_pi fun p => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply p))
  have hmu : μ.map (actTup R (gl1 x)) = a • μ := by
    rw [hactf]
    exact map_eq_of_semiconj φ μ (coordK R b lam) hcont (continuous_const.mul continuous_id)
      (fun X => rfl) ha
  have hal : algebraMap R (R ⊗[F] E) (u : R) = (u : R) ⊗ₜ[F] (1 : E) := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hgl : cT (sigR R σ) (gl1 x : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) * JR R J *
      (gl1 x : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = (algebraMap R (R ⊗[F] E) (u : R)) • JR R J := by
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.transpose_apply, Matrix.map_apply,
      gl1_apply, Matrix.smul_apply, smul_eq_mul, hal, hn]
    ring
  have ha0 : a ≠ 0 := by
    rintro rfl
    haveI : (lam.map (lmul u)).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map lam (lmul u)
    have h0 : lam.map (lmul u) = 0 := by
      rw [show (lmul u : R → R) = fun y => (u : R) * y from rfl, hρ, zero_smul]
    exact NeZero.ne (lam.map (lmul u)) h0
  have key := GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude F E σ hσ 1 J hJ R hR 1 μ ν m hμ hν hm (gl1 x) (u : R)
    u.isUnit hgl a a hmu hscal (hermScal R σ s)
  rw [hactf] at key
  rw [key, div_self ha0, one_smul, GlobalTheory.CompanionTheory.SW.MassSimil.scalH_hermScal]

end GlobalTheory.CompanionTheory.RgBase.ScalFib
