import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf

namespace GlobalTheory.PullbackComparison

theorem weil_pi {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)]
    [∀ i, MeasurableMul₂ (G i)] (μG μS ν : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μG i)]
    [∀ i, SigmaFinite (μS i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i (f : G i → ℝ≥0∞), Measurable f → ∫⁻ x, f x ∂μG i = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS i ∂ν i)
    (f : (∀ i, G i) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂Measure.pi μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂Measure.pi μS ∂Measure.pi ν := by
  set m : (∀ i, G i) × (∀ i, G i) → (∀ i, G i) := fun p => p.2 * p.1 with hm
  have hmm : Measurable m := measurable_snd.mul measurable_fst
  have key : Measure.pi μG = ((Measure.pi ν).prod (Measure.pi μS)).map m := by
    refine Measure.pi_eq fun s hs => ?_
    have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
    rw [Measure.map_apply hmm hbox, Measure.prod_apply (hmm hbox)]
    have e1 : ∀ x : ∀ i, G i, (Measure.pi μS) (Prod.mk x ⁻¹' (m ⁻¹' Set.univ.pi s)) =
        ∏ i, μS i ((fun a => a * x i) ⁻¹' s i) := by
      intro x
      have : Prod.mk x ⁻¹' (m ⁻¹' Set.univ.pi s) = Set.univ.pi (fun i => (fun a => a * x i) ⁻¹' s i) := by
        ext y; simp [m, Set.mem_pi, Pi.mul_apply]
      rw [this, Measure.pi_pi]
    simp_rw [e1]
    rw [Formalism.L2.SG.Pf.Carrier.JointQuot.lintegral_fintype_prod (μ := ν)
      (fun i y => μS i ((fun a => a * y) ⁻¹' s i))
      (fun i => measurable_measure_prodMk_right (measurable_mul (hs i)))]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := h i ((s i).indicator 1) (measurable_one.indicator (hs i))
    rw [lintegral_indicator_one (hs i)] at this
    rw [this]
    refine lintegral_congr fun x => ?_
    rw [← lintegral_indicator_one ((hs i).preimage (measurable_mul_const x))]
    congr 1
  rw [key, lintegral_map hf hmm, lintegral_prod (fun z => f (m z)) (hf.comp hmm).aemeasurable]

end GlobalTheory.PullbackComparison

namespace GlobalTheory.PullbackComparison

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

def eM (τ : D.what₂.Tau) : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ)

theorem eM_emb (τ : D.what₂.Tau) : MeasurableEmbedding (eM C τ) :=
  (Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (Formalism.L2.SG.Pf.Choice.n_eq' X) (X.B.I.ε (vOf X τ)) (C.isT τ).2.1).measurableEmbedding

theorem eM_mul (τ : D.what₂.Tau) (a b : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    eM C τ (a * b) = Matrix.of.symm (Matrix.of (eM C τ a) * Matrix.of (eM C τ b)) := by
  have h2 := (C.isT τ).2.1
  show Matrix.of.symm (C.Qi τ * uMat (a * b) * C.Q τ) =
    Matrix.of.symm (Matrix.of (Matrix.of.symm (C.Qi τ * uMat a * C.Q τ)) *
      Matrix.of (Matrix.of.symm (C.Qi τ * uMat b * C.Q τ)))
  simp only [Equiv.apply_symm_apply]
  rw [show uMat (a * b) = uMat a * uMat b from rfl]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), h2, Matrix.one_mul]

theorem eM_one (τ : D.what₂.Tau) : Matrix.of (eM C τ 1) = 1 := by
  show C.Qi τ * uMat (1 : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) * C.Q τ = 1
  rw [show uMat (1 : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) = 1 from rfl, Matrix.mul_one]
  exact (C.isT τ).1

theorem eM_inv (τ : D.what₂.Tau) (a : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (Matrix.of (eM C τ a))⁻¹ = Matrix.of (eM C τ a⁻¹) := by
  apply Matrix.inv_eq_right_inv
  have := eM_mul C τ a a⁻¹
  rw [mul_inv_cancel] at this
  rw [← eM_one C τ, this]
  rfl

theorem eM_lmul (τ : D.what₂.Tau) (s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    eM C τ ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) s) ∘ eM C τ := by
  funext γ
  show eM C τ (s * γ) = _
  rw [eM_mul]
  rfl

theorem uh_range (τ : D.what₂.Tau) {x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : x ∈ Set.range (eM C τ) := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hxU' : (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of x = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hx
  have hQiH := Formalism.L2.SG.Pf.Choice.qiHqi (X.B.I.ε (vOf X τ)) h2 hg
  have hγ : (C.Q τ * Matrix.of x * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * Matrix.of x * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    calc (C.Q τ * Matrix.of x * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * Matrix.of x * C.Qi τ)
        = (C.Qi τ)ᴴ * ((Matrix.of x)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * Matrix.of x) *
            C.Qi τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hxU', hQiH]
  refine ⟨Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * Matrix.of x * C.Qi τ) hγ, ?_⟩
  show Matrix.of.symm (C.Qi τ * (C.Q τ * Matrix.of x * C.Qi τ) * C.Q τ) = x
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
  rfl

theorem nDict (u : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (eM C τ γ) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ↔ γ ∈ Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ) := by
  obtain ⟨h1, h2, hgQ, hcol⟩ := C.isT τ
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 := fun a => pow_ne_zero _ (Formalism.L2.SG.Pf.Choice.frS_ne D)
  have hzB := (Formalism.L2.SG.Pf.zTr C u τ).1
  constructor
  · intro hm
    have := Formalism.L2.SG.Pf.EquivPf.inN_loc (Formalism.L2.SG.Pf.Choice.n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) hzB hm
    show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat γ)
    have e : C.Q τ * Matrix.of (eM C τ γ) * C.Qi τ = uMat γ := by
      show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [← e]; exact this
  · intro hN
    exact Formalism.L2.SG.Pf.EquivPf.nset_loc (Formalism.L2.SG.Pf.Choice.n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) γ.2 hN

end GlobalTheory.PullbackComparison

namespace GlobalTheory.PullbackComparison

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Smap

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem umat_mul' (τ : D.what₂.Tau) (a b : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : umat (a * b) = umat a * umat b := rfl

def cY (τ : D.what₂.Tau) : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) :=
  Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * C.y τ * C.Qi τ) (Formalism.L2.SG.Pf.LocJEq.y_facts C τ).2.1

theorem eM_eq_smap (τ : D.what₂.Tau) (γ g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    eM C τ g = Formalism.L2.SG.Pf.LocJEq.Smap C τ γ (γ * g * cY C τ) := by
  apply Matrix.of.injective
  rw [Formalism.L2.SG.Pf.LocJEq.smap_val, ← umat_mul', show γ⁻¹ * (γ * g * cY C τ) = g * cY C τ by group, umat_mul']
  show C.Qi τ * uMat g * C.Q τ = C.Qi τ * (umat g * (C.Q τ * C.y τ * C.Qi τ)) * C.Q τ * (C.y τ)⁻¹
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Qi τ) (C.Q τ), h1, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ (Formalism.L2.SG.Pf.LocJEq.unit_det_y C τ), Matrix.mul_one]

theorem eM_smap (τ : D.what₂.Tau) (γ w z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (eM C τ w) * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z) =
      Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ (γ * w * γ⁻¹ * z)) := by
  have hu : umat γ⁻¹ * umat (γ * w * γ⁻¹ * z) = umat w * (umat γ⁻¹ * umat z) := by
    simp only [← umat_mul']
    congr 1
    group
  rw [Formalism.L2.SG.Pf.LocJEq.smap_val, Formalism.L2.SG.Pf.LocJEq.smap_val, hu]
  show C.Qi τ * uMat w * C.Q τ * (C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹) =
    C.Qi τ * (umat w * (umat γ⁻¹ * umat z)) * C.Q τ * (C.y τ)⁻¹
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), h2, Matrix.one_mul]

theorem range_eM_sub (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Set.range (eM C τ) ⊆ Set.range (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ) := by
  rintro _ ⟨g, rfl⟩
  exact ⟨_, (eM_eq_smap C τ γ g).symm⟩

end Smap

section Rs

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

theorem rset_loc {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (x : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix.of (eM C τ (x (vOf X τ))) ∈ Rset D.R.k D.R.rS (GlobalTheory.TypeAsm.gamT C t τ)⁻¹ ↔
      (x (vOf X τ) ∈ Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ) ∧
        (t.pt.1⁻¹ * x * t.pt.1) (vOf X τ) ∈ Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) := by
  have hg : GlobalTheory.TypeAsm.gamT C t τ = Matrix.of (eM C τ (t.pt.1 (vOf X τ))) := rfl
  have hc : (GlobalTheory.TypeAsm.gamT C t τ)⁻¹ * Matrix.of (eM C τ (x (vOf X τ))) * ((GlobalTheory.TypeAsm.gamT C t τ)⁻¹)⁻¹ =
      Matrix.of (eM C τ ((t.pt.1⁻¹ * x * t.pt.1) (vOf X τ))) := by
    rw [hg, eM_inv, eM_inv, inv_inv]
    show _ = Matrix.of (eM C τ ((t.pt.1 (vOf X τ))⁻¹ * x (vOf X τ) * t.pt.1 (vOf X τ)))
    rw [eM_mul, eM_mul]
    rfl
  show (_ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ _ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) ↔ _
  rw [hc, nDict C u, nDict C u]

theorem rset_iff {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (x : X.B.I.Ginf) :
    x ∈ Formalism.L2.SG.TermOp.Vanish.Rset t ↔
      ∀ τ, Matrix.of (eM C τ (x (vOf X τ))) ∈ Rset D.R.k D.R.rS (GlobalTheory.TypeAsm.gamT C t τ)⁻¹ := by
  simp only [rset_loc C t x]
  have e : x ∈ Formalism.L2.SG.TermOp.Vanish.Rset t ↔ ∀ v, x v ∈ Formalism.L2.SG.Pf.WuDec.Nloc X u v ∧
      (t.pt.1⁻¹ * x * t.pt.1) v ∈ Formalism.L2.SG.Pf.WuDec.Nloc X u v :=
    ⟨fun h v => ⟨h.1 v, h.2 v⟩, fun h => ⟨fun v => (h v).1, fun v => (h v).2⟩⟩
  rw [e]
  exact X.pl.forall_congr_left (p := fun v => x v ∈ Formalism.L2.SG.Pf.WuDec.Nloc X u v ∧
      (t.pt.1⁻¹ * x * t.pt.1) v ∈ Formalism.L2.SG.Pf.WuDec.Nloc X u v)

end Rs

end GlobalTheory.PullbackComparison

namespace GlobalTheory.PullbackComparison

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Place

variable {D : D7} {X : HidaSetting D} (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u)
  (τ : D.what₂.Tau)

theorem map_muL {μτ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hH : IsHaarOn (Rset D.R.k D.R.rS (GlobalTheory.TypeAsm.gamT C t τ)⁻¹) μτ) :
    (μτ.comap (eM C τ)).map (eM C τ) = μτ := by
  rw [(eM_emb C τ).map_comap, Measure.restrict_eq_self_of_ae_mem]
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hH.2.2.1
  intro hR
  exact hx (uh_range C τ hR.1.1)

theorem sf_muL {μτ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hH : IsHaarOn (Rset D.R.k D.R.rS (GlobalTheory.TypeAsm.gamT C t τ)⁻¹) μτ) : SigmaFinite (μτ.comap (eM C τ)) := by
  haveI := hH.1
  exact SigmaFinite.of_map _ (eM_emb C τ).measurable.aemeasurable (by rw [map_muL C t τ hH]; infer_instance)

theorem map_nuL {ντ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hC : ντ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0) :
    (ντ.comap (Formalism.L2.SG.Pf.LocJEq.Smap C τ (t.pt.1 (vOf X τ)))).map
      (Formalism.L2.SG.Pf.LocJEq.Smap C τ (t.pt.1 (vOf X τ))) = ντ := by
  rw [(Formalism.L2.SG.Pf.LocJEq.smap_measEmb C τ _).map_comap, Measure.restrict_eq_self_of_ae_mem]
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hC
  intro hU
  exact hx (range_eM_sub C τ _ (uh_range C τ hU))

theorem sf_nuL {ντ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)} [SigmaFinite ντ]
    (hC : ντ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0) :
    SigmaFinite (ντ.comap (Formalism.L2.SG.Pf.LocJEq.Smap C τ (t.pt.1 (vOf X τ)))) :=
  SigmaFinite.of_map _ (Formalism.L2.SG.Pf.LocJEq.smap_measEmb C τ _).measurable.aemeasurable
    (by rw [map_nuL C t τ hC]; infer_instance)

theorem inv_muL {μτ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hH : IsHaarOn (Rset D.R.k D.R.rS (GlobalTheory.TypeAsm.gamT C t τ)⁻¹) μτ) (a : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ha : Matrix.of (eM C τ a) ∈ Rset D.R.k D.R.rS (GlobalTheory.TypeAsm.gamT C t τ)⁻¹) :
    (μτ.comap (eM C τ)).map (fun x => a * x) = μτ.comap (eM C τ) := by
  have he := eM_emb C τ
  rw [← he.comap_map ((μτ.comap (eM C τ)).map (fun x => a * x)),
    Measure.map_map he.measurable (measurable_const_mul a), eM_lmul,
    ← Measure.map_map (Formalism.L2.SG.Pf.WFL.measurable_lmulM _) he.measurable, map_muL C t τ hH, hH.2.2.2 (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) a) ha]

theorem conjM_meas (k r : ℕ) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (Formalism.QuantumDeterminants.conjM (k := k) (r := r) a) := by
  have hof : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    continuous_id
  have hos : Continuous fun x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => (Matrix.of.symm x : Formalism.QuantumDeterminants.Mt k r) :=
    continuous_id
  have hc : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm (a * Matrix.of x * a⁻¹) : Formalism.QuantumDeterminants.Mt k r) :=
    hos.comp ((continuous_const.matrix_mul hof).matrix_mul continuous_const)
  exact hc.measurable

end Place

end GlobalTheory.PullbackComparison

namespace GlobalTheory.PullbackComparison

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Weil

variable {D : D7} {X : HidaSetting D} (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u)
  (τ : D.what₂.Tau)

theorem weil_loc {μτ ντ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (hH : IsHaarOn (Rset D.R.k D.R.rS (GlobalTheory.TypeAsm.gamT C t τ)⁻¹) μτ)
    (hC : ντ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (hQ : IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μτ.map (Formalism.QuantumDeterminants.conjM (GlobalTheory.TypeAsm.gamT C t τ)⁻¹)) ντ)
    (f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
      ∫⁻ z, ∫⁻ a, f (a * z) ∂(μτ.comap (eM C τ))
        ∂(ντ.comap (Formalism.L2.SG.Pf.LocJEq.Smap C τ (t.pt.1 (vOf X τ)))) := by
  set γ := t.pt.1 (vOf X τ) with hγ
  set S := Formalism.L2.SG.Pf.LocJEq.Smap C τ γ with hSdef
  have hS : MeasurableEmbedding S := Formalism.L2.SG.Pf.LocJEq.smap_measEmb C τ γ
  have he := eM_emb C τ
  set F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞ := Function.extend S f 0 with hFdef
  have hFm : Measurable F := hS.measurable_extend hf measurable_const
  have hFS : ∀ z, F (S z) = f z := fun z => hS.injective.extend_apply f 0 z
  have h1 : ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ x, F x ∂(muGB X (C.Q τ) (C.Qi τ) τ) := by
    have hG : muGB X (C.Q τ) (C.Qi τ) τ = (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (eM C τ) := rfl
    rw [hG, he.lintegral_map]
    have e1 : ∀ g, F (eM C τ g) = f (γ * g * cY C τ) := fun g => by rw [eM_eq_smap C τ γ g, hFS]
    simp_rw [e1]
    rw [lintegral_mul_left_eq_self (fun g => f (g * cY C τ)) γ, lintegral_mul_right_eq_self f (cY C τ)]
  rw [h1, hQ F hFm]
  conv_lhs => rw [← map_nuL C t τ hC]
  rw [hS.lintegral_map]
  refine lintegral_congr fun z => ?_
  have hin : Measurable fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      F (fun i j => (Matrix.of s * Matrix.of (S z)) i j) :=
    hFm.comp ((Formalism.L2.SG.Pf.Choice.measurable_mulF (k := D.R.k) (r := D.R.rS)).comp
      (measurable_id.prodMk measurable_const))
  rw [lintegral_map hin (conjM_meas D.R.k D.R.rS _)]
  conv_lhs => rw [← map_muL C t τ hH]
  rw [he.lintegral_map]
  refine lintegral_congr fun a => ?_
  have hg : GlobalTheory.TypeAsm.gamT C t τ = Matrix.of (eM C τ γ) := rfl
  have e1 : Matrix.of (Formalism.QuantumDeterminants.conjM (GlobalTheory.TypeAsm.gamT C t τ)⁻¹ (eM C τ a)) = Matrix.of (eM C τ (γ⁻¹ * a * γ)) := by
    show (GlobalTheory.TypeAsm.gamT C t τ)⁻¹ * Matrix.of (eM C τ a) * ((GlobalTheory.TypeAsm.gamT C t τ)⁻¹)⁻¹ = _
    rw [hg, eM_inv, eM_inv, inv_inv, eM_mul, eM_mul]
    rfl
  have e2 : (fun i j => (Matrix.of (Formalism.QuantumDeterminants.conjM (GlobalTheory.TypeAsm.gamT C t τ)⁻¹ (eM C τ a)) * Matrix.of (S z)) i j :
      Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) = S (a * z) := by
    rw [e1, eM_smap, show γ * (γ⁻¹ * a * γ) * γ⁻¹ * z = a * z by group]
    rfl
  rw [e2, hFS]

end Weil

end GlobalTheory.PullbackComparison

namespace GlobalTheory.PullbackComparison

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pullC_holds : GlobalTheory.TypeAsm.PullC := by
  intro D X Y u C t μ ν h
  have hH : ∀ τ, IsHaarOn (Rset D.R.k D.R.rS (GlobalTheory.TypeAsm.gamT C t τ)⁻¹) (μ τ) := fun τ => (h τ).2.1
  have hC : ∀ τ, ν τ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 := fun τ => (h τ).2.2.2.1
  have hQ := fun τ => (h τ).2.2.2.2
  haveI : ∀ τ, SigmaFinite (μ τ) := fun τ => (h τ).1
  haveI : ∀ τ, SigmaFinite (ν τ) := fun τ => (h τ).2.2.1
  set μl : ∀ τ : D.what₂.Tau, Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) := fun τ => (μ τ).comap (eM C τ) with hμl
  set νl' : ∀ τ : D.what₂.Tau, Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :=
    fun τ => (ν τ).comap (Formalism.L2.SG.Pf.LocJEq.Smap C τ (t.pt.1 (vOf X τ))) with hνl'
  haveI : ∀ τ, SigmaFinite (μl τ) := fun τ => sf_muL C t τ (hH τ)
  haveI : ∀ τ, SigmaFinite (νl' τ) := fun τ => sf_nuL C t τ (hC τ)
  have hmap : ∀ τ, (μl τ).map (eM C τ) = μ τ := fun τ => map_muL C t τ (hH τ)
  set Rq : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) ≃ᵐ X.B.I.Ginf :=
    MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm with hRq
  have hRq_apply : ∀ p τ, Rq p (vOf X τ) = p τ := fun p τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hRq_symm : ∀ x τ, Rq.symm x τ = x (vOf X τ) := by
    intro x τ
    have := hRq_apply (Rq.symm x) τ
    rw [Rq.apply_symm_apply] at this
    exact this.symm
  have hRq_mul : ∀ p q, Rq (p * q) = Rq p * Rq q := by
    intro p q
    funext v
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    show Rq (p * q) (vOf X τ) = Rq p (vOf X τ) * Rq q (vOf X τ)
    rw [hRq_apply, hRq_apply, hRq_apply]
    rfl
  set νl : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
    Equiv.piCongrLeft (fun v => Measure (Formalism.REAL.UJ (X.B.I.ε v))) X.pl.symm νl' with hνldef
  have hνl : ∀ τ, νl (vOf X τ) = νl' τ := fun τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hsνl : ∀ v, SigmaFinite (νl v) := by
    intro v
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    have := (inferInstance : SigmaFinite (νl' τ))
    rw [← hνl τ] at this
    exact this
  have hpiν : Measure.pi νl = (Measure.pi νl').map Rq := by
    rw [← (measurePreserving_piCongrLeft νl X.pl.symm).map_eq]
    congr 2
    funext τ
    exact hνl τ
  have hpiG : Formalism.L2.SG.ProjRows.muInf X.B.I =
      (Measure.pi fun τ : D.what₂.Tau => Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map Rq :=
    ((measurePreserving_piCongrLeft (fun v => Formalism.REAL.muG (X.B.I.ε v)) X.pl.symm).map_eq).symm
  set E : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) → D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun p τ => eM C τ (p τ) with hEdef
  have hE : MeasurableEmbedding E := by
    refine MeasurableEmbedding.of_measurable_inverse
      (g := fun y τ => Function.extend (eM C τ) id (fun _ => (1 : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) (y τ))
      (measurable_pi_lambda _ fun τ => (eM_emb C τ).measurable.comp (measurable_pi_apply τ)) ?_
      (measurable_pi_lambda _ fun τ =>
        ((eM_emb C τ).measurable_extend measurable_id measurable_const).comp (measurable_pi_apply τ)) ?_
    · have : Set.range E = Set.univ.pi fun τ => Set.range (eM C τ) := by
        ext y
        simp only [Set.mem_range, Set.mem_pi, Set.mem_univ, true_implies]
        constructor
        · rintro ⟨p, rfl⟩ τ
          exact ⟨p τ, rfl⟩
        · intro hy
          choose p hp using hy
          exact ⟨p, funext hp⟩
      rw [this]
      exact MeasurableSet.univ_pi fun τ => (eM_emb C τ).measurableSet_range
    · intro p
      funext τ
      exact (eM_emb C τ).injective.extend_apply id _ (p τ)
  have hpiμ : Measure.pi μ = (Measure.pi μl).map E := by
    haveI : ∀ τ, SigmaFinite ((μl τ).map (eM C τ)) := fun τ => by rw [hmap τ]; infer_instance
    rw [Measure.pi_map_pi (μ := μl) (f := fun τ => eM C τ) (fun τ => (eM_emb C τ).measurable.aemeasurable)]
    congr 1
    funext τ
    exact (hmap τ).symm
  refine ⟨(Measure.pi μl).map Rq, νl, hsνl, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Rq.sigmaFinite_map
  · intro h0
    have h1 : Measure.pi μl = 0 := (Measure.map_eq_zero_iff Rq.measurable.aemeasurable).1 h0
    have h2 : Measure.pi μl Set.univ = 0 := by rw [h1]; rfl
    rw [Measure.pi_univ, Finset.prod_eq_zero_iff] at h2
    obtain ⟨τ, -, hτ⟩ := h2
    rw [Measure.measure_univ_eq_zero] at hτ
    apply (hH τ).2.1
    rw [← hmap τ, hτ, Measure.map_zero]
  · rw [Rq.map_apply]
    refine measure_mono_null (t := ⋃ τ, Function.eval τ ⁻¹'
      {a : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) | Matrix.of (eM C τ a) ∉ Rset D.R.k D.R.rS (GlobalTheory.TypeAsm.gamT C t τ)⁻¹}) ?_
      (measure_iUnion_null fun τ => Measure.pi_eval_preimage_null _ ?_)
    · intro p hp
      have hp' : Rq p ∉ Formalism.L2.SG.TermOp.Vanish.Rset t := hp
      rw [rset_iff C t] at hp'
      push_neg at hp'
      obtain ⟨τ, hτ⟩ := hp'
      rw [hRq_apply] at hτ
      exact Set.mem_iUnion.2 ⟨τ, hτ⟩
    · show ((μ τ).comap (eM C τ)) _ = 0
      rw [(eM_emb C τ).comap_apply]
      refine measure_mono_null ?_ (hH τ).2.2.1
      rintro _ ⟨a, ha, rfl⟩
      exact ha
  · intro s hs
    have hinvs : ∀ τ, (μl τ).map (fun a => Rq.symm s τ * a) = μl τ := by
      intro τ
      refine inv_muL C t τ (hH τ) _ ?_
      rw [hRq_symm]
      exact (rset_iff C t s).1 hs τ
    haveI : ∀ τ, SigmaFinite ((μl τ).map (fun a => Rq.symm s τ * a)) := fun τ => by rw [hinvs τ]; infer_instance
    have hpm := Measure.pi_map_pi (μ := μl) (f := fun τ a => Rq.symm s τ * a)
      (fun τ => (measurable_const_mul _).aemeasurable)
    have hcomp : (fun x => s * x) ∘ Rq = Rq ∘ (fun (p : ∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
        (i : D.what₂.Tau) => Rq.symm s i * p i) := by
      funext p
      show s * Rq p = Rq (Rq.symm s * p)
      rw [hRq_mul, Rq.apply_symm_apply]
    have hmeas : Measurable (fun (p : ∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
        (i : D.what₂.Tau) => Rq.symm s i * p i) :=
      measurable_pi_lambda _ fun τ => (measurable_const_mul _).comp (measurable_pi_apply τ)
    rw [Measure.map_map (measurable_const_mul s) Rq.measurable, hcomp,
      ← Measure.map_map Rq.measurable hmeas, hpm]
    congr 2
    funext τ
    exact hinvs τ
  · intro f hf
    rw [hpiG, hpiν, lintegral_map_equiv, lintegral_map_equiv]
    simp_rw [lintegral_map_equiv, ← hRq_mul]
    exact weil_pi (fun τ => Formalism.REAL.muG (X.B.I.ε (vOf X τ))) μl νl'
      (fun τ g hg => weil_loc C t τ (hH τ) (hC τ) (hQ τ) g hg) (fun p => f (Rq p)) (hf.comp Rq.measurable)
  · intro K _
    rw [Rq.map_apply, hpiμ, hE.map_apply]
    congr 1
    ext p
    constructor
    · intro hp
      refine ⟨Rq p, hp, funext fun τ => ?_⟩
      show eM C τ (Rq p (vOf X τ)) = eM C τ (p τ)
      rw [hRq_apply]
    · rintro ⟨x, hx, hxE⟩
      have hpx : p = Rq.symm x := funext fun τ => by
        rw [hRq_symm]
        exact ((eM_emb C τ).injective (congrFun hxE τ)).symm
      show Rq p ∈ K
      rw [hpx, Rq.apply_symm_apply]
      exact hx
  · intro τ
    rw [hνl τ]
    exact map_nuL C t τ (hC τ)

end GlobalTheory.PullbackComparison
