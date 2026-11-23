import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagStabilizerFixesFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsSmoothExt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundX

namespace Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Set Filter Topology Metric PI.PolynomialProperness

noncomputable section

section alg

variable {k r : ℕ}

def mm (A B : Mt k r) : Mt k r := fun i j => ∑ l, A i l * B l j

def ct (A : Mt k r) : Mt k r := fun i j => Complex.conjCLE (A j i)

def hinvM (A : Mt k r) : Mt k r := mm (mm (Matrix.of.symm (Hpk k r)) (ct A)) (Matrix.of.symm (Hpk k r))

def sgsP (p : B.SS k r) (g : Mt k r) : Mt k r := mm (mm (mm (mm (hinvM p.1.1) (hinvM p.1.2)) g) p.2.2) p.2.1

theorem of_mm (A B : Mt k r) : Matrix.of (mm A B) = Matrix.of A * Matrix.of B := by
  ext i j
  simp [mm, Matrix.mul_apply]

theorem of_ct (A : Mt k r) : Matrix.of (ct A) = (Matrix.of A)ᴴ := by
  ext i j
  simp [ct, Matrix.conjTranspose_apply]

theorem of_hinvM {A : Mt k r} (hA : Matrix.of A ∈ B.GV k r) : Matrix.of (hinvM A) = (Matrix.of A)⁻¹ := by
  simp only [hinvM, of_mm, of_ct, Equiv.apply_symm_apply]
  have hg : (Matrix.of A)ᴴ * Hpk k r * Matrix.of A = Hpk k r := hA
  refine (Matrix.inv_eq_left_inv ?_).symm
  calc Hpk k r * (Matrix.of A)ᴴ * Hpk k r * Matrix.of A
      = Hpk k r * ((Matrix.of A)ᴴ * Hpk k r * Matrix.of A) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Formalism.QuantumDeterminants.GBasic.Hpk_sq]

theorem of_sgsP {p : B.SS k r} (h1 : Matrix.of p.1.1 ∈ B.GV k r) (h2 : Matrix.of p.1.2 ∈ B.GV k r) (g : Mt k r) :
    Matrix.of (sgsP p g) = B.sgs p (Matrix.of g) := by
  rw [sgsP, of_mm, of_mm, of_mm, of_mm, of_hinvM h1, of_hinvM h2]
  rfl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}

theorem cd_ent {f : X → Mt k r} (hf : ContDiff ℝ n f) (i j : Fin (2 * r + k + 1)) :
    ContDiff ℝ n fun x => f x i j := contDiff_pi.mp (contDiff_pi.mp hf i) j

theorem cd_mm {f g : X → Mt k r} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun x => mm (f x) (g x) := by
  refine contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => ?_))
  simp only [mm]
  exact ContDiff.sum (fun l _ => (cd_ent hf i l).mul (cd_ent hg l j))

theorem cd_ct {f : X → Mt k r} (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => ct (f x) := by
  refine contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => ?_))
  exact Complex.conjCLE.contDiff.comp (cd_ent hf j i)

theorem cd_hinvM {f : X → Mt k r} (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => hinvM (f x) :=
  cd_mm (cd_mm contDiff_const (cd_ct hf)) contDiff_const

theorem cd_sgsP : ContDiff ℝ n fun q : B.SS k r × Mt k r => sgsP q.1 q.2 := by
  have h11 : ContDiff ℝ n fun q : B.SS k r × Mt k r => q.1.1.1 := contDiff_fst.comp (contDiff_fst.comp contDiff_fst)
  have h12 : ContDiff ℝ n fun q : B.SS k r × Mt k r => q.1.1.2 := contDiff_snd.comp (contDiff_fst.comp contDiff_fst)
  have h21 : ContDiff ℝ n fun q : B.SS k r × Mt k r => q.1.2.1 := contDiff_fst.comp (contDiff_snd.comp contDiff_fst)
  have h22 : ContDiff ℝ n fun q : B.SS k r × Mt k r => q.1.2.2 := contDiff_snd.comp (contDiff_snd.comp contDiff_fst)
  have hg : ContDiff ℝ n fun q : B.SS k r × Mt k r => q.2 := contDiff_snd
  exact cd_mm (cd_mm (cd_mm (cd_mm (cd_hinvM h11) (cd_hinvM h12)) hg) h22) h21

theorem norm_le_gN (x : Mt k r) : ‖x‖ ≤ B.gN (Matrix.of x) := by
  refine (pi_norm_le_iff_of_nonneg (GN.gN_nonneg _)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (GN.gN_nonneg _)).2 fun j => ?_
  exact GN.entry_le_gN (Matrix.of x) i j

end alg

section sand

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sand (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp)
    (ContinuousLinearMap.compL ℂ Wq Wp Wp A) ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B')

theorem sand_apply (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) (X : Wq →L[ℂ] Wp) : sand A B' X = A.comp (X.comp B') := rfl

theorem sand_cont : Continuous fun q : (Wp →L[ℂ] Wp) × (Wq →L[ℂ] Wq) => sand q.1 q.2 := by
  have h1 : Continuous fun q : (Wp →L[ℂ] Wp) × (Wq →L[ℂ] Wq) => ContinuousLinearMap.compL ℂ Wq Wp Wp q.1 :=
    (ContinuousLinearMap.compL ℂ Wq Wp Wp).continuous.comp continuous_fst
  have h2 : Continuous fun q : (Wp →L[ℂ] Wp) × (Wq →L[ℂ] Wq) => (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip q.2 :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip.continuous.comp continuous_snd
  exact h1.clm_comp h2

theorem sand_norm_le (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) (hA : ‖A‖ ≤ 1) (hB : ‖B'‖ ≤ 1) :
    ‖sand A B'‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun X => ?_)
  rw [sand_apply, one_mul]
  calc ‖A.comp (X.comp B')‖ ≤ ‖A‖ * ‖X.comp B'‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖X‖ * ‖B'‖) :=
        mul_le_mul hA (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one
    _ ≤ ‖X‖ := by nlinarith [norm_nonneg X, norm_nonneg B']

end sand

section main

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def fR (Bs : B.RealPlaceData k r Wp Wq) (p : B.SS k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  sand (Bs.π (Matrix.of p.1.1)) (Bs.π' (Matrix.of (hinvM p.2.1)))

def automorphic_in_spherical_level (Bs : B.RealPlaceData k r Wp Wq) (p : B.SS k r) : Prop :=
  Matrix.of p.1.1 ∈ UWset k r Bs.z ∧ Matrix.of p.1.2 ∈ C2.N0set k r Bs.z ∧
    Matrix.of p.2.1 ∈ UWset k r Bs.z' ∧ Matrix.of p.2.2 ∈ C2.N0set k r Bs.z'

theorem ae_mem_good_set (Bs : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r))
    (hμ0 : B.IsHaarOn (C2.N0set k r Bs.z) μ0) (hμ0' : B.IsHaarOn (C2.N0set k r Bs.z') μ0') :
    ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')), automorphic_in_spherical_level Bs p := by
  have hW := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW
  have hW' := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW'
  have hN := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0
  have hN' := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0'
  have b1 : ∀ᵐ q ∂(Bs.μW.prod μ0), Matrix.of q.1 ∈ UWset k r Bs.z :=
    (Measure.quasiMeasurePreserving_fst (μ := Bs.μW) (ν := μ0)).ae
      (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem Bs.haarW)
  have b2 : ∀ᵐ q ∂(Bs.μW.prod μ0), Matrix.of q.2 ∈ C2.N0set k r Bs.z :=
    (Measure.quasiMeasurePreserving_snd (μ := Bs.μW) (ν := μ0)).ae (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hμ0)
  have c1 : ∀ᵐ q ∂(Bs.μW'.prod μ0'), Matrix.of q.1 ∈ UWset k r Bs.z' :=
    (Measure.quasiMeasurePreserving_fst (μ := Bs.μW') (ν := μ0')).ae
      (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem Bs.haarW')
  have c2 : ∀ᵐ q ∂(Bs.μW'.prod μ0'), Matrix.of q.2 ∈ C2.N0set k r Bs.z' :=
    (Measure.quasiMeasurePreserving_snd (μ := Bs.μW') (ν := μ0')).ae (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hμ0')
  have d1 : ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')),
      Matrix.of p.1.1 ∈ UWset k r Bs.z ∧ Matrix.of p.1.2 ∈ C2.N0set k r Bs.z :=
    (Measure.quasiMeasurePreserving_fst (μ := Bs.μW.prod μ0) (ν := Bs.μW'.prod μ0')).ae (b1.and b2)
  have d2 : ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')),
      Matrix.of p.2.1 ∈ UWset k r Bs.z' ∧ Matrix.of p.2.2 ∈ C2.N0set k r Bs.z' :=
    (Measure.quasiMeasurePreserving_snd (μ := Bs.μW.prod μ0) (ν := Bs.μW'.prod μ0')).ae (c1.and c2)
  filter_upwards [d1, d2] with p h1 h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

theorem isClosed_good_set (Bs : B.RealPlaceData k r Wp Wq) : IsClosed {p : B.SS k r | automorphic_in_spherical_level Bs p} := by
  have hz : C2.StdZ k r Bs.z := ⟨Bs.z_mem, Bs.T_pos⟩
  have hz' : C2.StdZ k r Bs.z' := ⟨Bs.z'_mem, Bs.T'_pos⟩
  have u1 : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r Bs.z} := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs.z).closed
  have u2 : IsClosed {x : Mt k r | Matrix.of x ∈ C2.N0set k r Bs.z} := (PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r Bs.z hz).closed
  have u3 : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r Bs.z'} :=
    (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs.z').closed
  have u4 : IsClosed {x : Mt k r | Matrix.of x ∈ C2.N0set k r Bs.z'} :=
    (PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r Bs.z' hz').closed
  have h := ((u1.preimage (continuous_fst.comp continuous_fst)).inter (u2.preimage (continuous_snd.comp continuous_fst))).inter
    ((u3.preimage (continuous_fst.comp continuous_snd)).inter (u4.preimage (continuous_snd.comp continuous_snd)))
  convert h using 1
  ext p
  simp [automorphic_in_spherical_level, and_assoc]

theorem norm_pi_le_one (Bs : B.RealPlaceData k r Wp Wq) {h : B.Mat k r} (hh : h ∈ UWset k r Bs.z) : ‖Bs.π h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [Bs.π_unitary h hh v, one_mul]

theorem norm_pi'_le_one (Bs : B.RealPlaceData k r Wp Wq) {h : B.Mat k r} (hh : h ∈ UWset k r Bs.z') : ‖Bs.π' h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [Bs.π'_unitary h hh v, one_mul]

theorem hinv_mem (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : automorphic_in_spherical_level Bs p) :
    Matrix.of (hinvM p.2.1) ∈ UWset k r Bs.z' := by
  rw [of_hinvM hp.2.2.1.1]
  exact (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs.z').inv_mem _ hp.2.2.1

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem fR_loc (Bs : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r))
    (hμ0 : B.IsHaarOn (C2.N0set k r Bs.z) μ0) (hμ0' : B.IsHaarOn (C2.N0set k r Bs.z') μ0') :
    LocallyIntegrable (fR Bs) ((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')) := by
  have hae := ae_mem_good_set Bs μ0 μ0' hμ0 hμ0'
  have hc1 : Continuous fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r) := continuous_fst.comp continuous_fst
  have hc2 : Continuous fun p : B.SS k r => (Matrix.of (hinvM p.2.1) : B.Mat k r) :=
    (cd_hinvM (n := 0) (by fun_prop : ContDiff ℝ 0 fun p : B.SS k r => p.2.1)).continuous
  have hpair : ContinuousOn (fun p : B.SS k r => (Bs.π (Matrix.of p.1.1), Bs.π' (Matrix.of (hinvM p.2.1))))
      {p | automorphic_in_spherical_level Bs p} :=
    (Bs.π_cont.comp hc1.continuousOn fun p hp => hp.1).prodMk
      (Bs.π'_cont.comp hc2.continuousOn fun p hp => hinv_mem Bs hp)
  have h2 := sand_cont.comp_continuousOn hpair
  have hcont : ContinuousOn (fR Bs) {p | automorphic_in_spherical_level Bs p} := by
    unfold fR
    exact h2
  have hsm : AEStronglyMeasurable (fR Bs) ((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')) := by
    have h := hcont.aestronglyMeasurable (μ := (Bs.μW.prod μ0).prod (Bs.μW'.prod μ0'))
      (isClosed_good_set Bs).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {p | automorphic_in_spherical_level Bs p}) hae] at h
  have hbd : ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')), ‖fR Bs p‖ ≤ 1 :=
    hae.mono fun p hp => sand_norm_le _ _ (norm_pi_le_one Bs hp.1) (norm_pi'_le_one Bs (hinv_mem Bs hp))
  have := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW
  have := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW'
  have := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0
  have := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0'
  have : IsFiniteMeasureOnCompacts Bs.μW := ⟨fun K hK => Bs.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts Bs.μW' := ⟨fun K hK => Bs.haarW'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts μ0 := ⟨fun K hK => hμ0.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts μ0' := ⟨fun K hK => hμ0'.finite_compact K hK⟩
  exact fun x => ⟨closedBall x 1, closedBall_mem_nhds x one_pos,
    Measure.integrableOn_of_bounded (isCompact_closedBall x 1).measure_lt_top.ne hsm (ae_restrict_of_ae hbd)⟩

end main

section final

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem norm_SS_le (p : B.SS k r) (c : ℝ) (h1 : B.gN (Matrix.of p.1.1) ≤ c) (h2 : B.gN (Matrix.of p.1.2) ≤ c)
    (h3 : B.gN (Matrix.of p.2.1) ≤ c) (h4 : B.gN (Matrix.of p.2.2) ≤ c) : ‖p‖ ≤ c := by
  rw [norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
  exact ⟨⟨(norm_le_gN _).trans h1, (norm_le_gN _).trans h2⟩, ⟨(norm_le_gN _).trans h3, (norm_le_gN _).trans h4⟩⟩

theorem local_smooth (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (μ0 μ0' : Measure (Mt k r)) (hμ0 : B.IsHaarOn (C2.N0set k r Bs.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r Bs.z') μ0') (sec : G.Mat (r + 1) → Mt k r) (hsec : PBI.IsSec Bs ν' m₀ sec)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (R : ℝ) (hR : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R)
    (Ft : Mt k r → (Wq →L[ℂ] Wp)) (hFt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ft)
    (hFtF : ∀ x : Mt k r, Matrix.of x ∈ B.GV k r → Ft x = F (Matrix.of x)) (Z₀ : G.Mat (r + 1))
    (hZ₀ : 0 < PBI.gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z₀)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (PBI.phi0 Bs μ0 μ0' sec F) Z₀ := by
  have hstd : C2.Std k r Bs.z Bs.z' := ⟨Bs.k_pos, ⟨Bs.z_mem, Bs.T_pos⟩, ⟨Bs.z'_mem, Bs.T'_pos⟩⟩
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Set (G.Mat (r + 1)),
      Ω = {Z | 0 < PBI.gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z)} := ⟨_, rfl⟩
  have hΩ : IsOpen Ω := hΩdef ▸ isOpen_lt continuous_const (PBI.continuous_gPoly r _)
  have hZΩ : Z₀ ∈ Ω := hΩdef ▸ hZ₀
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hΩ Z₀ hZΩ
  have hδ : 0 < δ₀ / 2 := by positivity
  have hKΩ : closedBall Z₀ (δ₀ / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hball
  have hsΩ : ball Z₀ (δ₀ / 2) ⊆ Ω := ball_subset_closedBall.trans hKΩ
  have hsecΩ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sec Ω := hΩdef ▸ hsec.1
  have hsecΩ' : ∀ Z ∈ Ω, Matrix.of (sec Z) ∈ B.GV k r ∧
      Zhat k r Bs.z Bs.z' (Matrix.of (sec Z)) = Matrix.of Z := fun Z hZ => by
    rw [hΩdef] at hZ
    exact ⟨(hsec.2 Z hZ).1, (hsec.2 Z hZ).2.1⟩
  have hcont : ContinuousOn (fun Z => (Matrix.of (sec Z) : B.Mat k r)) (closedBall Z₀ (δ₀ / 2)) :=
    hsecΩ.continuousOn.mono hKΩ
  obtain ⟨Kg, hKgdef⟩ : ∃ Kg : Set (B.Mat k r), Kg = (fun Z => (Matrix.of (sec Z) : B.Mat k r)) '' closedBall Z₀ (δ₀ / 2) :=
    ⟨_, rfl⟩
  have hKg : IsCompact Kg := hKgdef ▸ (isCompact_closedBall Z₀ (δ₀ / 2)).image_of_continuousOn hcont
  have hKpos : ∀ g ∈ Kg, C2.PosPt k r Bs.z Bs.z' g := by
    intro g hg
    rw [hKgdef] at hg
    obtain ⟨Z, hZ, rfl⟩ := hg
    obtain ⟨hgG, hZg⟩ := hsecΩ' Z (hKΩ hZ)
    refine ⟨hgG, ?_⟩
    have hZ' := hKΩ hZ
    rw [hΩdef] at hZ'
    rw [PBI.gf_eq_gPoly, hZg]
    exact hZ'
  obtain ⟨Rp, hRp⟩ := fibreProper Bs.z Bs.z' hstd Kg hKg hKpos R
  have hρ : 0 < max Rp 1 := lt_max_of_lt_right one_pos
  let φ : ContDiffBump (0 : B.SS k r) := ⟨max Rp 1, max Rp 1 + 1, hρ, by linarith⟩

  have hgs : ∀ (Z : G.Mat (r + 1)) (x : B.SS k r), Z ∈ ball Z₀ (δ₀ / 2) → x ∉ closedBall (0 : B.SS k r) (max Rp 1 + 1) →
      φ (-x) • Ft (sgsP (-x) (sec Z)) = 0 := by
    intro Z x _ hx
    have h0 : φ (-x) = 0 := by
      apply φ.zero_of_le_dist
      rw [mem_closedBall, dist_zero_right, not_le] at hx
      rw [dist_zero_right, norm_neg]
      exact hx.le
    rw [h0, zero_smul]
  have hgsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : G.Mat (r + 1) × B.SS k r => φ (-q.2) • Ft (sgsP (-q.2) (sec q.1))) (ball Z₀ (δ₀ / 2) ×ˢ univ) := by
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun q : G.Mat (r + 1) × B.SS k r => φ (-q.2) :=
      φ.contDiff.comp contDiff_snd.neg
    have hsec2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : G.Mat (r + 1) × B.SS k r => sec q.1)
        (ball Z₀ (δ₀ / 2) ×ˢ univ) :=
      hsecΩ.comp contDiff_fst.contDiffOn fun q hq => hsΩ hq.1
    have hpair : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : G.Mat (r + 1) × B.SS k r => (-q.2, sec q.1)) (ball Z₀ (δ₀ / 2) ×ˢ univ) :=
      contDiff_snd.neg.contDiffOn.prodMk hsec2
    have hin := (cd_sgsP (k := k) (r := r) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp_contDiffOn hpair
    have hfull := hφ.contDiffOn.smul (hFt.comp_contDiffOn hin)
    exact hfull.congr fun q _ => rfl
  have hconv := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (n := ⊤)
    (μ := (Bs.μW.prod μ0).prod (Bs.μW'.prod μ0'))
    (ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℝ)
    (s := ball Z₀ (δ₀ / 2)) (v := fun _ => (0 : B.SS k r)) contDiffOn_const (f := fR Bs)
    (g := fun Z x => φ (-x) • Ft (sgsP (-x) (sec Z))) (k := closedBall (0 : B.SS k r) (max Rp 1 + 1))
    isOpen_ball (isCompact_closedBall _ _) hgs (fR_loc Bs μ0 μ0' hμ0 hμ0') hgsm

  have hae := ae_mem_good_set Bs μ0 μ0' hμ0 hμ0'
  have heq : ∀ Z ∈ ball Z₀ (δ₀ / 2), PBI.phi0 Bs μ0 μ0' sec F Z =
      convolution (fR Bs) (fun x => φ (-x) • Ft (sgsP (-x) (sec Z)))
        (ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℝ)
        ((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')) 0 := by
    intro Z hZ
    have hZΩ' := hsΩ hZ
    have hZpos : 0 < PBI.gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z) := by rw [hΩdef] at hZΩ'; exact hZΩ'
    obtain ⟨hgG, -⟩ := hsecΩ' Z hZΩ'
    have hgK : (Matrix.of (sec Z) : B.Mat k r) ∈ Kg := by
      rw [hKgdef]; exact ⟨Z, ball_subset_closedBall hZ, rfl⟩
    rw [PBI.phi0, if_pos hZpos, PBI.fibInt, convolution_def]
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have hG1 : Matrix.of p.1.1 ∈ B.GV k r := h1.1
    have hG2 : Matrix.of p.1.2 ∈ B.GV k r := h2.1.1
    have hG3 : Matrix.of p.2.1 ∈ B.GV k r := h3.1
    have hG4 : Matrix.of p.2.2 ∈ B.GV k r := h4.1.1
    have hsg : Matrix.of (sgsP p (sec Z)) = B.sgs p (Matrix.of (sec Z)) := of_sgsP hG1 hG2 _
    have hsgG : B.sgs p (Matrix.of (sec Z)) ∈ B.GV k r := by
      unfold B.sgs
      exact GN.mul_mem (GN.mul_mem (GN.mul_mem (GN.mul_mem (GN.inv_mem hG1) (GN.inv_mem hG2)) hgG) hG4) hG3
    have hFt' : Ft (sgsP p (sec Z)) = F (B.sgs p (Matrix.of (sec Z))) := by
      rw [hFtF _ (hsg ▸ hsgG), hsg]
    have hinv' : Matrix.of (hinvM p.2.1) = (Matrix.of p.2.1)⁻¹ := of_hinvM hG3
    have hR' : (ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℝ) (fR Bs p)
        (φ (- (0 - p)) • Ft (sgsP (- (0 - p)) (sec Z))) =
        (Bs.π (Matrix.of p.1.1)).comp ((φ p • F (B.sgs p (Matrix.of (sec Z)))).comp
          (Bs.π' (Matrix.of p.2.1)⁻¹)) := by
      rw [zero_sub, neg_neg, hFt', ← hinv']
      rfl
    rw [hR']
    by_cases hF0 : F (B.sgs p (Matrix.of (sec Z))) = 0
    · simp [B.rho, hF0]
    · have hb : B.gN ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * Matrix.of (sec Z) * Matrix.of p.2.2 *
          Matrix.of p.2.1) ≤ R := hR _ hsgG hF0
      obtain ⟨b1, b2, b3, b4⟩ := hRp _ hgK _ h1 _ h2 _ h3 _ h4 hb
      have hpn : ‖p‖ ≤ max Rp 1 :=
        norm_SS_le p _ (b1.trans (le_max_left _ _)) (b2.trans (le_max_left _ _))
          (b3.trans (le_max_left _ _)) (b4.trans (le_max_left _ _))
      have hφ1 : φ p = 1 := φ.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hpn)
      rw [hφ1, one_smul]
      rfl
  exact (hconv.congr heq).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))

end final

theorem fibIntSmooth : PBI.FibIntSmooth := by
  intro k r Wp Wq _ _ _ _ _ _ Bs ν' m₀ μ0 μ0' sec F _ hμ0 hμ0' hsec hF
  obtain ⟨hFsm, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  obtain ⟨Ft, hFt, hFtF⟩ := exists_smoothExt F hFsm
  rw [contDiff_iff_contDiffAt]
  intro Z₀
  by_cases hZ₀ : 0 < PBI.gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z₀)
  · exact local_smooth Bs ν' m₀ μ0 μ0' hμ0 hμ0' sec hsec F R hR Ft hFt hFtF Z₀ hZ₀
  · have hopen : IsOpen {Z : G.Mat (r + 1) | PBI.gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z) < ε} :=
      isOpen_lt (PBI.continuous_gPoly r _) continuous_const
    have hmem : Z₀ ∈ {Z : G.Mat (r + 1) | PBI.gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z) < ε} := by
      show PBI.gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z₀) < ε
      linarith [not_lt.1 hZ₀]
    have hev : PBI.phi0 Bs μ0 μ0' sec F =ᶠ[𝓝 Z₀] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hmem] with Z hZ
      by_contra hne
      obtain ⟨g, hg, hFg, hZg⟩ := PBI.support_phi_zero_subset Bs ν' m₀ μ0 μ0' hμ0 hμ0' sec hsec F Z hne
      have h1 := hεG g hg hFg
      rw [PBI.gf_eq_gPoly, hZg] at h1
      exact absurd hZ (not_lt.2 h1)
    exact contDiffAt_const.congr_of_eventuallyEq hev

end

end Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet

namespace Formalism.FourierDecayAlt.P

theorem fibre_integral_smooth : PBI.FibIntSmooth := SmoothExtensionClosedSet.fibIntSmooth

end Formalism.FourierDecayAlt.P
