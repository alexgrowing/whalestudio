import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatExtMulVec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.FB

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ}

def lmulE (a : B.Mat k r) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv x := by
    have : a⁻¹ * (a * Matrix.of x) = Matrix.of x := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]
    exact this
  right_inv x := by
    have : a * (a⁻¹ * Matrix.of x) = Matrix.of x := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
    exact this
  measurable_toFun := B2x5.measurable_lmulM a
  measurable_invFun := B2x5.measurable_lmulM a⁻¹

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

private theorem measurePreserving_lmulE_of_isHaarOn {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ)
    {a : B.Mat k r} (ha : a ∈ U) (hdet : IsUnit a.det) : MeasurePreserving (lmulE a hdet) μ μ :=
  ⟨(lmulE a hdet).measurable, h.left a ha⟩

theorem fibInt_left (Bs : B.RealPlaceData k r Wp Wq) {μ0 μ0' : Measure (Mt k r)}
    (hμ0 : B.IsHaarOn (C2.N0set k r Bs.z) μ0) (hμ0' : B.IsHaarOn (C2.N0set k r Bs.z') μ0')
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) {n1 : B.Mat k r} (hn1 : n1 ∈ C2.N0set k r Bs.z) :
    PBI.fibInt Bs μ0 μ0' F (n1⁻¹ * g) = PBI.fibInt Bs μ0 μ0' F g := by
  have hdet : IsUnit n1.det := Formalism.FourierDecayAlt.P.StabilizerDisintegration.A.isUnit_N hn1.1
  haveI := Formalism.FourierDecayAlt.P.B7.sf Bs.haarW
  haveI := Formalism.FourierDecayAlt.P.B7.sf Bs.haarW'
  haveI := Formalism.FourierDecayAlt.P.B7.sf hμ0
  haveI := Formalism.FourierDecayAlt.P.B7.sf hμ0'
  let e : B.SS k r ≃ᵐ B.SS k r :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (lmulE n1 hdet))
      (MeasurableEquiv.refl _)
  have he : MeasurePreserving e ((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0'))
      ((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')) :=
    ((MeasurePreserving.id Bs.μW).prod (measurePreserving_lmulE_of_isHaarOn hμ0 hn1 hdet)).prod
      (MeasurePreserving.id (Bs.μW'.prod μ0'))
  have key : ∀ p : B.SS k r, B.rho Bs (e p) F g = B.rho Bs p F (n1⁻¹ * g) := by
    intro p
    have hs : B.sgs (e p) g = B.sgs p (n1⁻¹ * g) := by
      show (Matrix.of p.1.1)⁻¹ * (n1 * Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 = _
      simp only [B.sgs, Matrix.mul_inv_rev, Matrix.mul_assoc]
    show (Bs.π (Matrix.of p.1.1)).comp ((F (B.sgs (e p) g)).comp (Bs.π' (Matrix.of p.2.1)⁻¹)) = _
    rw [hs]
    rfl
  unfold PBI.fibInt
  calc ∫ p, B.rho Bs p F (n1⁻¹ * g) ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0'))
      = ∫ p, B.rho Bs (e p) F g ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')) := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => (key p).symm)
    _ = _ := he.integral_comp' (fun p => B.rho Bs p F g)

theorem fibInt_right (Bs : B.RealPlaceData k r Wp Wq) {μ0 μ0' : Measure (Mt k r)}
    (hμ0 : B.IsHaarOn (C2.N0set k r Bs.z) μ0) (hμ0' : B.IsHaarOn (C2.N0set k r Bs.z') μ0')
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) {n1 : B.Mat k r} (hn1 : n1 ∈ C2.N0set k r Bs.z') :
    PBI.fibInt Bs μ0 μ0' F (g * n1) = PBI.fibInt Bs μ0 μ0' F g := by
  have hdet : IsUnit n1.det := Formalism.FourierDecayAlt.P.StabilizerDisintegration.A.isUnit_N hn1.1
  haveI := Formalism.FourierDecayAlt.P.B7.sf Bs.haarW
  haveI := Formalism.FourierDecayAlt.P.B7.sf Bs.haarW'
  haveI := Formalism.FourierDecayAlt.P.B7.sf hμ0
  haveI := Formalism.FourierDecayAlt.P.B7.sf hμ0'
  let e : B.SS k r ≃ᵐ B.SS k r :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (lmulE n1 hdet))
  have he : MeasurePreserving e ((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0'))
      ((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')) :=
    (MeasurePreserving.id (Bs.μW.prod μ0)).prod
      ((MeasurePreserving.id Bs.μW').prod (measurePreserving_lmulE_of_isHaarOn hμ0' hn1 hdet))
  have key : ∀ p : B.SS k r, B.rho Bs (e p) F g = B.rho Bs p F (g * n1) := by
    intro p
    have hs : B.sgs (e p) g = B.sgs p (g * n1) := by
      show (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * (n1 * Matrix.of p.2.2) * Matrix.of p.2.1 = _
      simp only [B.sgs, Matrix.mul_assoc]
    show (Bs.π (Matrix.of p.1.1)).comp ((F (B.sgs (e p) g)).comp (Bs.π' (Matrix.of p.2.1)⁻¹)) = _
    rw [hs]
    rfl
  unfold PBI.fibInt
  calc ∫ p, B.rho Bs p F (g * n1) ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0'))
      = ∫ p, B.rho Bs (e p) F g ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')) := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => (key p).symm)
    _ = _ := he.integral_comp' (fun p => B.rho Bs p F g)

theorem unipotent_character_one_of_product {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {hA nA : B.Mat k r}
    (hhA : hA ∈ UWset k r z) (hnA : nA ∈ Nset k r) (hs : C2.uMap k r z (hA * nA) = 1) : C2.uMap k r z nA = 1 := by
  have key : C2.uMap k r z (hA * nA) = C2.uMap k r z nA := by
    funext a b
    simp only [C2.uMap]
    split_ifs with h
    · have e := Formalism.FourierDecayAlt.P.Qx2.herm_uh hhA.1 (nA *ᵥ fvec k r z b) (bvec (esI k r ⟨a.val, h⟩))
      rw [(hhA.2.1 ⟨a.val, h⟩).2, Matrix.mulVec_mulVec] at e
      exact e
    · have e := Formalism.FourierDecayAlt.P.Qx2.herm_uh hhA.1 (nA *ᵥ fvec k r z b) z
      rw [hhA.2.2, Matrix.mulVec_mulVec] at e
      rw [e]
  rw [← key]
  exact hs

theorem conj_fix {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hv : v ∈ C2.UTset (r + 1)) {n : B.Mat k r} (hn : n ∈ Nset k r) (hu : C2.uMap k r z n = 1) :
    C2.tauM k r z v * n * (C2.tauM k r z v)⁻¹ ∈ Nset k r ∧
      ∀ b, (C2.tauM k r z v * n * (C2.tauM k r z v)⁻¹) *ᵥ fvec k r z b = fvec k r z b := by
  set τ := C2.tauM k r z v with hτdef
  have hτN : τ ∈ Nset k r := Formalism.FourierDecayAlt.P.StabilizerDisintegration.A.tau_N hz hv
  have hτdet : IsUnit τ.det := Formalism.FourierDecayAlt.P.StabilizerDisintegration.A.isUnit_N hτN
  refine ⟨Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hτN hn) (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hτN), ?_⟩

  have h1W : (1 : B.Mat k r) ∈ UWset k r z := by
    refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
    · show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
      simp
    all_goals simp
  have hS : ∀ s ∈ Nset k r, s ∈ Sset k r z := fun s hs => ⟨1, h1W, s, hs, (Matrix.one_mul s).symm⟩

  obtain ⟨Un, -, -, hUn⟩ := Formalism.QuantumDeterminants.S_F hz.1 (hS n hn)
  have hUn1 : Un = 1 := by
    rw [← hu]
    exact (Formalism.FourierDecayAlt.P.C2x5.uMap_eq hz n Un (Formalism.FourierDecayAlt.P.C2x5.colEq hUn)).symm
  rw [hUn1, Matrix.mul_one] at hUn

  obtain ⟨Ut, hlow, hdiag, hUt⟩ := Formalism.QuantumDeterminants.S_F hz.1 (hS τ hτN)
  have hUdet : IsUnit Ut.det := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hlow i j hij)]
    simp [hdiag]
  have hinv : τ⁻¹ * Fm k r z = Fm k r z * Ut⁻¹ := by
    calc τ⁻¹ * Fm k r z = τ⁻¹ * (Fm k r z * Ut * Ut⁻¹) := by
          rw [Matrix.mul_assoc (Fm k r z), Matrix.mul_nonsing_inv _ hUdet, Matrix.mul_one]
      _ = τ⁻¹ * (τ * Fm k r z) * Ut⁻¹ := by rw [← hUt]; simp only [Matrix.mul_assoc]
      _ = Fm k r z * Ut⁻¹ := by
          rw [← Matrix.mul_assoc τ⁻¹, Matrix.nonsing_inv_mul _ hτdet, Matrix.one_mul]
  have hM : τ * n * τ⁻¹ * Fm k r z = Fm k r z * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
    calc τ * n * τ⁻¹ * Fm k r z = τ * (n * Fm k r z) * Ut⁻¹ := by
          rw [Matrix.mul_assoc (τ * n), hinv]; simp only [Matrix.mul_assoc]
      _ = Fm k r z * (Ut * Ut⁻¹) := by rw [hUn, hUt, Matrix.mul_assoc]
      _ = Fm k r z * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by rw [Matrix.mul_nonsing_inv _ hUdet]
  intro b
  rw [Formalism.FourierDecayAlt.P.C2x5.colEq hM b]
  simp [Matrix.one_apply]

variable (S : B.RealPlaceData k r Wp Wq)

theorem fib_indep (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (hbase : D.IsBaseFrame S ν' m₀) (pt : C.LPt)
    (hp : D.IsLocPt pt (r + 1)) (hG : 0 < D.ptG (Tz k r S.z * Tz k r S.z') r pt) {σ : B.Mat k r}
    (hE : m₀ * σ ∈ B.GV k r ∧ Zhat k r S.z S.z' (m₀ * σ) = D.ptMatN pt (r + 1) ∧
      D.IsDFrame S ν' m₀ (m₀ * σ) ∧ σ ∈ UH (Hpk k r) ∧
      (∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x) ∧
      (∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ Dx2.DF.ee k r a = Dx2.DF.ee k r a ∧
        g *ᵥ Dx2.DF.es k r a = Dx2.DF.es k r a) → g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ))
    {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') (F : B.Mat k r → (Wq →L[ℂ] Wp))
    {v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hv : v ∈ C2.UTset (r + 1)) (hu' : u' ∈ C2.UTset (r + 1))
    {g2 : B.Mat k r} (hg2 : g2 ∈ B.GV k r)
    (hZ2 : Zhat k r S.z S.z' g2 = Zhat k r S.z S.z' ((C2.tauM k r S.z v)⁻¹ * (m₀ * σ) * C2.tauM k r S.z' u'))
    (hD2 : D.IsDFrame S ν' m₀ g2) :
    PBI.fibInt S μ0 μ0' F g2 = PBI.fibInt S μ0 μ0' F ((C2.tauM k r S.z v)⁻¹ * (m₀ * σ) * C2.tauM k r S.z' u') := by
  obtain ⟨hγe, hZe, hDe, hσU, hE3, hE2⟩ := hE
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  set γ0 := m₀ * σ with hγ0
  set τ := C2.tauM k r S.z v with hτ_def
  set τ' := C2.tauM k r S.z' u' with hτ'_def
  have hτN : τ ∈ Nset k r := A.tau_N hz hv
  have hτN' : τ' ∈ Nset k r := A.tau_N hz' hu'
  have uτ := A.isUnit_N hτN
  have uτ' := A.isUnit_N hτN'
  have hGG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hg1 : τ⁻¹ * γ0 * τ' ∈ B.GV k r :=
    hGG.mul_mem _ (hGG.mul_mem _ (hGG.inv_mem _ hτN.1) _ hγe) _ hτN'.1
  have hpos0 : 0 < Gf k r S.z S.z' γ0 := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec k r S.z S.z' pt _ hp hZe]; exact hG
  have hdet := Formalism.FourierDecayAlt.P.determinant_nonzero k r S.z S.z' hz hz' _ hpos0
  have hZ1 : Zhat k r S.z S.z' (τ⁻¹ * γ0 * τ') = vᴴ * Zhat k r S.z S.z' γ0 * u' := by
    rw [Formalism.FourierDecayAlt.P.zhat_equivalence k r S.z S.z' hz hz' τ (A.n_in_S hτN) τ' (A.n_in_S hτN') γ0,
      (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z hz v hv).2.2, (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' u' hu').2.2]
  have hpos1 : 0 < Gf k r S.z S.z' (τ⁻¹ * γ0 * τ') := by
    rw [PBI.gf_eq_gPoly, hZ1]
    rw [PBI.gf_eq_gPoly] at hpos0
    obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.StabilizerDisintegration.minorsLU r vᴴ (Zhat k r S.z S.z' γ0) u' (A.UT_star hv) hu'
    unfold PBI.gPoly at hpos0 ⊢
    rw [h1, h2]; exact hpos0
  obtain ⟨s, hs, s', hs', hgs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description k r S.z S.z' ⟨S.k_pos, hz, hz'⟩ _ hg1 g2 hg2
    hpos1 hZ2.symm
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent hz hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent hz' hs'
  have huA : C2.uMap k r S.z nA = 1 := unipotent_character_one_of_product hz hhA hnA hs.2
  have huB : C2.uMap k r S.z' nB = 1 := unipotent_character_one_of_product hz' hhB hnB hs'.2
  obtain ⟨hnA'', hfA''⟩ := conj_fix hz hv hnA huA
  obtain ⟨hnB'', hfB''⟩ := conj_fix hz' hu' hnB huB
  have uhA : IsUnit hA.det := Dx2.OrbJ.isUnit_of_G hhA.1
  have uhB : IsUnit hB.det := Dx2.OrbJ.isUnit_of_G hhB.1
  have unA : IsUnit nA.det := A.isUnit_N hnA

  have cA : hA⁻¹ * τ⁻¹ = τ⁻¹ * hA⁻¹ := by
    have := A.tau_comm hhA v
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev]
    exact congrArg _ this.symm
  have cB : τ' * hB = hB * τ' := (A.tau_comm hhB u').symm

  have hX := A.dframe_tau_inv S ν' m₀ hg2 hD2 hv hu'
  have hXeq : τ * g2 * τ'⁻¹ = (hA * (τ * nA * τ⁻¹))⁻¹ * γ0 * (hB * (τ' * nB * τ'⁻¹)) := by
    rw [hgs]
    have e1 : (hA * (τ * nA * τ⁻¹))⁻¹ = τ * nA⁻¹ * τ⁻¹ * hA⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ uτ]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.mul_inv_rev]
    calc τ * (nA⁻¹ * hA⁻¹ * (τ⁻¹ * γ0 * τ') * (hB * nB)) * τ'⁻¹
        = τ * nA⁻¹ * (hA⁻¹ * τ⁻¹) * γ0 * (τ' * hB) * nB * τ'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = τ * nA⁻¹ * (τ⁻¹ * hA⁻¹) * γ0 * (hB * τ') * nB * τ'⁻¹ := by rw [cA, cB]
      _ = τ * nA⁻¹ * τ⁻¹ * hA⁻¹ * γ0 * (hB * (τ' * nB * τ'⁻¹)) := by simp only [Matrix.mul_assoc]
  rw [hXeq] at hX
  have hfix := Dx2.VV.frame_fix S ν' m₀ hbase hσU hE3 hE2 hγe hDe hdet hhA hnA'' hfA'' hhB hnB'' hfB'' hX

  have hg2eq : (hA * nA)⁻¹ * (τ⁻¹ * γ0 * τ') * (hB * nB) = nA⁻¹ * (τ⁻¹ * γ0 * τ') * nB := by
    rw [Matrix.mul_inv_rev]
    calc nA⁻¹ * hA⁻¹ * (τ⁻¹ * γ0 * τ') * (hB * nB) = nA⁻¹ * (hA⁻¹ * τ⁻¹) * γ0 * (τ' * hB) * nB := by
          simp only [Matrix.mul_assoc]
      _ = nA⁻¹ * τ⁻¹ * (hA⁻¹ * γ0 * hB) * τ' * nB := by rw [cA, cB]; simp only [Matrix.mul_assoc]
      _ = nA⁻¹ * (τ⁻¹ * γ0 * τ') * nB := by rw [hfix]; simp only [Matrix.mul_assoc, hγ0]
  rw [hgs, hg2eq, fibInt_right S hμ0 hμ0' F _ ⟨hnB, huB⟩, fibInt_left S hμ0 hμ0' F _ ⟨hnA, huA⟩]

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.FB
