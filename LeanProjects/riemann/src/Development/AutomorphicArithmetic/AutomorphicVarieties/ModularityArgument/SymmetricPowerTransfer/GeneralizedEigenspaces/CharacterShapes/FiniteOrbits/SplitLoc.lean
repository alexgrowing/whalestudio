import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.KirillovFunctionValueEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulEqSumCosetInd

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem split_loc (O : Type) [CommRing O] [Algebra O k] (hO : IsInts k O) (h2 : (2 : k) ≠ 0) {Δ s : k}
    (hs : s * s = Δ) (hs0 : s ≠ 0) (x : DX Δ) (hx : x ∈ KD Δ O) :
    ∃ t ∈ SU Δ, eD hs (t⁻¹ * x) ∈ (Lev.iw k).J 2 := by
  obtain ⟨hbij, hKO, -, -, hdet, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  have hxK : eD hs x ∈ KO k (Fin 2) := by
    have hx' : x ∈ Subgroup.comap (eD hs) (KO k (Fin 2)) := by
      rw [hKO]
      exact hx
    exact hx'
  let d : Fin 2 → kˣ := ![Matrix.GeneralLinearGroup.det (eD hs x), 1]
  have hd : Matrix.GeneralLinearGroup.det (dg d) = Matrix.GeneralLinearGroup.det (eD hs x) := by
    apply Units.ext
    simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two, d]
  obtain ⟨t, ht⟩ := hbij.2 (eD hs x * (dg d)⁻¹)
  refine ⟨t, ?_, ?_⟩
  · rw [SU, MonoidHom.mem_ker]
    apply Units.ext
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    rw [show (↑(↑t : GL (Fin 2) (Lsq k Δ)) : Matrix (Fin 2) (Fin 2) (Lsq k Δ)) = Glob.mt t from rfl, (hdet t).1, ht,
      ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, hd, mul_inv_cancel, Units.val_one, map_one]
  · rw [map_mul, map_inv, ht, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    apply Lev.dg_mem
    intro i
    fin_cases i
    · show valuation k (↑(Matrix.GeneralLinearGroup.det (eD hs x)) : k) = 1
      exact GlobalTheory.StepData.valuation_det_of_mem_KO hxK
    · exact one_mem _

end

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (h : s * s = Δ) (h' : s' * s' = Δ) (e : s = s') (x : DX Δ) :
    eD h x = eD h' x := by
  subst e
  rfl

theorem UpperTheory.V.Z.Sym.So.kNon :
    UpperTheory.V.Z.Sym.So.KNon := by
  intro F _ _ Δ A hA A₀ hA₀ hE V _ _ ch C hC Y hY hoff φ hφ hφ0
  classical
  obtain ⟨-, -, hloc, -, hU2⟩ := datOk F Δ A hA
  obtain ⟨-, -, -, -, hU2₀⟩ := datOk F Δ A₀ hA₀
  have hinv := (kOps F Δ A hA V ch C hC).2.1 φ hφ
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (funext h)
  obtain ⟨γ, s, hs, y, hy, u, hu, rfl⟩ := hY.2 g
  have hu₀ := (hU2₀ u).1 hu
  have hspl : ∀ v (h : v ∈ A.Sg ∧ v ∉ A₀.Sg), ∃ r ∈ SU ((cv v) Δ),
      eD (A.hs v h.1) (r⁻¹ * u.1 v) ∈ (Lev.iw (Kv v)).J 2 := fun v h =>
    split_loc (Ov v) (hloc v h.1).1 (hloc v h.1).2.1 (A.hs v h.1) (hloc v h.1).2.2.1 (u.1 v) (hu₀.2 v h.2)
  let tf : (v : Pl F) → ↥(DX ((cv v) Δ)) := fun v =>
    if h : v ∈ A.Sg ∧ v ∉ A₀.Sg then (hspl v h).choose else 1
  have htf : tf ∈ RP (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v)) := by
    show ∀ᶠ v in Filter.cofinite, tf v ∈ KD ((cv v) Δ) (Ov v)
    refine Filter.eventually_cofinite.mpr (A.Sg.finite_toSet.subset ?_)
    intro v hv
    by_contra h
    apply hv
    have hn : ¬ (v ∈ A.Sg ∧ v ∉ A₀.Sg) := fun h' => h h'.1
    simp only [tf, dif_neg hn]
    exact one_mem _
  let t : DA Δ := ⟨tf, htf⟩
  have hcomm : t * y = y * t := by
    apply Subtype.ext
    funext v
    show tf v * y.1 v = y.1 v * tf v
    by_cases h : v ∈ A.Sg ∧ v ∉ A₀.Sg
    · rw [hoff y hy v h.1]
      simp
    · simp only [tf, dif_neg h]
      simp
  have htS : t ∈ SA Δ := by
    simp only [SA, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show tf v ∈ SU ((cv v) Δ)
    by_cases h : v ∈ A.Sg ∧ v ∉ A₀.Sg
    · simp only [tf, dif_pos h]
      exact (hspl v h).choose_spec.1
    · simp only [tf, dif_neg h]
      exact one_mem _
  have hj : t⁻¹ * u ∈ A.dat.U2 := by
    refine (hU2 _).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
    · show eD (A.hs v hv) ((tf v)⁻¹ * u.1 v) ∈ (A.V v).J 2
      by_cases h0 : v ∈ A₀.Sg
      · have hn : ¬ (v ∈ A.Sg ∧ v ∉ A₀.Sg) := fun h => h.2 h0
        simp only [tf, dif_neg hn, inv_one, one_mul]
        rw [eD_congr (A.hs v hv) (A₀.hs v h0) (hE.s v h0), hE.V v h0]
        exact hu₀.1 v h0
      · have hp : v ∈ A.Sg ∧ v ∉ A₀.Sg := ⟨hv, h0⟩
        simp only [tf, dif_pos hp]
        rw [hE.iw v hv h0]
        exact (hspl v hp).choose_spec.2
    · show (tf v)⁻¹ * u.1 v ∈ KD ((cv v) Δ) (Ov v)
      have hn : ¬ (v ∈ A.Sg ∧ v ∉ A₀.Sg) := fun h => hv h.1
      simp only [tf, dif_neg hn, inv_one, one_mul]
      exact hu₀.2 v (fun h0 => hv (hE.sub h0))
  refine ⟨y, hy, ⟨s * t, mul_mem hs htS⟩, ?_⟩
  intro h0
  apply hg
  have hsy : s * y * u = s * t * y * (t⁻¹ * u) := by
    calc s * y * u = s * (y * t) * (t⁻¹ * u) := by group
      _ = s * (t * y) * (t⁻¹ * u) := by rw [← hcomm]
      _ = s * t * y * (t⁻¹ * u) := by group
  rw [show C.ι γ * s * y * u = C.ι γ * (s * y * u) by group, hφ.1 γ (s * y * u), hsy, hinv _ hj]
  rw [show φ (s * t * y) = 0 from h0, map_zero]

end
