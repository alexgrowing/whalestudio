import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransferAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.ScalarOfCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrinciple
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem charpoly_of_scalar {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (c : ℂ) (hf : ∀ v, f v = c • v) :
    f.charpoly = (X - C c) ^ Module.finrank ℂ V := by
  have e : LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f
      = Matrix.diagonal fun _ => c := by
    ext i j
    simp [LinearMap.toMatrix_apply, hf, Matrix.diagonal_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), e, Matrix.charpoly_diagonal]
  simp

theorem UpperTheory.Gal.NearKilling.splitOff :
    SplitOff := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ z c γ q hq hcj h1 h2 h3
  classical
  set f := z.ρ (ineIncl h γ) with hf
  let U : Submodule ℂ V := Module.End.eigenspace f (c γ)
  let R : Submodule ℂ V := LinearMap.range (f - c γ • (1 : Module.End ℂ V))
  let Q : Submodule ℂ V := LinearMap.ker (aeval f q)
  have hUq : ∀ v ∈ U, aeval f q v = q.eval (c γ) • v := fun v hv => by
    by_cases h0 : v = 0
    · simp [h0]
    · exact Module.End.aeval_apply_of_hasEigenvector ⟨hv, h0⟩
  have hUs : ∀ v ∈ U, ∀ s : ↥(Ine (F := E) A), z.ρ (ineIncl h s) v = c s • v := fun v hv s => by
    have k := LinearMap.congr_fun (h1 s) v
    rw [Module.End.mul_apply, hUq v hv, map_smul] at k
    have k2 := (smul_eq_zero.1 k).resolve_left hq
    simpa [sub_eq_zero] using k2
  have hUQ : ∀ v, v ∈ U → v ∈ Q → v = 0 := fun v hv hv' => by
    have k : aeval f q v = 0 := hv'
    rw [hUq v hv] at k
    exact (smul_eq_zero.1 k).resolve_left hq
  have hRQ : R ≤ Q := by
    rintro _ ⟨u, rfl⟩
    exact LinearMap.congr_fun (h2 γ) u
  have hUR : IsCompl U R := by
    refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 ?_
    · have := LinearMap.finrank_range_add_finrank_ker (f - c γ • (1 : Module.End ℂ V))
      rw [← Module.End.eigenspace_def] at this
      change Module.finrank ℂ R + Module.finrank ℂ U = _ at this
      omega
    · exact Submodule.disjoint_def.2 fun v hv hv' => hUQ v hv (hRQ hv')
  have hQR : Q ≤ R := fun v hv => by
    have : v ∈ U ⊔ R := by rw [hUR.sup_eq_top]; trivial
    obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.1 this
    have hu' : u ∈ Q := by
      have := Q.sub_mem hv (hRQ hr)
      simpa using this
    rw [hUQ u hu hu', zero_add]
    exact hr
  have hc : IsCompl Q U := by
    rw [le_antisymm hQR hRQ]
    exact hUR.symm
  have hU : ∀ σ, ∀ v ∈ U, z.ρ σ v ∈ U := fun g v hv => by
    have e : f (z.ρ g v) = z.ρ g (z.ρ (ineIncl h (ineConj g⁻¹ γ)) v) := by
      rw [hf, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ineIncl_ineConj]
      simp [mul_assoc]
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [e, hUs v hv, hcj, map_smul]
  have hQ : ∀ σ, ∀ v ∈ Q, z.ρ σ v ∈ Q := fun g v hv => by
    obtain ⟨u, rfl⟩ := hQR hv
    have e : z.ρ g ((f - c γ • (1 : Module.End ℂ V)) u)
        = (z.ρ (ineIncl h (ineConj g γ)) - c (ineConj g γ) • (1 : Module.End ℂ V)) (z.ρ g u) := by
      have e1 : z.ρ (ineIncl h (ineConj g γ)) (z.ρ g u) = z.ρ g (f u) := by
        rw [hf, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ineIncl_ineConj]
        simp [mul_assoc]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, e1, hcj]
    show aeval f q _ = 0
    rw [e]
    exact LinearMap.congr_fun (h2 (ineConj g γ)) (z.ρ g u)
  let a := z.resZero Q hQ
  let b := z.resZero U hU
  let e := Submodule.prodEquivOfIsCompl Q U hc
  have hb : ∀ (s : ↥(Ine (F := E) A)) (v : U), b.ρ (ineIncl h s) v = c s • v := fun s v =>
    Subtype.ext (hUs v v.2 s)
  have ha : ∀ v, a.ρ (ineIncl h γ) v = c γ • v → v = 0 := fun v hv => by
    have k : z.ρ (ineIncl h γ) (v : V) = c γ • (v : V) := congrArg Subtype.val hv
    exact Subtype.ext (hUQ v (Module.End.mem_eigenspace_iff.2 k) v.2)
  have hg : ∀ σ v, e.symm (z.ρ σ v) = (a.sum b).ρ σ (e.symm v) := fun σ v => by
    obtain ⟨p, rfl⟩ := e.surjective v
    rw [e.symm_apply_apply, LinearEquiv.symm_apply_eq]
    simp [e, a, b, Submodule.coe_prodEquivOfIsCompl', WDRep.resZero]
  have h0 : ∀ v, z.N (e.symm.symm (0, v)) = 0 := fun v => by
    have k : e.symm.symm (0, v) = (v : V) := by simp [e, Submodule.coe_prodEquivOfIsCompl']
    rw [k]
    exact h3 v (hUs v v.2)
  obtain ⟨a', ea⟩ := UpperTheory.GalN.exists_sum z a b e.symm hg rfl (ineIncl h γ) (deg_ineIncl _) (c γ) (hb γ) ha h0
  have hbc : ∀ s : ↥(Ine (F := E) A), (b.ρ (ineIncl h s)).charpoly = (X - C (c s)) ^ Module.finrank ℂ U :=
    fun s => charpoly_of_scalar _ _ (hb s)
  have hm : f.charpoly.rootMultiplicity (c γ) = Module.finrank ℂ U := by
    have k := z.charpoly_eq_mul_of_isCompl Q U hQ hU hc (ineIncl h γ)
    have hne := (LinearMap.charpoly_monic (a.ρ (ineIncl h γ))).ne_zero
    have hroot : ¬ (a.ρ (ineIncl h γ)).charpoly.IsRoot (c γ) := fun hr => by
      have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hr
      obtain ⟨v, hv, hv0⟩ := hev.exists_hasEigenvector
      exact hv0 (ha v (Module.End.mem_eigenspace_iff.1 hv))
    rw [hf, k]
    show ((a.ρ (ineIncl h γ)).charpoly * (b.ρ (ineIncl h γ)).charpoly).rootMultiplicity (c γ) = _
    rw [hbc γ, rootMultiplicity_mul (mul_ne_zero hne ((monic_X_sub_C _).pow _).ne_zero),
      rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero hroot, zero_add]
  rw [hm]
  refine ⟨WD.mk a', WD.mk b, by rw [WD.lpSum_mk]; exact ea, WD.lpDim_mk b, (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 rfl, fun σ hσ => ?_⟩
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk]
  exact hbc ⟨σ, hσ⟩
