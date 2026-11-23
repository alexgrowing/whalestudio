import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieSkewAdjointMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2Bounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalKTypeFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSmoothModuleUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFiniteVectorsHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalFormL2Mem
import GroundTheory.PAdicHodge.ACrisBdR

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.IrredMod
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.FinitePart

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem enoughCompact_Rcusp : EnoughCompact (Rcusp μ) := by
  intro v hv
  obtain ⟨N, hN, h⟩ := exists_nhds_repOp_ne_zero μ (isUnitaryRep_Rcusp μ) hv
  obtain ⟨φ, hφ, hs, h0, h1, hsupp⟩ := GlobalTheory.CompanionTheory.Bump.exists_nonneg_bump (1 : GA E a) N hN
  have hf : Continuous fun g => (φ g : ℂ) := Complex.continuous_ofReal.comp hφ
  have hfs : HasCompactSupport fun g => (φ g : ℂ) := hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  exact ⟨_, GlobalTheory.T.cuspidal_convolution_compact E a μ _ hf hfs, fun S hS x =>
    (DFunLike.congr_fun ((isUnitaryRep_Rcusp μ).comp_repOp (isUnitaryRep_Rcusp μ) hf hfs S hS.2) x).symm,
    h φ hφ hs h0 h1 hsupp⟩

theorem exists_irred_le {C : Submodule ℂ (L2 (latticeGL E a) μ)} (hC : IsSubrep (R (latticeGL E a) μ) C)
    (hCc : C ≤ L2cusp μ) (h0 : C ≠ ⊥) : ∃ H ≤ C, IsIrredSubrep (R (latticeGL E a) μ) H := by
  have e : (C.comap (L2cusp μ).subtype).map (L2cusp μ).subtype = C := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hCc]
  have hW : IsSubrep (Rcusp μ) (C.comap (L2cusp μ).subtype) :=
    (isSubrep_L2cusp μ).isSubrep_rep_iff.2 (e.symm ▸ hC)
  have hW0 : C.comap (L2cusp μ).subtype ≠ ⊥ := fun hb => h0 (by rw [← e, hb, Submodule.map_bot])
  obtain ⟨X, hX, hi⟩ := enoughCompact_Rcusp.exists_irred_le (isUnitaryRep_Rcusp μ) hW hW0
  exact ⟨X.map (L2cusp μ).subtype, e ▸ Submodule.map_mono hX, isIrredSubrep_map hi⟩

open GlobalTheory.ExpDeriv in

theorem lie_mem {Z : Submodule ℂ (L2 (latticeGL E a) μ)} (hZ : IsSubrep (R (latticeGL E a) μ) Z)
    {W : Submodule ℂ (Sm E a)} (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E a) μ φ.1) (hW : IsStable W)
    (hA : ∀ φ ∈ W, IsAutForm φ) (X : Lie E a) (φ : W) (hφ : toL2ₗ μ W h φ ∈ Z) :
    toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩ ∈ Z := by
  have := hZ.completeSpace
  rw [← Submodule.orthogonal_orthogonal Z]
  refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
  set c : ℝ → GA E a := fun t => infGL E a (expGL X t) with hcdef
  have hc : Continuous c := by
    have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Matrix.of X) := by
      open scoped Matrix.Norms.Operator in
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have hinv : ∀ t, (expGL X t)⁻¹ = expGL X (-t) := fun t =>
      (eq_inv_of_mul_eq_one_right (by rw [← expGL_add, add_neg_cancel, expGL_zero])).symm
    have he : Continuous (expGL X) := Units.continuous_iff.2 ⟨hv, by
      simp only [hinv, expGL_val]
      exact hv.comp continuous_neg⟩
    exact GlobalTheory.CuspQuot.continuous_infGL.comp he
  have hc0 : c 0 = 1 := by simp only [c, expGL_zero, map_one]
  have hcont : ∀ θ ∈ W, Continuous (θ : GA E a → ℂ) := fun θ hθ =>
    ContAut.continuous_of_isOpen_stab E a θ (hA θ hθ).level
  have dF := GlobalTheory.LieSkew.hasDerivAt_inner_R (latticeGL E a) μ c hc hc0 (h φ φ.2) (h _ (hW (.lie X) φ.1 φ.2))
    (hcont _ (hW (.lie X) φ.1 φ.2)) (fun x t => hasDerivAt_along X φ.1 x t) u
  have e : (fun t => inner ℂ u (R (latticeGL E a) μ (c t) (h φ φ.2).toL2)) = fun _ => 0 := funext fun t =>
    (Submodule.mem_orthogonal' _ _).1 hu _ (hZ.2 _ _ hφ)
  rw [e] at dF
  exact dF.unique (hasDerivAt_const _ _)

theorem eq_zero_of_mem_orthogonal {π : CuspSub E a} (hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1)
    {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : IsSubrep (R (latticeGL E a) μ) H) (h0 : H ≠ ⊥)
    (hle : H ≤ (classes π.V μ).topologicalClosure) (ψ : π.V) (hψ : toL2ₗ μ π.V hm ψ ∈ Hᗮ) : ψ = 0 := by
  have hZ : IsSubrep (R (latticeGL E a) μ) Hᗮ := hH.orthogonal (isUnitaryRep_R (latticeGL E a) μ)
  let N : Submodule ℂ (Sm E a) := (Hᗮ.comap (toL2ₗ μ π.V hm)).map π.V.subtype
  have hNs : IsStable N := by
    rintro o _ ⟨θ, hθ, rfl⟩
    cases o with
    | fin k =>
      have h2 := hZ.2 (finGL E a k) _ (show toL2ₗ μ π.V hm θ ∈ Hᗮ from hθ)
      rw [R_toL2ₗ hm θ (π.stable (.fin k) _ θ.2)] at h2
      exact ⟨⟨_, π.stable (.fin k) _ θ.2⟩, h2, rfl⟩
    | cpt k =>
      have h2 := hZ.2 (((infGL E a).comp Unitary.toUnits) k) _ (show toL2ₗ μ π.V hm θ ∈ Hᗮ from hθ)
      rw [R_toL2ₗ hm θ (π.stable (.cpt k) _ θ.2)] at h2
      exact ⟨⟨_, π.stable (.cpt k) _ θ.2⟩, h2, rfl⟩
    | lie X => exact ⟨⟨_, π.stable (.lie X) _ θ.2⟩,
        lie_mem hZ hm π.stable (fun φ hφ => (π.cusp φ hφ).1) X θ hθ, rfl⟩
  rcases π.irred N (Submodule.map_subtype_le _ _) hNs with hb | ht
  · have : ψ.1 ∈ N := ⟨ψ, hψ, rfl⟩
    rw [hb] at this
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
  · exfalso
    have hcl : classes π.V μ ≤ Hᗮ := by
      intro F hF
      obtain ⟨θ, rfl⟩ := (range_toL2ₗ hm).ge hF
      obtain ⟨θ', hθ', e⟩ := ht.ge θ.2
      rwa [show θ = θ' from Subtype.ext e.symm]
    have hcl' : (classes π.V μ).topologicalClosure ≤ Hᗮ :=
      Submodule.topologicalClosure_minimal _ hcl hZ.1
    exact h0 (eq_bot_iff.2 fun x hx => by
      have := (Submodule.mem_orthogonal' _ _).1 (hcl' (hle hx)) x hx
      exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 this))

theorem mem_of_toL2_mem_irreducible {W : Submodule ℂ (Sm E a)} (hW : IsStable W) (hWa : ∀ φ ∈ W, IsAutForm φ)
    (hWm : ∀ φ ∈ W, MemL2Quotient (latticeGL E a) μ φ.1) {C H : Submodule ℂ (L2 (latticeGL E a) μ)}
    (hC : IsSubrep (R (latticeGL E a) μ) C) (hcl : (classes W μ).topologicalClosure = C)
    (hcusp : H ≤ L2cusp μ) (hirr : IsIrredSubrep (R (latticeGL E a) μ) H) (hHC : H ≤ C)
    (hinj : ∀ ψ : W, toL2ₗ μ W hWm ψ ∈ Hᗮ → ψ = 0)
    (φ : Sm E a) (hφ : IsAutForm φ) (h : MemL2Quotient (latticeGL E a) μ φ.1) (hH : h.toL2 ∈ H) : φ ∈ W := by
  have hn : ∀ k v, ‖piInf E a μ k v‖ = ‖v‖ := fun k v => norm_R _ v
  have hnF : ∀ k v, ‖piFin E a μ k v‖ = ‖v‖ := fun k v => norm_R _ v
  have hU' : IsUnitaryRep (R (latticeGL E a) μ) := isUnitaryRep_R (latticeGL E a) μ
  have hHs : ∀ g, ∀ v ∈ C, R (latticeGL E a) μ g v ∈ C := hC.2
  obtain ⟨U₀, hU₀o, hU₀c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | finRep E a k φ = φ}
      mul_mem' := fun {x y} hx hy => by
        change finRep E a (x * y) φ = φ
        rw [map_mul, Module.End.mul_apply, show finRep E a y φ = φ from hy, show finRep E a x φ = φ from hx]
      one_mem' := by
        change finRep E a 1 φ = φ
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {x} hx => by
        change finRep E a x⁻¹ φ = φ
        conv_lhs => rw [← show finRep E a x φ = φ from hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set (GL (Fin a) (Af E))) := hφ.level
  let U : Subgroup (GL (Fin a) (Af E)) := U₀ ⊓ S
  have hUo : IsOpen (U : Set (GL (Fin a) (Af E))) := hU₀o.inter hSo
  have hUc : IsCompact (U : Set (GL (Fin a) (Af E))) := hU₀c.inter_right (S.isClosed_of_isOpen hSo)
  have hfix : h.toL2 ∈ fixedBy μ U := fun u hu =>
    (right_translate_toL2 h _).trans (((h.mul_right _).toL2_eq_iff_ae_eq h).2 (.of_forall fun x => congrFun (congrArg Subtype.val hu.2) x))
  set Y₀ := Submodule.span ℂ (Set.range fun k : Kinf E a => piInf E a μ k h.toL2) with hY₀def
  haveI : FiniteDimensional ℂ Y₀ := finiteDimensional_span_inf hφ h
  have hY₀s : ∀ g, ∀ v ∈ Y₀, piInf E a μ g v ∈ Y₀ := span_orbit_stable _ _
  have hY₀ : Y₀ ≤ C ⊓ fixedBy μ U := span_inf_le hHs (hHC hH) hfix
  have hF0Y : h.toL2 ∈ Y₀ := Submodule.subset_span ⟨1, by simp⟩
  let ρ : Representation ℂ (Kinf E a) Y₀ := subRep (piInf E a μ) Y₀ hY₀s
  let P : L2 (latticeGL E a) μ → Prop := fun v => v ∈ C ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v
  let P₀ : L2 (latticeGL E a) μ → Prop := fun v => v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v
  let M : Submodule ℂ (L2 (latticeGL E a) μ) :=
    ⨆ (T : Y₀ →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : (∀ k w, T (ρ k w) = piInf E a μ k (T w)) ∧ ∀ w, P (T w)), LinearMap.range T
  let M₀ : Submodule ℂ (L2 (latticeGL E a) μ) :=
    ⨆ (T : Y₀ →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : (∀ k w, T (ρ k w) = piInf E a μ k (T w)) ∧ ∀ w, P₀ (T w)), LinearMap.range T
  haveI hM₀f : FiniteDimensional ℂ M₀ := GlobalTheory.T.cuspidal_K_type_finite E a μ H hcusp hirr U hUo Y₀ ρ
  have hMP : M ≤ C ⊓ fixedBy μ U := iSup₂_le fun T hT => by
    rintro _ ⟨w, rfl⟩
    exact hT.2 w
  have hF0M : h.toL2 ∈ M :=
    (le_iSup₂_of_le (f := fun (T : Y₀ →ₗ[ℂ] L2 (latticeGL E a) μ)
      (_ : (∀ k w, T (ρ k w) = piInf E a μ k (T w)) ∧ ∀ w, P (T w)) => LinearMap.range T) Y₀.subtype
      ⟨fun k w => rfl, fun w => hY₀ w.2⟩ le_rfl) ⟨⟨_, hF0Y⟩, rfl⟩
  let M' : Submodule ℂ (L2 (latticeGL E a) μ) := M ⊓ classes W μ
  haveI : CompleteSpace H := hirr.1.completeSpace
  have hPM : M ≤ M₀.comap (H.starProjection : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
    iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      refine (le_iSup₂_of_le (f := fun (T : Y₀ →ₗ[ℂ] L2 (latticeGL E a) μ)
        (_ : (∀ k w, T (ρ k w) = piInf E a μ k (T w)) ∧ ∀ w, P₀ (T w)) => LinearMap.range T)
        ((H.starProjection : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) ∘ₗ T)
        ⟨fun k w => ?_, fun w => ⟨H.starProjection_apply_mem _, fun u hu => ?_⟩⟩ le_rfl) ⟨w, rfl⟩
      · change H.starProjection (T (ρ k w)) = R (latticeGL E a) μ _ (H.starProjection (T w))
        rw [hT.1]
        exact hirr.1.starProjection_apply hU' _ _
      · change R (latticeGL E a) μ _ (H.starProjection (T w)) = H.starProjection (T w)
        rw [← hirr.1.starProjection_apply hU', (hT.2 w).2 u hu]
  let L : M' →ₗ[ℂ] M₀ := LinearMap.codRestrict M₀
    ((H.starProjection : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) ∘ₗ M'.subtype) fun x => hPM x.2.1
  have hL : Function.Injective L := (injective_iff_map_eq_zero L).2 fun x e => by
    have e0 : H.starProjection (x : L2 (latticeGL E a) μ) = 0 := congrArg Subtype.val e
    obtain ⟨ψ, hψ⟩ := (range_toL2ₗ hWm).ge x.2.2
    have h1 : toL2ₗ μ W hWm ψ ∈ Hᗮ := hψ ▸ (Submodule.starProjection_apply_eq_zero_iff _).1 e0
    refine Subtype.ext ?_
    rw [← hψ, hinj ψ h1, map_zero]
    rfl
  haveI : FiniteDimensional ℂ M' := FiniteDimensional.of_injective L hL
  have hpm : M'.starProjection h.toL2 ∈ M' := Submodule.starProjection_apply_mem _ _
  obtain ⟨m, hmdef⟩ : ∃ m, m = h.toL2 - M'.starProjection h.toL2 := ⟨_, rfl⟩
  have hmM : m ∈ M := hmdef ▸ M.sub_mem hF0M hpm.1
  have hm' : m ∈ M'ᗮ := hmdef ▸ Submodule.sub_starProjection_mem_orthogonal _
  have key : ∀ F ∈ classes W μ, ⟪m, F⟫_ℂ = 0 := by
    intro F hF
    obtain ⟨ψ, rfl⟩ := (range_toL2ₗ hWm).ge hF
    have hi := toL2ₗ_injective hWm fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (hWa ψ hψ).level
    have hop : IsOpen {g | piFin E a μ g (toL2ₗ μ W hWm ψ) = toL2ₗ μ W hWm ψ} := by
      convert (hWa ψ ψ.2).level using 1
      ext k
      exact (R_toL2ₗ hWm ψ (hW (.fin k) _ ψ.2)).congr_left.trans (hi.eq_iff.trans Subtype.ext_iff)
    obtain ⟨F', hF'c, hF'f, hF'i⟩ := exists_average (piFin E a μ) hnF U hUc hop (classes W μ)
      (fun g v hv => R_mem_classes (fun χ hχ => hW (.fin g) χ hχ) hv) hF
    rw [← hF'i m (fun u hu => (hMP hmM).2 u hu)]
    have hF'H : F' ∈ C := by
      have : classes W μ ≤ C := hcl ▸ Submodule.le_topologicalClosure _
      exact this hF'c
    have hF'U : F' ∈ fixedBy μ U := hF'f
    obtain ⟨ψ', rfl⟩ := (range_toL2ₗ hWm).ge hF'c
    haveI := finiteDimensional_span_inf (hWa ψ' ψ'.2) (hWm ψ' ψ'.2)
    obtain ⟨Y₁, hY₁⟩ : ∃ Y₁, Y₁ = Submodule.span ℂ (Set.range fun k : Kinf E a => piInf E a μ k (toL2ₗ μ W hWm ψ')) := ⟨_, rfl⟩
    haveI : FiniteDimensional ℂ Y₁ := hY₁ ▸ this
    have hY₁s : ∀ g, ∀ v ∈ Y₁, piInf E a μ g v ∈ Y₁ := hY₁ ▸ span_orbit_stable _ _
    have hY₁P : Y₁ ≤ C ⊓ fixedBy μ U := hY₁ ▸ span_inf_le hHs hF'H hF'U
    have hY₁c : Y₁ ≤ classes W μ := hY₁ ▸ Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact R_mem_classes (fun χ hχ => hW (.cpt k) χ hχ) hF'c)
    have hFY : toL2ₗ μ W hWm ψ' ∈ Y₁ := hY₁ ▸ Submodule.subset_span ⟨1, by simp⟩
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := exists_decomp ρ (piInf E a μ) hn P Y₁ hY₁s (fun v hv => hY₁P hv) hFY
    have e1 : ⟪m, x⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 hm' x ⟨hx2, hY₁c hx1⟩
    have e2 : ⟪m, toL2ₗ μ W hWm ψ' - x⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hx3 m hmM
    rw [inner_sub_right, e1, sub_zero] at e2
    exact e2
  have hm0 : m = 0 := by
    have h1 : m ∈ (classes W μ)ᗮ := (Submodule.mem_orthogonal' _ _).2 key
    rw [← Submodule.orthogonal_closure, hcl] at h1
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal' _ _).1 h1 m (hMP hmM).1)
  have hF0c : h.toL2 ∈ classes W μ := by
    have h1 : h.toL2 = M'.starProjection h.toL2 := sub_eq_zero.1 (hmdef.symm.trans hm0)
    rw [h1]
    exact hpm.2
  obtain ⟨ψ, hψ, e⟩ := hF0c
  rwa [show φ = ψ from Subtype.ext ((Continuous.ae_eq_iff_eq μ (ContAut.continuous_of_isOpen_stab E a φ hφ.level)
    (ContAut.continuous_of_isOpen_stab E a ψ (hWa ψ hψ).level)).1 (h.lift_toL2_ae_eq.symm.trans e))]

variable (μ) in

theorem exists_isFinitePartOf (π : CuspSub E a) (hπ : IsNormalised π) :
    ∃ H, IsIrredSubrep (R (latticeGL E a) μ) H ∧ IsFinitePartOf μ π H := by
  have hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1 := fun φ hφ =>
    (GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised GlobalTheory.CompanionTheory.CuspFinGL.Split.cuspFormsBoundedGL E a μ π hπ φ hφ).1
  have hWa : ∀ ψ ∈ π.V, IsAutForm ψ := fun ψ h => (π.cusp ψ h).1
  have hC : IsSubrep (R (latticeGL E a) μ) (classes π.V μ).topologicalClosure :=
    GlobalTheory.CompanionTheory.CuspIrred.isSubrep_closure π.stable fun φ h => ⟨hWa φ h, hm φ h⟩
  have hCc : (classes π.V μ).topologicalClosure ≤ L2cusp μ := closure_classes_le_L2cusp π.cusp hπ
  have hC0 : (classes π.V μ).topologicalClosure ≠ ⊥ := by
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
    refine (Submodule.ne_bot_iff _).2 ⟨_, Submodule.le_topologicalClosure _ (toL2_mem_classes hφ (hm φ hφ)),
      toL2_ne_zero (hm φ hφ) (ContAut.continuous_of_isOpen_stab E a φ (hWa φ hφ).level) fun e => h0 (Subtype.ext e)⟩
  obtain ⟨H, hHC, hi⟩ := exists_irred_le hC hCc hC0
  have hcusp : H ≤ L2cusp μ := hHC.trans hCc
  obtain ⟨π₀, hf⟩ := GlobalTheory.T.cusp_finite_vectors_holds E a μ H hcusp hi
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π₀.ne_bot
  have hφπ : φ ∈ π.V := mem_of_toL2_mem_irreducible π.stable hWa hm hC rfl hcusp hi hHC
    (fun ψ hψ => eq_zero_of_mem_orthogonal hm hi.1 hi.2.1 hHC ψ hψ) φ (π₀.cusp φ hφ).1 (hf.finitePartMemL2 φ hφ)
    (hf.classes_le (toL2_mem_classes hφ (hf.finitePartMemL2 φ hφ)))
  have hs : IsStable (π₀.V ⊓ π.V) := fun o ψ h => ⟨π₀.stable o ψ h.1, π.stable o ψ h.2⟩
  have hne : π₀.V ⊓ π.V ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨φ, ⟨hφ, hφπ⟩, h0⟩
  have e0 := (π₀.irred _ inf_le_left hs).resolve_left hne
  have e1 := (π.irred _ inf_le_right hs).resolve_left hne
  have e : π₀ = π := CuspSub.ext (e0.symm.trans e1)
  exact ⟨H, hi, e ▸ hf⟩

theorem g14 : PositivityTheory.jumpWindows.CuspidalIrreducibleSubrep := fun _ _ _ _ _ μ _ _ π hπ => exists_isFinitePartOf μ π hπ

theorem g14_of_meet : PositivityTheory.jumpWindows.Meet → PositivityTheory.jumpWindows.CuspidalIrreducibleSubrep := fun _ => g14

end GlobalTheory.CompanionTheory.FinitePart

end
