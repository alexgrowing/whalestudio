import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLatticeVacuumMemSpanFixedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeEqUnitaryMulIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassTranslateSumMemSpanSelfDualLatticeVacuaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntUnitaryOfGramClassStatement

noncomputable section

namespace GlobalTheory.Hk3.HoweG

theorem gramClass_orbit_mod_lower : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweDuality.latIdx y < GlobalTheory.Hk3.HoweDuality.latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs hvac hspan x hx
  classical
  obtain ⟨C, c, hxC, hC, hpw, hsum⟩ := GlobalTheory.T.gram_class_translate_sum_mem_span_selfDual_lattice_vacua L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac x hx
  have hψ0 : ∀ e : L, ψ e ≠ 0 := fun e h => by
    have h2 : ψ e * ψ (-e) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [h, zero_mul] at h2; exact zero_ne_one h2
  have hint_mul : ∀ (u : Matrix (Fin n') (Fin n) L) (k : GL (Fin n) L), (∀ i j, u i j ∈ Formalism.UG.intL L) →
      k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ∀ i j, (u * (k : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := by
    intro u k hu hk i j
    obtain ⟨k0, rfl⟩ := hk
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hu i l) ((k0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) l j).2

  have hvacSS : Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} ≤
      Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s) := by
    rw [Submodule.span_le]
    rintro w ⟨a, ha, hw⟩
    obtain ⟨g, k, hk, hak⟩ := GlobalTheory.T.selfDual_lattice_eq_unitary_mul_integralGL L ϖ σ q n JS hP.unr hP.odd hP.intS hP.hermS a ha
    have hw' : GlobalTheory.Hk3.LocVac ρ (ω (g⁻¹, 1) w) := by
      intro u hu
      have h1 := hP.norm g⁻¹ 1 (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
      have h2 : ρ (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w := by
        have := hw (u * (k : Matrix (Fin n) (Fin n) L)) (hint_mul u k hu hk)
        rw [hak] at this
        simpa [Matrix.mul_assoc, mul_inv_rev] using this
      have h3 := congrArg (fun F : Module.End ℂ M => F w) h1
      simp only [Module.End.mul_apply, h2] at h3
      have e : (((1 : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *
          (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          ((((g⁻¹ : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = u := by
        rw [Subgroup.coe_inv, inv_inv, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [e] at h3
      exact h3.symm
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (GlobalTheory.T.localLatticeVacuum_mem_span_fixed L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac hspan _ hw')
    have hww : w = t • ω (g, 1) s := by
      have e1 : ω (g, 1) (ω (g⁻¹, 1) w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one,
          Module.End.one_apply]
      rw [← e1, ← ht, map_smul]
    rw [SetLike.mem_coe, hww]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  refine ⟨∑ y ∈ C, c y • ρ y s, hvacSS hsum,
    ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y ≠ GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun y hy => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, ?_, rfl⟩)
    obtain ⟨hyC, hne⟩ := Finset.mem_filter.1 hy
    exact lt_of_le_of_ne (GlobalTheory.T.matrixLatticeIndex_le_of_integral_kernel L ϖ σ q n' n x y hP.unr (hC y hyC).2.1.1) hne
  have hsplit : ∑ y ∈ C, c y • ρ y s - ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y ≠ GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s =
      ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s := by
    rw [← Finset.sum_filter_add_sum_filter_not C (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x)]
    exact add_sub_cancel_right _ _
  rw [hsplit]

  have hshift : ∀ y y' : Matrix (Fin n') (Fin n) L, (∀ i j, (y - y') i j ∈ Formalism.UG.intL L) → ∃ ζ : ℂ, ζ ≠ 0 ∧ ρ y' s = ζ • ρ y s := by
    intro y y' hl
    refine ⟨ψ ((GlobalTheory.Hk3.locH σ δ JS JT y' (y - y') + σ (GlobalTheory.Hk3.locH σ δ JS JT y' (y - y'))) / 2), hψ0 _, ?_⟩
    have h1 := congrArg (fun F : Module.End ℂ M => F s) (hP.rho_mul y' (y - y'))
    simp only [Module.End.mul_apply, hvac _ hl, LinearMap.smul_apply, add_sub_cancel] at h1
    exact h1
  refine ⟨Submodule.sum_mem _ fun y hy => ?_, ?_⟩
  · obtain ⟨hyC, heq⟩ := Finset.mem_filter.1 hy
    obtain ⟨h, hh, hyl⟩ := GlobalTheory.T.exists_intUnitary_of_gramClass_alt L ϖ σ q n n' JS JT hP.unr hP.odd hP.intS hP.intT hP.hermS hP.hermT x y hx (hC y hyC).2.1 (hC y hyC).2.2 heq
    obtain ⟨ζ, hζ, hζe⟩ := hshift y (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) hyl
    have : ρ y s = ζ⁻¹ • ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s := by
      rw [hζe, smul_smul, inv_mul_cancel₀ hζ, one_smul]
    rw [this, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, hh, rfl⟩)
  ·
    have hI := GlobalTheory.Hk3.locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac
    set P := C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x) with hPdef
    have hxP : x ∈ P := Finset.mem_filter.2 ⟨hxC, rfl⟩
    set F := fun cl : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = cl ∧ w = ρ x s} with hF
    have hmem : ∀ y : Matrix (Fin n') (Fin n) L, ∀ t : ℂ, t • ρ y s ∈ F (QuotientAddGroup.mk y) :=
      fun y t => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl, rfl⟩)
    have hrest : ∑ y ∈ P.erase x, c y • ρ y s ∈ ⨆ (j) (_ : j ≠ (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n)), F j := by
      refine Submodule.sum_mem _ fun y hy => ?_
      have hyx : y ≠ x := Finset.ne_of_mem_erase hy
      have hyC : y ∈ C := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hy)).1
      have hne : (QuotientAddGroup.mk y : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ≠ QuotientAddGroup.mk x := by
        intro he
        apply hpw y hyC x hxC hyx
        have := (QuotientAddGroup.eq).1 he.symm
        have h2 : y - x = -x + y := by abel
        rw [h2]; exact this
      exact (le_iSup₂_of_le (QuotientAddGroup.mk y) hne le_rfl : F (QuotientAddGroup.mk y) ≤ _) (hmem y (c y))
    intro h0
    rw [← Finset.add_sum_erase P _ hxP] at h0
    have hxx : c x • ρ x s = 0 := by
      have hd := (hI (QuotientAddGroup.mk x))
      rw [Submodule.disjoint_def] at hd
      apply hd _ (hmem x (c x))
      have : c x • ρ x s = -(∑ y ∈ P.erase x, c y • ρ y s) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact neg_mem hrest
    have hcx := (hC x hxC).1
    rw [smul_eq_zero] at hxx
    rcases hxx with h | h
    · exact hcx h
    · apply hs
      have h1 := congrArg (fun F : Module.End ℂ M => F s) (hP.rho_mul (-x) x)
      simp only [Module.End.mul_apply, h, map_zero, neg_add_cancel, hP.rho_zero, LinearMap.smul_apply, Module.End.one_apply] at h1
      exact (smul_eq_zero.1 h1.symm).resolve_left (hψ0 _)

end GlobalTheory.Hk3.HoweG

end
