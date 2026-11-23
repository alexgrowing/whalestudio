import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequalityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartFormStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.toPolyX_pf :
    UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.ToPolyX := by
  intro hPF E _ _ _ l _ ι a w₀ K hK lam P hD Jx t η hFr hact U hU ε hε
  classical
  obtain ⟨W, f, hW, hf0, hfU, hfK, -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam K U hK hU w₀
  have hWe : Wt.ofFam lam = W := funext fun v => by
    show lam v.embedding = W v
    rw [← hW, Wt.at_embedding]
  rw [hWe] at hD hFr
  obtain ⟨X, b, hbd, hdef, hne⟩ := hFr
  obtain ⟨g₀, i₀, hz⟩ : ∃ g i, f.1 (b g i) g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (hdef f h)
  set z₀ := f.1 (b g₀ i₀) g₀ with hz₀
  let f₁ : algForms W := z₀⁻¹ • f
  have hf₁ : ∀ v g, f₁.1 v g = z₀⁻¹ * f.1 v g := fun v g => rfl
  have hf₁K : f₁ ∈ fixedBy W K := fun k hk v g => by rw [hf₁, hf₁, hfK k hk v g]
  have hf₁U : ∀ v, f₁.1 v ∈ U := fun v => U.smul_mem _ (hfU v)
  obtain ⟨R₀, hR₀⟩ := hbd f₁
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : ∀ g i, ‖ι.symm (f₁.1 (b g i) g)‖ ≤ R := fun g i => (hR₀ g i).trans (le_max_left _ _)
  obtain ⟨G, hG, e, he, hfe⟩ := hD f₁ hf₁K (ε / R) (div_pos hε hRpos)
  obtain ⟨I, F, hI, hsum⟩ := (hPF E a W K P).2.2.2.2 G hG
  let T : Jx → Module.End ℂ (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun j =>
    LinearMap.llcomp ℂ W.Sp (UA E a → ℂ) (UA E a → ℂ) (GlobalTheory.CongSc.opL (t j))
  let ev : UA E a × X → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) →ₗ[ℂ] ℂ := fun x =>
    (LinearMap.proj x.1) ∘ₗ (LinearMap.applyₗ (b x.1 x.2))
  have hT : ∀ j (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v, T j F' v = opOf (RU E a) (t j) (F' v) := fun _ _ _ => rfl
  have hev : ∀ x (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)), ev x F' = F' (b x.1 x.2) x.1 := fun _ _ => rfl
  have hne' : ∀ (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) (R' : ℝ), (∀ x, ‖ι.symm (ev x F')‖ ≤ R') →
      ∀ j x, ‖ι.symm (ev x (T j F'))‖ ≤ R' := fun F' R' hR' j x =>
    hne F' R' (fun g i => hR' (g, i)) j x.1 x.2
  have heig0 : ∀ j, T j f₁.1 = η U j • f₁.1 := by
    intro j; apply LinearMap.ext; intro v
    rw [hT, LinearMap.smul_apply]
    exact hact U hU.aut (f₁.1 v) (hf₁U v) (fun x hx => funext fun g => hf₁K x hx v g) j
  have hnorm : ‖ι.symm (ev (g₀, i₀) f₁.1)‖ = 1 := by
    have : ev (g₀, i₀) f₁.1 = 1 := by
      rw [hev]
      show z₀⁻¹ * f.1 (b g₀ i₀) g₀ = 1
      exact inv_mul_cancel₀ hz
    rw [this, map_one, norm_one]
  let vv : ↥I → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun π => -(F π.1).1
  let η' : ↥I → Jx → ℂ := fun π => η π.1.V
  have heig : ∀ π j, T j (vv π) = η' π j • vv π := by
    rintro ⟨π, hπ⟩ j
    obtain ⟨-, hfin, hfix, -⟩ := hI π hπ
    have h : T j (F π).1 = η π.V j • (F π).1 := by
      apply LinearMap.ext; intro v
      rw [hT, LinearMap.smul_apply]
      exact hact π.V π.isAut _ (AutSub.mem_finPart.1 hfin v)
        (fun x hx => funext fun g => hfix x hx v g) j
    show T j (-(F π).1) = η π.V j • -(F π).1
    rw [map_neg, h, smul_neg]
  have hvsum : f₁.1 + ∑ π, vv π = f₁.1 - G.1 := by
    have h1 : ∑ π, vv π = -G.1 := by
      simp only [vv]
      rw [Finset.sum_neg_distrib, Finset.sum_coe_sort I (fun π => (F π).1), hsum, Submodule.coe_sum]
    rw [h1, sub_eq_add_neg]
  have hbound : ∀ x, ‖ι.symm (ev x (f₁.1 + ∑ π, vv π))‖ ≤ ε := by
    intro x
    have h1 : ev x (f₁.1 + ∑ π, vv π) = e x.1 * f₁.1 (b x.1 x.2) x.1 := by
      rw [hvsum, hev]
      exact hfe _ _
    rw [h1, map_mul, norm_mul]
    calc ‖ι.symm (e x.1)‖ * ‖ι.symm (f₁.1 (b x.1 x.2) x.1)‖ ≤ ε / R * R :=
          mul_le_mul (he _) (hR _ _) (norm_nonneg _) (div_pos hε hRpos).le
      _ = ε := div_mul_cancel₀ _ hRpos.ne'
  obtain ⟨s, c, hs, hP⟩ := GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality l ι (W.Sp →ₗ[ℂ] (UA E a → ℂ)) (UA E a × X) Jx
    ↥I T ev hne' f₁.1 (η U) (g₀, i₀) heig0 hnorm vv η' heig ε hbound
  refine ⟨s, c, ?_, hP⟩
  intro z hz'
  obtain ⟨⟨π, hπ⟩, rfl⟩ := hs z hz'
  obtain ⟨hPπ, hfin, hfix, hF0⟩ := hI π hπ
  refine ⟨π.V, ?_, hPπ, rfl⟩
  have h := GlobalTheory.T.isAutomorphicOfWeight_of_nonzero_fixed_finPart_form E a π W K (F π) hfin hF0 (fun k hk v g => hfix k hk v g)
  have hl' : (fun τ => W.at τ) = lam := funext hW
  rwa [hl'] at h
