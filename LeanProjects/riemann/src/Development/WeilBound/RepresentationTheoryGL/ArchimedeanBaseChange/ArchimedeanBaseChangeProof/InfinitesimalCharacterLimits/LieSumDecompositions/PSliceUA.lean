import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceF

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm PositivityTheory.Rg.Rs.SliceClasses

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.LieSumUnipotentSlice

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem F_slicesU (V : Submodule ℂ (Sm E (r + s))) (hVs : IsStable V) (hVa : ∀ φ ∈ V, IsAutForm φ)
    (hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s))
    (hequiv : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) (τs : Finset ℝ) (a : ℝ → ℂ)
    (hTval : ∀ φ ∈ V, ∀ g, (T φ).1 g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (φ : Sm E (r + s)) (hφ : φ ∈ V) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    (∀ m₂, ∃ ψ : Sm E r, IsAutForm ψ ∧ ∀ m₁, ψ.1 m₁ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) ∧
    (∀ m₁, ∃ ψ : Sm E s, IsAutForm ψ ∧ ∀ m₂, ψ.1 m₂ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := by
  have hAφ := hVa φ hφ

  have hN : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (T φ).1 (unip x * g) = (T φ).1 g := by
    intro x g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    rw [← mul_assoc, hy, mul_assoc, ctn_unip hAφ]

  have hM : ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)),
      (T φ).1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = (T φ).1 g := by
    intro γ g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_assoc, aT_comm_lev, mul_assoc, ctn_lev_rat hAφ]

  let L := GlobalTheory.DiscClosure.stabSub φ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAφ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T φ) = T φ := fun h hh => by
    have e := hequiv (.fin h) φ hφ
    have hh' : finRep E (r + s) h φ = φ := hh
    change T (finRep E (r + s) h φ) = finRep E (r + s) h (T φ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T φ)
  haveI : FiniteDimensional ℂ S := by
    haveI := hAφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ φ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hequiv (.cpt κ) φ hφ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T φ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T φ)).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T φ, Submodule.subset_span ⟨1, by simp⟩⟩ g

  have hG : ∀ g₀ : GA E (r + s), ∃ (C : ℝ) (n : ℕ), ∀ y, ‖(T φ).1 (g₀ * infGL E (r + s) y)‖ ≤ C * height y ^ n := by
    intro g₀
    choose C n hCn using fun t => ctn_growth hAφ r (aT E (r + s) r t * g₀)
    refine ⟨∑ t ∈ τs, ‖a t‖ * |C t|, ∑ t ∈ τs, n t, fun y => ?_⟩
    rw [hTval φ hφ, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
    have hy := one_le_height y
    have e1 : height y ^ n t ≤ height y ^ (∑ t ∈ τs, n t) :=
      pow_le_pow_right₀ hy (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht)
    have hp : (0 : ℝ) ≤ height y ^ n t := pow_nonneg (by linarith) _
    calc ‖a t * An.ctn r φ.1 (aT E (r + s) r t * (g₀ * infGL E (r + s) y))‖
        = ‖a t‖ * ‖An.ctn r φ.1 (aT E (r + s) r t * g₀ * infGL E (r + s) y)‖ := by rw [norm_mul, mul_assoc]
      _ ≤ ‖a t‖ * (C t * height y ^ n t) := mul_le_mul_of_nonneg_left (hCn t y) (norm_nonneg _)
      _ ≤ ‖a t‖ * (|C t| * height y ^ (∑ t ∈ τs, n t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self _) e1 hp (abs_nonneg _)) (norm_nonneg _)
      _ = ‖a t‖ * |C t| * height y ^ (∑ t ∈ τs, n t) := by ring

  choose cc hcc using hsc
  let J : Set (Module.End ℂ (Sm E (r + s))) :=
    {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r + s) τ u) (Polynomial.X - Polynomial.C (cc τ u))}
  have hJZ : J ⊆ Zalg E (r + s) := by
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  have hJ : Cofin J := GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic E (r + s) J hJZ fun τ u =>
    ⟨_, Polynomial.monic_X_sub_C _, τ, u, rfl⟩
  have hZ : ∀ z ∈ J, z (T φ) = 0 := by
    rintro _ ⟨τ, u, rfl⟩
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
    rw [← GlobalTheory.SpehInfChar.cap_comm_quot (fun X ψ hψ => hVs (.lie X) ψ hψ) T hequiv τ u φ hφ,
      hcc τ u φ hφ, map_smul, sub_self]
  have hgood : T φ ∈ goodCT L ρ J := ⟨hN, hM, hLv, hC, hG, hZ⟩
  obtain ⟨J₁, J₂, c₁, c₂, k₁, k₂⟩ := centre J hJ
  have e : ∀ m : GA E r × GA E s, lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g) =
      lev (Ad E) r s m * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits k) := by
    intro m
    rw [infGL_comm, mul_assoc]
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨L₁, ρ₁, -, -, h⟩ := Slice1.slice_mem_genSpace E r s L hLo S ρ hρ J hJ J₁ c₁ k₁ g k
    obtain ⟨G, hG, hG'⟩ := h (T φ) hgood m₂
    exact ⟨G, hG.1, fun m₁ => by rw [hG', e]⟩
  · obtain ⟨L₂, ρ₂, -, -, h⟩ := Slice2.slice2 E r s L hLo S ρ hρ J hJ J₂ c₂ k₂ g k
    obtain ⟨G, hG, hG'⟩ := h (T φ) hgood m₁
    exact ⟨G, hG.1, fun m₂ => by rw [hG', e]⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.LieSumUnipotentSlice

end
