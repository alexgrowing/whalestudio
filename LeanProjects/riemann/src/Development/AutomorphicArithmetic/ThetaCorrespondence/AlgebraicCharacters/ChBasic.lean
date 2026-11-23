import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
open UpperTheory.Lit.CharWD GlobalTheory.Published
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open GlobalTheory.LocLanglands GlobalTheory.Pst GlobalTheory.TripleGal UpperTheory.V.W

private theorem continuous_rank_one_rep {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] (μ : Γ →* Kˣ)
    (hμ : Continuous μ) : Continuous fun g => ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i; fin_cases j
  simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using Units.continuous_val.comp hμ

private theorem exists_char {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (x : WD h) (hx : x.lpDim = 1) :
    ∃ (η : Weil h →* ℂˣ) (hη : IsSmooth η), x = WD.lpOfChar h η hη := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  obtain rfl : n = 1 := by simpa using hx
  have hsc : ∀ f : Module.End ℂ (Fin 1 → ℂ), ∀ v, f v = f 1 0 • v := fun f v => by
    have hv : v = v 0 • (1 : Fin 1 → ℂ) := by
      funext i; rw [Subsingleton.elim i 0]; simp
    funext i
    rw [Subsingleton.elim i 0]
    conv_lhs => rw [hv, map_smul]
    simp [mul_comm]
  let c : Weil h →* ℂ :=
    { toFun := fun σ => b.ρ σ 1 0
      map_one' := by simp
      map_mul' := fun σ τ => by
        rw [map_mul, Module.End.mul_apply, hsc (b.ρ σ) (b.ρ τ 1)]; simp }
  have hker : ∀ σ, b.ρ σ = 1 → c.toHomUnits σ = 1 := fun σ hσ => by
    ext
    show b.ρ σ 1 0 = 1
    simp [hσ]
  refine ⟨c.toHomUnits, b.smooth.of_le hker, ParamAboveModel.eq_lpOfChar h _ hx _ _ fun σ => ?_⟩
  rw [WD.eig_mk, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  exact Module.End.hasEigenvalue_of_hasEigenvector (x := 1)
    ⟨Module.End.mem_eigenspace_iff.mpr (hsc _ _), one_ne_zero⟩

theorem UpperTheory.Lit.CharWD.chBasic :
    ChBasic := by
  intro F Ω _ _ _ _ _ l _ A w ι h O _ _ _ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have eigW : ∀ κ ξ, WDis (UpperTheory.V.Loc.PP l) ι h Bw hj κ ξ → ∀ σ,
      (wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (rk1 κ)).eig σ = {ι (ξ σ : Qbar l)} := by
    rintro κ ξ ⟨-, hs, e⟩ σ
    rw [e, eig_lpOfChar]
    rfl
  refine ⟨fun κ _ hp => ?_, ?_, ?_⟩
  · obtain ⟨η, hη, e⟩ := exists_char _ (GlobalTheory.Pst.Test.lpDim_wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (rk1 κ))
    have hc : (Units.map ι.toRingHom.toMonoidHom).comp ((Units.map ι.symm.toRingHom.toMonoidHom).comp η) = η := by
      ext σ
      simp
    have H : WDis (UpperTheory.V.Loc.PP l) ι h Bw hj κ ((Units.map ι.symm.toRingHom.toMonoidHom).comp η) :=
      ⟨hp, hc.symm ▸ hη, by rw [e]; congr 1; exact hc.symm⟩
    refine ⟨_, H, fun ξ H' => MonoidHom.ext fun σ => Units.ext (ι.injective ?_)⟩
    exact Multiset.singleton_inj.mp ((eigW _ _ H' σ).symm.trans (eigW _ _ H σ))
  · intro κ κ' ξ ξ' hκ hκ' H H' hp
    have htw : rk1 (κ * κ') = Formalism.MainNotions.SumRepresentations.At.twGL (rk1 κ) (Matrix.GeneralLinearGroup.det.comp (rk1 κ')) := by
      ext g i j
      fin_cases i; fin_cases j
      simp [Formalism.MainNotions.SumRepresentations.At.twGL, GlobalTheory.TripleGal.rk1, mul_comm, Matrix.algebraMap_matrix_apply]
    have hs : IsSmooth ((Units.map ι.toRingHom.toMonoidHom).comp (ξ * ξ')) :=
      H.2.choose.of_le₂ H'.2.choose fun σ h1 h2 => by
        rw [MonoidHom.comp_apply] at h1 h2 ⊢
        rw [MonoidHom.mul_apply, map_mul, h1, h2, mul_one]
    refine ⟨hp, hs, ParamAboveModel.eq_lpOfChar h _ (GlobalTheory.Pst.Test.lpDim_wdAt _ ι Bw h hj _) _ _ fun σ => ?_⟩
    rw [htw] at hp ⊢
    rw [GlobalTheory.TwistParamAbove.wdAt_twist l _ _ ⟨T⟩ ι F Ω A w h O Bw hj 1 _ _ (continuous_rank_one_rep κ hκ) (continuous_rank_one_rep κ' hκ') H.1 H'.1 hp,
      GlobalTheory.RowTie.EigTwist.eig_lpChar _ _ σ (GlobalTheory.Pst.Test.lpDim_wdAt _ ι Bw h hj _) _ (eigW _ _ H' σ), eigW _ _ H σ]
    simp
  · intro ξ H σ
    set P := UpperTheory.V.Loc.PP l with hP
    have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have := nontrivial_B P
    have hcyc : ∀ g : Dec (F := F) A, (cycBar F Ω l g : Om l) = algebraMap _ _ (P.χQ (Bw.e g) : ℚ_[l]) := fun g => by
      rw [GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc P Bw.j (g : G F Ω) (Bw.e g : GQ l) (Bw.e_comm g)]
      rfl
    have key := ParamAboveModel.mem_eig_wdAt P ι Bw h hj (cycBar F Ω l) H.1 (tInv P)
      (fun h0 => by simpa [h0] using tInv_mul P) (l : ℚ_[l])⁻¹
      (inv_ne_zero hl) (by rw [eq_inv_smul_iff₀ hl, smul_phiB_tInv]) (fun g => P.χQ g) (fun g => Units.ne_zero _)
      (smul_actQ_tInv P) Bw.Kw (fun g _ => hcyc g) σ
    have h2 : (cycBar F Ω l σ : Om l) = algebraMap _ _ (P.χQ (weilToGK Bw h σ) : ℚ_[l]) :=
      hcyc ⟨σ, Weil_le_Dec h σ.2⟩
    rw [h2, ← map_mul, mul_inv_cancel_left₀ (Units.ne_zero _), inv_zpow', neg_neg, map_zpow₀, map_natCast,
      alpha, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_eq_pow (hj.mem_placesOver h)] at key
    have e := eigW _ _ H σ
    exact (ι.injective (Multiset.mem_singleton.mp (e ▸ key))).symm
