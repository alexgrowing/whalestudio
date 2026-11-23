import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactAltForm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyPhaseQuadratic
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaussSumEighthPower
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.UnitaryEighthOf
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.TripleEighthProof
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.StdDataCmProof

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace KR

theorem isLat_stdLat (L : PeriodPair) (m : Type) [Fintype m] : IsLat (stdLat L m) := by
  classical
  constructor
  · let f : stdLat L m → (∀ _ : m, L.lattice) := fun x i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
    have hf : Continuous f :=
      continuous_pi fun i => Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      funext i
      exact congrArg Subtype.val (congrFun hxy i)
    exact DiscreteTopology.of_continuous_injective hf hinj
  · rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, Pi.single i (x i) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : x i ∈ Submodule.span ℝ (L.lattice : Set ℂ) := by
      rw [IsZLattice.span_top (K := ℝ) (L := L.lattice)]
      trivial
    have h2 : (Submodule.span ℝ (L.lattice : Set ℂ)).map (LinearMap.single ℝ (fun _ : m => ℂ) i)
        ≤ Submodule.span ℝ ((stdLat L m : AddSubgroup (m → ℂ)) : Set (m → ℂ)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      apply Submodule.subset_span
      intro j _
      by_cases hj : j = i
      · subst hj
        simpa using hy
      · simp [hj]
    exact h2 ⟨x i, h1, rfl⟩

theorem isLat_of_comm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {Λ Λ₁ : AddSubgroup V}
    (hL : IsLat Λ) (h1 : Λ₁.relIndex Λ ≠ 0) (h2 : Λ.relIndex Λ₁ ≠ 0) : IsLat Λ₁ := by
  constructor
  · have := hL.1
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (Λ.relIndex Λ₁).factorial := ⟨_, rfl⟩
    have hN0 : N ≠ 0 := by rw [hN]; exact Nat.factorial_ne_zero _
    have hmem : ∀ x : Λ₁, N • (x : V) ∈ Λ := fun x =>
      (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd h2 x.2
        (fun k hk hk' => by rw [hN]; exact Nat.dvd_factorial hk hk')).1
    let f : Λ₁ → Λ := fun x => ⟨N • (x : V), hmem x⟩
    have hf : Continuous f := Continuous.subtype_mk (continuous_subtype_val.const_smul N) _
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have h3 : N • (x : V) = N • (y : V) := congrArg Subtype.val hxy
      rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at h3
      exact smul_right_injective V (by exact_mod_cast hN0 : (N : ℝ) ≠ 0) h3
    exact DiscreteTopology.of_continuous_injective hf hinj
  · have h3 := (isLat_inf hL h1).2
    rw [eq_top_iff, ← h3]
    exact Submodule.span_mono fun x hx => hx.2

theorem relIdx_trans {V : Type*} [AddCommGroup V] {Λ₁ Λ₂ Λ₃ : AddSubgroup V} (h12 : relIdx Λ₁ Λ₂ ≠ 0)
    (h23 : relIdx Λ₂ Λ₃ ≠ 0) : relIdx Λ₁ Λ₃ ≠ 0 :=
  AddSubgroup.relIndex_ne_zero_trans h12 h23

theorem imgLat_trans {V : Type*} [AddCommGroup V] [Module ℂ V] (g g' : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) :
    imgLat ((g.trans g' : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ = imgLat (g' : V →ₗ[ℂ] V) (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  ext x
  simp only [imgLat, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem norm_mul_eq_one {l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (κ c D : ℂ) (hc8 : c ^ 8 = D ^ 4)
    (hκ : ‖ι κ‖ ^ 2 * ‖ι D‖ = 1) : ‖ι (κ * c)‖ = 1 := by
  have h1 : ‖ι c‖ ^ 8 = ‖ι D‖ ^ 4 := by
    rw [← norm_pow, ← norm_pow, ← map_pow, ← map_pow, hc8]
  have h2 : (‖ι κ‖ * ‖ι c‖) ^ 8 = 1 := by
    rw [mul_pow, h1]
    calc _ = (‖ι κ‖ ^ 2 * ‖ι D‖) ^ 4 := by ring
      _ = 1 := by rw [hκ, one_pow]
  rw [map_mul, norm_mul]
  exact (pow_eq_one_iff_of_nonneg (by positivity) (by norm_num)).1 h2

end KR

open KR in

theorem KernelRatio_of (hC : UnitaryConstant) : KernelRatio := by
  intro L ω₀ n _ _ h Λ α β g₀ g₁ D0 D1 hfix
  have hE : UnitaryEighth := UnitaryEighth_of hC (UnitaryGauss_of gaussSumEighthPower) unitary_index
  obtain ⟨H, hHdef⟩ : ∃ H : Sesq (Fin 4 × n → ℂ), H = stdH L (Fin 4 × n) := ⟨_, rfl⟩
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : AddSubgroup (Fin 4 × n → ℂ), Λ₀ = stdLat L (Fin 4 × n) := ⟨_, rfl⟩
  obtain ⟨Λa, hΛa⟩ : ∃ Λa : AddSubgroup (Fin 4 × n → ℂ),
    Λa = imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := ⟨_, rfl⟩
  obtain ⟨Λb, hΛb⟩ : ∃ Λb : AddSubgroup (Fin 4 × n → ℂ),
    Λb = imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ), δ = g₀.symm.trans g₁ := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin 4 × n → ℂ) → ℂ, F = F0 L ω₀ (Fin 4 × n) := ⟨_, rfl⟩
  have hHerm : IsHerm H := hHdef ▸ (stdHBasic L (Fin 4 × n)).2.1
  have hPos : IsPosDef H := hHdef ▸ (stdHBasic L (Fin 4 × n)).2.2
  have hδap : ∀ x, δ x = g₁ (g₀.symm x) := fun x => by rw [hδ]; rfl
  have hδsy : ∀ x, δ.symm x = g₀ (g₁.symm x) := fun x => by rw [hδ]; rfl
  have hδΛ : imgLat (δ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) Λa = Λb := by
    rw [hΛa, ← imgLat_trans, hΛb, hδ]
    congr 2
    ext x
    simp

  have i0a : relIdx Λ₀ Λa ≠ 0 := by rw [hΛ₀, hΛa]; exact D0.idx₁
  have ia0 : relIdx Λa Λ₀ ≠ 0 := by rw [hΛ₀, hΛa]; exact D0.idx₂
  have i0b : relIdx Λ₀ Λb ≠ 0 := by rw [hΛ₀, hΛb]; exact D1.idx₁
  have ib0 : relIdx Λb Λ₀ ≠ 0 := by rw [hΛ₀, hΛb]; exact D1.idx₂
  have iab : relIdx Λa Λb ≠ 0 := relIdx_trans ia0 i0b
  have iba : relIdx Λb Λa ≠ 0 := relIdx_trans ib0 i0a

  have sd0 : IsSelfDual H Λ₀ := by rw [hHdef, hΛ₀]; exact stdSelfDual L _
  have sda : IsSelfDual H Λa := by rw [hHdef, hΛa]; exact D0.selfDual
  have sdb : IsSelfDual H Λb := by rw [hHdef, hΛb]; exact D1.selfDual
  have sc0 : IsSemiChar H Λ₀ β := by
    rw [hHdef, hΛ₀]
    exact isSemiChar_congr _ _ _ _ D0.betaStd (stdSemiChar L ω₀ (Fin 4 × n) D0.per)
  have sca : IsSemiChar H Λa β := by rw [hHdef, hΛa]; exact D0.betaSemi
  have scb : IsSemiChar H Λb β := by rw [hHdef, hΛb]; exact D1.betaSemi
  have hLat0 : IsLat Λ₀ := by rw [hΛ₀]; exact isLat_stdLat L _
  have hLata : IsLat Λa := isLat_of_comm hLat0 ia0 i0a

  have hiso : IsIsom H H (δ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
    intro x y
    have h1 := D1.isom (g₀.symm x) (g₀.symm y)
    have h0 := D0.isom (g₀.symm x) (g₀.symm y)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h0 h1 ⊢
    rw [hδap, hδap, hHdef, h1, h0]
  have hinj : Function.Injective
      ((LinearMap.id - (δ.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))) :
        (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : x = g₀ (g₁.symm x) := by
      have : x - δ.symm x = 0 := hx
      rw [sub_eq_zero, hδsy] at this
      exact this
    have h2 : g₁.symm x = 0 := hfix _ (by rw [← h1]; simp)
    simpa using congrArg g₁ h2
  obtain ⟨Ae, hAe⟩ : ∃ Ae : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ), ∀ x, Ae x = x - δ.symm x :=
    ⟨LinearEquiv.ofInjectiveEndo _ hinj, fun x => rfl⟩
  have hU : UnitaryData H Λa β δ Ae :=
    { herm := hHerm
      pos := hPos
      selfDual := sda
      semi := sca
      isom := hiso
      semi' := by rw [hδΛ]; exact scb
      inv := by
        intro x _
        rw [hδap, D1.betaAlpha, ← D0.betaAlpha, LinearEquiv.apply_symm_apply]
      idx₁ := by rw [hδΛ]; exact iba
      idx₂ := by rw [hδΛ]; exact iab
      cay := hAe }

  obtain ⟨hFmem, hF1⟩ := product_theta_mem' L ω₀ (Fin 4 × n) D0.per D0.half β D0.betaStd
  rw [← hF, ← hHdef, ← hΛ₀] at hFmem
  rw [← hF] at hF1
  have hFne : F ≠ 0 := by
    intro h0
    rw [h0] at hF1
    simp at hF1
  have hFline : ∀ G ∈ Th H β Λ₀, ∃ c : ℂ, G = c • F := by
    intro G hG
    rw [hHdef, hΛ₀] at hG
    exact ⟨G 0, hF ▸ thStd L ω₀ _ D0.per D0.half β D0.betaStd G hG⟩
  obtain ⟨hGa0, hGaline⟩ := lineTransport (Fin 4 × n → ℂ) H hHerm Λ₀ Λa β sd0 sda sc0 sca i0a ia0 F hFmem
    hFne hFline
  have hGamem : inter H β Λ₀ Λa F ∈ Th H β Λa := interTh _ H hHerm Λ₀ Λa β sca i0a F hFmem
  have hLine : AtMostLine H β Λa := by
    intro θ hθ hθ0 G hG
    obtain ⟨a, ha⟩ := hGaline θ hθ
    obtain ⟨b, hb⟩ := hGaline G hG
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hθ0 (by rw [ha, zero_smul])
    exact ⟨b * a⁻¹, by rw [ha, hb, smul_smul, inv_mul_cancel_right₀ ha0]⟩

  have hidxA : relIdx (latA Λa δ Ae) Λa ≠ 0 := by
    obtain ⟨-, hidx⟩ := unitary_index _ H Λa β δ Ae hLata hU
    intro h0
    rw [h0] at hidx
    have hdt0 : LinearMap.det (Ae : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ≠ 0 :=
      (LinearEquiv.isUnit_det' Ae).ne_zero
    have h1 : (relIdx (imgLat (δ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) Λa) Λa : ℝ) ≠ 0 := by
      exact_mod_cast hU.idx₁
    have h2 : ‖LinearMap.det (Ae : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))‖ ^ 2 ≠ 0 :=
      pow_ne_zero _ (norm_ne_zero_iff.mpr hdt0)
    exact mul_ne_zero h1 h2 (by simpa using hidx.symm)
  obtain ⟨S, hS⟩ := (repsExist _ _ _ hidxA).1
  have hconst := hC _ H Λa β δ Ae hLata hU hLine S hS _ hGamem
  have hc8 := hE _ H Λa β δ Ae hLata hU hLine _ hGamem hGa0 _ hconst
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (‖LinearMap.det (Ae : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))‖ : ℂ)
      / LinearMap.det (Ae : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * gaussC H β Ae S := ⟨_, rfl⟩
  rw [← hc] at hconst hc8
  rw [hδΛ] at hconst

  have hT : TripleData H β Λ₀ Λa Λb :=
    { herm := hHerm, sd₁ := sd0, sd₂ := sda, sd₃ := sdb, sc₁ := sc0, sc₂ := sca, sc₃ := scb
      i₁₂ := i0a, i₂₁ := ia0, i₁₃ := i0b, i₃₁ := ib0, i₂₃ := iab, i₃₂ := iba }
  obtain ⟨S₂, hS₂⟩ := (repsExist _ _ _ i0a).1
  obtain ⟨S₃, hS₃⟩ := (repsExist _ _ _ iab).1
  have hμ8 := TripleEighth_proof _ H β Λ₀ Λa Λb hT ⟨F, hFmem.2, hFne⟩ S₂ S₃ hS₂ hS₃
  have hμ := TripleFormula_proof _ H β Λ₀ Λa Λb hT S₂ S₃ hS₂ hS₃ F hFmem.2
  refine ⟨c * tripleMu H β Λ₀ Λa Λb S₂ S₃, ?_, ?_⟩
  · rw [mul_pow, hμ8, mul_one, hc8, hδ]
  · funext z
    have h1 := congrFun hconst (g₁ z)
    simp only [pullInv, Pi.smul_apply, smul_eq_mul, hδsy, LinearEquiv.symm_apply_apply, hμ] at h1
    simp only [kernel4, Pi.smul_apply, smul_eq_mul]
    rw [← hHdef, ← hΛ₀, ← hΛa, ← hΛb, ← hF, h1, mul_assoc]

theorem quadraticSemicharacterIdentityEquivalent_of_kernelRatio (hK : KernelRatio) : quadraticSemicharacterIdentityEquivalent := by
  intro l _ L ι ω₀ lg linv ph hlog hph hTr n _ _ h Λ α β g₀ g₁ D0 D1 hfix hl κ hκ θ hθ hθκ t N hN hlN hNt
    O _ τ γ B' hB
  obtain ⟨c, hc8, hc⟩ := hK L ω₀ n h Λ α β g₀ g₁ D0 D1 hfix
  refine quadraticSemicharacters_fact l L ι ω₀ lg linv ph hlog hph hTr n h Λ α β g₁ D1 hl (κ * c) ?_ θ hθ ?_ t N hN hlN hNt
    O τ γ B' hB
  · exact le_of_eq (KR.norm_mul_eq_one ι κ c _ hc8 hκ)
  · rw [hθκ, hc, smul_smul]

open KR in

theorem quadraticSemicharacterIdentityReformulated_of_kernelRatio_of_localStandard_of_kappaExists (hK : KernelRatio) (hL : LocalStandard) (hκ : KappaExists) : quadraticSemicharacterIdentityReformulated := by
  intro a b c d ha hd lam hlam hOK n _ _ h Λ g₀ hg₀ hsd hst i1 i2
  obtain ⟨h4, hodd, h8, hprime⟩ := hOK
  have hsda := CmData.selfDual_img _ _ g₀ hg₀ _ (CmData.isSelfDual_matH_blk4_pow4 h Λ hsd)
  have hsta : ∀ x ∈ imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ),
      Formalism.L2.Th1.F.cmTheta b d • x ∈ imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
    rintro x ⟨x', hx', rfl⟩
    refine ⟨Formalism.L2.Th1.F.cmTheta b d • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  obtain ⟨κ, hκ0, hκalg, hκabs, hκl⟩ := hκ a b c d ha hd lam hlam ⟨h4, hodd, h8, hprime⟩ (Fin 4 × n) _ hsda hsta i1 i2
  refine ⟨κ, hκ0, hκalg, hκabs, fun θ hθ hθκ l _ ι => ?_⟩
  obtain ⟨δ, hδiso, hδfix, j1, jl, j2⟩ := hL a b c d ha hd lam hlam ⟨h4, hodd, h8, hprime⟩ (Fin 4 × n) _ hsda hsta i1 i2
    l Fact.out
  have hκδ := hκl l ι δ hδiso j1 jl j2
  rw [← imgLat_trans] at j1 jl j2
  have hg₁ : IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
      ((g₀.trans δ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
    intro x y
    have h1 := hδiso (g₀ x) (g₀ y)
    have h0 := hg₀ x y
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢
    rw [h1, h0]
  have D0 := StdDataCm_proof a b c d ha hd lam hlam h4 hodd h8 n h Λ g₀ hg₀ hsd hst i1 i2
  have D1 := StdDataCm_proof a b c d ha hd lam hlam h4 hodd h8 n h Λ (g₀.trans δ) hg₁ hsd hst j1 j2
  have hcomp : g₀.symm.trans (g₀.trans δ) = δ := by
    ext x
    simp
  have hfix : ∀ x, (g₀.trans δ) x = g₀ x → x = 0 := by
    intro x hx
    have h1 : g₀ x = 0 := hδfix _ hx
    simpa using congrArg g₀.symm h1
  rw [← hcomp] at hκδ
  refine ⟨g₀.trans δ, hg₁, jl, j2, ?_, fun lg linv ph hlog hph hTr t N hN hlN hNt O _ τ γ B' hB =>
    quadraticSemicharacterIdentityEquivalent_of_kernelRatio hK l _ ι _ lg linv ph hlog hph hTr n h Λ _ _ g₀ (g₀.trans δ) D0 D1 hfix jl κ hκδ θ hθ hθκ
      t N hN hlN hNt O τ γ B' hB⟩
  obtain ⟨e, he8, he⟩ := hK _ _ n h Λ _ _ g₀ (g₀.trans δ) D0 D1 hfix
  exact ⟨κ * e, norm_mul_eq_one ι κ e _ he8 hκδ, by rw [hθκ, he, smul_smul]⟩

end Formalism.L2.Th1.H
