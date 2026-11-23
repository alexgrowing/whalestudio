import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lift_key (hK : UpperTheory.Gal.TP.Loc.KeepsSB) (hD : UpperTheory.Gal.TP.Loc.ModelDict)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    {ν b : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) k) V} {π : Representation ℂ (GL (Fin d) k) W}
    {β : SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] V →ₗ[ℂ] W}
    (hβ : ∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Φ Φ' : SB (Matrix (Fin n) (Fin d) k)),
      (Φ' : Matrix (Fin n) (Fin d) k → ℂ) = GlobalTheory.SplitFlip.omA ν b g h Φ → ∀ v : V, β Φ' (σ g v) = π h (β Φ v))
    (g : GL (Fin n) k) (h : GL (Fin d) k) (Φ Φ' : SB (Matrix (Fin n) (Fin d) k))
    (Ψ Ψ' : Matrix (Fin d) (Fin n) k → ℂ)
    (hΦ : ∀ X, (Φ : Matrix (Fin n) (Fin d) k → ℂ) X = Ψ X.transpose)
    (hΦ' : ∀ X, (Φ' : Matrix (Fin n) (Fin d) k → ℂ) X = Ψ' X.transpose)
    (hΨ' : Ψ' = om b⁻¹ g h Ψ) (v : V) :
    β Φ' (src (ν * b) σ g v) = π h (β Φ v) := by
  have hmem : GlobalTheory.SplitFlip.omA ν b (GlobalTheory.SplitFlip.invT g) h (Φ : Matrix (Fin n) (Fin d) k → ℂ)
      ∈ SB (Matrix (Fin n) (Fin d) k) := (hK k n d).1 ν b _ h _ Φ.2
  have hfun : GlobalTheory.SplitFlip.omA ν b (GlobalTheory.SplitFlip.invT g) h (Φ : Matrix (Fin n) (Fin d) k → ℂ)
      = ((ν * b) (Matrix.GeneralLinearGroup.det g) : ℂ) • (Φ' : Matrix (Fin n) (Fin d) k → ℂ) := by
    have hΦf : (Φ : Matrix (Fin n) (Fin d) k → ℂ) = fun Y => Ψ Y.transpose := funext hΦ
    funext X
    rw [hΦf, hD k n d ν b g h Ψ X, Pi.smul_apply, smul_eq_mul, hΦ' X, hΨ']
  have hsub : (⟨_, hmem⟩ : SB (Matrix (Fin n) (Fin d) k))
      = ((ν * b) (Matrix.GeneralLinearGroup.det g) : ℂ) • Φ' := Subtype.ext hfun
  have key := hβ (GlobalTheory.SplitFlip.invT g) h Φ ⟨_, hmem⟩ rfl v
  rw [src_apply, map_smul, ← LinearMap.smul_apply, ← map_smul, ← hsub, key]

private theorem continuous_invT' {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} :
    Continuous (GlobalTheory.SplitFlip.invT : GL (Fin n) k →* GL (Fin n) k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem UpperTheory.Gal.TP.Loc.pairOfLift :
    UpperTheory.Gal.TP.Loc.LeftSmooth → UpperTheory.Gal.TP.Loc.KeepsSB → UpperTheory.Gal.TP.Loc.ModelDict → UpperTheory.Gal.TP.Loc.Separates → UpperTheory.Gal.TP.Loc.PairOfLift := by
  intro hL hK hD hS k _ _ _ _ n d ν b V _ _ W _ _ σ π hν hb hπ ⟨β, hβ0, hβ⟩
  let tr : SB (Matrix (Fin d) (Fin n) k) → SB (Matrix (Fin n) (Fin d) k) :=
    fun Ψ => ⟨fun X => (Ψ : Matrix (Fin d) (Fin n) k → ℂ) X.transpose, (hK k n d).2 _ Ψ.2⟩
  have tr_add : ∀ Ψ₁ Ψ₂, tr (Ψ₁ + Ψ₂) = tr Ψ₁ + tr Ψ₂ := fun _ _ => rfl
  have tr_smul : ∀ (c : ℂ) Ψ, tr (c • Ψ) = c • tr Ψ := fun _ _ => rfl
  have hsm : ∀ (Ψ : SB (Matrix (Fin d) (Fin n) k)) (F : smoothPart π.dual),
      (F : Module.Dual ℂ W) ∘ₗ β (tr Ψ) ∈ smoothPart (src (ν * b) σ).dual := by
    intro Ψ F
    apply mem_smoothPart_of_nhds
    have hT : {g : GL (Fin n) k | ∀ Y : Matrix (Fin d) (Fin n) k,
        (Ψ : Matrix (Fin d) (Fin n) k → ℂ) (Y * (g : Matrix (Fin n) (Fin n) k))
          = (Ψ : Matrix (Fin d) (Fin n) k → ℂ) Y} ∈ nhds 1 := by
      have hc : Continuous (fun g : GL (Fin n) k => GlobalTheory.SplitFlip.invT g⁻¹) :=
        continuous_invT'.comp continuous_inv
      have h1 : (fun g : GL (Fin n) k => GlobalTheory.SplitFlip.invT g⁻¹) 1 = 1 := by simp
      have hpre := hc.tendsto' 1 1 h1 (hL k n d (tr Ψ))
      filter_upwards [hpre] with g hg Y
      have hval : ((GlobalTheory.SplitFlip.invT g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
          = (g : Matrix (Fin n) (Fin n) k).transpose := by
        rw [GlobalTheory.SplitFlip.invT_val, inv_inv]
      have hY := hg Y.transpose
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hY
      simp only [tr, hval, Matrix.transpose_mul, Matrix.transpose_transpose] at hY
      exact hY
    have hK0 : (KO k (Fin n) : Set (GL (Fin n) k)) ∈ nhds 1 :=
      GlobalTheory.SplitFlip.isOpen_KO.mem_nhds (one_mem _)
    have hker : ((detChar (Fin n) b).ker : Set (GL (Fin n) k)) ∈ nhds 1 :=
      (IsSmoothChar.detChar hb).mem_nhds (one_mem _)
    have hab1 : nabs k (1 : kˣ) = 1 := GlobalTheory.SplitFlip.nabs_of_valuation_eq_one (by simp)
    have hfix : {g : GL (Fin n) k | om b⁻¹ g 1 (Ψ : Matrix (Fin d) (Fin n) k → ℂ) = Ψ} ∈ nhds 1 := by
      filter_upwards [hT, hK0, hker] with g hgT hgK hgk
      have hdet : b (Matrix.GeneralLinearGroup.det g) = 1 := hgk
      have hab : nabs k (Matrix.GeneralLinearGroup.det g) = 1 :=
        GlobalTheory.SplitFlip.nabs_of_valuation_eq_one (GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hgK)
      funext x
      simp [om, hdet, hab, hab1, hgT]
    have hfix' := (continuous_inv.tendsto' (1 : GL (Fin n) k) 1 inv_one) hfix
    filter_upwards [hfix'] with g hg
    apply LinearMap.ext
    intro v
    rw [Representation.dual_apply]
    simp only [Module.Dual.transpose_apply, LinearMap.coe_comp, Function.comp_apply]
    congr 1
    have hk := lift_key hK hD hβ g⁻¹ 1 (tr Ψ) (tr Ψ) Ψ Ψ (fun _ => rfl) (fun _ => rfl) hg.symm v
    simpa using hk
  let B : SB (Matrix (Fin d) (Fin n) k) →ₗ[ℂ] smoothPart π.dual →ₗ[ℂ] smoothPart (src (ν * b) σ).dual :=
    LinearMap.mk₂ ℂ (fun Ψ F => ⟨(F : Module.Dual ℂ W) ∘ₗ β (tr Ψ), hsm Ψ F⟩)
      (fun Ψ₁ Ψ₂ F => by ext v; simp [tr_add])
      (fun c Ψ F => by ext v; simp [tr_smul])
      (fun Ψ F₁ F₂ => by ext v; simp)
      (fun c Ψ F => by ext v; simp)
  refine ⟨B, ?_, ?_⟩
  · intro hB
    obtain ⟨Φ0, hΦ0⟩ : ∃ Φ0, β Φ0 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hβ0 (LinearMap.ext hc)
    obtain ⟨v, hv⟩ : ∃ v, β Φ0 v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hΦ0 (LinearMap.ext hc)
    obtain ⟨l, hl⟩ := hS k d W π hπ _ hv
    let Ψ0 : SB (Matrix (Fin d) (Fin n) k) :=
      ⟨fun Y => (Φ0 : Matrix (Fin n) (Fin d) k → ℂ) Y.transpose, (hK k d n).2 _ Φ0.2⟩
    have htr : tr Ψ0 = Φ0 := Subtype.ext (funext fun X => by simp [tr, Ψ0])
    apply hl
    have := congrArg (fun B' : SB (Matrix (Fin d) (Fin n) k) →ₗ[ℂ] smoothPart π.dual →ₗ[ℂ]
      smoothPart (src (ν * b) σ).dual => ((B' Ψ0 l : smoothPart _) : Module.Dual ℂ V) v) hB
    simpa [B, htr] using this
  · intro g h Ψ Ψ' hΨ' F
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have key := lift_key hK hD hβ g h (tr Ψ) (tr Ψ') Ψ Ψ' (fun _ => rfl) (fun _ => rfl) hΨ'
      ((src (ν * b) σ) g⁻¹ v)
    have hv : (src (ν * b) σ) g ((src (ν * b) σ) g⁻¹ v) = v := by
      show ((src (ν * b) σ) g * (src (ν * b) σ) g⁻¹) v = v
      rw [← map_mul]
      simp
    rw [hv] at key
    simp only [B, LinearMap.mk₂_apply, contra_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [key]
    congr 1
    show (π h⁻¹ * π h) _ = _
    rw [← map_mul]
    simp
