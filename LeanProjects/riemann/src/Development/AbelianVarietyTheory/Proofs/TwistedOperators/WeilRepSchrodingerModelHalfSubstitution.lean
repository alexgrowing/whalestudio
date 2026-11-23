import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrodSubst

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

private lemma isSBHalf_psi_mul_halfInd {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    {y : WO S T} (hy : y ∈ half S T (cA D e)) {m : ℕ} (hm : 0 < m) (hmy : m • y ∈ Λ) :
    IsSBHalf e Λ (fun t => ψ (symplO S T t y) * halfInd e Λ t) := by
  have h0 : IsSBHalf e Λ (halfInd e Λ) := GlobalTheory.isSBHalf_halfInd e Λ
  unfold IsSBHalf at h0 ⊢
  obtain ⟨hsupp, k, hk, hinv, hlat⟩ := h0
  have hχ := GlobalTheory.PlaceModel.isBichar_symplO S T ψ
  refine ⟨fun t ht => hsupp t (right_ne_zero_of_mul ht), m * k, Nat.mul_pos hm hk, ?_, ?_⟩
  · intro u hu hue t
    have huh : u ∈ half S T e := (GlobalTheory.PlaceModel.isHalf_iff S T).1 hue
    have hmu : IsHalf e (m • u) := (GlobalTheory.PlaceModel.isHalf_iff S T).2 ((half S T e).nsmul_mem huh m)
    have hI : halfInd e Λ (t + (m * k) • u) = halfInd e Λ t := by
      rw [mul_comm, ← smul_smul]
      exact hinv (m • u) (Λ.nsmul_mem hu m) hmu t
    have hone : ψ (symplO S T ((m * k) • u) y) = 1 := by
      have hs := hχ.nsmul m (k • u) y
      rw [← smul_smul, hs]
      exact hLL' (k • u) ⟨Λ.nsmul_mem hu k, (half S T e).nsmul_mem huh k⟩ (m • y)
        ⟨hmy, (half S T (cA D e)).nsmul_mem hy m⟩
    have hsplit := hχ.left t ((m * k) • u) y
    beta_reduce
    rw [hI, hsplit, hone, mul_one]
  · intro t ht
    rw [← smul_smul]
    exact Λ.nsmul_mem (hlat t (right_ne_zero_of_mul ht)) m

theorem placeModel_wave {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {f₀ : WO S T → ℂ} {T₁ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ T₁) {x y : WO S T} (hx : IsHalf e x)
    (hy' : IsHalf (cA D e) y) :
    T₁ (wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y) =
      heisO ψ S T x (heisO ψ S T y f₀) := by
  obtain ⟨m, hm, hmy⟩ := hden y ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy')
  have hΦ0 : IsSBHalf e Λ (halfInd e Λ) := GlobalTheory.isSBHalf_halfInd e Λ
  have hΨ := isSBHalf_psi_mul_halfInd hLL' ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy') hm hmy
  have hwave : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y =
      fun t => ψ (symplO S T (t + x) y) * halfInd e Λ (t + x) := by
    funext t
    simp only [GlobalTheory.PlaceModel.wave, GlobalTheory.PlaceModel.halfInd_eq_ind]
  have hvac : T₁ (halfInd e Λ) = f₀ := by simpa using h₁.vac
  rw [hwave, h₁.trans _ hΨ x hx, h₁.modul _ hΦ0 y hy', hvac]

theorem wave_actO (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (x y : WO S T) :
    (fun t => wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y (actO S T g⁻¹ h⁻¹ t)) =
      wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) (actO S T g h x) (actO S T g h y) := by
  funext t
  have ht : actO S T g h (actO S T g⁻¹ h⁻¹ t) = t := by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ t
  have hadd : t + actO S T g h x = actO S T g h (actO S T g⁻¹ h⁻¹ t + x) := by
    have := map_add (GlobalTheory.SplitHecke.actAdd S T g h) (actO S T g⁻¹ h⁻¹ t) x
    change actO S T g h (actO S T g⁻¹ h⁻¹ t + x) = actO S T g h (actO S T g⁻¹ h⁻¹ t) + actO S T g h x at this
    rw [this, ht]
  have hhalf : ∀ w : WO S T, actO S T g h w ∈ half S T e ↔ w ∈ half S T e := by
    intro w
    simp only [← GlobalTheory.PlaceModel.isHalf_iff]
    constructor
    · intro hw
      simpa [GlobalTheory.SplitHecke.actO_inv_actO] using GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ hw
    · exact GlobalTheory.SplitHecke.isHalf_actO g h
  have hmem : ∀ w : WO S T, actO S T g h w ∈ Λ ⊓ half S T e ↔ w ∈ Λ ⊓ half S T e := by
    intro w
    simp only [AddSubgroup.mem_inf, hhalf, ← hΛ w]
  simp only [GlobalTheory.PlaceModel.wave]
  rw [hadd, GlobalTheory.SplitHecke.symplO_actO]
  simp only [GlobalTheory.PlaceModel.ind]
  by_cases hw : actO S T g⁻¹ h⁻¹ t + x ∈ Λ ⊓ half S T e
  · rw [if_pos hw, if_pos ((hmem _).2 hw)]
  · rw [if_neg hw, if_neg (fun hw' => hw ((hmem _).1 hw'))]

theorem om_placeModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → a * a = a → infPart D a = 0 → IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ (g : GA D S) (h : GA D T) (c : ℂ), (∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun _ => True)) → om (g, h) f₀ = c • f₀ → ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = c • Tm fun x => Φ (actO S T g⁻¹ h⁻¹ x) := by
  intro D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hth hTm g h c hΛ hc Φ hΦ
  have hstd : IsStdChar D ψ (-1) := hW.std
  have hψ : IsCharAF D.host.F ψ := by
    unfold IsStdChar at hstd
    exact hstd.1
  have hdual := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hstd hS hT).1
  have hsm : ∀ w : AE D, w * w = w → ∀ u ∈ (latO S T ΛS ΛT fun _ => True),
      w • u ∈ (latO S T ΛS ΛT fun _ => True) := by
    intro w hw u hu
    refine GlobalTheory.LatticeStable.smul_mem_latO D S T ΛS ΛT (fun _ => True) w ?_ u hu
    exact GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hw])
  have hfm := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True)
  have hnm : ∀ t : WO S T, t.map (infPart D) = 0 → ∃ k : ℕ, 0 < k ∧ k • t ∈ (latO S T ΛS ΛT fun _ => True) :=
    fun t ht => GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 t ht
  generalize (latO S T ΛS ΛT fun _ => True) = Λ at hdual hsm hfm hnm hTm hΛ hΦ ⊢
  have hcA : cA D a * cA D a = cA D a := by rw [← map_mul, ha]
  have hinf' : infPart D (cA D a) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hLL : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T u y) = 1 := by
    intro u hu y hy
    rw [AddSubgroup.mem_inf] at hu hy
    exact (hdual u (GlobalTheory.PlaceDatum.infPart_of_half hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hden : ∀ y ∈ half S T (cA D a), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ := fun y hy =>
    hnm y (GlobalTheory.PlaceDatum.infPart_of_half hinf' ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hy))
  have hXd : ∀ x ∈ half S T a, (∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) →
      x ∈ Λ ⊓ half S T a := by
    intro x hx hxy
    refine AddSubgroup.mem_inf.2 ⟨?_, hx⟩
    refine (hdual x (GlobalTheory.PlaceDatum.infPart_of_half hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hx))).2 ?_
    intro u' hu'
    have hmem : cA D a • u' ∈ Λ ⊓ half S T (cA D a) := by
      refine AddSubgroup.mem_inf.2 ⟨hsm _ hcA u' hu', ?_⟩
      rw [GlobalTheory.PlaceModel.mem_half, smul_smul, hcA]
    have heq : symplO S T x u' = symplO S T x (cA D a • u') := by
      rw [← GlobalTheory.PlaceModel.symplO_smul, (GlobalTheory.PlaceModel.mem_half S T).1 hx]
    rw [heq]
    exact hxy _ hmem
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T a, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T a, t = r + k • u := by
    intro k hk
    obtain ⟨R, hR, hRt⟩ := hfm k hk
    refine ⟨(fun r => a • r) '' R, hR.image _, ?_⟩
    intro t ht
    rw [AddSubgroup.mem_inf] at ht
    obtain ⟨r, hr, u, hu, rfl⟩ := hRt t ht.1
    refine ⟨a • r, Set.mem_image_of_mem _ hr, a • u, AddSubgroup.mem_inf.2 ⟨hsm a ha u hu, ?_⟩, ?_⟩
    · rw [GlobalTheory.PlaceModel.mem_half, smul_smul, ha]
    · have h2 := (GlobalTheory.PlaceModel.mem_half S T).1 ht.2
      rw [smul_add, smul_comm a k u] at h2
      exact h2.symm
  have htf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk =>
    Function.LeftInverse.injective (g := fun t : WO S T => incA D (k : D.host.E)⁻¹ • t)
      (fun t => GlobalTheory.PlaceModel.inv_smul_nsmul S T hk t)
  have hspan : Φ ∈ GlobalTheory.PlaceModel.waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T a)
      (half S T (cA D a)) (Λ ⊓ half S T a) := by
    unfold IsSBHalf at hΦ
    obtain ⟨hsupp, k, hk, hinv, hlat⟩ := hΦ
    refine GlobalTheory.PlaceDatum.mem_waveSpan (L' := Λ ⊓ half S T (cA D a)) (GlobalTheory.PlaceModel.isBichar_symplO S T ψ)
      inf_le_right inf_le_right hLL hXd (fun k hk x hx => GlobalTheory.PlaceModel.half_div S T a k hk x hx)
      (fun k hk y hy => GlobalTheory.PlaceModel.half_div S T (cA D a) k hk y hy) htf hfin Φ
      (fun t ht => (GlobalTheory.PlaceModel.isHalf_iff S T).1 (hsupp t ht)) k hk ?_ ?_
    · intro u hu t
      rw [AddSubgroup.mem_inf] at hu
      exact hinv u hu.1 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2) t
    · intro t ht
      exact AddSubgroup.mem_inf.2 ⟨hlat t ht,
        (half S T a).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hsupp t ht)) k⟩
  clear hΦ
  unfold GlobalTheory.PlaceModel.waveSpan at hspan
  induction hspan using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hΨ
    have hxH : IsHalf a x := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hx
    have hyH : IsHalf (cA D a) y := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hy
    have hthy : IsThetaFunO ψ S T (heisO ψ S T y f₀) :=
      GlobalTheory.FinTranslate.isTheta_heisO_fin hψ (GlobalTheory.PlaceDatum.infPart_of_half hinf' hyH) hth
    rw [placeModel_wave hLL hden hTm hxH hyH, hW.om_heis g h x _ hthy, hW.om_heis g h y f₀ hth, hc,
      GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_smul, wave_actO ψ a hΛ x y,
      placeModel_wave hLL hden hTm (GlobalTheory.SplitHecke.isHalf_actO g h hxH) (GlobalTheory.SplitHecke.isHalf_actO g h hyH)]
  | zero =>
    rw [show (fun x => (0 : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x)) = 0 from rfl]
    simp only [map_zero, smul_zero]
  | add Ψ₁ Ψ₂ _ _ ih₁ ih₂ =>
    rw [show (fun x => (Ψ₁ + Ψ₂) (actO S T g⁻¹ h⁻¹ x)) =
      (fun x => Ψ₁ (actO S T g⁻¹ h⁻¹ x)) + (fun x => Ψ₂ (actO S T g⁻¹ h⁻¹ x)) from rfl]
    simp only [map_add, ih₁, ih₂, smul_add]
  | smul r Ψ _ ih =>
    rw [show (fun x => (r • Ψ) (actO S T g⁻¹ h⁻¹ x)) = r • (fun x => Ψ (actO S T g⁻¹ h⁻¹ x)) from rfl]
    simp only [map_smul, ih]
    exact smul_comm r c _

end GlobalTheory.SchrodSubst

end
