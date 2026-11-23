import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointExpEqOfIsometry
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CongruenceActionMemFrameOrbit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGroupOfCongruent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat

noncomputable section

namespace GlobalTheory.DictMove

open Filter Topology in

theorem exists_const_of_pointwise {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {ι : Type}
    {O : Set V} (hO : IsOpen O) (hc : IsPreconnected O) (P Q : ι → V → ℂ) (hP : ∀ i, DifferentiableOn ℂ (P i) O)
    (hQ : ∀ i, DifferentiableOn ℂ (Q i) O) (h : ∀ x ∈ O, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i, P i x = c * Q i x) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i, ∀ x ∈ O, P i x = c * Q i x := by
  by_cases h0 : ∃ i, ∃ x ∈ O, Q i x ≠ 0
  · obtain ⟨i₀, x₀, hx₀, hq⟩ := h0
    obtain ⟨-, c, hcc⟩ := GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq V Unit O hO hc ⟨x₀, hx₀⟩ (P i₀)
      (fun _ => Q i₀) (hP i₀) (fun _ => hQ i₀) fun x hx => by
        obtain ⟨c, h1, h2⟩ := h x hx
        exact ⟨(), by rw [h2, norm_mul, h1, one_mul]⟩
    have key : ∀ x ∈ O, Q i₀ x ≠ 0 → ‖c‖ = 1 ∧ ∀ i, P i x = c * Q i x := fun x hx hq => by
      obtain ⟨c', h1, h2⟩ := h x hx
      obtain rfl : c' = c := mul_right_cancel₀ hq ((h2 i₀).symm.trans (hcc x hx))
      exact ⟨h1, h2⟩
    refine ⟨c, (key x₀ hx₀ hq).1, fun i y hy => ?_⟩
    have hne : ∀ᶠ y in 𝓝 x₀, Q i₀ y ≠ 0 :=
      ((hQ i₀).continuousOn.continuousAt (hO.mem_nhds hx₀)).eventually_ne hq
    have hd : DifferentiableOn ℂ (fun y => P i y - c * Q i y) O := (hP i).sub ((hQ i).const_mul c)
    exact sub_eq_zero.mp (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hO hc hd hx₀ (by
      filter_upwards [hne, hO.mem_nhds hx₀] with z hz hzO
      rw [(key z hzO hz).2 i, sub_self]; rfl) y hy)
  · push Not at h0
    refine ⟨1, norm_one, fun i x hx => ?_⟩
    obtain ⟨c, -, h2⟩ := h x hx
    rw [h2, h0 i x hx, mul_zero, mul_zero]

section Family

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}

theorem exp_of_levMove {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (hr : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty) (hA : l.A = 1)
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {s s' : Dw.La →ₗ[𝓞 E] Dw.La} (hν : IsLevMove ρ ν s s')
    {i j : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di j).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di j).La)
    (hEF : ∀ a b, (F.Di j).EF (gam a) (gam b) = (F.Di i).EF a b)
    (hM : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t i (s a)) = F.t j a + l.M • x)
    (h : ∀ a, P' (gam a) = P a) :
    F.u i P ≫ ρ = F.u j P' ∧ ∀ z, (F.ex j P' z).left = (F.ex i P z).left ≫ ν.φ := by
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨m, P₁, hP₁, hu⟩ := F.onto (F.u i P ≫ ρ) (by rw [Category.assoc, hν.1, F.over_σ i P hP])
  obtain ⟨g₁, h₁, e₁, hh₁, hex⟩ := GlobalTheory.LevelCusp.exists_isometry_of_sabMap F ν hP hP₁ hu.symm
  have t₁ : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, g₁ (F.t i (s a)) = F.t m a + l.M • x := fun a ha => by
    refine (GlobalTheory.UnifPoint.div_eq_iff hP₁.2.1 (F.ex_add m P₁ hP₁) (F.ex_ker m P₁ hP₁) hM0 _ _).1 ?_
    apply Over.OverMorphism.ext
    rw [hh₁, ← map_smul h₁, hex, ← F.ex_eta m P₁ hP₁ a ha,
      ← F.ex_eta i P hP _ (GlobalTheory.LevStab.map_mem_smul_top _ _ ha)]
    change (F.u i P ≫ (Xo.univ.eta (s a)).left) ≫ ν.φ = F.u m P₁ ≫ (Xo.univ.eta a).left
    rw [Category.assoc, hν.2.1, ← Category.assoc, hu]
  obtain ⟨k₁, k₂⟩ := GlobalTheory.ArcCM.point_exp_eq_of_isometry GlobalTheory.ArcCM.known_holds E H Dw l Xo σ' g ty F j m P' P₁
    (gam.symm.trans g₁) h₁ hr hσ hty hA hP' hP₁
    (fun u v => by rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e₁, ← hEF, gam.apply_symm_apply,
      gam.apply_symm_apply])
    (fun a ha => by
      obtain ⟨x, hx⟩ := hM a ha
      obtain ⟨y, hy⟩ := t₁ a ha
      refine ⟨y - g₁ (gam.symm x), ?_⟩
      rw [LinearEquiv.trans_apply, eq_sub_of_add_eq hx.symm, map_sub, map_sub, gam.symm_apply_apply, hy, map_nsmul,
        map_nsmul, smul_sub, add_sub_assoc])
    (fun u => by rw [LinearEquiv.trans_apply, hh₁, ← h, gam.apply_symm_apply])
  exact ⟨hu.symm.trans k₁.symm, fun z => (k₂ z).symm.trans (hex z)⟩

end Family

section Frames

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}
  {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)

def HasPeriods : Prop :=
  ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
    (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
    IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
    ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      ((U.un k x).u τ i)

structure Carries (s : Dw.La →ₗ[𝓞 E] Dw.La) (k k' : U.Comp) (δ : GL (Fin r) E) : Prop where
  mt : IsMatch (U.X k) (U.X k') δ
  gm : (U.X k').Gm = (U.X k).Gm
  lat : ∃ gam : (F.Di (ik k)).La ≃ₗ[𝓞 E] (F.Di (ik k')).La,
    (∀ a b, (F.Di (ik k')).EF (gam a) (gam b) = (F.Di (ik k)).EF a b) ∧
    (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t (ik k) (s a)) = F.t (ik k') a + l.M • x) ∧
    ∀ a, (φ k' (gam a) : Fin r → E) = δ.1 *ᵥ (φ k a : Fin r → E)

theorem carries_one (k : U.Comp) : Carries φ LinearMap.id k k 1 :=
  ⟨⟨rfl, rfl, rfl, by simp, by simp⟩, rfl, LinearEquiv.refl _ _, fun _ _ => rfl, fun _ _ => ⟨0, by simp⟩, by simp⟩

variable {φ}

theorem move_eq (hσ : GoodEmb c σ) (hr : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hP : HasPeriods φ)
    {s s' : Dw.La →ₗ[𝓞 E] Dw.La} {k k' : U.Comp} {δ : GL (Fin r) E} (h : Carries φ s k k' δ)
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (hν : IsLevMove ρ ν s s') (x : (U.X k).dom)
    {y' : FrPt Xo c (CAt σ)} (hm : FrMove ρ ν (U.un k x) y') :
    y'.x = (U.un k' ⟨_, h.mt.mem_dom x.2⟩).x ∧ y'.u = (U.un k' ⟨_, h.mt.mem_dom x.2⟩).u := by
  obtain ⟨gam, e₁, t₁, hgam⟩ := h.lat
  obtain ⟨P, hPe, p, hy, hd⟩ := hP k x
  obtain ⟨P', hPe', p', hy', hd'⟩ := hP k' ⟨_, h.mt.mem_dom x.2⟩
  obtain ⟨k₁, k₂⟩ := exp_of_levMove F hr hσ ((GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e) hA hν p p' gam e₁ t₁
    fun v => funext fun j => by
      rw [hPe, hPe', hgam]
      exact GlobalTheory.TwistTie.perFr_of_unitary _ _ (fun τ => by rw [h.mt.psi]) h.gm h.mt.p0.symm
        (fun u v => by rw [← h.mt.iso u v, h.gm]) (fun τ _ _ => rfl) _ _ _
  refine ⟨by rw [hm.1, hy, hy']; exact k₁, funext fun τ => funext fun i => ?_⟩
  have d0 := GlobalTheory.FibreDeriv.isDerivAt0_comp (hd τ i) ν.φ
  simp only [← k₂] at d0
  rw [hm.2.1]
  exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p').2.1 _).unique d0 (hd' τ i)

theorem carries_unique (hσ : GoodEmb c σ) (hU : IsUnf U) (hr : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hP : HasPeriods φ)
    {s s' : Dw.La →ₗ[𝓞 E] Dw.La} {k k₁ k₂ : U.Comp} {δ₁ δ₂ : GL (Fin r) E} (h₁ : Carries φ s k k₁ δ₁)
    (h₂ : Carries φ s k k₂ δ₂) {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (hν : IsLevMove ρ ν s s')
    (x : (U.X k).dom) {y' : FrPt Xo c (CAt σ)} (hm : FrMove ρ ν (U.un k x) y') :
    k₁ = k₂ ∧ (k₁ = k₂ → IsUStab (U.X k₂).Gm (U.X k₂).Λ (δ₂ * δ₁⁻¹) ∧
      ∀ v ∈ (U.X k₂).Λ, ∃ u ∈ (U.X k₂).Λ, (δ₂ * δ₁⁻¹).1 *ᵥ v = v + l.M • u) := by
  constructor
  · obtain ⟨a₁, b₁⟩ := move_eq hσ hr hA hP h₁ hν x hm
    obtain ⟨a₂, b₂⟩ := move_eq hσ hr hA hP h₂ hν x hm
    obtain ⟨_, -, _, -, h⟩ := (hU.2.2.2.1 _ _ _ _).1
      (GlobalTheory.CongrOrbit.frBor_of_eq _ _ (a₂.symm.trans a₁) (b₂.symm.trans b₁))
    exact (congrArg Sigma.fst h).symm
  rintro rfl
  have hri : ∀ v, δ₁.1 *ᵥ ((δ₁⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ₁⁻¹).1 *ᵥ (δ₁.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hmul : ∀ v, (δ₂ * δ₁⁻¹).1 *ᵥ v = δ₂.1 *ᵥ ((δ₁⁻¹).1 *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, Units.val_mul]
  refine ⟨⟨fun u v => ?_, fun v => ?_⟩, fun v hv => ?_⟩
  · rw [hmul, hmul, h₂.mt.iso, ← h₁.mt.iso, hri, hri]
  · rw [hmul, ← h₂.mt.lat, h₁.mt.lat, hri]
  · obtain ⟨g₁, e₁, t₁, m₁⟩ := h₁.lat
    obtain ⟨g₂, e₂, t₂, m₂⟩ := h₂.lat
    have hM : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x,
        (g₁.symm.trans g₂) (F.t _ a) = F.t _ a + l.M • x := fun a ha => by
      obtain ⟨x, hx⟩ := t₁ a ha
      obtain ⟨y, hy⟩ := t₂ a ha
      refine ⟨y - g₂ (g₁.symm x), ?_⟩
      conv_lhs => rw [LinearEquiv.trans_apply, eq_sub_of_add_eq hx.symm, map_sub, map_sub, g₁.symm_apply_apply, hy,
        map_nsmul, map_nsmul]
      rw [smul_sub, add_sub_assoc]
    have hM' := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H _ l (g₁.symm.trans g₂)
      (fun u v => by rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e₂, ← e₁, g₁.apply_symm_apply,
        g₁.apply_symm_apply])
      (fun a ha => by
        generalize g₁.symm.trans g₂ = gam at hM
        refine Submodule.smul_induction_on ha ?_ ?_
        · intro v hv b _
          obtain ⟨c, e, rfl⟩ := F.t_surj _ b
          obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
          obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
          refine ⟨e₁ + r • (gam (v • e) - v • e), ?_⟩
          rw [smul_add, ← map_smul, smul_comm v, map_add, he₁, map_nsmul, hr, smul_add, smul_smul, smul_sub]
          abel
        · rintro x y ⟨e, he⟩ ⟨e', he'⟩
          exact ⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩)
    obtain ⟨a, ha⟩ := (φ k₁).surjective ⟨v, hv⟩
    obtain ⟨b, rfl⟩ := g₁.surjective a
    obtain ⟨w, hw⟩ := hM' (g₁ b)
    have hv' : v = (φ k₁ (g₁ b) : Fin r → E) := by rw [ha]
    refine ⟨φ k₁ w, (φ k₁ w).2, ?_⟩
    rw [LinearEquiv.trans_apply, g₁.symm_apply_apply] at hw
    rw [hmul, hv', m₁, hli, ← m₂, hw, map_add, map_nsmul, ← m₁]
    rfl

variable {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}

theorem rdU_eq_of_carries (hσ : GoodEmb c σ) (hU : IsUnf U) (hr : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hP : HasPeriods φ)
    (hΓ : ∀ k γ, IsUStab (U.X k).Gm (U.X k).Λ γ →
      (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, γ.1 *ᵥ v = v + l.M • u) → γ ∈ (U.X k).Γ)
    (hD : Dom w n) (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U w n k) γ = 1)
    {s s' : Dw.La →ₗ[𝓞 E] Dw.La} {k k₁ k₂ : U.Comp} {δ₁ δ₂ : GL (Fin r) E} (h₁ : Carries φ s k k₁ δ₁)
    (h₂ : Carries φ s k k₂ δ₂) {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (hν : IsLevMove ρ ν s s')
    (x : (U.X k).dom) {y' : FrPt Xo c (CAt σ)} (hm : FrMove ρ ν (U.un k x) y') {f : Rul Xo c} (hf : f ∈ sec Xo c w n) :
    rdU U f k₁ (lact δ₁ (castFr h₁.mt.psi x.1)) = rdU U f k₂ (lact δ₂ (castFr h₂.mt.psi x.1)) := by
  obtain ⟨rfl, h⟩ := carries_unique hσ hU hr hA hP h₁ h₂ hν x hm
  have hγ := hΓ _ _ (h rfl).1 (h rfl).2
  have := (hU.2.2.2.2.1 w n hD f hf k₁).2.2 _ hγ _ (h₁.mt.mem_dom x.2)
  rw [hχ _ _ hγ, one_mul, GlobalTheory.Dict.Extend.lact_lact, inv_mul_cancel_right] at this
  exact this.symm

theorem exists_const_of_carries (hσ : GoodEmb c σ) (hU : IsUnf U) (hr : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hP : HasPeriods φ) (hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0) (hD : Dom w n) {s s' : Dw.La →ₗ[𝓞 E] Dw.La}
    (act : Rul Xo c → Rul Xo c) (hact : ∀ f ∈ sec Xo c w n, act f ∈ sec Xo c w n)
    (hmv : ∀ y : FrPt Xo c (CAt σ), ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y' : FrPt Xo c (CAt σ)),
      IsLevMove ρ ν s s' ∧ FrMove ρ ν y y' ∧ ∀ f ∈ sec Xo c w n, evR Xo c (act f) y = evR Xo c f y')
    {k k' : U.Comp} {δ : GL (Fin r) E} (h : Carries φ s k k' δ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ f ∈ sec Xo c w n, ∀ x ∈ (U.X k).dom,
      rdU U (act f) k x = z * rdU U f k' (lact δ (castFr h.mt.psi x)) := by
  have hsec := hU.2.2.2.2.1 w n hD
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU
  obtain ⟨z, hz, hc⟩ := exists_const_of_pointwise (ι := sec Xo c w n) (FourierCoefficientDomain.isOpen_dom (U.X k))
    (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected (fun f => rdU U (act f) k)
    (fun f x => rdU U f k' (lact δ (castFr h.mt.psi x))) (fun f => (hsec _ (hact f f.2) k).1)
    (fun f => (hsec _ f.2 k').1.comp ((GlobalTheory.Dict.Extend.differentiable_lact δ).comp
      (GlobalTheory.Dict.Pull.cast_diff h.mt.psi)).differentiableOn fun x hx => h.mt.mem_dom hx)
    (fun x hx => by
      obtain ⟨x₀, hx₀, b₀, hb₀, e₀⟩ : ∃ x' : (U.X k).dom, GlobalTheory.FrameNorm.IsUnitFr (U.X k) x'.1 ∧
          ∃ b ∈ Bor (U.X k).Ψ r, x'.1 = rmul x b := (hun1 k ⟨x, hx⟩).imp fun _ h => ⟨h.1, h.2.1⟩
      obtain ⟨ρ, ν, y', hν, hm, hv⟩ := hmv (U.un k x₀)
      obtain ⟨a₁, b₁⟩ := move_eq hσ hr hA hP h hν x₀ hm
      obtain ⟨t, hb⟩ := GlobalTheory.CongrOrbit.frBor_of_eq _ _ a₁ b₁
      obtain ⟨-, -, -, -, -, -, ht⟩ := exists_match (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU (hU.1 ▸ hr)
        (fun k k' τ => congrArg (fun a => ‖τ a‖) (hxi k k')) hm hb hx₀
        (fun τ i => (congrArg norm (h.mt.dmin_eq x₀.1 τ i)).trans (hx₀ _ i))
      refine ⟨toC (wchar (ex Dw w n) t : CAt σ), ?_, fun f => ?_⟩
      · have : toC (wchar (ex Dw w n) t : CAt σ) = ∏ j, toC (t j : CAt σ) ^ ex Dw w n j := rfl
        rw [this, norm_prod]
        exact Finset.prod_eq_one fun j _ => by
          rw [norm_pow, show ‖toC (t j : CAt σ)‖ = 1 from ht j, one_pow]
      have v1 : rdU U (act f) k x₀.1 = toC (evR Xo c (act f) (U.un k x₀)) := dif_pos x₀.2
      have v2 : rdU U f k' (lact δ (castFr h.mt.psi x₀.1)) = toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom x₀.2⟩)) :=
        dif_pos (h.mt.mem_dom x₀.2)
      have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
        (inferInstanceAs (IsReduced ℂ)) w n f f.2 t _ y' hb
      have v5 : rdU U (act f) k x₀.1 =
          toC (wchar (ex Dw w n) t : CAt σ) * rdU U f k' (lact δ (castFr h.mt.psi x₀.1)) := by
        rw [v1, v2, hv f f.2, v3]
        rfl
      rw [e₀, (hsec _ (hact f f.2) k).2.1 x hx b₀ hb₀, GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        (hsec _ f.2 k').2.1 _ (h.mt.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.mt.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar (la := laU U w n k) (la' := laU U w n k') h.mt.psi
          (laU_match (U := Formalism.L2.PjFree.Unf.ofPj U) h.mt w n), mul_left_comm] at v5
      exact mul_left_cancel₀ (AR.Up.OntoE.bchar_ne _ _ hb₀) v5)
  exact ⟨z, hz, fun f hf => hc ⟨f, hf⟩⟩

end Frames

section Adelic

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

def Induces (V : HSp D) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ latGHat V κ = latGHat V 1 ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
    (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s a)) + l.M • w

set_option maxHeartbeats 1000000 in

theorem exists_const_dict {V W : HSp D} (hV : V = W) {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {U : Unf Xo c σ r}
    {dict : GA D V → Σ k, Frame (U.X k).Ψ r} (io : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hW : ∀ k, ModelW V hr (U.X k))
    (hL : DictLat U V hr dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ io) e F ik φ th x₀)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom)
    (hΓ : ∀ k γ, IsUStab (U.X k).Gm (U.X k).Λ γ →
      (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, γ.1 *ᵥ v = v + l.M • u) → γ ∈ (U.X k).Γ)
    {w : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n) (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U w n k) γ = 1)
    {s s' : Dw.La →ₗ[𝓞 D.host.E] Dw.La} (act : Rul Xo c → Rul Xo c)
    (hact : ∀ f ∈ sec Xo c w n, act f ∈ sec Xo c w n)
    (hmv : ∀ y : FrPt Xo c (CAt σ), ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y' : FrPt Xo c (CAt σ)),
      IsLevMove ρ ν s s' ∧ FrMove ρ ν y y' ∧ ∀ f ∈ sec Xo c w n, evR Xo c (act f) y = evR Xo c f y') :
    ∃ z : U.Comp → ℂ, (∀ x, ‖z x‖ = 1) ∧
      ∀ κ, Induces W l (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ io) s κ → ∀ f ∈ sec Xo c w n, ∀ h,
        rdU U (act f) (Formalism.IndefR.FWT.castDict hV dict h).1 (Formalism.IndefR.FWT.castDict hV dict h).2 =
          z (Formalism.IndefR.FWT.castDict hV dict h).1 *
            rdU U f (Formalism.IndefR.FWT.castDict hV dict (h * κ)).1 (Formalism.IndefR.FWT.castDict hV dict (h * κ)).2 := by
  subst hV
  subst hr
  change DictLat U V rfl dict io e F ik φ th x₀ at hL
  change ∃ z : U.Comp → ℂ, (∀ x, ‖z x‖ = 1) ∧ ∀ κ, Induces V l io s κ → ∀ f ∈ sec Xo c w n, ∀ h,
    rdU U (act f) (dict h).1 (dict h).2 = z (dict h).1 * rdU U f (dict (h * κ)).1 (dict (h * κ)).2
  have hP : HasPeriods φ := hL.1.2
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0 := fun k k' => (hW k).2.trans (hW k').2.symm
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have key : ∀ κ, Induces V l io s κ → ∀ h, ∃ δ, ∃ hc : Carries φ s (dict h).1 (dict (h * κ)).1 δ,
      (dict (h * κ)).2 = lact δ (castFr hc.mt.psi (dict h).2) := by
    intro κ hκ h
    obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, hf₁⟩ := hL.2 h
    obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, hf₂⟩ := hL.2 (h * κ)
    have e₀ : γ₂ * (h * κ) = γ₂ * γ₁⁻¹ * (γ₁ * h) * κ := by group
    obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V (γ₂ * γ₁⁻¹) (mul_mem hγ₂ (inv_mem hγ₁))
    obtain ⟨gam, e₁, t₁, hgam⟩ := GlobalTheory.TwistTie.marked_isometry_half V l io (U.X (dict h).1) (U.X (dict (h * κ)).1) _ _
      (φ _) (φ _) (F.t _) (F.t _) s (γ₁ * h) (γ₂ * γ₁⁻¹) κ (hW _) (hW _) (hL.1.1 _) (hL.1.1 _) δ hδu hδf hκ.2.1 hκ.2.2
      ⟨hΛ₁, hm₁⟩ (by rw [← e₀]; exact ⟨hΛ₂, hm₂⟩)
    have hmt : IsMatch (U.X (dict h).1) (U.X (dict (h * κ)).1) δ := by
      refine ⟨Finset.ext fun τ => ((hU.2.1 _).2 τ).trans ((hU.2.1 _).2 τ).symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm,
        hxi _ _, fun u v => by rw [hG, hG]; exact hδu u v, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
      · obtain ⟨a, ha⟩ := (φ _).surjective ⟨v, hv⟩
        rw [show v = (φ (dict h).1 a : Fin V.rank → D.host.E) by rw [ha], ← hgam]
        exact (φ _ _).2
      · obtain ⟨a, ha⟩ := (φ _).surjective ⟨_, hv⟩
        obtain ⟨b, rfl⟩ := gam.surjective a
        have h1 := congrArg (fun u => (δ⁻¹).1 *ᵥ u) ((hgam b).symm.trans (congrArg Subtype.val ha))
        simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
        rw [← h1]
        exact (φ _ _).2
    refine ⟨δ, ⟨hmt, by rw [hG, hG], gam, e₁, t₁, hgam⟩, funext fun τ => ?_⟩
    change mat (dict (h * κ)).2 τ = δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hmt.mem τ⟩
    rw [hf₁, hf₂, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ τ) (hθ τ.1),
      GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ ⟨τ.1, hmt.mem τ⟩) (hθ τ.1), e₀, (hAr τ.1).2.1, (hAr τ.1).2.1,
      (hAr τ.1).2.2.1 κ hκ.1, hδa τ.1 _ (hθ τ.1), Matrix.mul_one, ← Matrix.mul_assoc]
    rfl
  have ex : ∀ k : U.Comp, ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ k' δ (hc : Carries φ s k k' δ), ∀ f ∈ sec Xo c w n,
      ∀ x ∈ (U.X k).dom, rdU U (act f) k x = z * rdU U f k' (lact δ (castFr hc.mt.psi x)) := by
    intro k
    by_cases h0 : ∃ k' δ, Carries φ s k k' δ
    · obtain ⟨k₀, δ₀, h₀⟩ := h0
      obtain ⟨z, hz, hc₀⟩ := exists_const_of_carries hσ hU hpq hA hP hxi hD act hact hmv h₀
      refine ⟨z, hz, fun k' δ hc f hf x hx => ?_⟩
      obtain ⟨ρ, ν, y', hν, hm, -⟩ := hmv (U.un k ⟨x, hx⟩)
      rw [hc₀ f hf x hx, rdU_eq_of_carries hσ hU hpq hA hP hΓ hD hχ h₀ hc hν ⟨x, hx⟩ hm hf]
    · exact ⟨1, norm_one, fun k' δ hc => absurd ⟨k', δ, hc⟩ h0⟩
  choose z hz hzc using ex
  refine ⟨z, hz, fun κ hκ f hf h => ?_⟩
  obtain ⟨δ, hc, e₁⟩ := key κ hκ h
  rw [e₁]
  exact hzc _ _ δ hc f hf _ (hdom h)

end Adelic

section Lifts

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV
  Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
  {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {L : LevDat D.host.E ℂ V.rank}

theorem mulVec_mem_latHat (hβ : IsSDFrame V β Λ 1) {g : G0 L.Pg L.r} {k : GA D V} (hk : Lev.IsLevelLift V β L g k)
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ Formalism.L2.Pj.latHat V) :
    (finHom V k).1 *ᵥ z ∈ Formalism.L2.Pj.latHat V := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  rw [hl] at hz ⊢
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨y, hy⟩ := parLev_St hk.2.1
  have hy' : β * intGL D.host.F D.host.E V.rank y * β⁻¹ = Formalism.UG.bc (Lev.swapAE D) (finHom V k) := hy
  have h2 := (hfr _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)
  have h3 : (Formalism.UG.bc (Lev.swapAE D) (finHom V k)).1 *ᵥ
      (fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← hy']
    exact (hfr _).2 (GlobalTheory.RepsCompare.conj_mulVec_mem _ β y _ h2)
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h3
  convert h4 using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  exact RingHom.map_mulVec (Lev.swapAE D) (finHom V k).1 z i

theorem latGHat_eq (hβ : IsSDFrame V β Λ 1) {g : G0 L.Pg L.r} {k : GA D V} (hk : Lev.IsLevelLift V β L g k) :
    latGHat V k = latGHat V 1 := by
  have e : Formalism.L2.Pj.gLat V k = Formalism.L2.Pj.gLat V 1 := by
    unfold Formalism.L2.Pj.gLat
    rw [map_one, Units.val_one]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, mulVec_mem_latHat hβ hk hy, Matrix.one_mulVec _⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨_, mulVec_mem_latHat hβ (GlobalTheory.ProjComm.isLift_inv hk) hy, ?_⟩
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  unfold latGHat
  rw [e]

theorem induces_of_lift {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hio : LatEmb V io)
    {s : Dw.La →ₗ[𝓞 D.host.E] Dw.La} (hβ : IsSDFrame V β Λ 1)
    (hK : ∀ k, Lev.IsLevelLift V β L 1 k →
      ∀ z ∈ Formalism.L2.Pj.latHat V, ∃ y ∈ Formalism.L2.Pj.latHat V, (finHom V k).1.mulVec z - z = l.M • y)
    {g : G0 L.Pg L.r} {k₀ k : GA D V} (hk₀ : Lev.IsLevelLift V β L g k₀) (hk : Lev.IsLevelLift V β L g k)
    (hs : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      finVec V (io (s a)) - (finHom V k₀).1.mulVec (finVec V (io a)) = l.M • w) : Induces V l io s k := by
  refine ⟨hk.1, latGHat_eq hβ hk, fun a ha => ?_⟩
  have h1 := GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_inv hk₀) hk
  rw [inv_mul_cancel] at h1
  have hmem : finVec V (io a) ∈ latGHat V 1 :=
    ((GlobalTheory.MarkCoset.latG_spec D V 1).1 _).1 (hio.2 ▸ LinearMap.mem_range_self io a)
  obtain ⟨y, hy, e₁⟩ := GlobalTheory.MarkCoset.level_latGHat V l.M _ (hK _ h1) _ hmem
  obtain ⟨w, hw, e₂⟩ := hs a ha
  have hy' : (finHom V k₀).1 *ᵥ y ∈ latGHat V 1 :=
    latGHat_eq hβ hk₀ ▸ ((GlobalTheory.MarkCoset.latG_spec D V k₀).2 _).2 ⟨y, hy, rfl⟩
  refine ⟨_, sub_mem hy' hw, ?_⟩
  have e₃ : (finHom V k).1 = (finHom V k₀).1 * (finHom V (k₀⁻¹ * k)).1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have e₄ : (finHom V k₀).1 *ᵥ (l.M • y) = l.M • (finHom V k₀).1 *ᵥ y :=
    map_nsmul (finHom V k₀).1.mulVecLin.toAddMonoidHom l.M y
  rw [e₃, ← Matrix.mulVec_mulVec, e₁, Matrix.mulVec_add, e₄, nsmul_sub, ← e₂]
  abel

theorem cast_level {W : HSp D} (hV : V = W) {N r : ℕ} {Kf : Subgroup (GA D V)} (hK : IsLevelK V N Kf) {La : Type}
    [AddCommGroup La] [Module (𝓞 D.host.E) La] (io : La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (hr : V.rank = r)
    (hr' : W.rank = r) (hio : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ io)) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ io) ∧
      ∀ k : GA D W, cast (congrArg (GA D) hV.symm) k ∈ Kf →
        ∀ z ∈ Formalism.L2.Pj.latHat W, ∃ y ∈ Formalism.L2.Pj.latHat W, (finHom W k).1.mulVec z - z = N • y := by
  subst hV
  exact ⟨hio, fun k hk => ((hK k).1 hk).2⟩

end Lifts

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem rdU_actLev_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∃ z : (T.U ((i : ℕ) + 1) σ).Comp → G → ℂ, (∀ x g, ‖z x g‖ = 1) ∧ ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ h, rdU (T.U ((i : ℕ) + 1) σ) (actLev T.Q.c (O i).lev2 g f) (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2 = z (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 g * rdU (T.U ((i : ℕ) + 1) σ) f (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).2 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR ht hpb hO i σ hσ hV
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have h := ht.laws
  obtain ⟨_, _, -, hd⟩ := h.dictU _ hj σ hσ
  obtain ⟨hr, g₀, e, F, ik, φ, th, hio, -, hth, hL⟩ := h.adPin _ hj σ hσ
  obtain ⟨_, hW⟩ := h.modelW _ hj σ hσ
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hU := h.unf _ hj σ hσ
  have hpq := hU.1 ▸ (show 1 ≤ D.R.r from (hnum _ hj).2.1)
  have hK := h.levelK _ hj σ hσ
  rw [← h.pins.2.1.1] at hK
  obtain ⟨hio', hK'⟩ := cast_level hV hK (T.iota _) hr (rank_Wc i) hio
  have hact := (hO i).2.act.1
  choose z hz hzc using fun g : G => exists_const_dict hV hr (rank_Wc i) (T.iota _) hσ hU hpq hA hW hL hth hd.2.2.2.1
    (GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM _ hj σ hσ) (dom_wtA (κ i))
    (h.chiTriv _ hj σ hσ _ _ (dom_wtA (κ i))) (s := (O i).lev g) (s' := LinearMap.id)
    (actLev T.Q.c (O i).lev2 g) (fun f hf => actL_mem _ _ _ _ hact.total hact.nat hact.bor _ g hf) fun y => by
      obtain ⟨ρ, ν, -, hν, hm⟩ := mvPt_spec hact.total g y
      exact ⟨ρ, ν, _, hν, hm, fun f hf => evalAt_actL hact (h.evalWD _ hj) frMap_trans_id g hf.1 y⟩
  refine ⟨fun x g => z g x, fun x g => hz g x, fun g k hk f hf p => ?_⟩
  obtain ⟨k₀, hk₀, hs⟩ := (hO i).2.lift.lev g
  exact hzc g k (induces_of_lift hio' (hR.βW i)
    (fun k hk => hK' k ((GlobalTheory.LiftLevel.isLift_one_iff_mem_level T R κ v₀ hR ht hpb i σ hσ hV k).1 hk)) hk₀ hk hs) f
    ((mem_cusp _ _ _ _ _ _).1 hf).1 p

end GlobalTheory.DictMove
