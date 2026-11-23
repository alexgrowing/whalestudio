import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ContinuousFinId

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Comp

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG PositivityTheory.ThKEst PositivityTheory.ThKF PositivityTheory.ThKG.Loc GlobalTheory.CompanionTheory.Ar.RT.Move
open scoped Classical

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem det_of {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (τ : E →+* ℂ) (hJ : (J.map τ).det ≠ 0) : J.det ≠ 0 := fun h0 =>
  hJ (((RingHom.map_det _ J).symm.trans (congrArg _ h0)).trans (map_zero _))

theorem detX (hp : IsPair B M χX χW om r s r' s') : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_of _ _ (GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.herm.sig w))

theorem detW (hp : IsPair B M χX χW om r s r' s') : W.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_of _ (B.emb w).1 fun h0 =>
    GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.skew.sig w) (by rw [Matrix.det_smul, h0, mul_zero])

theorem I_left (hU : Unimod) (hT : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (g₀ : UA σ X.J) : M.I om (om (g₀, 1) Φ) = M.I om Φ := by
  funext h
  obtain ⟨h1, -, h3⟩ := hU F E σ hp.base.cm n X.J 1 (fun i j => by simpa using hp.herm.herm i j) (detX hp)
  have h2 := h3 _ hp.good.haar
  have := hp.good.haar
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have e : ∀ g, theta om (om (g₀, 1) Φ) g h = theta om Φ (g * g₀) h := fun g => by
    simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e]
  exact L2.integral_right hp.good.dom (fun g => theta om Φ g h) (fun γ hγ g => by
    simpa using ((hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 γ hγ 1 (one_mem _) g h) g₀

theorem theta_add (hp : IsPair B M χX χW om r s r' s') {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _) (g h) :
    theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  simp only [theta, map_add]
  exact thetaSum_add F (hp.weil.isUSplitting.pres _ _ hΦ) (hp.weil.isUSplitting.pres _ _ hΨ)

def convS (hp : IsPair B M χX χW om r s r' s') : Submodule ℂ (Fn F n d) where
  carrier := {Φ | Φ ∈ schA F _ ∧ M.Conv om Φ}
  zero_mem' := ⟨zero_mem _, fun h => by simp [theta, thetaSum]⟩
  add_mem' := fun hΦ hΨ => ⟨add_mem hΦ.1 hΨ.1, fun h => by
    simp only [theta_add hp hΦ.1 hΨ.1]; exact (hΦ.2 h).add (hΨ.2 h)⟩
  smul_mem' := fun c Φ hΦ => ⟨Submodule.smul_mem _ _ hΦ.1, fun h => by
    simp only [theta, map_smul, thetaSum_smul]; exact (hΦ.2 h).const_mul c⟩

theorem I_add' (hp : IsPair B M χX χW om r s r' s') {Φ Ψ : Fn F n d} (hΦ : Φ ∈ convS hp) (hΨ : Ψ ∈ convS hp) :
    M.I om (Φ + Ψ) = M.I om Φ + M.I om Ψ := by
  funext h
  simp only [Model.I, theta_add hp hΦ.1 hΨ.1, Pi.add_apply]
  exact integral_add (hΦ.2 h) (hΨ.2 h)

def kerS (hp : IsPair B M χX χW om r s r' s') : Submodule ℂ (Fn F n d) where
  carrier := {Φ | Φ ∈ convS hp ∧ M.I om Φ = 0}
  zero_mem' := ⟨zero_mem _, I_zero _ _⟩
  add_mem' := fun hΦ hΨ => ⟨add_mem hΦ.1 hΨ.1, by rw [I_add' hp hΦ.1 hΨ.1, hΦ.2, hΨ.2, add_zero]⟩
  smul_mem' := fun c Φ hΦ => ⟨Submodule.smul_mem _ _ hΦ.1, funext fun h => by rw [ThKG.I_smul, hΦ.2]; simp⟩

theorem sub_mem_ker (hp : IsPair B M χX χW om r s r' s') {Φ Ψ : Fn F n d} (hΦ : Φ ∈ convS hp) (hΨ : Ψ ∈ convS hp) :
    Φ - Ψ ∈ kerS hp ↔ M.I om Φ = M.I om Ψ := by
  have := I_add' hp (sub_mem hΦ hΨ) hΨ
  rw [sub_add_cancel] at this
  refine ⟨fun h => by rw [this, h.2, zero_add], fun h => ⟨sub_mem hΦ hΨ, ?_⟩⟩
  rw [h] at this
  exact (add_eq_right.1 this.symm)

theorem dom_conv (hT : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕) (hs : φ ∈ SB _) :
    (∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ convS hp) ∧
      ∀ h, ∃ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f, L f = M.I om (pureA F f φ) h := by
  obtain ⟨p, k, G, hpc, -, hG, hb⟩ := hD φ hφ
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hl : ∀ (f : SInf F (Fin n × Fin d)) h, ∫⁻ g in M.dom, ‖theta om (pureA F f φ) g h‖ₑ ∂M.μ ≤
      ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * ∫⁻ g in M.dom, G g ∂M.μ := fun f h => by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun g => hb f g h
  have hc : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ convS hp := fun f => ⟨pureA_mem f hs, fun h =>
    ⟨(((hT F E σ B n d X W M χX χW om r s r' s' hp).1 _ (pureA_mem f hs)).1.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable,
      (hl f h).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG)⟩⟩
  refine ⟨hc, fun h => ?_⟩
  let l : SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun f => M.I om (pureA F f φ) h
      map_add' := fun f g => by
        rw [show pureA F (f + g : SInf F _) φ = pureA F f φ + pureA F g φ from funext fun x => add_mul _ _ _,
          I_add' hp (hc f) (hc g)]; rfl
      map_smul' := fun c f => by
        rw [show pureA F (c • f : SInf F _) φ = c • pureA F f φ from funext fun x => mul_assoc _ _ _, ThKG.I_smul]; rfl }
  refine ⟨⟨l, continuous_of_continuousAt_zero l ?_⟩, fun _ => rfl⟩
  rw [ContinuousAt, map_zero]
  refine squeeze_zero_norm (a := fun f => p f * (ht h : ℝ) ^ k * (∫⁻ g in M.dom, G g ∂M.μ).toReal) (fun f => ?_) ?_
  · refine (norm_integral_le_lintegral_norm _).trans ?_
    simp only [ofReal_norm]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.ne) (hl f h)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  · simpa using ((hpc.tendsto 0).mul_const _).mul_const _

theorem so_conv (hT : ThetaBasic) (hD : DomSoU) (hF : SoFin) (hp : IsPair B M χX χW om r s r' s') : M.So B.ψ B.τ₁ ≤ convS hp := by
  intro Φ hΦ
  obtain ⟨k, hk⟩ := hD F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨m, f, φ, h1, rfl⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
  exact Submodule.sum_mem _ fun i _ => (dom_conv hT hp (fun φ hφ => let ⟨p, G, h⟩ := hk φ hφ; ⟨p, k, G, h⟩) (h1 i) (h1 i).1).1 _

theorem iZero_of (hT : ThetaBasic) (hU : Unimod) (hW : DomWeil) (hD : DomSoU) (hF : SoFin) (hR : RealVanish) : IZero := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp m hm hd hr
  have key : ∀ 𝓕, Dom M om 𝓕 → ∀ φ ∈ 𝓕, φ ∈ SB _ → ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ kerS hp := fun 𝓕 h𝓕 φ hφ hs f => by
    obtain ⟨h1, h2⟩ := dom_conv hT hp h𝓕 hφ hs
    refine ⟨h1 f, funext fun h => ?_⟩
    obtain ⟨L, hL⟩ := h2 h
    rw [← hL, hR F E σ B n d X W M χX χW om r s r' s' hp m hm hd hr L fun g _ T hT' f => by
      rw [hL, hL, ← hT'.1 f φ hs, I_left hU hT hp (pureA_mem f hs)]]
    rfl
  obtain ⟨k, hk⟩ := hD F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨s1, s2, -⟩ := hF F E σ B n d X W M χX χW om r s r' s' hp
  refine ⟨fun hw Φ hΦ => ?_, fun Φ hΦ => ?_⟩
  · obtain ⟨m, f, φ, h1, rfl⟩ := s2 Φ hΦ
    exact (Submodule.sum_mem (kerS hp) fun i _ =>
      key _ (hW F E σ B n d X W M χX χW om r s r' s' hp (Or.inl hw)) _ (h1 i) (h1 i) _).2
  · obtain ⟨m, f, φ, h1, rfl⟩ := s1 Φ hΦ
    exact (Submodule.sum_mem (kerS hp) fun i _ =>
      key _ (fun φ hφ => let ⟨p, G, h⟩ := hk φ hφ; ⟨p, k, G, h⟩) _ (h1 i) (h1 i).1 _).2

theorem exists_proj {A : Type} [AddCommGroup A] [Module ℂ A] (G U : Submodule ℂ A) :
    ∃ π : A →ₗ[ℂ] A, (∀ x, π x ∈ G) ∧ ∀ x ∈ G ⊔ U, x - π x ∈ U := by
  let g := U.mkQ.domRestrict G
  obtain ⟨t, ht⟩ := g.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict g)
  obtain ⟨q, hq⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  refine ⟨G.subtype ∘ₗ t ∘ₗ q ∘ₗ U.mkQ, fun x => Subtype.prop _, fun x hx => ?_⟩
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
  have e : U.mkQ (y + u) = (g.rangeRestrict ⟨y, hy⟩).1 := by
    simp [g, (Submodule.Quotient.mk_eq_zero U).2 hu]
  have e1 : q (U.mkQ (y + u)) = g.rangeRestrict ⟨y, hy⟩ := by
    rw [e]; exact LinearMap.congr_fun hq (g.rangeRestrict ⟨y, hy⟩)
  have e2 := congrArg Subtype.val (LinearMap.congr_fun ht (g.rangeRestrict ⟨y, hy⟩))
  rw [← Submodule.Quotient.eq]
  simp only [LinearMap.comp_apply, e1]
  exact e.trans e2.symm

theorem upd_sb {κ : Type} [Fintype κ] {v : Pl F} {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {z} (hz : z ∈ SB _) (u : Pl F) :
    Function.update φ v z u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [Function.update_self]
  · rw [Function.update_of_ne e]; exact h u

theorem upd_cof {κ : Type} {v : Pl F} {φ φ' : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = φ' u) (z) :
    ∀ᶠ u in cofinite, Function.update φ v z u = φ' u :=
  (h.and (eventually_cofinite_ne v)).mono fun _ e => by rw [Function.update_of_ne e.2]; exact e.1

theorem upd_so (hM : M.IsGood B.ψ) (f : SInf F (Fin n × Fin d)) {φ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u) {z}
    (hz : z ∈ Submodule.span ℂ (M.SoLoc B.ψ B.τ₁)) : pure f (Function.update φ B.v₁ z) ∈ M.So B.ψ B.τ₁ :=
  pure_update_mem hM.std h2 _ f _ (S := M.SoLoc B.ψ B.τ₁)
    (fun ψ' h' => Submodule.subset_span (by exact ⟨f, _, upd_sb h1 h'.1, upd_cof h2 _, by simpa using h', rfl⟩)) hz

theorem soMove_of (hT : ThetaBasic) (hU : Unimod) (hD : DomSoU) (hF : SoFin) (hP : TriplePair) (hL : SoLower) : SoMove := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hp₁ e he Φ' hΦ'
  obtain ⟨-, hp, -⟩ := hP F E σ B a a' G X om om' hTr
  obtain ⟨ei, ev, hne, hvac, hpure⟩ := he.loc
  have haB := hTr.geo.aBig
  have hrk := hH.rank
  have hlt := hTr.geo.lt
  have key := hL F E σ B _ _ _ _ _ _ G.M' M₁ _ _ om' om₁ _ _ _ _ _ _ H' i₀ i₁ hp hp₁ hH (by omega) (by omega)
    (PositivityTheory.KCo.nu_statement F E σ B a a' G X om om' hTr B.v₁ hTr.chars.good) e ei ev he ⟨hne, hvac, hpure⟩
  obtain ⟨π, hπ, hπ'⟩ := exists_proj (Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) ⊓ (Submodule.span ℂ (M₁.SoLoc B.ψ B.τ₁)).comap (ev B.v₁))
    (augOn om' B.v₁ (G.M'.SoLoc B.ψ B.τ₁))
  have hsb : ∀ x, π x ∈ SB _ := fun x => soLoc_sub _ _ _ (hπ x).1
  have hc := so_conv hT hD hF hp
  have hst := PositivityTheory.KCo.so_stable G.M' hp.base.cm hp.base.std (detX hp) (detW hp) hp.good hp.weil.isUSplitting.toIsSplitting B.τ₁
  have A : opL B.v₁ π Φ' ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ⊓ (M₁.So B.ψ B.τ₁).comap e := by
    rw [← Submodule.mem_comap]
    refine Submodule.span_le.2 ?_ hΦ'.1
    rintro _ ⟨f, hf, φ, h1, h2, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, opL_pure hp.good.std h2]
    refine ⟨⟨Submodule.subset_span (by exact ⟨f, hf, _, upd_sb h1 (hsb _), upd_cof h2 _, rfl⟩), upd_so hp.good f h1 h2 (hπ _).1⟩, ?_⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hpure f _ (upd_sb h1 (hsb _)) (upd_cof h2 _)]
    have := upd_so hp₁.good (ei f) (φ := fun v => ev v (φ v)) (fun v => (hvac v).2 ▸ Submodule.mem_map_of_mem (h1 v))
      (h2.mono fun v hv => by rw [hv, (hvac v).1]) (hπ (φ B.v₁)).2
    convert this using 2
    funext v
    by_cases hv : v = B.v₁
    · subst hv; simp
    · simp [Function.update_of_ne hv]
  refine ⟨_, A.1, ((sub_mem_ker hp (hc hΦ'.2) (hc A.1.2)).1 ?_).symm, A.2⟩
  refine (Submodule.span_le (p := Submodule.comap (LinearMap.id - opL B.v₁ π) (kerS hp))).2 ?_ hΦ'.2
  rintro _ ⟨f, φ, h1, h2, h3, rfl⟩
  obtain ⟨t, ht, er⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_at G.M' B.ψ hp.good φ h2 f B.v₁
  have er' : ∀ z, pure f (Function.update φ B.v₁ z) = tens (evFin F B.v₁) z t := fun z => by
    rw [er _ fun w hw => Function.update_of_ne hw _ _, Function.update_self]
  have esub : ∀ z z', pure f (Function.update φ B.v₁ (z - z')) =
      pure f (Function.update φ B.v₁ z) - pure f (Function.update φ B.v₁ z') := fun z z' => by
    rw [er', er', er']; exact funext fun _ => sub_mul _ _ _
  obtain ⟨φ', k1, k2, k3⟩ := key _ h3
  have hu := hπ' (φ B.v₁) (Submodule.mem_sup.2 ⟨φ', ⟨Submodule.subset_span k1, Submodule.subset_span k3⟩, _, k2, by abel⟩)
  have := pure_update_mem hp.good.std h2 B.v₁ f (kerS hp) (fun z hz => ?_) hu
  · rw [esub, Function.update_eq_self] at this
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, opL_pure hp.good.std h2]
    exact this
  · obtain ⟨g, -, x, hx, y, -, ha, rfl⟩ := hz
    have hx' := upd_so hp.good f h1 h2 (Submodule.subset_span hx)
    have e := ha t ⟨ht, er' x ▸ (hc hx').1⟩
    rw [← er', ← er'] at e
    rw [esub, ← e]
    exact (sub_mem_ker hp (hc (hst _ _ hx')) (hc hx')).2 (I_left hU hT hp (hc hx').1 g)

theorem conePol_of (hM : MeasEx) (hC : ConeIntegralFactorisation) : ConePol := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ hΦ
  obtain ⟨e₁, e₂, hC⟩ := hC
  obtain ⟨ei, ev, hne, hvac, hpure⟩ := he.loc
  obtain ⟨m, hm⟩ := hM F E σ B _ G.V _ _ hT.base hT.geo.hV K hK
  obtain ⟨κ, -, hC⟩ := hC F E σ B b a' G G₁ H H' hc e ei ev he ⟨hne, hvac, hpure⟩ K μK μ m hK hμK hμ hm
  obtain ⟨L, Λ, u, -, hL, hΛ, hu, hlin, hT'⟩ := hC X om om' om₁ om₁' hT hT₁
  have z : cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) 0 = 0 := by
    simpa using hlin 0 (zero_mem _) 0 (zero_mem _) (-1)
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := h
    let T : Finset (Pl F) := X.T ∪ (eventually_cofinite.1 h2).toFinset
    have := hT' T Finset.subset_union_left f φ h1 fun v hv => by
      by_contra h
      exact hv (Finset.mem_union_right _ (by simpa using h))
    have hu0 : ∏ v ∈ T \ X.T, u v ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (hu v (Finset.mem_sdiff.1 hv).2).1
    rw [← (PolData B G₁.M).smul_mem_iff hu0, this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hL f hf, _, fun v => ?_, ?_, rfl⟩)
    · split_ifs
      · exact (hΛ v _ (h1 v)).2
      · exact (hT₁.geo.hM.vac v).1
    · exact T.eventually_cofinite_notMem.mono fun v hv => if_neg hv
  | zero => rw [z]; exact zero_mem _
  | add x y hx hy h1 h2 =>
    have := hlin x (polData_le hT.geo.hM hx) y (polData_le hT.geo.hM hy) 1
    rw [one_smul, one_smul] at this
    rw [this]; exact add_mem h1 h2
  | smul c x hx h1 =>
    have := hlin 0 (zero_mem _) x (polData_le hT.geo.hM hx) c
    rw [zero_add, z, zero_add] at this
    rw [this]; exact Submodule.smul_mem _ _ h1

end PositivityTheory.ThKEnd.Comp

end
