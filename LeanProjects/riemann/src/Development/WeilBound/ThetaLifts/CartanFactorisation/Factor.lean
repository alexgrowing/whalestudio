import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsPureML
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def ILeft : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F _, ∀ g, M.I om (om (g, 1) Φ) = M.I om Φ

theorem exists_Ilin {ψ : AddChar (AF F) ℂ} {M : Model σ X W} {om : Rep σ X W} {χ χ' : Chr F E} (hw : M.IsWeil ψ χ χ' om)
    (C : Submodule ℂ (Fn F n d)) (h1 : C ≤ schA F _) (h2 : ∀ Φ ∈ C, M.Conv om Φ) :
    ∃ J : Fn F n d →ₗ[ℂ] (UA σ W.J → ℂ), ∀ Φ ∈ C, J Φ = M.I om Φ := by
  let J₀ : C →ₗ[ℂ] (UA σ W.J → ℂ) :=
    { toFun := fun Φ => M.I om Φ
      map_add' := fun Φ Ψ => funext fun h => by
        have e : ∀ g, theta om (Φ.1 + Ψ.1) g h = theta om Φ g h + theta om Ψ g h := fun g => by
          simp only [theta, map_add]
          exact thetaSum_add F (hw.isUSplitting.pres _ _ (h1 Φ.2)) (hw.isUSplitting.pres _ _ (h1 Ψ.2))
        simp only [Model.I, Submodule.coe_add, e, Pi.add_apply]
        exact integral_add (h2 _ Φ.2 h) (h2 _ Ψ.2 h)
      map_smul' := fun c Φ => funext fun h => I_smul M om c Φ h }
  obtain ⟨J, hJ⟩ := LinearMap.exists_extend J₀
  exact ⟨J, fun Φ hΦ => LinearMap.congr_fun hJ ⟨Φ, hΦ⟩⟩

theorem vanish {κ : Type} [Fintype κ] {Z P : Type} [AddCommGroup Z] [Module ℂ Z] [AddCommGroup P] [Module ℂ P]
    {Q : Pl F → Type} [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (J : ((κ → AF F) → ℂ) →ₗ[ℂ] Z)
    {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (T : Finset (Pl F)) (p : SInf F κ →ₗ[ℂ] P)
    (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v) (S₀ : Submodule ℂ (SInf F κ)) (S : ∀ v : Pl F, Submodule ℂ ((κ → Fv F v) → ℂ))
    (hS : ∀ v ∉ T, w v ∈ S v)
    (h : ∀ f ∈ S₀, ∀ φ, (∀ v, φ v ∈ S v) → (∀ v ∉ T, φ v = w v) → (p f = 0 ∨ ∃ v, q v (φ v) = 0) → J (pure f φ) = 0)
    {m : ℕ} (f : Fin m → SInf F κ) (φ : Fin m → ∀ v : Pl F, (κ → Fv F v) → ℂ) (hf : ∀ i, f i ∈ S₀)
    (hφ : ∀ i v, φ i v ∈ S v) (hoff : ∀ i, ∀ v ∉ T, φ i v = w v)
    (h0 : ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) = 0) : J (∑ i, pure (f i) (φ i)) = 0 := by
  obtain ⟨l, hl⟩ := exists_pureML hw T
  obtain ⟨L, hL⟩ := desc (Q := fun v : T => Q v) ((LinearMap.compMultilinearMapₗ ℂ J) ∘ₗ l) p (fun v : T => q v) S₀ (fun v => S v)
    (fun f hf ψ hψ hz => by
      change J (l f ψ) = 0
      rw [hl]
      refine h f hf _ (fun v => ?_) (ext_off w T ψ) (hz.imp_right fun ⟨v, hv⟩ => ⟨v, ?_⟩)
      · unfold ext; split_ifs with hv
        exacts [hψ ⟨v, hv⟩, hS v hv]
      · unfold ext; rw [dif_pos v.2]; exact hv)
  have := congrArg L h0
  rw [map_sum, map_zero] at this
  rw [map_sum, ← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hL (f i) (hf i) (fun v => φ i v) fun v => hφ i v]
  change _ = J (l (f i) _)
  rw [hl, ext_of (hoff i)]

theorem good_std {ψ : AddChar (AF F) ℂ} {M : Model σ X W} (hM : M.IsGood ψ) : Std M.vac := hM.std

theorem pure_mem_So {ψ : AddChar (AF F) ℂ} {M : Model σ X W} (hM : M.IsGood ψ) {v₁ : Pl F} (t : E →ₐ[F] Fv F v₁)
    (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (h1 : ∀ v ≠ v₁, φ v ∈ SB _)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) (h3 : φ v₁ ∈ Submodule.span ℂ (M.SoLoc ψ t)) : pure f φ ∈ M.So ψ t := by
  obtain ⟨r, -, hr⟩ := GlobalTheory.PureFactor.exists_rest_factor v₁ f φ ((good_std hM).congr h2)
  have key : ∀ z ∈ Submodule.span ℂ (M.SoLoc ψ t), tens (evFin F v₁) z r ∈ M.So ψ t := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rw [hr]
      refine Submodule.subset_span ⟨f, _, fun v => ?_, ?_, by rw [Function.update_self]; exact hz, rfl⟩
      · by_cases hv : v = v₁
        · subst hv; rw [Function.update_self]; exact hz.1
        · rw [Function.update_of_ne hv]; exact h1 v hv
      · filter_upwards [h2, Filter.eventually_cofinite_ne v₁] with v hv hne
        rw [Function.update_of_ne hne]; exact hv
    | zero =>
      have : tens (evFin F v₁) (0 : (Fin n × Fin d → Fv F v₁) → ℂ) r = 0 := funext fun x => zero_mul _
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : tens (evFin F v₁) (x + y) r = tens (evFin F v₁) x r + tens (evFin F v₁) y r := funext fun _ => add_mul _ _ _
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : tens (evFin F v₁) (a • x) r = a • tens (evFin F v₁) x r := funext fun _ => mul_assoc _ _ _
      rw [this]; exact Submodule.smul_mem _ a hx
  have := key _ h3
  rwa [hr, Function.update_eq_self] at this

theorem soLoc_le {ψ : AddChar (AF F) ℂ} (M : Model σ X W) {v₁ : Pl F} (t : E →ₐ[F] Fv F v₁) :
    Submodule.span ℂ (M.SoLoc ψ t) ≤ SB _ := Submodule.span_le.2 fun _ h => h.1

theorem so_le {ψ : AddChar (AF F) ℂ} {M : Model σ X W} (hM : M.IsGood ψ) {v₁ : Pl F} (t : E →ₐ[F] Fv F v₁) :
    M.So ψ t ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ h1 ((good_std hM).congr h2)

theorem so_proj {ψ : AddChar (AF F) ℂ} {M : Model σ X W} (hM : M.IsGood ψ) {v₁ : Pl F} (t : E →ₐ[F] Fv F v₁) :
    ∃ π : Module.End ℂ ((Fin n × Fin d → Fv F v₁) → ℂ), (∀ x, π x ∈ Submodule.span ℂ (M.SoLoc ψ t)) ∧
      ∀ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ i, Std (φ i)) →
        ∑ i, pure (f i) (φ i) ∈ M.So ψ t →
        ∑ i, pure (f i) (φ i) = ∑ i, pure (f i) (Function.update (φ i) v₁ (π (φ i v₁))) := by
  obtain ⟨π, h1, h2⟩ := exists_section (LinearMap.id : Module.End ℂ _) (Submodule.span ℂ (M.SoLoc ψ t))
  obtain ⟨O, hO⟩ := exists_factorOp (κ := Fin n × Fin d) v₁ π
  refine ⟨π, h1, fun m f φ hφ hs => ?_⟩
  have key : ∀ Φ ∈ M.So ψ t, O Φ = Φ := by
    intro Φ hΦ
    refine LinearMap.eqOn_span (g := LinearMap.id) ?_ hΦ
    rintro _ ⟨f, φ, -, h4, h5, rfl⟩
    rw [hO f φ ((good_std hM).congr h4), show π (φ v₁) = φ v₁ from h2 _ (Submodule.subset_span h5), Function.update_eq_self]
    rfl
  rw [← key _ hs, map_sum]
  exact Finset.sum_congr rfl fun i _ => hO _ _ (hφ i)

theorem factor_of (hD : KDecay) (hK : Kills) : Factor := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm
  obtain ⟨dc, dc'⟩ := hD F E σ B a a' G X om om' hm.triple
  obtain ⟨k, k'⟩ := hK F E σ B a a' G X om om' R Rf hm
  have g := hm.triple.geo.hM
  have g' := hm.triple.geo.hM'
  constructor
  · rintro Φ ⟨T, -, m, m', f, φ, f', φ', h1, h2, rfl, e0, e⟩
    obtain ⟨J, hJ⟩ := exists_Ilin hm.triple.weil (schA F _) le_rfl dc
    have mem : ∀ f (φ : ∀ v : Pl F, _), (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = G.M.vac v) → pure f φ ∈ schA F _ := fun f φ a b =>
      GlobalTheory.TensUniq.pure_mem_schA f φ a ((good_std g).congr (ev_of_off b))
    rw [← hJ _ (sum_mem fun i _ => mem _ _ (h1 i).2.1 (h1 i).2.2)]
    refine vanish J (good_std g) T R.p Rf.p (G.M.Pol B.ψ B.emb) (fun _ => SB _) (fun v _ => (g.vac v).1)
      (fun f hf φ a b c => ?_) f φ (fun i => (h1 i).1) (fun i => (h1 i).2.1) (fun i => (h1 i).2.2) ?_
    · rw [hJ _ (mem f φ a b)]; exact k f hf φ a (ev_of_off b) c
    · rw [e, tens_eq_map (fun v => (g'.vac v).2.1) (good_std g') T f' φ' (ι' := Empty) Empty.elim Empty.elim
        (fun i => (h2 i).2.2) (fun i => i.elim) (by rw [← e0]; simp)]
      simp
  · rintro Φ' hΦ' ⟨T, -, m, m', f, φ, f', φ', h1, h2, e0, rfl, e⟩
    obtain ⟨J, hJ⟩ := exists_Ilin hm.triple.weil' (G.M'.So B.ψ B.τ₁) (so_le g' _) fun Φ h => (dc' Φ h).2.1
    obtain ⟨π, p1, p2⟩ := so_proj g' B.τ₁
    have e1 := p2 m' f' φ' (fun i => (good_std g').congr (ev_of_off (h2 i).2.2)) hΦ'
    rw [← hJ _ hΦ', e1]
    have z : ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v)) = 0 := by
      rw [← e, tens_eq_map (fun v => (g.vac v).2.1) (good_std g) T f φ (ι' := Empty) Empty.elim Empty.elim
        (fun i => (h1 i).2.2) (fun i => i.elim) (by rw [← e0]; simp)]
      simp
    let w := Function.update G.M'.vac B.v₁ (π (G.M'.vac B.v₁))
    have hwv : ∀ᶠ v in cofinite, w v = G.M'.vac v := by
      filter_upwards [Filter.eventually_cofinite_ne B.v₁] with v hv using Function.update_of_ne hv _ _
    let S : ∀ v : Pl F, Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
      Function.update (fun _ => SB _) B.v₁ (Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁))
    have S1 : S B.v₁ = Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) := Function.update_self _ _ _
    have S2 : ∀ v ≠ B.v₁, S v = SB _ := fun v hv => Function.update_of_ne hv _ _
    have up : ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → ∀ v, Function.update φ B.v₁ (π (φ B.v₁)) v ∈ S v := fun φ h v => by
      by_cases hv : v = B.v₁
      · subst hv; rw [Function.update_self, S1]; exact p1 _
      · rw [Function.update_of_ne hv, S2 v hv]; exact h v
    have off : ∀ j, ∀ v ∉ T, Function.update (φ' j) B.v₁ (π (φ' j B.v₁)) v = w v := fun j v hv => by
      by_cases h : v = B.v₁
      · subst h; simp only [w, Function.update_self, (h2 j).2.2 _ hv]
      · simp only [w, Function.update_of_ne h, (h2 j).2.2 _ hv]
    refine vanish J ((good_std g').congr hwv) T R.p' Rf.p' (G.M'.Pol B.ψ B.emb) S (fun v _ => up _ (fun v => (g'.vac v).1) v)
      (fun f hf φ a b c => ?_) f' _ (fun i => (h2 i).1) (fun i => up _ (h2 i).2.1) off ?_
    · have ev : ∀ᶠ v in cofinite, φ v = G.M'.vac v := by
        filter_upwards [ev_of_off b, hwv] with v x y using x.trans y
      have s1 : φ B.v₁ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) := S1 ▸ a B.v₁
      have s2 : ∀ v, φ v ∈ SB _ := fun v => by
        by_cases hv : v = B.v₁
        · subst hv; exact soLoc_le _ _ s1
        · exact S2 v hv ▸ a v
      rw [hJ _ (pure_mem_So g' _ f φ (fun v _ => s2 v) ev s1)]
      exact k' f hf φ s2 ev s1 c
    · by_cases hv : B.v₁ ∈ T
      · rw [← z]
        exact (tens_eq_map (fun v => (g'.vac v).2.1) (good_std g') T f' φ' f' _ (fun i => (h2 i).2.2)
          (fun i v h => by rw [Function.update_of_ne (fun x : v = B.v₁ => h (x ▸ hv))]; exact (h2 i).2.2 v h) e1 _ _).symm
      · rw [← z]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 2
        funext v
        rw [Function.update_of_ne (fun x : v.1 = B.v₁ => hv (x ▸ v.2))]

end PositivityTheory.ThKF

end
