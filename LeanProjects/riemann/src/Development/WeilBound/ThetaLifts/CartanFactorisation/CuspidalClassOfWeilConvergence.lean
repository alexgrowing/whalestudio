import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsPureML
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.LocalTheory.SplitInv

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

structure Cls0 (M : Model σ X W) (om : Rep σ X W) (𝓒 : Submodule ℂ (Fn F n d)) : Prop where
  sch : 𝓒 ≤ schA F _
  conv : ∀ Φ ∈ 𝓒, M.Conv om Φ
  contf : ∀ ψ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f ψ ∈ 𝓒) →
    ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f ψ) h

theorem inj_add (hp : IsPair B M χX χW om r s r' s') {𝓒} (hc : Cls0 M om 𝓒) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ 𝓒) (hΨ : Ψ ∈ 𝓒) :
    M.I om (Φ + Ψ) = M.I om Φ + M.I om Ψ := by
  funext h
  have e : ∀ g, theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun g => by
    simp only [theta, map_add]
    exact thetaSum_add F (hp.weil.isUSplitting.pres _ _ (hc.sch hΦ)) (hp.weil.isUSplitting.pres _ _ (hc.sch hΨ))
  simp only [Model.I, e, Pi.add_apply]
  exact integral_add (hc.conv _ hΦ h) (hc.conv _ hΨ h)

theorem inj_smul (c : ℂ) (Φ : Fn F n d) : M.I om (c • Φ) = c • M.I om Φ := funext fun h => PositivityTheory.ThKG.I_smul M om c Φ h

theorem inj_right (Φ : Fn F n d) (h₀ h : UA σ W.J) : M.I om (om (1, h₀) Φ) h = M.I om Φ (h * h₀) := by
  simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem inj_at {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev :=
  fun u _ => by simp [mat]

theorem inj_kinf {m : ℕ} {Y : Spc F E m} (τ) : (1 : UA σ Y.J) ∈ KInf σ Y τ :=
  ⟨inj_at _, fun w => by
    have : (mat (1 : UA σ Y.J)).map (piInf (τ w)) = 1 := by simp [mat]
    rw [this]; exact Commute.one_left _⟩

theorem inj_line {m : ℕ} {Y : Spc F E m} : (1 : Multiplicative ℝ →* UA σ Y.J) ∈ Lines σ Y :=
  ⟨continuous_const, fun _ => inj_at _⟩

theorem upd_mem {κ : Type} {S : ∀ v : Pl F, Submodule ℂ ((κ → Fv F v) → ℂ)} {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ}
    (h : ∀ u, φ u ∈ S u) {v : Pl F} {x} (hx : x ∈ S v) (u) : Function.update φ v x u ∈ S u := by
  by_cases e : u = v
  · subst e; rwa [Function.update_self]
  · rw [Function.update_of_ne e]; exact h u

theorem upd_ev {κ : Type} {φ ψ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = ψ u) (v : Pl F) (x) :
    ∀ᶠ u in cofinite, Function.update φ v x u = ψ u :=
  (h.and (Filter.eventually_cofinite_ne v)).mono fun _ hu => (Function.update_of_ne hu.2 ..).trans hu.1

def kerIn {A P : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] (S : Submodule ℂ A) (p : A →ₗ[ℂ] P)
    (K : Submodule ℂ A) : Submodule ℂ P := (K ⊓ S).map p

theorem mem_kerIn {A P : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] {S : Submodule ℂ A} {p : A →ₗ[ℂ] P}
    {K : Submodule ℂ A} (hk : ∀ x ∈ S, p x = 0 → x ∈ K) {x : A} (hx : x ∈ S) : p x ∈ kerIn S p K ↔ x ∈ K := by
  refine ⟨?_, fun h => ⟨x, ⟨h, hx⟩, rfl⟩⟩
  rintro ⟨y, hy, e⟩
  have := K.add_mem hy.1 (hk _ (S.sub_mem hx hy.2) (by rw [map_sub, e, sub_self]))
  rwa [add_sub_cancel] at this

theorem injGen (hO : ArchOp) (hLie : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {𝓒} (hc : Cls0 M om 𝓒)
    (S : ∀ v : Pl F, Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ)) (hS : ∀ v, S v ≤ SB _)
    (h𝓒 : ∀ (f : SInf F (Fin n × Fin d)) φ, (∀ v, φ v ∈ S v) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ∈ 𝓒)
    {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {Pf : Pl F → Type} [∀ v, AddCommGroup (Pf v)] [∀ v, Module ℂ (Pf v)] (pf : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Pf v)
    (kill : ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ, (∀ v, φ v ∈ S v) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      (p f = 0 ∨ ∃ v, pf v (φ v) = 0) → M.I om (pure f φ) = 0)
    (irrF : ∀ v, ∀ N : Submodule ℂ (Pf v), (∀ h ∈ UAt σ W (evFin F v), ∀ x ∈ S v, ∀ x₁ ∈ S v,
      Acts (evFin F v) (om (1, h)) x x₁ → pf v x ∈ N → pf v x₁ ∈ N) → N = ⊥ ∨ N = ⊤)
    (irrI : ∀ N : Submodule ℂ P,
      (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F _,
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f ∈ N → p f₁ ∈ N) →
      (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F _,
        Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N) → N = ⊥ ∨ N = ⊤)
    {f} (hf : f ∈ M.Pol B.ψ B.emb) {φ} (h1 : ∀ v, φ v ∈ S v) (h2 : ∀ᶠ v in cofinite, φ v = M.vac v)
    (pf0 : p f ≠ 0) (pφ : ∀ v, pf v (φ v) ≠ 0) (h0 : M.I om (pure f φ) = 0) :
    ∀ g ∈ M.Pol B.ψ B.emb, ∀ ψ, (∀ v, ψ v ∈ S v) → (∀ᶠ v in cofinite, ψ v = M.vac v) → M.I om (pure g ψ) = 0 := by
  have stepF : ∀ χ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ, (∀ v, χ v ∈ S v) → (∀ᶠ v in cofinite, χ v = M.vac v) →
      ∀ v, pf v (χ v) ≠ 0 → M.I om (pure f χ) = 0 → ∀ x ∈ S v, M.I om (pure f (Function.update χ v x)) = 0 := by
    intro χ c1 c2 v c3 c0
    have c4 := (c2.and hp.good.std).mono fun _ h => h.1.trans h.2
    have l : ∀ x y (a : ℂ), pure f (Function.update χ v (x + a • y)) =
        pure f (Function.update χ v x) + a • pure f (Function.update χ v y) := (pureAct F _ v id f χ (fun u => hS u (c1 u)) c4).2.1
    have mem : ∀ x ∈ S v, pure f (Function.update χ v x) ∈ 𝓒 := fun x hx => h𝓒 _ _ (upd_mem c1 hx) (upd_ev c2 v x)
    have kl : ∀ x ∈ S v, pf v x = 0 → M.I om (pure f (Function.update χ v x)) = 0 := fun x hx e =>
      kill f hf _ (upd_mem c1 hx) (upd_ev c2 v x) (Or.inr ⟨v, by rwa [Function.update_self]⟩)
    let K : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ) :=
      { carrier := {x | x ∈ S v ∧ M.I om (pure f (Function.update χ v x)) = 0}
        zero_mem' := ⟨zero_mem _, kl 0 (zero_mem _) (map_zero _)⟩
        add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
          have := l x y 1
          simp only [one_smul] at this
          rw [this, inj_add hp hc (mem x hx.1) (mem y hy.1), hx.2, hy.2, add_zero]⟩
        smul_mem' := fun a x hx => ⟨(S v).smul_mem a hx.1, by
          have := l 0 x a
          rw [zero_add] at this
          rw [this, inj_add hp hc (mem 0 (zero_mem _)) (𝓒.smul_mem a (mem x hx.1)), inj_smul, hx.2,
            kl 0 (zero_mem _) (map_zero _), smul_zero, add_zero]⟩ }
    have hk : ∀ x ∈ S v, pf v x = 0 → x ∈ K := fun x hx e => ⟨hx, kl x hx e⟩
    rcases irrF v (kerIn (S v) (pf v) K) (fun h hh x hx x₁ hx₁ ha hN => (mem_kerIn hk hx₁).2 ⟨hx₁, by
      have e := (pureAct F _ v (om (1, h)) f (Function.update χ v x) (fun u => hS u (upd_mem c1 hx u)) (upd_ev c4 v x)).2.2 x₁
        (by rwa [Function.update_self])
      have e' : om (1, h) (pure f (Function.update χ v x)) = pure f (Function.update χ v x₁) :=
        e.trans (congrArg (pure f) (Function.update_idem ..))
      funext g
      rw [← e', inj_right, ((mem_kerIn hk hx).1 hN).2]; rfl⟩) with hb | hb
    · exfalso
      have : pf v (χ v) ∈ kerIn (S v) (pf v) K := (mem_kerIn hk (c1 v)).2 ⟨c1 v, by rwa [Function.update_eq_self]⟩
      rw [hb] at this
      exact c3 this
    · exact fun x hx => ((mem_kerIn hk hx).1 (hb ▸ Submodule.mem_top)).2
  intro g hg ψ k1 k2
  have fin : ∀ T : Finset (Pl F), M.I om (pure f (T.piecewise ψ φ)) = 0 := fun T => by
    induction T using Finset.induction_on with
    | empty => rwa [Finset.piecewise_empty]
    | insert v T hv ih =>
      rw [Finset.piecewise_insert]
      refine stepF _ (fun u => ?_) ?_ v (by rw [Finset.piecewise_eq_of_notMem _ _ _ hv]; exact pφ v) ih _ (k1 v)
      · by_cases hu : u ∈ T
        · rw [Finset.piecewise_eq_of_mem _ _ _ hu]; exact k1 u
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hu]; exact h1 u
      · filter_upwards [h2, T.eventually_cofinite_notMem] with u e hu
        rwa [Finset.piecewise_eq_of_notMem _ _ _ hu]
  have hψ0 : M.I om (pure f ψ) = 0 := by
    have hfin : {v | ¬ (φ v = ψ v)}.Finite := Filter.eventually_cofinite.1 ((h2.and k2).mono fun _ h => h.1.trans h.2.symm)
    have := fin hfin.toFinset
    rwa [show hfin.toFinset.piecewise ψ φ = ψ from funext fun u => by
      by_cases hu : u ∈ hfin.toFinset
      · exact Finset.piecewise_eq_of_mem _ _ _ hu
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hu]; simpa using hu] at this
  obtain ⟨ξ, hξ, eξ⟩ := PositivityTheory.ThKG.pure_eq_pureA hp.good ψ (fun u => hS u (k1 u)) k2
  have mem : ∀ x : SInf F (Fin n × Fin d), pureA F x ξ ∈ 𝓒 := fun x => eξ x ▸ h𝓒 x ψ k1 k2
  let L : UA σ W.J → SInf F (Fin n × Fin d) →L[ℂ] ℂ := fun h =>
    { toFun := fun f => M.I om (pureA F f ξ) h
      map_add' := fun f g => by
        have : pureA F ⇑(f + g) ξ = pureA F f ξ + pureA F g ξ := by funext x; simp [pureA, add_mul]
        rw [this, inj_add hp hc (mem f) (mem g)]; rfl
      map_smul' := fun c f => by
        have : pureA F ⇑(c • f) ξ = c • pureA F f ξ := by funext x; simp [pureA, mul_assoc]
        rw [this, PositivityTheory.ThKG.I_smul]; rfl
      cont := hc.contf ξ hξ mem h }
  have hL : ∀ h x, L h x = M.I om (pureA F x ξ) h := fun _ _ => rfl
  let K : Submodule ℂ (SInf F (Fin n × Fin d)) := ⨅ h, LinearMap.ker (L h : _ →ₗ[ℂ] ℂ)
  have mK : ∀ x, x ∈ K ↔ ∀ h, L h x = 0 := fun x => by simp [K, Submodule.mem_iInf]
  have mK' : ∀ x, x ∈ K ↔ M.I om (pure x ψ) = 0 := fun x => by rw [mK, eξ]; exact ⟨fun h => funext h, fun h g => congrFun h g⟩
  have hk : ∀ x ∈ M.Pol B.ψ B.emb, p x = 0 → x ∈ K := fun x hx e => (mK' x).2 (kill x hx ψ k1 k2 (Or.inl e))
  choose op hop hopP using hO F E σ B n d X W M χX χW om r s r' s' hp 1 (inj_at _)
  have LW : ∀ h hh g x, L g (op h hh x) = L (g * h) x := fun h hh g x => by
    rw [hL, hL, ← (hop h hh).1 x ξ hξ, inj_right]
  rcases irrI (kerIn (M.Pol B.ψ B.emb) p K) (fun γ hγ x hx x₁ ha hN => by
      obtain ⟨y, h3, h4, h5⟩ := hLie F E σ B n d X W M χX χW om r s r' s' hp 1 inj_line γ hγ (fun t => op _ (hγ.2 _))
        (fun t => hop _ _) x hx
      obtain rfl : x₁ = y := (hQ F _ x x₁ y).2 _ ha h4
      refine (mem_kerIn hk h3).2 ((mK _).2 fun g => (h5 (L g)).unique ?_)
      simp only [LW, (mK x).1 ((mem_kerIn hk hx).1 hN)]
      exact hasDerivAt_const _ _) (fun k hk' x hx x₁ ha hN => by
      obtain rfl : x₁ = op k hk'.1 x := (hQ F _ x x₁ _).1 _ ha ((hop k _).2 x)
      refine (mem_kerIn hk (hopP k _ (inj_kinf _) hk' x hx)).2 ((mK _).2 fun g => ?_)
      rw [LW]; exact (mK x).1 ((mem_kerIn hk hx).1 hN) _) with hb | hb
  · exfalso
    have : p f ∈ kerIn (M.Pol B.ψ B.emb) p K := (mem_kerIn hk hf).2 ((mK' f).2 hψ0)
    rw [hb] at this
    exact pf0 this
  · exact (mK' g).1 ((mem_kerIn hk hg).1 (hb ▸ Submodule.mem_top))

theorem I_span (hp : IsPair B M χX χW om r s r' s') {𝓒} (hc : Cls0 M om 𝓒) {s₀ : Set (Fn F n d)}
    (h : ∀ Φ ∈ s₀, Φ ∈ 𝓒 ∧ M.I om Φ = 0) : ∀ Φ ∈ Submodule.span ℂ s₀, Φ ∈ 𝓒 ∧ M.I om Φ = 0 := fun Φ hΦ => by
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨zero_mem _, PositivityTheory.ThKG.I_zero M om⟩
  | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, by rw [inj_add hp hc hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  | smul a x _ hx => exact ⟨𝓒.smul_mem a hx.1, by rw [inj_smul, hx.2, smul_zero]⟩

theorem cuspidal_class_of_weil_convergence (hW : WeilConv) (hp : IsPair B M χX χW om r s r' s') (h : d + 2 * min r s < 2 * n ∨ min r s = 0) :
    Cls0 M om (schA F _) :=
  have := hW F E σ B n d X W M χX χW om r s r' s' hp h
  ⟨le_rfl, fun Φ hΦ => (this.1 Φ hΦ).1, fun ψ hψ _ g => this.2 ψ hψ g⟩

theorem soLoc_leI {v : Pl F} (t : E →ₐ[F] Fv F v) : Submodule.span ℂ (M.SoLoc B.ψ t) ≤ SB _ :=
  Submodule.span_le.2 fun _ h => h.1

theorem so_leI (hp : IsPair B M χX χW om r s r' s') : M.So B.ψ B.τ₁ ≤ schA F _ := Submodule.span_le.2 (by
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hp.good φ h1 h2
  rw [e]; exact PositivityTheory.ThKG.pureA_mem f hg)

theorem pure_so (hp : IsPair B M χX χW om r s r' s') (f : SInf F (Fin n × Fin d)) {φ} (h1 : ∀ v, φ v ∈ SB _)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) {x} (hx : x ∈ Submodule.span ℂ (M.SoLoc B.ψ B.τ₁)) :
    pure f (Function.update φ B.v₁ x) ∈ M.So B.ψ B.τ₁ := by
  have c4 := (h2.and hp.good.std).mono fun _ h => h.1.trans h.2
  have l : ∀ x y (a : ℂ), pure f (Function.update φ B.v₁ (x + a • y)) =
      pure f (Function.update φ B.v₁ x) + a • pure f (Function.update φ B.v₁ y) := (pureAct F _ B.v₁ id f φ h1 c4).2.1
  have z : pure f (Function.update φ B.v₁ 0) = 0 := by
    have := l 0 0 1
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨f, _, upd_mem (S := fun _ => SB _) h1 hx.1, upd_ev h2 _ _,
      by rwa [Function.update_self], rfl⟩
  | zero => rw [z]; exact zero_mem _
  | add x y _ _ hx hy => have := l x y 1; simp only [one_smul] at this; rw [this]; exact add_mem hx hy
  | smul a x _ hx => have := l 0 x a; rw [zero_add, z, zero_add] at this; rw [this]; exact Submodule.smul_mem _ a hx

theorem exists_proj (hp : IsPair B M χX χW om r s r' s') :
    ∃ (π : Module.End ℂ ((Fin n × Fin d → Fv F B.v₁) → ℂ)) (O : Module.End ℂ (Fn F n d)),
      (∀ x, π x ∈ Submodule.span ℂ (M.SoLoc B.ψ B.τ₁)) ∧ (∀ Φ ∈ M.So B.ψ B.τ₁, O Φ = Φ) ∧
      ∀ (f : SInf F _) φ, (∀ᶠ v in cofinite, φ v = M.vac v) → O (pure f φ) = pure f (Function.update φ B.v₁ (π (φ B.v₁))) := by
  obtain ⟨π₀, hπ⟩ := LinearMap.exists_extend (LinearMap.id : Submodule.span ℂ (M.SoLoc B.ψ B.τ₁) →ₗ[ℂ] _)
  obtain ⟨O, hO⟩ := exists_factorOp B.v₁ ((Submodule.span ℂ (M.SoLoc B.ψ B.τ₁)).subtype ∘ₗ π₀)
  have hO' := fun (f : SInf F (Fin n × Fin d)) φ (h : ∀ᶠ v in cofinite, φ v = M.vac v) => hO f φ (Std.congr hp.good.std h)
  refine ⟨_, O, fun x => (π₀ x).2, fun Φ hΦ => ?_, hO'⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, -, h2, h3, rfl⟩ := hx
    have : π₀ (φ B.v₁) = ⟨φ B.v₁, Submodule.subset_span h3⟩ := LinearMap.congr_fun hπ ⟨φ B.v₁, Submodule.subset_span h3⟩
    rw [hO' f φ h2, LinearMap.comp_apply, this]
    exact congrArg (pure f) (Function.update_eq_self ..)
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

theorem pure_inj (hp : IsPair B M χX χW om r s r' s') {f : SInf F (Fin n × Fin d)} (hf : f ≠ 0) (v : Pl F) {x y}
    (h : pure f (Function.update M.vac v x) = pure f (Function.update M.vac v y)) : x = y := by
  have off : ∀ z, ∀ u ∉ ({v} : Finset (Pl F)), Function.update M.vac v z u = M.vac u := fun z u hu =>
    Function.update_of_ne (by simpa using hu) ..
  have e := tens_eq (fun u => (hp.good.vac u).2.1) hp.good.std {v} (ι := Unit) (ι' := Unit) (fun _ => f)
    (fun _ => Function.update M.vac v x) (fun _ => f) (fun _ => Function.update M.vac v y) (fun _ => off x) (fun _ => off y)
    (by simpa using h)
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hf (SchwartzMap.ext hn)
  funext b
  let pt : ∀ u : ({v} : Finset (Pl F)), Fin n × Fin d → Fv F u := fun u => (Finset.mem_singleton.1 u.2).symm ▸ b
  let l₁ : SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ := { toFun := fun g => g a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let l₂ := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ({v} : Finset (Pl F)) ℂ).compLinearMap
    fun u => (LinearMap.proj (pt u) : ((Fin n × Fin d → Fv F u) → ℂ) →ₗ[ℂ] ℂ))
  have e2 := congrArg (fun z => LinearMap.mul' ℂ ℂ (TensorProduct.map l₁ l₂ z)) e
  simp only [Finset.univ_unique, Finset.sum_singleton, TensorProduct.map_tmul, LinearMap.mul'_apply, l₂,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    Finset.prod_singleton, LinearMap.proj_apply] at e2
  have e3 := mul_left_cancel₀ (show l₁ f ≠ 0 from ha) e2
  have dflt : (default : ({v} : Finset (Pl F))) = ⟨v, Finset.mem_singleton_self v⟩ := Subsingleton.elim _ _
  rw [dflt] at e3
  simpa [pt] using e3

end Pair

theorem injPure_of (hO : ArchOp) (hLie : ArchLie) (hQ : ArchUniq) (hA : ActsEx) (hW : WeilConv) (hSC : SoCont)
    (hD : KDecay) (hCo : KCoinv) (hK : Kills) (hK0 : PositivityTheory.ThKG.Loc.Kills0) : PositivityTheory.ThKG.Loc.InjPure := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hnz
  have t := hm.triple
  have hp := PositivityTheory.ThKG.pairV t
  have hp' := PositivityTheory.ThKG.pairV' t
  obtain ⟨k1, k2⟩ := hK F E σ B a a' G X om om' R Rf hm
  have sch : ∀ {n d} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W}, M.IsGood B.ψ → ∀ (f : SInf F (Fin n × Fin d)) φ,
      (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ∈ schA F _ := fun hM f φ h1 h2 => by
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hM φ h1 h2
    rw [e]; exact PositivityTheory.ThKG.pureA_mem f hg
  refine ⟨fun f hf φ h1 h2 p0 pφ h0 => ?_, fun f hf φ h1 h2 hq p0 pφ h0 => ?_⟩
  · obtain ⟨Φ, hΦ, hne⟩ := hnz.1
    have hc := cuspidal_class_of_weil_convergence hW hp (PositivityTheory.ThKG.weilCondV t)
    have key := injGen hO hLie hQ hp hc (fun _ => SB _) (fun _ => le_rfl) (sch hp.good) R.p Rf.p k1
      hm.fin.irred hm.real.irred hf h1 h2 p0 pφ h0
    refine hne (I_span hp hc ?_ Φ hΦ).2
    rintro _ ⟨g, hg, ψ, c1, c2, rfl⟩
    exact ⟨sch hp.good g ψ c1 c2, key g hg ψ c1 c2⟩
  obtain ⟨Φ, hΦ, hne⟩ := hnz.2
  have ex := fun v => (hA F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hp' v).1 1 (inj_at _)
  choose op hop hopP using hO F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hp' 1 (inj_at _)
  have irrI : ∀ N : Submodule ℂ R.Pi,
      (∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ f₁ : SInf F _,
        ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p' f ∈ N → R.p' f₁ ∈ N) →
      (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ f₁ : SInf F _,
        Acts (evI F) (om' (1, k)) f f₁ → R.p' f ∈ N → R.p' f₁ ∈ N) → N = ⊥ ∨ N = ⊤ := fun N n1 n2 => by
    have on : ∀ y, ∃ x ∈ G.M'.Pol B.ψ B.emb, R.p' x = y := fun y =>
      (hm.real.quot'.onto ▸ Submodule.mem_top : y ∈ (G.M'.Pol B.ψ B.emb).map R.p')
    refine hm.real.irred N (fun γ hγ x hx x₁ ha hN => ?_) fun k hk x hx x₁ ha hN => ?_
    · obtain ⟨y, hy, e⟩ := on (R.p x)
      obtain ⟨y₁, -, h4, -⟩ := hLie F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hp' 1 inj_line γ hγ (fun t => op _ (hγ.2 _))
        (fun t => hop _ _) y hy
      rw [hm.real.lie γ hγ x hx y hy x₁ y₁ ha h4 e.symm]
      exact n1 γ hγ y hy y₁ h4 (e ▸ hN)
    · obtain ⟨y, hy, e⟩ := on (R.p x)
      rw [hm.real.cpt k hk x hx y hy x₁ _ ha ((hop k hk.1).2 y) e.symm]
      exact n2 k hk y hy _ ((hop k hk.1).2 y) (e ▸ hN)
  have irrF : ∀ S : ∀ v : Pl F, Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ v, S v ≤ SB _) →
      (∀ v y, ∃ x ∈ S v, Rf.p' v x = y) →
      (∀ v, ∀ h ∈ UAt σ G.W (evFin F v), ∀ x ∈ S v, ∀ x₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) x x₁ → x₁ ∈ S v) →
      ∀ v, ∀ N : Submodule ℂ (Rf.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ x ∈ S v, ∀ x₁ ∈ S v,
        Acts (evFin F v) (om' (1, h)) x x₁ → Rf.p' v x ∈ N → Rf.p' v x₁ ∈ N) → N = ⊥ ∨ N = ⊤ := fun S hS on st v N n1 => by
    refine hm.fin.irred v N fun h hh x hx x₁ hx₁ ha hN => ?_
    obtain ⟨y, hy, e⟩ := on v (Rf.p v x)
    obtain ⟨y₁, ⟨h3, h4⟩, -⟩ := ex v h hh y (hS v hy)
    rw [hm.fin.equiv v h hh x hx y (hS v hy) x₁ hx₁ y₁ h3 ha h4 e.symm]
    exact n1 h hh y hy y₁ (st v h hh y hy y₁ h3 h4) h4 (e ▸ hN)
  have onF : ∀ v y, ∃ x ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v x = y := fun v y =>
    (hm.fin.onto' v ▸ Submodule.mem_top : y ∈ (SB _).map (Rf.p' v))
  rcases hq with hq | hq
  · have hc := cuspidal_class_of_weil_convergence hW hp' (Or.inr (by rw [hq]; simp))
    have key := injGen hO hLie hQ hp' hc (fun _ => SB _) (fun _ => le_rfl) (sch hp'.good) R.p' Rf.p'
      (hK0 F E σ B a a' G X om om' R Rf hm hq) (irrF _ (fun _ => le_rfl) onF fun _ _ _ _ _ _ h _ => h) irrI hf h1 h2 p0 pφ h0
    refine hne (I_span hp' hc ?_ Φ hΦ.1).2
    rintro _ ⟨g, hg, ψ, c1, c2, rfl⟩
    exact ⟨sch hp'.good g ψ c1 c2, key g hg ψ c1 c2⟩
  obtain ⟨co1, co2⟩ := hCo F E σ B a a' G X om om' R Rf hm
  obtain ⟨π, O, hπ, hOs, hOp⟩ := exists_proj hp'
  have hc : Cls0 G.M' om' (G.M'.So B.ψ B.τ₁) :=
    ⟨so_leI hp', fun Ψ hΨ => ((hD F E σ B a a' G X om om' t).2 Ψ hΨ).2.1, fun ψ hψ hm' g =>
      continuous_iff_seqContinuous.2 fun u x hu => by
        simpa [Function.comp_def] using hSC F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hp' 1 (fun _ => ψ) (fun _ => x) (fun k _ => u k)
          (fun _ => ⟨hψ, hu⟩) (fun k => by simpa using hm' (u k)) (by simpa using hm' x) g⟩
  let S : ∀ v : Pl F, Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    Function.update (fun _ => SB _) B.v₁ (Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁))
  have S1 : S B.v₁ = Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) := Function.update_self ..
  have S2 : ∀ v, v ≠ B.v₁ → S v = SB _ := fun v h => Function.update_of_ne h ..
  have hS : ∀ v, S v ≤ SB _ := fun v => by
    by_cases e : v = B.v₁
    · subst e; rw [S1]; exact soLoc_leI _
    · rw [S2 v e]
  have mS : ∀ ψ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, ψ v ∈ SB _) →
      ψ B.v₁ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) → ∀ v, ψ v ∈ S v := fun ψ c1 c2 v => by
    by_cases e : v = B.v₁
    · subst e; rwa [S1]
    · rw [S2 v e]; exact c1 v
  have inSo : ∀ (g : SInf F _) ψ, (∀ v, ψ v ∈ S v) → (∀ᶠ v in cofinite, ψ v = G.M'.vac v) → pure g ψ ∈ G.M'.So B.ψ B.τ₁ :=
    fun g ψ c1 c2 => by
      have := pure_so hp' g (fun v => hS v (c1 v)) c2 (S1 ▸ c1 B.v₁)
      rwa [Function.update_eq_self] at this
  have f0 : f ≠ 0 := fun e => p0 (by rw [e, map_zero])
  have vsb : ∀ v, G.M'.vac v ∈ SB _ := fun v => (hp'.good.vac v).1
  have key := injGen hO hLie hQ hp' hc S hS inSo R.p' Rf.p'
    (fun g hg ψ c1 c2 => k2 g hg ψ (fun v => hS v (c1 v)) c2 (S1 ▸ c1 B.v₁))
    (irrF S hS (fun v y => by
      by_cases e : v = B.v₁
      · subst e
        obtain ⟨x, hx, ex⟩ := (co1 _ t.chars.good).2.2.1 B.τ₁ y
        exact ⟨x, S1 ▸ Submodule.subset_span hx, ex⟩
      · rw [S2 v e]; exact onF v y) fun v h hh x hx x₁ hx₁ ha => by
      by_cases e : v = B.v₁
      · subst e
        rw [S1] at hx ⊢
        have ev : ∀ z, ∀ᶠ u in cofinite, Function.update G.M'.vac B.v₁ z u = G.M'.vac u :=
          fun z => upd_ev (Filter.Eventually.of_forall fun _ => rfl) _ z
        have e1 := (pureAct F _ B.v₁ (om' (1, h)) f (Function.update G.M'.vac B.v₁ x)
          (upd_mem (S := fun _ => SB _) vsb (soLoc_leI _ hx)) (upd_ev hp'.good.std _ x)).2.2 x₁ (by rwa [Function.update_self])
        have e2 : om' (1, h) (pure f (Function.update G.M'.vac B.v₁ x)) = pure f (Function.update G.M'.vac B.v₁ x₁) :=
          e1.trans (congrArg (pure f) (Function.update_idem ..))
        have e3 := hOs _ (e2 ▸ co2 (1, h) _ (pure_so hp' f vsb (Filter.Eventually.of_forall fun _ => rfl) hx))
        rw [hOp f _ (ev x₁), Function.update_idem, Function.update_self] at e3
        rw [← pure_inj hp' f0 _ e3]
        exact hπ x₁
      · rwa [S2 v e]) irrI hf (mS φ h1 hq) h2 p0 pφ h0
  have : O Φ ∈ Submodule.span ℂ (O '' {Φ | ∃ f ∈ G.M'.Pol B.ψ B.emb, ∃ φ, (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) ∧ Φ = pure f φ}) := by
    rw [← Submodule.map_span]; exact ⟨Φ, hΦ.1, rfl⟩
  rw [hOs Φ hΦ.2] at this
  refine hne (I_span hp' hc ?_ Φ this).2
  rintro _ ⟨_, ⟨g, hg, ψ, c1, c2, rfl⟩, rfl⟩
  rw [hOp g ψ c2]
  have c3 := mS _ (upd_mem (S := fun _ => SB _) c1 (soLoc_leI _ (hπ (ψ B.v₁)))) (by rw [Function.update_self]; exact hπ _)
  exact ⟨inSo g _ c3 (upd_ev c2 _ _), key g hg _ c3 (upd_ev c2 _ _)⟩

end PositivityTheory.ThKF

end
