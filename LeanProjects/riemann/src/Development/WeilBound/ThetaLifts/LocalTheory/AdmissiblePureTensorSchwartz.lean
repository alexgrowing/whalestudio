import Development.WeilBound.ThetaLifts.LocalTheory.Cross
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedMultiplicityOneProportional
import Development.WeilBound.ThetaLifts.LocalTheory.SplitInv2

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF
open scoped Classical

section Gen

variable {κ : Type} [Fintype κ]

theorem pure_ne {f : SInf F κ} (hf : f ≠ 0) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (h0 : ∀ v, φ v ≠ 0) (hs : Std φ) : pure f φ ≠ 0 := by
  intro h
  have := tensInj F κ φ h0 hs ∅ 1 (fun _ => 1) (fun _ => f) (fun _ => φ) (fun _ _ _ => rfl) (by simpa using h)
  have := congrArg ((TensorProduct.rid ℂ (SInf F κ)).toLinearMap ∘ₗ (PiTensorProduct.isEmptyEquiv (R := ℂ) ((∅ : Finset (Pl F)))
    (s := fun v => (κ → Fv F v) → ℂ)).toLinearMap.lTensor (SInf F κ)) this
  simp at this
  exact hf this

theorem pure_upd_zero (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hs : Std φ) (v : Pl F) :
    pure f (Function.update φ v 0) = 0 := by
  obtain ⟨r, -, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hs
  rw [← hr']; funext x; simp [tens]

theorem arch_slice {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (h0 : ∀ v, φ v ≠ 0) (hs : Std φ) (N : Submodule ℂ (SInf F κ)) {g : SInf F κ}
    (h : pure g φ ∈ Submodule.span ℂ {Φ | ∃ f ∈ N, ∃ ψ, Φ = pure f ψ}) : g ∈ N := by
  by_cases hg : g = 0
  · exact hg ▸ zero_mem _
  obtain ⟨x₀, hx⟩ := Function.ne_iff.1 (pure_ne hg h0 hs)
  let pt : (κ → mixedEmbedding.mixedSpace F) → κ → AF F := fun z k =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z k), (x₀ k).2)
  have e : ∀ (f : SInf F κ) ψ z, pure f ψ (pt z) = f z * ∏ᶠ v, ψ v fun i => evFin F v (x₀ i) := fun f ψ z => by
    have : (fun k => evI F (pt z k)) = z := funext fun k => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    rw [this]; rfl
  have key : ∀ Φ ∈ Submodule.span ℂ {Φ | ∃ f ∈ N, ∃ ψ, Φ = pure f ψ}, ∃ f ∈ N, ∀ z, Φ (pt z) = f z := fun Φ hΦ => by
    induction hΦ using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨f, hf, ψ, rfl⟩ := h
      exact ⟨(∏ᶠ v, ψ v fun i => evFin F v (x₀ i)) • f, N.smul_mem _ hf, fun z => by rw [e, mul_comm]; rfl⟩
    | zero => exact ⟨0, zero_mem _, fun _ => rfl⟩
    | add _ _ _ _ a b =>
      obtain ⟨f, hf, a⟩ := a; obtain ⟨f', hf', b⟩ := b
      exact ⟨f + f', add_mem hf hf', fun z => by rw [Pi.add_apply, a, b]; rfl⟩
    | smul c _ _ a =>
      obtain ⟨f, hf, a⟩ := a
      exact ⟨c • f, N.smul_mem _ hf, fun z => by rw [Pi.smul_apply, a]; rfl⟩
  obtain ⟨f, hf, a⟩ := key _ h
  have hc : (∏ᶠ v, φ v fun i => evFin F v (x₀ i)) ≠ 0 := right_ne_zero_of_mul hx
  have : g = (∏ᶠ v, φ v fun i => evFin F v (x₀ i))⁻¹ • f := by
    ext z
    rw [SchwartzMap.smul_apply, ← a, e, smul_eq_mul]; field_simp
  exact this ▸ N.smul_mem _ hf

end Gen

variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ Y W}

theorem vac_ne (h : M.IsGood B.ψ) (v) : M.vac v ≠ 0 := (h.vac v).2.1

theorem vac_sb (h : M.IsGood B.ψ) (v) : M.vac v ∈ SB _ := (h.vac v).1

variable (B M) in

def SS : ∀ v : Pl F, Submodule ℂ (Fl F v n d) := Function.update (fun _ => SB _) B.v₁ (Submodule.span ℂ (M.SoLoc B.ψ B.τ₁))

theorem SS_self : SS B M B.v₁ = Submodule.span ℂ (M.SoLoc B.ψ B.τ₁) := Function.update_self ..

theorem SS_ne {v} (h : v ≠ B.v₁) : SS B M v = SB _ := Function.update_of_ne h ..

theorem SS_le (v) : SS B M v ≤ SB _ := by
  by_cases h : v = B.v₁
  · subst h; rw [SS_self]; exact Submodule.span_le.2 fun x hx => hx.1
  · rw [SS_ne h]

theorem pure_mem_so (h : M.IsGood B.ψ) (f : SInf F _) {φ} (a : admitted M (SS B M) φ) : pure f φ ∈ M.So B.ψ B.τ₁ := by
  have sb := fun v => SS_le v (a.1 v)
  have st : Std φ := (a.2.and h.std).mono fun _ h => h.1.trans h.2
  have k : ∀ x ∈ Submodule.span ℂ (M.SoLoc B.ψ B.τ₁), pure f (Function.update φ B.v₁ x) ∈ M.So B.ψ B.τ₁ := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have b : admitted M (fun _ => SB _) (Function.update φ B.v₁ x) := admitted.upd ⟨sb, a.2⟩ hx.1
      exact Submodule.subset_span ⟨f, _, b.1, b.2, by rwa [Function.update_self], rfl⟩
    | zero => rw [pure_upd_zero f st]; exact zero_mem _
    | add x y _ _ hx hy =>
      have := (pureAct F _ B.v₁ id f φ sb st).2.1 x y 1
      rw [one_smul, one_smul] at this
      rw [this]; exact add_mem hx hy
    | smul c x _ hx =>
      have := (pureAct F _ B.v₁ id f φ sb st).2.1 0 x c
      rw [zero_add, pure_upd_zero f st, zero_add] at this
      rw [this]; exact Submodule.smul_mem _ _ hx
  have := k _ (SS_self (B := B) (M := M) ▸ a.1 B.v₁)
  rwa [Function.update_eq_self] at this

theorem so_le (h : M.IsGood B.ψ) : M.So B.ψ B.τ₁ ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  obtain ⟨g, hg, e⟩ := pure_eq_pureA h φ h1 h2
  rw [e]; exact pureA_mem f hg

theorem so_slice (h : M.IsGood B.ψ) {f : SInf F _} (hf : f ≠ 0) {x} (hx : pure f (Function.update M.vac B.v₁ x) ∈ M.So B.ψ B.τ₁) :
    x ∈ Submodule.span ℂ (M.SoLoc B.ψ B.τ₁) := by
  obtain ⟨N, hN⟩ := (Submodule.span ℂ (M.SoLoc B.ψ B.τ₁)).exists_isCompl
  let π : Module.End ℂ (Fl F B.v₁ n d) := N.subtype ∘ₗ N.linearProjOfIsCompl _ hN.symm
  obtain ⟨O, hO⟩ := exists_factorOp B.v₁ π
  have k : M.So B.ψ B.τ₁ ≤ LinearMap.ker O := Submodule.span_le.2 (by
    rintro _ ⟨g, φ, -, h2, h3, rfl⟩
    have st : Std φ := (h2.and h.std).mono fun _ h => h.1.trans h.2
    have : π (φ B.v₁) = 0 := by
      exact congrArg N.subtype ((Submodule.linearProjOfIsCompl_apply_eq_zero_iff hN.symm).2 (Submodule.subset_span h3))
    show O _ = 0
    rw [hO g φ st, this, pure_upd_zero g st])
  have st : ∀ y, Std (Function.update M.vac B.v₁ y) := fun y =>
    (h.std.and (Filter.eventually_cofinite_ne B.v₁)).mono fun u hu => (Function.update_of_ne hu.2 ..).trans hu.1
  have z : O _ = 0 := k hx
  rw [hO f _ (st x), Function.update_self, Function.update_idem] at z
  have p0 : π x = 0 := by
    by_contra hn
    refine pure_ne hf (fun u => ?_) (st _) z
    by_cases e : u = B.v₁
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact vac_ne h u
  have : N.linearProjOfIsCompl _ hN.symm x = 0 := Subtype.ext p0
  exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hN.symm).1 this

theorem I_add₂ {o : Rep σ Y W} {χ χ' : Chr F E} (hw : M.IsWeil B.ψ χ χ' o) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _)
    (c : M.Conv o Φ) (c' : M.Conv o Ψ) (h : UA σ W.J) : M.I o (Φ + Ψ) h = M.I o Φ h + M.I o Ψ h := by
  have e : ∀ g, theta o (Φ + Ψ) g h = theta o Φ g h + theta o Ψ g h := fun g => by
    simp only [theta, map_add]
    exact thetaSum_add F (hw.isUSplitting.pres _ _ hΦ) (hw.isUSplitting.pres _ _ hΨ)
  simp only [Model.I, e]
  exact integral_add (c h) (c' h)

structure Hyp : Prop where
  acts : ActsEx
  weil : WeilConv
  soc : SoCont
  dec : KDecay
  coinv : KCoinv
  kills : Kills
  kills0 : Kills0
  op : ArchOp
  lie : ArchLie
  uniq : ArchUniq
  inj : InjPure
  split : SplitEx
  sinv : SplitInv2
  levi : LeviEx
  ev0 : EvZero
  dense : PolDense
  fac : FacNe
  unim : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F _, ∀ g, M.I om (om (g, 1) Φ) = M.I om Φ

theorem one_line : (1 : Multiplicative ℝ →* UA σ Y.J) ∈ Lines σ Y := ⟨continuous_const, fun _ => uat_one⟩

theorem one_kinf (τ) : (1 : UA σ Y.J) ∈ KInf σ Y τ := ⟨uat_one, fun w => by
  rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩

section Mk

variable {om : Rep σ Y W} {χX χW : Chr F E} {r s r' s' : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P] {Q : Pl F → Type}
  [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] {pi : SInf F (Fin n × Fin d) →ₗ[ℂ] P} {p : ∀ v, Fl F v n d →ₗ[ℂ] Q v}
  {n₂ : ℕ} {Y₂ : Spc F E n₂} {M₂ : Model σ Y₂ W} {om₂ : Rep σ Y₂ W} {χX₂ χW₂ : Chr F E} {r₂ s₂ r₂' s₂' : ℕ}
  {pi₂ : SInf F (Fin n₂ × Fin d) →ₗ[ℂ] P} {p₂ : ∀ v, Fl F v n₂ d →ₗ[ℂ] Q v}

theorem Cross.symm (c : Cross B M om M₂ om₂ pi p pi₂ p₂) : Cross B M₂ om₂ M om pi₂ p₂ pi p :=
  ⟨fun v h hh a ha b hb a' ha' b' hb' x y e => (c.fin v h hh b hb a ha b' hb' a' ha' y x e.symm).symm,
    fun γ hγ a ha b hb a' b' x y e => (c.lie γ hγ b hb a ha b' a' y x e.symm).symm,
    fun γ hγ a ha b hb a' b' x y e => (c.cpt γ hγ b hb a ha b' a' y x e.symm).symm⟩

theorem side_of (H : Hyp) (hp : IsPair B M χX χW om r s r' s') (hp₂ : IsPair B M₂ χX₂ χW₂ om₂ r₂ s₂ r₂' s₂')
    (c : Cross B M om M₂ om₂ pi p pi₂ p₂) (o₂ : ∀ v, (SB _).map (p₂ v) = ⊤) (oi₂ : (M₂.Pol B.ψ B.emb).map pi₂ = ⊤)
    (oi : (M.Pol B.ψ B.emb).map pi = ⊤) {S : ∀ v : Pl F, Submodule ℂ (Fl F v n d)} (le : ∀ v, S v ≤ SB _)
    (onto : ∀ v ξ, ∃ x ∈ S v, p v x = ξ)
    (stab : ∀ v, ∀ h ∈ UAt σ W (evFin F v), ∀ x ∈ S v, ∀ x' ∈ SB _, Acts (evFin F v) (om (1, h)) x x' → x' ∈ S v)
    (𝓒 : Submodule ℂ (Fn F n d)) (h1 : ∀ (f : SInf F _) φ, admitted M S φ → pure f φ ∈ 𝓒) (h2 : ∀ Φ ∈ 𝓒, Φ ∈ schA F _ ∧ M.Conv om Φ)
    (cont : ∀ φ, admitted M S φ → ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pure f φ) h)
    (kill : ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ, admitted M S φ → (pi f = 0 ∨ ∃ v, p v (φ v) = 0) → M.I om (pure f φ) = 0) :
    Side B M om pi p S := by
  have A := fun v => (H.acts F E σ B _ _ _ _ M _ _ om _ _ _ _ hp v).1 1 uat_one
  have A₂ := fun v => (H.acts F E σ B _ _ _ _ M₂ _ _ om₂ _ _ _ _ hp₂ v).1 1 uat_one
  have O₂ := H.op F E σ B _ _ _ _ M₂ _ _ om₂ _ _ _ _ hp₂ 1 uat_one
  refine ⟨hp.good, le, onto, fun ξ => Submodule.mem_map.1 (oi ▸ Submodule.mem_top), fun v h hh x hx => ?_,
    ⟨𝓒, h1, fun Φ a Ψ b => I_add₂ hp.weil (h2 Φ a).1 (h2 Ψ b).1 (h2 Φ a).2 (h2 Ψ b).2⟩, cont, kill,
    fun v h hh a ha b hb a' ha' b' hb' x y e => ?_, fun γ hγ a ha b hb a' b' x y e => ?_, fun k hk a ha b hb a' b' x y e => ?_,
    fun h hh => ?_, fun δ hδ T hT => H.lie F E σ B _ _ _ _ M _ _ om _ _ _ _ hp 1 one_line δ hδ T hT, H.uniq F _⟩
  · obtain ⟨x', ⟨h3, h4⟩, -⟩ := A v h hh x (le v hx)
    exact ⟨x', stab v h hh x hx x' h3 h4, h4⟩
  · obtain ⟨z, hz, ez⟩ := Submodule.mem_map.1 (o₂ v ▸ Submodule.mem_top : p v a ∈ (SB _).map (p₂ v))
    obtain ⟨z', ⟨h3, h4⟩, -⟩ := A₂ v h hh z hz
    rw [c.fin v h hh a ha z hz a' ha' z' h3 x h4 ez.symm, c.fin v h hh b hb z hz b' hb' z' h3 y h4 (e ▸ ez.symm)]
  · obtain ⟨z, hz, ez⟩ := Submodule.mem_map.1 (oi₂ ▸ Submodule.mem_top : pi a ∈ (M₂.Pol B.ψ B.emb).map pi₂)
    choose T hT _ using fun t : ℝ => O₂ _ (hγ.2 (Multiplicative.ofAdd t))
    obtain ⟨z', -, h4, -⟩ := H.lie F E σ B _ _ _ _ M₂ _ _ om₂ _ _ _ _ hp₂ 1 one_line γ hγ T hT z hz
    rw [c.lie γ hγ a ha z hz a' z' x h4 ez.symm, c.lie γ hγ b hb z hz b' z' y h4 (e ▸ ez.symm)]
  · obtain ⟨z, hz, ez⟩ := Submodule.mem_map.1 (oi₂ ▸ Submodule.mem_top : pi a ∈ (M₂.Pol B.ψ B.emb).map pi₂)
    obtain ⟨T, hT, -⟩ := O₂ k hk.1
    rw [c.cpt k hk a ha z hz a' _ x (hT.2 z) ez.symm, c.cpt k hk b hb z hz b' _ y (hT.2 z) (e ▸ ez.symm)]
  · obtain ⟨T, hT, hT'⟩ := H.op F E σ B _ _ _ _ M _ _ om _ _ _ _ hp 1 uat_one h hh
    exact ⟨T, hT, hT' (one_kinf _)⟩

theorem cont_weil (H : Hyp) (hp : IsPair B M χX χW om r s r' s') (hw : d + 2 * min r s < 2 * n ∨ min r s = 0) {φ}
    (a : admitted M (fun _ => SB _) φ) (h) : Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pure f φ) h := by
  obtain ⟨g, hg, e⟩ := pure_eq_pureA hp.good φ a.1 a.2
  simp only [e]
  exact (H.weil F E σ B _ _ _ _ M _ _ om _ _ _ _ hp hw).2 g hg h

end Mk

variable {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'}
  {Rf : FinMaps F a a'}

theorem crossM (m : IsMatched B G X om om' R Rf) : Cross B G.M om G.M' om' R.p Rf.p R.p' Rf.p' :=
  ⟨m.fin.equiv, m.real.lie, m.real.cpt⟩

theorem admissible_pure_tensor_schwartz (h : M.IsGood B.ψ) (f : SInf F _) {φ} (a : admitted M (fun _ => SB _) φ) : pure f φ ∈ schA F (Fin n × Fin d) := by
  obtain ⟨g, hg, e⟩ := pure_eq_pureA h φ a.1 a.2
  rw [e]; exact pureA_mem f hg

theorem sideV (H : Hyp) (m : IsMatched B G X om om' R Rf) : Side B G.M om R.p Rf.p fun _ => SB _ :=
  side_of H (pairV m.triple) (pairV' m.triple) (crossM m) m.fin.onto' m.real.quot'.onto m.real.quot.onto (fun _ => le_rfl)
    (fun v _ => Submodule.mem_map.1 (m.fin.onto v ▸ Submodule.mem_top)) (fun _ _ _ _ _ _ h _ => h) (schA F _)
    (fun f _ a => admissible_pure_tensor_schwartz m.triple.geo.hM f a)
    (fun Φ hΦ => ⟨hΦ, ((H.weil F E σ B _ _ _ _ _ _ _ om _ _ _ _ (pairV m.triple) (weilCondV m.triple)).1 Φ hΦ).1⟩)
    (fun _ a => cont_weil H (pairV m.triple) (weilCondV m.triple) a)
    fun f hf φ a => (H.kills F E σ B _ _ G X om om' R Rf m).1 f hf φ a.1 a.2

theorem side_condition_vanishing (H : Hyp) (m : IsMatched B G X om om' R Rf) (q : G.q = 0) : Side B G.M' om' R.p' Rf.p' fun _ => SB _ :=
  have w : a + a' + 2 * min G.q (a' - G.q) < 2 * a' ∨ min G.q (a' - G.q) = 0 := Or.inr (by rw [q]; simp)
  side_of H (pairV' m.triple) (pairV m.triple) (crossM m).symm m.fin.onto m.real.quot.onto m.real.quot'.onto (fun _ => le_rfl)
    (fun v _ => Submodule.mem_map.1 (m.fin.onto' v ▸ Submodule.mem_top)) (fun _ _ _ _ _ _ h _ => h) (schA F _)
    (fun f _ a => admissible_pure_tensor_schwartz m.triple.geo.hM' f a)
    (fun Φ hΦ => ⟨hΦ, ((H.weil F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (pairV' m.triple) w).1 Φ hΦ).1⟩)
    (fun _ a => cont_weil H (pairV' m.triple) w a)
    fun f hf φ a => H.kills0 F E σ B _ _ G X om om' R Rf m q f hf φ a.1 a.2

theorem ex_ne (m : IsMatched B G X om om' R Rf) : ∃ f : SInf F (Fin a' × Fin (a + a')), f ≠ 0 := by
  haveI := m.real.nontriv
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : R.Pi)
  obtain ⟨f, -, e⟩ := Submodule.mem_map.1 (m.real.quot'.onto ▸ Submodule.mem_top : ξ ∈ (G.M'.Pol B.ψ B.emb).map R.p')
  exact ⟨f, fun h => hξ (by rw [← e, h, map_zero])⟩

theorem sideSo (H : Hyp) (m : IsMatched B G X om om' R Rf) : Side B G.M' om' R.p' Rf.p' (SS B G.M') := by
  have hM := m.triple.geo.hM'
  have co := H.coinv F E σ B _ _ G X om om' R Rf m
  refine side_of H (pairV' m.triple) (pairV m.triple) (crossM m).symm m.fin.onto m.real.quot.onto m.real.quot'.onto SS_le
    (fun v ξ => ?_) (fun v h hh x hx x' hx' ac => ?_) (G.M'.So B.ψ B.τ₁) (fun f _ a => pure_mem_so hM f a)
    (fun Φ hΦ => ⟨so_le hM hΦ, ((H.dec F E σ B _ _ G X om om' m.triple).2 Φ hΦ).2.1⟩) (fun φ ad h => ?_)
    fun f hf φ ad => (H.kills F E σ B _ _ G X om om' R Rf m).2 f hf φ (fun v => SS_le v (ad.1 v)) ad.2
      (SS_self (B := B) (M := G.M') ▸ ad.1 B.v₁)
  · by_cases e : v = B.v₁
    · subst e
      obtain ⟨x, hx, ex⟩ := (co.1 _ m.triple.chars.good).2.2.1 B.τ₁ ξ
      exact ⟨x, by rw [SS_self]; exact Submodule.subset_span hx, ex⟩
    · rw [SS_ne e]; exact Submodule.mem_map.1 (m.fin.onto' v ▸ Submodule.mem_top)
  · by_cases e : v = B.v₁
    · subst e
      obtain ⟨f, hf⟩ := ex_ne m
      have ad : admitted G.M' (SS B G.M') (Function.update G.M'.vac B.v₁ x) := by
        refine ⟨fun u => ?_, (Filter.eventually_cofinite_ne B.v₁).mono fun u hu => Function.update_of_ne hu ..⟩
        by_cases e : u = B.v₁
        · subst e; rwa [Function.update_self]
        · rw [Function.update_of_ne e, SS_ne e]; exact vac_sb hM u
      have := co.2 (1, h) _ (pure_mem_so hM f ad)
      rw [(pureAct F _ B.v₁ (om' (1, h)) f _ (fun u => SS_le u (ad.1 u))
        ((ad.2.and hM.std).mono fun _ h => h.1.trans h.2)).2.2 x' (by rwa [Function.update_self]), Function.update_idem] at this
      rw [SS_self]; exact so_slice hM hf this
    · rwa [SS_ne e]
  · obtain ⟨g, hg, e⟩ := pure_eq_pureA hM φ (fun v => SS_le v (ad.1 v)) ad.2
    refine continuous_iff_seqContinuous.2 fun u f hu => ?_
    have := H.soc F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (pairV' m.triple) 1 (fun _ => g) (fun _ => f) (fun k _ => u k)
      (fun _ => ⟨hg, hu⟩) (fun k => by simpa [← e] using pure_mem_so hM (u k) ad) (by simpa [← e] using pure_mem_so hM f ad) h
    simpa [← e, Function.comp_def] using this

end PositivityTheory.ThKG.Loc

end
