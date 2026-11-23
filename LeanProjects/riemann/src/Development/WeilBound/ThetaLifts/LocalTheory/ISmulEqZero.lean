import Development.WeilBound.ThetaLifts.LocalTheory.UatClosure

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF
open scoped Classical

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

def admitted (M : Model σ X W) (S : ∀ v : Pl F, Submodule ℂ (Fl F v n d)) (φ : ∀ v : Pl F, Fl F v n d) : Prop :=
  (∀ v, φ v ∈ S v) ∧ ∀ᶠ v in cofinite, φ v = M.vac v

theorem admitted.upd {M : Model σ X W} {S φ} (h : admitted M S φ) {v x} (hx : x ∈ S v) : admitted M S (Function.update φ v x) := by
  refine ⟨fun u => ?_, (h.2.and (Filter.eventually_cofinite_ne v)).mono fun u hu => (Function.update_of_ne hu.2 ..).trans hu.1⟩
  by_cases e : u = v
  · subst e; rwa [Function.update_self]
  · rw [Function.update_of_ne e]; exact h.1 u

structure Side (B : Base F E) (M : Model σ X W) (om : Rep σ X W) {P : Type} [AddCommGroup P] [Module ℂ P] {Q : Pl F → Type}
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (pi : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p : ∀ v, Fl F v n d →ₗ[ℂ] Q v)
    (S : ∀ v : Pl F, Submodule ℂ (Fl F v n d)) : Prop where
  good : M.IsGood B.ψ
  le : ∀ v, S v ≤ SB _
  onto : ∀ v ξ, ∃ x ∈ S v, p v x = ξ
  ontoI : ∀ ξ, ∃ f ∈ M.Pol B.ψ B.emb, pi f = ξ
  stab : ∀ v, ∀ h ∈ UAt σ W (evFin F v), ∀ x ∈ S v, ∃ x' ∈ S v, Acts (evFin F v) (om (1, h)) x x'
  cls : ∃ 𝓒 : Submodule ℂ (Fn F n d), (∀ (f : SInf F _) φ, admitted M S φ → pure f φ ∈ 𝓒) ∧
    ∀ Φ ∈ 𝓒, ∀ Ψ ∈ 𝓒, ∀ h, M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h
  cont : ∀ φ, admitted M S φ → ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pure f φ) h
  kill : ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ, admitted M S φ → (pi f = 0 ∨ ∃ v, p v (φ v) = 0) → M.I om (pure f φ) = 0
  wdF : ∀ v, ∀ h ∈ UAt σ W (evFin F v), ∀ a ∈ SB _, ∀ b ∈ SB _, ∀ a' ∈ SB _, ∀ b' ∈ SB _, Acts (evFin F v) (om (1, h)) a a' →
    Acts (evFin F v) (om (1, h)) b b' → p v a = p v b → p v a' = p v b'
  wdL : ∀ γ ∈ Lines σ W, ∀ a ∈ M.Pol B.ψ B.emb, ∀ b ∈ M.Pol B.ψ B.emb, ∀ a' b' : SInf F _,
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) a a' →
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) b b' → pi a = pi b → pi a' = pi b'
  wdK : ∀ k ∈ KInf σ W B.emb, ∀ a ∈ M.Pol B.ψ B.emb, ∀ b ∈ M.Pol B.ψ B.emb, ∀ a' b' : SInf F _,
    Acts (evI F) (om (1, k)) a a' → Acts (evI F) (om (1, k)) b b' → pi a = pi b → pi a' = pi b'
  op : ∀ h ∈ UAt σ W (evI F), ∃ T, IsArchOp om (1, h) T ∧ (h ∈ KInf σ W B.emb → ∀ f ∈ M.Pol B.ψ B.emb, T f ∈ M.Pol B.ψ B.emb)
  lie : ∀ δ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d),
    (∀ t, IsArchOp om (1, δ (Multiplicative.ofAdd t)) (T t)) → ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) f f₁ ∧
      ∀ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, HasDerivAt (fun t => L (T t f)) (L f₁) 0
  uniq : ∀ f f₁ f₂ : SInf F (Fin n × Fin d), (∀ S, Acts (evI F) S f f₁ → Acts (evI F) S f f₂ → f₁ = f₂) ∧
    ∀ S, ActsD (evI F) S f f₁ → ActsD (evI F) S f f₂ → f₁ = f₂

abbrev sc (χ : Chr F E) (r : ℝ) (t : (AE F E)ˣ) : ℂ := (χ t : ℂ) * (((absE F E t : ℝ) ^ r : ℝ) : ℂ)

structure Br (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (M₁ : Model σ X₁ W₁) (om₁ : Rep σ X₁ W₁) (H' : Plane E d d₁)
    (χ : Chr F E) (r : ℝ) (S : ∀ v : Pl F, Submodule ℂ (Fl F v n d)) (S₁ : ∀ v : Pl F, Submodule ℂ (Fl F v n₁ d₁))
    (Ev : Fn F n d → Fn F n₁ d₁) (L : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (Λ : ∀ v : Pl F, Fl F v n d →ₗ[ℂ] Fl F v n₁ d₁) : Prop where
  pol : ∀ f ∈ M.Pol B.ψ B.emb, L f ∈ M₁.Pol B.ψ B.emb
  mapS : ∀ v, ∀ x ∈ S v, Λ v x ∈ S₁ v
  fac : ∀ φ, admitted M S φ → ∀ v₀, ∃ (c : ℂ) (ψ : ∀ v, Fl F v n₁ d₁), c ≠ 0 ∧ admitted M₁ S₁ ψ ∧ (∀ v, ∃ a : ℂ, Λ v (φ v) = a • ψ v) ∧
    ∀ (f : SInf F _), ∀ x ∈ S v₀, Ev (pure f (Function.update φ v₀ x)) = c • pure (L f) (Function.update ψ v₀ (Λ v₀ x))
  kil : ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ, admitted M S φ → M.I om (pure f φ) = 0 → M₁.I om₁ (Ev (pure f φ)) = 0
  rule : ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ, admitted M S φ → ∀ t h₁ m, IsLevi H' t h₁ m → ∀ u ∈ unip σ W H', ∀ h',
    M₁.I om₁ (Ev (om (1, u * m) (pure f φ))) h' = sc χ r t * M₁.I om₁ (Ev (pure f φ)) (h' * h₁)

theorem I_right' (M : Model σ X W) (om : Rep σ X W) (Φ : Fn F n d) (h₀ h : UA σ W.J) :
    M.I om (om (1, h₀) Φ) h = M.I om Φ (h * h₀) := by
  simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem pure_add_smul {κ : Type} [Fintype κ] (f g : SInf F κ) (a : ℂ) (φ) : pure (f + a • g) φ = pure f φ + a • pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul, mul_assoc]

section

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {P : Type} [AddCommGroup P] [Module ℂ P] {Q : Pl F → Type}
  [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] {pi : SInf F (Fin n × Fin d) →ₗ[ℂ] P} {p : ∀ v, Fl F v n d →ₗ[ℂ] Q v}
  {S : ∀ v : Pl F, Submodule ℂ (Fl F v n d)}

theorem Side.std (s : Side B M om pi p S) {φ} (h : admitted M S φ) :
    ∀ᶠ u in cofinite, φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1 :=
  (h.2.and s.good.std).mono fun _ h => h.1.trans h.2

theorem Side.act (s : Side B M om pi p S) {φ} (h : admitted M S φ) (f : SInf F _) {v x y} (hx : x ∈ S v) {T}
    (a : Acts (evFin F v) T x y) : T (pure f (Function.update φ v x)) = pure f (Function.update φ v y) := by
  have h' := h.upd hx
  have := (pureAct F _ v T f _ (fun u => s.le u (h'.1 u)) (s.std h')).2.2 y (by rwa [Function.update_self])
  rwa [Function.update_idem] at this

theorem Side.linF (s : Side B M om pi p S) {φ} (h : admitted M S φ) (f : SInf F _) {v x y} (hx : x ∈ S v) (hy : y ∈ S v) (a : ℂ) (g) :
    M.I om (pure f (Function.update φ v (x + a • y))) g =
      M.I om (pure f (Function.update φ v x)) g + a * M.I om (pure f (Function.update φ v y)) g := by
  obtain ⟨𝓒, h1, h2⟩ := s.cls
  rw [(pureAct F _ v id f φ (fun u => s.le u (h.1 u)) (s.std h)).2.1 x y a,
    h2 _ (h1 _ _ (h.upd hx)) _ (𝓒.smul_mem _ (h1 _ _ (h.upd hy))), I_smul]

theorem Side.clm (s : Side B M om pi p S) {φ} (h : admitted M S φ) (g) :
    ∃ l : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f, l f = M.I om (pure f φ) g := by
  obtain ⟨𝓒, h1, h2⟩ := s.cls
  refine ⟨⟨⟨⟨fun f => M.I om (pure f φ) g, fun a b => ?_⟩, fun c a => ?_⟩, s.cont φ h g⟩, fun _ => rfl⟩
  · have := pure_add_smul a b 1 φ
    rw [one_smul, one_smul] at this
    rw [this, h2 _ (h1 _ _ h) _ (h1 _ _ h)]
  · have : pure (c • a) φ = c • pure a φ := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    simp only [this, I_smul, RingHom.id_apply, smul_eq_mul]

theorem Side.arch (s : Side B M om pi p S) {φ} (h : admitted M S φ) {x T} (a : IsArchOp om x T) (f : SInf F _) :
    om x (pure f φ) = pure (T f) φ := by
  obtain ⟨g, hg, e⟩ := pure_eq_pureA s.good φ (fun u => s.le u (h.1 u)) h.2
  rw [e, e, a.1 f g hg]

variable {M₁ : Model σ X₁ W₁} {om₁ : Rep σ X₁ W₁} {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁] {Q₁ : Pl F → Type}
  [∀ v, AddCommGroup (Q₁ v)] [∀ v, Module ℂ (Q₁ v)] {pi₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁} {p₁ : ∀ v, Fl F v n₁ d₁ →ₗ[ℂ] Q₁ v}
  {S₁ : ∀ v : Pl F, Submodule ℂ (Fl F v n₁ d₁)} {H' : Plane E d d₁} {χ : Chr F E} {r : ℝ} {Ev : Fn F n d → Fn F n₁ d₁}
  {L : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)} {Λ : ∀ v : Pl F, Fl F v n d →ₗ[ℂ] Fl F v n₁ d₁}

variable (B M₁ om₁ pi₁ p₁ S₁) in

def Inj : Prop := ∀ f ∈ M₁.Pol B.ψ B.emb, ∀ φ, admitted M₁ S₁ φ → pi₁ f ≠ 0 → (∀ v, p₁ v (φ v) ≠ 0) → M₁.I om₁ (pure f φ) ≠ 0

variable (B M S L Λ pi₁ p₁) in

def Pt : Prop := ∃ f ∈ M.Pol B.ψ B.emb, ∃ φ, admitted M S φ ∧ pi₁ (L f) ≠ 0 ∧ ∀ v, p₁ v (Λ v (φ v)) ≠ 0

theorem exists_test_vectors_at_place (b : Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ) (j : Inj B M₁ om₁ pi₁ p₁ S₁) (pt : Pt B M S pi₁ p₁ L Λ) (v : Pl F) :
    ∃ f ∈ M.Pol B.ψ B.emb, ∃ φ ψ, ∃ c : ℂ, c ≠ 0 ∧ admitted M S φ ∧ admitted M₁ S₁ ψ ∧
      (∀ x ∈ S v, Ev (pure f (Function.update φ v x)) = c • pure (L f) (Function.update ψ v (Λ v x))) ∧
      ∀ y ∈ S₁ v, M₁.I om₁ (pure (L f) (Function.update ψ v y)) = 0 → p₁ v y = 0 := by
  obtain ⟨f, hf, φ, hφ, h1, h2⟩ := pt
  obtain ⟨c, ψ, hc, hψ, h3, h4⟩ := b.fac φ hφ v
  refine ⟨f, hf, φ, ψ, c, hc, hφ, hψ, h4 f, fun y hy h0 => by_contra fun hn => j _ (b.pol f hf) _ (hψ.upd hy) h1 (fun u => ?_) h0⟩
  by_cases e : u = v
  · subst e; rwa [Function.update_self]
  · rw [Function.update_of_ne e]
    obtain ⟨a, ha⟩ := h3 u
    intro z
    exact h2 u (by rw [ha, map_smul, z, smul_zero])

theorem exists_test_vectors (b : Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ) (j : Inj B M₁ om₁ pi₁ p₁ S₁) (pt : Pt B M S pi₁ p₁ L Λ) :
    ∃ φ ψ, ∃ c : ℂ, c ≠ 0 ∧ admitted M S φ ∧ admitted M₁ S₁ ψ ∧ (∀ f : SInf F _, Ev (pure f φ) = c • pure (L f) ψ) ∧
      ∀ g ∈ M₁.Pol B.ψ B.emb, M₁.I om₁ (pure g ψ) = 0 → pi₁ g = 0 := by
  obtain ⟨-, -, φ, hφ, -, h2⟩ := pt
  obtain ⟨c, ψ, hc, hψ, h3, h4⟩ := b.fac φ hφ B.v₁
  have a := hψ.upd (b.mapS _ _ (hφ.1 B.v₁))
  refine ⟨φ, _, c, hc, hφ, a, fun f => ?_, fun g hg h0 => by_contra fun hn => j _ hg _ a hn (fun u => ?_) h0⟩
  · have := h4 f _ (hφ.1 B.v₁)
    rwa [Function.update_eq_self] at this
  by_cases e : u = B.v₁
  · subst e; rw [Function.update_self]; exact h2 _
  · rw [Function.update_of_ne e]
    obtain ⟨a, ha⟩ := h3 u
    intro z
    exact h2 u (by rw [ha, map_smul, z, smul_zero])

theorem I_smul_eq_zero {c : ℂ} (hc : c ≠ 0) {Ψ} (h : M₁.I om₁ (c • Ψ) = 0) : M₁.I om₁ Ψ = 0 := by
  funext g
  have := congrFun h g
  rw [I_smul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

theorem kerF (s : Side B M om pi p S) (b : Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ) (j : Inj B M₁ om₁ pi₁ p₁ S₁)
    (pt : Pt B M S pi₁ p₁ L Λ) (v : Pl F) : ∀ x ∈ S v, p v x = 0 → p₁ v (Λ v x) = 0 := by
  intro x hx h0
  obtain ⟨f, hf, φ, ψ, c, hc, hφ, hψ, h1, h2⟩ := exists_test_vectors_at_place b j pt v
  have := b.kil f hf _ (hφ.upd hx) (s.kill f hf _ (hφ.upd hx) (Or.inr ⟨v, by rwa [Function.update_self]⟩))
  rw [h1 x hx] at this
  exact h2 _ (b.mapS v x hx) (I_smul_eq_zero hc this)

theorem kerI (s : Side B M om pi p S) (b : Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ) (j : Inj B M₁ om₁ pi₁ p₁ S₁)
    (pt : Pt B M S pi₁ p₁ L Λ) : ∀ f ∈ M.Pol B.ψ B.emb, pi f = 0 → pi₁ (L f) = 0 := by
  intro f hf h0
  obtain ⟨φ, ψ, c, hc, hφ, hψ, h1, h2⟩ := exists_test_vectors b j pt
  have := b.kil f hf _ hφ (s.kill f hf _ hφ (Or.inl h0))
  rw [h1] at this
  exact h2 _ (b.pol f hf) (I_smul_eq_zero hc this)

theorem eqF (s : Side B M om pi p S) (s₁ : Side B M₁ om₁ pi₁ p₁ S₁) (b : Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ)
    (j : Inj B M₁ om₁ pi₁ p₁ S₁) (pt : Pt B M S pi₁ p₁ L Λ) (v : Pl F) {t h₁ m u} (hl : IsLevi H' t h₁ m) (hu : u ∈ unip σ W H')
    (h₁v : h₁ ∈ UAt σ W₁ (evFin F v)) {x x' y y'} (hx : x ∈ S v) (hx' : x' ∈ S v) (hy : y ∈ SB _) (hy' : y' ∈ SB _)
    (a : Acts (evFin F v) (om (1, u * m)) x x') (a₁ : Acts (evFin F v) (om₁ (1, h₁)) y y') (e : p₁ v (Λ v x) = p₁ v y) :
    p₁ v (Λ v x') = sc χ r t • p₁ v y' := by
  obtain ⟨f, hf, φ, ψ, c, hc, hφ, hψ, h1, h2⟩ := exists_test_vectors_at_place b j pt v
  obtain ⟨z, hz, az⟩ := s₁.stab v h₁ h₁v _ (b.mapS v x hx)
  have := h2 (Λ v x' + (-sc χ r t) • z) (add_mem (b.mapS v _ hx') (Submodule.smul_mem _ _ hz)) (funext fun g => by
    have k := b.rule f hf _ (hφ.upd hx) t h₁ m hl u hu g
    rw [s.act hφ f hx a, h1 _ hx', h1 _ hx, I_smul, I_smul, ← I_right', s₁.act hψ _ (b.mapS v x hx) az] at k
    rw [s₁.linF hψ _ (b.mapS v _ hx') hz, Pi.zero_apply]
    apply mul_left_cancel₀ hc
    rw [mul_add, k]; ring)
  rw [map_add, map_smul, neg_smul, add_neg_eq_zero] at this
  rw [this, s₁.wdF v h₁ h₁v _ (s₁.le v (b.mapS v x hx)) _ hy _ (s₁.le v hz) _ hy' az a₁ e]

theorem eqK (s : Side B M om pi p S) (s₁ : Side B M₁ om₁ pi₁ p₁ S₁) (b : Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ)
    (j : Inj B M₁ om₁ pi₁ p₁ S₁) (pt : Pt B M S pi₁ p₁ L Λ) {k k₁ t} (hk : k ∈ KInf σ W B.emb) (hk₁ : k₁ ∈ KInf σ W₁ B.emb)
    (hl : IsLevi H' t k₁ k) {f f₁ f' f₁' : SInf F _} (hf : f ∈ M.Pol B.ψ B.emb) (hf₁ : f₁ ∈ M₁.Pol B.ψ B.emb)
    (a : Acts (evI F) (om (1, k)) f f') (a₁ : Acts (evI F) (om₁ (1, k₁)) f₁ f₁') (e : pi₁ (L f) = pi₁ f₁) :
    pi₁ (L f') = sc χ r t • pi₁ f₁' := by
  obtain ⟨φ, ψ, c, hc, hφ, hψ, h1, h2⟩ := exists_test_vectors b j pt
  obtain ⟨T, hT, hT'⟩ := s.op k hk.1
  obtain ⟨T₁, hT₁, hT₁'⟩ := s₁.op k₁ hk₁.1
  obtain rfl := (s.uniq f f' (T f)).1 _ a (hT.2 f)
  have := h2 (L (T f) + (-sc χ r t) • T₁ (L f))
    (add_mem (b.pol _ (hT' hk f hf)) (Submodule.smul_mem _ _ (hT₁' hk₁ _ (b.pol f hf)))) (funext fun g => by
    have k := b.rule f hf _ hφ t k₁ k hl 1 (one_mem _) g
    rw [one_mul, s.arch hφ hT, h1, h1, I_smul, I_smul, ← I_right', s₁.arch hψ hT₁] at k
    obtain ⟨l, hl⟩ := s₁.clm hψ g
    rw [← hl, ← hl] at k
    rw [← hl, map_add, map_smul, Pi.zero_apply, smul_eq_mul]
    apply mul_left_cancel₀ hc
    rw [mul_add, k]; ring)
  rw [map_add, map_smul, neg_smul, add_neg_eq_zero] at this
  rw [this, s₁.wdK k₁ hk₁ _ (b.pol f hf) _ hf₁ _ _ (hT₁.2 _) a₁ e]

theorem eqN (s : Side B M om pi p S) (s₁ : Side B M₁ om₁ pi₁ p₁ S₁) (b : Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ)
    (j : Inj B M₁ om₁ pi₁ p₁ S₁) (pt : Pt B M S pi₁ p₁ L Λ) {γ} (hγ : γ ∈ Lines σ W) (hu : ∀ s, γ s ∈ unip σ W H')
    {f f' : SInf F _} (hf : f ∈ M.Pol B.ψ B.emb) (a : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f') :
    pi₁ (L f') = 0 := by
  obtain ⟨φ, ψ, c, hc, hφ, hψ, h1, h2⟩ := exists_test_vectors b j pt
  choose T hT _ using fun t : ℝ => s.op _ (hγ.2 (Multiplicative.ofAdd t))
  obtain ⟨g, hg, ag, dg⟩ := s.lie γ hγ T hT f hf
  obtain rfl := (s.uniq f f' g).2 _ a ag
  refine h2 _ (b.pol _ hg) (funext fun h => ?_)
  obtain ⟨l, hl⟩ := s₁.clm hψ h
  have k : (fun t => (l.comp L) (T t f)) = fun _ => l (L f) := funext fun t => by
    have k := b.rule f hf _ hφ 1 1 1 (isLevi_one H') _ (hu (Multiplicative.ofAdd t)) h
    rw [mul_one, mul_one, s.arch hφ (hT t), h1, h1, I_smul, I_smul, ← hl, ← hl] at k
    simp only [sc, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at k
    exact mul_left_cancel₀ hc k
  have d := dg (l.comp L)
  rw [k] at d
  rw [← hl]
  exact d.unique (hasDerivAt_const _ _)

theorem eqL (s : Side B M om pi p S) (s₁ : Side B M₁ om₁ pi₁ p₁ S₁) (b : Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ)
    (j : Inj B M₁ om₁ pi₁ p₁ S₁) (pt : Pt B M S pi₁ p₁ L Λ) {γ γ₁} (hγ : γ ∈ Lines σ W) (hγ₁ : γ₁ ∈ Lines σ W₁)
    {τ : ℝ → (AE F E)ˣ} (hl : ∀ s, IsLevi H' (τ s) (γ₁ (Multiplicative.ofAdd s)) (γ (Multiplicative.ofAdd s))) (h0 : τ 0 = 1) {c' : ℂ}
    (hd : HasDerivAt (fun s => sc χ r (τ s)) c' 0) {f f₁ f' f₁' : SInf F _} (hf : f ∈ M.Pol B.ψ B.emb)
    (hf₁ : f₁ ∈ M₁.Pol B.ψ B.emb) (a : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f')
    (a₁ : ActsD (evI F) (fun t => om₁ (1, γ₁ (Multiplicative.ofAdd t))) f₁ f₁') (e : pi₁ (L f) = pi₁ f₁) :
    pi₁ (L f') = c' • pi₁ f₁ + pi₁ f₁' := by
  obtain ⟨φ, ψ, c, hc, hφ, hψ, h1, h2⟩ := exists_test_vectors b j pt
  choose T hT _ using fun t : ℝ => s.op _ (hγ.2 (Multiplicative.ofAdd t))
  choose T₁ hT₁ _ using fun t : ℝ => s₁.op _ (hγ₁.2 (Multiplicative.ofAdd t))
  obtain ⟨g, hg, ag, dg⟩ := s.lie γ hγ T hT f hf
  obtain rfl := (s.uniq f f' g).2 _ a ag
  obtain ⟨g₁, hg₁, ag₁, dg₁⟩ := s₁.lie γ₁ hγ₁ T₁ hT₁ _ (b.pol f hf)
  have := h2 (L f' - (c' • L f + g₁)) (sub_mem (b.pol _ hg) (add_mem (Submodule.smul_mem _ _ (b.pol f hf)) hg₁)) (funext fun h => by
    obtain ⟨l, hl'⟩ := s₁.clm hψ h
    have k : (fun t => (l.comp L) (T t f)) = fun t => sc χ r (τ t) * l (T₁ t (L f)) := funext fun t => by
      have k := b.rule f hf _ hφ _ _ _ (hl t) 1 (one_mem _) h
      rw [one_mul, s.arch hφ (hT t), h1, h1, I_smul, I_smul, ← I_right', s₁.arch hψ (hT₁ t), ← hl', ← hl'] at k
      apply mul_left_cancel₀ hc
      exact k.trans (by ring)
    have d := dg (l.comp L)
    rw [k] at d
    have z : l (T₁ 0 (L f)) = l (L f) := by
      rw [hl', hl', ← s₁.arch hψ (hT₁ 0), I_right']; simp
    have d2 := d.unique (hd.mul (dg₁ l))
    rw [z, h0] at d2
    simp only [sc, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul,
      ContinuousLinearMap.comp_apply] at d2
    rw [← hl', map_sub, map_add, map_smul, d2, Pi.zero_apply, smul_eq_mul, sub_self])
  rw [map_sub, sub_eq_zero, map_add, map_smul] at this
  rw [this, e, s₁.wdL γ₁ hγ₁ _ (b.pol f hf) _ hf₁ _ _ ag₁ a₁ e]

end

end PositivityTheory.ThKG.Loc

end
