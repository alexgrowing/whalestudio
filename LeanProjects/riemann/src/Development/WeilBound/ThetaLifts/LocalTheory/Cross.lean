import Development.WeilBound.ThetaLifts.LocalTheory.ISmulEqZero

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF
open scoped Classical

variable {n d n₁ d₁ n₂ n₃ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {X₂ : Spc F E n₂} {X₃ : Spc F E n₃}

structure Cross (B : Base F E) (M₂ : Model σ X₂ W) (om₂ : Rep σ X₂ W) (M : Model σ X W) (om : Rep σ X W) {P : Type} [AddCommGroup P]
    [Module ℂ P] {Q : Pl F → Type} [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (pi₂ : SInf F (Fin n₂ × Fin d) →ₗ[ℂ] P)
    (p₂ : ∀ v, Fl F v n₂ d →ₗ[ℂ] Q v) (pi : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p : ∀ v, Fl F v n d →ₗ[ℂ] Q v) : Prop where
  fin : ∀ v, ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
    Acts (evFin F v) (om₂ (1, h)) φ φ₁ → Acts (evFin F v) (om (1, h)) φ' φ₁' → p₂ v φ = p v φ' → p₂ v φ₁ = p v φ₁'
  lie : ∀ γ ∈ Lines σ W, ∀ f ∈ M₂.Pol B.ψ B.emb, ∀ f' ∈ M.Pol B.ψ B.emb, ∀ (f₁ : SInf F _) (f₁' : SInf F _),
    ActsD (evI F) (fun t => om₂ (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f' f₁' → pi₂ f = pi f' → pi₂ f₁ = pi f₁'
  cpt : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M₂.Pol B.ψ B.emb, ∀ f' ∈ M.Pol B.ψ B.emb, ∀ (f₁ : SInf F _) (f₁' : SInf F _),
    Acts (evI F) (om₂ (1, k)) f f₁ → Acts (evI F) (om (1, k)) f' f₁' → pi₂ f = pi f' → pi₂ f₁ = pi f₁'

variable {B : Base F E} {P : Type} [AddCommGroup P] [Module ℂ P] {Q : Pl F → Type} [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)]
  {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁] {Q₁ : Pl F → Type} [∀ v, AddCommGroup (Q₁ v)] [∀ v, Module ℂ (Q₁ v)]
  {M : Model σ X W} {om : Rep σ X W} {pi : SInf F (Fin n × Fin d) →ₗ[ℂ] P} {p : ∀ v, Fl F v n d →ₗ[ℂ] Q v}
  {M₂ : Model σ X₂ W} {om₂ : Rep σ X₂ W} {pi₂ : SInf F (Fin n₂ × Fin d) →ₗ[ℂ] P} {p₂ : ∀ v, Fl F v n₂ d →ₗ[ℂ] Q v}
  {M₁ : Model σ X₁ W₁} {om₁ : Rep σ X₁ W₁} {pi₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁} {p₁ : ∀ v, Fl F v n₁ d₁ →ₗ[ℂ] Q₁ v}
  {M₃ : Model σ X₃ W₁} {om₃ : Rep σ X₃ W₁} {pi₃ : SInf F (Fin n₃ × Fin d₁) →ₗ[ℂ] P₁} {p₃ : ∀ v, Fl F v n₃ d₁ →ₗ[ℂ] Q₁ v}
  {S : ∀ v : Pl F, Submodule ℂ (Fl F v n d)} {S₁ : ∀ v : Pl F, Submodule ℂ (Fl F v n₁ d₁)} {H' : Plane E d d₁} {χ : Chr F E} {r : ℝ}
  {Ev : Fn F n d → Fn F n₁ d₁} {L : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)} {Λ : ∀ v : Pl F, Fl F v n d →ₗ[ℂ] Fl F v n₁ d₁}

theorem Side.cross (s : Side B M om pi p S) : Cross B M om M om pi p pi p :=
  ⟨fun v h hh a ha b hb a' ha' b' hb' => s.wdF v h hh a ha b hb a' ha' b' hb', s.wdL, s.wdK⟩

theorem Side.der (s : Side B M om pi p S) {γ} (hγ : γ ∈ Lines σ W) {f} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ g : SInf F _, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f g := by
  choose T hT _ using fun t : ℝ => s.op _ (hγ.2 (Multiplicative.ofAdd t))
  obtain ⟨g, -, ag, -⟩ := s.lie γ hγ T hT f hf
  exact ⟨g, ag⟩

theorem lams (s : Side B M om pi p S) (s₁ : Side B M₁ om₁ pi₁ p₁ S₁) (b : Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ)
    (j : Inj B M₁ om₁ pi₁ p₁ S₁) (pt : Pt B M S pi₁ p₁ L Λ) (c : Cross B M₂ om₂ M om pi₂ p₂ pi p)
    (c₁ : Cross B M₃ om₃ M₁ om₁ pi₃ p₃ pi₁ p₁) {i₀ i₁ r₁ r₂ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hW : W₁.IsSkew σ B r₁ r₂) :
    ∃ (li : P →ₗ[ℂ] P₁) (lf : ∀ v, Q v →ₗ[ℂ] Q₁ v), (∀ f ∈ M.Pol B.ψ B.emb, li (pi f) = pi₁ (L f)) ∧
      (∀ v, ∀ x ∈ S v, lf v (p v x) = p₁ v (Λ v x)) ∧ IsArchimedeanLocalEquivariantMap B M₂ M₃ om₂ om₃ H' χ r pi₂ pi₃ li ∧
      ∀ v, IsFiniteLocalEquivariantMap om₂ om₃ H' v χ r (p₂ v) (p₃ v) (lf v) := by
  obtain ⟨si, hi, hi'⟩ := exists_section pi (M.Pol B.ψ B.emb)
  choose sf hf hf' using fun v => exists_section (p v) (S v)
  have e1 : ∀ f ∈ M.Pol B.ψ B.emb, (pi₁ ∘ₗ (L : _ →ₗ[ℂ] _) ∘ₗ si) (pi f) = pi₁ (L f) := fun f h => by
    have := kerI s b j pt (si (pi f) - f) (sub_mem (hi _) h) (by rw [map_sub, hi' f h, sub_self])
    rwa [map_sub, map_sub, sub_eq_zero] at this
  have e2 : ∀ v, ∀ x ∈ S v, (p₁ v ∘ₗ Λ v ∘ₗ sf v) (p v x) = p₁ v (Λ v x) := fun v x h => by
    have := kerF s b j pt v (sf v (p v x) - x) (sub_mem (hf v _) h) (by rw [map_sub, hf' v x h, sub_self])
    rwa [map_sub, map_sub, sub_eq_zero] at this
  refine ⟨_, _, e1, e2, ⟨fun γ hγ hu f h f' a => ?_, fun γ hγ γ₁ hγ₁ τ hl c' hd f h f₁ h₁ f' f₁' a a₁ e => ?_,
    fun k hk k₁ hk₁ t hl f h f₁ h₁ f' f₁' a a₁ e => ?_⟩, fun v t h₁ m hl u hu huv hm φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' a a₁ e => ?_⟩
  · obtain ⟨x, hx, ex⟩ := s.ontoI (pi₂ f)
    choose T hT _ using fun t : ℝ => s.op _ (hγ.2 (Multiplicative.ofAdd t))
    obtain ⟨x', hx', ax, -⟩ := s.lie γ hγ T hT x hx
    rw [c.lie γ hγ f h x hx f' x' a ax ex.symm, e1 _ hx']
    exact eqN s s₁ b j pt hγ hu hx ax
  · obtain ⟨x, hx, ex⟩ := s.ontoI (pi₂ f)
    choose T hT _ using fun t : ℝ => s.op _ (hγ.2 (Multiplicative.ofAdd t))
    obtain ⟨x', hx', ax, -⟩ := s.lie γ hγ T hT x hx
    obtain ⟨y, hy, ey⟩ := s₁.ontoI (pi₃ f₁)
    obtain ⟨y', ay⟩ := s₁.der hγ₁ hy
    have h0 : τ 0 = 1 := levi_t_one hH (h₁ := γ₁ (Multiplicative.ofAdd 0)) (by simpa using hl 0)
    rw [c.lie γ hγ f h x hx f' x' a ax ex.symm, e1 _ hx', c₁.lie γ₁ hγ₁ f₁ h₁ y hy f₁' y' a₁ ay ey.symm, ← ey]
    exact eqL s s₁ b j pt hγ hγ₁ hl h0 hd hx hy ax ay (by rw [← e1 _ hx, ex, e, ey])
  · obtain ⟨x, hx, ex⟩ := s.ontoI (pi₂ f)
    obtain ⟨T, hT, hT'⟩ := s.op k hk.1
    obtain ⟨y, hy, ey⟩ := s₁.ontoI (pi₃ f₁)
    obtain ⟨T₁, hT₁, -⟩ := s₁.op k₁ hk₁.1
    rw [c.cpt k hk f h x hx f' _ a (hT.2 x) ex.symm, e1 _ (hT' hk x hx), c₁.cpt k₁ hk₁ f₁ h₁ y hy f₁' _ a₁ (hT₁.2 y) ey.symm]
    exact eqK s s₁ b j pt hk hk₁ hl hx hy (hT.2 x) (hT₁.2 y) (by rw [← e1 _ hx, ex, e, ey])
  · obtain ⟨x, hx, ex⟩ := s.onto v (p₂ v φ)
    obtain ⟨x', hx', ax⟩ := s.stab v _ (uat_mul huv hm) x hx
    obtain ⟨y, hy, ey⟩ := s₁.onto v (p₃ v φ₁)
    have hh := levi_at hH hW hl hm
    obtain ⟨y', hy', ay⟩ := s₁.stab v _ hh y hy
    rw [c.fin v _ (uat_mul huv hm) φ hφ x (s.le v hx) φ' hφ' x' (s.le v hx') a ax ex.symm, e2 v _ hx',
      c₁.fin v _ hh φ₁ hφ₁ y (s₁.le v hy) φ₁' hφ₁' y' (s₁.le v hy') a₁ ay ey.symm]
    exact eqF s s₁ b j pt v hl hu hh hx hx' (s₁.le v hy) (s₁.le v hy') ax ay (by rw [← e2 v _ hx, ex, e, ey])

end PositivityTheory.ThKG.Loc

end
