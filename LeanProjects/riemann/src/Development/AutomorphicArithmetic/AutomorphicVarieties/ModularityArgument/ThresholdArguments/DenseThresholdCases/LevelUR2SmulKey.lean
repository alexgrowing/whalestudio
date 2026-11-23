import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2SmulKey
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CLocConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2BaseEq

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem sk_hecke {A M ι ι₀ : Type} [CommRing A] [AddCommGroup M] [Module A M] (Y Y₀ : Submodule A M)
    (op : ι → Module.End A M) (op₀ : ι₀ → Module.End A M) [h : Fact (CommOn Y op)] [h₀ : Fact (CommOn Y₀ op₀)] (j : ι → ι₀)
    (hop : ∀ i, op i = op₀ (j i)) (hm : ∀ f, f ∈ Y ↔ f ∈ Y₀) :
    ∃ φ : heckeAlg Y op →ₐ[A] heckeAlg Y₀ op₀, (∀ i, φ (heckeGen Y op i) = heckeGen Y₀ op₀ (j i)) ∧
      ∀ (t : heckeAlg Y op) (y : Y) (y₀ : Y₀), y.1 = y₀.1 →
        ((t : Module.End A Y) y).1 = ((φ t : Module.End A Y₀) y₀).1 := by
  have hle : Y₀ ≤ Y := fun f hf => (hm f).2 hf
  obtain ⟨φ, h1, h2⟩ := levelUR2HeckeMap A M M ι₀ ι Y₀ Y op₀ op (Submodule.inclusion hle) j
    (Submodule.inclusion_injective hle) fun i y => by
      rw [hop]
      rfl
  refine ⟨φ, h1, fun t y y₀ e => ?_⟩
  have e' : y = Submodule.inclusion hle y₀ := Subtype.ext e
  rw [e', ← h2]
  rfl
private theorem sk_bot {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y Y₀ : Submodule A M}
    (hm : ∀ f, f ∈ Y ↔ f ∈ Y₀) : Y = ⊥ ↔ Y₀ = ⊥ := by
  rw [Submodule.ext hm]
private theorem sk_zero {A M R : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y Y₀ : Submodule A M}
    (hY : Y = ⊥) (ν : R → Y → M) (hν : ∀ t, ν t 0 = 0) (μ : Module.End A Y₀) (t : R) (y : Y) (y₀ : Y₀) (e : y.1 = y₀.1) :
    ν t y = (μ y₀).1 := by
  have h : y = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hY _ y.2)
  have h₀ : y₀ = 0 := Subtype.ext (e.symm.trans (congrArg Subtype.val h))
  rw [h, h₀, hν, map_zero]
  rfl
private theorem sk_comp {O : Type} [CommRing O] {R R₀ T T₀ : Type} [CommRing R] [Algebra O R] [CommRing R₀] [Algebra O R₀]
    [CommRing T] [Algebra O T] [CommRing T₀] [Algebra O T₀] (f : R →ₐ[O] T) (f₀ : R₀ →ₐ[O] T₀) (β : R →ₐ[O] R₀)
    (Φ : T →ₐ[O] T₀) (φ : T →+* T₀) (hφ : ∀ x, Φ x = φ x) {n : ℕ} {G G₀ V : Type} {Γ : V → Type} [Group G] [Group G₀]
    [∀ v, Group (Γ v)] (p : G →* G₀) (D : W.GDet n R G) (ψ : ∀ v, Fin n → Γ v →* Rˣ)
    (D₀ : W.GDet n R₀ G₀) (ψ₀ : ∀ v, Fin n → Γ v →* R₀ˣ)
    (hD : D.map β.toRingHom = D₀.comap p) (hψ : ∀ v i, W.pushCh β.toRingHom (ψ v i) = ψ₀ v i)
    (hu : ∀ f g : R →ₐ[O] T₀, D.map f.toRingHom = D.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g)
    (h : (D.map f.toRingHom).map φ = (D₀.map f₀.toRingHom).comap p ∧
      ∀ v i, W.pushCh φ (W.pushCh f.toRingHom (ψ v i)) = W.pushCh f₀.toRingHom (ψ₀ v i)) (t : R) :
    φ (f t) = f₀ (β t) := by
  obtain rfl : φ = Φ.toRingHom := RingHom.ext fun x => (hφ x).symm
  have e : Φ.comp f = f₀.comp β := by
    refine hu _ _ ?_ fun v i => ?_
    · have e1 : D.map (Φ.comp f).toRingHom = (D.map f.toRingHom).map Φ.toRingHom := ((CA.d_gmap D).2.1 _ _).symm
      have e2 : D.map (f₀.comp β).toRingHom = (D.map β.toRingHom).map f₀.toRingHom := ((CA.d_gmap D).2.1 _ _).symm
      rw [e1, e2, h.1, hD]
      rfl
    · have e := h.2 v i
      rw [← hψ] at e
      exact e
  exact DFunLike.congr_fun e t
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.levelUR2SmulKey_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q₀ τ₀).X.I.T →* Aˣ), (hset Q₀ τ₀).IsWt θ →  ∀ (a : (hset Q₀ τ₀).Op → c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q τ₀).Op → (hset Q₀ τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → ∀ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O), (hset Q τ₀).IsWt θ' → @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ → (∀ i, a' i = a (j i)) → (∀ i, (hset Q τ₀).op A i = (hset Q₀ τ₀).op A (j i)) → (∀ f : (hset Q₀ τ₀).X.Fn A m, f ∈ (hset Q τ₀).MK θ' a' K ↔ f ∈ (hset Q₀ τ₀).MK θ a K₀) → ∀ (R₀ R : Type) [CommRing R₀] [Algebra c.O R₀] [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R₀ V₀.frame.G₀) (ψ₀ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* R₀ˣ) (D : W.GDet n R V.frame.G₀) (ψ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* Rˣ) (β : R →ₐ[c.O] R₀), D.map β.toRingHom = D₀.comap p → (∀ v i, W.pushCh β.toRingHom (ψ v i) = ψ₀ v i) → (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D.map f.toRingHom = D.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g) → ∀ μ : R₀ →+* Module.End A ((hset Q₀ τ₀).MK θ a K₀), ((hset Q₀ τ₀).MK θ a K₀ = ⊥ ∨ ∃ (_ : Fact (CommOn ((hset Q₀ τ₀).MK θ a K₀) ((hset Q₀ τ₀).op A))) (_ : Alg.IsCO c.O ((hset Q₀ τ₀).TK θ a K₀)) (f : R₀ →ₐ[c.O] (hset Q₀ τ₀).TK θ a K₀), (hset Q₀ τ₀).IsMap θ a K₀ D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A ((hset Q₀ τ₀).MK θ a K₀))) → ∀ ν : R → (hset Q τ₀).MK θ' a' K → (hset Q₀ τ₀).X.Fn A m, (∀ t, ν t 0 = 0) → (∀ [Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A))] [Alg.IsCO c.O ((hset Q τ₀).TK θ' a' K)], ∃ f : R →ₐ[c.O] (hset Q τ₀).TK θ' a' K, (hset Q τ₀).IsMap θ' a' K D ψ f ∧ ∀ t y, ν t y = ((f t : Module.End A ((hset Q τ₀).MK θ' a' K)) y).1) → ∀ t (y : (hset Q τ₀).MK θ' a' K) (y₀ : (hset Q₀ τ₀).MK θ a K₀), y.1 = y₀.1 → ν t y = (μ (β t) y₀).1 := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ A _ _ _ θ hθ a K₀ K p hp hps hpr j hj1 hj2 θ' a' hθ' hθθ ha hop hm
    R₀ R _ _ _ _ D₀ ψ₀ D ψ β hD hψ hu μ hμ ν hν0 hν t y y₀ hy
  by_cases hne : (hset Q τ₀).MK θ' a' K = ⊥
  · exact sk_zero hne ν hν0 (μ (β t)) t y y₀ hy
  have hAx := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c m τ₀
  haveI hF : Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A)) :=
    ⟨((hiComm L Ω l n c _ hAx A θ' hθ' K).2.2.2 a').1⟩
  obtain ⟨hCO, -⟩ := hiAlg L Ω l n c _ hAx A θ' hθ' a' K hne
  obtain ⟨f, hf, hνf⟩ := hν
  obtain ⟨hF₀, hCO₀, f₀, hf₀, hμf⟩ := hμ.resolve_left fun h => hne ((sk_bot hm).2 h)
  obtain ⟨φ, hg, hφ⟩ : ∃ φ : (hset Q τ₀).TK θ' a' K →ₐ[A] (hset Q₀ τ₀).TK θ a K₀,
      (∀ i, φ ((hset Q τ₀).gen θ' a' K i) = (hset Q₀ τ₀).gen θ a K₀ (j i)) ∧
      ∀ (t : (hset Q τ₀).TK θ' a' K) (y : (hset Q τ₀).MK θ' a' K) (y₀ : (hset Q₀ τ₀).MK θ a K₀), y.1 = y₀.1 →
        ((t : Module.End A ((hset Q τ₀).MK θ' a' K)) y).1 = ((φ t : Module.End A ((hset Q₀ τ₀).MK θ a K₀)) y₀).1 :=
    sk_hecke _ _ _ _ (h := hF) (h₀ := hF₀) j hop hm
  have hB := _root_.UpperTheory.V.Hi.levelUR2BaseEq_alt hN l L Ω s n hn V₀ V Q₀ Q c m τ₀ A θ hθ a K₀ K p hp hps hpr j hj1 hj2 θ' a' hθ' hθθ ha
    _ _ hf₀ _ _ hf φ hg
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (hset Q τ₀).TK θ' a' K →ₐ[c.O] (hset Q₀ τ₀).TK θ a K₀, ∀ x, Φ x = φ x :=
    ⟨φ.restrictScalars c.O, fun _ => rfl⟩
  have e := sk_comp f f₀ β Φ φ.toRingHom hΦ p D ψ D₀ ψ₀ hD hψ (hu _) hB t
  refine (hνf t y).trans ((hφ (f t) y y₀ hy).trans ?_)
  exact congrArg (fun u : Module.End A ((hset Q₀ τ₀).MK θ a K₀) => (u y₀).1)
    ((congrArg Subtype.val e).trans (hμf (β t)).symm)
end
