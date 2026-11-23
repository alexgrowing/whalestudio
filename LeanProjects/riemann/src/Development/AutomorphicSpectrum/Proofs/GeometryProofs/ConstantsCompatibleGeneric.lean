import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapId
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRankStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodgeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcLie

theorem mem_eigSp_iff {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {O : Type} [CommRing O]
    (ρ : O →+* Module.End R V) (σ : O →+* R) (e : V) :
    e ∈ eigSp ρ σ ↔ ∀ a, ρ a e = σ a • e := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem exists_lie_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → 𝔐.ξ₀ = y₁ ≫ Y.j → 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) → 𝔐.fn.comp cst₀ = 𝔐.cst → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ (a : 𝔐.Ω₀) e, j (a • e) = 𝔐.fn a • j e) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (∀ s, LinearIndependent 𝔐.Ω₀ (b s) ∧ Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s) ∧ (∀ s, LinearIndependent Ω fun k => j (b s k)) ∧ ∀ s, Submodule.span Ω (Set.range fun k => j (b s k)) = 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J y 𝔐 y₀ cst₀ y₁ hy hy₁ hs₀ hcst
  classical
  haveI : CharZero 𝔐.Ω₀ := (RingHom.charZero_iff 𝔐.fn.injective).2 inferInstance
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G 𝔐.Ω₀ 𝔐.ξ₀
  obtain ⟨ρ₀, hρ₀, -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ Y.t.G 𝔐.Ω₀ 𝔐.ξ₀ Li₀ M₀ (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  obtain ⟨j, hj, hsl, hli, -, -⟩ := GlobalTheory.T.lie_model_dominant_hodge E H Y.X Y.t 𝔐.X 𝔐.t 𝔐.f 𝔐.m 𝔐.Ω₀ Ω 𝔐.ξ₀ 𝔐.ξ 𝔐.fn Li₀ 𝔐.Li M₀ 𝔐.M
    𝔐.gen₀ 𝔐.tie.gen 𝔐.fn_over
  obtain ⟨m₀, -⟩ := GlobalTheory.CompanionTheory.Ar.exists_sabMap_id E H Y.X Y.t
  obtain ⟨hfd₀, hrk₀⟩ := GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y Y.X 𝔐.Ω₀ 𝔐.ξ₀ (𝟙 _) y₁ Y.t m₀ Li₀ M₀ ρ₀ cst₀
    (by rw [Category.comp_id]; exact hy₁) (by rw [Category.id_comp]; exact hs₀) hρ₀
  obtain ⟨hfd, hrk⟩ := GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y 𝔐.X Ω 𝔐.ξ 𝔐.f y₀ 𝔐.t 𝔐.m 𝔐.Li 𝔐.M 𝔐.ρ 𝔐.cst hy 𝔐.cst_over 𝔐.act
  have hρj : ∀ (a : 𝓞 E) e, j (ρ₀ a e) = 𝔐.ρ a (j e) := by
    intro a e
    apply 𝔐.M.inj
    refine Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ?_)
    · rw [hj, hρ₀ a e, 𝔐.act a (j e), Over.comp_left, Over.comp_left, Category.assoc, 𝔐.m.act, ← Category.assoc,
        ← Category.assoc (𝔐.M.pt (j e)).left]
      exact congrArg (· ≫ (Y.t.act.act a).left) (hj e).symm
    · rw [Over.w, Over.w]
  have hinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun v hv => by_contra fun h0 => ?_
    exact (hli 1 (fun _ => v) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hv
  have hσ : ∀ s (a : 𝓞 E), 𝔐.fn ((cst₀.comp (labelEmb c s)) a) = 𝔐.emb s a := by
    intro s a
    show (𝔐.fn.comp cst₀) (labelEmb c s a) = 𝔐.cst (labelEmb c s a)
    rw [hcst]
  let V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀ := fun s => eigSp ρ₀ (cst₀.comp (labelEmb c s))
  have hV : ∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s := by
    intro s e
    show e ∈ eigSp ρ₀ _ ↔ j e ∈ eigSp 𝔐.ρ _
    rw [mem_eigSp_iff, mem_eigSp_iff]
    refine forall_congr' fun a => ?_
    rw [← hρj, ← hσ, ← hsl]
    exact hinj.eq_iff.symm
  let B : ∀ s, Module.Basis (Fin (labelRk D s)) 𝔐.Ω₀ (V₀ s) := fun s => Module.finBasisOfFinrankEq _ _ (hrk₀ s)
  let b : ∀ s, Fin (labelRk D s) → Li₀ := fun s k => (B s k : Li₀)
  have hbli : ∀ s, LinearIndependent 𝔐.Ω₀ (b s) := fun s =>
    (B s).linearIndependent.map' (V₀ s).subtype (Submodule.ker_subtype _)
  have hbsp : ∀ s, Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s := by
    intro s
    have h : Set.range (b s) = (V₀ s).subtype '' Set.range (B s) := by
      rw [← Set.range_comp]
      rfl
    rw [h, ← Submodule.map_span, (B s).span_eq, Submodule.map_top, Submodule.range_subtype]
  have hjli : ∀ s, LinearIndependent Ω fun k => j (b s k) := fun s => hli _ _ (hbli s)
  refine ⟨Li₀, inferInstance, inferInstance, M₀, j, V₀, b, hj, hsl, hV, fun s => ⟨hbli s, hbsp s⟩, hjli, fun s => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (hV s _).1 ((hbsp s) ▸ Submodule.subset_span ⟨k, rfl⟩)
  · rw [finrank_span_eq_card (hjli s), Fintype.card_fin]
    exact (hrk s).symm

end GlobalTheory.CompanionTheory.Ar.HcLie
