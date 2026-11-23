import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtension
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPoint
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.FlagsLieBaseChange

theorem bc {S : Scheme.{0}} {G : Over S} [GrpObj G] (hs : Smooth G.hom) {R R' : Type} [Field R] [Field R']
    (f : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (y : Spec (CommRingCat.of R') ⟶ S)
    (hy : Spec.map (CommRingCat.ofHom f) ≫ x = y) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E']
    [Module R' E'] (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap f)) ≫ (M.pt e).left) ∧
      IsExtOver f j ∧ Submodule.span R' (Set.range j) = ⊤ ∧ Module.Finite R E := by
  subst hy
  let _ := f.toAlgebra
  obtain ⟨j, hj, hl, hb⟩ := PositivityTheory.HtPt.Htat.lie_bc S G R R' x E E' M M'
  haveI := hs
  haveI : Module.Finite R E := (PositivityTheory.HtPt.Htat.lie_fin S G R x E M).1
  let b₁ := Module.finBasis R E
  refine ⟨j, hj, ⟨hl, fun n b h => LiePull.indep_of_bases b₁ j (fun m B => (hb hs m B).1) b h⟩, ?_, inferInstance⟩
  refine top_le_iff.1 ((hb hs _ b₁).2.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

theorem basis {F Ω V W : Type} [Field F] [Field Ω] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module Ω W]
    [Module.Finite F V] {i : F →+* Ω} {j : V →+ W} (hj : IsExtOver i j) (U : Submodule F V) (U' : Submodule Ω W)
    (h : U' = Submodule.span Ω (j '' (U : Set V))) {n : ℕ} (B : Module.Basis (Fin n) Ω U') :
    ∃ b : Fin n → V, LinearIndependent F b ∧ Submodule.span F (Set.range b) = U := by
  let b := Module.finBasis F U
  have h1 : LinearIndependent F (fun k => (b k : V)) := b.linearIndependent.map' U.subtype U.ker_subtype
  have h2 : Submodule.span F (Set.range fun k => (b k : V)) = U := by
    have := congrArg (Submodule.map U.subtype) b.span_eq
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at this
  have h3 := hj.2 _ _ h1
  have h4 : Submodule.span Ω (Set.range fun k => j (b k : V)) = U' := by
    rw [h]
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      exact ⟨_, (b k).2, rfl⟩
    · rintro _ ⟨e, he, rfl⟩
      rw [← h2] at he
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 he
      rw [map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [hj.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h5 : Module.finrank F U = n := by
    have := finrank_span_eq_card h3
    rw [h4, Module.finrank_eq_card_basis B, Fintype.card_fin, Fintype.card_fin] at this
    exact this.symm
  subst h5
  exact ⟨_, h1, h2⟩

end PositivityTheory.Xgp.FlagsLieBaseChange

open PositivityTheory.Xgp.FlagsLieBaseChange in
theorem PositivityTheory.Xgp.exists_flags_lie_compact_dominated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (A : HodgeCpt Y S x) (F₀ : Type) [Field F₀] (ξ₀ : Spec (CommRingCat.of F₀) ⟶ Y.X) (ι : F₀ →+* Ω), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f ι → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module F₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j₁ : Li₀ →+ A.Li) (V₀ : CMType H ⊕ CMType H → Submodule F₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (A.M.pt (j₁ e)).left ≫ A.m.φ = spMap (dualMap ι) ≫ (M₀.pt e).left) ∧ IsExtOver ι j₁ ∧ (∀ s e, e ∈ V₀ s ↔ j₁ e ∈ A.Vgen s) ∧ ∀ s, LinearIndependent F₀ (b s) ∧ Submodule.span F₀ (Set.range (b s)) = V₀ s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J x A F₀ _ ξ₀ ι hgen hd
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G F₀ ξ₀
  obtain ⟨ρ₀, hact₀, -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ Y.t.G F₀ ξ₀ Li₀ M₀ (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  obtain ⟨j, hj, hext, hsp, hfin⟩ := bc Y.t.semi.smooth ι ξ₀ (A.ξ ≫ A.f) (Eq.symm hd) M₀
    (LieMove.pushModel A.m.cart A.M)
  have hj' : ∀ e, (A.M.pt (j e)).left ≫ A.m.φ = spMap (dualMap ι) ≫ (M₀.pt e).left := hj
  have hint := FlagStep.lieMap_act_pull E H Y.X A.X Y.t A.t A.f A.m F₀ Ω ξ₀ A.ξ ι Li₀ A.Li M₀ A.M ρ₀ A.ρ j hd hact₀
    A.act hj'
  have hjinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun e he => ?_
    by_contra hne
    have h1 := hext.2 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  let a : 𝓞 c.F →+* F₀ := (Spec.preimage (ξ₀ ≫ Y.s)).hom
  have ha : spMap a = ξ₀ ≫ Y.s := by
    simp only [spMap, a, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfa : ι.comp a = A.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have h1 : spMap (ι.comp a) = spMap (A.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← A.cst_over]
      have hd' : A.ξ ≫ A.f = spMap ι ≫ ξ₀ := hd
      calc spMap (ι.comp a) = spMap ι ≫ spMap a := by
            simp only [spMap, ← Spec.map_comp]; rfl
        _ = A.ξ ≫ A.f ≫ Y.s := by rw [ha, ← Category.assoc, ← hd', Category.assoc]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hainj : Function.Injective a := by
    have : Function.Injective (ι.comp a) := by
      rw [hfa]
      exact A.cst.injective.comp (IsFractionRing.injective (𝓞 c.F) c.F)
    exact Function.Injective.of_comp (f := ι) this
  let a' : c.F →+* F₀ := IsFractionRing.lift hainj
  have ha' : ι.comp a' = A.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
    rw [← hfa]
    refine RingHom.ext fun o => ?_
    exact congrArg ι (IsFractionRing.lift_algebraMap hainj o)
  haveI : CharZero F₀ := ι.charZero
  let σ : CMType H ⊕ CMType H → (𝓞 E →+* F₀) := fun s => a'.comp (labelEmb c s)
  have hσ : ∀ s, A.emb s = ι.comp (σ s) := fun s => by
    rw [← RingHom.comp_assoc, ha']
    rfl
  have hV : ∀ s, A.Vgen s = Submodule.span Ω (j '' (eigSp ρ₀ (σ s) : Set Li₀)) := fun s => by
    unfold HodgeCpt.Vgen
    rw [hσ]
    exact EigExt.eigSp_ext E F₀ Ω ι Li₀ A.Li j ρ₀ A.ρ (σ s) hext hsp fun a e => (hint a e).symm
  have hb := fun s => basis hext _ _ (hV s) (nonempty_basis_Vgen A s).some
  choose b hb using hb
  refine ⟨Li₀, inferInstance, inferInstance, M₀, j, fun s => eigSp ρ₀ (σ s), b, hj', hext, fun s e => ?_, hb⟩
  unfold HodgeCpt.Vgen
  rw [hσ]
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun a => ?_
  rw [← hint a e, RingHom.comp_apply ι, ← hext.1]
  exact hjinj.eq_iff.symm
