import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapSnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LiePull

section Lat

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {Ω : Type} [Field Ω]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem lat_eq_span (M : LieModel G ξ E) (p : Cpt ξ)
    (hx : Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ) {r : ℕ}
    (b : Fin r → ExtE hx M) (hsp : Submodule.span (X.presheaf.stalk p.1) (Set.range b) = ⊤) :
    M.lat p = Submodule.span (regAt ξ p) (Set.range fun k => val (b k)) := by
  have car := (lieLat_carrier X G Ω ξ E M p).1
  apply le_antisymm
  · intro e he
    obtain ⟨v, hv⟩ := (car e).1 he
    let y : ExtE hx M := ⟨e, v, hv⟩
    have hy : y ∈ Submodule.span (X.presheaf.stalk p.1) (Set.range b) := by
      rw [hsp]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
    have he' : e = ∑ k, genMap ξ p (c k) • val (b k) := by
      have h1 : val y = e := rfl
      rw [← h1, ← hc, map_sum]
      rfl
    rw [he']
    refine Submodule.sum_mem _ fun k _ => ?_
    exact Submodule.smul_mem _ (⟨genMap ξ p (c k), c k, rfl⟩ : regAt ξ p) (Submodule.subset_span ⟨k, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact (car _).2 (val_spec (b k))

theorem ext_basis {A : Type} [CommRing A] [IsLocalRing A] {g : A →+* Ω} {x : Spec (CommRingCat.of A) ⟶ X}
    (hs : Smooth G.hom) (hg : Function.Injective g) (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ)
    (M : LieModel G ξ E) : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) A (ExtE hx M)) :=
  GlobalTheory.T.lie_model_free_over_local_ring X G hs A x (ExtE hx M) (extModel hg hx M)

end Lat

theorem frame : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X'), IsCptGen ξ → IsCptGen ξ' → ∀ (f : X' ⟶ X) (i : Ω →+* Ω') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → Smooth G.hom → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (E' : Type) [AddCommGroup E'] [Module Ω' E'] (M' : LieModel G' ξ' E') (j : E →+ E'), (∀ v, (M'.pt (j v)).left ≫ φ = spMap (dualMap i) ≫ (M.pt v).left) → ∀ q' : Cpt ξ', ∃ (r : ℕ) (B : Module.Basis (Fin r) Ω E) (B' : Module.Basis (Fin r) Ω' E') (v : Fin r → (epsAt (X.fromSpecStalk (f q'.1)) ⟶ G)) (v' : Fin r → (epsAt (X'.fromSpecStalk q'.1) ⟶ G')), (∀ k, B' k = j (B k)) ∧ M.lat ⟨f q'.1, hd.specializes q'⟩ = Submodule.span (regAt ξ ⟨f q'.1, hd.specializes q'⟩) (Set.range B) ∧ M'.lat q' = Submodule.span (regAt ξ' q') (Set.range B') ∧ (∀ k, M.Extends ⟨f q'.1, hd.specializes q'⟩ (B k) (v k)) ∧ (∀ k, M'.Extends q' (B' k) (v' k)) ∧ ∀ k, (v' k).left ≫ φ = spMap (dualMap (f.stalkMap q'.1).hom) ≫ (v k).left := by
  intro X X' Ω Ω' _ _ ξ ξ' hξ hξ' f i hd G _ _ G' _ _ φ hG hs E _ _ M E' _ _ M' j hj q'
  have hp : genPt ξ ⤳ f q'.1 := hd.specializes q'
  have hx := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨f q'.1, hp⟩
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ') q'
  have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap q'.1).hom) ≫ X.fromSpecStalk (f q'.1) =
      X'.fromSpecStalk q'.1 ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hρ' : (genMap ξ' q').comp (f.stalkMap q'.1).hom = i.comp (genMap ξ ⟨f q'.1, hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd q'.1 q'.2 hp)
  have hg := hξ.inj ⟨f q'.1, hp⟩
  have hg' := hξ'.inj q'
  obtain ⟨r, ⟨b⟩⟩ := ext_basis (A := X.presheaf.stalk (f q'.1)) hs hg hx M
  obtain ⟨hli, hsp⟩ := bc hs (genMap ξ ⟨f q'.1, hp⟩) (X.fromSpecStalk (f q'.1)) ξ hx (extModel hg hx M) M b
    (fun k => val (b k)) (fun k => (vec_spec (b k)).2)
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ k, B k = val (b k) := fun k => by simp [B]
  obtain ⟨hli', hsp'⟩ := bc hs i ξ (ξ' ≫ f) hd.symm M (LieMove.pushModel hG M') B (fun k => j (B k)) (fun k => hj _)
  let B' : Module.Basis (Fin r) Ω' E' := Module.Basis.mk hli' hsp'.ge
  have hB' : ∀ k, B' k = j (B k) := fun k => by simp [B']
  have up : ∀ k, ∃ u : epsAt (X'.fromSpecStalk q'.1) ⟶ G',
      Ext (genMap ξ' q') (X'.fromSpecStalk q'.1) M' (j (val (b k))) u ∧
      u.left ≫ φ = spMap (dualMap (f.stalkMap q'.1).hom) ≫ (vec (b k)).left :=
    fun k => ext_up hG hj hρ hρ' hx' (vec_spec (b k))
  choose u hu huφ using up
  let b' : Fin r → ExtE hx' M' := fun k => ⟨j (val (b k)), u k, hu k⟩
  obtain ⟨-, hsp''⟩ := bc hs (f.stalkMap q'.1).hom (X.fromSpecStalk (f q'.1)) (X'.fromSpecStalk q'.1 ≫ f) hρ
    (extModel hg hx M) (LieMove.pushModel hG (extModel hg' hx' M')) b b'
    (fun k => by
      have e₁ : vec (b' k) = u k := (vec_spec (b' k)).unique hg' (hu k)
      show (vec (b' k)).left ≫ φ = _
      rw [e₁]
      exact huφ k)
  refine ⟨r, B, B', fun k => vec (b k), u, hB', ?_, ?_, ?_, ?_, huφ⟩
  · rw [lat_eq_span M _ hx b b.span_eq]
    congr 2
    exact funext fun k => (hB k).symm
  · rw [lat_eq_span M' q' hx' b' hsp'']
    congr 2
    exact funext fun k => by rw [hB', hB]; rfl
  · intro k
    rw [hB]
    exact vec_spec (b k)
  · intro k
    rw [hB', hB]
    exact hu k

end GlobalTheory.CompanionTheory.Ar.LiePull
