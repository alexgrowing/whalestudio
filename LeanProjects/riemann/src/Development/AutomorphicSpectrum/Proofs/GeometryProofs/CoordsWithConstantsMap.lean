import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsForComponent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsModelVectorBundlesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocksStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodgeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAddedProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsAddedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelAddedCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorEquivOfBasisExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagUnderEquivStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBundleUnderEquivStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelConstantsExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DimensionPlusFlagCountStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnipotentEntriesFieldDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

set_option maxHeartbeats 1000000 in
open GlobalTheory.CompanionTheory.Ar.FlagStep in

theorem GlobalTheory.CompanionTheory.Ar.exists_flagStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] [CharZero Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω₀) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω₀ Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω₀ Li) (L : CMType H ⊕ CMType H → Lat ξ Li) (bd : Ideal (MRing J)), IsCptGen ξ₀ → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ξ ≫ f = ξ₀ → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ s, (L s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s)))) → (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) → Cmp.IsSncModel y D.dim bd → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G)) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (_ : Algebra Ω₀ Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) (_ : AddCommGroup Li) (_ : Module Ω Li) (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module Ω₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) ∧ ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) ∧ M.IsActOf t.act.act ρ ∧ (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) ∧ IsGenericFlag (Ω' := Ω) j V₀ b 1 ∧ (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) ∧ Cmp.IsSncModel y (Top.dimFl (CMType H) (D.p + D.q)) bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  classical
  intro E _ _ _ H D l Xo c Y Ω₀ _ _ ξ₀ K _ J _ y X ξ f cst t m Li _ _ M ρ L bd hgen hall htie hξ hcst hact hvb hLeq hsnc hbd
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  obtain ⟨X', Ω', _, _, ξ', f', N, x', b₁, htie', hall', hdom, hsm, -, hgf, hfl⟩ :=
    GlobalTheory.T.exists_model_vector_bundles X Ω₀ ξ Li ((k : K) → J k) (fun c' => ∏ k, y ⟨k, c' k⟩) (CMType H ⊕ CMType H) (labelRk D)
      (fun s => eigSp ρ (cst.comp (labelEmb c s))) L htie hall hvb
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω₀ Ω').injective
  have hg : IsCptGen ξ := htie.gen
  have hg' : IsCptGen ξ' := htie'.gen
  obtain ⟨t', ⟨m₁⟩⟩ : ∃ t' : SAB H X', Nonempty (SABMap t' t f') := by
    obtain ⟨_, _, _, _, _, m₁, -⟩ := sabPull Out.proved_CubePullSt f' t
    exact ⟨_, ⟨m₁⟩⟩
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H Y.X X X' Y.t t t' f f' m m₁
  obtain ⟨Li', _, _, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t'.G Ω' ξ'
  obtain ⟨ρ', hact', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ t'.G Ω' ξ' Li' M' (𝓞 E) t'.act.act t'.act.hom
    t'.act.one t'.act.mul t'.act.add
  obtain ⟨j', hj₁, hj₂, hj₃, hj₄, hj₅⟩ := GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' f' m₁ Ω₀ Ω' ξ ξ' (algebraMap Ω₀ Ω') Li Li' M M'
    hg hg' hdom
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G Ω₀ ξ₀
  have hdom₀ : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (RingHom.id Ω₀) := by
    show ξ ≫ f = _
    rw [hξ]
    simp
  obtain ⟨a₀, ha₁, ha₂, ha₃, ha₄, -⟩ := GlobalTheory.T.lie_model_dominant_hodge E H Y.X Y.t X t f m Ω₀ Ω₀ ξ₀ ξ (RingHom.id Ω₀) Li₀ Li M₀ M
    hgen hg hdom₀

  let aL : Li₀ →ₗ[Ω₀] Li := { toFun := a₀, map_add' := a₀.map_add, map_smul' := fun c e => ha₂ c e }
  have hainj : Function.Injective aL := by
    refine (injective_iff_map_eq_zero aL).2 fun e he => ?_
    by_contra hne
    have h1 := ha₃ 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  have hasurj : Function.Surjective aL := by
    have : LinearMap.range aL = ⊤ := by
      rw [eq_top_iff, ← ha₄]
      exact Submodule.span_le.2 (by rintro _ ⟨e, rfl⟩; exact ⟨e, rfl⟩)
    exact LinearMap.range_eq_top.1 this
  let a : Li₀ ≃ₗ[Ω₀] Li := LinearEquiv.ofBijective aL ⟨hainj, hasurj⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.tensor_equiv_of_basis_extension Ω₀ Ω' Li Li' j' hj₂ hj₃ hj₄
  have hjinj : Function.Injective j' := by
    refine (injective_iff_map_eq_zero j').2 fun e he => ?_
    by_contra hne
    have h1 := hj₃ 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  have hint := GlobalTheory.T.lie_model_pullback_action_ring E H X X' t t' f' m₁ Ω₀ Ω' ξ ξ' (algebraMap Ω₀ Ω') Li Li' M M' ρ ρ' j' hdom hact hact' hj₁
  have hjΦ : Φ.toLinearMap.toAddMonoidHom.comp (TensorProduct.mk Ω₀ Ω' Li 1).toAddMonoidHom = j' :=
    AddMonoidHom.ext hΦ
  let cst' : c.F →+* Ω' := (algebraMap Ω₀ Ω').comp cst
  have heig : ∀ (σ : 𝓞 E →+* Ω₀) e, j' e ∈ eigSp ρ' ((algebraMap Ω₀ Ω').comp σ) ↔ e ∈ eigSp ρ σ := by
    intro σ e
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← hint a e, RingHom.comp_apply, ← hj₂]
    exact hjinj.eq_iff
  let V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀ := fun s => (eigSp ρ (cst.comp (labelEmb c s))).comap aL
  have hgf' := GlobalTheory.T.generic_flag_under_equiv Ω₀ Ω' Li₀ Li _ Li' a _ Φ _ (labelRk D) _ V₀ b₁ 1 (fun s e => Iff.rfl) hgf
  obtain ⟨cc, u, -, -, -, -, hu1, hu0, -, halg, -, hfr⟩ := hgf
  have htop := GlobalTheory.T.unipotent_entries_field_degree Ω₀ Ω' _ (labelRk D) u hu1 hu0 hfr
  have hgf'' : IsGenericFlag (Ω' := Ω') (j'.comp aL.toAddMonoidHom) V₀ (fun s k => Φ (b₁ s k)) 1 := by
    rw [← hjΦ]
    exact hgf'
  have hg'' : IsCptGen ξ' := hg'
  have tie₁ := GlobalTheory.T.coords_added_projective X X' Ω₀ Ω' ξ ξ' f' K J y N x' hall htie htie' hdom
  have snc₁ := GlobalTheory.T.snc_model_added_coords X X' Ω₀ Ω' ξ ξ' f' K J y N x' D.dim bd _ _ hall hall' htie tie₁ hdom hsm halg htop hsnc
  rw [GlobalTheory.T.dimension_plus_flag_count E H D l c] at snc₁
  refine ⟨Ω', inferInstance, inferInstance, inferInstance, Unit ⊕ K, inferInstance, addJ J N, inferInstance,
    addY y x', X', ξ', f' ≫ f, cst', t', n, Li', inferInstance, inferInstance, M', ρ', Li₀, inferInstance,
    inferInstance, M₀, j'.comp aL.toAddMonoidHom, V₀, fun s k => Φ (b₁ s k),
    bd.map (MvPolynomial.rename (addV J N)), hall', tie₁, fun q hq => EigBase.isIntegrallyClosed_of_snc tie₁ snc₁ q hq,
    ?_, ?_, hact', ?_, ?_, ?_, ?_, snc₁, ?_⟩
  · show ξ' ≫ f' ≫ f = _
    rw [← Category.assoc, show ξ' ≫ f' = _ from hdom, Category.assoc, hξ]
  · have hd : ξ' ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap Ω₀ Ω')) ≫ ξ := hdom
    have e₁ : ξ' ≫ (f' ≫ f) ≫ Y.s = (ξ' ≫ f') ≫ f ≫ Y.s := by simp only [Category.assoc]
    rw [e₁, hd, Category.assoc, hcst]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · intro e
    rw [hn]
    show (M'.pt (j' (a₀ e))).left ≫ m₁.φ ≫ m.φ = _
    rw [← Category.assoc, hj₁, Category.assoc, ha₁, SatModel.spMap_dualMap_id, Category.id_comp]
  · intro s e
    exact (heig _ _).symm.trans Iff.rfl
  · exact hgf''
  · intro s
    have heig' : ∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
        j' e ∈ eigSp ρ' (((algebraMap Ω₀ Ω').comp cst).comp (labelEmb c s)) := by
      intro s e he
      rw [RingHom.comp_assoc]
      exact (heig _ e).2 he
    have hfl' : ∀ s, ((L s).pull ξ' f' j').IsFlagVBOn Set.univ (fun k => Φ (b₁ s k)) := by
      intro s
      rw [← hjΦ]
      exact GlobalTheory.T.flag_bundle_under_equiv X X' Ω₀ Ω' ξ ξ' f' Li _ Li' (L s) _ Φ Set.univ _ (b₁ s) (hfl s)
    have hi₀ : ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q) :=
      fun q hq => EigBase.isIntegrallyClosed_of_snc htie hsnc q hq
    have hi₁ : ∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q) :=
      fun q hq => EigBase.isIntegrallyClosed_of_snc tie₁ snc₁ q hq
    exact GlobalTheory.T.lie_model_constants_extension E H l c X X' t t' f' Ω₀ Ω' ξ ξ' cst Li Li' M M' ρ ρ' L j' (labelRk D) (fun s k => Φ (b₁ s k)) hg hg'
      hdom hact hact' hi₀ hi₁ hLeq hj₅ heig' hfl' s
  · intro z w hw
    have hw₁ := GlobalTheory.T.complex_coords_added X X' Ω₀ Ω' ξ ξ' f' K J y N x' z w hall htie hg'' hall' hdom hw
    have hne : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hw.1 k).imp fun _ h => h.ne_zero
    have hne' : ∀ k, ∃ i, w (addV J N ⟨k, i⟩) ≠ 0 := fun k => (hw₁.1 k).imp fun _ h => h.ne_zero
    rw [EigBase.mem_mcPts_rename (addV J N) bd w hne hne']
    exact hbd (z ≫ f') _ hw₁
