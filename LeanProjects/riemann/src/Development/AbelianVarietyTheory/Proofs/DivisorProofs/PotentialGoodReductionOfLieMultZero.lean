import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveAnnihilatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqZeroOfDualKilledByTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCoordinatesOnFieldFibresLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPartFibreLieAlgebraCharactersStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

open scoped Matrix

namespace GlobalTheory.PotGoodLie

theorem proper_pull {K W L : Type} [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L]
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (hM : GlobalTheory.SS.IsModel (L := L) A G)
    (hA : IsAbelianScheme A) : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
  obtain ⟨e, -⟩ := hM
  have := hA.proper
  have h : ((Over.pullback (spMap (algebraMap W L))).obj G).hom = e.hom.left ≫ ((Over.pullback (spMap (algebraMap K L))).obj A).hom := (Over.w e.hom).symm
  rw [h]
  have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
    show IsProper (pullback.snd A.hom _)
    infer_instance
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  infer_instance

theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eq_one_of_lieMult_zero {S : Scheme.{0}} {O : Type} [CommRing O] {G : Over S} [GrpObj G] (a : OAct O G)
    {k : Type} [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (h : LieMult a t τ 0) (w : epsPt t ⟶ G)
    (hw : IsLieEigen a t τ w) : w = 1 := by
  obtain ⟨v, -, H⟩ := h
  obtain ⟨c, ⟨u, -, hu⟩, -⟩ := H w hw
  simpa using hu

theorem lift_ext (V K W L Ω : Type) [CommRing V] [Field K] [CommRing W] [IsDomain W] [Field L] [Field Ω]
    [IsAlgClosed Ω] [Algebra V K] [Algebra V W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    (hc : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hfin : Module.Finite V W) (g : K →+* Ω) : ∃ g' : L →+* Ω, g'.comp (algebraMap K L) = g := by
  letI := g.toAlgebra
  have hint : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have halg : ∀ w : W, IsAlgebraic K (algebraMap W L w) := by
    intro w
    obtain ⟨p, hp, hpw⟩ := hint.isIntegral w
    refine ⟨p.map (algebraMap V K), (hp.map _).ne_zero, ?_⟩
    have := congrArg (algebraMap W L) hpw
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← this, hc]
  haveI : Algebra.IsAlgebraic K L := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    rw [div_eq_mul_inv]
    exact IsAlgebraic.mul (halg a) (IsAlgebraic.inv (halg b))
  exact ⟨(IsAlgClosed.lift : L →ₐ[K] Ω).toRingHom, by ext x; simp [RingHom.algebraMap_toAlgebra]⟩

theorem prod_of_add {A B J : Type} [AddCommMonoid A] [CommMonoid B] (φ : A → B) (h0 : φ 0 = 1)
    (hadd : ∀ x y, φ (x + y) = φ x * φ y) (s : Finset J) (g : J → A) : φ (∑ i ∈ s, g i) = ∏ i ∈ s, φ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, hadd, ih]

theorem exists_ringHom {R : Type} [CommRing R] {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) {n : ℕ} (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R) {k : Type} [Field k] (f : R →+* k)
    (hf : Function.Injective f) {X : Over S} (T : (Fin n → k) → (X ⟶ G)) (Tinj : Function.Injective T)
    (Tadd : ∀ c c', T (c + c') = T c * T c')
    (Tact : ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c)) :
    ∃ Mr : O →+* Matrix (Fin n) (Fin n) R, ∀ x, Mr x = M (a.act x) := by
  have key : ∀ P Q : Matrix (Fin n) (Fin n) R, (∀ c, T ((P.map f) *ᵥ c) = T ((Q.map f) *ᵥ c)) → P = Q := by
    intro P Q h
    apply Matrix.map_injective hf
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun c => by simpa [Matrix.toLin'_apply] using Tinj (h c)
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have act0 : a.act 0 = 1 := by simpa using a.add 0 0
  refine ⟨{ toFun := fun x => M (a.act x), map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun _ => rfl⟩
  · apply key; intro c
    rw [← Tact _ (a.hom 1), a.one]
    simp
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x * y)), mul_comm x y, a.mul, ← Category.assoc, Tact _ (a.hom y), Tact _ (a.hom x),
      Matrix.mulVec_mulVec, ← Matrix.map_mul]
  · apply key; intro c
    rw [← Tact _ (a.hom 0), act0, comp_one]
    simp [T0]
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x + y)), a.add, comp_mul, Tact _ (a.hom x), Tact _ (a.hom y), ← Tadd, Matrix.map_add _ (map_add f),
      Matrix.add_mulVec]

theorem finrank_zero (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) (F : Type) [Field F] [NumberField F] (a : OAct (𝓞 F) G) (Ω : Type) [Field Ω] [CharZero Ω]
    [IsAlgClosed Ω] (f : W →+* Ω) (hf : Function.Injective f) (σ : 𝓞 F →+* Ω) (h0 : LieMult a (spMap f) σ 0)
    (E : TorusExtension (GlobalTheory.SS.spFibre G)) : (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 := by
  classical
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  haveI : IsCommMonObj G := hG.comm
  obtain ⟨n, M, -, hT⟩ := GlobalTheory.T.exists_lie_coordinates_on_field_fibres_local_ring W G hG.smooth
  obtain ⟨T, Tinj, Trange, Tadd, Tsc, Tact⟩ := hT Ω f
  obtain ⟨Mr, hMr⟩ := exists_ringHom a M f hf T Tinj Tadd Tact
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have hno : ∀ c : Fin n → Ω, (∀ x, ((Mr x).map f).mulVec c = σ x • c) → c = 0 := by
    intro c hc
    have hE : IsLieEigen a (spMap f) σ (T c) := by
      refine ⟨(Trange (T c)).2 ⟨c, rfl⟩, fun x => ?_⟩
      rw [Tact _ (a.hom x), ← hMr, hc, Tsc]
    exact Tinj ((eq_one_of_lieMult_zero a _ σ h0 _ hE).trans T0.symm)
  let b := Module.Free.chooseBasis ℤ (𝓞 F)
  obtain ⟨w, ⟨i0, hu⟩, hsum⟩ := GlobalTheory.T.exists_primitive_annihilator' F W Ω f hf n Mr σ hno _ b
  obtain ⟨ρ, U, Uinj, Ufst, Uadd, Usc, Uact⟩ := GlobalTheory.T.toric_part_fibre_lie_algebra_characters (Sp W) G (𝓞 F) a.act a.hom a.one a.mul a.add
    (ResidueField W) (spMap (residue W)) E
  obtain ⟨T', -, T'range, T'add, T'sc, T'act⟩ := hT (ResidueField W) (residue W)
  have T'0 : T' 0 = 1 := by simpa using T'add 0 0
  have U0 : U 0 = 1 := by simpa using Uadd 0 0
  refine GlobalTheory.T.finrank_eq_zero_of_dual_killed_by_tensor F E.X ρ (ResidueField W) _ b (fun i => residue W (w i)) ?_ ?_
  · intro h
    exact (residue_ne_zero_iff_isUnit _).2 hu (congrFun h i0)
  · intro l χ
    obtain ⟨c, hc⟩ := (T'range (U l)).1 (Ufst l)
    have step : ∀ i, U ((AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) =
        T' (residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c)) := by
      intro i
      have e : U (l.comp (ρ (b i)).toAddMonoidHom) = T' ((Mr (b i)).map (residue W) *ᵥ c) := by
        rw [← Uact, ← hc, T'act _ (a.hom _), hMr]
      apply Over.OverMorphism.ext
      rw [Usc, T'sc, e]
    have hv : ∑ i, residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c) = 0 := by
      have := congrArg (fun P => ((residue W).mapMatrix P) *ᵥ c) hsum
      have hsm : ∀ i, (w i • Mr (b i)).map (residue W) = residue W (w i) • (Mr (b i)).map (residue W) := by
        intro i; ext; simp
      simpa [map_sum, Matrix.sum_mulVec, hsm, Matrix.smul_mulVec] using this
    have hL : (∑ i, (AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) = 0 := by
      apply Uinj
      rw [prod_of_add U U0 Uadd, U0, Finset.prod_congr rfl (fun i _ => step i), ← prod_of_add T' T'0 T'add, hv, T'0]
    have := congrArg (fun m => m χ) hL
    simpa using this

theorem potGood_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA F _ _ act Ω _ _ g σ hL
  obtain ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, hsemi, ⟨E⟩⟩ :=
    GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus V K A hA
  refine ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, ?_⟩
  have hAL := isGrpPullback_pullback A (spMap (algebraMap K L))
  obtain ⟨actL, ⟨h1, h2, h3, h4⟩, hLc⟩ := GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes _ _ (spMap (algebraMap K L)) A
    ((Over.pullback (spMap (algebraMap K L))).obj A) _ hAL (𝓞 F) act.act act.hom act.one act.mul act.add
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L A G hM _ _ hAL
  obtain ⟨actG, ⟨g1, g2, g3, g4⟩, hGc⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G _ φ hsemi hφ (𝓞 F) actL h1 h2 h3 h4
  let aL : OAct (𝓞 F) ((Over.pullback (spMap (algebraMap K L))).obj A) := ⟨actL, h1, h2, h3, h4⟩
  let aG : OAct (𝓞 F) G := ⟨actG, g1, g2, g3, g4⟩
  obtain ⟨g', hg'⟩ := lift_ext V K W L Ω hc hfin g
  have e1 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ A _ _ (pullback.fst _ _) act aL hAL hLc Ω (spMap g') σ 0
  have hx : spMap g' ≫ spMap (algebraMap K L) = spMap g := by rw [← hg', spMap_comp]
  have e2 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ G _ _ φ aG aL hφ hGc Ω (spMap g') σ 0
  have hG0 : LieMult aG (spMap (g'.comp (algebraMap W L))) σ 0 := by
    rw [spMap_comp]
    exact e2.1 (e1.2 (hx ▸ hL))
  haveI : CharZero Ω := charZero_of_injective_ringHom g.injective
  have hinj : Function.Injective (g'.comp (algebraMap W L)) :=
    g'.injective.comp (IsFractionRing.injective W L)
  exact GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus W L G hsemi (proper_pull A G hM hA) E
    (finrank_zero W G hsemi F aG Ω _ hinj σ hG0 E)

end GlobalTheory.PotGoodLie
