import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.FinitePartExtensionCore
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGenericStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.StightBad
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroupStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDividesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPullbackCorrespondenceStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpanStatement
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualTopTwoNeTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGrpObjOfFlatClosed
import Development.WeilBound.CoreStatements.HodgeTatePoints.MhQuot
import Development.WeilBound.CoreStatements.HodgeTatePoints.MhTorusA
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfSub
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharactersStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDenOfOpen
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExtTensor
import Development.WeilBound.CoreStatements.HodgeTatePoints.MiTors
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
import Development.WeilBound.CoreStatements.HodgeTatePoints.MjBase
import Development.WeilBound.CoreStatements.HodgeTatePoints.ResFiniteOpenBtOrder
import Development.WeilBound.CoreStatements.HodgeTatePoints.BtOrderOfPoints
import Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfPowMul
import Development.WeilBound.CoreStatements.HodgeTatePoints.IsAbFactorTens
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfMain
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralClosureFiniteLocalCompleteMixedCharStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtensionSplitSpecialFibrePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNZOfPolAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsIntegrallyClosedOfDenom
import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenGen

namespace PositivityTheory.Xgn.TightHopfOrder

section Orders
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct PositivityTheory.HtPt PositivityTheory.HtPt.Mj

theorem split_prod : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H C : Type) [CommGroup H] [CommGroup C] (ι : H →* T) (κ : C →* T), Function.Bijective (ι.coprod κ) → ∀ A : Subalgebra R (H → R), IsHopfOrder A → ∃ e : A ⊗[R] (C → R) ≃ₐ[R] indOrder ι A, ∀ (a : A) (c : C → R) (h : H) (k : C), (e (a ⊗ₜ c)).1 (ι h * κ k) = a.1 h * c k := by
  intro R _ _ T _ _ H C _ _ ι κ hb A hA
  have := hA.finite
  have := hA.projective
  let E : H × C ≃ T := Equiv.ofBijective _ hb
  have hE : ∀ h k, E (h, k) = ι h * κ k := fun _ _ => rfl
  obtain ⟨e, he⟩ := exists_tensor_equiv A (⊤ : Subalgebra R (C → R)) E (indOrder ι A) fun f => by
    constructor
    · intro hf
      refine mem_pspan_of (fun k => ?_) fun _ => Algebra.mem_top
      simpa only [hE, mul_comm] using hf (κ k)
    · intro hf t
      obtain ⟨⟨h, k⟩, rfl⟩ := E.surjective t
      have := Twhopf.translate_mem R H A hA _ (slice_mem hf k) h
      simpa only [hE, map_mul, mul_right_comm] using this
  exact ⟨(Algebra.TensorProduct.congr AlgEquiv.refl Subalgebra.topEquiv.symm).trans e,
    fun a c h k => he a (Subalgebra.topEquiv.symm c) h k⟩

section
variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

theorem char_mem_muOrder (χ : T →* Rˣ) : (fun t => ((χ t : Rˣ) : R)) ∈ muOrder R T :=
  Algebra.subset_adjoin ⟨χ, rfl⟩

theorem muOrder_eq_span : Subalgebra.toSubmodule (muOrder R T) =
    Submodule.span R (Set.range fun (χ : T →* Rˣ) (t : T) => ((χ t : Rˣ) : R)) := by
  refine le_antisymm (fun f hf => ?_) (Submodule.span_le.2 (by rintro _ ⟨χ, rfl⟩; exact char_mem_muOrder χ))
  let S : Submonoid (T → R) :=
    { carrier := {f | ∃ χ : T →* Rˣ, f = fun t => ((χ t : Rˣ) : R)}
      one_mem' := ⟨1, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨χ, rfl⟩ ⟨ψ, rfl⟩
        exact ⟨χ * ψ, rfl⟩ }
  have h := Algebra.adjoin_eq_span R (S : Set (T → R))
  rw [Submonoid.closure_eq] at h
  have h2 : f ∈ Submodule.span R (S : Set (T → R)) := h ▸ hf
  exact Submodule.span_mono (by rintro _ ⟨χ, rfl⟩; exact ⟨χ, rfl⟩) h2

theorem muOrder_induction (N : Submodule R (T → R)) (h : ∀ χ : T →* Rˣ, (fun t => ((χ t : Rˣ) : R)) ∈ N)
    {f : T → R} (hf : f ∈ muOrder R T) : f ∈ N := by
  have : f ∈ Subalgebra.toSubmodule (muOrder R T) := hf
  rw [muOrder_eq_span] at this
  exact Submodule.span_le.2 (by rintro _ ⟨χ, rfl⟩; exact h χ) this

end

theorem pull_mu_mem {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {T M : Type} [CommGroup T]
    [Finite T] [CommGroup M] (p : T →* M) {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) {a : M → R}
    (ha : a ∈ muOrder R M) : (fun t => a (p t)) ∈ A :=
  muOrder_induction ((Subalgebra.toSubmodule A).comap (LinearMap.funLeft R R p))
    (fun χ => char_mem_hopfOrder R T A hA (χ.comp p)) ha

theorem split_multiplicative_hopf_order {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {T M B : Type} [CommGroup T]
    [Finite T] [CommGroup M] [CommGroup B] {ι : M →* T} {κ : B →* T} (p : T →* M) (q : T →* B)
    (h : ∀ t, ι (p t) * κ (q t) = t) {A : Subalgebra R (T → R)} (hA : IsHopfOrder A)
    (hmu : resOrder ι A = muOrder R M) :
    (∀ f ∈ A, (fun t => f (κ (q t))) ∈ A) ∧
      ∀ f ∈ A, (fun z : M × B => f (ι z.1 * κ z.2)) ∈ pspan (muOrder R M) (resOrder κ A) := by
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · have := pspan_comp (Subalgebra.toSubmodule A) (fun t => (t, (ι (p t))⁻¹))
      (fun a ha b hb => A.mul_mem ha (pull_mu_mem p hA (hmu ▸ res_mem ι (hA.inv b hb)))) (hA.comul f hf)
    rw [Subalgebra.mem_toSubmodule] at this
    convert this using 3 with t
    rw [eq_mul_inv_iff_mul_eq, mul_comm, h]
  · exact pspan_comp _ (fun z : M × B => (ι z.1, κ z.2))
      (fun a ha b hb => mul_mem_pspan (hmu ▸ res_mem ι ha) (res_mem κ hb)) (hA.comul f hf)

theorem split_mu : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsIntegrallyClosed R] (M B : Type) [CommGroup M] [CommGroup B] (ι : M →* T) (κ : B →* T), Function.Bijective (ι.coprod κ) → ∀ A : Subalgebra R (T → R), IsHopfOrder A → resOrder ι A = muOrder R M → IsHopfOrder (resOrder ι A) ∧ IsHopfOrder (resOrder κ A) ∧ (∀ π : T →* B, π.comp ι = 1 → π.comp κ = MonoidHom.id B → quotOrder π A = resOrder κ A) ∧ ∃ e : muOrder R M ⊗[R] resOrder κ A ≃ₐ[R] A, ∀ (a : muOrder R M) (b : resOrder κ A) (m : M) (k : B), (e (a ⊗ₜ b)).1 (ι m * κ k) = a.1 m * b.1 k := by
  intro R _ _ T _ _ _ M B _ _ ι κ hb A hA hmu
  let E : M × B ≃* T := MulEquiv.ofBijective _ hb
  have hE : ∀ m k, E (m, k) = ι m * κ k := fun _ _ => rfl
  let p : T →* M := (MonoidHom.fst M B).comp E.symm.toMonoidHom
  let q : T →* B := (MonoidHom.snd M B).comp E.symm.toMonoidHom
  have h : ∀ t, ι (p t) * κ (q t) = t := fun t => E.apply_symm_apply t
  have hp : ∀ m k, p (ι m * κ k) = m := fun m k => congrArg Prod.fst (E.symm_apply_apply (m, k))
  have hq : ∀ m k, q (ι m * κ k) = k := fun m k => congrArg Prod.snd (E.symm_apply_apply (m, k))
  have hpι : ∀ m, p (ι m) = m := fun m => by simpa using hp m 1
  have hqκ : ∀ k, q (κ k) = k := fun k => by simpa using hq 1 k
  obtain ⟨h1, h2⟩ := split_multiplicative_hopf_order p q h hA hmu
  have hM : IsHopfOrder (resOrder ι A) :=
    res_hopf_of_section (Function.LeftInverse.injective hpι) hA (LinearMap.funLeft R R p)
      (fun f hf => pull_mu_mem p hA (hmu ▸ res_mem ι hf)) fun g m => congrArg g (hpι m)
  refine ⟨hM, res_hopf_of_section (Function.LeftInverse.injective hqκ) hA (LinearMap.funLeft R R q) h1
    fun g k => congrArg g (hqκ k), fun π hπι hπκ => ?_, ?_⟩
  · have : π = q := by
      ext t
      have e1 : π (ι (p t)) = 1 := DFunLike.congr_fun hπι _
      have e2 : π (κ (q t)) = q t := DFunLike.congr_fun hπκ _
      rw [← e2, ← one_mul (π (κ _)), ← e1, ← map_mul, h]
    subst this
    ext g
    refine ⟨fun hg => ⟨_, mem_quotOrder.1 hg, funext fun k => congrArg g (hqκ k)⟩, ?_⟩
    rintro ⟨f, hf, rfl⟩
    exact h1 f hf
  · rw [hmu] at hM
    have := hM.finite
    have := hM.projective
    refine exists_tensor_equiv (muOrder R M) (resOrder κ A) E.toEquiv A fun f => ⟨h2 f, fun hf => ?_⟩
    have := pspan_comp (Subalgebra.toSubmodule A) (fun t => (p t, q t)) (by
      rintro a ha _ ⟨b, hb, rfl⟩
      exact A.mul_mem (pull_mu_mem p hA ha) (h1 b hb)) hf
    rw [Subalgebra.mem_toSubmodule] at this
    convert this using 2 with t
    exact congrArg f (h t).symm

end Orders

section FinitePart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi PositivityTheory.HtPt PositivityTheory.HtPt.Mh

theorem sub_qf : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∃ (H : Subgroup T) (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G), (∀ t, t ∈ H ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) ∧ IsMonHom u ∧ IsOpenImmersion u.left ∧ IsClosedImmersion u.left ∧ Set.range u.left = (U : Set Γ.G.left) ∧ IsFinite Γf.G.hom ∧ ∀ h : H, Γf.pt h ≫ u = Γ.pt h := by
  intro R _ _ T _ _ Γ U hU
  have := Γ.flat
  have := Γ.quasiFinite
  have := Γ.separated
  have := Γ.finPres
  have := Γ.gen_reduced
  have hfin := hU.finite
  have hqc : QuasiCompact (U.ι ≫ Γ.G.hom) :=
    quasiCompact_iff_forall_isAffineOpen.mpr fun _ h => (h.preimage _).isCompact
  let W : Over (Spec (CommRingCat.of R)) := Over.mk (U.ι ≫ Γ.G.hom)
  let u : W ⟶ Γ.G := Over.homMk U.ι rfl
  have : Mono u.left := inferInstanceAs (Mono U.ι)
  have : Mono u := Over.mono_of_mono_left _
  have hmem : ∀ z, u.left z ∈ U := fun z => z.2
  have hl : ∀ {Y : Over (Spec (CommRingCat.of R))} (x : Y ⟶ Γ.G), (∀ z, x.left z ∈ U) → ∃ l : Y ⟶ W, l ≫ u = x := by
    intro Y x hx
    have hr : Set.range x.left ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨_, hx z⟩, rfl⟩
    have e := IsOpenImmersion.lift_fac U.ι x.left hr
    exact ⟨Over.homMk (IsOpenImmersion.lift U.ι x.left hr) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Γ.G.hom) e).trans (Over.w x))),
      Over.OverMorphism.ext e⟩
  obtain ⟨o, ho⟩ := hl η[Γ.G] hU.one
  obtain ⟨m, hm⟩ := hl ((fst W W ≫ u) * (snd W W ≫ u)) (hU.mul _ _ _ (fun z => hmem _) (fun z => hmem _))
  obtain ⟨n, hn⟩ := hl u⁻¹ (hU.inv _ _ hmem)
  obtain ⟨grp, hu⟩ := GlobalTheory.exists_grpObj_of_mono u o m n ho (by rw [hm, Hom.mul_def, ← lift_fst_comp_snd_comp])
    (by rw [hn, Hom.inv_def])
  have comm : IsCommMonObj W := ⟨by
    rw [← cancel_mono u, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  choose p hp using fun h : SubOrder.subH Γ hU => hl (Γ.pt h) ((SubOrder.top_le_iff_mem _ _).1 h.2)
  let pt : SubOrder.subH Γ hU →* (genPt R ⟶ W) := MonoidHom.mk' p fun s t => by
    rw [← cancel_mono u, MonObj.mul_comp, hp, hp, hp, ← map_mul]
    rfl
  have hpl : ∀ h x, U.ι ((p h).left x) = (Γ.pt h).left x := fun h x => by
    rw [← hp h]
    rfl
  have hred : IsReduced (pullback W.hom (genPt R).hom) := by
    have : IsOpenImmersion (pullback.map W.hom (genPt R).hom Γ.G.hom (genPt R).hom U.ι (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) := inferInstance
    exact isReduced_of_isOpenImmersion (pullback.map W.hom (genPt R).hom Γ.G.hom (genPt R).hom U.ι (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm))
  have hcl : IsClosedImmersion U.ι := by
    have : IsFinite U.ι := IsFinite.of_comp _ Γ.G.hom
    exact (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨this, inferInstance⟩
  refine ⟨SubOrder.subH Γ hU,
    { G := W
      flat := inferInstanceAs (Flat (U.ι ≫ Γ.G.hom))
      quasiFinite := inferInstanceAs (LocallyQuasiFinite (U.ι ≫ Γ.G.hom))
      separated := inferInstanceAs (IsSeparated (U.ι ≫ Γ.G.hom))
      quasiCompact := hqc
      finPres := inferInstanceAs (LocallyOfFinitePresentation (U.ι ≫ Γ.G.hom))
      pt := pt
      pt_inj := fun s t x y h => Subtype.ext (Γ.pt_inj _ _ x y
        ((hpl s x).symm.trans ((congrArg U.ι h).trans (hpl t y))))
      pt_onto := fun g hg => ?_
      gen_reduced := hred }, u, fun t => Iff.rfl, hu, (inferInstance : IsOpenImmersion U.ι), hcl,
    U.range_ι, hfin, hp⟩
  obtain ⟨t, x, hx⟩ := Γ.pt_onto (U.ι g) hg
  have ht : t ∈ SubOrder.subH Γ hU := (SubOrder.top_le_iff_mem _ _).2 fun z => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z x]
    exact hx ▸ hmem g
  exact ⟨⟨t, ht⟩, x, U.ι.isOpenEmbedding.injective ((hpl ⟨t, ht⟩ x).trans hx)⟩

theorem mu_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (i : Γ.G.left ⟶ (splitTorus (Spec (CommRingCat.of R)) X).left), 1 ≤ N → Γ.IsTorsionAlong (splitTorus (Spec (CommRingCat.of R)) X) (𝟙 _) N i → IsFinite Γ.G.hom ∧ Γ.btOrder ⊤ = muOrder R T := by
  intro R _ _ _ T _ _ Γ X _ _ _ N i hN hi
  have hio : i ≫ (splitTorus (Spec (CommRingCat.of R)) X).hom = Γ.G.hom := hi.isOver.trans (Category.comp_id _)
  let up : ∀ {Y : Over (Spec (CommRingCat.of R))} (_ : Y ⟶ Γ.G),
      Over.mk (Y.hom ≫ 𝟙 _) ⟶ splitTorus (Spec (CommRingCat.of R)) X := fun {Y} y =>
    Over.homMk (y.left ≫ i) (by rw [Category.assoc, hio, Over.w y]; exact (Category.comp_id _).symm)
  have hc : ∀ x, chi i x ^ N = 1 := fun x => by
    have h := (pow_eq_one_iff_chi _ N).1 ((hi.kernel Γ.G (up (𝟙 _))).2 ⟨𝟙 _, rfl⟩) x
    have e : (up (𝟙 Γ.G)).left = i := Category.id_comp i
    exact e ▸ h
  let P : Subgroup (Multiplicative X) := (powMonoidHom N : Multiplicative X →* Multiplicative X).range
  let Q := Multiplicative X ⧸ P
  have hQN : ∀ q : Q, q ^ N = 1 := by
    rintro ⟨x⟩
    exact (QuotientGroup.eq_one_iff (N := P) (x ^ N)).2 ⟨x, rfl⟩
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 inferInstance
  have : Finite Q := CommGroup.finite_of_fg_isMulTorsion Q fun q => isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, hQN q⟩
  let cq : Q →* Γ(Γ.G.left, ⊤) := QuotientGroup.lift P (chi i) (by
    rintro _ ⟨x, rfl⟩
    exact (map_pow (chi i) x N).trans (hc x))
  let B := MonoidAlgebra R Q
  obtain ⟨j, hj⟩ := exists_pb (A := B) (MonoidAlgebra.liftNCRingHom (pb Γ.G.hom) cq fun _ _ => Commute.all _ _)
  have hj1 : ∀ x : Multiplicative X, pb j (MonoidAlgebra.single (QuotientGroup.mk x) 1) = chi i x := fun x => by
    rw [hj, MonoidAlgebra.liftNCRingHom_single, map_one, _root_.one_mul]
    rfl
  have hj2 : ∀ r : R, pb j (algebraMap R B r) = pb Γ.G.hom r := fun r => by
    rw [hj]
    exact (MonoidAlgebra.liftNCRingHom_single _ _ _ 1 r).trans (by rw [map_one, _root_.mul_one])
  have hjo : j ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = Γ.G.hom := pb_ext fun r => by rw [pb_spec, hj2]
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  let c₀ : Multiplicative X →* Γ(Spec (CommRingCat.of B), ⊤) :=
    ((pb (𝟙 (Spec (CommRingCat.of B)))).toMonoidHom.comp (MonoidAlgebra.of R Q)).comp (QuotientGroup.mk' P)
  obtain ⟨g, hg⟩ := exists_chi (Over.mk (Y.hom ≫ 𝟙 _)) c₀
  obtain ⟨y, hy⟩ := (hi.kernel Y g).1 ((pow_eq_one_iff_chi g N).2 fun x => by
    rw [hg]
    change ((pb (𝟙 (Spec (CommRingCat.of B)))).toMonoidHom.comp (MonoidAlgebra.of R Q)) (QuotientGroup.mk x) ^ N = 1
    rw [← map_pow, hQN, map_one])
  have h1 : y.left ≫ j = 𝟙 (Spec (CommRingCat.of B)) := by
    refine pb_ext (RingHom.congr_fun (MonoidAlgebra.ringHom_ext (fun r => ?_) ?_))
    · change pb (y.left ≫ j) (algebraMap R B r) = pb (𝟙 _) (algebraMap R B r)
      rw [← pb_spec, ← pb_spec, Category.assoc, hjo, Category.id_comp]
      exact congrArg (fun k => pb k r) (Over.w y)
    · rintro ⟨x⟩
      exact (pb_comp _ _ _).trans ((congrArg y.left.appTop (hj1 x)).trans ((chi_comp _ _ _).symm.trans
        ((congrArg (fun k => chi k x) hy).trans (hg x))))
  have h2 : j ≫ y.left = 𝟙 Γ.G.left := by
    let j' : Γ.G ⟶ Y := Over.homMk j hjo
    refine congrArg (·.left) (hi.inj Γ.G (j' ≫ y) (𝟙 _) (chi_ext ?_ fun x => ?_))
    · rw [Category.assoc, Category.assoc, hio, Over.w, Over.w]
    · have e : (j' ≫ y).left ≫ i = j ≫ g.left := (Category.assoc _ _ _).trans (congrArg (j ≫ ·) hy)
      have e' : (𝟙 Γ.G : Γ.G ⟶ Γ.G).left ≫ i = i := Category.id_comp i
      rw [e, e', ← hj1]
      refine (chi_comp _ _ _).trans ((congrArg j.appTop (hg x)).trans ((pb_comp j (𝟙 _) _).symm.trans ?_))
      rw [Category.comp_id]
      rfl
  have : IsIso j := ⟨y.left, h2, h1⟩
  have hfin : IsFinite Γ.G.hom := by
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.2 inferInstance
    rw [← hjo]
    infer_instance
  refine ⟨hfin, le_antisymm (fun f hf => ?_) (Algebra.adjoin_le ?_)⟩
  · have inj := IsFractionRing.injective R (FractionRing R)
    have hχ : ∀ x : Multiplicative X, ∃ χ : T →* Rˣ, ∀ t,
        val (Γ.pt t).left (chi i x) = algebraMap R (FractionRing R) (χ t) := by
      intro x
      have hr : ∀ t, ∃ r : R, algebraMap R (FractionRing R) r = val (Γ.pt t).left (chi i x) := fun t =>
        IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (n := N) hN (by
          rw [← map_pow, hc, map_one]
          exact isIntegral_one)
      choose r hr using hr
      have hv : ∀ t, val (Γ.pt t).left (chi i x) = val (𝟙 _) (chi ((Γ.pt t).left ≫ i) x) := fun t => by
        rw [chi_comp, ← val_comp, Category.id_comp]
      have hm : ∀ s t, r (s * t) = r s * r t := fun s t => inj (by
        rw [map_mul, hr, hr, hr, hv, hv, hv, ← map_mul, map_mul Γ.pt,
          ← hi.mul _ (Γ.pt s) (Γ.pt t) (up (Γ.pt s)) (up (Γ.pt t)) rfl rfl]
        exact congrArg (val (𝟙 _)) (chi_mul (up (Γ.pt s)) (up (Γ.pt t)) x))
      have hu : ∀ t, IsUnit (r t) := fun t => IsUnit.of_pow_eq_one (n := N) (inj (by
        rw [map_pow, hr, ← map_pow, hc, map_one, map_one])) (by omega)
      exact ⟨MonoidHom.mk' (fun t => (hu t).unit) fun s t => Units.ext (hm s t), fun t => (hr t).symm⟩
    have key : ∀ b : B, ∃ f' ∈ muOrder R T, ∀ t,
        val (Γ.pt t).left (pb j b) = algebraMap R (FractionRing R) (f' t) := by
      intro b
      induction b using MonoidAlgebra.induction_on with
      | of q =>
        obtain ⟨x⟩ := q
        obtain ⟨χ, hχ⟩ := hχ x
        exact ⟨_, Algebra.subset_adjoin ⟨χ, rfl⟩, fun t => (congrArg _ (hj1 x)).trans (hχ t)⟩
      | add a b ha hb =>
        obtain ⟨f₁, h₁, h₁'⟩ := ha
        obtain ⟨f₂, h₂, h₂'⟩ := hb
        exact ⟨f₁ + f₂, add_mem h₁ h₂, fun t => by rw [map_add, map_add, h₁', h₂', Pi.add_apply, map_add]⟩
      | smul r a ha =>
        obtain ⟨f₁, h₁, h₁'⟩ := ha
        refine ⟨r • f₁, Subalgebra.smul_mem _ h₁ r, fun t => ?_⟩
        rw [Algebra.smul_def, map_mul, map_mul, h₁', hj2, val_const, ← map_mul]
        rfl
    obtain ⟨s, hs⟩ := (mem_top_iff Γ f).1 hf 1
    obtain ⟨f', hf', h'⟩ := key (val y.left s)
    have e : pb j (val y.left s) = s := by
      have e1 : pb (𝟙 (Spec (CommRingCat.of B))) (val y.left s) = y.left.appTop s :=
        val_id_injective ((val_pb_id _).trans ((congrArg (fun k => val k s) (Category.id_comp y.left).symm).trans
          (val_comp _ _ _)))
      rw [← Category.comp_id j, pb_comp, e1]
      exact (congrArg (fun φ => φ.hom s) (Scheme.Hom.comp_appTop j y.left)).symm.trans (by rw [h2])
    convert hf' using 1
    funext t
    have := inj ((hs t).symm.trans (e ▸ h' t))
    rwa [_root_.one_mul] at this
  · rintro _ ⟨χ, rfl⟩
    refine GlobalTheory.T.hopf_order_contains_characters R T _ (Htat.bt_sub_hopf R T Γ ⊤ ⟨?_, fun _ => trivial, fun _ _ _ _ _ _ => trivial,
      fun _ _ _ _ => trivial⟩) χ
    rw [← Scheme.topIso_hom]
    infer_instance

end FinitePart

section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open Limits MonoidalCategory CartesianMonoidalCategory MonObj

section Ring
open IsLocalRing

theorem exists_complete_normal (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [CharZero V]
    (p : ℕ) (hp : p.Prime) (hpV : (p : V) ∈ maximalIdeal V) [IsAdicComplete (Ideal.span {(p : V)}) V]
    (hnil : maximalIdeal V ≤ (Ideal.span {(p : V)}).radical)
    (R₀ : Type) [CommRing R₀] [IsNoetherianRing R₀] (f : R₀ →+* V) (s : Finset V) :
    ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (g : R₀ →+* D) (h : D →+* V),
      IsNoetherianRing D ∧ IsIntegrallyClosed D ∧ IsAdicComplete (maximalIdeal D) D ∧ Function.Injective h ∧
      IsLocalHom h ∧ h.comp g = f ∧ ∀ a ∈ s, a ∈ Set.range h := by
  classical
  let R₁ := MvPolynomial s R₀
  let f₁ : R₁ →+* V := MvPolynomial.eval₂Hom f fun a => a.1
  let P : Ideal R₁ := (maximalIdeal V).comap f₁
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  let R₂ := Localization.AtPrime P
  have hu : ∀ y : P.primeCompl, IsUnit (f₁ y) := fun y => by
    by_contra hy
    exact y.2 hy
  let f₂ : R₂ →+* V := IsLocalization.lift hu
  have hf₂ : f₂.comp (algebraMap R₁ R₂) = f₁ := IsLocalization.lift_comp hu
  have hm₂ : (maximalIdeal R₂).map f₂ ≤ maximalIdeal V := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hf₂]
    exact Ideal.map_comap_le
  haveI l₂ : IsLocalHom f₂ := ((IsLocalRing.local_hom_TFAE f₂).out 2 0).1 hm₂
  have hfg : (maximalIdeal R₂).FG := IsNoetherian.noetherian _
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (hm₂.trans hnil) (hfg.map f₂)
  let R₃ := AdicCompletion (maximalIdeal R₂) R₂
  haveI : IsNoetherianRing R₃ := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian R₂ _
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.exists_extend_adicCompletion f₂ (maximalIdeal R₂) _ hk
  haveI l₃ : IsLocalHom ψ := @GlobalTheory.isLocalHom_of_extend_adicCompletion _ _ _ _ _ _ hfg ψ (hψ ▸ l₂)
  let S₀ : Subring V := ψ.range
  letI : Algebra R₃ S₀ := ψ.rangeRestrict.toAlgebra
  haveI : Module.Finite R₃ S₀ := RingHom.Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  haveI : IsLocalRing S₀ := IsLocalRing.of_surjective' ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hN₀ : IsNoetherianRing S₀ := IsNoetherianRing.of_finite R₃ S₀
  have hc₀ : IsAdicComplete (maximalIdeal S₀) S₀ := GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R₃ S₀
  have l₀ : IsLocalHom S₀.subtype := ⟨by
    rintro ⟨_, a, rfl⟩ ha
    exact ((isUnit_map_iff ψ a).1 ha).map ψ.rangeRestrict⟩
  have hp₀ : (p : S₀) ∈ maximalIdeal S₀ := fun h => hpV (by simpa using h.map S₀.subtype)
  obtain ⟨hfin, hl, hN, hc⟩ := GlobalTheory.T.integralClosure_finite_local_complete_mixedChar S₀ p hp hp₀ hN₀ hc₀
  let D := integralClosure S₀ (FractionRing S₀)
  let K := FractionRing V
  have hi : Function.Injective ((algebraMap V K).comp S₀.subtype) :=
    (IsFractionRing.injective V K).comp Subtype.val_injective
  let j : FractionRing S₀ →+* K := IsFractionRing.lift hi
  have hj : ∀ a : S₀, j (algebraMap S₀ _ a) = algebraMap V K a := fun a => IsFractionRing.lift_algebraMap hi a
  have hmem : ∀ x : D, ∃ y : V, algebraMap V K y = j x := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.map_of_comp_eq S₀.subtype j (RingHom.ext fun a => (hj a).symm) x.2)
  choose h₀ hh₀ using hmem
  have hK := IsFractionRing.injective V K
  let h : D →+* V :=
    { toFun := h₀
      map_one' := hK (by simp [hh₀])
      map_mul' := fun a b => hK (by simp [hh₀])
      map_zero' := hK (by simp [hh₀])
      map_add' := fun a b => hK (by simp [hh₀]) }
  have hhS : ∀ a : S₀, h (algebraMap S₀ D a) = a := fun a => hK ((hh₀ _).trans (hj a))
  haveI : IsFractionRing D (FractionRing S₀) :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing S₀) (FractionRing S₀)
  refine ⟨D, inferInstance, inferInstance, hl,
    (algebraMap S₀ D).comp (ψ.rangeRestrict.comp ((algebraMap R₂ R₃).comp ((algebraMap R₁ R₂).comp MvPolynomial.C))),
    h, hN, (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing S₀)).2 inferInstance, hc, fun a b hab => ?_,
    GlobalTheory.Ex.UnifModel.isLocalHom_of_integral (V := S₀) h fun a ha => ?_, RingHom.ext fun a => ?_, fun a ha => ?_⟩
  · exact Subtype.ext (j.injective ((hh₀ a).symm.trans ((congrArg _ hab).trans (hh₀ b))))
  · rw [hhS]
    exact map_nonunit S₀.subtype a ha
  · refine (hhS _).trans ((RingHom.congr_fun hψ _).trans ((RingHom.congr_fun hf₂ _).trans ?_))
    exact MvPolynomial.eval₂Hom_C _ _ a
  · refine ⟨algebraMap S₀ D (ψ.rangeRestrict (algebraMap R₂ R₃ (algebraMap R₁ R₂ (MvPolynomial.X ⟨a, ha⟩)))), ?_⟩
    refine (hhS _).trans ((RingHom.congr_fun hψ _).trans ((RingHom.congr_fun hf₂ _).trans ?_))
    exact MvPolynomial.eval₂Hom_X' _ _ _

theorem isAlgClosed_residueField (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V]
    [IsAlgClosed (FractionRing V)] : IsAlgClosed (ResidueField V) := by
  refine IsAlgClosed.of_exists_root _ fun q₀ hp hi => ?_
  obtain ⟨q, hq, hd, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts q₀).2 (Polynomial.map_surjective (residue V) residue_surjective q₀)) hp
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero (FractionRing V) q
    (by rw [hd]; exact (Polynomial.degree_pos_of_irreducible hi).ne')
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 (show IsIntegral V z from ⟨q, hm, hz⟩)
  refine ⟨residue V y, ?_⟩
  have : q.eval y = 0 := IsFractionRing.injective V (FractionRing V)
    ((Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := FractionRing V) y q).symm.trans (hz.trans (map_zero _).symm))
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_hom, this, map_zero]

end Ring

section Unif
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.UU GlobalTheory.LN
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_unif {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [CharZero V] [IsAlgClosed (FractionRing V)]
    (p : ℕ) (hp : p.Prime) (hpV : (p : V) ∈ maximalIdeal V) [IsAdicComplete (Ideal.span {(p : V)}) V]
    (hnil : maximalIdeal V ≤ (Ideal.span {(p : V)}).radical)
    (R₀ : Type) [CommRing R₀] [IsNoetherianRing R₀] (f : R₀ →+* V) (hf : Function.Injective f)
    (Ω : Type) [Field Ω] [Algebra R₀ Ω] [IsFractionRing R₀ Ω] {X : Scheme.{0}} (t : SAB H X) (x : Sp R₀ ⟶ X)
    (hpol : PolAt t (spMap (algebraMap R₀ Ω) ≫ x)) :
    ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (g : R₀ →+* D) (h : D →+* V)
      (t' : SAB H (Sp D)) (φ : t'.G.left ⟶ t.G.left) (Dd : DegData D (maximalIdeal D)) (A : PolAV (Sp (FractionRing D))),
      IsNoetherianRing D ∧ IsIntegrallyClosed D ∧ IsAdicComplete (maximalIdeal D) D ∧ Function.Injective h ∧
      h.comp g = f ∧ IsGrpPullback t'.G t.G (spMap g ≫ x) φ ∧ Nonempty (UnifPre (maximalIdeal D) Dd A t'.G) := by
  classical
  haveI := isAlgClosed_residueField V
  obtain ⟨D₀, _, _, _, g₀, h₀, hN₀, -, -, -, l₀, e₀, -⟩ := exists_complete_normal V p hp hpV hnil R₀ f ∅
  obtain ⟨t₀, ⟨m₀⟩⟩ := Geo.Tor.exists_sab (spMap g₀ ≫ x) t
  obtain ⟨s, hs, hsp⟩ := GlobalTheory.Ex.UnifModel.exists_finite_split (ResidueField.map h₀) t₀.G t₀.semi
  choose r hr using residue_surjective (R := V)
  obtain ⟨R, _, _, _, g₁, h, hN, hic, hc, hi, l₁, e₁, hs₁⟩ :=
    exists_complete_normal V p hp hpV hnil D₀ h₀ (hs.toFinset.image r)
  haveI : IsLocalHom g₁ := @isLocalHom_of_comp _ _ _ _ _ _ g₁ h (e₁ ▸ l₀)
  obtain ⟨E₁, hE₁⟩ := hsp R g₁ (ResidueField.map h) (by rw [← ResidueField.map_comp]; congr 1) fun a ha => by
    obtain ⟨b, hb⟩ := hs₁ (r a) (Finset.mem_image.2 ⟨a, hs.mem_toFinset.2 ha, rfl⟩)
    exact ⟨residue R b, by rw [ResidueField.map_residue, hb, hr]⟩
  obtain ⟨t', ⟨m⟩⟩ := Geo.Tor.exists_sab (spMap (g₁.comp g₀) ≫ x) t
  have ec : spMap g₁ ≫ spMap g₀ = spMap (g₁.comp g₀) := GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl
  have hs' : GlobalTheory.LN.SplitOver t'.G (maximalIdeal R) := by
    obtain ⟨i, hi, -⟩ := grpPullback_iso
      (((isGrpPullback_pullback _ (spMap (residue R))).comp ((isGrpPullback_pullback t₀.G (spMap g₁)).comp
        m₀.cart)).congr (by rw [← Category.assoc (spMap g₁), ec]) rfl)
      ((isGrpPullback_pullback t'.G (spMap (residue R))).comp m.cart)
    have hE := isGt_of_iso i hE₁
    exact ⟨E₁, hE⟩
  have e : h.comp (g₁.comp g₀) = f := by rw [← RingHom.comp_assoc, e₁, e₀]
  have hg : Function.Injective (g₁.comp g₀) := Function.Injective.of_comp (f := h) (by
    rw [← RingHom.coe_comp, e]; exact hf)
  have j : Function.Injective ((algebraMap R (FractionRing R)).comp (g₁.comp g₀)) := (IsFractionRing.injective R _).comp hg
  let gm : Ω →+* FractionRing R := IsFractionRing.lift j
  have hpol' : PolAt t' (jK R) := GlobalTheory.SplitPoint.polAt_pullback m hpol _ (spMap gm) (by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm)
  have hA : admitted R (maximalIdeal R) := by
    refine ⟨⟨hN, inferInstance, hic, hc⟩, hc, h.charZero, inferInstance, ?_⟩
    letI := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h1 h2 E H R t' hpol'
  obtain ⟨P, hPL, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric h1 R A t'.G t'.semi gen hgen t'.PP t'.cub t'.sym
  have hσ : ∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0 := by
    rw [hPL]; exact GlobalTheory.T.exists_nonzero_section_of_polarised_generic_fibre E H R t' hpol'
  obtain ⟨Dd, U, -, -⟩ := GlobalTheory.T.semiabelian_generic_fibre_polarization_iso R hA t'.G P t'.semi (hPL ▸ GlobalTheory.LN.UnifPrime.hypW_of_triple t') hs' A gen hgen
    (hPL ▸ hL) hσ
  exact ⟨R, _, _, _, g₁.comp g₀, h, t', m.φ, Dd, A, hN, hic, hc, hi, e, m.cart, ⟨U.toUnifPre⟩⟩

end Unif

end

section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.BT
open GlobalTheory.CompanionTheory.Ar

section Groups

theorem exists_split (p : ℕ) [Fact p.Prime] {M T C : Type} [CommGroup M] [CommGroup T] [CommGroup C]
    (hT : ∀ t : T, t ^ p = 1) (j : M →* T) (π : T →* C) (hj : Function.Injective j) (hπ : Function.Surjective π)
    (hk : ∀ t, π t = 1 ↔ ∃ m, j m = t) : ∃ κ : C →* T, π.comp κ = MonoidHom.id C ∧ Function.Bijective (j.coprod κ) := by
  have hC : ∀ c : C, c ^ p = 1 := fun c => by
    obtain ⟨t, rfl⟩ := hπ c
    rw [← map_pow, hT, map_one]
  letI : Module (ZMod p) (Additive T) := AddCommGroup.zmodModule fun x => hT x.toMul
  letI : Module (ZMod p) (Additive C) := AddCommGroup.zmodModule fun x => hC x.toMul
  let L : Additive T →ₗ[ZMod p] Additive C := (MonoidHom.toAdditive π).toZModLinearMap p
  have hfree : Module.Free (ZMod p) (Additive C) := Module.Free.of_divisionRing (ZMod p) (Additive C)
  have hproj : Module.Projective (ZMod p) (Additive C) := @Module.Projective.of_free _ _ _ _ _ hfree
  obtain ⟨g, hg⟩ := @Module.projective_lifting_property _ _ _ _ _ _ _ _ _ _ _ hproj L LinearMap.id hπ
  let κ : C →* T := MonoidHom.toAdditive.symm g.toAddMonoidHom
  have hκ : ∀ c, π (κ c) = c := fun c => LinearMap.congr_fun hg (Additive.ofMul c)
  have h0 : ∀ m, π (j m) = 1 := fun m => (hk _).2 ⟨m, rfl⟩
  refine ⟨κ, MonoidHom.ext hκ, (injective_iff_map_eq_one _).2 fun z hz => ?_, fun t => ?_⟩
  · rw [MonoidHom.coprod_apply] at hz
    have h1 := congrArg π hz
    rw [map_mul, h0, hκ, _root_.one_mul, map_one] at h1
    rw [h1, map_one, _root_.mul_one] at hz
    exact Prod.ext (hj (hz.trans (map_one j).symm)) h1
  · obtain ⟨m, hm⟩ := (hk (t * (κ (π t))⁻¹)).1 (by rw [map_mul, map_inv, hκ, mul_inv_cancel])
    exact ⟨(m, π t), by rw [MonoidHom.coprod_apply, hm, inv_mul_cancel_right]⟩

theorem mem_iff_span {R A B H K T : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (φ : A → H → R) (ψ : B → K → R) (X : Subalgebra R (T → R)) (e : TensorProduct R A B ≃ₗ[R] X) (u : H × K → T)
    (hu : Function.Surjective u) (he : ∀ a b h k, (e (a ⊗ₜ b)).1 (u (h, k)) = φ a h * ψ b k) (f : T → R) :
    f ∈ X ↔ (fun z => f (u z)) ∈ Submodule.span R {F : H × K → R | ∃ a b, F = fun z => φ a z.1 * ψ b z.2} := by
  constructor
  · intro hf
    obtain ⟨x, hx⟩ := e.surjective ⟨f, hf⟩
    obtain rfl : f = (e x).1 := by rw [hx]
    clear hx hf
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a b => exact Submodule.subset_span ⟨a, b, funext fun z => he a b z.1 z.2⟩
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · intro hf
    have key : ∀ F ∈ Submodule.span R {F : H × K → R | ∃ a b, F = fun z => φ a z.1 * ψ b z.2},
        ∃ g ∈ X, F = fun z => g (u z) := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨a, b, rfl⟩ := hF
        exact ⟨_, (e (a ⊗ₜ b)).2, funext fun z => (he a b z.1 z.2).symm⟩
      | zero => exact ⟨0, zero_mem _, rfl⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨g, hg, rfl⟩ := h1
        obtain ⟨g', hg', rfl⟩ := h2
        exact ⟨g + g', add_mem hg hg', rfl⟩
      | smul c _ _ h1 =>
        obtain ⟨g, hg, rfl⟩ := h1
        exact ⟨c • g, X.smul_mem hg c, rfl⟩
    obtain ⟨g, hg, h⟩ := key _ hf
    obtain rfl : f = g := funext fun t => by
      obtain ⟨z, rfl⟩ := hu t
      exact congrFun h z
    exact hg

end Groups

section QF
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {T H : Type} [CommGroup T] [CommGroup H]

theorem pt_inj (Γ : QFGroup R T) : Function.Injective Γ.pt := fun s t h =>
  Γ.pt_inj s t default default (by rw [h])

theorem exists_pt (Γ : QFGroup R T) (κ : BT.genPt R ⟶ Γ.G) : ∃ t, Γ.pt t = κ := by
  obtain ⟨t, ht⟩ := GlobalTheory.T.torus_point_over_fraction_field R T Γ (FractionRing R) (RingHom.id _) κ.left (Over.w κ)
  refine ⟨t, Over.OverMorphism.ext (ht.trans ?_).symm⟩
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

theorem exists_map (Γ₁ : QFGroup R H) (Γ : QFGroup R T) (a : Γ₁.G ⟶ Γ.G) [IsMonHom a] :
    ∃ α : H →* T, ∀ h, Γ₁.pt h ≫ a = Γ.pt (α h) := by
  choose f hf using fun h => exists_pt Γ (Γ₁.pt h ≫ a)
  exact ⟨MonoidHom.mk' f fun x y => pt_inj Γ (by rw [map_mul, hf, hf, hf, map_mul, MonObj.mul_comp]),
    fun h => (hf h).symm⟩

theorem map_surjective (Γ₁ : QFGroup R H) (Γ : QFGroup R T) (a : Γ₁.G ⟶ Γ.G) (α : H →* T)
    (hα : ∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) (hs : Surjective a.left) : Function.Surjective α := by
  intro c
  let x₀ : Spec (CommRingCat.of (FractionRing R)) := default
  obtain ⟨w, hw⟩ := hs.surj ((Γ.pt c).left x₀)
  have hg : (Γ₁.G.hom w).asIdeal = ⊥ := by
    have e : Γ₁.G.hom w = (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) x₀ := by
      rw [← Over.w a, Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, Over.w (Γ.pt c)]
      rfl
    have hx₀ : x₀.asIdeal = ⊥ := (Ideal.eq_bot_or_top x₀.asIdeal).resolve_right x₀.isPrime.ne_top
    rw [e]
    change Ideal.comap (algebraMap R (FractionRing R)) x₀.asIdeal = ⊥
    rw [hx₀]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
  obtain ⟨h, x, hx⟩ := Γ₁.pt_onto w hg
  refine ⟨h, Γ.pt_inj _ _ x x₀ ?_⟩
  rw [← hα, ← hw, ← hx]
  rfl

theorem btOrder_ind [IsIntegrallyClosed R] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hsub : Γ.IsFinOpenSub U)
    (H : Subgroup T) (hH : ∀ t, t ∈ H ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) :
    Γ.btOrder ⊤ = indOrder H.subtype (resOrder H.subtype (Γ.btOrder ⊤)) := by
  have htop := PositivityTheory.HtPt.Htat.bt_sub_eq_top R T Γ U hsub
  obtain ⟨H', A, hH', hA, hAf⟩ := PositivityTheory.HtPt.Twhopf.sub_order R T Γ U hsub
  obtain rfl : H = H' := Subgroup.ext fun t => (hH t).trans (hH' t).symm
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [PositivityTheory.HtPt.Twhopf.mem_order R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  rw [← htop, key, PositivityTheory.HtPt.Twhopf.res_ind H A hA]

end QF

section Struct
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem span_triple {R X Y Z : Type} [CommRing R] (A : Set (X × Y → R)) (S : Set (X × Y → R))
    (h : ∀ f, f ∈ A ↔ f ∈ Submodule.span R S) :
    Submodule.span R {F : (X × Y) × Z → R | ∃ (a : A) (c : Z → R), F = fun z => a.1 z.1 * c z.2} =
      Submodule.span R {F : (X × Y) × Z → R | ∃ a ∈ S, ∃ c : Z → R, F = fun z => a z.1 * c z.2} := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨⟨a, ha⟩, c, rfl⟩
    have ha' := (h a).1 ha
    change (fun z : (X × Y) × Z => a z.1 * c z.2) ∈ Submodule.span R _
    clear ha
    induction ha' using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span ⟨a, ha, c, rfl⟩
    | zero => convert Submodule.zero_mem _ using 1; ext; simp
    | add a b _ _ h1 h2 => convert Submodule.add_mem _ h1 h2 using 1; ext; simp [add_mul]
    | smul r a _ h1 => convert Submodule.smul_mem _ r h1 using 1; ext; simp [_root_.mul_assoc]
  · rintro _ ⟨a, ha, c, rfl⟩
    exact ⟨⟨a, (h a).2 (Submodule.subset_span ha)⟩, c, rfl⟩

theorem exists_struct (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    [IsIntegrallyClosed R] [IsAdicComplete (maximalIdeal R) R] (D : DegData R (maximalIdeal R))
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G) (p : ℕ) [Fact p.Prime] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T)
    (i : Γ.G.left ⟶ G.left) (hi : Γ.IsTorsionAlong G (𝟙 _) p i) :
    ∃ (M C Q : Type) (_ : CommGroup M) (_ : CommGroup C) (_ : CommGroup Q) (ΓB : QFGroup R C)
      (iB : ΓB.G.left ⟶ D.toPre.P.A.left) (e : (M × C) × Q ≃* T), ΓB.IsTorsionAlong D.toPre.P.A (𝟙 _) p iB ∧
      IsHopfOrder (muOrder R M) ∧ ∀ f : T → R, f ∈ Γ.btOrder ⊤ ↔ (fun z => f (e z)) ∈ Submodule.span R {F : (M × C) × Q → R |
        ∃ a ∈ muOrder R M, ∃ b ∈ ΓB.btOrder ⊤, ∃ c : Q → R, F = fun z => a z.1.1 * b z.1.2 * c z.2} := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  haveI : HenselianLocalRing R :=
    { is_henselian := fun f hf a₀ h₁ h₂ =>
        HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _) }
  have := Γ.quasiFinite
  have := Γ.separated
  have := Γ.quasiCompact
  have := Γ.finPres
  obtain ⟨W, hWf, hWc⟩ := PositivityTheory.HtPt.Twhopf.finite_part R Γ.G.left Γ.G.hom
  have hsub := PositivityTheory.HtPt.Twhopf.finite_sub R T Γ W hWf hWc
  obtain ⟨H, Γf, u, hH, _, hop, hcl, hr, hfin, hu⟩ := sub_qf R T Γ W hsub
  obtain ⟨M, C, _, _, ΓM, ΓB, iM, iB, a, b, hM, hB, _, _, ha, hbf, hbs, hpb, -⟩ :=
    PositivityTheory.HtPt.Stight.D1.finitePart_extension R D A G U p hp1 T Γ i hi H Γf u hop hfin fun g hg => hr ▸ hWc g hg
  have hT : ∀ t : T, t ^ p = 1 := GlobalTheory.T.torsion_along_order_divides R T Γ _ G _ p i hi
  obtain ⟨α, hα⟩ := exists_map ΓM Γf a
  obtain ⟨π, hπ⟩ := exists_map Γf ΓB b
  have hαi : Function.Injective α := fun m m' h => by
    have h1 : ΓM.pt m ≫ a = ΓM.pt m' ≫ a := by rw [hα, hα, h]
    refine pt_inj ΓM (Over.OverMorphism.ext ?_)
    rw [← cancel_mono a.left]
    exact congrArg CommaMorphism.left h1
  have hπs := map_surjective Γf ΓB b π hπ hbs
  haveI : Finite M := Finite.of_injective α hαi
  haveI : Finite C := Finite.of_surjective π hπs
  have hk : ∀ h, π h = 1 ↔ ∃ m, α m = h := fun h => by
    constructor
    · intro h1
      have w : Γf.pt h ≫ b = toUnit _ ≫ η[ΓB.G] := by rw [hπ, h1, map_one, Hom.one_def]
      obtain ⟨m, hm⟩ := exists_pt ΓM (hpb.lift _ _ w)
      exact ⟨m, pt_inj Γf (by rw [← hα, hm, hpb.lift_fst])⟩
    · rintro ⟨m, rfl⟩
      refine pt_inj ΓB ?_
      rw [← hπ, ← hα, Category.assoc, hpb.w, map_one, Hom.one_def, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
  obtain ⟨κ', hκ', hb'⟩ := exists_split p (fun t : H => Subtype.ext (hT t.1)) α π hαi hπs hk
  obtain ⟨κ, -, hb⟩ := exists_split p hT H.subtype (QuotientGroup.mk' H) H.subtype_injective
    (QuotientGroup.mk'_surjective H) fun t => (QuotientGroup.eq_one_iff t).trans
      ⟨fun h => ⟨⟨t, h⟩, rfl⟩, fun ⟨m, h⟩ => h ▸ m.2⟩
  have hAf := PositivityTheory.HtPt.Htat.bt_hopf R H Γf
  have r₁ : resOrder H.subtype (Γ.btOrder ⊤) = Γf.btOrder ⊤ := PositivityTheory.HtPt.Mk.res_bt_order_top @GlobalTheory.T.exists_base_change_group R T Γ H Γf u H.subtype hu hcl
  have r₂ : resOrder α (Γf.btOrder ⊤) = muOrder R M :=
    (PositivityTheory.HtPt.Mk.res_bt_order_top @GlobalTheory.T.exists_base_change_group R H Γf M ΓM a α hα ha).trans (mu_torus R M ΓM _ p iM hp1 hM).2
  have := D.toPre.P.isAb.proper
  have r₃ : quotOrder π (Γf.btOrder ⊤) = ΓB.btOrder ⊤ := PositivityTheory.HtPt.Mh.quot R C ΓB H Γf b π hπ hfin
    (PositivityTheory.HtPt.Mi.torsion_finite R C ΓB _ _ _ p iB hB inferInstance) hbf hbs
  obtain ⟨hmu, -, hq, e₂, he₂⟩ := split_mu R H M C α κ' hb' _ hAf r₂
  have r₄ : resOrder κ' (Γf.btOrder ⊤) = ΓB.btOrder ⊤ :=
    (hq π (MonoidHom.ext fun m => (hk _).2 ⟨m, rfl⟩) hκ').symm.trans r₃
  obtain ⟨e₁, he₁⟩ := split_prod R T H _ H.subtype κ hb _ hAf
  let ε' := MulEquiv.ofBijective _ hb'
  refine ⟨M, C, T ⧸ H, _, _, _, ΓB, iB, (ε'.prodCongr (MulEquiv.refl _)).trans (MulEquiv.ofBijective _ hb), hB,
    r₂ ▸ hmu, fun f => ?_⟩
  have k₂ := mem_iff_span (fun a : muOrder R M => (a.1 : M → R)) (fun b : resOrder κ' (Γf.btOrder ⊤) => (b.1 : C → R)) _ e₂.toLinearEquiv ε' ε'.surjective he₂
  have k₁ := mem_iff_span (H := M × C) (fun a z => a.1 (ε' z)) (fun c => c) _ e₁.toLinearEquiv
    ((ε'.prodCongr (MulEquiv.refl _)).trans (MulEquiv.ofBijective _ hb)) (MulEquiv.surjective _)
    (fun a c h k => he₁ a c (ε' h) k) f
  rw [btOrder_ind Γ W hsub H hH, r₁, k₁]
  have k₃ := span_triple (Z := T ⧸ H) {g : M × C → R | ∃ a ∈ Γf.btOrder ⊤, g = fun z => a (ε' z)} _ fun g =>
    ⟨fun ⟨a, ha, hg⟩ => hg ▸ (k₂ a).1 ha, fun hg => ⟨fun h => g (ε'.symm h), (k₂ _).2 (by simpa using hg), by simp⟩⟩
  refine Iff.of_eq (congrArg (fun W : Submodule R ((M × C) × (T ⧸ H) → R) => _ ∈ W)
    (Eq.trans (congrArg _ ?_) (k₃.trans (congrArg _ ?_))))
  · ext F
    constructor
    · rintro ⟨a, c, rfl⟩
      exact ⟨⟨_, a.1, a.2, rfl⟩, c, rfl⟩
    · rintro ⟨⟨_, a, ha, rfl⟩, c, rfl⟩
      exact ⟨⟨a, ha⟩, c, rfl⟩
  · ext F
    constructor
    · rintro ⟨_, ⟨a, b, rfl⟩, c, rfl⟩
      exact ⟨a.1, a.2, b.1, r₄ ▸ b.2, c, rfl⟩
    · rintro ⟨a, ha, b, hb, c, rfl⟩
      exact ⟨_, ⟨⟨a, ha⟩, ⟨b, r₄ ▸ hb⟩, rfl⟩, c, rfl⟩

end Struct

section Rep
open GlobalTheory.CompanionTheory.Ar.GR
open ReciprocityTheory.ChartRestriction.G.Chart (sp)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_rep (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] (C : Type) [Field C]
    [Algebra V C] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup V T) (G : Over (Spec (CommRingCat.of V))) [GrpObj G]
    (p : ℕ) (i : Γ.G.left ⟶ G.left) (ht : Γ.IsTorsionAlong G (𝟙 _) p i) (hfin : IsFinite Γ.G.hom) :
    ∃ (Tr : TorsRep G p) (pt : Additive T → (sp (R₀ := V) V ⟶ G)), IsTorsPts G p pt ∧
      ∀ f, f ∈ torsFun C Tr pt ↔ ∃ a ∈ Γ.btOrder ⊤, f = fun x => algebraMap V C (a x.toMul) := by
  let A := Γ.btOrder ⊤
  have hA : IsHopfOrder A := GlobalTheory.T.btOrder_isHopfOrder V T Γ ⊤
    ⟨by rw [← Scheme.topIso_hom]; infer_instance, fun _ => trivial, fun _ _ _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
  have := hA.finite
  have := hA.projective
  have hfree : Module.Free V A := Module.free_of_flat_of_isLocalRing
  obtain ⟨j, hj, -⟩ := PositivityTheory.HtPt.Mh.emb V T Γ
  have := GlobalTheory.T.btOrder_embedding_iso_finite V T Γ j hj hfin
  let iG : Γ.G ⟶ G := Over.homMk i (ht.isOver.trans (Category.comp_id _))
  let w : sp (R₀ := V) A ⟶ Γ.G := Over.homMk (inv j) (by
    rw [← hj.isOver, IsIso.inv_hom_id_assoc]; rfl)
  let c : ∀ Y : Over (Spec (CommRingCat.of V)), Over.mk (Y.hom ≫ 𝟙 _) ⟶ Y := fun Y =>
    Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hc : ∀ (Y : Over (Spec (CommRingCat.of V))) (g : Y ⟶ G), (c Y ≫ g).left = g.left := fun Y g => Category.id_comp _
  have hker : ∀ (Y : Over (Spec (CommRingCat.of V))) (g : Y ⟶ G), g ^ p = 1 ↔ ∃ y : Y ⟶ Γ.G, y ≫ iG = g := by
    intro Y g
    have h1 : g ^ p = 1 ↔ (c Y ≫ g) ^ p = 1 := by
      rw [← MonObj.comp_pow]
      refine ⟨fun h => by rw [h, MonObj.comp_one], fun h => Over.OverMorphism.ext ?_⟩
      rw [← hc, h, ← MonObj.comp_one (c Y), hc]
    rw [h1, ht.kernel, hc]
    exact exists_congr fun y => ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg CommaMorphism.left h⟩
  have hmul : ∀ (Y : Over (Spec (CommRingCat.of V))) (y z : Y ⟶ Γ.G), (y * z) ≫ iG = (y ≫ iG) * (z ≫ iG) := by
    intro Y y z
    have := ht.mul Y y z (c Y ≫ y ≫ iG) (c Y ≫ z ≫ iG) (hc _ _) (hc _ _)
    rw [← MonObj.comp_mul, hc] at this
    exact Over.OverMorphism.ext this.symm
  have hinj : ∀ (Y : Over (Spec (CommRingCat.of V))) (y z : Y ⟶ Γ.G), y ≫ iG = z ≫ iG → y = z := fun Y y z h =>
    ht.inj Y y z (congrArg CommaMorphism.left h)
  have hw : ∀ (S : Type) [CommRing S] [Algebra V S] (φ : A →ₐ[V] S),
      (Chart.spMap φ ≫ w).left ≫ j = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    intro S _ _ φ
    rw [Over.comp_left, Chart.spMap_left, Category.assoc]
    exact (congrArg _ (IsIso.inv_hom_id j)).trans (Category.comp_id _)
  have hφ : ∀ (S : Type) [CommRing S] [Algebra V S] (y : sp (R₀ := V) S ⟶ Γ.G),
      ∃! φ : A →ₐ[V] S, Chart.spMap φ ≫ w = y := by
    intro S _ _ y
    obtain ⟨φ₀, h₀⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of S) (y.left ≫ j)
    have h₁ : CommRingCat.ofHom (algebraMap V A) ≫ φ₀ = CommRingCat.ofHom (algebraMap V S) := by
      apply Spec.map_injective
      rw [Spec.map_comp, h₀, Category.assoc, hj.isOver]
      exact Over.w y
    have h₂ : ∀ φ : A →ₐ[V] S, Chart.spMap φ ≫ w = y ↔ φ.toRingHom = φ₀.hom := fun φ => by
      constructor
      · intro h
        have h₃ := hw S φ
        rw [h] at h₃
        exact (congrArg CommRingCat.Hom.hom (Spec.map_injective (h₀.trans h₃))).symm
      · intro h
        refine Over.OverMorphism.ext ?_
        rw [← cancel_mono j, hw, h]
        exact h₀
    refine ⟨⟨φ₀.hom, fun r => RingHom.congr_fun (congrArg CommRingCat.Hom.hom h₁) r⟩, (h₂ _).2 rfl, fun φ h => ?_⟩
    exact AlgHom.coe_ringHom_injective ((h₂ φ).1 h)
  let Tr : TorsRep G p :=
    { A := A, free := hfree, fin := inferInstance, y := w ≫ iG, y_p := (hker _ _).2 ⟨w, rfl⟩
      univ := fun S _ _ z hz => by
        obtain ⟨y, rfl⟩ := (hker _ _).1 hz
        obtain ⟨φ, h, hu⟩ := hφ S y
        exact ⟨φ, by rw [← h, Category.assoc], fun φ' h' => hu φ' (hinj _ _ _ ((Category.assoc _ _ _).trans h'))⟩ }
  let gm : BT.genPt V ⟶ sp (R₀ := V) V := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) (by
    change _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; rfl)
  have hgm : ∀ φ : A →ₐ[V] V, (gm ≫ Chart.spMap φ ≫ w).left ≫ j =
      Spec.map (CommRingCat.ofHom ((algebraMap V (FractionRing V)).comp φ.toRingHom)) := fun φ => by
    rw [Over.comp_left, Category.assoc, hw, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  let σ : T → (sp (R₀ := V) V ⟶ Γ.G) := fun t => Chart.spMap (evalAt A t) ≫ w
  have hσ : ∀ t, gm ≫ σ t = Γ.pt t := fun t => Over.OverMorphism.ext (by
    rw [← cancel_mono j, hgm, hj.pt]; rfl)
  have hext : ∀ y z : sp (R₀ := V) V ⟶ Γ.G, gm ≫ y = gm ≫ z → y = z := fun y z h => by
    obtain ⟨a, rfl, -⟩ := hφ V y
    obtain ⟨b, rfl, -⟩ := hφ V z
    have h₁ := (hgm a).symm.trans ((congrArg (fun u => u.left ≫ j) h).trans (hgm b))
    have h₂ := congrArg CommRingCat.Hom.hom (Spec.map_injective h₁)
    rw [show a = b from AlgHom.ext fun x => IsFractionRing.injective V (FractionRing V) (RingHom.congr_fun h₂ x)]
  refine ⟨Tr, fun x => σ x.toMul ≫ iG, ⟨fun x y h => ?_, fun x y => ?_, fun z => (hker _ z).trans ⟨?_, ?_⟩⟩, fun f => ⟨?_, ?_⟩⟩
  · have h₁ := congrArg (gm ≫ ·) (hinj _ _ _ h)
    simp only [hσ] at h₁
    exact Additive.toMul.injective (pt_inj Γ h₁)
  · rw [← hmul]
    congr 1
    exact hext _ _ (by rw [MonObj.comp_mul, hσ, hσ, hσ, toMul_add, map_mul])
  · rintro ⟨y, rfl⟩
    obtain ⟨t, h⟩ := exists_pt Γ (gm ≫ y)
    exact ⟨Additive.ofMul t, congrArg (· ≫ iG) (hext _ _ ((hσ t).trans h))⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a.1, a.2, funext fun x => ha x (evalAt A x.toMul) (Category.assoc _ _ _).symm⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha⟩, fun x φ h => ?_⟩
    have h₁ : φ = evalAt A x.toMul := (hφ V (σ x.toMul)).unique (hinj _ _ _ ((Category.assoc _ _ _).trans h)) rfl
    rw [h₁]
    rfl

end Rep

section Span
open GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

def spn {R V : Type} (C : Type) [CommRing R] [CommRing V] [Field C] [Algebra V C] (h : R →+* V) {T N : Type}
    (S : Set (T → R)) (u : N → T) : Submodule V (N → C) :=
  Submodule.span V {f | ∃ g ∈ S, f = fun x => algebraMap V C (h (g (u x)))}

variable {R R' V C : Type} [CommRing R] [CommRing R'] [CommRing V] [Field C] [Algebra V C] {T N : Type}

theorem spn_span (h : R →+* V) (S : Set (T → R)) (u : N → T) :
    spn C h (Submodule.span R S : Set (T → R)) u = spn C h S u := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono fun f ⟨g, hg, e⟩ => ⟨g, Submodule.subset_span hg, e⟩)
  rintro _ ⟨g, hg, rfl⟩
  change (fun x => algebraMap V C (h (g (u x)))) ∈ spn C h S u
  induction hg using Submodule.span_induction with
  | mem g hg => exact Submodule.subset_span ⟨g, hg, rfl⟩
  | zero => convert Submodule.zero_mem _ using 1; ext; simp
  | add a b _ _ h1 h2 => convert Submodule.add_mem _ h1 h2 using 1; ext; simp
  | smul r a _ h1 => convert Submodule.smul_mem _ (h r) h1 using 1; ext; simp [Algebra.smul_def]

theorem spn_ext [CommGroup T] (φ : R →+* R') (h : R' →+* V) (A : Subalgebra R (T → R)) (u : N → T) :
    spn C h (extOrder φ A : Set (T → R')) u = spn C (h.comp φ) A u := by
  have e : (extOrder φ A : Set (T → R')) = Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} :=
    Set.ext (GlobalTheory.T.extension_order_eq_span R T R' φ A)
  rw [e, spn_span]
  refine congrArg (Submodule.span V) (Set.ext fun f => ⟨?_, ?_⟩)
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩

theorem tens_span {X Y : Type} (S : Set (X → C)) (S' : Set (Y → C)) :
    tens (Submodule.span V S) (Submodule.span V S') =
      Submodule.span V {F : X × Y → C | ∃ g ∈ S, ∃ k ∈ S', F = fun z => g z.1 * k z.2} := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono fun f ⟨g, hg, k, hk, e⟩ =>
    ⟨g, Submodule.subset_span hg, k, Submodule.subset_span hk, e⟩)
  rintro _ ⟨g, hg, k, hk, rfl⟩
  change (fun z : X × Y => g z.1 * k z.2) ∈ Submodule.span V _
  induction hg using Submodule.span_induction with
  | mem g hg =>
    induction hk using Submodule.span_induction with
    | mem k hk => exact Submodule.subset_span ⟨g, hg, k, hk, rfl⟩
    | zero => convert Submodule.zero_mem _ using 1; ext; simp
    | add a b _ _ h1 h2 => convert Submodule.add_mem _ h1 h2 using 1; ext; simp [mul_add]
    | smul r a _ h1 => convert Submodule.smul_mem _ r h1 using 1; ext; simp
  | zero => convert Submodule.zero_mem _ using 1; ext; simp
  | add a b _ _ h1 h2 => convert Submodule.add_mem _ h1 h2 using 1; ext; simp [add_mul]
  | smul r a _ h1 => convert Submodule.smul_mem _ r h1 using 1; ext; simp

theorem int_eq [Finite T] (h : R →+* V) :
    intFun (C := C) V (Additive T) = spn C h (Set.univ : Set (T → R)) Additive.toMul := by
  classical
  have := Fintype.ofFinite (Additive T)
  refine le_antisymm (fun f hf => ?_) (Submodule.span_le.2 ?_)
  · choose r hr using hf
    have e : f = ∑ q, r q • fun x : Additive T => algebraMap V C (h ((Pi.single q.toMul (1 : R) : T → R) x.toMul)) := by
      funext x
      rw [Finset.sum_apply, Finset.sum_eq_single x]
      · simp [Algebra.smul_def, hr]
      · intro q _ hq
        rw [Pi.smul_apply, Pi.single_eq_of_ne (fun e => hq (Additive.toMul.injective e).symm)]
        simp
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, trivial, rfl⟩)
  · rintro _ ⟨g, -, rfl⟩ x
    exact ⟨_, rfl⟩

theorem mu_eq [IsDomain R] [IsDomain V] [IsIntegrallyClosed V] [CommGroup T] [Finite T] (v : Valuation C NNReal)
    (hv : v.Integers V) (h : R →+* V) (hh : Function.Injective h) (hA : IsHopfOrder (muOrder R T)) :
    Submodule.span V (Set.range fun (ψ : AddChar (Additive T) C) (x : Additive T) => ψ x) =
      spn C h (muOrder R T) Additive.toMul := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨ψ, rfl⟩
    letI := h.toAlgebra
    obtain ⟨d, hd, hdf⟩ := hA.full
    have hB := (PositivityTheory.HtPt.Mh.ext_tensor R T V _ hA ⟨d, (map_ne_zero_iff h hh).2 hd, hdf⟩).1
    have hr : ∀ t : T, ∃ r : V, algebraMap V C r = ψ (Additive.ofMul t) := fun t => by
      refine hv.exists_of_le_one (le_of_pow_le_pow_left₀ (Nat.card_pos (α := T)).ne' zero_le ?_)
      rw [← map_pow, ← AddChar.map_nsmul_eq_pow, ← ofMul_pow, pow_card_eq_one', ofMul_one, AddChar.map_zero_eq_one,
        map_one, one_pow]
    choose r hr using hr
    let χ : T →* V :=
      { toFun := r
        map_one' := hv.hom_inj (by simp [hr])
        map_mul' := fun a b => hv.hom_inj (by simp [hr, AddChar.map_add_eq_mul]) }
    have := GlobalTheory.T.hopf_order_contains_characters V T _ hB χ.toHomUnits
    have e := spn_ext (C := C) h (RingHom.id V) (muOrder R T) (Additive.toMul (α := T))
    rw [RingHom.id_comp] at e
    rw [← e]
    exact Submodule.subset_span ⟨_, this, funext fun x => (hr x.toMul).symm⟩
  · have e : (muOrder R T : Set (T → R)) = Submodule.span R
        (Set.range fun (χ : T →* Rˣ) (t : T) => ((χ t : Rˣ) : R)) := congrArg SetLike.coe muOrder_eq_span
    rw [e, spn_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨χ, rfl⟩, rfl⟩
    exact ⟨⟨fun x => algebraMap V C (h (χ x.toMul)), by simp, fun a b => by simp⟩, rfl⟩

theorem transport (p : ℕ) [Fact p.Prime] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (hv : v.Integers V)
    (hp : v (p : C) < 1) {N N' : Type} [AddCommGroup N] [Fintype N] [DecidableEq N] [AddCommGroup N'] [Fintype N']
    [DecidableEq N'] (hN : ∀ x : N, p • x = 0) (AA : HopfOrder (C := C) V N) (e : N' ≃+ N)
    (h : IsAbFactor p (AA.carrier.map (LinearMap.funLeft V C (e : N' → N))) ∧
      IsTight v p (AA.carrier.map (LinearMap.funLeft V C (e : N' → N)))) :
    IsAbFactor p AA.carrier ∧ IsTight v p AA.carrier := by
  obtain ⟨⟨A', hA'⟩, -⟩ := PositivityTheory.HtPt.Re.ret_hopf p C v V hv hp N AA N' e.toAddMonoidHom e.symm.toAddMonoidHom
    e.symm_apply_apply fun g hg => by simpa using hg
  have hA'' : A'.carrier = AA.carrier.map (LinearMap.funLeft V C (e : N' → N)) := hA'
  rw [← hA''] at h
  have hb : A'.carrier.map (LinearMap.funLeft V C (e.symm.toAddMonoidHom : N → N')) = AA.carrier := by
    rw [hA'', ← Submodule.map_comp, ← LinearMap.funLeft_comp]
    convert Submodule.map_id AA.carrier
    ext f x
    simp [LinearMap.funLeft]
  rw [← hb]
  exact ⟨(PositivityTheory.HtPt.Rg.abfac_prod p C v V hv hp).2 N N' A'.carrier e.symm.toAddMonoidHom e.toAddMonoidHom
      e.apply_symm_apply (fun g hg => by simpa using hg) h.1,
    PositivityTheory.HtPt.Re.ret_tight p C v V hv hp N' (fun x => e.injective (by rw [map_nsmul, hN, map_zero])) A' N
      e.symm.toAddMonoidHom e.toAddMonoidHom e.apply_symm_apply (fun g hg => by simpa using hg) h.2⟩

end Span

theorem val_facts {C V : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing V] [IsDomain V] [Algebra V C]
    (v : Valuation C NNReal) (hint : v.Integers V) (p : ℕ) (hp : p ≠ 0) (hvp : v (p : C) < 1) :
    ∃ _ : IsLocalRing V, IsIntegrallyClosed V ∧ IsAlgClosed (FractionRing V) ∧ (p : V) ∈ IsLocalRing.maximalIdeal V ∧
      IsLocalRing.maximalIdeal V ≤ (Ideal.span {(p : V)}).radical := by
  haveI : IsFractionRing V C := hint.isFractionRing
  haveI : ValuationRing V := ValuationRing.of_integers v hint
  have hm : ∀ a : V, a ∈ IsLocalRing.maximalIdeal V ↔ v (algebraMap V C a) < 1 := fun a =>
    (not_congr hint.isUnit_iff_valuation_eq_one).trans
      ⟨fun h => lt_of_le_of_ne (hint.map_le_one a) h, fun h => h.ne⟩
  have hp0 : 0 < v (p : C) := (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 hp)
  refine ⟨inferInstance, inferInstance, IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv V C).symm.toRingEquiv,
    (hm _).2 (by rw [map_natCast]; exact hvp), fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hp0 ((hm a).1 ha)
  refine ⟨n, Ideal.mem_span_singleton.2 (hint.dvd_of_le ?_)⟩
  rw [map_pow, map_pow, map_natCast]
  exact hn.le

section Core
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem core (hD : HodgeTateDatumStatement) (hO : OrdinaryCurveStatement) (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsIntegrallyClosed V] [Algebra V C] (hv : v.Integers V) (hp : v (p : C) < 1)
    (hc : IsAdicComplete (Ideal.span {(p : V)}) V)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    [IsIntegrallyClosed R] [IsAdicComplete (maximalIdeal R) R] (h : R →+* V) (hh : Function.Injective h)
    (D : DegData R (maximalIdeal R))
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N]
    (Γ : QFGroup R (Multiplicative N)) (i : Γ.G.left ⟶ G.left) (hi : Γ.IsTorsionAlong G (𝟙 _) p i) :
    IsAbFactor p (spn C h (Γ.btOrder ⊤) (Multiplicative.ofAdd (α := N))) ∧
      IsTight v p (spn C h (Γ.btOrder ⊤) (Multiplicative.ofAdd (α := N))) := by
  classical
  obtain ⟨M, B, Q, _, _, _, ΓB, iB, e, hB, hmu, hsp⟩ := exists_struct R D A G U p _ Γ i hi
  have hT : ∀ t : Multiplicative N, t ^ p = 1 := GlobalTheory.T.torsion_along_order_divides R _ Γ _ G _ p i hi
  have hT' : ∀ z : (M × B) × Q, z ^ p = 1 := fun z => e.injective (by rw [map_pow, hT, map_one])
  haveI : Finite ((M × B) × Q) := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite M := Finite.of_injective (fun m : M => (((m, 1), 1) : (M × B) × Q)) fun _ _ h =>
    congrArg (fun z => z.1.1) h
  haveI : Finite B := Finite.of_injective (fun m : B => (((1, m), 1) : (M × B) × Q)) fun _ _ h =>
    congrArg (fun z => z.1.2) h
  haveI : Finite Q := Finite.of_injective (fun m : Q => ((1, m) : (M × B) × Q)) fun _ _ h =>
    congrArg (fun z => z.2) h
  letI := Fintype.ofFinite (Additive M)
  letI := Fintype.ofFinite (Additive B)
  letI := Fintype.ofFinite (Additive Q)
  letI : Algebra R V := h.toAlgebra
  obtain ⟨hL, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨P', gA, pA, -, mA, -⟩ := hL.polBaseChange _ _ (spMap h) D.toPre.P
  have gpA : IsGrpPullback P'.A D.toPre.P.A (spMap h) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  obtain ⟨Γ', F, hF⟩ := GlobalTheory.T.exists_base_change_group R B ΓB V h hh
  have t₁ := GlobalTheory.T.torsion_along_base_change R B ΓB _ _ _ p iB hB V h Γ' F hF
  rw [Category.comp_id] at t₁
  obtain ⟨i₀, -, t₀⟩ := (GlobalTheory.T.torsion_pullback_correspondence V B Γ' _ (spMap h) _ P'.A gA p gpA).1 _ t₁
  have := P'.isAb.proper
  obtain ⟨Tr, pt, hpt, hTr⟩ := exists_rep V C B Γ' P'.A p i₀ t₀
    (PositivityTheory.HtPt.Mi.torsion_finite V B Γ' _ _ _ p i₀ t₀ inferInstance)
  have eT : torsFun C Tr pt = spn C h (ΓB.btOrder ⊤) Additive.toMul := by
    have e₁ := spn_ext (C := C) h (RingHom.id V) (ΓB.btOrder ⊤) (Additive.toMul (α := B))
    rw [RingHom.id_comp] at e₁
    rw [← e₁, ← Submodule.span_eq (torsFun C Tr pt)]
    refine congrArg (Submodule.span V) (Set.ext fun f => (hTr f).trans ?_)
    rw [(GlobalTheory.T.btOrder_base_change_generic R B ΓB V Γ' F hF).2]
    rfl
  have key := PositivityTheory.HtPt.Stight.BadRed.main hD hO p C v V hv hp hc P' Tr (Additive B) pt hpt (Additive M) (Additive Q)
    (fun x => congrArg (fun z => z.1.1) (hT' ((x.toMul, 1), 1))) (fun x => congrArg (fun z => z.2) (hT' (1, x.toMul)))
  rw [eT, mu_eq v hv h hh hmu, int_eq h] at key
  have hA := PositivityTheory.HtPt.Htat.bt_hopf R _ Γ
  obtain ⟨d, hd, hdf⟩ := hA.full
  obtain ⟨AA, hAA⟩ := PositivityTheory.HtPt.Mk.bt_pgsh V C hv.hom_inj N _
    (PositivityTheory.HtPt.Mh.ext_tensor R _ V _ hA ⟨d, (map_ne_zero_iff h hh).2 hd, hdf⟩).1
  have eA : AA.carrier = spn C h (Γ.btOrder ⊤) Multiplicative.ofAdd := by
    have e₁ := spn_ext (C := C) h (RingHom.id V) (Γ.btOrder ⊤) (Multiplicative.ofAdd (α := N))
    rw [RingHom.id_comp] at e₁
    rw [← e₁, ← Submodule.span_eq AA.carrier]
    exact congrArg (Submodule.span V) (Set.ext fun f => (hAA f).trans
      (exists_congr fun g => and_congr Iff.rfl funext_iff.symm))
  let u : Additive B × Additive M × Additive Q ≃ (M × B) × Q :=
    { toFun := fun z => ((z.2.1.toMul, z.1.toMul), z.2.2.toMul)
      invFun := fun z => (Additive.ofMul z.1.2, Additive.ofMul z.1.1, Additive.ofMul z.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E : Additive B × Additive M × Additive Q ≃+ N :=
    AddEquiv.mk' (u.trans (e.toEquiv.trans Multiplicative.toAdd)) fun a b =>
      congrArg Multiplicative.toAdd (e.map_mul (u a) (u b))
  rw [← eA]
  refine transport p v hv hp (fun x => hT (Multiplicative.ofAdd x)) AA E ?_
  convert key using 2
  all_goals
    rw [eA, spn, Submodule.map_span, spn, spn, spn, tens_span, tens_span]
    refine Eq.trans ?_ ((spn_span (C := C) h {F : (M × B) × Q → R |
        ∃ a ∈ muOrder R M, ∃ b ∈ ΓB.btOrder ⊤, ∃ c : Q → R, F = fun z => a z.1.1 * b z.1.2 * c z.2} u).trans ?_)
    · refine congrArg (Submodule.span V) (Set.ext fun f => ⟨?_, ?_⟩)
      · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨_, (hsp g).1 hg, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        refine ⟨_, ⟨fun t => g (e.symm t), (hsp _).2 (by simpa using hg), rfl⟩, funext fun z => ?_⟩
        exact congrArg (fun w => algebraMap V C (h (g w))) (e.symm_apply_apply (u z))
    · refine congrArg (Submodule.span V) (Set.ext fun f => ⟨?_, ?_⟩)
      · rintro ⟨_, ⟨a, ha, b, hb, c, rfl⟩, rfl⟩
        refine ⟨_, ⟨b, hb, rfl⟩, _, ⟨_, ⟨a, ha, rfl⟩, _, ⟨c, trivial, rfl⟩, rfl⟩, funext fun z => ?_⟩
        simp only [map_mul, u, Equiv.coe_fn_mk]
        ring
      · rintro ⟨_, ⟨b, hb, rfl⟩, _, ⟨_, ⟨a, ha, rfl⟩, _, ⟨c, -, rfl⟩, rfl⟩, rfl⟩
        refine ⟨_, ⟨a, ha, b, hb, c, rfl⟩, funext fun z => ?_⟩
        simp only [map_mul, u, Equiv.coe_fn_mk]
        ring

end Core

end

end PositivityTheory.Xgn.TightHopfOrder

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

open PositivityTheory.Xgn.TightHopfOrder in
theorem PositivityTheory.Xgn.tight_hopf_order_test : GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → GlobalTheory.CompanionTheory.Ar.GR.IsAbFactor p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ GlobalTheory.CompanionTheory.Ar.GR.IsTight v p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) := by
  intro hD hO E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d h1 h2 p _ h3 h4 h5 h6 b h7 φ hφ A _ _ _ m _ h8 O _ _ _ _ _ _ _
    t₀ Sg _ e φ' F _ _ _ pq sc w σ hOr hsec G c' h9 P i h10 h11 C _ _ _ _ RC hT χ hχ _ _ _ v hv hvp
  obtain ⟨hC, -, hcompl, hle⟩ := hT
  obtain ⟨hch, hN, hic, hfr, -⟩ := PositivityTheory.Xgn.torsion_packing_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d h1 p h3 A m h8 O c' h9
  haveI : CharZero C := charZero_of_injective_ringHom (algebraMap Ω C).injective
  have hint : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  obtain ⟨_, _, _, hpm, hnil⟩ := val_facts v hint p (Fact.out : p.Prime).ne_zero hvp
  let f : CR O y c' →+* RC := ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω)).codRestrict RC fun a => hle a a.2
  have hf : Function.Injective f := fun a a' h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  obtain ⟨x₀, hx₀⟩ := PositivityTheory.HtPt.Hcptgen.exists_lift 𝔐
  have hpol := GlobalTheory.Ex.UnifModel.polAt_of_point Y 𝔐.ξ 𝔐.f x₀ hx₀ 𝔐.t 𝔐.m
  rw [← P.x_gen] at hpol
  obtain ⟨R, _, _, _, g, h, t', ψ, Dd, A', hRN, hRi, hRc, hh, hgf, hpb, ⟨U⟩⟩ :=
    exists_unif RC p Fact.out hpm hnil (CR O y c') f hf Ω 𝔐.t P.x hpol
  haveI : CharZero R := h.charZero
  have hg : Function.Injective g := Function.Injective.of_comp (f := h) (by rw [← RingHom.coe_comp, hgf]; exact hf)
  letI : Algebra (CR O y c') R := g.toAlgebra
  obtain ⟨Γ', F', hF⟩ := GlobalTheory.T.exists_base_change_group _ _ P.Γ₁ R g hg
  have t₁ := GlobalTheory.T.torsion_along_base_change _ _ P.Γ₁ _ _ _ p P.i₁ P.tors₁ R g Γ' F' hF
  obtain ⟨i₀, -, t₂⟩ := (GlobalTheory.T.torsion_pullback_correspondence R _ Γ' _ _ _ t'.G ψ p hpb).1 _ t₁
  have key := core hD hO p C v RC hint hvp hcompl R h hh Dd A' t'.G U _ Γ' i₀ t₂
  rw [(GlobalTheory.T.btOrder_base_change_generic _ _ P.Γ₁ R Γ' F' hF).2, spn_ext, show h.comp (algebraMap (CR O y c') R) = f from hgf] at key
  exact key
