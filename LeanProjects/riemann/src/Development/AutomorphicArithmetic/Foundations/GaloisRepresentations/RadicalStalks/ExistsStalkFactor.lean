import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.EpsMulSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.ArtTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartLieDeRhamQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdemKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupSchemeStalkLengthConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLengthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermSystemHeightFree

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace UpperTheory.Gal.Ord.CntStalk

variable {k : Type} [Field k]

private theorem exists_stalk_factor {X : Scheme.{0}} (x : X) {T : Type} [CommRing T] [IsLocalRing T] (g : Sp T ⟶ X)
    (hx : g (IsLocalRing.closedPoint T) = x) :
    ∃ u : X.presheaf.stalk x →+* T, Spec.map (CommRingCat.ofHom u) ≫ X.fromSpecStalk x = g := by
  subst hx
  exact ⟨(Scheme.stalkClosedPointTo g).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk g⟩

private def stalkAlg (K : Over (Sp k)) (x : K.left) : CommRingCat.of k ⟶ K.left.presheaf.stalk x :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ K.hom.appTop ≫ K.left.presheaf.germ ⊤ x trivial

private theorem spec_stalkAlg (K : Over (Sp k)) (x : K.left) :
    Spec.map (stalkAlg K x) = K.left.fromSpecStalk x ≫ K.hom := by
  rw [stalkAlg, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

private theorem stalkAlg_finite (K : Over (Sp k)) [IsFinite K.hom] (x : K.left) : (stalkAlg K x).hom.Finite := by
  have hA : IsAffine K.left := isAffine_of_isAffineHom K.hom
  have h1 : K.hom.appTop.hom.Finite := K.hom.finite_appTop
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  have h01 : (K.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Finite := h1.comp h0
  letI : Algebra k Γ(K.left, ⊤) := (K.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  haveI : Module.Finite k Γ(K.left, ⊤) := h01
  haveI : IsArtinianRing Γ(K.left, ⊤) := IsArtinianRing.of_finite k _
  letI := TopCat.Presheaf.algebra_section_stalk K.left.presheaf (⟨x, trivial⟩ : (⊤ : K.left.Opens))
  have hloc := (isAffineOpen_top K.left).isLocalization_stalk ⟨x, trivial⟩
  have hs : Function.Surjective (algebraMap Γ(K.left, ⊤) (K.left.presheaf.stalk x)) :=
    IsArtinianRing.localization_surjective ((isAffineOpen_top K.left).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl _
  have h2 : (K.left.presheaf.germ ⊤ x trivial).hom.Finite := RingHom.Finite.of_surjective _ hs
  exact h2.comp h01

@[reducible] private def stalkAlgebra (K : Over (Sp k)) (x : K.left) : Algebra k (K.left.presheaf.stalk x) :=
  (stalkAlg K x).hom.toAlgebra

attribute [local instance] stalkAlgebra

private def stalkPt (K : Over (Sp k)) (x : K.left) :
    Over.mk (spMap (algebraMap k (K.left.presheaf.stalk x))) ⟶ K :=
  Over.homMk (K.left.fromSpecStalk x) (spec_stalkAlg K x).symm

private theorem exists_alg (K : Over (Sp k)) (x : K.left) {T : Type} [CommRing T] [IsLocalRing T] [Algebra k T]
    (g : Over.mk (spMap (algebraMap k T)) ⟶ K) (hx : g.left (IsLocalRing.closedPoint T) = x) :
    ∃ u : K.left.presheaf.stalk x →ₐ[k] T, spOver u ≫ stalkPt K x = g := by
  obtain ⟨u, hu⟩ := exists_stalk_factor x g.left hx
  let u' : K.left.presheaf.stalk x ⟶ CommRingCat.of T := CommRingCat.ofHom u
  have hc : stalkAlg K x ≫ u' = CommRingCat.ofHom (algebraMap k T) := by
    apply Spec.map_injective
    rw [Spec.map_comp, spec_stalkAlg, ← Category.assoc]
    exact (congrArg (· ≫ K.hom) hu).trans (Over.w g)
  refine ⟨{ u with commutes' := fun a => ?_ }, ?_⟩
  · exact congrArg (fun f => f.hom a) hc
  · apply Over.OverMorphism.ext
    exact hu

private theorem closed_eps : (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (IsLocalRing.closedPoint k) =
    IsLocalRing.closedPoint (DualNumber k) := by
  haveI : IsLocalHom (TrivSqZeroExt.fstHom k k k).toRingHom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  exact Spec_closedPoint (R := CommRingCat.of (DualNumber k)) (S := CommRingCat.of k)
    (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

private theorem exists_stalkPt [IsAlgClosed k] (K : Over (Sp k)) [GrpObj K] [IsFinite K.hom] :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra k B) (_ : Module.Finite k B)
      (y : Over.mk (spMap (algebraMap k B)) ⟶ K),
      Mono y.left ∧
      (∀ x : K.left, Module.length (K.left.presheaf.stalk x) (K.left.presheaf.stalk x) = Module.length B B) ∧
      (∃ c : B →ₐ[k] k, spOver c ≫ y = 1) ∧
      ∀ v : epsR k ⟶ K, IsTangent v → ∃ u : B →ₐ[k] DualNumber k, spOver u ≫ y = v := by
  set g₁ : Over.mk (spMap (algebraMap k k)) ⟶ K := 1 with hg₁
  set x₀ : K.left := g₁.left (IsLocalRing.closedPoint k) with hx₀
  haveI : Module.Finite k (K.left.presheaf.stalk x₀) := stalkAlg_finite K x₀
  obtain ⟨c, hc⟩ := exists_alg K x₀ g₁ rfl
  refine ⟨K.left.presheaf.stalk x₀, inferInstance, inferInstance, inferInstance, inferInstance, stalkPt K x₀,
    ?_, fun x => GlobalTheory.T.finite_group_scheme_stalk_length_constant k K inferInstance x x₀, ⟨c, hc⟩, fun v hv => ?_⟩
  · show Mono (K.left.fromSpecStalk x₀)
    infer_instance
  · apply exists_alg
    have h1 : spMap (algebraMap k k) = 𝟙 (Sp k) := by
      show Spec.map (CommRingCat.ofHom (RingHom.id k)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    have hg : g₁.left = Over.Hom.left η := by
      rw [hg₁, GlobalTheory.HTSummand.LieMod.one_left, h1, Category.id_comp]
    unfold IsTangent at hv
    rw [← closed_eps, hx₀, hg, ← hv]
    rfl

end UpperTheory.Gal.Ord.CntStalk

namespace UpperTheory.Gal.Ord.CntLie

private theorem lie_line (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (hN : 3 ≤ N) (hNp : N.Coprime p) (hm : D.m = 1)
    (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ)
    (hw : RingHom.ker (β.comp (b.t i)) = w) (hq : Ideal.absNorm w = p ^ f) (hf : 0 < f) (π : Par p w f) :
    (∃ v₀ : epsR k ⟶ o.A, IsTangent v₀ ∧ v₀ ≠ 1 ∧ KilledBy o w v₀) ∧
    ∀ v₁ v₂ : epsR k ⟶ o.A, IsTangent v₁ → IsTangent v₂ → KilledBy o w v₁ → KilledBy o w v₂ → v₁ ≠ 1 →
      ∃ l : k, v₂ = GlobalTheory.GrpTangent.epsScale l ≫ v₁ := by
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o.A o.ab
  have HL : LieExact o.A := (GlobalTheory.abelianDeRham.2.1 k o.A g o.ab hg).1
  let a := OActN.toF D o.act
  have e1 : ∀ (c : 𝓞 D.F) (V : GlobalTheory.Serre.Lie a), (c • V).hom = V.hom ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) :=
    fun c V => rfl
  have e2 : ∀ (l : k) (V : GlobalTheory.Serre.Lie a), (l • V).hom = GlobalTheory.GrpTangent.epsScale l ≫ V.hom := fun l V => rfl
  have e3 : (0 : GlobalTheory.Serre.Lie a).hom = 1 := rfl
  obtain ⟨h1, ⟨h₀, hne, hspan⟩, -⟩ := UpperTheory.Gal.Ord.lie p D R b N hN hNp hm k hk β o i w f hw hq hf π
  set T := HL.toLie a with hT
  have Tker : ∀ h, T h = 0 ↔ h ∈ Fil o.A := fun h => by
    rw [← LinearMap.mem_ker, hT, LieExact.ker_toLie]
  have Tcrys : ∀ (c : 𝓞 D.F) h, T (UpperTheory.Gal.Ord.hom o c h) = c • T h := fun c h =>
    GlobalTheory.HTLieRho.toLie_crys o HL c h
  have hzero : ∀ c ∈ w, β (b.t i c) = 0 := fun c hc => by
    rw [← hw] at hc
    exact RingHom.mem_ker.mp hc
  have stepA : ∀ c ∈ w, ∀ h, c • T (UpperTheory.Gal.Ord.hom o π.ε h) = 0 := fun c hc h => by
    rw [← Tcrys, Tker]
    have := h1 c h
    rwa [hzero c hc, zero_smul, sub_zero] at this
  have killed : ∀ (V : GlobalTheory.Serre.Lie a), KilledBy o w V.hom → ∀ c ∈ w, c • V = 0 := fun V hV c hc =>
    GlobalTheory.Serre.Lie.ext (by rw [e1, e3]; exact hV c hc)
  have stepB : ∀ V : GlobalTheory.Serre.Lie a, (∀ c ∈ w, c • V = 0) → ∃ h, V = T (UpperTheory.Gal.Ord.hom o π.ε h) := fun V hV => by
    obtain ⟨h', rfl⟩ := LieExact.toLie_surjective HL a V
    refine ⟨h', ?_⟩
    rw [Tcrys]
    have h2 := hV (π.ε - 1) π.one
    rw [sub_smul, one_smul, sub_eq_zero] at h2
    exact h2.symm
  have stepC : ∀ h, ∃ l : k, T (UpperTheory.Gal.Ord.hom o π.ε h) = l • T (UpperTheory.Gal.Ord.hom o π.ε h₀) := fun h => by
    obtain ⟨l, hl⟩ := hspan h
    refine ⟨l, ?_⟩
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Tker]
    exact hl
  have ne0 : T (UpperTheory.Gal.Ord.hom o π.ε h₀) ≠ 0 := fun h => hne ((Tker _).mp h)
  refine ⟨⟨(T (UpperTheory.Gal.Ord.hom o π.ε h₀)).hom, (T (UpperTheory.Gal.Ord.hom o π.ε h₀)).isTangent,
    fun h => ne0 (GlobalTheory.Serre.Lie.ext (by rw [h, e3])), ?_⟩, ?_⟩
  · intro c hc
    rw [← e1, stepA c hc, e3]
  · intro v₁ v₂ hv₁ hv₂ hk₁ hk₂ hne₁
    obtain ⟨g₁, hg₁⟩ := stepB _ (killed (GlobalTheory.Serre.Lie.mk a v₁ hv₁) hk₁)
    obtain ⟨g₂, hg₂⟩ := stepB _ (killed (GlobalTheory.Serre.Lie.mk a v₂ hv₂) hk₂)
    obtain ⟨l₁, hl₁⟩ := stepC g₁
    obtain ⟨l₂, hl₂⟩ := stepC g₂
    have hl₁0 : l₁ ≠ 0 := by
      rintro rfl
      apply hne₁
      have := congrArg GlobalTheory.Serre.Lie.hom (hg₁.trans hl₁)
      rw [zero_smul, e3] at this
      exact this
    refine ⟨l₂ / l₁, ?_⟩
    have h3 : GlobalTheory.Serre.Lie.mk a v₂ hv₂ = (l₂ / l₁) • GlobalTheory.Serre.Lie.mk a v₁ hv₁ := by
      rw [hg₂, hl₂, hg₁, hl₁, smul_smul, div_mul_cancel₀ _ hl₁0]
    have := congrArg GlobalTheory.Serre.Lie.hom h3
    rw [e2] at this
    exact this

end UpperTheory.Gal.Ord.CntLie

namespace UpperTheory.Gal.Ord.CntPt

variable {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B] {A : Over (Sp k)} [GrpObj A]

private theorem algHom_unique [IsLocalRing B] (c c' : B →ₐ[k] k) : c = c' := by
  have key : ∀ d : B →ₐ[k] k, RingHom.ker d.toRingHom = IsLocalRing.maximalIdeal B := fun d =>
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨algebraMap k B a, by simp⟩))
  ext b
  have hm : b - algebraMap k B (c b) ∈ RingHom.ker c'.toRingHom := by
    rw [key c', ← key c, RingHom.mem_ker]
    simp
  rw [RingHom.mem_ker] at hm
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at hm
  exact hm.symm

private abbrev fstA : DualNumber k →ₐ[k] k := TrivSqZeroExt.fstHom k k k

private abbrev inlA : k →ₐ[k] DualNumber k := Algebra.ofId k _

private def scA (l : k) : DualNumber k →ₐ[k] DualNumber k :=
  { epsScaleR l with
    commutes' := fun a => by
      simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl] }

private theorem snd_scA (l : k) (x : DualNumber k) : TrivSqZeroExt.snd (scA l x) = l * TrivSqZeroExt.snd x := by
  show TrivSqZeroExt.snd (epsScaleR l x) = _
  simp [epsScaleR]

private theorem spOver_inj (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (hz : Mono z.left) {T : Type} [CommRing T] [Algebra k T]
    {u u' : B →ₐ[k] T} (h : spOver u ≫ z = spOver u' ≫ z) : u = u' := by
  have h1 := congrArg (fun f => f.left) h
  simp only [Over.comp_left] at h1
  have h2 : (spOver u).left = (spOver u').left := (cancel_mono z.left).mp h1
  have h3 : CommRingCat.ofHom (u : B →+* T) = CommRingCat.ofHom (u' : B →+* T) := Spec.map_injective h2
  ext b
  exact congrArg (fun f => f.hom b) h3

private theorem tangent_of [IsLocalRing B] (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (c : B →ₐ[k] k) (hc : spOver c ≫ z = 1)
    (u : B →ₐ[k] DualNumber k) : IsTangent (spOver u ≫ z) := by
  have hcu : (fstA (k := k)).comp u = c := algHom_unique _ _
  have h1 := congrArg (fun f => f.left) hc
  simp only [Over.comp_left, GlobalTheory.HTSummand.LieMod.one_left] at h1
  have h2 : (spOver (fstA (k := k)) ≫ spOver u).left = (spOver c).left := by
    rw [spOver_comp, hcu]
  rw [Over.comp_left] at h2
  unfold IsTangent
  rw [Over.comp_left, ← Category.assoc]
  erw [h2, h1]
  simp only [Algebra.algebraMap_self]
  show Spec.map (CommRingCat.ofHom (RingHom.id k)) ≫ _ = _
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

private theorem const_eq_one (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (c : B →ₐ[k] k) (hc : spOver c ≫ z = 1) :
    spOver (inlA.comp c) ≫ z = (1 : epsR k ⟶ A) := by
  have h1 := congrArg (fun f => f.left) hc
  simp only [Over.comp_left, GlobalTheory.HTSummand.LieMod.one_left] at h1
  have hw := Over.w (spOver (inlA (k := k)))
  simp only [Over.mk_hom] at hw
  apply Over.OverMorphism.ext
  rw [GlobalTheory.HTSummand.LieMod.one_left, ← spOver_comp, Category.assoc, Over.comp_left, Over.comp_left, h1,
    ← Category.assoc, hw]

private theorem eq_const_of_one (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (hz : Mono z.left) (c : B →ₐ[k] k)
    (hc : spOver c ≫ z = 1) (u : B →ₐ[k] DualNumber k) (h : spOver u ≫ z = (1 : epsR k ⟶ A)) :
    ∀ x, TrivSqZeroExt.snd (u x) = 0 := by
  have := spOver_inj z hz (h.trans (const_eq_one z c hc).symm)
  intro x
  rw [this]
  simp [inlA, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl]

private theorem scale_comp (z : Over.mk (spMap (algebraMap k B)) ⟶ A) (l : k) (u : B →ₐ[k] DualNumber k) :
    GlobalTheory.GrpTangent.epsScale l ≫ spOver u ≫ z = spOver ((scA l).comp u) ≫ z := by
  have he : GlobalTheory.GrpTangent.epsScale l = spOver (scA l) := Over.OverMorphism.ext rfl
  rw [he, ← Category.assoc, spOver_comp]

private theorem const_of_length [IsLocalRing B] (h : Module.length B B = 1) (c : B →ₐ[k] k) (u : B →ₐ[k] DualNumber k) :
    u = inlA.comp c := by
  have hs := (isSimpleModule_self_iff_isUnit.mp (Module.length_eq_one_iff.mp h)).2
  refine AlgHom.ext fun b => ?_
  have hb : b = algebraMap k B (c b) := by
    by_contra hne
    have hu := (hs (b - algebraMap k B (c b)) (sub_ne_zero.mpr hne)).map c
    simp at hu
  rw [hb, AlgHom.commutes, AlgHom.commutes]

end UpperTheory.Gal.Ord.CntPt

theorem UpperTheory.Gal.Ord.cnt :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      IsWOrd o w (𝟙 (Sp k)) ∨ ∃ v : epsR k ⟶ o.A, IsTangent v ∧ v ≠ 1 ∧ IsDeep o w (p ^ f) v := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i₀ w f hw hq hf π
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hk
  have hPne : p ^ f ≠ 0 := pow_ne_zero f (Fact.out : p.Prime).ne_zero
  have hP2 : 2 ≤ p ^ f := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow hf.ne' p)
  have hwP : w.IsPrime := hw ▸ RingHom.ker_isPrime _
  have hpw : ((p : ℕ) : 𝓞 D.F) ∈ w := by
    rw [← hw, RingHom.mem_ker, RingHom.comp_apply, map_natCast, map_natCast, hk]
  have hw0 : w ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hq
    exact hPne hq.symm
  have hwM : w.IsMaximal := hwP.isMaximal hw0
  obtain ⟨K, _, i, hiMon, hiMono, hdeg, hiff⟩ := GlobalTheory.HTTors.htTorsion p D R b N (Sp k) (spMap β) o w hw0
  have hKiff : ∀ (T : Over (Sp k)) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ KilledBy o w x := fun T x =>
    (hiff T x).trans ((GlobalTheory.HTTors.killedBy_map o w x).trans Iff.rfl)
  have hqK : (toUnit K).left = K.hom := by simpa using Over.w (toUnit K)
  haveI : IsFinite K.hom := hqK ▸ hdeg.fin
  obtain ⟨B, _, _, _, _, y, hyMono, hlen, ⟨c, hc⟩, hfac⟩ := UpperTheory.Gal.Ord.CntStalk.exists_stalkPt K
  let z : Over.mk (spMap (algebraMap k B)) ⟶ o.A := y ≫ i
  have hzMono : Mono z.left := by
    show Mono (y ≫ i).left
    rw [Over.comp_left]
    exact mono_comp _ _
  have hzc : spOver c ≫ z = 1 := by
    show spOver c ≫ y ≫ i = 1
    rw [← Category.assoc, hc]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.HTSummand.LieMod.one_left, GlobalTheory.HTSummand.LieMod.one_left, Category.assoc]
    congr 1
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hkill : ∀ {T : Type} [CommRing T] [Algebra k T] (u : B →ₐ[k] T), KilledBy o w (spOver u ≫ z) := by
    intro T _ _ u
    exact (hKiff _ _).mp ⟨spOver u ≫ y, Category.assoc _ _ _⟩
  let pt : ↥(Sp k) := IsLocalRing.closedPoint k
  have hI := GlobalTheory.T.finrank_fiber_eq_card_sections_mul_length k K.left K.hom inferInstance (Module.length B B) hlen pt
  have hrank : Scheme.Hom.finrank K.hom pt = (Ideal.absNorm w ^ D.m) ^ D.n := by
    rw [← hqK]
    exact hdeg.rank pt
  rw [hrank, hm, pow_one, hq] at hI
  let e₁ : (Over.mk (𝟙 (Sp k)) ⟶ K) ≃ {s : Sp k ⟶ K.left // s ≫ K.hom = 𝟙 (Sp k)} :=
    { toFun := fun g => ⟨g.left, by simpa using Over.w g⟩
      invFun := fun s => Over.homMk s.1 (by simpa using s.2)
      left_inv := fun g => Over.OverMorphism.ext rfl
      right_inv := fun s => rfl }
  let e₂ := GlobalTheory.UPel.HT.ES.OrdCount.subEquiv (T := Over.mk (𝟙 (Sp k))) i
    (fun g : Over.mk (𝟙 (Sp k)) ⟶ o.A => KilledBy o w g) (hKiff _)
  have hcard : Nat.card {s : Sp k ⟶ K.left // s ≫ K.hom = 𝟙 (Sp k)} =
      Nat.card {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // KilledBy o w g} :=
    (Nat.card_congr e₁.symm).trans (Nat.card_congr e₂)
  rw [hcard] at hI
  set M := Nat.card {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // KilledBy o w g} with hM
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, zero_mul] at hI
    exact pow_ne_zero _ hPne (by exact_mod_cast hI)
  obtain ⟨L, hL⟩ : ∃ L : ℕ, Module.length B B = L := by
    have hne : Module.length B B ≠ ⊤ := by
      intro htop
      rw [htop, ENat.mul_top (by exact_mod_cast hM0)] at hI
      exact ENat.coe_ne_top _ hI
    obtain ⟨L, hL⟩ := ENat.ne_top_iff_exists.mp hne
    exact ⟨L, hL.symm⟩
  rw [hL] at hI
  have hIN : (p ^ f) ^ D.n = M * L := by exact_mod_cast hI
  let ψ := o.act.act (algebraMap (𝓞 D.F) D.O ((p : ℕ) : 𝓞 D.F))
  have eψ : {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} ≃
      {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // KilledBy o w g} :=
    Equiv.subtypeEquivRight fun g => ⟨fun h => h.2, fun h => ⟨h _ hpw, h⟩⟩
  haveI : Finite {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // KilledBy o w g} := Nat.finite_of_card_ne_zero hM0
  haveI : Finite {g : Over.mk (𝟙 (Sp k)) ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} := Finite.of_equiv _ eψ.symm
  obtain ⟨j', hj'⟩ := GlobalTheory.UPel.HT.ES.card_kerW_eq_pow o o ψ (o.act.hom _)
    (fun a => by rw [← o.act.mul, ← o.act.mul, ← map_mul, ← map_mul, mul_comm]) w hwM (𝟙 (Sp k)) inferInstance
  have hMpow : M = (p ^ f) ^ j' := by
    rw [hM, ← Nat.card_congr eψ, hj', hq]
  obtain ⟨⟨v₀, hv₀t, hv₀1, hv₀k⟩, hline⟩ :=
    UpperTheory.Gal.Ord.CntLie.lie_line p D R b N hN hNp hm k hk β o i₀ w f hw hq hf π
  obtain ⟨v₀', hv₀'⟩ := (hKiff _ v₀).mpr hv₀k
  have hv₀'t : IsTangent v₀' := by
    unfold IsTangent at hv₀t ⊢
    apply (cancel_mono i.left).mp
    rw [Category.assoc, ← Over.comp_left, hv₀', hv₀t, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨u₀, hu₀⟩ := hfac v₀' hv₀'t
  have hL1 : L ≠ 1 := by
    intro hL1
    have hlen1 : Module.length B B = 1 := by rw [hL, hL1]; rfl
    have hu := UpperTheory.Gal.Ord.CntPt.const_of_length hlen1 c u₀
    apply hv₀1
    rw [← hv₀', ← hu₀, hu, Category.assoc]
    exact UpperTheory.Gal.Ord.CntPt.const_eq_one z c hzc
  have hdim : ∀ (u v : B →ₐ[k] DualNumber k), (∃ x, TrivSqZeroExt.snd (u x) ≠ 0) →
      ∃ l : k, ∀ x, TrivSqZeroExt.snd (v x) = l * TrivSqZeroExt.snd (u x) := by
    intro u v ⟨x, hx⟩
    have h1 : spOver u ≫ z ≠ 1 := fun h => hx (UpperTheory.Gal.Ord.CntPt.eq_const_of_one z hzMono c hzc u h x)
    obtain ⟨l, hl⟩ := hline _ _ (UpperTheory.Gal.Ord.CntPt.tangent_of z c hzc u) (UpperTheory.Gal.Ord.CntPt.tangent_of z c hzc v)
      (hkill u) (hkill v) h1
    rw [UpperTheory.Gal.Ord.CntPt.scale_comp] at hl
    have hv := UpperTheory.Gal.Ord.CntPt.spOver_inj z hzMono hl
    refine ⟨l, fun x => ?_⟩
    rw [hv]
    exact UpperTheory.Gal.Ord.CntPt.snd_scA l (u x)
  by_cases hlt : ((p ^ f : ℕ) : ℕ∞) < Module.length B B
  · right
    obtain ⟨T, _, _, τ, j, u, hj, hpow, x, hx⟩ := UpperTheory.Gal.Ord.art p k B f hf hdim hlt
    refine ⟨spOver (τ.comp u) ≫ z, UpperTheory.Gal.Ord.CntPt.tangent_of z c hzc _,
      fun h => hx (UpperTheory.Gal.Ord.CntPt.eq_const_of_one z hzMono c hzc _ h x),
      T, inferInstance, inferInstance, τ, j, spOver u ≫ z, hj, hpow, hkill u, ?_⟩
    rw [← spOver_comp, Category.assoc]
    rfl
  · left
    push_neg at hlt
    have hLle : L ≤ p ^ f := by
      rw [hL] at hlt
      exact_mod_cast hlt
    have hL0 : L ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hIN
      exact pow_ne_zero _ hPne hIN
    have hjle : j' ≤ D.n := by
      by_contra hcon
      push_neg at hcon
      have h1 : (p ^ f) ^ D.n < (p ^ f) ^ j' := Nat.pow_lt_pow_right hP2 hcon
      have h2 : (p ^ f) ^ j' ≤ (p ^ f) ^ j' * L := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hL0)
      rw [hIN, hMpow] at h1
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
    have hLeq : L = (p ^ f) ^ (D.n - j') := by
      have h3 : (p ^ f) ^ D.n = (p ^ f) ^ j' * (p ^ f) ^ (D.n - j') := by
        rw [← pow_add, Nat.add_sub_cancel' hjle]
      rw [hIN, hMpow] at h3
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hPne) j') h3
    have hd : D.n - j' = 1 := by
      rcases Nat.lt_trichotomy (D.n - j') 1 with h | h | h
      · exfalso
        apply hL1
        rw [hLeq, Nat.lt_one_iff.mp h, pow_zero]
      · exact h
      · exfalso
        have h4 : (p ^ f) ^ 2 ≤ (p ^ f) ^ (D.n - j') := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hPne) h
        have h5 : p ^ f < (p ^ f) ^ 2 := by
          rw [pow_two]
          nlinarith
        have h6 : (p ^ f) ^ (D.n - j') ≤ p ^ f := by
          rw [← hLeq]
          exact hLle
        exact absurd (lt_of_lt_of_le h5 (h4.trans h6)) (lt_irrefl _)
    have hjn : j' = D.n - 1 := by omega
    refine ⟨inferInstance, hwP, hpw, ?_⟩
    show M = _
    rw [hMpow, hjn, hm, Nat.one_mul, hq]
