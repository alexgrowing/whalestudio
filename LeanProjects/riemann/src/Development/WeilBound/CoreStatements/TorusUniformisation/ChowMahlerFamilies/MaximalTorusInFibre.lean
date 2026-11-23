import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.IBIsKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.MaximalTorusFibre

open GlobalTheory.TorusToProper ReciprocityTheory.ChartRestriction.G.Out.GtBCPf ReciprocityTheory.ChartRestriction.G.Out.PullGtPf

variable {K : Type} [Field K] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

theorem pt_inj (R : Type) [CommRing R] [Algebra K R] : Function.Injective (pt K X R) := by
  intro θ θ' h
  have h1 : Spec.map (CommRingCat.ofHom (charRing X R θ)) =
      Spec.map (CommRingCat.ofHom (charRing X R θ')) := by
    rw [← ptFun_fst (K := K), ← ptFun_fst (K := K)]
    exact congrArg (fun t => Over.Hom.left t ≫ Rosenlicht.torusFst _ X) h
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  ext x
  have h3 := congrArg (fun f => f (AddMonoidAlgebra.single x 1)) h2
  simpa [charRing_single] using h3

theorem pt_surj (R : Type) [CommRing R] [Algebra K R] : Function.Surjective (pt K X R) := by
  intro t
  obtain ⟨f, hf⟩ := Spec.map_surjective
    (Over.Hom.left t ≫ Rosenlicht.torusFst (Spec (CommRingCat.of K)) X)
  let θ : Multiplicative X →* Rˣ :=
    (Units.map (f.hom : AddMonoidAlgebra (ULift.{0} ℤ) X →+* R).toMonoidHom).comp
      (AddMonoidAlgebra.of (ULift.{0} ℤ) X).toHomUnits
  refine ⟨θ, torus_ext ?_⟩
  show Over.Hom.left (ptFun K X R θ) ≫ _ = _
  rw [ptFun_fst, ← hf]
  congr 1
  ext1
  have hU : ∀ (a b : ULift.{0} ℤ →+* R), a = b := by
    intro a b
    ext r
    obtain ⟨n⟩ := r
    have e : (ULift.up n : ULift.{0} ℤ) = (n : ULift.{0} ℤ) := by ext; simp
    rw [e, map_intCast, map_intCast]
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    exact congrArg (fun g : ULift.{0} ℤ →+* R => g r)
      (hU ((charRing X R θ).comp AddMonoidAlgebra.singleZeroRingHom)
        ((f.hom : AddMonoidAlgebra (ULift.{0} ℤ) X →+* R).comp AddMonoidAlgebra.singleZeroRingHom))
  · intro m
    simp [charRing_single, θ]

theorem pt_eq_spm (R : Type) [CommRing R] [Algebra K R] (θ : Multiplicative X →* Rˣ) :
    (Units.map ((AddMonoidAlgebra.lift K R X ((Units.coeHom R).comp θ) : AddMonoidAlgebra K X →ₐ[K] R) :
      AddMonoidAlgebra K X →* R)).comp (univ K X) = θ := by
  ext x
  simp [univ]

theorem exists_char [Module.Free ℤ X] [Module.Finite ℤ X]
    (w : splitTorus (Sp K) X ⟶ splitTorus (Sp K) Y) (hw : (1 : sp K K ⟶ _) ≫ w = 1) :
    ∃ φ : Y →+ X, ∀ (R : Type) [CommRing R] [Algebra K R] (θ : Multiplicative X →* Rˣ),
      pt K X R θ ≫ w = pt K Y R (θ.comp (AddMonoidHom.toMultiplicative φ)) := by
  classical
  obtain ⟨ψ, hψ⟩ := pt_surj (K := K) (X := Y) (AddMonoidAlgebra K X)
    (pt K X (AddMonoidAlgebra K X) (univ K X) ≫ w)
  have hunit : ∀ y : Y, ∃ (a : X) (c : K), IsUnit c ∧
      ((ψ (Multiplicative.ofAdd y) : (AddMonoidAlgebra K X)ˣ) : AddMonoidAlgebra K X) =
        AddMonoidAlgebra.single a c :=
    fun y => Rosenlicht.isUnit_eq_single (Units.isUnit _)
  choose f c hc hfc using hunit
  let ε : AddMonoidAlgebra K X →ₐ[K] K :=
    AddMonoidAlgebra.lift K K X ((Units.coeHom K).comp (1 : Multiplicative X →* Kˣ))
  have hε1 : (Units.map (ε : AddMonoidAlgebra K X →* K)).comp (univ K X) = 1 :=
    pt_eq_spm (K := K) (X := X) K 1
  have h1 : spm ε ≫ pt K X (AddMonoidAlgebra K X) (univ K X) = 1 := by
    rw [← pt_nat, hε1, map_one]
  have hε : (Units.map (ε : AddMonoidAlgebra K X →* K)).comp ψ = 1 := by
    apply pt_inj (K := K) (X := Y) K
    rw [pt_nat, hψ, ← Category.assoc, h1, map_one]
    exact hw
  have hc1 : ∀ y, c y = 1 := by
    intro y
    have h2 := congrArg (fun g => ((g (Multiplicative.ofAdd y) : Kˣ) : K)) hε
    simpa [ε, hfc, AddMonoidAlgebra.lift_single] using h2
  have hψs : ∀ y, ((ψ (Multiplicative.ofAdd y) : (AddMonoidAlgebra K X)ˣ) : AddMonoidAlgebra K X) =
      AddMonoidAlgebra.single (f y) 1 := fun y => by rw [hfc, hc1]
  have hadd : ∀ y y', f (y + y') = f y + f y' := by
    intro y y'
    have h := congrArg (fun u : (AddMonoidAlgebra K X)ˣ => (u : AddMonoidAlgebra K X))
      (map_mul ψ (Multiplicative.ofAdd y) (Multiplicative.ofAdd y'))
    simp only [Units.val_mul, ← ofAdd_add, hψs, AddMonoidAlgebra.single_mul_single] at h
    rw [show (1 : K) * 1 = 1 from mul_one 1] at h
    exact (AddMonoidAlgebra.single_left_inj (one_ne_zero (α := K))).mp h
  refine ⟨AddMonoidHom.mk' f hadd, ?_⟩
  intro R _ _ θ
  let L : AddMonoidAlgebra K X →ₐ[K] R := AddMonoidAlgebra.lift K R X ((Units.coeHom R).comp θ)
  have hL : (Units.map (L : AddMonoidAlgebra K X →* R)).comp (univ K X) = θ := pt_eq_spm R θ
  have e1 : pt K X R θ = spm L ≫ pt K X (AddMonoidAlgebra K X) (univ K X) := by
    rw [← pt_nat, hL]
  rw [e1, Category.assoc, ← hψ, ← pt_nat]
  congr 1
  ext y
  simp [L, hψs, AddMonoidAlgebra.lift_single]

theorem surj_of_inj (φ : Y →+ X)
    (h : ∀ (R : Type) [CommRing R] [Algebra K R] (θ : Multiplicative X →* Rˣ),
      θ.comp (AddMonoidHom.toMultiplicative φ) = 1 → θ = 1) : Function.Surjective φ := by
  classical
  let Q := X ⧸ φ.range
  let θ : Multiplicative X →* (AddMonoidAlgebra K Q)ˣ :=
    (univ K Q).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' φ.range))
  have hθ : θ = 1 := by
    refine h (AddMonoidAlgebra K Q) θ ?_
    refine MonoidHom.ext fun y => Units.ext ?_
    have hy : (QuotientAddGroup.mk' φ.range) (φ (Multiplicative.toAdd y)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨_, rfl⟩
    simp [θ, univ, AddMonoidAlgebra.one_def, AddMonoidAlgebra.of_apply, hy]
  intro x
  have h3 := congrArg (fun f => ((f (Multiplicative.ofAdd x) : (AddMonoidAlgebra K Q)ˣ) :
    AddMonoidAlgebra K Q)) hθ
  simp only [θ, univ, MonoidHom.comp_apply, MonoidHom.one_apply, Units.val_one,
    MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply, AddMonoidAlgebra.one_def] at h3
  have h4 : (QuotientAddGroup.mk' φ.range) x = 0 :=
    (AddMonoidAlgebra.single_left_inj (one_ne_zero (α := K))).mp h3
  obtain ⟨y, hy⟩ := (QuotientAddGroup.eq_zero_iff x).mp h4
  exact ⟨y, hy⟩

theorem inj_of_surj [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (φ : Y →+ X) (hφ : Function.Surjective φ) (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) :
    Function.Injective φ := by
  have hle : Module.finrank ℤ X ≤ Module.finrank ℤ Y :=
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toIntLinearMap) hφ
  let e : X ≃ₗ[ℤ] Y := LinearEquiv.ofFinrankEq X Y (le_antisymm hle hr)
  have hs : Function.Surjective (e.toLinearMap ∘ₗ φ.toIntLinearMap) :=
    e.surjective.comp hφ
  have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs
  intro a b hab
  exact hi (by simp [hab])

theorem field_case [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over (Sp K)} [GrpObj G]
    (v : splitTorus (Sp K) X ⟶ G) [IsMonHom v]
    (hv : ∀ (A : Type) [CommRing A] [Algebra K A] (t : sp K A ⟶ splitTorus (Sp K) X), t ≫ v = 1 → t = 1)
    (τ : TorusExtension G) (hr : letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X)
    (A : Type) [CommRing A] [Algebra K A] (p : sp K A ⟶ G) :
    letI := τ.grpB; p ≫ τ.q = 1 ↔ ∃ t : sp K A ⟶ splitTorus (Sp K) X, t ≫ v = p := by
  letI := τ.addCommGroup
  haveI := τ.free
  haveI := τ.finite
  letI := τ.grpB
  haveI := τ.q_hom
  haveI := τ.i_hom
  haveI : IsProper τ.B.hom := τ.isAbelian.proper
  have hvq : v ≫ τ.q = toUnit _ ≫ η :=
    GlobalTheory.splitTorus_hom_proper_trivial_field K X τ.B (v ≫ τ.q) inferInstance
  let w := τ.isKernel.lift v (toUnit _) hvq
  have hwv : w ≫ τ.i = v := τ.isKernel.lift_fst _ _ _
  haveI : Mono τ.i := τ.isKernel.mono_fst_of_mono
  have hw1 : (1 : sp K K ⟶ _) ≫ w = 1 := by
    apply (cancel_mono τ.i).mp
    rw [Category.assoc, hwv, MonObj.one_comp, MonObj.one_comp]
  obtain ⟨φ, hφ⟩ := exists_char w hw1
  have hsurj : Function.Surjective φ := by
    apply surj_of_inj (K := K) φ
    intro R _ _ θ hθ
    apply pt_inj (K := K) (X := X) R
    rw [map_one]
    apply hv R
    rw [← hwv, ← Category.assoc, hφ, hθ, map_one, MonObj.one_comp]
  have hinj := inj_of_surj φ hsurj hr
  constructor
  · intro hp
    let s := τ.isKernel.lift p (toUnit _) hp
    have hs : s ≫ τ.i = p := τ.isKernel.lift_fst _ _ _
    obtain ⟨σ, hσ⟩ := pt_surj (K := K) (X := τ.X) A s
    let e : τ.X ≃+ X := AddEquiv.ofBijective φ ⟨hinj, hsurj⟩
    have he : ∀ y, e.symm (φ y) = y := fun y => e.symm_apply_apply y
    refine ⟨pt K X A (σ.comp (AddMonoidHom.toMultiplicative (e.symm : X →+ τ.X))), ?_⟩
    have hcomp : (σ.comp (AddMonoidHom.toMultiplicative (e.symm : X →+ τ.X))).comp
        (AddMonoidHom.toMultiplicative φ) = σ := by
      ext y
      simp [he]
    rw [← hwv, ← Category.assoc, hφ, hcomp, hσ, hs]
  · rintro ⟨t, rfl⟩
    rw [Category.assoc, hvq]
    exact MonObj.comp_one t

end PositivityTheory.Xgn.MaximalTorusFibre

open PositivityTheory.Xgn.MaximalTorusFibre GlobalTheory.TorusToProper ReciprocityTheory.ChartRestriction.G.Out.GtBCPf ReciprocityTheory.ChartRestriction.G.Out.PullGtPf in
theorem PositivityTheory.Xgn.maximal_torus_in_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ := by
  intro S G _ X _ _ _ u _ k _ x hu Gk _ ψ hψ τ hr A _ g p
  letI : Algebra k A := g.toAlgebra
  have one_left : ∀ {T : Scheme.{0}} (Z M : Over T) [GrpObj M],
      (1 : Z ⟶ M).left = Z.hom ≫ (η : 𝟙_ (Over T) ⟶ M).left := by
    intro T Z M _
    show (toUnit Z ≫ η).left = _
    rw [Over.comp_left, toUnit_left']
  have gT := grpT x X
  have hTsnd := hT_snd x X
  have hcond : (hT x X ≫ u.left) ≫ G.hom = (splitTorus (Sp k) X).hom ≫ x := by
    rw [Category.assoc, Over.w u, hTsnd]
  let v : splitTorus (Sp k) X ⟶ Gk :=
    Over.homMk (hψ.1.lift (hT x X ≫ u.left) (splitTorus (Sp k) X).hom hcond) (hψ.1.lift_snd _ _ _)
  have hvψ : v.left ≫ ψ = hT x X ≫ u.left := hψ.1.lift_fst _ _ _
  haveI : IsMonHom v := isMonHom_of_grpPullback gT hψ u v hvψ
  have toS : ∀ (B : Type) [CommRing B] [Algebra k B] (t' : sp k B ⟶ splitTorus (Sp k) X),
      (t'.left ≫ hT x X) ≫ (splitTorus S X).hom =
        (Over.mk (spMap (algebraMap k B) ≫ x)).hom := by
    intro B _ _ t'
    rw [Category.assoc, hTsnd, ← Category.assoc, Over.w t']
    rfl
  have hv : ∀ (B : Type) [CommRing B] [Algebra k B] (t' : sp k B ⟶ splitTorus (Sp k) X),
      t' ≫ v = 1 → t' = 1 := by
    intro B _ _ t' ht'
    let t : Over.mk (spMap (algebraMap k B) ≫ x) ⟶ splitTorus S X :=
      Over.homMk (t'.left ≫ hT x X) (toS B t')
    have ht1 : t ≫ u = 1 := by
      ext1
      rw [Over.comp_left, one_left]
      show (t'.left ≫ hT x X) ≫ u.left = _
      rw [Category.assoc, ← hvψ, ← Category.assoc, ← Over.comp_left, ht', one_left,
        Category.assoc, IsGrpPullback.one_left hψ]
      simp only [Over.mk_hom, Category.assoc]
    have ht := hu B (algebraMap k B) t ht1
    ext1
    apply gT.1.hom_ext
    · have h2 := congrArg (fun s => Over.Hom.left s) ht
      rw [show t'.left ≫ hT x X = t.left from rfl, h2, one_left, one_left, Category.assoc,
        IsGrpPullback.one_left gT]
      simp only [Over.mk_hom, Category.assoc]
    · rw [Over.w t', Over.w (1 : sp k B ⟶ splitTorus (Sp k) X)]
  have key := field_case (K := k) v hv τ hr A p
  rw [key]
  constructor
  · rintro ⟨t', rfl⟩
    refine ⟨Over.homMk (t'.left ≫ hT x X) (toS A t'), ?_⟩
    rw [Over.comp_left, Over.comp_left]
    show (t'.left ≫ hT x X) ≫ u.left = (t'.left ≫ v.left) ≫ ψ
    rw [Category.assoc, Category.assoc, hvψ]
  · rintro ⟨t, ht⟩
    let L := gT.1.lift t.left (spMap g) (Over.w t)
    have hL1 : L ≫ hT x X = t.left := gT.1.lift_fst _ _ _
    have hL2 : L ≫ (splitTorus (Sp k) X).hom = spMap g := gT.1.lift_snd _ _ _
    refine ⟨Over.homMk L hL2, ?_⟩
    ext1
    apply hψ.1.hom_ext
    · show (L ≫ v.left) ≫ ψ = p.left ≫ ψ
      rw [Category.assoc, hvψ, ← Category.assoc, hL1, ← Over.comp_left, ht]
    · show (L ≫ v.left) ≫ Gk.hom = p.left ≫ Gk.hom
      rw [Category.assoc, Over.w v, hL2]
      exact (Over.w p).symm
