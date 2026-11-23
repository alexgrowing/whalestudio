import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelianStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHolPtsOfFamExp
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.Lat

open GlobalTheory.CompanionTheory.Ar.Flat

section Points

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

def ptU (h : IsGrpPullback G' G f φ) {T : Over S} (c : T ⟶ Over.mk ((𝟙_ (Over S')).hom ≫ f)) :
    (𝟙_ (Over S') ⟶ G') →* (T ⟶ G) :=
  MonoidHom.mk' (fun s => c ≫ GlobalTheory.ZH.TorusPerp.ptHom h _ s) fun s s' => by
    rw [map_mul, MonObj.comp_mul]

theorem ptU_bijective (h : IsGrpPullback G' G f φ) {T : Over S} (c : T ⟶ Over.mk ((𝟙_ (Over S')).hom ≫ f))
    [IsIso c] : Function.Bijective (ptU h c) := by
  have hb := GlobalTheory.ZH.TorusPerp.ptHom_bijective h (𝟙_ (Over S'))
  refine ⟨fun a a' e => hb.1 ((cancel_epi c).1 e), fun x => ?_⟩
  obtain ⟨s, hs⟩ := hb.2 (inv c ≫ x)
  refine ⟨s, ?_⟩
  show c ≫ _ = x
  rw [hs, IsIso.hom_inv_id_assoc]

end Points

section Fibre

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

def fibreExp (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    FamExp G M (Set.univ : Set (Fin 0 → ℂ)) (fun _ => ψ b) where
  ex _ := e.ex b
  add _ _ := e.add b hb
  hol := by
    refine GlobalTheory.LocLift.isHolTo_comp e.hol (C := Set.univ ×ˢ Set.univ)
      (β := fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (b, bz.2)) (isOpen_univ.prod isOpen_univ) ?_ ?_
    · exact ((differentiable_const b).prodMk differentiable_snd).differentiableOn
    · exact fun _ _ => ⟨hb, trivial⟩
  diff _ _ := e.diff b hb
  log b' _ := by
    obtain ⟨V, N, f, L, hV, hL, h1, h2⟩ := e.log b hb
    refine ⟨V, N, f, fun p => L (b, p.2), hV, ?_, ?_, ?_⟩
    · exact AnalyticAt.comp (f := fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) hL
        (analyticAt_const.prod analyticAt_snd)
    · have hc : Tendsto (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (b, bz.2)) (𝓝 (b', 0)) (𝓝 (b, 0)) :=
        (continuous_const.prodMk continuous_snd).tendsto' _ _ rfl
      exact hc.eventually h1
    · have hc : Tendsto (fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2))
          (𝓝 (b', fun j => valAt' (e.ex b 0).left V (f j))) (𝓝 (b, fun j => valAt' (e.ex b 0).left V (f j))) :=
        (continuous_const.prodMk continuous_snd).tendsto' _ _ rfl
      exact hc.eventually h2

theorem exists_lift_fibre [IsCommMonObj G] (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) {m : ℕ}
    (u : (Fin m → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)) (hadd : ∀ z w, u (z + w) = u z * u w)
    (hhol : IsHolTo Set.univ (fun z => (u z).left)) :
    ∃ h : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e.ex b (h z) = u z := by
  obtain ⟨h, -, H⟩ := exists_linear_lift_of_additive_family R G g 0 M Set.univ (fun _ => ψ b) (fibreExp e hb) m
    Set.univ (fun _ => u) isOpen_univ subset_rfl (fun _ _ => hadd)
    (GlobalTheory.LocLift.isHolTo_comp hhol (C := Set.univ ×ˢ Set.univ)
      (β := fun bz : (Fin 0 → ℂ) × (Fin m → ℂ) => bz.2) (isOpen_univ.prod isOpen_univ)
      differentiable_snd.differentiableOn (fun _ _ => trivial))
  exact ⟨h 0, (H 0 trivial).1⟩

end Fibre

section Core

variable {Gk F Ab Au : Type} [Group Gk] [Group F] [Group Ab] [Group Au] {g g' : ℕ}

theorem core (P₁ : Gk →* F) (hP₁ : Function.Bijective P₁) (D : Au →* Ab) (hD : Function.Injective D)
    (Q : Gk →* Ab) (hQ : Function.Surjective Q) (ex : (Fin g → ℂ) → F)
    (hadd : ∀ z w, ex (z + w) = ex z * ex w) (hex : Function.Surjective ex)
    (uex : (Fin g' → ℂ) → Au) (uadd : ∀ z w, uex (z + w) = uex z * uex w)
    (Λ : Submodule ℤ (Fin g' → ℂ)) (ker : ∀ z, uex z = 1 ↔ z ∈ Λ) [DiscreteTopology Λ]
    (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hl : ∀ y s, P₁ s = ex y → D (uex (ℓ y)) = Q s)
    (hker : ∀ s, Q s = 1 → ∃ (d : ℕ) (h : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (δ : Fin d → ℂ), ex (h δ) = P₁ s ∧
      ∀ z, ∃ s', P₁ s' = ex (h z) ∧ Q s' = 1) :
    (∀ y, ex y = 1 → ℓ y ∈ Λ) ∧ ∀ p ∈ Λ, ∃ y, ex y = 1 ∧ ℓ y = p := by
  have hu1 : ∀ z, D (uex z) = 1 → z ∈ Λ := fun z hz =>
    (ker z).1 (hD (hz.trans (map_one D).symm))
  have hsub : ∀ w v, uex v = uex w → w - v ∈ Λ := by
    intro w v hv
    refine (ker _).1 ?_
    have := uadd (w - v) v
    rw [sub_add_cancel, hv] at this
    exact (mul_eq_right.1 this.symm)
  have hrange : LinearMap.range ℓ = ⊤ := by
    refine GlobalTheory.AHWeil.eq_top_of_add_discrete Λ _ fun w => ?_
    obtain ⟨s, hs⟩ := hQ (D (uex w))
    obtain ⟨y, hy⟩ := hex (P₁ s)
    have h1 : uex (ℓ y) = uex w := hD ((hl y s hy.symm).trans hs)
    refine ⟨⟨w - ℓ y, hsub w _ h1⟩, ⟨y, ?_⟩⟩
    simp
  refine ⟨fun y hy => hu1 _ ?_, fun p hp => ?_⟩
  · rw [hl y 1 (by rw [map_one, hy]), map_one]
  · obtain ⟨y, rfl⟩ := LinearMap.range_eq_top.1 hrange p
    obtain ⟨s, hs⟩ := hP₁.2 (ex y)
    have hQs : Q s = 1 := by
      rw [← hl y s hs, (ker _).2 hp, map_one]
    obtain ⟨d, h, δ, h1, h2⟩ := hker s hQs
    have hmem : ∀ z, ℓ (h z) ∈ Λ := fun z => by
      obtain ⟨s', e1, e2⟩ := h2 z
      exact hu1 _ ((hl _ s' e1).trans e2)
    have hcont : Continuous fun z => (⟨ℓ (h z), hmem z⟩ : Λ) :=
      Continuous.subtype_mk ((LinearMap.continuous_of_finiteDimensional (ℓ ∘ₗ h))) _
    have hconst := PreconnectedSpace.constant (α := Fin d → ℂ) inferInstance hcont (x := δ) (y := 0)
    have hz : ℓ (h δ) = 0 := by
      have := congrArg Subtype.val hconst
      simpa using this
    refine ⟨y - h δ, ?_, by simp [hz]⟩
    have := hadd (y - h δ) (h δ)
    rw [sub_add_cancel, h1, hs] at this
    exact mul_eq_right.1 this.symm

end Core

section Torus

open GlobalTheory.SplitTorus ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.CompanionTheory.Ar.Flat.GaExp
open AddMonoidAlgebra (single)

variable {X : Type} [AddCommGroup X]

def torusPt (c : X →+ Additive ℂˣ) : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X :=
  ofVal ((MonoidHom.toAdditive
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.toMonoidHom)).comp c)

def chHom (τ : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X) : X →+ Additive ℂˣ :=
  (MonoidHom.toAdditive (Units.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.toMonoidHom)).comp (valHom τ)

theorem val_torusPt (c : X →+ Additive ℂˣ) (a : X) :
    GlobalTheory.SplitTorus.val (torusPt c) a = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (((c a).toMul : ℂˣ) : ℂ) := by
  rw [torusPt, val_ofVal]
  rfl

theorem torusPt_chHom (τ : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X) : torusPt (chHom τ) = τ := by
  refine hom_ext fun a => ?_
  rw [val_torusPt]
  exact CategoryTheory.Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) (GlobalTheory.SplitTorus.val τ a)

theorem torusPt_add (c c' : X →+ Additive ℂˣ) : torusPt (c + c') = torusPt c * torusPt c' := by
  refine hom_ext fun a => ?_
  rw [GlobalTheory.SplitTorus.val_mul, val_torusPt, val_torusPt, val_torusPt, ← map_mul]
  rfl

theorem isHolTo_torusPt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : V → X →+ Additive ℂˣ)
    (hc : ∀ a, Differentiable ℂ fun z => (((c z a).toMul : ℂˣ) : ℂ)) :
    IsHolTo Set.univ (fun z => (torusPt (c z)).left) := by
  refine GlobalTheory.HolFibre.isHolTo_of_isPullback (s := (splitTorusAff ZU X).hom) (t := toZ (Sp ℂ))
    (IsPullback.of_hasPullback _ _) ?_ ?_
  · have : IsAffine (splitTorusAff ZU X).left := inferInstanceAs (IsAffine (Spec (torusRing ZU X)))
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_affine isOpen_univ fun r => ?_
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (torusRing ZU X)).inv).2 r
    let φ : V → torusRing ZU X →+* ℂ := fun z =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (coord (torusPt (c z))).hom
    have hs : ∀ z x, φ z (single x 1) = (((c z x).toMul : ℂˣ) : ℂ) := by
      intro z x
      have := val_torusPt (c z) x
      show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (GlobalTheory.SplitTorus.val (torusPt (c z)) x) = _
      rw [this]
      exact CategoryTheory.Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) _
    suffices hd : Differentiable ℂ (fun z => φ z a) from
      hd.differentiableOn.congr fun z _ => GlobalTheory.CompanionTheory.Ar.Flat.GaExp.valAt'_top _ _
    induction a using AddMonoidAlgebra.induction_on with
    | of x =>
      simp only [AddMonoidAlgebra.of_apply, hs]
      exact hc x
    | add a a' h h' =>
      simp only [map_add]
      exact h.add h'
    | smul r a h =>
      have : ∀ z, φ z (r • a) = (r.down : ℂ) * φ z a := by
        intro z
        have e : r • a = r.down • a := by
          ext x
          simp
        rw [e, map_zsmul, zsmul_eq_mul]
      simp only [this]
      exact h.const_mul _
  · refine GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const isOpen_univ (𝟙 (Sp ℂ))) fun z _ => ?_
    exact Over.w (torusPt (c z))

theorem exists_torus_family [Module.Free ℤ X] [Module.Finite ℤ X]
    (τ : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X) :
    ∃ (d : ℕ) (T : (Fin d → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X)) (δ : Fin d → ℂ),
      (∀ z w, T (z + w) = T z * T w) ∧ IsHolTo Set.univ (fun z => (T z).left) ∧ T δ = τ := by
  let bs := Module.finBasis ℤ X
  let lin : (Fin (Module.finrank ℤ X) → ℂ) → X → ℂ := fun z x => ∑ i, ((bs.repr x i : ℤ) : ℂ) * z i
  have lin_add : ∀ z x y, lin z (x + y) = lin z x + lin z y := by
    intro z x y
    simp [lin, add_mul, Finset.sum_add_distrib]
  have lin_addz : ∀ z w x, lin (z + w) x = lin z x + lin w x := by
    intro z w x
    simp [lin, mul_add, Finset.sum_add_distrib]
  let c : (Fin (Module.finrank ℤ X) → ℂ) → X →+ Additive ℂˣ := fun z =>
    AddMonoidHom.mk' (fun x => Additive.ofMul (Units.mk0 (Complex.exp (lin z x)) (Complex.exp_ne_zero _)))
      fun x y => by
        apply Additive.toMul.injective
        apply Units.ext
        simp [lin_add, Complex.exp_add]
  have hcv : ∀ z x, (((c z x).toMul : ℂˣ) : ℂ) = Complex.exp (lin z x) := fun _ _ => rfl
  refine ⟨_, fun z => torusPt (c z), fun i => Complex.log ((((chHom τ (bs i)).toMul : ℂˣ)) : ℂ), ?_, ?_, ?_⟩
  · intro z w
    have key : c (z + w) = c z + c w := by
      refine AddMonoidHom.ext fun x => Additive.toMul.injective (Units.ext ?_)
      show Complex.exp (lin (z + w) x) = Complex.exp (lin z x) * Complex.exp (lin w x)
      rw [lin_addz, Complex.exp_add]
    show torusPt (c (z + w)) = torusPt (c z) * torusPt (c w)
    rw [key, torusPt_add]
  · refine isHolTo_torusPt c fun a => ?_
    simp only [hcv]
    refine Differentiable.cexp ?_
    simp only [lin]
    fun_prop
  · have key : c (fun i => Complex.log ((((chHom τ (bs i)).toMul : ℂˣ)) : ℂ)) = chHom τ := by
      refine AddMonoidHom.toIntLinearMap_injective (bs.ext fun i => ?_)
      refine Additive.toMul.injective (Units.ext ?_)
      show Complex.exp (lin (fun i => Complex.log ((((chHom τ (bs i)).toMul : ℂˣ)) : ℂ)) (bs i)) = _
      have : lin (fun i => Complex.log ((((chHom τ (bs i)).toMul : ℂˣ)) : ℂ)) (bs i) =
          Complex.log ((((chHom τ (bs i)).toMul : ℂˣ)) : ℂ) := by
        simp [lin, Finsupp.single_apply]
      rw [this, Complex.exp_log (Units.ne_zero _)]
      rfl
    show torusPt (c _) = τ
    rw [key, torusPt_chHom]

end Torus

section Main

theorem exists_pt_of_q {G : Over (Sp ℂ)} [GrpObj G] (τ : TorusExtension G) (x : 𝟙_ (Over (Sp ℂ)) ⟶ τ.B) :
    ∃ s : 𝟙_ (Over (Sp ℂ)) ⟶ G, s ≫ τ.q = x := by
  have hs : Smooth τ.q.left := (GlobalTheory.torusExtension_smooth_geometricallyConnected G τ).1
  have := τ.q_surjective
  obtain ⟨p, hp⟩ := τ.q.left.surjective (x.left (IsLocalRing.closedPoint ℂ))
  obtain ⟨g, hg, -⟩ := GlobalTheory.ZH.LocThetaConv.exists_point (K := ℂ) τ.q.left x.left ⊤ p trivial hp
  have hw : g ≫ G.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [← Over.w τ.q, ← Category.assoc, hg]
    exact Over.w x
  exact ⟨Over.homMk g hw, Over.OverMorphism.ext hg⟩

end Main

end GlobalTheory.CompanionTheory.Ar.QuotLoc.Lat

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open GlobalTheory.CompanionTheory.Ar.QuotLoc.Lat

theorem periods_map_onto_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → (∀ y ∈ e.per b, ℓ y ∈ u.Λ) ∧ ∀ p ∈ u.Λ, ∃ y ∈ e.per b, ℓ y = p := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ ℓ hb hA hAH hP hL
  letI := P.τ.grpB
  letI := P.τ.addCommGroup
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  haveI := u.discrete
  let c₁ : Over.mk (spMap (ψ b)) ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap (ψ b)) :=
    Over.homMk (𝟙 _) (by simp)
  let c₂ : 𝟙_ (Over (Sp ℂ)) ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ 𝟙 (Sp ℂ)) :=
    Over.homMk (𝟙 _) (by simp)
  haveI : IsIso c₁ := by
    refine ⟨Over.homMk (𝟙 _) (by simp), ?_, ?_⟩ <;> exact Over.OverMorphism.ext (Category.id_comp _)
  haveI : IsIso c₂ := by
    refine ⟨Over.homMk (𝟙 _) (by simp), ?_, ?_⟩ <;> exact Over.OverMorphism.ext (Category.id_comp _)
  let P₁ := ptU P.m.cart c₁
  let D := ptU hA c₂
  let Q : (𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G) →* (𝟙_ (Over (Sp ℂ)) ⟶ P.tB.G) :=
    MonoidHom.mk' (fun s => s ≫ P.τ.q ≫ P.e.hom) fun s s' => by
      rw [← Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc]
  have hQ1 : ∀ z : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X, Q (z ≫ P.τ.i) = 1 := by
    intro z
    have h1 : P.τ.i ≫ P.τ.q = toUnit _ ≫ η := P.τ.isKernel.w
    have h2 : z ≫ P.τ.i ≫ P.τ.q = 1 := by
      rw [h1, ← Category.assoc, Hom.one_def]
      congr 1
      exact toUnit_unique _ _
    show (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = 1
    calc (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = (z ≫ P.τ.i ≫ P.τ.q) ≫ P.e.hom := by simp only [Category.assoc]
      _ = 1 := by rw [h2, MonObj.one_comp]
  have hQ : Function.Surjective Q := fun a => by
    obtain ⟨s, hs⟩ := exists_pt_of_q P.τ (a ≫ P.e.inv)
    refine ⟨s, ?_⟩
    show s ≫ P.τ.q ≫ P.e.hom = a
    rw [← Category.assoc, hs, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hl : ∀ y s, P₁ s = e.ex b y → D (u.ex (ℓ y)) = Q s := by
    intro y s h
    have h1 : s.left ≫ P.m.φ = (e.ex b y).left :=
      (Category.id_comp _).symm.trans (congrArg (fun q => q.left) h)
    exact Over.OverMorphism.ext ((Category.id_comp _).trans (hL y s h1))
  have hker : ∀ s, Q s = 1 → ∃ (d : ℕ) (h : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (δ : Fin d → ℂ),
      e.ex b (h δ) = P₁ s ∧ ∀ z, ∃ s', P₁ s' = e.ex b (h z) ∧ Q s' = 1 := by
    intro s hs
    have h0 : s ≫ P.τ.q = 1 := by
      rw [← cancel_mono P.e.hom, MonObj.one_comp, Category.assoc]
      exact hs
    let τ₀ : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X :=
      P.τ.isKernel.lift s (toUnit _) (by rw [h0, Hom.one_def])
    have hτ : τ₀ ≫ P.τ.i = s := P.τ.isKernel.lift_fst _ _ _
    obtain ⟨d, T, δ, hadd, hhol, hT⟩ := exists_torus_family τ₀
    let v : (Fin d → ℂ) → (Over.mk (spMap (ψ b)) ⟶ t.G) := fun z => P₁ (T z ≫ P.τ.i)
    have vadd : ∀ z w, v (z + w) = v z * v w := fun z w => by
      show P₁ (T (z + w) ≫ P.τ.i) = P₁ (T z ≫ P.τ.i) * P₁ (T w ≫ P.τ.i)
      rw [hadd, MonObj.mul_comp, map_mul]
    have vhol : IsHolTo Set.univ (fun z => (v z).left) :=
      GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.LocLift.isHolTo_comp_hom hhol (P.τ.i.left ≫ P.m.φ)) fun z _ =>
        Category.id_comp _
    obtain ⟨h, hh⟩ := exists_lift_fibre e hb v vadd vhol
    refine ⟨d, h, δ, ?_, fun z => ⟨T z ≫ P.τ.i, (hh z).symm, hQ1 _⟩⟩
    rw [hh]
    show P₁ (T δ ≫ P.τ.i) = _
    rw [hT, hτ]
  exact core P₁ (ptU_bijective _ c₁) D (ptU_bijective hA c₂).1 Q hQ (e.ex b) (e.add b hb)
    (GlobalTheory.T.exponential_surjective_semiabelian R t.G g n M B ψ e t.semi b hb) u.ex u.ex_add u.Λ u.ker ℓ hl hker

end GlobalTheory.CompanionTheory.Ar.QuotLoc
