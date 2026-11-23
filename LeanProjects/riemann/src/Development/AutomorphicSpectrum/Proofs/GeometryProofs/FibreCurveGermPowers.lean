import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenFirstStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreCurveDegreeCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibrePowerFreeConjInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.GermFam

theorem isMapOf_cancel {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {d : ℕ} {O : Type} [CommRing O]
    [StarRing O] {f : R →+* R₁} {g : R₁ →+* R₂} {B : Germ.FB R d O} {B₁ : Germ.FB R₁ d O} {B₂ : Germ.FB R₂ d O}
    (h : IsMapOf f B B₁) (h' : IsMapOf (g.comp f) B B₂) : IsMapOf g B₁ B₂ where
  F := fun i => by rw [h'.F, h.F, MvPowerSeries.map_comp]; rfl
  act := fun a i => by rw [h'.act, h.act, MvPowerSeries.map_comp]; rfl
  ph1 := by rw [h'.ph1, h.ph1, MvPowerSeries.map_comp]; rfl
  ph2 := by rw [h'.ph2, h.ph2, MvPowerSeries.map_comp]; rfl
  sy := by rw [h'.sy, h.sy, MvPowerSeries.map_comp]; rfl
  ad := fun a => by rw [h'.ad, h.ad, MvPowerSeries.map_comp]; rfl

section Lat

variable {Ω : Type} [Field Ω] {A : Subring Ω} {d : ℕ}

theorem mem_stdLat {T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)}
    {x : (Fin d → Ω) × (Fin d → Ω)} (hx : x ∈ stdLat A T) :
    ∃ y : (Fin d → Ω) × (Fin d → Ω), (∀ i, y.1 i ∈ A ∧ y.2 i ∈ A) ∧ x = T y := by
  unfold stdLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, fun i => ⟨A.zero_mem, A.zero_mem⟩, (map_zero T).symm⟩
  | add x x' _ _ h h' =>
    obtain ⟨y, hy, rfl⟩ := h
    obtain ⟨y', hy', rfl⟩ := h'
    exact ⟨y + y', fun i => ⟨A.add_mem (hy i).1 (hy' i).1, A.add_mem (hy i).2 (hy' i).2⟩, (map_add T y y').symm⟩
  | smul c x _ h =>
    obtain ⟨y, hy, rfl⟩ := h
    refine ⟨(c : Ω) • y, fun i => ⟨A.mul_mem c.2 (hy i).1, A.mul_mem c.2 (hy i).2⟩, ?_⟩
    rw [map_smul]
    rfl

theorem trans_integral {T₀ T T' : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)}
    (he : T = T₀ ∘ₗ T') (h0 : Function.Injective T₀) (hl : stdLat A T₀ = stdLat A T)
    (y : (Fin d → Ω) × (Fin d → Ω)) (hy : ∀ i, y.1 i ∈ A ∧ y.2 i ∈ A) :
    ∀ i, (T' y).1 i ∈ A ∧ (T' y).2 i ∈ A := by
  have h1 : T y ∈ stdLat A T := Submodule.subset_span ⟨y, hy, rfl⟩
  rw [← hl] at h1
  obtain ⟨y₁, hy₁, e⟩ := mem_stdLat h1
  have h2 : T' y = y₁ := h0 (by rw [← e, he]; rfl)
  rwa [h2]

theorem entries_mem (φ ψ : Germ.Pt Ω 1 d) (lam : Germ.PS Ω 2 d) (hψφ : lin ψ 1 * lin φ 1 = 1)
    (h : ∀ y : (Fin d → Ω) × (Fin d → Ω), (∀ i, y.1 i ∈ A ∧ y.2 i ∈ A) →
      ∀ i, (transH φ ψ lam y).1 i ∈ A ∧ (transH φ ψ lam y).2 i ∈ A) (a b : Fin d) :
    lin φ 1 a b ∈ A ∧ lin ψ 1 a b ∈ A ∧ bil lam 1 1 a b ∈ A := by
  classical
  have hs : ∀ (l : Fin d) (i : Fin d), (Pi.single l 1 : Fin d → Ω) i ∈ A := fun l i => by
    by_cases e : i = l
    · subst e; simpa using A.one_mem
    · simpa [Pi.single_apply, e] using A.zero_mem
  have h1 : ∀ a b, lin φ 1 a b ∈ A := fun a b => by
    have := (h (Pi.single b 1, 0) (fun i => ⟨hs b i, A.zero_mem⟩) a).1
    simpa [transH_apply] using this
  have h2 : ∀ a b, lin ψ 1 a b ∈ A := fun a b => by
    have := (h (0, Pi.single a 1) (fun i => ⟨A.zero_mem, hs a i⟩) b).2
    simpa [transH_apply] using this
  have h3 : ∀ a b, ((lin ψ 1).transpose * (bil lam 1 1).transpose) a b ∈ A := fun a b => by
    have h0 := (h (Pi.single b 1, 0) (fun i => ⟨hs b i, A.zero_mem⟩) a).2
    have e : (transH φ ψ lam (Pi.single b 1, 0)).2 a =
        ((lin ψ 1).transpose * (bil lam 1 1).transpose) a b := by
      simp [transH_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rwa [e] at h0
  have h4 : (bil lam 1 1).transpose =
      (lin φ 1).transpose * ((lin ψ 1).transpose * (bil lam 1 1).transpose) := by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hψφ, Matrix.transpose_one, Matrix.one_mul]
  refine ⟨h1 a b, h2 a b, ?_⟩
  have h5 : bil lam 1 1 a b = (bil lam 1 1).transpose b a := rfl
  rw [h5, h4, Matrix.mul_apply]
  exact A.sum_mem fun c _ => A.mul_mem (h1 c b) (h3 c a)

end Lat

section Curve

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω}

theorem stalk_sq (Γ : FibreCurve ξ ϖ) (i : Γ.C.I) :
    (Γ.C.v i).valuationSubring.subtype.comp (Scheme.stalkClosedPointTo (Γ.z i)).hom =
      (Scheme.stalkClosedPointTo Γ.η).hom.comp (X.presheaf.stalkSpecializes (Γ.generic_centre_specializes i)).hom := by
  have key := ProjectiveLinePlaces.stalk_square (Γ.generic_centre_specializes i) (Scheme.stalkClosedPointTo (Γ.z i))
    (Scheme.stalkClosedPointTo Γ.η) (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype)
    ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk Γ.η).trans ((Γ.z_gen i).symm.trans
      (congrArg (Spec.map (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype) ≫ ·)
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (Γ.z i))).symm))
  exact (congrArg CommRingCat.Hom.hom key).symm

theorem val_le_one (hξ : IsCptGen ξ) (Γ : FibreCurve ξ ϖ) (i : Γ.C.I) (a : X.presheaf.stalk (centre Γ.η))
    (ha : genMap ξ ⟨centre Γ.η, Γ.η_spec⟩ a ∈ regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩) :
    Γ.C.v i ((Scheme.stalkClosedPointTo Γ.η).hom a) ≤ 1 := by
  obtain ⟨c, hc⟩ := ha
  have h1 : (X.presheaf.stalkSpecializes (Γ.generic_centre_specializes i)).hom c = a :=
    hξ.inj ⟨centre Γ.η, Γ.η_spec⟩
      ((ProjectiveLinePlaces.genMap_specializes (Γ.generic_centre_specializes i) Γ.η_spec (Γ.z_spec i) c).trans hc)
  have h2 : ((Scheme.stalkClosedPointTo (Γ.z i)).hom c : Γ.κ) = (Scheme.stalkClosedPointTo Γ.η).hom
      ((X.presheaf.stalkSpecializes (Γ.generic_centre_specializes i)).hom c) := DFunLike.congr_fun (stalk_sq Γ i) c
  rw [h1] at h2
  rw [← h2]
  exact ((Scheme.stalkClosedPointTo (Γ.z i)).hom c).2

end Curve

section Point

variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R]

theorem natCast_residueField (z : Sp R ⟶ X) (p : ℕ) (hp : (p : R) = 0) :
    (p : X.residueField (centre z)) = 0 := by
  have hnu : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (centre z)) := fun h => by
    have h1 := h.map (Scheme.stalkClosedPointTo z).hom
    have e : (Scheme.stalkClosedPointTo z).hom (p : X.presheaf.stalk (centre z)) = (0 : R) :=
      (map_natCast (Scheme.stalkClosedPointTo z).hom p).trans hp
    exact not_isUnit_zero (M₀ := R) ((congrArg IsUnit e).mp h1)
  have h2 := (IsLocalRing.residue_eq_zero_iff _).2 hnu
  rw [map_natCast] at h2
  exact h2

theorem centre_spMap {S : Type} [CommRing S] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (z : Sp R ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom f) ≫ z) = centre z := by
  change z ((Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint S)) = z (IsLocalRing.closedPoint R)
  congr 1
  exact IsLocalRing.comap_closedPoint f

end Point

section Main

theorem exists_residue_germ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (hbar : ∀ a : 𝓞 E, star a = H.bar a) (X : Scheme.{0}) (t : SAB H X) (hpow : PowFns t)
    {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X) (d : ℕ) (g : GermAt t x d) (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) (hf : FibPF t (centre x)) :
    ∃ Bk : Germ.FB (IsLocalRing.ResidueField R) d (𝓞 E), IsMapOf (IsLocalRing.residue R) g.B Bk ∧ ConjInj Bk p := by
  obtain ⟨g₂, hm, -⟩ := GlobalTheory.T.formal_germ_base_change E H hbar X t R (IsLocalRing.ResidueField R) (IsLocalRing.residue R) x d g
  haveI : CharP (IsLocalRing.ResidueField R) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast (IsLocalRing.residue R), hp, map_zero])
  refine ⟨g₂.B, hm, GlobalTheory.T.fibre_power_free_conj_injective E H hbar X t hpow _ p _ d g₂ ?_⟩
  have e := centre_spMap (IsLocalRing.residue R) x
  change FibPF t (centre (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ x))
  rw [e]
  exact hf

end Main

section Integral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X : Scheme.{0}}
  {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}

theorem integral_at (S : GermSys t ξ M) {ϖ : Ω} (Γ : FibreCurve ξ ϖ) (hξ : IsCptGen ξ) (i : Γ.C.I)
    {B' : Germ.FB (X.presheaf.stalk (centre Γ.η)) d (𝓞 E)} {φ' ψ' : Germ.Pt (X.presheaf.stalk (centre Γ.η)) 1 d}
    {lam' : Germ.PS (X.presheaf.stalk (centre Γ.η)) 2 d}
    (hiso : IsIso (S.g ⟨centre Γ.η, Γ.η_spec⟩).B B' φ' ψ' lam')
    (he : transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩)
        (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩) =
      transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩) ∘ₗ
        transH (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (φ' l))
          (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (ψ' l))
          (MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) lam'))
    (hl : stdLat (regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩)
        (transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩)) =
      stdLat (regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩)
        (transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩)
          (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩)))
    (a b : Fin d) :
    Γ.C.v i (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l)) 1 a b) ≤ 1 ∧
      Γ.C.v i (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l)) 1 a b) ≤ 1 ∧
      Γ.C.v i (bil (MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam') 1 1 a b) ≤ 1 := by
  have h0 := (GlobalTheory.T.formal_isomorphism_transport Ω d (𝓞 E) S.g₀.B (S.BK ⟨centre Γ.η, Γ.η_spec⟩) _ _ _
    (S.iso ⟨centre Γ.η, Γ.η_spec⟩)).2.2.1.1
  have h1 := (GlobalTheory.T.formal_isomorphism_transport _ d (𝓞 E) _ _ _ _ _ hiso).2.1
  have h2 : lin (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (ψ' l)) 1 *
      lin (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (φ' l)) 1 = 1 := by
    rw [lin_map, lin_map, ← Matrix.map_mul]
    exact (congrArg (fun m => Matrix.map m (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩)) h1).trans
      (Matrix.map_one _ (map_zero _) (map_one _))
  obtain ⟨e1, e2, e3⟩ := entries_mem (A := regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩) _ _ _ h2
    (fun y hy => trans_integral he h0 hl y hy) a b
  rw [lin_map, Matrix.map_apply] at e1 e2
  rw [bil_map, Matrix.map_apply] at e3
  refine ⟨?_, ?_, ?_⟩
  · have e : (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l)) 1 a b : Γ.κ) =
        (Scheme.stalkClosedPointTo Γ.η).hom (lin φ' 1 a b) :=
      congrFun (congrFun (lin_map (Scheme.stalkClosedPointTo Γ.η).hom φ' 1) a) b
    rw [e]
    exact val_le_one hξ Γ i _ e1
  · have e : (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l)) 1 a b : Γ.κ) =
        (Scheme.stalkClosedPointTo Γ.η).hom (lin ψ' 1 a b) :=
      congrFun (congrFun (lin_map (Scheme.stalkClosedPointTo Γ.η).hom ψ' 1) a) b
    rw [e]
    exact val_le_one hξ Γ i _ e2
  · have e : (bil (MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam') 1 1 a b : Γ.κ) =
        (Scheme.stalkClosedPointTo Γ.η).hom (bil lam' 1 1 a b) :=
      congrFun (congrFun (bil_map (Scheme.stalkClosedPointTo Γ.η).hom lam' 1 1) a) b
    rw [e]
    exact val_le_one hξ Γ i _ e3

end Integral

theorem germ_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (O : Type) [CommRing O] (s : X ⟶ Sp O) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (p : ℕ) [Fact p.Prime] (Γ : FibreCurve ξ ϖ) [CharP Γ.κ p], IsCptGen ξ → PowFns t → (∀ q : Cpt ξ, (p : X.residueField q.1) = 0 → FibPF t q.1) → ∃ F : Family Γ.C p d (𝓞 E), IsMapOf (Scheme.stalkClosedPointTo Γ.η).hom (S.g ⟨centre Γ.η, Γ.η_spec⟩).B F.B ∧ ∀ i, IsMapOf (Scheme.stalkClosedPointTo (Γ.z i)).hom (S.g ⟨centre (Γ.z i), Γ.z_spec i⟩).B (F.Bi i) ∧ ∃ (φ' ψ' : Germ.Pt (X.presheaf.stalk (centre Γ.η)) 1 d) (lam' : Germ.PS (X.presheaf.stalk (centre Γ.η)) 2 d), transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩) = transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩) ∘ₗ transH (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (φ' l)) (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (ψ' l)) (MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) lam') ∧ F.φ i = (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l)) ∧ F.ψ i = (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l)) ∧ F.lam i = MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam' := by
  intro E _ _ _ H _ hbar X t Ω _ ξ d M S O _ s _ _ ϖ p _ Γ _ hξ hpow hfib
  have hκ : ((p : ℕ) : Γ.κ) = 0 := CharP.cast_eq_zero Γ.κ p
  obtain ⟨g0, m0, -⟩ := GlobalTheory.T.formal_germ_base_change E H hbar X t _ _ (Scheme.stalkClosedPointTo Γ.η).hom
    (X.fromSpecStalk (centre Γ.η)) d (S.g ⟨centre Γ.η, Γ.η_spec⟩)
  have place : ∀ i : Γ.C.I, ∃ (Bi : Germ.FB (Γ.C.v i).valuationSubring d (𝓞 E)) (BK : Germ.FB Γ.κ d (𝓞 E))
      (Bk : Germ.FB (IsLocalRing.ResidueField (Γ.C.v i).valuationSubring) d (𝓞 E))
      (φ' ψ' : Germ.Pt (X.presheaf.stalk (centre Γ.η)) 1 d) (lam' : Germ.PS (X.presheaf.stalk (centre Γ.η)) 2 d),
      IsMapOf (Scheme.stalkClosedPointTo (Γ.z i)).hom (S.g ⟨centre (Γ.z i), Γ.z_spec i⟩).B Bi ∧
      IsMapOf (Γ.C.v i).valuationSubring.subtype Bi BK ∧ IsMapOf (IsLocalRing.residue _) Bi Bk ∧ ConjInj Bk p ∧
      IsIso g0.B BK (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l))
        (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l))
        (MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam') ∧
      transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩)
          (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩) =
        transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩) ∘ₗ
          transH (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (φ' l))
            (fun l => MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) (ψ' l))
            (MvPowerSeries.map (genMap ξ ⟨centre Γ.η, Γ.η_spec⟩) lam') ∧
      (stdLat (regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩)
          (transH (S.φ ⟨centre Γ.η, Γ.η_spec⟩) (S.ψ ⟨centre Γ.η, Γ.η_spec⟩) (S.lam ⟨centre Γ.η, Γ.η_spec⟩)) =
        stdLat (regAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩)
          (transH (S.φ ⟨centre (Γ.z i), Γ.z_spec i⟩) (S.ψ ⟨centre (Γ.z i), Γ.z_spec i⟩)
            (S.lam ⟨centre (Γ.z i), Γ.z_spec i⟩)) → ∀ a b,
        Γ.C.v i (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' l)) 1 a b) ≤ 1 ∧
        Γ.C.v i (lin (fun l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' l)) 1 a b) ≤ 1 ∧
        Γ.C.v i (bil (MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom lam') 1 1 a b) ≤ 1) := by
    intro i
    obtain ⟨gi, mi, -⟩ := GlobalTheory.T.formal_germ_base_change E H hbar X t _ (Γ.C.v i).valuationSubring
      (Scheme.stalkClosedPointTo (Γ.z i)).hom (X.fromSpecStalk (centre (Γ.z i))) d
      (S.g ⟨centre (Γ.z i), Γ.z_spec i⟩)
    obtain ⟨gK, mK, -⟩ := GlobalTheory.T.formal_germ_base_change E H hbar X t _ Γ.κ (Γ.C.v i).valuationSubring.subtype _ d gi
    have hp : ((p : ℕ) : (Γ.C.v i).valuationSubring) = 0 := Subtype.ext (by simpa using hκ)
    have ex : spMap (Scheme.stalkClosedPointTo (Γ.z i)).hom ≫ X.fromSpecStalk (centre (Γ.z i)) = Γ.z i :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk (Γ.z i)
    have hf : FibPF t (centre (Γ.z i)) :=
      hfib ⟨_, Γ.z_spec i⟩ (natCast_residueField (Γ.z i) p hp)
    obtain ⟨Bk, mk, hk⟩ := exists_residue_germ E H hbar X t hpow _ d gi p hp (by rw [ex]; exact hf)
    obtain ⟨B', φ', ψ', lam', hm', hiso, he⟩ := S.gen ⟨centre (Γ.z i), Γ.z_spec i⟩ ⟨centre Γ.η, Γ.η_spec⟩
      (Γ.generic_centre_specializes i)
    have hK : IsMapOf (Scheme.stalkClosedPointTo Γ.η).hom B' gK.B :=
      isMapOf_cancel hm' (by rw [← stalk_sq Γ i]; exact mi.trans mK)
    exact ⟨gi.B, gK.B, Bk, φ', ψ', lam', mi, mK, mk, hk,
      GlobalTheory.T.intersection_first _ _ _ d _ _ _ _ _ _ _ _ m0 hK hiso, he, fun hl a b => integral_at S Γ hξ i hiso he hl a b⟩
  choose Bi BK Bk φ' ψ' lam' mi mK mk hk hiso he hint using place
  obtain ⟨Y, hY, -⟩ := GlobalTheory.T.fibre_curve_degree_compare X Ω ξ O s ϖ Γ hξ
  obtain ⟨U, hU, hloc⟩ := S.loc ⟨centre Γ.η, Γ.η_spec⟩
  have hfin := Y.ae U hU
  rw [hY] at hfin
  exact ⟨{ B := g0.B, Bi := Bi, BK := BK, Bk := Bk, mapK := mK, mapk := mk, inj := hk
           φ := fun i l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (φ' i l)
           ψ := fun i l => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (ψ' i l)
           lam := fun i => MvPowerSeries.map (Scheme.stalkClosedPointTo Γ.η).hom (lam' i)
           iso := hiso
           ae := hfin.subset fun i hi h => hi (hint i (hloc ⟨_, Γ.z_spec i⟩ h)) }, m0,
    fun i => ⟨mi i, φ' i, ψ' i, lam' i, he i, rfl, rfl, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.GermFam
