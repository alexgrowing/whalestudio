import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompat
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsFunctionAtPoint
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceFamilyPairing

theorem val_mem {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom)
    {Ω R B T : Type} [Field Ω] [CommRing R] [CommRing B] [CommRing T]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : Spec (CommRingCat.of R) ⟶ X) (t : Spec (CommRingCat.of T) ⟶ X)
    (φ : R →+* Ω) (ψ : R →+* B) (k : B →+* Ω) (s : T →+* B) (g : T →+* Ω)
    (hk : k.comp ψ = φ) (hs : k.comp s = g)
    (hx : Spec.map (CommRingCat.ofHom φ) ≫ x = ξ)
    (ht : Spec.map (CommRingCat.ofHom ψ) ≫ x = Spec.map (CommRingCat.ofHom s) ≫ t)
    {L Li : Type} [AddCommGroup L] [Module R L] [AddCommGroup Li] [Module Ω Li]
    (M₀ : LieModel G x L) (M : LieModel G ξ Li) (j₀ : L → Li)
    (hj₀ : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M₀.pt v).left)
    (u₀ : Module.Dual R L) (u : Module.Dual Ω Li) (hu : ∀ v, u (j₀ v) = φ (u₀ v))
    (e : Li) (v : epsAt t ⟶ G) (hv : IsTanAt G t v)
    (he : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) : u e ∈ k.range := by
  obtain ⟨L', _, _, ⟨M'⟩⟩ := lieModel_exists X G B (Spec.map (CommRingCat.ofHom ψ) ≫ x)
  obtain ⟨L'', _, _, ⟨M''⟩⟩ := lieModel_exists X G T t
  have hξ : ξ = Spec.map (CommRingCat.ofHom k) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ x := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hk, hx]
  obtain ⟨β, hβ, -, hsp, hext⟩ := HTPull.lieBC ψ x _ rfl hsm M₀ M'
  obtain ⟨j', hj', hjs, -, -⟩ := HTPull.lieBC k _ ξ hξ hsm M' M
  obtain ⟨j₂, hj₂, -, -, -⟩ := HTPull.lieBC s t _ ht hsm M'' M'
  obtain ⟨u', hu'⟩ := hext u₀
  have hjj : ∀ l, j' (β l) = j₀ l := fun l => M.inj (Over.OverMorphism.ext (by
    rw [hj', hβ, hj₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, HTPull.dualMap_comp, hk]))
  have hall : ∀ e' : L', u (j' e') = k (u' e') := by
    intro e'
    have he' : e' ∈ Submodule.span B (Set.range β) := by rw [hsp]; trivial
    induction he' using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      rw [hjj, hu, hu', ← hk]
      rfl
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [hjs, hb]
  obtain ⟨l, rfl⟩ := M''.onto v hv
  have e1 : e = j' (j₂ l) := M.inj (Over.OverMorphism.ext (by
    rw [he, hj', hj₂, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, HTPull.dualMap_comp, hs]))
  rw [e1, hall]
  exact ⟨_, rfl⟩

theorem val_frac {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom)
    {Ω R : Type} [Field Ω] [CommRing R] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z)
    {L Li : Type} [AddCommGroup L] [Module R L] [AddCommGroup Li] [Module Ω Li]
    (M₀ : LieModel G x L) (M : LieModel G ξ Li) (j₀ : L → Li)
    (hj₀ : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M₀.pt v).left)
    (u₀ : Module.Dual R L) (u : Module.Dual Ω Li) (hu : ∀ v, u (j₀ v) = φ (u₀ v))
    (e : Li) (he : e ∈ M.lat ⟨x z, hz⟩) : ∃ r s : R, s ∉ z.asIdeal ∧ φ s * u e = φ r := by
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  letI alg : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk z) := StructureSheaf.stalkAlgebra R z
  haveI loc : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R z
  have hun : ∀ s : z.asIdeal.primeCompl, IsUnit (φ s) := by
    intro s
    refine IsUnit.mk0 _ fun h => s.2 ?_
    have h0 : (s : R) = 0 := hφ (h.trans (map_zero φ).symm)
    rw [h0]
    exact z.asIdeal.zero_mem
  let lam : (Spec (CommRingCat.of R)).presheaf.stalk z →+* Ω := IsLocalization.lift (M := z.asIdeal.primeCompl) hun
  let lam' : (Spec (CommRingCat.of R)).presheaf.stalk z ⟶ CommRingCat.of Ω := CommRingCat.ofHom lam
  have hlam : ∀ r : R, lam (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hun r
  have e0 : (Spec (CommRingCat.of R)).fromSpecStalk z =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) :=
    Spec.fromSpecStalk_eq' _ _
  have e1 : Spec.map (CommRingCat.ofHom lam) ≫ (Spec (CommRingCat.of R)).fromSpecStalk z = spMap φ := by
    rw [e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hlam
  have e2 : Spec.map (x.stalkMap z ≫ lam') ≫ X.fromSpecStalk (x z) = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) e1).trans hx)
  have e3 : spMap (genMap ξ ⟨x z, hz⟩) ≫ X.fromSpecStalk (x z) = ξ :=
    GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk ⟨x z, hz⟩
  have e4 : x.stalkMap z ≫ lam' = CommRingCat.ofHom (genMap ξ ⟨x z, hz⟩) :=
    Spec.map_injective ((cancel_mono (X.fromSpecStalk (x z))).1 (e2.trans e3.symm))
  have e5 : ∀ a, lam ((x.stalkMap z).hom a) = genMap ξ ⟨x z, hz⟩ a := fun a => ConcreteCategory.congr_hom e4 a
  have e6 : Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) ≫ x =
      Spec.map (CommRingCat.ofHom (x.stalkMap z).hom) ≫ X.fromSpecStalk (x z) :=
    (congrArg (· ≫ x) e0.symm).trans (Scheme.SpecMap_stalkMap_fromSpecStalk x).symm
  obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ Li M ⟨x z, hz⟩).1 e).1 he
  obtain ⟨b, hb⟩ := val_mem hsm ξ x (X.fromSpecStalk (x z)) φ
    (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z)) lam (x.stalkMap z).hom (genMap ξ ⟨x z, hz⟩)
    (RingHom.ext hlam) (RingHom.ext e5) hx e6 M₀ M j₀ hj₀ u₀ u hu e v hv hev
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj z.asIdeal.primeCompl b
  refine ⟨r, s, s.2, ?_⟩
  rw [← hb, ← hlam, ← hlam, ← map_mul, mul_comm]
  exact congrArg lam hrs

theorem mem_of_frac {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) (a : Ω)
    (h : ∀ z : PrimeSpectrum R, ∃ r s : R, s ∉ z.asIdeal ∧ (s : Ω) * a = r) : a ∈ R := by
  let I : Ideal R :=
    { carrier := {s | (s : Ω) * a ∈ R}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : R) : Ω) * a ∈ R
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : R) : Ω) * a ∈ R
        simp
      smul_mem' := fun c u hu => by
        show ((c • u : R) : Ω) * a ∈ R
        rw [smul_eq_mul, Subalgebra.coe_mul, _root_.mul_assoc]
        exact mul_mem c.2 hu }
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    have h2 : ((1 : R) : Ω) * a ∈ R := h1
    simpa using h2
  · obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨r, s, hs, e⟩ := h ⟨P, hP.isPrime⟩
    exact absurd (hIP (show (s : Ω) * a ∈ R from e ▸ r.2)) hs

end PositivityTheory.Xgn.SequenceFamilyPairing

theorem PositivityTheory.Xgn.sequence_family_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (u : Module.Dual Ω 𝔐.Li), u ∈ P.Dh.om → ∀ v : 𝔐.Li, (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → v ∈ 𝔐.M.lat q) → u v ∈ CR O y c' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd _ p _ hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ G c' hc' P u
    hu v hv
  rw [P.isHT.1] at hu
  obtain ⟨u₀, rfl⟩ := hu
  refine PositivityTheory.Xgn.SequenceFamilyPairing.mem_of_frac _ _ fun z => ?_
  obtain ⟨h1, h2, -⟩ := PositivityTheory.Xgn.exists_function_at_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O G
    c' hc' P z
  exact PositivityTheory.Xgn.SequenceFamilyPairing.val_frac 𝔐.t.semi.smooth 𝔐.ξ (algebraMap (CR O y c') Ω)
    Subtype.val_injective P.x P.x_gen z (𝔐.all _) P.M 𝔐.M P.toLi P.toLi_pt u₀ (P.j u₀) (P.j_apply u₀) v (hv _ h1 h2)
