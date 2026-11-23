import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.ChartCompat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def liftF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, spMap_comp_ring]; rfl)

theorem liftF_fst {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _

theorem liftF_snd {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

theorem liftF_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : liftF z = spMap φ.toRingHom ≫ liftF y := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftF_fst, liftF_fst, h.1]
  · rw [Category.assoc, liftF_snd, liftF_snd, spMap_comp_ring]
    congr 1
    ext a
    simp

theorem liftF_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ}
    {y z : FrPt Xo c S} (h : FrBor t y z) : liftF z = liftF y := by
  apply pullback.hom_ext
  · rw [liftF_fst, liftF_fst, h.1]
  · rw [liftF_snd, liftF_snd]

theorem liftF_gen (h : GenFrEx Xo c) (Z : Comp Xo c) :
    liftF (genFr h Z) = spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftF_fst, (isGenFr_genFr h Z).1]; rfl
  · rw [Category.assoc, liftF_snd, IsScalarTower.algebraMap_eq c.F (kap Z) (Om Z), ← spMap_comp_ring]
    congr 1
    exact Spec.map_preimage (genSp Z ≫ strK)

theorem liftF_gen_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (p : Sp (Om Z)) :
    (liftF (genFr h Z)) p = genPt Z := by
  rw [liftF_gen, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

theorem closure_genPt' (Z : Comp Xo c) : closure {genPt Z} = (Z : Set (Xo.XF c)) :=
  (IsIrreducible.genericPoint_closure_eq (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c)))).trans
    (isClosed_of_mem_irreducibleComponents _ Z.2).closure_eq

theorem chart_mem {h : GenFrEx Xo c} (C : FChart h) (p : Sp C.R) : (liftF C.y) p ∈ (C.Z : Set (Xo.XF c)) := by
  have hcl : IsClosed ((liftF C.y) ⁻¹' (C.Z : Set (Xo.XF c))) :=
    (isClosed_of_mem_irreducibleComponents _ C.Z.2).preimage (liftF C.y).continuous
  let q : Sp (Om C.Z) := (⊥ : PrimeSpectrum (Om C.Z))
  have h1 : (liftF C.y) (spMap C.R.val.toRingHom q) = genPt C.Z := by
    rw [← Scheme.Hom.comp_apply, ← liftF_map C.gen, liftF_bor C.bor, liftF_gen_apply]
  have h2 : spMap C.R.val.toRingHom q ∈ (liftF C.y) ⁻¹' (C.Z : Set (Xo.XF c)) := by
    show (liftF C.y) (spMap C.R.val.toRingHom q) ∈ (C.Z : Set (Xo.XF c))
    rw [h1, ← closure_genPt']
    exact subset_closure rfl
  have h3 : spMap C.R.val.toRingHom q ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have ha' : C.R.val a = 0 := ha
    have : a = 0 := Subtype.ext ha'
    rw [this]
    exact Ideal.zero_mem _
  exact h3.mem_closed hcl h2

theorem comp_eq {h : GenFrEx Xo c} (C C' : FChart h) (ψ : C'.R →ₐ[c.F] Om C.Z) (z : FrPt Xo c (Om C.Z))
    (t : Ix Dw → (Om C.Z)ˣ) (hz : FrMap ψ C'.y z) (hb : FrBor t z C.yg) : C.Z = C'.Z := by
  let q : Sp (Om C.Z) := (⊥ : PrimeSpectrum (Om C.Z))
  have h1 : genPt C.Z ∈ (C'.Z : Set (Xo.XF c)) := by
    rw [← liftF_gen_apply h C.Z q, ← liftF_bor C.bor, liftF_bor hb, liftF_map hz, Scheme.Hom.comp_apply]
    exact chart_mem C' _
  have h2 : (C.Z : Set (Xo.XF c)) ⊆ (C'.Z : Set (Xo.XF c)) := by
    rw [← closure_genPt']
    exact closure_minimal (Set.singleton_subset_iff.2 h1) (isClosed_of_mem_irreducibleComponents _ C'.Z.2)
  exact Subtype.ext (Set.Subset.antisymm h2 (C.Z.2.2 C'.Z.2.1 h2))

theorem wchar_mul {J S : Type} [Fintype J] [CommRing S] (e : J → ℕ) (t t' : J → Sˣ) :
    wchar e (t * t') = wchar e t * wchar e t' := by
  simp [wchar, mul_pow, Finset.prod_mul_distrib]

theorem wchar_map {J K S T : Type} [Fintype J] [Field K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (φ : S →ₐ[K] T) (e : J → ℕ) (t : J → Sˣ) :
    wchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (wchar e t) := by
  simp [wchar]

theorem away_lift {K R T : Type} [Field K] [CommRing R] [Algebra K R] [Field T] [Algebra K T] (g : R)
    (φ : R →ₐ[K] T) (hφ : φ g ≠ 0) :
    ∃ m : Localization.Away g →ₐ[K] T, m.comp (IsScalarTower.toAlgHom K R (Localization.Away g)) = φ := by
  have hu : ∀ m : Submonoid.powers g, IsUnit (φ m) := by
    rintro ⟨_, n, rfl⟩
    simpa using Ne.isUnit (pow_ne_zero n hφ)
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers g) hu, ?_⟩
  ext a
  simp

theorem away_inj {K R T : Type} [Field K] [CommRing R] [Algebra K R] [CommRing T] [Algebra K T] (g : R)
    (m : Localization.Away g →ₐ[K] T)
    (h : Function.Injective (m.comp (IsScalarTower.toAlgHom K R (Localization.Away g)))) : Function.Injective m := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨⟨a, n⟩, hm⟩ := IsLocalization.surj (Submonoid.powers g) s
  have h1 : m (algebraMap R _ a) = 0 := by
    rw [← hm, map_mul, hs, zero_mul]
  have h3 : a = 0 := (injective_iff_map_eq_zero _).1 h a h1
  dsimp only at hm
  rw [h3, map_zero] at hm
  exact (IsLocalization.map_units _ n).mul_left_eq_zero.1 hm

end GlobalTheory.Reg.ChartCompat

namespace GlobalTheory.Reg
open ChartCompat

set_option maxHeartbeats 1000000 in
theorem FChart.compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℕ) (b : ∀ Z : Comp Xo c, Om Z) (hb : wchar e C.t * b C.Z ∈ C.R) (hb' : wchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = wchar e t * ψ ⟨_, hb⟩ := by
  intro E _ _ _ H Dw l Xo c hev h C C' L _ _ ψ ψ' z z' t hz hz' hbor
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c
  have U := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c
  obtain ⟨g, hg, hopn⟩ := C'.opn C.R L ψ C.y z hz ⟨ψ', z', t⁻¹, hz', (G L).2.2.1 t z z' hbor⟩
  have hg0 : g ≠ 0 := fun e => hg (by rw [e, map_zero])
  have hg1 : C.R.val g ≠ 0 := fun e => hg0 (Subtype.ext e)
  have hZ : C.Z = C'.Z := by
    obtain ⟨ψ0, z0, t0, h1, h2⟩ := hopn (Om C.Z) C.R.val (Ne.isUnit hg1) C.yg C.gen
    exact comp_eq C C' ψ0 z0 t0 h1 h2
  refine ⟨hZ, ?_⟩
  obtain ⟨Z, R, sm, frac, y, yg, tC, gen, bor, mono, opn⟩ := C
  obtain ⟨Z', R', sm', frac', y', yg', tC', gen', bor', mono', opn'⟩ := C'
  dsimp only at *
  subst hZ
  intro e b hb hb'
  let S := Localization.Away g
  let lam : R →ₐ[c.F] S := IsScalarTower.toAlgHom c.F R S
  have hlam : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨mu, hmu⟩ : ∃ m : S →ₐ[c.F] Om Z, m.comp lam = R.val := away_lift g R.val hg1
  obtain ⟨nu, hnu⟩ : ∃ m : S →ₐ[c.F] L, m.comp lam = ψ := away_lift g ψ hg
  have hinj : Function.Injective mu := away_inj g mu (by rw [hmu]; exact Subtype.val_injective)
  obtain ⟨w, hw⟩ := hev.bc R S lam y
  obtain ⟨φ, v, s, hv, hs⟩ := hopn S lam hlam w hw

  obtain ⟨vmu, hvmu⟩ := hev.bc S (Om Z) mu v
  have m1 : FrMap mu w yg := frMap_cancel _ _ _ lam mu y w yg hw (by rw [hmu]; exact gen)
  have b1 := frBorBC _ _ mu s v w vmu yg hs hvmu m1
  have m2 : FrMap (mu.comp φ) y' vmu := frMap_trans _ _ _ φ mu y' v vmu hv hvmu
  have b2 := (G _).2.1 _ _ _ _ _ b1 ((G _).2.1 _ _ _ _ _ ((G _).2.2.1 _ _ _ bor) bor')
  have e1 : mu.comp φ = R'.val := mono' _ _ _ _ _ _ m2 gen' b2
  have e2 : vmu = yg' := (U _ _ R'.val y').1 _ _ (e1 ▸ m2) gen'
  subst e2
  have e3 : tC = tC' * fun i => Units.map (mu : S →* Om Z) (s i) :=
    (G _).2.2.2 _ _ _ _ bor ((G _).2.1 _ _ _ _ _ bor' b1)

  obtain ⟨vnu, hvnu⟩ := hev.bc S L nu v
  have m3 : FrMap nu w z := frMap_cancel _ _ _ lam nu y w z hw (by rw [hnu]; exact hz)
  have b3 := frBorBC _ _ nu s v w vnu z hs hvnu m3
  have m4 : FrMap (nu.comp φ) y' vnu := frMap_trans _ _ _ φ nu y' v vnu hv hvnu
  have b4 := (G _).2.1 _ _ _ _ _ b3 hbor
  have e4 : nu.comp φ = ψ' := mono' _ _ _ _ _ _ m4 hz' b4
  have e5 : vnu = z' := (U _ _ ψ' y').1 _ _ (e4 ▸ m4) hz'
  subst e5
  have e6 : (fun i => Units.map (nu : S →* L) (s i)) * t = 1 :=
    (G _).2.2.2 _ _ _ _ b4 ((G _).1 _)
  have e7 : lam ⟨_, hb⟩ = wchar e s * φ ⟨_, hb'⟩ := by
    apply hinj
    have a1 : mu (lam ⟨_, hb⟩) = wchar e tC * b Z := DFunLike.congr_fun hmu ⟨_, hb⟩
    have a2 : mu (φ ⟨_, hb'⟩) = wchar e tC' * b Z := DFunLike.congr_fun e1 ⟨_, hb'⟩
    have a0 : wchar e tC = wchar e tC' * mu (wchar e s) :=
      (congrArg (wchar e) e3).trans ((wchar_mul _ _ _).trans (congrArg _ (wchar_map mu e s)))
    rw [map_mul, a1, a2]
    linear_combination (b Z) * a0
  have a3 : ψ ⟨_, hb⟩ = nu (wchar e s) * ψ' ⟨_, hb'⟩ := by
    rw [← hnu, ← e4, AlgHom.comp_apply, AlgHom.comp_apply, e7, map_mul]
  have a4 : nu (wchar e s) * wchar e t = 1 := by
    rw [← wchar_map, ← wchar_mul, e6]
    simp [wchar]
  linear_combination (-(wchar e t)) * a3 - (ψ' ⟨_, hb'⟩) * a4

end GlobalTheory.Reg
