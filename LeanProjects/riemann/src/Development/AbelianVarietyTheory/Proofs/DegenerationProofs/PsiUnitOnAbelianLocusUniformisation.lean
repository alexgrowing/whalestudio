import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.PsiAbelian

section Hartogs

variable {R : Type} [CommRing R] [IsDomain R]

def RegAt (a : FractionRing R) (Q : PrimeSpectrum R) : Prop :=
  ∃ s, s ∉ Q.asIdeal ∧ ∃ c : R, algebraMap R (FractionRing R) s * a = algebraMap R (FractionRing R) c

theorem regAt_of_height_one [IsNoetherianRing R] [IsIntegrallyClosed R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    {a : FractionRing R} (h : ∀ P ∈ U, P.asIdeal.height = 1 → RegAt a P) : ∀ Q ∈ U, RegAt a Q := by
  intro Q hQ
  by_contra hn
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap R (FractionRing R) c ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hc0
  let d : Ideal R := (Ideal.span {c}).colon {b}
  have hd : ∀ s, s ∈ d ↔ c ∣ s * b := fun s => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  have reg : ∀ s, (∃ e : R, algebraMap R (FractionRing R) s * (algebraMap R _ b / algebraMap R _ c) =
      algebraMap R (FractionRing R) e) ↔ s ∈ d := fun s => by
    rw [hd]
    refine exists_congr fun e => ?_
    rw [← mul_div_assoc, div_eq_iff hcK, ← map_mul, ← map_mul, (IsFractionRing.injective R _).eq_iff, mul_comm e]
  have hdQ : d ≤ Q.asIdeal := fun s hs => by_contra fun hsQ => hn ⟨s, hsQ, (reg s).2 hs⟩
  obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le hdQ
  have hpa : p ∈ associatedPrimes R (R ⧸ d) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [Ideal.annihilator_quotient]
    exact hp
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hpa
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : p.height = 1 := height_eq_one_of_forall_mem_iff_dvd (b := x * b) hc0 fun r => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hd, _root_.mul_assoc]
  obtain ⟨s, hs, he⟩ := h ⟨p, hpp⟩ (((PrimeSpectrum.le_iff_specializes ⟨p, hpp⟩ Q).mp hpQ).mem_open hU hQ) h1
  exact hs (hp.1.2 ((reg s).1 he))

theorem top_le_preimage {V : (Sp R).Opens} {P : Sp R} (hP : P ∈ V) : ⊤ ≤ jK R ⁻¹ᵁ V := by
  intro z _
  have : (jK R z : PrimeSpectrum R).asIdeal ≤ (P : PrimeSpectrum R).asIdeal := by
    intro r hr
    have hr' : algebraMap R (FractionRing R) r ∈ (z : PrimeSpectrum (FractionRing R)).asIdeal := hr
    have := PrimeSpectrum.isPrime z
    rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal z), Ideal.mem_bot, IsFractionRing.to_map_eq_zero_iff] at hr'
    rw [hr']; exact Ideal.zero_mem _
  exact ((PrimeSpectrum.le_iff_specializes (jK R z) P).mp this).mem_open V.isOpen hP

def ev (V : (Sp R).Opens) (h : ⊤ ≤ jK R ⁻¹ᵁ V) : Γ(Sp R, V) →+* FractionRing R :=
  (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.comp ((jK R).appLE V ⊤ h).hom

theorem ev_res {V V' : (Sp R).Opens} (l : V' ≤ V) (h : ⊤ ≤ jK R ⁻¹ᵁ V) (h' : ⊤ ≤ jK R ⁻¹ᵁ V') (r : Γ(Sp R, V)) :
    ev V' h' (((Sp R).presheaf.map (homOfLE l).op).hom r) = ev V h r := by
  have e : (Sp R).presheaf.map (homOfLE l).op ≫ (jK R).appLE V' ⊤ h' = (jK R).appLE V ⊤ h :=
    Scheme.Hom.map_appLE _ _ _
  simp only [ev, RingHom.comp_apply]
  rw [← e]
  rfl

theorem ev_toOpen (V : (Sp R).Opens) (h : ⊤ ≤ jK R ⁻¹ᵁ V) (r : R) :
    ev V h (DegPre.toOpen V r) = algebraMap R _ r := by
  refine (ev_res le_top (le_refl _) h _).trans ?_
  have e : (jK R).appLE ⊤ ⊤ (le_refl _) = (jK R).appTop := Scheme.Hom.appLE_eq_app _
  simp only [ev, RingHom.comp_apply]
  rw [e, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp

theorem exists_frac {V : (Sp R).Opens} {P : Sp R} (hP : P ∈ V) (r : Γ(Sp R, V)) :
    ∃ (s : R) (c : R) (V' : (Sp R).Opens) (l : V' ≤ V), P ∈ V' ∧ s ∉ (P : PrimeSpectrum R).asIdeal ∧
      DegPre.toOpen V' s * ((Sp R).presheaf.map (homOfLE l).op).hom r = DegPre.toOpen V' c := by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hf, l⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hP V.isOpen
  let sI := Scheme.ΓSpecIso (CommRingCat.of R)
  have hb : (Sp R).basicOpen (sI.inv.hom f) = PrimeSpectrum.basicOpen f := basicOpen_eq_of_affine (R := CommRingCat.of R) f
  have l' : (Sp R).basicOpen (sI.inv.hom f) ≤ V := hb ▸ l
  have := (isAffineOpen_top (Sp R)).isLocalization_basicOpen (sI.inv.hom f)
  obtain ⟨⟨c, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers (sI.inv.hom f))
    (S := Γ(Sp R, (Sp R).basicOpen (sI.inv.hom f))) (((Sp R).presheaf.map (homOfLE l').op).hom r)
  refine ⟨f ^ n, sI.hom.hom c, _, l', hb ▸ hf, fun h => hf (P.2.mem_of_pow_mem n h), ?_⟩
  rw [mul_comm]
  have e₁ : sI.inv.hom (sI.hom.hom c) = c := sI.hom_inv_id_apply c
  show _ * ((Sp R).presheaf.map _).hom (sI.inv.hom (f ^ n)) = ((Sp R).presheaf.map _).hom (sI.inv.hom (sI.hom.hom c))
  rw [e₁, map_pow sI.inv.hom]
  exact e

theorem regAt_ev {V : (Sp R).Opens} (h : ⊤ ≤ jK R ⁻¹ᵁ V) {P : Sp R} (hP : P ∈ V) (r : Γ(Sp R, V)) :
    RegAt (ev V h r) P := by
  obtain ⟨s, c, V', l, hP', hs, e⟩ := exists_frac hP r
  refine ⟨s, hs, c, ?_⟩
  have e' := congrArg (ev V' (top_le_preimage hP')) e
  rwa [map_mul, ev_toOpen, ev_toOpen, ev_res l h] at e'

theorem ev_injective {V : (Sp R).Opens} (h : ⊤ ≤ jK R ⁻¹ᵁ V) : Function.Injective (ev V h) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  let z : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
  have hP : jK R z ∈ V := h (TopologicalSpace.Opens.mem_top z)
  obtain ⟨s, c, V', l, hP', hs, e⟩ := exists_frac hP r
  have : Nonempty V' := ⟨⟨_, hP'⟩⟩
  have e' := congrArg (ev V' (top_le_preimage hP')) e
  rw [map_mul, ev_toOpen, ev_toOpen, ev_res l h, hr, mul_zero, eq_comm, IsFractionRing.to_map_eq_zero_iff] at e'
  rw [e', map_zero, mul_eq_zero] at e
  rcases e with e | e
  · have e₂ := congrArg (ev V' (top_le_preimage hP')) e
    rw [ev_toOpen, map_zero, IsFractionRing.to_map_eq_zero_iff] at e₂
    exact absurd (e₂ ▸ Ideal.zero_mem _) hs
  · exact map_injective_of_isIntegral (Sp R) (homOfLE l) (e.trans (map_zero _).symm)

theorem exists_ev_eq {V : (Sp R).Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ jK R ⁻¹ᵁ V) {a : FractionRing R}
    (ha : ∀ Q ∈ V, RegAt a Q) : ∃ r, ev V h r = a := by
  let d : Ideal Γ(Sp R, V) :=
    { carrier := {s | ∃ r, ev V h r = ev V h s * a}
      add_mem' := by rintro s t ⟨r, hr⟩ ⟨r', hr'⟩; exact ⟨r + r', by rw [map_add, map_add, hr, hr', add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by rintro t s ⟨r, hr⟩; exact ⟨t * r, by rw [smul_eq_mul, map_mul, map_mul, hr, _root_.mul_assoc]⟩ }
  have : Ideal.span (d : Set Γ(Sp R, V)) = ⊤ := by
    rw [← hV.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun s => (Sp R).basicOpen_le _) fun Q hQ => ?_
    obtain ⟨s, hs, c, e⟩ := ha Q hQ
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨DegPre.toOpen V s, DegPre.toOpen V c, by rw [ev_toOpen, ev_toOpen, e]⟩, ?_⟩
    show Q ∈ (Sp R).basicOpen (((Sp R).presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s))
    rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]
    exact ⟨hQ, hs⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨r, by rw [hr, map_one, _root_.one_mul]⟩

theorem app_eq_iff {V : (Sp R).Opens} (hV : ⊤ ≤ jK R ⁻¹ᵁ V) {W : (Sp (FractionRing R)).Opens} (h : jK R ⁻¹ᵁ V ≤ W)
    (r : Γ(Sp R, V)) (x : Γ(Sp (FractionRing R), W)) :
    ((jK R).app V).hom r = ((Sp (FractionRing R)).presheaf.map (homOfLE h).op).hom x ↔
      ev V hV r = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
        (((Sp (FractionRing R)).presheaf.map (homOfLE (hV.trans h)).op).hom x) := by
  have : Nonempty (⊤ : (Sp (FractionRing R)).Opens) := ⟨⟨(default : PrimeSpectrum (FractionRing R)), trivial⟩⟩
  have i₁ := map_injective_of_isIntegral (Sp (FractionRing R)) (homOfLE hV)
  have i₂ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).1
  rw [← i₁.eq_iff, ← i₂.eq_iff, ← CommRingCat.comp_apply _ _ x, ← Functor.map_comp]
  rfl

theorem psiUnitOn_of_height_one [IsNoetherianRing R] [IsIntegrallyClosed R] (D : DegPre R) (y : D.X) (U : Set (Sp R))
    (H : ∀ P ∈ U, (P : PrimeSpectrum R).asIdeal.height = 1 → ∃ V : (Sp R).Opens, P ∈ V ∧ PsiUnitOn D y V) :
    PsiUnitOn D y U := by
  intro j V hV hVU hj h
  by_cases hE : V = ⊥
  · subst hE
    have : Subsingleton Γ(Sp (FractionRing R), jK R ⁻¹ᵁ ⊥) := ((jK R).app ⊥).hom.codomain_trivial
    exact ⟨1, isUnit_one, Subsingleton.elim (α := Γ(Sp (FractionRing R), jK R ⁻¹ᵁ ⊥)) _ _⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P, P ∈ V := by
    by_contra! hn
    exact hE (le_bot_iff.1 fun P hP => absurd hP (hn P))
  have hT := top_le_preimage hP₀
  let a : (FractionRing R)ˣ := Units.map ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.comp
    ((Sp (FractionRing R)).presheaf.map (homOfLE (hT.trans h)).op).hom).toMonoidHom ((D.psi y).s j)
  have key : ∀ P ∈ V, (P : PrimeSpectrum R).asIdeal.height = 1 → RegAt a.val P ∧ RegAt a⁻¹.val P := by
    intro P hP h1
    obtain ⟨V₁, hP₁, H₁⟩ := H P (hVU hP) h1
    obtain ⟨_, ⟨W, hW, rfl⟩, hPW, hle⟩ :=
      (Sp R).isBasis_affineOpens.exists_subset_of_mem_open (show P ∈ V ⊓ V₁ from ⟨hP, hP₁⟩) (V ⊓ V₁).isOpen
    have l : W ≤ V := fun x hx => (hle hx).1
    have h' : jK R ⁻¹ᵁ W ≤ jK R ⁻¹ᵁ V := fun x hx => l hx
    obtain ⟨r, ⟨u, rfl⟩, e⟩ := H₁ j W hW (fun x hx => (hle hx).2) (l.trans hj) (h'.trans h)
    have hW' := top_le_preimage hPW
    have e' : ev W hW' u.val = a.val := (app_eq_iff hW' (h'.trans h) _ _).1 e
    have e₂ : ev W hW' u⁻¹.val = a⁻¹.val := by
      apply Units.eq_inv_of_mul_eq_one_left
      rw [← e', ← map_mul, Units.mul_inv, map_one]
    exact ⟨e' ▸ regAt_ev hW' hPW _, e₂ ▸ regAt_ev hW' hPW _⟩
  obtain ⟨r, hr⟩ := exists_ev_eq hV hT (regAt_of_height_one V.isOpen fun P hP h1 => (key P hP h1).1)
  obtain ⟨r', hr'⟩ := exists_ev_eq hV hT (regAt_of_height_one V.isOpen fun P hP h1 => (key P hP h1).2)
  refine ⟨r, IsUnit.of_mul_eq_one r' (ev_injective hT ?_), (app_eq_iff hT h _ _).2 hr⟩
  rw [map_mul, hr, hr', Units.mul_inv, map_one]

end Hartogs

section Torsion

theorem pow_eq_one_iff_of_pull {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'} {A : Over S} {A' : Over S'}
    [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ) {x : Over.mk t ⟶ A}
    {x' : Over.mk t' ⟶ A'} (hx : x'.left ≫ Φ = x.left) {k : ℕ} : x' ^ k = 1 ↔ x ^ k = 1 := by
  subst ht
  have e : pushHom hp (Over.mk t') x' = x := Over.OverMorphism.ext hx
  have inj : Function.Injective (pushHom hp (Over.mk t')) := fun a b hab =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun q => q.left) hab) ((Over.w a).trans (Over.w b).symm))
  rw [← inj.eq_iff, map_pow, map_one, e]

theorem fixed_of_extends {R T F : Type} [CommRing R] [IsDomain R] [CommRing T] [Field F] [Algebra R T] [Algebra T F]
    [Algebra (FractionRing R) F]
    (hc : (algebraMap T F).comp (algebraMap R T) = (algebraMap (FractionRing R) F).comp (algebraMap R _))
    {G : Over (Sp R)} [GrpObj G] {A : Over (Sp (FractionRing R))} [GrpObj A] {Φ : A.left ⟶ G.left}
    (hp : IsGrpPullback A G (jK R) Φ) (T' : Subalgebra T F) {k : ℕ}
    (hT : ∀ x : Over.mk (spMap (algebraMap T F)) ⟶ (Over.pullback (spMap (algebraMap R T))).obj G, x ^ k = 1 →
      ∃ x' : Sp T' ⟶ ((Over.pullback (spMap (algebraMap R T))).obj G).left, spMap (T'.val.toRingHom) ≫ x' = x.left)
    (σ : F →ₐ[FractionRing R] F) (hσ : ∀ x ∈ T', σ x = x) (x : TFK (R := R) F ⟶ A) (hx : x ^ k = 1) :
    x.left = spMap σ.toRingHom ≫ x.left := by
  have sq : spMap (algebraMap T F) ≫ spMap (algebraMap R T) = jFK (R := R) F ≫ jK R := by
    rw [← spMap_comp, hc, spMap_comp]
  have w : x.left ≫ A.hom = jFK (R := R) F := Over.w x
  let x₀ : Over.mk (jFK (R := R) F ≫ jK R) ⟶ G := Over.homMk (x.left ≫ Φ) (by
    show (x.left ≫ Φ) ≫ G.hom = jFK (R := R) F ≫ jK R
    rw [Category.assoc, hp.1.w, ← Category.assoc, w])
  have h₀ : x₀ ^ k = 1 := (pow_eq_one_iff_of_pull rfl hp (x := x₀) (x' := x) rfl).1 hx
  let x₁ : Over.mk (spMap (algebraMap T F)) ⟶ (Over.pullback (spMap (algebraMap R T))).obj G :=
    Over.homMk (pullback.lift x₀.left (spMap (algebraMap T F)) ((Over.w x₀).trans sq.symm)) (pullback.lift_snd _ _ _)
  have e₁ : x₁.left ≫ pullback.fst G.hom (spMap (algebraMap R T)) = x₀.left := pullback.lift_fst _ _ _
  obtain ⟨x', hx'⟩ := hT x₁ ((pow_eq_one_iff_of_pull sq (isGrpPullback_pullback G _) e₁).2 h₀)
  have s₁ : spMap σ.toRingHom ≫ spMap T'.val.toRingHom = spMap T'.val.toRingHom := by
    rw [← spMap_comp]
    congr 1
    ext a
    exact hσ a a.2
  have s₂ : spMap σ.toRingHom ≫ jFK (R := R) F = jFK (R := R) F := by
    refine (spMap_comp _ _).symm.trans ?_
    congr 1
    ext a
    exact σ.commutes a
  have s₃ : spMap σ.toRingHom ≫ x₁.left = x₁.left := by
    rw [← hx']
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x') s₁)
  refine hp.1.hom_ext ?_ ?_
  · have := congrArg (· ≫ pullback.fst G.hom (spMap (algebraMap R T))) s₃
    exact (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e₁.symm)).trans
      (((Category.assoc _ _ _).symm.trans this).trans e₁)).symm
  · exact (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) w)).trans (s₂.trans w.symm)).symm

theorem exists_two_le_isUnit (R : Type) [CommRing R] [IsLocalRing R] : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : R) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
  · exact ⟨3, by norm_num, by exact_mod_cast h⟩
  · exact ⟨2, le_rfl, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩

end Torsion

theorem psiUnitOn_abLocus : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, IsOpen (abLocus G) → ∀ y, PsiUnitOn D.toPre y (abLocus G) := by
  intro h₁ h₂ h₃ h₄ h₅ R _ _ _ I hA D A G _ _ hG U hO y
  obtain ⟨hB, -, hc, -, -⟩ := hA
  have := hB.1
  have := hB.2.2.1
  obtain ⟨n, hn, hu⟩ := exists_two_le_isUnit R
  refine psiUnitOn_of_height_one D.toPre y _ fun P hP h1 => ?_
  refine T.psiUnitOn_of_fixed_over_unramified_extension h₁ h₂ R D.toPre D.tau_bimult D.psi_even P h1 n hn (fun j => ?_) y
  have := PrimeSpectrum.isPrime P
  let T := Localization.AtPrime (PrimeSpectrum.asIdeal P)
  let F := AlgebraicClosure (FractionRing R)
  have := isDiscreteValuationRing_of_height_eq_one _ h1 T
  have hcomp : (algebraMap T F).comp (algebraMap R T) = (algebraMap (FractionRing R) F).comp (algebraMap R _) := by
    ext r
    rw [RingHom.comp_apply, RingHom.comp_apply, IsScalarTower.algebraMap_apply T (FractionRing R) F,
      ← IsScalarTower.algebraMap_apply R T (FractionRing R)]
  have hinj : Function.Injective (algebraMap T F) := by
    rw [IsScalarTower.algebraMap_eq T (FractionRing R) F]
    exact (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective T (FractionRing R))
  have hab : abLocus ((Over.pullback (spMap (algebraMap R T))).obj G) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    refine (abLocus_pullback abLocusOne hG (isGrpPullback_pullback G _).1 x).1 ?_
    have le : (spMap (algebraMap R T) x : PrimeSpectrum R).asIdeal ≤ (P : PrimeSpectrum R).asIdeal := by
      intro r hr
      have hr' : algebraMap R T r ∈ (x : PrimeSpectrum T).asIdeal := hr
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff T _ r).1
        (IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime x).ne_top hr')
    exact ((PrimeSpectrum.le_iff_specializes (spMap (algebraMap R T) x) P).mp le).mem_open hO hP
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ (by omega)
  obtain ⟨T', hT', hπ, hx⟩ := GlobalTheory.T.exists_unramified_ext_torsion_points_good_reduction h₁ h₂ T _ (IsSemiAbelian.pullback _ G hG) hab F hinj (n ^ j)
    (by simpa using (hu.map (algebraMap R T)).pow j)
  refine ⟨T'.toSubring, hT', algebraMap T T', fun r => RingHom.congr_fun hcomp r, hπ, fun σ hσ p q hpq => ?_⟩
  have hσR : ∀ r : R, σ (algebraMap (FractionRing R) F (algebraMap R _ r)) =
      algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    hσ _ ((RingHom.congr_fun hcomp r :) ▸ T'.algebraMap_mem _)
  let σ' : F →ₐ[FractionRing R] F := ⟨σ.toRingHom, fun a => RingHom.congr_fun
    (IsLocalization.ringHom_ext (nonZeroDivisors R) (j := σ.toRingHom.comp (algebraMap (FractionRing R) F))
      (k := algebraMap (FractionRing R) F) (RingHom.ext hσR)) a⟩
  have hL : UT.LL := ⟨h₁, h₂, h₃, h₄, h₅⟩
  obtain ⟨f, hf, -, hfi, -⟩ := TorsionIso.torsion_eq hL R I hB D A G hG U F (n ^ j) hk
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have hp : QkToAkU U.toUnifPre F (n ^ j) p (f p) := (hf p _).2 rfl
  obtain ⟨w, hw⟩ := U.ext
  have fix := fixed_of_extends hcomp gp T' hx σ' hσ (f p) (hp w hw).1
  exact (hfi p q).1 ((hf q _).1 ((GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R I hB D A G hG U F F σ' (n ^ j) hk p q (f p) (f p) hpq fix).1 hp))

end GlobalTheory.PsiAbelian
