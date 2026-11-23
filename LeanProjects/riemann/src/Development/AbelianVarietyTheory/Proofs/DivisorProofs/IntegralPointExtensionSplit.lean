import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtChar

open GlobalTheory.HTMap

section Gen

theorem lift_roots {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] (x : A →+* O) {q : ℕ} (hq : q ≠ 0)
    {ζ : A} (hζ : IsPrimitiveRoot ζ q) (hx : IsPrimitiveRoot (x ζ) q) {D : Type} [Group D] (c : D →* Oˣ)
    (hc : ∀ d, c d ^ q = 1) : ∃ χ : D →* Aˣ, ∀ d, x (χ d) = c d := by
  haveI : NeZero q := ⟨hq⟩
  have hb : Function.Bijective (restrictRootsOfUnity x q) := by
    refine ⟨(injective_iff_map_eq_one _).2 fun a ha => ?_, fun a => ?_⟩
    · obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' _ _).1 a.2)
      have h1 : x ((a : Aˣ) : A) = 1 := congrArg (fun z : rootsOfUnity q O => ((z : Oˣ) : O)) ha
      rw [← hi, map_pow, hx.pow_eq_one_iff_dvd, ← hζ.pow_eq_one_iff_dvd, hi] at h1
      exact Subtype.ext (Units.ext h1)
    · obtain ⟨i, -, hi⟩ := hx.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' _ _).1 a.2)
      refine ⟨hζ.toRootsOfUnity ^ i, Subtype.ext (Units.ext ?_)⟩
      rw [← hi, map_pow]
      simp
  let r := MulEquiv.ofBijective _ hb
  refine ⟨(rootsOfUnity q A).subtype.comp (r.symm.toMonoidHom.comp (c.codRestrict (rootsOfUnity q O) hc)), fun d => ?_⟩
  exact congrArg (fun z : rootsOfUnity q O => ((z : Oˣ) : O)) (r.apply_symm_apply ⟨c d, hc d⟩)

theorem prim_map {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [CharZero O] (x : A →+* O) {q : ℕ}
    (hq : q ≠ 0) {ζ : A} (hζ : IsPrimitiveRoot ζ q) : IsPrimitiveRoot (x ζ) q := by
  haveI : NeZero (q : O) := ⟨Nat.cast_ne_zero.2 hq⟩
  have h := hζ.isRoot_cyclotomic (Nat.pos_of_ne_zero hq)
  rw [← Polynomial.isRoot_cyclotomic_iff, Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic q x, Polynomial.eval_map,
    Polynomial.eval₂_hom, h.eq_zero, map_zero]

theorem root_mem {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {q : ℕ} (hq : q ≠ 0) {u : K} (hu : u ^ q = 1) : ∃ a : R, algebraMap R K a = u :=
  IsIntegrallyClosed.isIntegral_iff.1 ⟨Polynomial.X ^ q - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hq, by simp [hu]⟩

def torsEquiv {M N : Type} [CommGroup M] [CommGroup N] (Φ : M ≃* N) (q : ℕ) :
    (powMonoidHom q : M →* M).ker ≃* (powMonoidHom q : N →* N).ker where
  toFun a := ⟨Φ a, MonoidHom.mem_ker.2 (by rw [powMonoidHom_apply, ← map_pow, ← powMonoidHom_apply, MonoidHom.mem_ker.1 a.2, map_one])⟩
  invFun b := ⟨Φ.symm b, MonoidHom.mem_ker.2 (by rw [powMonoidHom_apply, ← map_pow, ← powMonoidHom_apply, MonoidHom.mem_ker.1 b.2, map_one])⟩
  left_inv a := Subtype.ext (Φ.symm_apply_apply a.1)
  right_inv b := Subtype.ext (Φ.apply_symm_apply b.1)
  map_mul' a a' := Subtype.ext (map_mul Φ a.1 a'.1)

end Gen

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {T T' : Scheme.{0}} {y : T ⟶ X} {y' : T' ⟶ X}

def pullEquiv (g : T' ⟶ T) (g' : T ⟶ T') (h : g ≫ y = y') (h' : g' ≫ y' = y) (e₁ : g' ≫ g = 𝟙 T) (e₂ : g ≫ g' = 𝟙 T') :
    (Over.mk y ⟶ G) ≃* (Over.mk y' ⟶ G) where
  toFun := pull g h
  invFun := pull g' h'
  left_inv w := Over.OverMorphism.ext (by rw [pull_left, pull_left, ← Category.assoc, e₁, Category.id_comp])
  right_inv w := Over.OverMorphism.ext (by rw [pull_left, pull_left, ← Category.assoc, e₂, Category.id_comp])
  map_mul' := map_mul (pull g h)

end Pull

section Frac

variable (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def fracToK : FractionRing R →+* K := (FractionRing.algEquiv R K).toRingEquiv.toRingHom

def kToFrac : K →+* FractionRing R := (FractionRing.algEquiv R K).symm.toRingEquiv.toRingHom

theorem fracToK_comp : (fracToK R K).comp (algebraMap R (FractionRing R)) = algebraMap R K :=
  RingHom.ext fun a => (FractionRing.algEquiv R K).commutes a

theorem kToFrac_comp : (kToFrac R K).comp (algebraMap R K) = algebraMap R (FractionRing R) :=
  RingHom.ext fun a => (FractionRing.algEquiv R K).symm.commutes a

theorem fracToK_kToFrac : (fracToK R K).comp (kToFrac R K) = RingHom.id K :=
  RingHom.ext fun a => (FractionRing.algEquiv R K).apply_symm_apply a

theorem kToFrac_fracToK : (kToFrac R K).comp (fracToK R K) = RingHom.id _ :=
  RingHom.ext fun a => (FractionRing.algEquiv R K).symm_apply_apply a

end Frac

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Tr

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (x : Sp R ⟶ X) (q : ℕ)

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

def trEquiv : Gam t x q ≃* TorsK t (spMap (algebraMap R K) ≫ x) q :=
  torsEquiv (pullEquiv (G := t.G) (spMap (fracToK R K)) (spMap (kToFrac R K))
    (by rw [spc_assoc, fracToK_comp]) (by rw [spc_assoc, kToFrac_comp])
    (by rw [spc, kToFrac_fracToK, spMap_id']) (by rw [spc, fracToK_kToFrac, spMap_id'])) q

theorem trEquiv_left (a : Gam t x q) :
    ((trEquiv (K := K) x q a).1).left = spMap (fracToK R K) ≫ a.1.left := rfl

def gen {x : Sp R ⟶ X} {q : ℕ} (σ : Over.mk x ⟶ t.G) (hσ : σ ^ q = 1) : Gam t x q :=
  ⟨pull _ rfl σ, MonoidHom.mem_ker.2 (by rw [powMonoidHom_apply, ← map_pow, hσ, map_one])⟩

theorem trEquiv_gen {σ : Over.mk x ⟶ t.G} (hσ : σ ^ q = 1) (k : TorsK t (spMap (algebraMap R K) ≫ x) q)
    (hk : k.1.left = spMap (algebraMap R K) ≫ σ.left) : trEquiv x q (gen σ hσ) = k :=
  Subtype.ext (Over.OverMorphism.ext (by rw [trEquiv_left, hk]; exact (spc_assoc _ _ _).trans (by rw [fracToK_comp])))

theorem splitTors_of_splitK (h : SplitK t (spMap (algebraMap R K) ≫ x) q) : SplitTors t x q := by
  intro Ω _ io w hw
  have e1 : spMap (io.comp (kToFrac R K)) ≫ spMap (algebraMap R K) ≫ x =
      spMap (io.comp (algebraMap R (FractionRing R))) ≫ x := by
    rw [spc_assoc, RingHom.comp_assoc, kToFrac_comp]
  obtain ⟨w₀, h₀⟩ := h Ω (io.comp (kToFrac R K)) (pull (𝟙 _) (by rw [Category.id_comp, e1]) w)
    (by rw [← map_pow, hw, map_one])
  refine ⟨spMap (kToFrac R K) ≫ w₀, ?_⟩
  rw [← Category.assoc, spc, h₀, pull_left, Category.id_comp]

end Tr

section Pts

variable {A : Type} [CommRing A] [IsDomain A] {x₀ : Sp A ⟶ X} {q : ℕ}

theorem at_pt {P : FP t x₀ q} {𝔮 : Ideal A} (hP : P.Full 𝔮) (h𝔮 : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪 = 𝔮)
    {χ₀ : Gam t x₀ q →* Aˣ} {b : P.Bˣ} (hb : P.Gl (kap χ₀) b) (σ : Over.mk x₀ ⟶ t.G) (hσ : σ ^ q = 1) :
    ∃ β₀ : P.B →+* A, P.At (RingHom.id A) σ.left β₀ ∧ β₀ b = χ₀ (gen σ hσ) := by
  obtain ⟨β₀, hβ₀⟩ := hP.at (φ := RingHom.id A) (fun 𝔪 h𝔪 => by rw [Ideal.comap_id]; exact h𝔮 𝔪 h𝔪) (y := x₀)
    (by rw [spMap_id', Category.id_comp]) σ hσ
  refine ⟨β₀, hβ₀, ?_⟩
  have h2 := hβ₀.map (algebraMap A (FractionRing A))
  rw [RingHom.comp_id] at h2
  have h3 := hb.1 (gen σ hσ).1.left _ h2
  rw [kap_left] at h3
  exact IsFractionRing.injective A (FractionRing A) h3

theorem sect_of {P : FP t x₀ q} (hA : IsUnit P.f) {O : Type} [CommRing O] [IsDomain O] (φ : A →+* O)
    {w : Sp O ⟶ t.G.left} {β : P.B →+* O} (h : P.At φ w β) :
    ∃ β₀ : P.B →+* A, β₀.comp P.str = RingHom.id A ∧ β = φ.comp β₀ := by
  let ℓ : Localization.Away P.f →+* A := IsLocalization.Away.lift P.f (g := RingHom.id A) hA
  have hℓ : ℓ.comp (algebraMap A _) = RingHom.id A := IsLocalization.Away.lift_comp _ _
  have h' := h.map (algebraMap O (FractionRing O))
  have e : (algebraMap O (FractionRing O)).comp φ =
      ((algebraMap O (FractionRing O)).comp (φ.comp ℓ)).comp (algebraMap A (Localization.Away P.f)) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hℓ, RingHom.comp_id]
  rw [e] at h'
  obtain ⟨σ, hσ⟩ := FP.At.sect h'
  refine ⟨ℓ.comp σ.toRingHom, RingHom.ext fun a => ?_, RingHom.ext fun z => ?_⟩
  · show ℓ (σ (algebraMap (Localization.Away P.f) P.B (algebraMap A _ a))) = a
    rw [σ.commutes]
    exact RingHom.congr_fun hℓ a
  · exact IsFractionRing.injective O (FractionRing O) (RingHom.congr_fun hσ z)

end Pts

section Chi

variable {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {q : ℕ}

theorem ex_chi' [IsDomain A] [Finite (Gam t x₀ q)] (hq : q ≠ 0) {ζ : A} (hζ : IsPrimitiveRoot ζ q) {O : Type}
    [CommRing O] [IsDomain O] {x : A →+* O} (hx : IsPrimitiveRoot (x ζ) q) (P : FP t x₀ q) (hu : IsUnit (x P.f))
    (c : TorsChar t (spMap x ≫ x₀) q) : ∃ χ : Gam t x₀ q →* Aˣ, ∀ b, P.Gl (kap χ) b →
      ∀ (w : Over.mk (spMap (algebraMap O O) ≫ spMap x ≫ x₀) ⟶ t.G) (β : P.B →+* O),
        P.At ((algebraMap O O).comp x) w.left β → (c.χ O w : O) = β b := by
  obtain ⟨x', rfl⟩ := FP.ex_lift hu
  have e₁ : spMap x' ≫ spMap (algebraMap A _) ≫ x₀ = spMap (algebraMap O O) ≫ spMap (x'.comp (algebraMap A _)) ≫ x₀ := by
    rw [spc_assoc, spc_assoc]
  have e₂ : spMap P.toK ≫ spMap (algebraMap A _) ≫ x₀ = spMap (algebraMap A (FractionRing A)) ≫ x₀ := by
    rw [spc_assoc, P.toK_comp]
  have ht : ∀ d : P.secs hq, d.1 ^ q = 1 := fun d => d.2.choose_spec.tors
  have ht' : ∀ d : P.secs hq, pull _ e₁ d.1 ^ q = 1 := fun d => by rw [← map_pow, ht, map_one]
  let c₀ : P.secs hq →* Oˣ := MonoidHom.mk' (fun d => c.χ O (pull _ e₁ d.1)) fun d d' => by
    rw [Subgroup.coe_mul, map_mul, c.mul O _ _ (ht' d) (ht' d')]
  obtain ⟨χ₀, h₀⟩ := lift_roots (x'.comp (algebraMap A _)) hq hζ hx c₀ fun d => by
    rw [← map_pow, show d ^ q = 1 from Subtype.ext (ht d), map_one]
  let i : P.secs hq →* Gam t x₀ q := ((pull _ e₂).comp (P.secs hq).subtype).codRestrict _ fun d => by
    show pull _ e₂ d.1 ^ q = 1
    rw [← map_pow, ht, map_one]
  have hi : Function.Injective i := fun d d' h => by
    obtain ⟨β, hβ⟩ := d.2
    obtain ⟨β', hβ'⟩ := d'.2
    have h1 : spMap P.toK ≫ d.1.left = spMap P.toK ≫ d'.1.left := congrArg (fun z : Gam t x₀ q => z.1.left) h
    have h2 := hβ.map P.toK
    rw [h1] at h2
    have h3 : β = β' := RingHom.ext fun z => P.toK_inj (RingHom.congr_fun (h2.mono (hβ'.map P.toK)) z)
    exact Subtype.ext (Over.OverMorphism.ext (by rw [← hβ.2, ← hβ'.2, h3]))
  obtain ⟨χ, hχ⟩ := ext_char hq hζ (fun a => Subtype.ext a.2) i hi χ₀
  refine ⟨χ, fun b hb w β h => ?_⟩
  obtain ⟨σ, hσ⟩ := FP.At.sect (φ := (algebraMap O (FractionRing O)).comp x') (h.map (algebraMap O (FractionRing O)))
  obtain rfl : β = x'.comp σ.toRingHom := RingHom.ext fun z =>
    IsFractionRing.injective O (FractionRing O) (RingHom.congr_fun hσ z)
  let d : P.secs hq := ⟨mkPt _ (P.at_sect σ).over, _, P.at_sect σ⟩
  have h1 : w = pull _ e₁ d.1 := Over.OverMorphism.ext (h.2.symm.trans (spc_assoc _ _ _).symm)
  have h2 : spMap (P.toK.comp σ.toRingHom) ≫ P.u.left = (i d).1.left := (spc_assoc _ _ _).symm
  have h3 := hb.1 _ _ (P.at_sectK σ)
  rw [h2, kap_left, hχ, ← P.toK_comp] at h3
  rw [h1]
  exact (h₀ d).symm.trans (congrArg x' (P.toK_inj h3)).symm

end Chi

theorem ker_pow {M : Type} [CommGroup M] {q : ℕ} (a : (powMonoidHom q : M →* M).ker) : a ^ q = 1 :=
  Subtype.ext (MonoidHom.mem_ker.1 a.2)

theorem induced_chars : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K] (ξ : Sp K ⟶ X) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) → SplitK t ξ q → ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K] (x : Sp R ⟶ X), spMap (algebraMap R K) ≫ x = ξ → Finite (TorsK t ξ q →* Kˣ) ∧ ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X), IsLocalHom ψ → spMap ψ ≫ x = z → (∀ χ : TorsK t ξ q →* Kˣ, ∃ c : TorsChar t z q, InducedBy χ x (algebraMap R K) ψ c) ∧ (∀ c : TorsChar t z q, ∃ χ : TorsK t ξ q →* Kˣ, InducedBy χ x (algebraMap R K) ψ c) ∧ ∀ (χ : TorsK t ξ q →* Kˣ) (c c' : TorsChar t z q), InducedBy χ x (algebraMap R K) ψ c → InducedBy χ x (algebraMap R K) ψ c' → Agree c c' := by
  intro E _ _ _ H X _ t K _ _ ξ q hq hζK hs R _ _ _ _ _ _ x hx
  obtain ⟨ζ, hζ⟩ := hζK
  subst hx
  haveI : CharZero R := ⟨fun m n h => Nat.cast_injective (R := K) (by simpa using congrArg (algebraMap R K) h)⟩
  have hF := ex_full hq (splitTors_of_splitK x q hs)
  haveI := finite_gam hF
  haveI : Finite (TorsK t (spMap (algebraMap R K) ≫ x) q) := Finite.of_equiv _ (trEquiv x q).toEquiv
  obtain ⟨ζR, hζR⟩ := root_mem (R := R) hq hζ.pow_eq_one
  have hζR' : IsPrimitiveRoot ζR q :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap R K) (by rw [hζR]; exact hζ) (IsFractionRing.injective R K)
  refine ⟨inferInstance, fun p _ ψ z _ hz => ?_⟩
  subst hz
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  obtain ⟨P, hP⟩ := hF ((IsLocalRing.maximalIdeal _).comap ψ) inferInstance
  have h𝔮 : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 𝔪 = (IsLocalRing.maximalIdeal _).comap ψ := fun 𝔪 h𝔪 => by
    rw [IsLocalRing.maximalIdeal_comap ψ]; exact IsLocalRing.eq_maximalIdeal h𝔪
  have hu : IsUnit (ψ P.f) := by by_contra hn; exact hP.1 hn
  have hA : IsUnit P.f := by
    by_contra hn; exact hP.1 (by rw [IsLocalRing.maximalIdeal_comap ψ]; exact hn)
  have hψ : (algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])).comp ψ = ψ.comp (RingHom.id R) := by
    rw [Algebra.algebraMap_self, RingHom.id_comp, RingHom.comp_id]
  have hval : ∀ {χ₀ : Gam t x q →* Rˣ} {b : P.Bˣ}, P.Gl (kap χ₀) b → ∀ (c : TorsChar t (spMap ψ ≫ x) q),
      (∀ (w : Over.mk (spMap (algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])) ≫ spMap ψ ≫ x) ⟶ t.G) (β : P.B →+* ↥(intO ℂ_[p])),
        P.At ((algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])).comp ψ) w.left β → (c.χ _ w : ↥(intO ℂ_[p])) = β b) →
      ∀ (σ : Over.mk x ⟶ t.G) (hσ : σ ^ q = 1)
        (w : Over.mk (spMap (algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])) ≫ spMap ψ ≫ x) ⟶ t.G),
        w.left = spMap ψ ≫ σ.left → (c.χ _ w : ↥(intO ℂ_[p])) = ψ (χ₀ (gen σ hσ)) := by
    intro χ₀ b hb c hc σ hσ w hw
    obtain ⟨β₀, h1, h2⟩ := at_pt hP h𝔮 hb σ hσ
    have h3 := h1.map ψ
    rw [← hψ, ← hw] at h3
    rw [hc w _ h3, RingHom.comp_apply, h2]
  refine ⟨fun χ => ?_, fun c => ?_, fun χ c c' hc hc' => ?_⟩
  · obtain ⟨χ₀, h₀⟩ := lift_roots (algebraMap R K) hq hζR' (by rw [hζR]; exact hζ)
      (χ.comp (trEquiv x q).toMonoidHom) fun d => by rw [← map_pow, ker_pow, map_one]
    obtain ⟨b, hb⟩ := P.ex_gl (mult_kap χ₀)
    obtain ⟨c, hc⟩ := ex_char hP hb
    refine ⟨c, fun σ k a w hσ hk hw ha => ?_⟩
    rw [hval hb c (hc _) σ hσ w hw]
    congr 1
    apply IsFractionRing.injective R K
    rw [h₀, ha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, trEquiv_gen x q hσ k hk]
  · obtain ⟨χ₀, h₀⟩ := ex_chi' hq hζR' (prim_map ψ hq hζR') P hu c
    refine ⟨(Units.map (algebraMap R K).toMonoidHom).comp (χ₀.comp (trEquiv x q).symm.toMonoidHom),
      fun σ k a w hσ hk hw ha => ?_⟩
    obtain ⟨b, hb⟩ := P.ex_gl (mult_kap χ₀)
    rw [hval hb c (h₀ b hb) σ hσ w hw]
    congr 1
    apply IsFractionRing.injective R K
    rw [ha, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← trEquiv_gen x q hσ k hk,
      MulEquiv.symm_apply_apply, Units.coe_map]
    rfl
  · refine fun B _ _ _ w hw => GlobalTheory.T.torsionChar_eq_of_eq_on_torsion E H X t ℂ_[p] _ q hq c c' (fun w hw => ?_) B w hw
    obtain ⟨β, hβ⟩ := hP.at_fin _ w hw
    obtain ⟨β₀, hβ₀, rfl⟩ := sect_of hA _ hβ
    have hσA : P.At (RingHom.id R) (spMap β₀ ≫ P.u.left) β₀ := ⟨hβ₀, rfl⟩
    let σ : Over.mk x ⟶ t.G := mkPt (spMap β₀ ≫ P.u.left) (hσA.over.trans (by rw [spMap_id', Category.id_comp]))
    have hσ : σ ^ q = 1 := FP.At.tors (w := σ) hσA
    have hw' : w.left = spMap ψ ≫ σ.left := by
      rw [← hβ.2, Algebra.algebraMap_self, RingHom.id_comp, ← spc_assoc]; rfl
    let k := trEquiv (K := K) x q (gen σ hσ)
    have hk : k.1.left = spMap (algebraMap R K) ≫ σ.left := by
      rw [trEquiv_left]; exact (spc_assoc _ _ _).trans (by rw [fracToK_comp])
    obtain ⟨a, ha⟩ := root_mem (R := R) hq (u := ((χ k : Kˣ) : K))
      (by rw [← Units.val_pow_eq_pow_val, ← map_pow, ker_pow, map_one, Units.val_one])
    exact Units.ext ((hc σ k a w hσ hk hw' ha).trans (hc' σ k a w hσ hk hw' ha).symm)

end GlobalTheory.HtChar
