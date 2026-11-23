import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharEqOfEqOnTorsionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDlogUniqueModuloPStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFiniteTorsionSplittingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescentStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.HTMap

attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {T T' : Scheme.{0}} {y : T ⟶ X} {y' : T' ⟶ X}

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by rw [← Spec.map_comp]; rfl

theorem spc_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) {Z : Scheme.{0}}
    (h : Sp A ⟶ Z) : spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by rw [← Category.assoc, spc]

def pull (g : T' ⟶ T) (h : g ≫ y = y') : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G) := Formalism.L2.Pj.preHom (Over.homMk g h)

theorem pull_left (g : T' ⟶ T) (h : g ≫ y = y') (w : Over.mk y ⟶ G) : (pull g h w).left = g ≫ w.left := rfl

omit [GrpObj G] in
theorem over_w (w : Over.mk y ⟶ G) : w.left ≫ G.hom = y := Over.w w

omit [GrpObj G] in

def mkPt (w : T ⟶ G.left) (h : w ≫ G.hom = y) : Over.mk y ⟶ G := Over.homMk w h

omit [GrpObj G] in
theorem mkPt_left (w : T ⟶ G.left) (h : w ≫ G.hom = y) : (mkPt w h).left = w := rfl

theorem eq_pull {g : T' ⟶ T} (w : Over.mk y ⟶ G) (w' : Over.mk y' ⟶ G) (e : w'.left = g ≫ w.left) :
    ∃ h : g ≫ y = y', w' = pull g h w :=
  ⟨by rw [← over_w w, ← over_w w', e, Category.assoc], Over.OverMorphism.ext e⟩

theorem tors_of {g : T' ⟶ T} {w : Over.mk y ⟶ G} {w' : Over.mk y' ⟶ G} (e : w'.left = g ≫ w.left) {q : ℕ}
    (hw : w ^ q = 1) : w' ^ q = 1 := by
  obtain ⟨h, rfl⟩ := eq_pull w w' e
  rw [← map_pow, hw, map_one]

theorem mul_of {g : T' ⟶ T} {w₁ w₂ : Over.mk y ⟶ G} {w₁' w₂' : Over.mk y' ⟶ G} (e₁ : w₁'.left = g ≫ w₁.left)
    (e₂ : w₂'.left = g ≫ w₂.left) : (w₁' * w₂').left = g ≫ (w₁ * w₂).left := by
  obtain ⟨h, rfl⟩ := eq_pull w₁ w₁' e₁
  obtain ⟨h', rfl⟩ := eq_pull w₂ w₂' e₂
  rw [← map_mul]; rfl

theorem one_of {g : T' ⟶ T} (h : g ≫ y = y') : (1 : Over.mk y' ⟶ G).left = g ≫ (1 : Over.mk y ⟶ G).left := by
  rw [← map_one (pull (G := G) g h)]; rfl

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {q : ℕ}

variable (t x₀ q) in

structure FP : Type 1 where
  f : A
  B : Type
  [ring : CommRing B]
  [alg : Algebra (Localization.Away f) B]
  u : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap A (Localization.Away f)) ≫ x₀) ⟶ t.G
  ne : f ≠ 0
  fin : IsFinPart t (spMap (algebraMap A (Localization.Away f)) ≫ x₀) q u

attribute [instance] FP.ring FP.alg

namespace FP

variable (P : FP t x₀ q) {S S' : Type} [CommRing S] [CommRing S']

def str : A →+* P.B := (algebraMap (Localization.Away P.f) P.B).comp (algebraMap A (Localization.Away P.f))

def At (φ : A →+* S) (w : Sp S ⟶ t.G.left) (β : P.B →+* S) : Prop := β.comp P.str = φ ∧ spMap β ≫ P.u.left = w

def Full (𝔮 : Ideal A) : Prop :=
  P.f ∉ 𝔮 ∧ ∀ (k : Type) [Field k] (φ : A →+* k), RingHom.ker φ = 𝔮 →
    ∀ y : Sp k ⟶ X, y = spMap φ ≫ x₀ → ∀ w : Over.mk y ⟶ t.G, w ^ q = 1 → ∃ β, P.At φ w.left β

variable {P}

theorem alg_ext {β β' : P.B →+* S} (h : β.comp P.str = β'.comp P.str) :
    β.comp (algebraMap (Localization.Away P.f) P.B) = β'.comp (algebraMap (Localization.Away P.f) P.B) :=
  IsLocalization.ringHom_ext (Submonoid.powers P.f) h

theorem At.mono {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β β' : P.B →+* S} (h : P.At φ w β) (h' : P.At φ w β') :
    β = β' := P.fin.mono S β β' (alg_ext (h.1.trans h'.1.symm)) (h.2.trans h'.2.symm)

theorem At.map {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) (ψ : S →+* S') :
    P.At (ψ.comp φ) (spMap ψ ≫ w) (ψ.comp β) :=
  ⟨by rw [← h.1]; rfl, by rw [← h.2]; exact (spc_assoc _ _ _).symm⟩

theorem At.over {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) :
    w ≫ t.G.hom = spMap φ ≫ x₀ := by
  rw [← h.2, ← h.1, Category.assoc, over_w P.u, spc_assoc, spc_assoc]; rfl

theorem At.tors {φ : A →+* S} {y : Sp S ⟶ X} {w : Over.mk y ⟶ t.G} {β : P.B →+* S} (h : P.At φ w.left β) :
    w ^ q = 1 := tors_of h.2.symm P.fin.tors

theorem At.unit {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) : IsUnit (φ P.f) := by
  rw [← h.1]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away P.f) P.f).map
    (algebraMap (Localization.Away P.f) P.B)).map β

theorem at_self : P.At P.str P.u.left (RingHom.id _) :=
  ⟨rfl, by rw [show spMap (RingHom.id P.B) = 𝟙 _ from Spec.map_id _, Category.id_comp]⟩

theorem at_iff (φ : Localization.Away P.f →+* S) (w : Sp S ⟶ t.G.left) :
    (∃ β, P.At (φ.comp (algebraMap A _)) w β) ↔ Thru t P.u.left φ w :=
  exists_congr fun _ => and_congr_left fun _ =>
    ⟨fun h => IsLocalization.ringHom_ext (Submonoid.powers P.f) h, fun h => by rw [← h]; rfl⟩

theorem ex_lift {φ : A →+* S} (hu : IsUnit (φ P.f)) :
    ∃ φ' : Localization.Away P.f →+* S, φ'.comp (algebraMap A _) = φ :=
  ⟨IsLocalization.Away.lift P.f hu, IsLocalization.Away.lift_comp _ _⟩

theorem at_open {φ : A →+* S} (hu : IsUnit (φ P.f)) {y : Sp S ⟶ X} (hy : y = spMap φ ≫ x₀) (w : Over.mk y ⟶ t.G)
    (hw : w ^ q = 1) (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      ∃ β, P.At ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ w.left) β) :
    ∃ β, P.At φ w.left β := by
  obtain ⟨φ', rfl⟩ := ex_lift hu
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.isOpen S φ' w hw fun 𝔪 h𝔪 => (at_iff _ _).1 (h 𝔪 h𝔪))

theorem at_one {φ : A →+* S} (hu : IsUnit (φ P.f)) {y : Sp S ⟶ X} (hy : y = spMap φ ≫ x₀) :
    ∃ β, P.At φ (1 : Over.mk y ⟶ t.G).left β := by
  obtain ⟨φ', rfl⟩ := ex_lift hu
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.one S φ')

theorem At.mul {φ : A →+* S} {y : Sp S ⟶ X} {w w' : Over.mk y ⟶ t.G} {β β' : P.B →+* S} (h : P.At φ w.left β)
    (h' : P.At φ w'.left β') : ∃ β'', P.At φ (w * w').left β'' := by
  have hy : y = spMap φ ≫ x₀ := (over_w w).symm.trans h.over
  obtain ⟨φ', rfl⟩ := ex_lift h.unit
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.mul S φ' w w' ((at_iff _ _).1 ⟨_, h⟩) ((at_iff _ _).1 ⟨_, h'⟩))

theorem Full.at {𝔮 : Ideal A} (hP : P.Full 𝔮) {φ : A →+* S} (hφ : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 𝔪.comap φ = 𝔮)
    {y : Sp S ⟶ X} (hy : y = spMap φ ≫ x₀) (w : Over.mk y ⟶ t.G) (hw : w ^ q = 1) : ∃ β, P.At φ w.left β := by
  have hu : IsUnit (φ P.f) := by
    by_contra hn
    obtain ⟨𝔪, h𝔪, hm⟩ := exists_max_ideal_of_mem_nonunits hn
    exact hP.1 (hφ 𝔪 h𝔪 ▸ hm)
  refine at_open hu hy w hw fun 𝔪 h𝔪 => ?_
  letI := Ideal.Quotient.field 𝔪
  have e : spMap (Ideal.Quotient.mk 𝔪) ≫ y = spMap ((Ideal.Quotient.mk 𝔪).comp φ) ≫ x₀ := by rw [hy, spc_assoc]
  exact hP.2 (S ⧸ 𝔪) _ (by rw [← RingHom.comap_ker, Ideal.mk_ker, hφ 𝔪 h𝔪]) _ rfl (pull _ e w)
    (tors_of (pull_left _ e w) hw)

variable (P) in

def Gl (κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ) (b : P.Bˣ) : Prop :=
  (∀ w β, P.At (algebraMap A (FractionRing A)) w β → β b = algebraMap A (FractionRing A) (κ w)) ∧
    ∀ (S : Type) [CommRing S] (φ : A →+* S) (y : Sp S ⟶ X) (w w' : Over.mk y ⟶ t.G) (β β' β'' : P.B →+* S),
      P.At φ w.left β → P.At φ w'.left β' → P.At φ (w * w').left β'' → β'' b = β b * β' b

end FP

variable (t x₀ q) in

def Mult (κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ) : Prop :=
  ∀ w w' : Over.mk (spMap (algebraMap A (FractionRing A)) ≫ x₀) ⟶ t.G, w ^ q = 1 → w' ^ q = 1 →
    κ (w * w').left = κ w.left * κ w'.left

variable (x₀ q) in

def Val (κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ) {S : Type} [CommRing S] (φ : A →+* S) (w : Sp S ⟶ t.G.left)
    (s : S) : Prop :=
  ∃ (P : FP t x₀ q) (b : P.Bˣ) (β : P.B →+* S), P.Gl κ b ∧ P.At φ w β ∧ β b = s

theorem Val.map {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ} {S S' : Type} [CommRing S] [CommRing S'] {φ : A →+* S}
    {w : Sp S ⟶ t.G.left} {s : S} (h : Val x₀ q κ φ w s) (ψ : S →+* S') :
    Val x₀ q κ (ψ.comp φ) (spMap ψ ≫ w) (ψ s) := by
  obtain ⟨P, b, β, h1, h2, rfl⟩ := h
  exact ⟨P, b, _, h1, h2.map ψ, rfl⟩

theorem ex_full [IsLocallyNoetherian X] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] (hq : q ≠ 0)
    (hs : SplitTors t x₀ q) (𝔮 : Ideal A) (h𝔮 : 𝔮.IsPrime) : ∃ P : FP t x₀ q, P.Full 𝔮 := by
  obtain ⟨f, B, _, _, u, hf, hu, h⟩ := GlobalTheory.T.exists_local_finite_torsion_splitting E H X t A x₀ q hq hs 𝔮 h𝔮
  have hf0 : f ≠ 0 := fun h0 => hf (by rw [h0]; exact 𝔮.zero_mem)
  let P : FP t x₀ q := { f := f, B := B, u := u, ne := hf0, fin := hu }
  refine ⟨P, hf, fun k _ φ hφ y hy w hw => ?_⟩
  have hu' : IsUnit (φ P.f) := IsUnit.mk0 _ fun h0 => hf (by rw [← hφ]; exact h0)
  obtain ⟨φ', rfl⟩ := FP.ex_lift hu'
  rw [← spc_assoc] at hy
  subst hy
  exact (FP.at_iff (P := P) φ' _).2 (h k φ' hφ w hw)

section Dom

variable [IsDomain A]

namespace FP

variable (P : FP t x₀ q)

def toK : Localization.Away P.f →+* FractionRing A :=
  IsLocalization.Away.lift P.f (g := algebraMap A (FractionRing A)) (IsUnit.mk0 _ (by simpa using P.ne))

theorem toK_comp : P.toK.comp (algebraMap A _) = algebraMap A (FractionRing A) := IsLocalization.Away.lift_comp _ _

theorem toK_inj : Function.Injective P.toK := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj P.f z
  have h1 := congrArg P.toK h
  rw [map_mul, hz, zero_mul] at h1
  have h2 : algebraMap A (FractionRing A) a = 0 := by rw [← P.toK_comp]; exact h1.symm
  rw [(IsFractionRing.to_map_eq_zero_iff).1 h2, map_zero] at h
  exact ((IsLocalization.Away.algebraMap_isUnit P.f).pow n).mul_left_eq_zero.1 h

theorem at_sect (σ : P.B →ₐ[Localization.Away P.f] Localization.Away P.f) :
    P.At (algebraMap A (Localization.Away P.f)) (spMap σ.toRingHom ≫ P.u.left) σ.toRingHom :=
  ⟨RingHom.ext fun a => σ.commutes _, rfl⟩

theorem at_sectK (σ : P.B →ₐ[Localization.Away P.f] Localization.Away P.f) :
    P.At (algebraMap A (FractionRing A)) (spMap (P.toK.comp σ.toRingHom) ≫ P.u.left) (P.toK.comp σ.toRingHom) :=
  ⟨((P.at_sect σ).map P.toK).1.trans P.toK_comp, rfl⟩

variable {P}

omit [IsDomain A] in
theorem At.sect {k : Type} [Field k] {φ : Localization.Away P.f →+* k} {w : Sp k ⟶ t.G.left} {β : P.B →+* k}
    (h : P.At (φ.comp (algebraMap A _)) w β) :
    ∃ σ : P.B →ₐ[Localization.Away P.f] Localization.Away P.f, β = φ.comp σ.toRingHom := by
  obtain ⟨σ, hσ⟩ := P.fin.sect k β
  have e : β.comp (algebraMap (Localization.Away P.f) P.B) = φ :=
    IsLocalization.ringHom_ext (Submonoid.powers P.f) h.1
  exact ⟨σ, by rw [← e]; exact hσ⟩

theorem At.sectK {w : Sp (FractionRing A) ⟶ t.G.left} {β : P.B →+* FractionRing A}
    (h : P.At (algebraMap A (FractionRing A)) w β) :
    ∃ σ : P.B →ₐ[Localization.Away P.f] Localization.Away P.f, β = P.toK.comp σ.toRingHom :=
  At.sect (w := w) (by rw [P.toK_comp]; exact h)

theorem dom : IsDomain (Localization.Away P.f) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors P.ne)

variable (P) in
theorem ex_gl [IsIntegrallyClosed A] {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ} (hκ : Mult t x₀ q κ) :
    ∃ b, P.Gl κ b := by
  haveI := P.dom
  haveI : IsIntegrallyClosed (Localization.Away P.f) :=
    isIntegrallyClosed_of_isLocalization _ _ (powers_le_nonZeroDivisors_of_noZeroDivisors P.ne)
  obtain ⟨b, hb, hb'⟩ := GlobalTheory.T.torsion_character_cocycle_descent E H X t (Localization.Away P.f) _ q P.B P.u P.fin
    (fun σ => Units.map (algebraMap A (Localization.Away P.f)).toMonoidHom
      (κ (spMap (P.toK.comp σ.toRingHom) ≫ P.u.left))) (fun σ σ' σ'' w w' h h' h'' => by
      have e : spMap P.toK ≫ spMap (RingHom.id _) ≫ spMap (algebraMap A (Localization.Away P.f)) ≫ x₀ =
          spMap (algebraMap A (FractionRing A)) ≫ x₀ := by
        rw [spc_assoc, spc_assoc, RingHom.comp_id, P.toK_comp]
      have key : ∀ (τ : P.B →ₐ[Localization.Away P.f] Localization.Away P.f) v,
          spMap τ.toRingHom ≫ P.u.left = Over.Hom.left v →
          spMap (P.toK.comp τ.toRingHom) ≫ P.u.left = (pull (G := t.G) _ e v).left := fun τ v hv => by
        rw [pull_left, ← hv]; exact (spc_assoc _ _ _).symm
      have h1 := key _ _ h
      have h2 := key _ _ h'
      rw [← map_mul, key _ _ h'', h1, h2, map_mul (pull _ e),
        hκ _ _ (tors_of h1.symm P.fin.tors) (tors_of h2.symm P.fin.tors)])
  refine ⟨b, fun w β h => ?_, fun S _ φ y w w' β β' β'' h h' h'' => ?_⟩
  · obtain ⟨σ, rfl⟩ := h.sectK
    rw [← h.2, ← P.toK_comp]
    exact congrArg P.toK (hb σ)
  · have hy : y = spMap φ ≫ x₀ := (over_w w).symm.trans h.over
    rw [← h.1, str, ← RingHom.comp_assoc, ← spc_assoc] at hy
    subst hy
    exact hb' S _ w w' β β' β'' rfl (alg_ext (h'.1.trans h.1.symm)) (alg_ext (h''.1.trans h.1.symm)) h.2 h'.2 h''.2

theorem sep (𝔫 : Ideal P.B) [𝔫.IsPrime] (z : Localization.AtPrime 𝔫)
    (h : ∀ τ : Localization.AtPrime 𝔫 →+* FractionRing A,
      τ.comp ((algebraMap P.B _).comp P.str) = algebraMap A _ → τ z = 0) : z = 0 := by
  haveI := P.dom
  haveI := P.fin.finite
  haveI := P.fin.free
  haveI := Fintype.ofFinite (P.B →ₐ[Localization.Away P.f] Localization.Away P.f)
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔫.primeCompl z
  have key : ∀ σ : P.B →ₐ[Localization.Away P.f] Localization.Away P.f, ∃ r ∈ 𝔫.primeCompl, σ (r * c) = 0 := by
    intro σ
    by_cases h0 : ∃ r ∈ 𝔫.primeCompl, σ r = 0
    · obtain ⟨r, hr, h0⟩ := h0
      exact ⟨r, hr, by rw [map_mul, h0, zero_mul]⟩
    have hu : ∀ r : 𝔫.primeCompl, IsUnit (P.toK.comp σ.toRingHom r) := fun r =>
      IsUnit.mk0 _ fun h1 => h0 ⟨r, r.2, P.toK_inj (h1.trans (map_zero _).symm)⟩
    have h1 := h (IsLocalization.lift hu) (by
      rw [← RingHom.comp_assoc, IsLocalization.lift_comp]; exact (P.at_sectK σ).1)
    rw [IsLocalization.lift_mk'_spec, mul_zero] at h1
    exact ⟨1, one_mem _, by rw [_root_.one_mul]; exact P.toK_inj (h1.trans (map_zero _).symm)⟩
  choose r hr hr' using key
  refine (IsLocalization.mk'_eq_zero_iff _ _).2 ⟨⟨∏ σ, r σ, prod_mem fun σ _ => hr σ⟩, P.fin.inj _ fun σ => ?_⟩
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem r (Finset.mem_univ σ)
  show σ ((∏ σ, r σ) * c) = 0
  rw [hd, mul_right_comm, map_mul, hr', zero_mul]

theorem Gl.loc {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ} {P' : FP t x₀ q} {b : P.Bˣ} {b' : P'.Bˣ} (hb : P.Gl κ b)
    (hb' : P'.Gl κ b') {S : Type} [CommRing S] {φ : A →+* S} (𝔪 : Ideal S) [𝔪.IsPrime] (hP' : P'.Full (𝔪.comap φ))
    {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) :
    ∃ δ, P'.At ((algebraMap S (Localization.AtPrime 𝔪)).comp φ) (spMap (algebraMap S _) ≫ w) δ ∧
      δ b' = algebraMap S _ (β b) := by
  let a := algebraMap P.B (Localization.AtPrime (𝔪.comap β))
  have h1 := (at_self (P := P)).map a
  obtain ⟨δ, hδ⟩ := hP'.at (φ := a.comp P.str) (fun 𝔪' h𝔪' => by
    rw [IsLocalRing.eq_maximalIdeal h𝔪', ← Ideal.comap_comap, show Ideal.comap a _ = _ from
      Localization.AtPrime.under_maximalIdeal,
      Ideal.comap_comap, h.1]) h1.over (mkPt (spMap a ≫ P.u.left) rfl)
    (At.tors (w := mkPt (spMap a ≫ P.u.left) rfl) h1)
  have h2 : δ b' = a b := by
    refine sub_eq_zero.1 (sep _ _ fun τ hτ => ?_)
    have h3 := hδ.map τ
    have h4 := h1.map τ
    rw [hτ] at h3 h4
    rw [map_sub, sub_eq_zero]
    exact (hb'.1 _ _ h3).trans (hb.1 _ _ h4).symm
  let l := Localization.localRingHom (𝔪.comap β) 𝔪 β rfl
  have hl : l.comp a = (algebraMap S _).comp β := RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ rfl z
  refine ⟨l.comp δ, ?_, ?_⟩
  · have h5 := hδ.map l
    rw [← RingHom.comp_assoc, hl, RingHom.comp_assoc, h.1] at h5
    refine ⟨h5.1, h5.2.trans ?_⟩
    show spMap l ≫ spMap a ≫ P.u.left = _
    rw [← h.2]
    exact (spc_assoc _ _ _).trans ((congrArg (fun z => spMap z ≫ P.u.left) hl).trans (spc_assoc _ _ _).symm)
  · rw [RingHom.comp_apply, h2]
    exact RingHom.congr_fun hl _

end FP

variable [IsIntegrallyClosed A] {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ}

theorem Val.uniq (hF : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → ∃ P : FP t x₀ q, P.Full 𝔮) (hκ : Mult t x₀ q κ) {S : Type}
    [CommRing S] {φ : A →+* S} {w : Sp S ⟶ t.G.left} {s s' : S} (h : Val x₀ q κ φ w s) (h' : Val x₀ q κ φ w s') :
    s = s' := by
  obtain ⟨P, b, β, h1, h2, rfl⟩ := h
  obtain ⟨P', b', β', h1', h2', rfl⟩ := h'
  refine Module.eq_of_localization_maximal (R := S) (fun 𝔪 _ => Localization.AtPrime 𝔪)
    (fun 𝔪 _ => Algebra.linearMap S _) _ _ fun 𝔪 _ => ?_
  obtain ⟨Q, hQ⟩ := hF (𝔪.comap φ) inferInstance
  obtain ⟨c, hc⟩ := Q.ex_gl hκ
  obtain ⟨δ, h3, h4⟩ := h1.loc hc 𝔪 hQ h2
  obtain ⟨δ', h3', h4'⟩ := h1'.loc hc 𝔪 hQ h2'
  exact h4.symm.trans ((congrArg (fun z => z c) (h3.mono h3')).trans h4')

end Dom

section Tan

variable {S : Type} [CommRing S] {x : Sp S ⟶ X}

theorem tan_tors {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) (hq : (q : S) = 0)
    {y : Sp (DualNumber S) ⟶ X} (w : Over.mk y ⟶ t.G) (e : w.left = v) : w ^ q = 1 := by
  have key : ∀ n : ℕ, smT x (n : S) (ovT hv) = ovT hv ^ n := fun n => by
    induction n with
    | zero => rw [Nat.cast_zero, pow_zero, smT_zero_ovT]
    | succ n ih => rw [Nat.cast_succ, smT_add x _ (smT_zero_ovT hv), ih, smT_unit, pow_succ]
  have h : ovT hv ^ q = 1 := by rw [← key, hq, smT_zero_ovT]
  exact tors_of (w := ovT hv) (g := 𝟙 _) (e.trans (Category.id_comp _).symm) h

theorem comb_tan {g : ℕ} {e : Fin g → (Sp (DualNumber S) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i)) {a : Fin g → S}
    {v : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x e a v) : IsTanAtG t x v := by
  rw [← (isCombAtG_iff t x (fun j => ovT (he j)) _ _).1 h]
  exact isTanAtG_of _ (combT_tan _ _ (fun j => smT_zero_ovT _) _)

theorem comb_single {g : ℕ} {e : Fin g → (Sp (DualNumber S) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i)) (i : Fin g) :
    IsCombAtG t x e (Pi.single i 1) (e i) :=
  (isCombAtG_iff t x (fun j => ovT (he j)) _ _).2 (by rw [combT_single _ _ fun j => smT_zero_ovT _]; rfl)

theorem tan_at (P : FP t x₀ q) {φ : A →+* S} {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t (spMap φ ≫ x₀) v)
    (hq : (q : S) = 0) {S' : Type} [CommRing S'] (ψ : DualNumber S →+* S')
    (hu : IsUnit (ψ (((algebraMap S (DualNumber S)).comp φ) P.f))) :
    ∃ β, P.At (ψ.comp ((algebraMap S (DualNumber S)).comp φ)) (spMap ψ ≫ v) β := by
  refine FP.at_open (φ := ψ.comp ((algebraMap S (DualNumber S)).comp φ)) hu ?_ (mkPt (spMap ψ ≫ v) rfl)
    (tors_of (g := spMap ψ) (w := ovT hv) rfl (tan_tors hv hq _ rfl)) fun 𝔪 h𝔪 => ?_
  · rw [Category.assoc, hv.1, spc_assoc, spc_assoc]
  let ρ := (Ideal.Quotient.mk 𝔪).comp ψ
  have hρ : ρ = (ρ.comp (algebraMap S (DualNumber S))).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    refine RingHom.ext fun z => ?_
    have h0 : ρ (TrivSqZeroExt.inr z.snd) = 0 :=
      mul_self_eq_zero.1 (by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero])
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z, map_add, h0, add_zero]
    rfl
  have e : spMap (Ideal.Quotient.mk 𝔪) ≫ spMap ψ ≫ v =
      (1 : Over.mk (spMap (ρ.comp (algebraMap S (DualNumber S))) ≫ spMap φ ≫ x₀) ⟶ t.G).left := by
    rw [one_of rfl, ← hv.2]
    exact (spc_assoc _ _ _).trans ((congrArg (fun z => spMap z ≫ v) hρ).trans (spc_assoc _ _ _).symm)
  rw [mkPt_left, e]
  exact FP.at_one (hu.map (Ideal.Quotient.mk 𝔪)) (spc_assoc _ _ _)

theorem dlog_congr {p n : ℕ} {c c' : TorsChar t x (p ^ n)} {g : ℕ} {e : Fin g → (Sp (DualNumber S) ⟶ t.G.left)}
    (he : ∀ i, IsTanAtG t x (e i)) {h : Fin g → S}
    (hc : ∀ (B : Type) [CommRing B] [Algebra S B] [Module.Finite S B]
      (w : Over.mk (spMap (algebraMap S B) ≫ x) ⟶ t.G), w ^ (p ^ n) = 1 → c.χ B w = c'.χ B w)
    (hd : DlogIs t p n c' e h) : DlogIs t p n c e h := fun a v hv w hw => by
  rw [hc _ w (tan_tors (GlobalTheory.FactorDepth.isTanAtG_map t _ (comb_tan he hv)) ?_ w hw)]
  · exact hd a v hv w hw
  · rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.mem_span_singleton_self _

end Tan

theorem Val.map' {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ} {S S' S'' : Type} [CommRing S] [CommRing S']
    [CommRing S''] {φ : A →+* S} {w : Sp S ⟶ t.G.left} {ψ : S →+* S'} {s : S'}
    (h : Val x₀ q κ (ψ.comp φ) (spMap ψ ≫ w) s) (l : S' →+* S'') {ψ' : S →+* S''} (e : l.comp ψ = ψ') :
    Val x₀ q κ (ψ'.comp φ) (spMap ψ' ≫ w) (l s) := by
  subst e
  have := h.map l
  rwa [spc_assoc] at this

theorem glue [IsDomain A] [IsIntegrallyClosed A] {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ}
    (hF : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → ∃ P : FP t x₀ q, P.Full 𝔮) (hκ : Mult t x₀ q κ) {S : Type} [CommRing S]
    (φ : A →+* S) (w : Sp S ⟶ t.G.left)
    (h : ∀ (P : FP t x₀ q) (S' : Type) [CommRing S'] (ψ : S →+* S'), IsUnit (ψ (φ P.f)) →
      ∃ β, P.At (ψ.comp φ) (spMap ψ ≫ w) β) :
    ∃ s : S, ∀ (P : FP t x₀ q) (S' : Type) [CommRing S'] (ψ : S →+* S'), IsUnit (ψ (φ P.f)) →
      Val x₀ q κ (ψ.comp φ) (spMap ψ ≫ w) (ψ s) := by
  let T : Set S := Set.range fun P : FP t x₀ q => φ P.f
  have hT : Ideal.span T = ⊤ := by
    by_contra hn
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hn
    obtain ⟨P, hP⟩ := hF (𝔪.comap φ) inferInstance
    exact hP.1 (hle (Ideal.subset_span ⟨P, rfl⟩))
  have hv : ∀ a : T, ∃ s, Val x₀ q κ ((algebraMap S (Localization.Away a.1)).comp φ) (spMap (algebraMap S _) ≫ w) s := by
    rintro ⟨_, P, rfl⟩
    obtain ⟨β, hβ⟩ := h P _ (algebraMap S (Localization.Away (φ P.f))) (IsLocalization.Away.algebraMap_isUnit _)
    obtain ⟨b, hb⟩ := P.ex_gl hκ
    exact ⟨_, P, b, β, hb, hβ, rfl⟩
  choose s hs using hv
  have hc : ∀ a b : T, IsLocalization.Away.awayToAwayRight (P := Localization.Away (a.1 * b.1)) a.1 b.1 (s a) =
      IsLocalization.Away.awayToAwayLeft b.1 a.1 (s b) := fun a b => by
    have e1 : (IsLocalization.Away.awayToAwayRight (S := Localization.Away a.1) (P := Localization.Away (a.1 * b.1))
        a.1 b.1).comp (algebraMap S _) = algebraMap S _ :=
      IsLocalization.Away.lift_comp a.1 _
    have e2 : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away b.1) (P := Localization.Away (a.1 * b.1))
        b.1 a.1).comp (algebraMap S _) = algebraMap S _ :=
      IsLocalization.Away.lift_comp b.1 _
    have h1 := (hs a).map' _ e1
    have h2 := (hs b).map' _ e2
    exact Val.uniq hF hκ h1 h2
  obtain ⟨r, hr, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top T hT s hc
  refine ⟨r, fun P S' _ ψ hu => ?_⟩
  let a : T := ⟨_, P, rfl⟩
  have h1 := (hs a).map' (IsLocalization.Away.lift a.1 (g := ψ) hu) (IsLocalization.Away.lift_comp _ _)
  rwa [← hr a, IsLocalization.Away.lift_eq] at h1

section Char

variable {O : Type} [CommRing O] [IsLocalRing O] {x : A →+* O} {P : FP t x₀ q}

theorem FP.Full.at_fin (hP : P.Full ((IsLocalRing.maximalIdeal O).comap x)) (B : Type) [CommRing B] [Algebra O B]
    [Module.Finite O B] (w : Over.mk (spMap (algebraMap O B) ≫ spMap x ≫ x₀) ⟶ t.G) (hw : w ^ q = 1) :
    ∃ β, P.At ((algebraMap O B).comp x) w.left β :=
  hP.at (fun 𝔪 _ => by
    rw [← Ideal.comap_comap, IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) 𝔪)])
    (spc_assoc _ _ _) w hw

theorem ex_char {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ} (hP : P.Full ((IsLocalRing.maximalIdeal O).comap x))
    {b : P.Bˣ} (hb : P.Gl κ b) : ∃ c : TorsChar t (spMap x ≫ x₀) q,
      ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
        (w : Over.mk (spMap (algebraMap O B) ≫ spMap x ≫ x₀) ⟶ t.G) (β : P.B →+* B),
        P.At ((algebraMap O B).comp x) w.left β → (c.χ B w : B) = β b := by
  classical
  let χ : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B],
      (Over.mk (spMap (algebraMap O B) ≫ spMap x ≫ x₀) ⟶ t.G) → Bˣ := fun B _ _ _ w =>
    if h : w ^ q = 1 then Units.map (hP.at_fin B w h).choose.toMonoidHom b else 1
  have hχ : ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
      (w : Over.mk (spMap (algebraMap O B) ≫ spMap x ≫ x₀) ⟶ t.G) (β : P.B →+* B),
      P.At ((algebraMap O B).comp x) w.left β → (χ B w : B) = β b := fun B _ _ _ w β h => by
    simp only [χ, dif_pos h.tors]
    exact congrArg (fun z : P.B →+* B => z b) ((hP.at_fin B w h.tors).choose_spec.mono h)
  refine ⟨⟨χ, fun B _ _ _ w w' hw hw' => Units.ext ?_, fun B B' _ _ _ _ _ _ φ w w' hw e => ?_⟩, hχ⟩
  · obtain ⟨β, h⟩ := hP.at_fin B w hw
    obtain ⟨β', h'⟩ := hP.at_fin B w' hw'
    obtain ⟨β'', h''⟩ := h.mul h'
    rw [Units.val_mul, hχ B _ _ h, hχ B _ _ h', hχ B _ _ h'']
    exact hb.2 _ _ _ _ _ _ _ _ h h' h''
  · obtain ⟨β, h⟩ := hP.at_fin B w hw
    have h' := h.map φ.toRingHom
    rw [← e, ← RingHom.comp_assoc, show φ.toRingHom.comp (algebraMap O B) = algebraMap O B' from φ.comp_algebraMap] at h'
    rw [hχ B _ _ h, hχ B' _ _ h']
    rfl

end Char

variable (t x₀ q) in

abbrev Gam : Subgroup (Over.mk (spMap (algebraMap A (FractionRing A)) ≫ x₀) ⟶ t.G) := (powMonoidHom q).ker

def kap (χ : Gam t x₀ q →* Aˣ) : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ :=
  Function.extend (fun a : Gam t x₀ q => (a.1.left : Sp (FractionRing A) ⟶ t.G.left)) χ 1

theorem kap_left (χ : Gam t x₀ q →* Aˣ) (a : Gam t x₀ q) : kap χ a.1.left = χ a :=
  Function.Injective.extend_apply (fun _ _ h => Subtype.ext (Over.OverMorphism.ext h)) _ _ _

theorem mult_kap (χ : Gam t x₀ q →* Aˣ) : Mult t x₀ q (kap χ) := fun w w' hw hw' => by
  let a : Gam t x₀ q := ⟨w, hw⟩
  let a' : Gam t x₀ q := ⟨w', hw'⟩
  have h1 : kap χ w.left = χ a := kap_left χ a
  have h2 : kap χ w'.left = χ a' := kap_left χ a'
  have h3 : kap χ (w * w').left = χ (a * a') := kap_left χ (a * a')
  rw [h1, h2, h3, map_mul]

theorem finite_gam [IsDomain A] (hF : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → ∃ P : FP t x₀ q, P.Full 𝔮) :
    Finite (Gam t x₀ q) := by
  obtain ⟨P, hP⟩ := hF ⊥ Ideal.isPrime_bot
  haveI := P.dom
  haveI := P.fin.finite
  haveI := P.fin.free
  have h : ∀ a : Gam t x₀ q, ∃ σ : P.B →ₐ[Localization.Away P.f] Localization.Away P.f,
      spMap (P.toK.comp σ.toRingHom) ≫ P.u.left = a.1.left := fun a => by
    obtain ⟨β, hβ⟩ := hP.2 _ (algebraMap A (FractionRing A))
      ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective _ _)) _ rfl a.1 a.2
    obtain ⟨σ, rfl⟩ := hβ.sectK
    exact ⟨σ, hβ.2⟩
  choose σ hσ using h
  exact Finite.of_injective σ fun a a' e => Subtype.ext (Over.OverMorphism.ext (by rw [← hσ, ← hσ, e]))

theorem lift_char [IsDomain A] {O : Type} [CommRing O] [IsDomain O] [CharZero O] (x : A →+* O) (hq : q.Prime) {ζ : A}
    (hζ : IsPrimitiveRoot ζ q) {D : Type} [Group D] (c : D →* Oˣ) (hc : ∀ d, c d ^ q = 1) :
    ∃ χ : D →* Aˣ, ∀ d, x (χ d) = c d := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI := Fact.mk hq
  have hx : IsPrimitiveRoot (x ζ) q := by
    have h1 : x ζ ≠ 1 := fun h => by
      have := congrArg x (hζ.geom_sum_eq_zero hq.one_lt)
      simp [map_sum, h, hq.ne_zero] at this
    have h2 : x ζ ^ q = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    rw [← orderOf_eq_prime h2 h1]
    exact IsPrimitiveRoot.orderOf _
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

theorem ext_char [IsDomain A] (hq : q ≠ 0) {ζ : A} (hζ : IsPrimitiveRoot ζ q) {D Γ : Type} [Group D] [CommGroup Γ]
    [Finite Γ] (hΓ : ∀ a : Γ, a ^ q = 1) (i : D →* Γ) (hi : Function.Injective i) (χ : D →* Aˣ) :
    ∃ χ' : Γ →* Aˣ, ∀ d, χ' (i d) = χ d := by
  haveI : NeZero q := ⟨hq⟩
  haveI : HasEnoughRootsOfUnity A q := ⟨⟨ζ, hζ⟩, inferInstance⟩
  haveI : HasEnoughRootsOfUnity A (Monoid.exponent Γ) :=
    HasEnoughRootsOfUnity.of_dvd A (Monoid.exponent_dvd_of_forall_pow_eq_one hΓ)
  obtain ⟨χ', h⟩ := MonoidHom.domRestrict_surjective A i.range
    (χ.comp (MonoidHom.ofInjective hi).symm.toMonoidHom)
  refine ⟨χ', fun d => ?_⟩
  have := DFunLike.congr_fun h (MonoidHom.ofInjective hi d)
  exact this.trans (congrArg χ ((MonoidHom.ofInjective hi).symm_apply_apply d))

def FP.secs (P : FP t x₀ q) (hq : q ≠ 0) :
    Subgroup (Over.mk (spMap (algebraMap A (Localization.Away P.f)) ≫ x₀) ⟶ t.G) where
  carrier := {w | ∃ β, P.At (algebraMap A _) w.left β}
  mul_mem' := fun ⟨_, h⟩ ⟨_, h'⟩ => h.mul h'
  one_mem' := FP.at_one (IsLocalization.Away.algebraMap_isUnit _) rfl
  inv_mem' := fun {w} ⟨β, h⟩ => by
    have key : ∀ n : ℕ, ∃ β, P.At (algebraMap A _) (w ^ n).left β := fun n => by
      induction n with
      | zero => rw [pow_zero]; exact FP.at_one (IsLocalization.Away.algebraMap_isUnit _) rfl
      | succ n ih => obtain ⟨_, ih⟩ := ih; rw [pow_succ]; exact ih.mul h
    have e : w⁻¹ = w ^ (q - 1) := inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hq, h.tors])
    rw [e]
    exact key _

theorem ex_chi [IsDomain A] [Finite (Gam t x₀ q)] (hq : q.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ q) {O : Type}
    [CommRing O] [IsDomain O] [CharZero O] {x : A →+* O} (P : FP t x₀ q) (hu : IsUnit (x P.f))
    (c : TorsChar t (spMap x ≫ x₀) q) : ∃ χ : Gam t x₀ q →* Aˣ, ∀ b, P.Gl (kap χ) b →
      ∀ (w : Over.mk (spMap (algebraMap O O) ≫ spMap x ≫ x₀) ⟶ t.G) (β : P.B →+* O),
        P.At ((algebraMap O O).comp x) w.left β → (c.χ O w : O) = β b := by
  obtain ⟨x', rfl⟩ := FP.ex_lift hu
  have e₁ : spMap x' ≫ spMap (algebraMap A _) ≫ x₀ = spMap (algebraMap O O) ≫ spMap (x'.comp (algebraMap A _)) ≫ x₀ := by
    rw [spc_assoc, spc_assoc]
  have e₂ : spMap P.toK ≫ spMap (algebraMap A _) ≫ x₀ = spMap (algebraMap A (FractionRing A)) ≫ x₀ := by
    rw [spc_assoc, P.toK_comp]
  have ht : ∀ d : P.secs hq.ne_zero, d.1 ^ q = 1 := fun d => d.2.choose_spec.tors
  have ht' : ∀ d : P.secs hq.ne_zero, pull _ e₁ d.1 ^ q = 1 := fun d => by rw [← map_pow, ht, map_one]
  let c₀ : P.secs hq.ne_zero →* Oˣ := MonoidHom.mk' (fun d => c.χ O (pull _ e₁ d.1)) fun d d' => by
    rw [Subgroup.coe_mul, map_mul, c.mul O _ _ (ht' d) (ht' d')]
  obtain ⟨χ₀, h₀⟩ := lift_char (x'.comp (algebraMap A _)) hq hζ c₀ fun d => by
    rw [← map_pow, show d ^ q = 1 from Subtype.ext (ht d), map_one]
  let i : P.secs hq.ne_zero →* Gam t x₀ q := ((pull _ e₂).comp (P.secs hq.ne_zero).subtype).codRestrict _ fun d => by
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
  obtain ⟨χ, hχ⟩ := ext_char hq.ne_zero hζ (fun a => Subtype.ext a.2) i hi χ₀
  refine ⟨χ, fun b hb w β h => ?_⟩
  obtain ⟨σ, hσ⟩ := FP.At.sect (φ := (algebraMap O (FractionRing O)).comp x') (h.map (algebraMap O (FractionRing O)))
  obtain rfl : β = x'.comp σ.toRingHom := RingHom.ext fun z =>
    IsFractionRing.injective O (FractionRing O) (RingHom.congr_fun hσ z)
  let d : P.secs hq.ne_zero := ⟨mkPt _ (P.at_sect σ).over, _, P.at_sect σ⟩
  have h1 : w = pull _ e₁ d.1 := Over.OverMorphism.ext (h.2.symm.trans (spc_assoc _ _ _).symm)
  have h2 : spMap (P.toK.comp σ.toRingHom) ≫ P.u.left = (i d).1.left := (spc_assoc _ _ _).symm
  have h3 := hb.1 _ _ (P.at_sectK σ)
  rw [h2, kap_left, hχ, ← P.toK_comp] at h3
  rw [h1]
  exact (h₀ d).symm.trans (congrArg x' (P.toK_inj h3)).symm

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => by ext <;> simp [dualMap]

theorem cast_quot (R : Type) [CommRing R] (p n : ℕ) : ((p ^ n : ℕ) : R ⧸ Ideal.span {(p : R) ^ n}) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.mem_span_singleton_self _

theorem ex_dlog [IsDomain A] [IsIntegrallyClosed A] {p n : ℕ}
    (hF : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → ∃ P : FP t x₀ (p ^ n), P.Full 𝔮)
    {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ} (hκ : Mult t x₀ (p ^ n) κ) {g : ℕ}
    {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x₀ (e i)) :
    ∃ h : Fin g → A, ∀ (O : Type) [CommRing O] [IsLocalRing O] (x : A →+* O) (P : FP t x₀ (p ^ n)) (b : P.Bˣ),
      P.Full ((IsLocalRing.maximalIdeal O).comap x) → P.Gl κ b → ∀ c : TorsChar t (spMap x ≫ x₀) (p ^ n),
      (∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
        (w : Over.mk (spMap (algebraMap O B) ≫ spMap x ≫ x₀) ⟶ t.G) (β : P.B →+* B),
        P.At ((algebraMap O B).comp x) w.left β → (c.χ B w : B) = β b) →
      DlogIs t p n c (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h i)) := by
  let I : Ideal A := Ideal.span {(p : A) ^ n}
  have h1 := fun i => glue hF hκ ((algebraMap (A ⧸ I) (DualNumber (A ⧸ I))).comp (Ideal.Quotient.mk I))
    (spMap (dualMap (Ideal.Quotient.mk I)) ≫ e i) fun P S' _ ψ hu =>
      tan_at P (GlobalTheory.FactorDepth.isTanAtG_map t _ (he i)) (cast_quot A p n) ψ hu
  choose s hs using h1
  choose h hh using fun i => Ideal.Quotient.mk_surjective (s i).snd
  refine ⟨h, fun O _ _ x P b hP hb c hc => ?_⟩
  let J : Ideal O := Ideal.span {(p : O) ^ n}
  have hIJ : I ≤ J.comap x := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
    exact Ideal.mem_span_singleton_self _
  let x' : A ⧸ I →+* O ⧸ J := Ideal.quotientMap J x hIJ
  have hx' : x'.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp x := Ideal.quotientMap_comp_mk hIJ
  have hex := fun i => GlobalTheory.FactorDepth.isTanAtG_map t x (he i)
  obtain ⟨h', hd⟩ := (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t O _ p n c g _ hex).1
  have key : ∀ i, Ideal.Quotient.mk J (h' i) = Ideal.Quotient.mk J (x (h i)) := fun i => by
    have hv := GlobalTheory.FactorDepth.isTanAtG_map t (Ideal.Quotient.mk J) (hex i)
    let w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ J))) ≫ spMap x ≫ x₀) ⟶ t.G :=
      mkPt _ (hv.1.trans (spc_assoc _ _ _))
    have h2 := hd _ _ (comb_single hex i) w rfl
    obtain ⟨β, hβ⟩ := hP.at_fin _ w (tan_tors hv (cast_quot O p n) w rfl)
    have e₁ : (dualMap x').comp ((algebraMap (A ⧸ I) (DualNumber (A ⧸ I))).comp (Ideal.Quotient.mk I)) =
        (algebraMap O (DualNumber (O ⧸ J))).comp x := by
      rw [← RingHom.comp_assoc, dualMap_comp_alg, RingHom.comp_assoc, hx']; rfl
    have e₂ : spMap (dualMap x') ≫ spMap (dualMap (Ideal.Quotient.mk I)) ≫ e i = w.left := by
      rw [mkPt_left, spc_assoc, spc_assoc, dual_comp, dual_comp, hx']
    have h3 := hs i P _ (dualMap x') (by rw [← RingHom.comp_apply, e₁]; exact hβ.unit)
    rw [e₁, e₂] at h3
    have h4 := h3.uniq hF hκ ⟨P, b, β, hb, hβ, rfl⟩
    rw [hc _ w β hβ, ← h4] at h2
    have h5 : Ideal.Quotient.mk J (x (h i)) = x' (s i).snd := by rw [← hh]; exact (RingHom.congr_fun hx' _).symm
    rw [h5]
    simpa [dualMap, Pi.single_apply] using h2.symm
  intro a v hv w hw
  rw [hd a v hv w hw, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul, key]

theorem hodgeTate_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), IsTanBasis t x₀ e → ∀ p : ℕ, p.Prime → (∃ ζ : A, IsPrimitiveRoot ζ p) → SplitTors t x₀ p → ∃ (n : ℕ) (h : Fin n → Fin g → A), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : A →+* ↥(intO C)), (∀ c : TorsChar t (spMap x ≫ x₀) (p ^ 1), ∃ j, DlogIs t p 1 c (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) ∧ ∀ j, ∃ c : TorsChar t (spMap x ≫ x₀) (p ^ 1), DlogIs t p 1 c (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i)) := by
  intro E _ _ _ H X _ t A _ _ _ _ x₀ g e he p hp ⟨ζ, hζ⟩ hs
  have hq : (p ^ 1).Prime := by rwa [pow_one]
  have hζ' : IsPrimitiveRoot ζ (p ^ 1) := by rwa [pow_one]
  have hF := ex_full hq.ne_zero (show SplitTors t x₀ (p ^ 1) by rwa [pow_one])
  haveI := finite_gam hF
  haveI : Finite (Gam t x₀ (p ^ 1) →* Aˣ) := inferInstance
  obtain ⟨n, ⟨ε⟩⟩ := Finite.exists_equiv_fin (Gam t x₀ (p ^ 1) →* Aˣ)
  choose h hh using fun χ : Gam t x₀ (p ^ 1) →* Aˣ => ex_dlog hF (mult_kap χ) he.1
  refine ⟨n, fun j => h (ε.symm j), fun C _ _ _ _ x => ?_⟩
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing C
  obtain ⟨P, hP⟩ := hF ((IsLocalRing.maximalIdeal _).comap x) inferInstance
  refine ⟨fun c => ?_, fun j => ?_⟩
  · obtain ⟨χ, hχ⟩ := ex_chi hq hζ' P (by by_contra hn; exact hP.1 hn) c
    obtain ⟨b, hb⟩ := P.ex_gl (mult_kap χ)
    obtain ⟨c', hc'⟩ := ex_char hP hb
    refine ⟨ε χ, dlog_congr (c' := c') (fun i => GlobalTheory.FactorDepth.isTanAtG_map t x (he.1 i))
      (GlobalTheory.T.torsionChar_eq_of_eq_on_torsion E H X t C _ _ hq.ne_zero c c' fun w hw => ?_) ?_⟩
    · obtain ⟨β, hβ⟩ := hP.at_fin _ w hw
      exact Units.ext ((hχ b hb w β hβ).trans (hc' _ w β hβ).symm)
    · simp only [Equiv.symm_apply_apply]
      exact hh χ _ x P b hP hb c' hc'
  · obtain ⟨b, hb⟩ := P.ex_gl (mult_kap (ε.symm j))
    obtain ⟨c', hc'⟩ := ex_char hP hb
    exact ⟨c', hh _ _ x P b hP hb c' hc'⟩

end GlobalTheory.HTMap
