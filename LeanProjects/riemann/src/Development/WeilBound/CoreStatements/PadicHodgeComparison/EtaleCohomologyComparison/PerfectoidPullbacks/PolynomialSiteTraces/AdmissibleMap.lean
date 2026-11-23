import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsStdOfInjective

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA

namespace CrystallineSemistableComparison.Pb.Site

variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def ofMap (T : Thick (nlFun γ p X q κ)) {B : Type} [CommRing B] (f : T.B →+* B) (J : Ideal B) (δ : DividedPowers J)
    (hJ : T.J ≤ J.comap f) (hdp : IsDPMorphism T.δ δ f)
    (adm : (p ≠ 0 → IsNilpotent (p : B)) ∧ (p = 0 → IsNilpotent J)) : Thick (nlFun γ p X q κ) :=
  mkT B (f.comp T.i) J δ adm (IsDPMorphism.comp _ hdp T.compat)
    ((nlFun γ p X q κ).Pt.map (CommRingCat.ofHom (Ideal.quotientMap J f hJ)) T.y) (fun r => by
      change Ideal.quotientMap J f hJ (T.y.1.1 (Ideal.Quotient.mk _ r)) = _
      rw [show T.y.1.1 (Ideal.Quotient.mk _ r) = _ from T.w r]
      rfl)

section OfMap

variable (T : Thick (nlFun γ p X q κ)) {B : Type} [CommRing B] (f : T.B →+* B) (J : Ideal B) (δ : DividedPowers J)
    (hJ : T.J ≤ J.comap f) (hdp : IsDPMorphism T.δ δ f)
    (adm : (p ≠ 0 → IsNilpotent (p : B)) ∧ (p = 0 → IsNilpotent J))

def homOf : T ⟶ ofMap T f J δ hJ hdp adm := mkH f (fun _ => rfl) hdp hJ rfl

theorem homOf_φ : (homOf T f J δ hJ hdp adm).φ = f := rfl

variable {T f J δ hJ hdp adm}

def descOf {T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (g : B →+* T'.B) (hg : g.comp f = φ.φ)
    (hdp' : IsDPMorphism δ T'.δ g) (hle : J ≤ T'.J.comap g) : ofMap T f J δ hJ hdp adm ⟶ T' :=
  mkH g (fun r => by
      change g (f (T.i r)) = _
      rw [show g (f (T.i r)) = (g.comp f) (T.i r) from rfl, hg, φ.comm]) hdp' hle (by
      have e : CommRingCat.ofHom (Ideal.quotientMap J f hJ) ≫ CommRingCat.ofHom (Ideal.quotientMap T'.J g hle) =
          CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle) := by
        ext x
        change Ideal.Quotient.mk T'.J (g (f x)) = Ideal.Quotient.mk T'.J (φ.φ x)
        rw [← hg]
        rfl
      rw [← φ.pt, ← e, Functor.map_comp]
      rfl)

theorem descOf_φ {T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (g : B →+* T'.B) (hg : g.comp f = φ.φ)
    (hdp' : IsDPMorphism δ T'.δ g) (hle : J ≤ T'.J.comap g) :
    (descOf (hJ := hJ) (hdp := hdp) (adm := adm) φ g hg hdp' hle).φ = g := rfl

end OfMap

theorem pt_hom {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') :
    pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T := by
  rw [pt, ← φ.pt]
  rfl

theorem inU_hom {V : X.Opens} {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : InU V T) : InU V T' := by
  intro x _
  have hx := h (show (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle))).base x ∈
    (⊤ : (Spec (CommRingCat.of (T.B ⧸ T.J))).Opens) from trivial)
  rw [pt_hom φ]
  exact hx

theorem admissible_map (T : Thick (nlFun γ p X q κ)) {B : Type} [CommRing B] (f : T.B →+* B) :
    (p ≠ 0 → IsNilpotent (p : B)) ∧ (p = 0 → IsNilpotent (T.J.map f)) := by
  refine ⟨fun h => by simpa using (T.adm.1 h).map f, fun h => ?_⟩
  obtain ⟨n, hn⟩ := T.adm.2 h
  exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩

abbrev pq (B : Type) [CommRing B] : PDPoly B := GlobalTheory.PDA.Model.pdPoly B

def eta {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : DividedPowers ((pq B).ext J) :=
  Classical.choose (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))

theorem eta_std {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : (pq B).IsStd δ (eta δ) :=
  Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))

theorem le_ext {B : Type} [CommRing B] (J : Ideal B) : J ≤ ((pq B).ext J).comap (algebraMap B (pq B).P) :=
  fun _ hx => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)

def polyT (T : Thick (nlFun γ p X q κ)) (hp : p ≠ 0) : Thick (nlFun γ p X q κ) :=
  ofMap T (algebraMap T.B (pq T.B).P) ((pq T.B).ext T.J) (eta T.δ) (le_ext T.J) (eta_std T.δ).dp
    ⟨fun h => by simpa using (T.adm.1 h).map (algebraMap T.B (pq T.B).P), fun h => absurd h hp⟩

def polyJ (T : Thick (nlFun γ p X q κ)) (hp : p ≠ 0) : T ⟶ polyT T hp := homOf _ _ _ _ _ _ _

abbrev trI (T : Thick (nlFun γ p X q κ)) (s : ℕ) : Ideal (pq T.B).P := fil (eta T.δ) (max s 1)

theorem trI_sub (T : Thick (nlFun γ p X q κ)) (s : ℕ) : (eta T.δ).IsSubDPIdeal (trI T s) :=
  FubiniStudyChowHeightFormula₂.Adr.Fil.fil_isSubDPIdeal _ _ (le_max_right _ _)

abbrev trB (T : Thick (nlFun γ p X q κ)) (s : ℕ) : Type := (pq T.B).P ⧸ trI T s

abbrev trJ (T : Thick (nlFun γ p X q κ)) (s : ℕ) : Ideal (trB T s) := ((pq T.B).ext T.J).map (Ideal.Quotient.mk _)

def trD (T : Thick (nlFun γ p X q κ)) (s : ℕ) : DividedPowers (trJ T s) :=
  Classical.choose (FubiniStudyChowHeightFormula₂.Adr.Fil.exists_quot (eta T.δ) (trI T s) (trI_sub T s))

theorem trD_spec (T : Thick (nlFun γ p X q κ)) (s : ℕ) :
    IsDPMorphism (eta T.δ) (trD T s) (Ideal.Quotient.mk (trI T s)) ∧
      ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : trB T s →+* C),
        IsDPMorphism (eta T.δ) δ'' (g.comp (Ideal.Quotient.mk (trI T s))) → IsDPMorphism (trD T s) δ'' g :=
  Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.Fil.exists_quot (eta T.δ) (trI T s) (trI_sub T s))

abbrev trF (T : Thick (nlFun γ p X q κ)) (s : ℕ) : T.B →+* trB T s :=
  (Ideal.Quotient.mk (trI T s)).comp (algebraMap T.B (pq T.B).P)

theorem trF_le (T : Thick (nlFun γ p X q κ)) (s : ℕ) : T.J ≤ (trJ T s).comap (trF T s) :=
  fun _ hx => Ideal.mem_map_of_mem _ (le_ext T.J hx)

theorem trF_dp (T : Thick (nlFun γ p X q κ)) (s : ℕ) : IsDPMorphism T.δ (trD T s) (trF T s) :=
  IsDPMorphism.comp _ (trD_spec T s).1 (eta_std T.δ).dp

def polyTr (T : Thick (nlFun γ p X q κ)) (s : ℕ)
    (adm : (p ≠ 0 → IsNilpotent (p : trB T s)) ∧ (p = 0 → IsNilpotent (trJ T s))) : Thick (nlFun γ p X q κ) :=
  ofMap T (trF T s) (trJ T s) (trD T s) (trF_le T s) (trF_dp T s) adm

def locD (T : Thick (nlFun γ p X q κ)) (f : T.B) : DividedPowers (T.J.map (algebraMap T.B (Localization.Away f))) :=
  Classical.choose (FubiniStudyChowHeightFormula₂.Adr.flatExt T.B (Localization.Away f) T.J T.δ)

theorem locD_dp (T : Thick (nlFun γ p X q κ)) (f : T.B) :
    IsDPMorphism T.δ (locD T f) (algebraMap T.B (Localization.Away f)) :=
  Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.flatExt T.B (Localization.Away f) T.J T.δ)

def locT (T : Thick (nlFun γ p X q κ)) (f : T.B) : Thick (nlFun γ p X q κ) :=
  ofMap T (algebraMap T.B (Localization.Away f)) _ (locD T f) Ideal.le_comap_map (locD_dp T f) (admissible_map T _)

def locH (T : Thick (nlFun γ p X q κ)) (f : T.B) : T ⟶ locT T f := homOf _ _ _ _ _ _ _

def quoD (T : Thick (nlFun γ p X q κ)) {K : Ideal T.B} (hK : T.δ.IsSubDPIdeal K) :
    DividedPowers (T.J.map (Ideal.Quotient.mk K)) :=
  Classical.choose (FubiniStudyChowHeightFormula₂.Adr.Fil.exists_quot T.δ K hK)

theorem quoD_spec (T : Thick (nlFun γ p X q κ)) {K : Ideal T.B} (hK : T.δ.IsSubDPIdeal K) :
    IsDPMorphism T.δ (quoD T hK) (Ideal.Quotient.mk K) ∧
      ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : T.B ⧸ K →+* C),
        IsDPMorphism T.δ δ'' (g.comp (Ideal.Quotient.mk K)) → IsDPMorphism (quoD T hK) δ'' g :=
  Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.Fil.exists_quot T.δ K hK)

def quoT (T : Thick (nlFun γ p X q κ)) {K : Ideal T.B} (hK : T.δ.IsSubDPIdeal K) : Thick (nlFun γ p X q κ) :=
  ofMap T (Ideal.Quotient.mk K) _ (quoD T hK) Ideal.le_comap_map (quoD_spec T hK).1 (admissible_map T _)

def quoH (T : Thick (nlFun γ p X q κ)) {K : Ideal T.B} (hK : T.δ.IsSubDPIdeal K) : T ⟶ quoT T hK :=
  homOf _ _ _ _ _ _ _

end CrystallineSemistableComparison.Pb.Site
