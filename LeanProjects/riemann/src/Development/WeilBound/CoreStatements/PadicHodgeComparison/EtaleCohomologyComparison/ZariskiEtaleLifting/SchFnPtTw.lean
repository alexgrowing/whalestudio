import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElementAlt
import BuildAid.D2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.B

open PAlg

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]

variable (F : Fn O) (κ : O →+* OC l)

theorem map_sq (P : CommRingCat.{0} ⥤ Type) {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C) (g' : C ⟶ D)
    (h : g.hom.comp f.hom = g'.hom.comp f'.hom) (y : P.obj A) : P.map g (P.map f y) = P.map g' (P.map f' y) := by
  have e : f ≫ g = f' ≫ g' := CommRingCat.hom_ext h
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, e]

def basePt {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂} (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) :
    F.ptK κ₂ ⟶ F.ptK κ₁ where
  app B := TypeCat.ofHom fun z => ⟨(z.1.1.comp τ, z.1.2), by rw [RingHom.comp_assoc, h]; exact z.2⟩
  naturality _ _ _ := rfl

theorem red_le (k : Bool) {m n : ℕ} (h : n ≤ m) : JJ k (base l) m ≤ (JJ k (base l) n).comap ((base l).red h) :=
  Ideal.map_le_iff_le_comap.1 (dd_red k _ h).1

theorem red_κb (k : Bool) {m n : ℕ} (h : n ≤ m) :
    (Ideal.quotientMap _ ((base l).red h) (red_le k h)).comp (κb κ k m) = κb κ k n := RingHom.ext fun x => by
  change Ideal.quotientMap _ _ (red_le k h) (uJ k (base l) m ((base l).oC (κ x))) = uJ k (base l) n ((base l).oC (κ x))
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective ((base l).oC (κ x))
  rw [← hw]; rfl

theorem red_cris (A : PAlg l) {m n : ℕ} (h : n ≤ m) (a : Acris l) : A.red h (A.cris m a) = A.cris n a :=
  RingHom.congr_fun (ACris.ringHom_ext (F := (A.red h).comp (A.cris m)) (G := A.cris n) fun y => by
    rw [RingHom.comp_apply, cris_of, cris_of, red_mk]) a

def redMor (k : Bool) {m n : ℕ} (h : n ≤ m) : CH.Mor (Oc F κ k m) (Oc F κ k n) (RingHom.id _) :=
  omMor (crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl (dd_red k _ h)
    (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl) (RingHom.id _) (red_cris _ h)

def redHc (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) : Hc F κ k m j →ₗ[Acris l] Hc F κ k n j := (redMor F κ k h).pull j

def HcSys (k : Bool) (j : ℕ) : Sys.{1} (Acris l) where
  M n := Hc F κ k n j
  r n := redHc F κ k n.le_succ j

section Gal
variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K))

theorem gal_le (k : Bool) (n : ℕ) : JJ k (base l) n ≤ (JJ k (base l) n).comap (galBase σ n) :=
  Ideal.map_le_iff_le_comap.1 (dd_gal k σ n).1

theorem gal_κb (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ) :
    (Ideal.quotientMap _ (galBase σ n) (gal_le σ k n)).comp (κb κ k n) = κb κ k n := RingHom.ext fun x => by
  change Ideal.quotientMap _ _ (gal_le σ k n) (uJ k (base l) n ((base l).oC (κ x))) = uJ k (base l) n ((base l).oC (κ x))
  obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (κ x)
  have hw' : theta0 l w = κ x := hw
  conv_rhs => rw [← hσ, ← hw', ← theta0_gal]
  rw [← hw', oC_theta0, oC_theta0, uJ_th, uJ_th, ← cris_algebraMap, ← cris_algebraMap, Ideal.quotientMap_mk, galBase_cris]
  exact congrArg (fun a => Ideal.Quotient.mk _ ((base l).cris n a)) (ACris.gal_smul_algebraMap σ w)

def galMorC (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ) : CH.Mor (Oc F κ k n) (Oc F κ k n) (ACris.galCris σ) :=
  omMor (crMor (F := F) (F' := F) (b := bs l k n) (b' := bs l k n) (ht := rfl) (ht' := rfl) (galBase σ n) rfl (dd_gal k σ n)
    (basePt F _ (gal_κb κ σ hσ k n)) fun _ _ _ => rfl) (ACris.galCris σ) (galBase_cris σ n)

def galHc (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) : Hc F κ k n j →ₛₗ[ACris.galCris σ] Hc F κ k n j :=
  (galMorC F κ σ hσ k n).pull j

def ptTw (hσ : ∀ x, galOC σ (κ x) = κ x) : F.pt κ ⟶ twF σ ⋙ F.pt κ where
  app A := TypeCat.ofHom fun y => ⟨F.Pt.map (CommRingCat.ofHom (twUEquiv σ A).symm.toRingHom) y.1, by
    have e : (twUEquiv σ A).symm.toRingHom.comp (A.oC.comp κ) = (tw σ A).oC.comp κ := RingHom.ext fun x =>
      (twUEquiv σ A).symm_apply_eq.2 ((twU_oC σ A _).trans (congrArg A.oC (hσ x))).symm
    have h := F.ov_map (CommRingCat.ofHom (twUEquiv σ A).symm.toRingHom) y.2
    rw [CommRingCat.hom_ofHom, e] at h
    exact h⟩
  naturality A A' f := by
    ext y
    refine Subtype.ext ?_
    change F.Pt.map (CommRingCat.ofHom (twUEquiv σ A').symm.toRingHom) (F.Pt.map (CommRingCat.ofHom (mapU f)) y.1) =
      F.Pt.map (CommRingCat.ofHom (mapU (twMap σ f))) (F.Pt.map (CommRingCat.ofHom (twUEquiv σ A).symm.toRingHom) y.1)
    have e : (twUEquiv σ A').symm.toRingHom.comp (mapU f) = (mapU (twMap σ f)).comp (twUEquiv σ A).symm.toRingHom :=
      RingHom.ext fun x => (twUEquiv σ A').symm_apply_eq.2
        ((twU_mapU σ f _).trans (congrArg (mapU f) ((twUEquiv σ A).apply_symm_apply x))).symm
    exact map_sq F.Pt _ _ _ _ e _

theorem schFn_ptTw {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (hσ : ∀ x, galOC σ (κ x) = κ x) :
    ptTw (schFn q) κ σ hσ = pxTw q κ σ hσ := rfl

end Gal

noncomputable def frb {B : Type} [CommRing B] (h : (l : B) = 0) : B →+* B :=
  _root_.UpperTheory.Reformulated.B.FrobeniusElementAlt.frb h

theorem l_zero {B : Type} [CommRing B] {n : ℕ} (ψ : (base l).Acr n ⧸ JJ true (base l) n →+* B) : (l : B) = 0 := by
  have h : (l : (base l).Acr n) ∈ JJ true (base l) n := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  rw [← map_natCast ψ, ← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]

def phiPt (n : ℕ) : F.ptK (κb κ true n) ⟶ F.ptK (κb κ true n) where
  app B := TypeCat.ofHom fun z => (F.ptK _).map (CommRingCat.ofHom (frb (l_zero z.1.1))) z
  naturality B B' φ := by
    ext z
    exact map_sq (F.ptK _) φ (CommRingCat.ofHom (frb (l_zero (φ.hom.comp z.1.1)))) (CommRingCat.ofHom (frb (l_zero z.1.1))) φ
      (RingHom.ext fun x => (map_pow φ.hom x l).symm) z

theorem phi_mk (A : PAlg l) (n : ℕ) (r : A.Acr n) :
    Ideal.Quotient.mk (A.PFil n) (A.phi n r) = Ideal.Quotient.mk (A.PFil n) r ^ l := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : Subsingleton (A.Acr 0) := subsingleton_of_zero_eq_one (by simpa using (A.pow_l_acr 0).symm)
    rw [← map_pow]; exact congrArg _ (Subsingleton.elim _ _)
  obtain ⟨u, hu⟩ := (RL.uToQ A n).2.2.1 (Ideal.Quotient.mk _ r)
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hu' : Ideal.Quotient.mk (A.PFil n) (A.toAcr n w) = Ideal.Quotient.mk _ r := hu
  have h1 : Ideal.Quotient.mk (A.PFil n) (A.phi n r) = Ideal.Quotient.mk _ (A.phi n (A.toAcr n w)) := by
    refine Ideal.Quotient.eq.2 ?_
    rw [← map_sub]
    exact (A.dpP_phi n).1 (Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.1 hu'.symm))
  have h2 : A.phiW w - w ^ l ∈ Ideal.span {(l : A.W)} := by
    rw [A.mem_span_l_iff, ← WittVector.constantCoeff_apply, map_sub, map_pow]
    exact sub_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h2
  rw [h1, ← hu', phi_toAcr, ← map_pow, ← map_pow]
  refine Ideal.Quotient.eq.2 ?_
  rw [← map_sub, ← hc, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

def phiMorC (n : ℕ) : CH.Mor (Oc F κ true n) (Oc F κ true n) (ACris.phi ℂ_[l] l) :=
  omMor (crMor (F := F) (F' := F) (b := bs l true n) (b' := bs l true n) (ht := rfl) (ht' := rfl) ((base l).phi n) rfl
    ((base l).dpP_phi n) (phiPt F κ n) fun _ y r =>
      ((congrArg y.1.1 (phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm) (ACris.phi ℂ_[l] l) ((base l).phi_cris n)

def phiHc (n j : ℕ) : Hc F κ true n j →ₛₗ[ACris.phi ℂ_[l] l] Hc F κ true n j := (phiMorC F κ n).pull j

def cmpMor (n : ℕ) : CH.Mor (Oc F κ false n) (Oc F κ true n) (RingHom.id _) :=
  omMor (crMor (F := F) (F' := F) (b := bs l false n) (b' := bs l true n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    ((base l).dp_fil_pfil n) (basePt F (Ideal.Quotient.factor le_sup_right) rfl) fun _ _ _ => rfl) (RingHom.id _) fun _ => rfl

variable {F} {F' : Fn O}

def pullMorC (u : Fn.Map F F') (k : Bool) (n : ℕ) : CH.Mor (Oc F' κ k n) (Oc F κ k n) (RingHom.id _) :=
  omMor (crMor (F := F') (F' := F) (b := bs l k n) (b' := bs l k n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    (DPMorphism.id _).isDPMorphism (u.ptK _) fun _ _ _ => rfl) (RingHom.id _) fun _ => rfl

def pullHc (u : Fn.Map F F') (k : Bool) (n j : ℕ) : Hc F' κ k n j →ₗ[Acris l] Hc F κ k n j := (pullMorC κ u k n).pull j

variable (l) in

structure Compat : Prop where
  red : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j),
    β F κ k n j (redHc F κ k h j x) = (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).pull j (β F κ k m j x)
  gal : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j),
    β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x)
  phi : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ true n j),
    β F κ true n j (phiHc F κ n j x) = (phiMor (F.pt κ) n).pull j (β F κ true n j x)
  pull : ∀ {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j),
    β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x)
  cmp : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j),
    β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x
  cup : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ} (h : i + j = m)
    (x : Hc F κ k n i) (y : Hc F κ k n j), β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) =
      (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y)
  one : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ),
    β F κ k n 0 (CH.oneH (OcA F κ k n)) = CH.oneH (AcrEl (F.pt κ) n)
  red_fil : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (r j : ℕ),
    ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j
  smul_fil : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n r j : ℕ) (a : Acris l),
    (base l).cris n a ∈ JJ k (base l) n → ∀ x ∈ HcFil F κ k n r j, a • x ∈ HcFil F κ k n (r + 1) j

end CrystallineSemistableComparison.B
