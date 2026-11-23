import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ConeClZeroBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u

variable {k k' k'' : Type} [CommRing k] [CommRing k'] [CommRing k''] {X X' X'' : Scheme.{0}}

def resAlg (σ : k →+* k') (B : CommAlgCat.{0} k') : CommAlgCat.{0} k :=
  letI : Algebra k B := Algebra.compHom B σ
  CommAlgCat.of k B

theorem algebraMap_resAlg (σ : k →+* k') (B : CommAlgCat.{0} k') :
    algebraMap k (resAlg σ B) = (algebraMap k' B).comp σ := rfl

def resHom (σ : k →+* k') {B B' : CommAlgCat.{0} k'} (f : B ⟶ B') : resAlg σ B ⟶ resAlg σ B' :=
  letI : Algebra k B := Algebra.compHom B σ
  letI : Algebra k B' := Algebra.compHom B' σ
  CommAlgCat.ofHom { (f.hom : B →+* B') with commutes' := fun r ↦ f.hom.commutes (σ r) }

theorem resHom_apply (σ : k →+* k') {B B' : CommAlgCat.{0} k'} (f : B ⟶ B') (b : B) :
    (resHom σ f).hom b = f.hom b := rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := Spec.map_comp _ _

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem eq_of_spMap_eq {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := congrArg CommRingCat.Hom.hom (Spec.map_injective h)

structure AffPt (s : X ⟶ Sp k) : Type 1 where

  B : CommAlgCat.{0} k

  x : Sp B ⟶ X

  w : x ≫ s = spMap (algebraMap k B)

namespace AffPt

variable {s : X ⟶ Sp k}

instance : Category.{0} (AffPt s) where
  Hom T T' := {φ : T.B ⟶ T'.B // spMap (φ.hom : T.B →+* T'.B) ≫ T.x = T'.x}
  id T := ⟨𝟙 _, by
    rw [show spMap ((𝟙 T.B : T.B ⟶ T.B).hom : T.B →+* T.B) = 𝟙 _ from spMap_id' _, Category.id_comp]⟩
  comp {T T' T''} φ ψ := ⟨φ.1 ≫ ψ.1, by
    have e : ((φ.1 ≫ ψ.1).hom : T.B →+* T''.B) =
        (ψ.1.hom : T'.B →+* T''.B).comp (φ.1.hom : T.B →+* T'.B) := rfl
    rw [e, spMap_comp', Category.assoc, φ.2, ψ.2]⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

@[ext] theorem hom_ext {T T' : AffPt s} {φ ψ : T ⟶ T'} (h : φ.1 = ψ.1) : φ = ψ := Subtype.ext h

end AffPt

def OPt (s : X ⟶ Sp k) : AffPt s ⥤ CommAlgCat.{0} k where
  obj T := T.B
  map φ := φ.1
  map_id _ := rfl
  map_comp _ _ := rfl

section Coef

variable {s : X ⟶ Sp k} {σ : k →+* k'} {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} k'}
  (x : ∀ T : C, Sp (F.obj T) ⟶ X) (hx : ∀ T, x T ≫ s = spMap ((algebraMap k' (F.obj T)).comp σ))
  (hc : ∀ ⦃T T' : C⦄ (a : T ⟶ T'), spMap (mp F a : F.obj T →+* F.obj T') ≫ x T = x T')

def ptFun : C ⥤ AffPt s where
  obj T := ⟨resAlg σ (F.obj T), x T, hx T⟩
  map a := ⟨resHom σ (F.map a), hc a⟩
  map_id T := AffPt.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun b ↦ mp_id F T b))
  map_comp a b := AffPt.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun c ↦ mp_comp F a b c))

def ptCoef : CoefMap σ (OPt s) F where
  G := ptFun x hx hc
  α T := RingHom.id (F.obj T)
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem pull_ptCoef_congr {x' : ∀ T : C, Sp (F.obj T) ⟶ X}
    (hx' : ∀ T, x' T ≫ s = spMap ((algebraMap k' (F.obj T)).comp σ))
    (hc' : ∀ ⦃T T' : C⦄ (a : T ⟶ T'), spMap (mp F a : F.obj T →+* F.obj T') ≫ x' T = x' T')
    (e : ∀ T, x T = x' T) (n : ℕ) :
    Hyp.pull (ptCoef x hx hc) n = Hyp.pull (ptCoef x' hx' hc') n := by
  obtain rfl : x = x' := funext e
  rfl

end Coef

abbrev HdR (s : X ⟶ Sp k) (n : ℕ) : Type 1 := Hyp (OPt s) n

abbrev HdRF (s : X ⟶ Sp k) (p n : ℕ) : Type 1 := HypF (OPt s) p n

abbrev HPt (s : X ⟶ Sp k) (q a : ℕ) : Type 1 := CatH.H (OmF (OPt s) q) a

abbrev HdR.fil (s : X ⟶ Sp k) (p n : ℕ) : Submodule k (HdR s n) := Hyp.fil (OPt s) p n

abbrev HdRF.toHdR (s : X ⟶ Sp k) (p n : ℕ) : HdRF s p n →ₗ[k] HdR s n := HypF.toHyp (OPt s) p n

abbrev HdRF.lead (s : X ⟶ Sp k) {a p n : ℕ} (h : a + p = n) : HdRF s p n →ₗ[k] HPt s p a :=
  HypF.lead (OPt s) h

section Pull

variable {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {s'' : X'' ⟶ Sp k''} {σ : k →+* k'} {τ : k' →+* k''}

theorem comp_w {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (T : AffPt s') :
    (T.x ≫ φ) ≫ s = spMap ((algebraMap k' T.B).comp σ) := by
  rw [Category.assoc, h, ← Category.assoc, T.w, spMap_comp']

def pullCoef {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (OPt s) (OPt s') :=
  ptCoef (F := OPt s') (fun T ↦ T.x ≫ φ) (comp_w h) fun _ _ a ↦
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) a.2)

def HdR.pullSemi {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (n : ℕ) : HdR s n →ₛₗ[σ] HdR s' n :=
  Hyp.pull (pullCoef h) n

theorem over_id {s' : X' ⟶ Sp k} {f : X' ⟶ X} (hf : f ≫ s = s') : f ≫ s = s' ≫ spMap (RingHom.id k) := by
  rw [hf, spMap_id', Category.comp_id]

def HdR.pull {s' : X' ⟶ Sp k} {f : X' ⟶ X} (hf : f ≫ s = s') (n : ℕ) : HdR s n →ₗ[k] HdR s' n :=
  HdR.pullSemi (over_id hf) n

theorem ptCoef_self : ptCoef (s := s) (F := OPt s) (σ := RingHom.id k) (fun T ↦ T.x) (fun T ↦ T.w)
    (fun _ _ a ↦ a.2) = CoefMap.id (OPt s) := rfl

theorem ptCoef_comp {φ : X' ⟶ X} {ψ : X'' ⟶ X'} (h : φ ≫ s = s' ≫ spMap σ)
    (h' : ψ ≫ s' = s'' ≫ spMap τ) (hx : ∀ T : AffPt s'', ((T.x ≫ ψ) ≫ φ) ≫ s =
      spMap ((algebraMap k'' T.B).comp (τ.comp σ)))
    (hc : ∀ ⦃T T' : AffPt s''⦄ (a : T ⟶ T'),
      spMap (mp (OPt s'') a : (OPt s'').obj T →+* (OPt s'').obj T') ≫ (T.x ≫ ψ) ≫ φ = (T'.x ≫ ψ) ≫ φ) :
    ptCoef (F := OPt s'') (fun T ↦ (T.x ≫ ψ) ≫ φ) hx hc = (pullCoef h).comp (pullCoef h') := rfl

theorem HdR.pull_id (n : ℕ) (c : HdR s n) : HdR.pull (f := 𝟙 X) (Category.id_comp s) n c = c := by
  refine (LinearMap.congr_fun (pull_ptCoef_congr (F := OPt s) (σ := RingHom.id k)
    (fun T ↦ T.x ≫ 𝟙 X) (comp_w (over_id (Category.id_comp s)))
    (fun _ _ a ↦ (Category.assoc _ _ _).symm.trans (congrArg (· ≫ 𝟙 X) a.2))
    (x' := fun T ↦ T.x) (fun T ↦ T.w) (fun _ _ a ↦ a.2) (fun T ↦ Category.comp_id T.x) n) c).trans ?_
  exact (congrArg (fun m ↦ Hyp.pull m n c) ptCoef_self).trans (Hyp.pull_id c)

theorem HdR.pullSemi_comp {φ : X' ⟶ X} {ψ : X'' ⟶ X'} (h : φ ≫ s = s' ≫ spMap σ)
    (h' : ψ ≫ s' = s'' ≫ spMap τ) (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (n : ℕ) (c : HdR s n) :
    HdR.pullSemi h'' n c = HdR.pullSemi h' n (HdR.pullSemi h n c) := by
  have hx : ∀ T : AffPt s'', ((T.x ≫ ψ) ≫ φ) ≫ s = spMap ((algebraMap k'' T.B).comp (τ.comp σ)) :=
    fun T ↦ (Category.assoc _ _ _).trans (comp_w h'' T)
  have hc : ∀ ⦃T T' : AffPt s''⦄ (a : T ⟶ T'),
      spMap (mp (OPt s'') a : (OPt s'').obj T →+* (OPt s'').obj T') ≫ (T.x ≫ ψ) ≫ φ = (T'.x ≫ ψ) ≫ φ :=
    fun _ _ a ↦ by
      simp only [← Category.assoc]
      exact congrArg (fun y ↦ (y ≫ ψ) ≫ φ) a.2
  refine (LinearMap.congr_fun (pull_ptCoef_congr (F := OPt s'') (σ := τ.comp σ)
    (fun T ↦ T.x ≫ ψ ≫ φ) (comp_w h'')
    (fun _ _ a ↦ (Category.assoc _ _ _).symm.trans (congrArg (· ≫ ψ ≫ φ) a.2))
    (x' := fun T ↦ (T.x ≫ ψ) ≫ φ) hx hc (fun T ↦ (Category.assoc _ _ _).symm) n) c).trans ?_
  exact (congrArg (fun m ↦ Hyp.pull m n c) (ptCoef_comp h h' hx hc)).trans
    (Hyp.pull_comp (pullCoef h) (pullCoef h') c)

theorem HdR.pull_comp {s' : X' ⟶ Sp k} {s'' : X'' ⟶ Sp k} {f : X' ⟶ X} {g : X'' ⟶ X'}
    (hf : f ≫ s = s') (hg : g ≫ s' = s'') (n : ℕ) (c : HdR s n) :
    HdR.pull (f := g ≫ f) (by rw [Category.assoc, hf, hg]) n c = HdR.pull hg n (HdR.pull hf n c) :=
  HdR.pullSemi_comp (over_id hf) (over_id hg) _ n c

theorem HdR.pullSemi_mem_fil {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) {p n : ℕ} {c : HdR s n}
    (hc : c ∈ HdR.fil s p n) : HdR.pullSemi h n c ∈ HdR.fil s' p n :=
  Hyp.pull_mem_fil (pullCoef h) hc

theorem HdR.pull_mem_fil {s' : X' ⟶ Sp k} {f : X' ⟶ X} (hf : f ≫ s = s') {p n : ℕ} {c : HdR s n}
    (hc : c ∈ HdR.fil s p n) : HdR.pull hf n c ∈ HdR.fil s' p n :=
  HdR.pullSemi_mem_fil (over_id hf) hc

def HdRF.pullSemi {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (p n : ℕ) : HdRF s p n →ₛₗ[σ] HdRF s' p n :=
  HypF.pull (pullCoef h) p n

theorem HdRF.toHdR_pullSemi {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) {p n : ℕ} (c : HdRF s p n) :
    HdRF.toHdR s' p n (HdRF.pullSemi h p n c) = HdR.pullSemi h n (HdRF.toHdR s p n c) :=
  HypF.toHyp_pull (pullCoef h) c

end Pull

section Aff

variable (s : X ⟶ Sp k)

def affCoef : CoefMap (RingHom.id k) (OPt s) (OAff s) :=
  ptCoef (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)

def HdR.toAff (n : ℕ) : HdR s n →ₗ[k] Hyp (OAff s) n := Hyp.pull (affCoef s) n

theorem HdR.toAff_mem_fil {p n : ℕ} {c : HdR s n} (hc : c ∈ HdR.fil s p n) :
    HdR.toAff s n c ∈ Hyp.fil (OAff s) p n :=
  Hyp.pull_mem_fil (affCoef s) hc

end Aff

section Fil

variable (s : X ⟶ Sp k)

theorem HdR.fil_zero (n : ℕ) : HdR.fil s 0 n = ⊤ := Hyp.fil_zero _ n

theorem HdR.fil_succ (n : ℕ) : HdR.fil s (n + 1) n = ⊥ := Hyp.fil_eq_bot _ (Nat.lt_succ_self n)

theorem HdR.fil_anti {p p' : ℕ} (h : p ≤ p') (n : ℕ) : HdR.fil s p' n ≤ HdR.fil s p n :=
  Hyp.fil_anti _ h n

end Fil

section Affine

variable (k) (B : Type) [CommRing B] [Algebra k B]

def idPt : AffPt (algStr k B) := ⟨CommAlgCat.of k B, 𝟙 _, Category.id_comp _⟩

variable {k B}

def toPt (T : AffPt (algStr k B)) : B →ₐ[k] T.B :=
  { (Spec.preimage T.x).hom with
    commutes' := fun r ↦ by
      have e : spMap (((Spec.preimage T.x).hom).comp (algebraMap k B)) = spMap (algebraMap k T.B) := by
        rw [spMap_comp', ← T.w]
        exact congrArg (· ≫ algStr k B) (Spec.map_preimage T.x)
      exact congrArg (fun g : k →+* T.B ↦ g r) (eq_of_spMap_eq e) }

theorem spMap_toPt (T : AffPt (algStr k B)) : spMap (toPt T : B →+* T.B) = T.x := Spec.map_preimage T.x

theorem toPt_comp ⦃T T' : AffPt (algStr k B)⦄ (φ : T ⟶ T') (b : B) :
    mp (OPt (algStr k B)) φ (toPt T b) = toPt T' b := by
  have e : spMap (((φ.1.hom : T.B →+* T'.B)).comp (toPt T : B →+* T.B)) = spMap (toPt T' : B →+* T'.B) := by
    rw [spMap_comp', spMap_toPt, spMap_toPt]; exact φ.2
  exact congrArg (fun g : B →+* T'.B ↦ g b) (eq_of_spMap_eq e)

def idPt_isInitial : Limits.IsInitial (idPt k B) :=
  Limits.IsInitial.ofUniqueHom (fun T ↦ ⟨CommAlgCat.ofHom (toPt T), (Category.comp_id _).trans (spMap_toPt T)⟩)
    fun T φ ↦ AffPt.hom_ext (CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective (eq_of_spMap_eq
      (((Category.comp_id _).symm.trans φ.2).trans (spMap_toPt T).symm))))

theorem toPt_idPt (b : B) : toPt (idPt k B) b = b := by
  have e : spMap (toPt (idPt k B) : B →+* (idPt k B).B) = spMap (RingHom.id B) :=
    (spMap_toPt _).trans (spMap_id' B).symm
  exact congrArg (fun g : B →+* B ↦ g b) (@eq_of_spMap_eq B (idPt k B).B _ _ (toPt (idPt k B)) (RingHom.id B) e)

theorem toPt_idPt_bijective : Function.Bijective (toPt (idPt k B)) :=
  Function.bijective_iff_has_inverse.2 ⟨fun b ↦ b, fun b ↦ toPt_idPt b, fun b ↦ toPt_idPt b⟩

def HdR.ofForm (n : ℕ) : LinearMap.ker (dOm k B n) →ₗ[k] HdR (algStr k B) n :=
  coneCl (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) n

theorem HdR.ofForm_mem_fil {n : ℕ} (ω : LinearMap.ker (dOm k B n)) :
    HdR.ofForm n ω ∈ HdR.fil (algStr k B) n n :=
  coneCl_mem_fil (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) ω

theorem HdR.ofForm_eq_zero_iff {n : ℕ} (ω : LinearMap.ker (dOm k B (n + 1))) :
    HdR.ofForm (n + 1) ω = 0 ↔ ∃ η, dOm k B n η = ω.1 :=
  coneCl_eq_zero_iff (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) (T₀ := idPt k B) toPt_idPt_bijective ω

def HdR.affZeroEquiv : LinearMap.ker (dOm k B 0) ≃ₗ[k] HdR (algStr k B) 0 :=
  LinearEquiv.ofBijective (HdR.ofForm 0) (coneCl_zero_bijective (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B))
    (fun T ↦ toPt T) (fun _ _ φ b ↦ toPt_comp φ b) (T₀ := idPt k B) toPt_idPt_bijective idPt_isInitial)

variable (k) in

theorem dOm_zero_self (x : Om k k 0) : dOm k k 0 x = 0 := by
  refine Subtype.ext ?_
  rw [coe_dOm, coe_eq_algebraMap_zeroEquiv x, dDR_algebraMap]
  have : D k k (exteriorPower.zeroEquiv k Ω[k⁄k] x) = 0 := by
    rw [← Algebra.algebraMap_self_apply (exteriorPower.zeroEquiv k Ω[k⁄k] x)]
    exact (D k k).map_algebraMap _
  rw [this, map_zero]; rfl

variable (k) in

def HdR.pointEquiv : k ≃ₗ[k] HdR (algStr k k) 0 :=
  (fn0 k).symm ≪≫ₗ (LinearEquiv.ofTop _ (eq_top_iff.2 fun x _ ↦ LinearMap.mem_ker.2 (dOm_zero_self k x))).symm ≪≫ₗ
    HdR.affZeroEquiv

open Polynomial in
variable (k) in

def tdtForm : LinearMap.ker (dOm k k[X] 1) :=
  ⟨⟨ι1 ((Polynomial.X : k[X]) • D k k[X] Polynomial.X), ι_mem _⟩, by
    rw [LinearMap.mem_ker, ← dOne_eq_dOm, dOne_line]⟩

open Polynomial in

theorem HdR.ofForm_tdt_ne_zero [Nontrivial k] (h2 : (2 : k) = 0) : HdR.ofForm 1 (tdtForm k) ≠ 0 := by
  rw [Ne, HdR.ofForm_eq_zero_iff]
  rintro ⟨η, hη⟩
  have e1 := congrArg Subtype.val hη
  rw [coe_dOm, coe_eq_algebraMap_zeroEquiv η, dDR_algebraMap] at e1
  have e2 := ExteriorAlgebra.ι_inj k[X] _ _ |>.1 e1
  have f3 := congrArg (polynomialEquiv k) e2
  simp only [Derivation.coeFn_coe, map_smul, polynomialEquiv_D, derivative_X, smul_eq_mul,
    mul_one] at f3
  have := congrArg (coeff · 1) f3
  simp only [coeff_derivative, coeff_X_one] at this
  have hc := this
  rw [show ((1 : ℕ) : k) + 1 = 2 by norm_num, h2, mul_zero] at hc
  exact zero_ne_one hc

end Affine

example (s : X ⟶ Sp k) : Module k (HdR s 5) := inferInstance

example (s : X ⟶ Sp k) : HdR.fil s 2 1 = ⊥ := HdR.fil_succ s 1

example : Nontrivial (HdR (algStr ℤ ℤ) 0) := (HdR.pointEquiv ℤ).symm.toEquiv.nontrivial

example : HdR.fil (algStr (ZMod 2) (Polynomial (ZMod 2))) 1 1 ≠ ⊥ := fun h ↦
  HdR.ofForm_tdt_ne_zero (k := ZMod 2) rfl
    ((Submodule.mem_bot _).1 (h ▸ HdR.ofForm_mem_fil (tdtForm (ZMod 2))))

end GlobalTheory.HodgeCoh
