import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.HodgeCoh

theorem isIso_map_homOfLE {X : Scheme.{0}} {A B : X.Opens} (h : A ≤ B) (e : A = B) :
    IsIso (X.presheaf.map (homOfLE h).op) := by
  subst e
  have : homOfLE h = 𝟙 A := rfl
  rw [this, op_id, X.presheaf.map_id]
  infer_instance

theorem isIso_ι_app {X : Scheme.{0}} (V U : X.Opens) (h : U ≤ V) : IsIso (V.ι.app U) := by
  rw [Scheme.Opens.ι_app]
  refine isIso_map_homOfLE _ ?_
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 h

theorem preimage_square {X Y Z W : Scheme.{0}} {a : Y ⟶ Z} {b : Z ⟶ X} {c : Y ⟶ W} {d : W ⟶ X}
    (e : a ≫ b = c ≫ d) (U : X.Opens) : c ⁻¹ᵁ (d ⁻¹ᵁ U) = a ⁻¹ᵁ (b ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, e]

theorem app_square {X Y Z W : Scheme.{0}} {a : Y ⟶ Z} {b : Z ⟶ X} {c : Y ⟶ W} {d : W ⟶ X}
    (e : a ≫ b = c ≫ d) (U : X.Opens) (h : c ⁻¹ᵁ (d ⁻¹ᵁ U) ≤ a ⁻¹ᵁ (b ⁻¹ᵁ U)) (u : Γ(X, U)) :
    Y.presheaf.map (homOfLE h).op (a.app (b ⁻¹ᵁ U) (b.app U u)) = c.app (d ⁻¹ᵁ U) (d.app U u) := by
  have m : b.app U ≫ a.app (b ⁻¹ᵁ U) ≫ Y.presheaf.map (homOfLE h).op = d.app U ≫ c.app (d ⁻¹ᵁ U) := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, e]
  exact ConcreteCategory.congr_hom m u

theorem formRes_formPull_congr {k : Type} [CommRing k] {X Y : Scheme.{0}} {s : X ⟶ Sp k}
    {t : Y ⟶ Sp k} {m m' : Y ⟶ X} (e : m = m') (hm : m ≫ s = t) (hm' : m' ≫ s = t)
    (U : X.Opens) (h : m' ⁻¹ᵁ U ≤ m ⁻¹ᵁ U) (j : ℕ) (x : OmU s U j) :
    formRes t h j (formPull hm U j x) = formPull hm' U j x := by
  subst e
  exact formRes_refl t _ _

theorem formRes_formPull_formPull {k : Type} [CommRing k] {X Y Z W : Scheme.{0}}
    {s : X ⟶ Sp k} {sZ : Z ⟶ Sp k} {sW : W ⟶ Sp k} {t : Y ⟶ Sp k} {a : Y ⟶ Z} {b : Z ⟶ X}
    {c : Y ⟶ W} {d : W ⟶ X} (e : a ≫ b = c ≫ d) (hb : b ≫ s = sZ) (ha : a ≫ sZ = t)
    (hd : d ≫ s = sW) (hc : c ≫ sW = t) (U : X.Opens) (h : c ⁻¹ᵁ (d ⁻¹ᵁ U) ≤ a ⁻¹ᵁ (b ⁻¹ᵁ U))
    (j : ℕ) (x : OmU s U j) :
    formRes t h j (formPull ha (b ⁻¹ᵁ U) j (formPull hb U j x)) =
      formPull hc (d ⁻¹ᵁ U) j (formPull hd U j x) := by
  have h1 : (a ≫ b) ≫ s = t := by rw [Category.assoc, hb, ha]
  have h2 : (c ≫ d) ≫ s = t := by rw [Category.assoc, hd, hc]
  rw [formPull_formPull hb ha h1 U j x, formPull_formPull hd hc h2 U j x]
  exact formRes_formPull_congr e h1 h2 U h j x

theorem hom_ext_ι {X : Scheme.{0}} (V : X.Opens) {G : X.Modules} {F : (V : Scheme.{0}).Modules}
    (a b : G ⟶ (Scheme.Modules.pushforward V.ι).obj F)
    (h : ∀ U : X.Opens, IsAffineOpen U → U ≤ V → ∀ x, a.app U x = b.app U x) : a = b := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext x
  refine section_ext_affine (F := F) (U := V.ι ⁻¹ᵁ U) fun W hW hWU ↦ ?_
  have hW' : IsAffineOpen (V.ι ''ᵁ W) := hW.image_of_isOpenImmersion V.ι
  have hWV : V.ι ''ᵁ W ≤ V := by
    have := (V.ι.image_le_image_iff W ⊤).2 le_top
    rwa [Scheme.Opens.ι_image_top] at this
  have hWU' : V.ι ''ᵁ W ≤ U := by
    refine ((V.ι.image_le_image_iff W _).2 hWU).trans ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_right
  have hW2 : W ≤ V.ι ⁻¹ᵁ (V.ι ''ᵁ W) := (V.ι.preimage_image_eq W).ge
  have n : ∀ c : G ⟶ (Scheme.Modules.pushforward V.ι).obj F,
      F.presheaf.map (homOfLE hWU).op (c.app U x) =
        F.presheaf.map (homOfLE hW2).op (c.app (V.ι ''ᵁ W) (G.presheaf.map (homOfLE hWU').op x)) :=
    fun c ↦ by
      have e1 : ((Scheme.Modules.pushforward V.ι).obj F).presheaf.map (homOfLE hWU').op
          (c.app U x) = c.app (V.ι ''ᵁ W) (G.presheaf.map (homOfLE hWU').op x) :=
        (ConcreteCategory.congr_hom (c.mapPresheaf.naturality (homOfLE hWU').op) x).symm
      rw [← e1]
      change _ = F.presheaf.map (homOfLE hW2).op
        (F.presheaf.map ((TopologicalSpace.Opens.map V.ι.base).map (homOfLE hWU')).op (c.app U x))
      exact ConcreteCategory.congr_hom (F.presheaf.map_comp _ _) _
  rw [n a, n b, h _ hW' hWV]

theorem secTrace_restrict {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k}
    {s' : X' ⟶ Sp k} {f : X' ⟶ X} [IsFinite f] [Etale f] (V : X.Opens) {U : X.Opens}
    (hU : IsAffineOpen U) (hUV : U ≤ V) (hU' : IsAffineOpen (V.ι ⁻¹ᵁ U))
    (h : (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ U)) (b' : Sec s' (f ⁻¹ᵁ U)) :
    secTrace (f := f ∣_ V) (V.ι ≫ s) ((f ⁻¹ᵁ V).ι ≫ s') hU'
        (Sec.res ((f ⁻¹ᵁ V).ι ≫ s') h (appSec s' ((f ⁻¹ᵁ V).ι ≫ s') (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ U) b')) =
      appSec s (V.ι ≫ s) V.ι U (secTrace s s' hU b') := by
  have hw : (f ⁻¹ᵁ V).ι ≫ f = f ∣_ V ≫ V.ι := (morphismRestrict_ι f V).symm
  letI := secAlg s s' f U
  letI : Algebra (Sec s U) (Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ U)) := (appSec s (V.ι ≫ s) V.ι U).toAlgebra
  letI : Algebra (Sec s' (f ⁻¹ᵁ U)) (Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) :=
    ((Sec.res ((f ⁻¹ᵁ V).ι ≫ s') h : _ →+* _).comp
      (appSec s' ((f ⁻¹ᵁ V).ι ≫ s') (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ U))).toAlgebra
  letI := secAlg (V.ι ≫ s) ((f ⁻¹ᵁ V).ι ≫ s') (f ∣_ V) (V.ι ⁻¹ᵁ U)
  letI : Algebra (Sec s U) (Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) :=
    ((appSec (V.ι ≫ s) ((f ⁻¹ᵁ V).ι ≫ s') (f ∣_ V) (V.ι ⁻¹ᵁ U)).comp
      (appSec s (V.ι ≫ s) V.ι U)).toAlgebra
  have hsq : ∀ b : Sec s U, appSec (V.ι ≫ s) ((f ⁻¹ᵁ V).ι ≫ s') (f ∣_ V) (V.ι ⁻¹ᵁ U)
      (appSec s (V.ι ≫ s) V.ι U b) = Sec.res ((f ⁻¹ᵁ V).ι ≫ s') h
        (appSec s' ((f ⁻¹ᵁ V).ι ≫ s') (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ U) (appSec s s' f U b)) :=
    fun b ↦ (app_square hw U h b).symm
  haveI : IsScalarTower (Sec s U) (Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ U))
      (Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (Sec s U) (Sec s' (f ⁻¹ᵁ U))
      (Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) := .of_algebraMap_eq hsq
  haveI : IsIso (CommRingCat.ofHom (algebraMap (Sec s U) (Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ U)))) :=
    isIso_ι_app V U hUV
  haveI : IsIso (CommRingCat.ofHom (algebraMap (Sec s' (f ⁻¹ᵁ U))
      (Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))))) := by
    have : IsIso ((f ⁻¹ᵁ V).ι.app (f ⁻¹ᵁ U)) := isIso_ι_app _ _ (f.preimage_mono hUV)
    have : IsIso ((f ⁻¹ᵁ V : Scheme.{0}).presheaf.map (homOfLE h).op) :=
      isIso_map_homOfLE h (preimage_square hw U)
    change IsIso ((f ⁻¹ᵁ V).ι.app (f ⁻¹ᵁ U) ≫ (f ⁻¹ᵁ V : Scheme.{0}).presheaf.map (homOfLE h).op)
    infer_instance
  haveI : Algebra.IsPushout (Sec s U) (Sec s' (f ⁻¹ᵁ U)) (Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ U))
      (Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) :=
    CommRingCat.isPushout_iff_isPushout.1 (IsPushout.of_vert_isIso ⟨by ext b; exact (hsq b).symm⟩)
  haveI := this.symm
  haveI := sec_finite (s := s) (s' := s') (f := f) hU
  haveI := sec_etale (s := s) (s' := s') (f := f) hU
  haveI := sec_finite (s := V.ι ≫ s) (s' := (f ⁻¹ᵁ V).ι ≫ s') (f := f ∣_ V) hU'
  haveI := sec_etale (s := V.ι ≫ s) (s' := (f ⁻¹ᵁ V).ι ≫ s') (f := f ∣_ V) hU'
  haveI := projective_of_etale (Sec s U) (Sec s' (f ⁻¹ᵁ U))
  haveI := projective_of_etale (Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ U))
    (Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
  change algTrace (Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ U)) (Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
      (algebraMap (Sec s' (f ⁻¹ᵁ U)) (Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) b') =
    algebraMap (Sec s U) (Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ U)) (algTrace (Sec s U) (Sec s' (f ⁻¹ᵁ U)) b')
  exact algTrace_of_isPushout (C := Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ U))
    (C' := Sec ((f ⁻¹ᵁ V).ι ≫ s') ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) b'

theorem formPull_restrict {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k}
    {s' : X' ⟶ Sp k} {f : X' ⟶ X} (hf : f ≫ s = s') (V : X.Opens)
    (hg : f ∣_ V ≫ V.ι ≫ s = (f ⁻¹ᵁ V).ι ≫ s') (U : X.Opens)
    (h : (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ U)) (j : ℕ) (x : OmU s U j) :
    formRes ((f ⁻¹ᵁ V).ι ≫ s') h j
        (formPull (f := (f ⁻¹ᵁ V).ι) (s' := (f ⁻¹ᵁ V).ι ≫ s') rfl (f ⁻¹ᵁ U) j (formPull hf U j x)) =
      formPull hg (V.ι ⁻¹ᵁ U) j (formPull (f := V.ι) (s' := V.ι ≫ s) rfl U j x) := by
  exact formRes_formPull_formPull (morphismRestrict_ι f V).symm hf rfl rfl hg U h j x

theorem formRes_formPull_smul {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k}
    {s' : X' ⟶ Sp k} {f : X' ⟶ X} (hf : f ≫ s = s') (V : X.Opens)
    (hg : f ∣_ V ≫ V.ι ≫ s = (f ⁻¹ᵁ V).ι ≫ s') (j : ℕ) (U : X.Opens)
    (hle : (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ U))
    (b' : Sec s' (f ⁻¹ᵁ U)) (x : OmU s U j) :
    formRes ((f ⁻¹ᵁ V).ι ≫ s') hle j (formPull (f := (f ⁻¹ᵁ V).ι) (s' := (f ⁻¹ᵁ V).ι ≫ s') rfl
        (f ⁻¹ᵁ U) j (b' • formPull hf U j x)) =
      Sec.res ((f ⁻¹ᵁ V).ι ≫ s') hle (appSec s' ((f ⁻¹ᵁ V).ι ≫ s') (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ U) b') •
        formPull hg (V.ι ⁻¹ᵁ U) j (formPull (f := V.ι) (s' := V.ι ≫ s) rfl U j x) := by
  rw [formPull_smul rfl (f ⁻¹ᵁ U) b' (formPull hf U j x)]
  refine (formRes_smul ((f ⁻¹ᵁ V).ι ≫ s') hle
    (appSec s' ((f ⁻¹ᵁ V).ι ≫ s') (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ U) b')
    (formPull (f := (f ⁻¹ᵁ V).ι) (s' := (f ⁻¹ᵁ V).ι ≫ s') rfl (f ⁻¹ᵁ U) j
      (formPull hf U j x))).trans ?_
  exact congrArg (Sec.res ((f ⁻¹ᵁ V).ι ≫ s') hle
    (appSec s' ((f ⁻¹ᵁ V).ι ≫ s') (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ U) b') • ·) (formPull_restrict hf V hg U hle j x)

theorem cohOn_pull_pull {X Y Z : Scheme.{0}} {R : Type} [CommRing R] [Algebra R Γ(X, ⊤)]
    [Algebra R Γ(Y, ⊤)] [Algebra R Γ(Z, ⊤)] {b : Y ⟶ X} {a : Z ⟶ Y}
    (hb : ∀ r, b.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) (RingHom.id R r))
    (ha : ∀ r, a.appTop (algebraMap R Γ(Y, ⊤) r) = algebraMap R Γ(Z, ⊤) (RingHom.id R r))
    (hab : ∀ r, (a ≫ b).appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Z, ⊤) (RingHom.id R r))
    {F : X.Modules} {G : Y.Modules} {H : Z.Modules} (φ : F ⟶ (Scheme.Modules.pushforward b).obj G)
    (ψ : G ⟶ (Scheme.Modules.pushforward a).obj H) {V : X.Opens} {W : Y.Opens} {T : Z.Opens}
    (h₁ : W ≤ b ⁻¹ᵁ V) (h₂ : T ≤ a ⁻¹ᵁ W) (h : T ≤ (a ≫ b) ⁻¹ᵁ V) (n : ℕ) (x : cohOn F V n) :
    cohOn.pull ha ψ h₂ n (cohOn.pull hb φ h₁ n x) =
      cohOn.pull hab (φ ≫ (Scheme.Modules.pushforward b).map ψ ≫
        (Scheme.Modules.pushforwardComp a b).hom.app H) h n x := by
  apply (cohOn.toH' H T n).injective
  rw [cohOn.toH'_pull, cohOn.toH'_pull, cohOn.toH'_pull]
  exact SheafPull.pull_pull.{0, 0, 0} b.base a.base _ _ n _ _ _

theorem cohOn_pull_congr {X Y : Scheme.{0}} {R : Type} [CommRing R] [Algebra R Γ(X, ⊤)]
    [Algebra R Γ(Y, ⊤)] {a b : Y ⟶ X} (e : a = b)
    (ha : ∀ r, a.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) (RingHom.id R r))
    (hb : ∀ r, b.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) (RingHom.id R r))
    {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (Scheme.Modules.pushforward a).obj G)
    {V : X.Opens} {W : Y.Opens} (h : W ≤ a ⁻¹ᵁ V) (h' : W ≤ b ⁻¹ᵁ V) (n : ℕ) (x : cohOn F V n) :
    cohOn.pull ha φ h n x =
      cohOn.pull hb (φ ≫ (Scheme.Modules.pushforwardCongr e).hom.app G) h' n x := by
  subst e
  have : (Scheme.Modules.pushforwardCongr (rfl : a = a)).hom.app G = 𝟙 _ := by
    ext U : 1
    exact G.presheaf.map_id _
  rw [this, Category.comp_id]

def pushRestrict {k : Type} [CommRing k] {X X' : Scheme.{0}} (s' : X' ⟶ Sp k) (f : X' ⟶ X)
    (V : X.Opens) (j : ℕ) :
    (Scheme.Modules.pushforward f).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.pushforward (f ∣_ V)).obj
        (Omega ((f ⁻¹ᵁ V).ι ≫ s') j)) :=
  (Scheme.Modules.pushforward f).map (omegaPull (f := (f ⁻¹ᵁ V).ι) rfl j) ≫
    (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ V).ι f).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V).symm).hom.app _ ≫
        (Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).inv.app _

theorem pushRestrict_app {k : Type} [CommRing k] {X X' : Scheme.{0}} (s' : X' ⟶ Sp k)
    (f : X' ⟶ X) (V : X.Opens) (j : ℕ) (U : X.Opens)
    (hle : (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ U))
    (w : Γ((Scheme.Modules.pushforward f).obj (Omega s' j), U)) :
    (pushRestrict s' f V j).app U w = (Omega ((f ⁻¹ᵁ V).ι ≫ s') j).presheaf.map (homOfLE hle).op
      ((omegaPull (f := (f ⁻¹ᵁ V).ι) (s' := (f ⁻¹ᵁ V).ι ≫ s') rfl j).app (f ⁻¹ᵁ U) w) := by
  rfl

theorem trace_pull_app_lhs {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k}
    {s' : X' ⟶ Sp k} {f : X' ⟶ X} [IsFinite f] [Etale f] (hf : f ≫ s = s') (V : X.Opens) (j : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) (b' : Sec s' (f ⁻¹ᵁ U)) (x : OmU s U j) :
    (omegaTrace hf j ≫ omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl j).app U
        (toOm s' j (f ⁻¹ᵁ U) (b' • formPull hf U j x)) = toOm (V.ι ≫ s) j (V.ι ⁻¹ᵁ U)
          (appSec s (V.ι ≫ s) V.ι U (secTrace s s' hU b') •
            formPull (f := V.ι) (s' := V.ι ≫ s) rfl U j x) := by
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl j).val.app (op U)
    ((omegaTrace hf j).app U (toOm s' j (f ⁻¹ᵁ U) (b' • formPull hf U j x))) = _
  rw [omegaTrace_toOm_smul_formPull hf j hU, toOm_apply, omegaPull_toOmega, formPull_smul]
  rfl

theorem pushRestrict_app_smul {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k}
    {s' : X' ⟶ Sp k} {f : X' ⟶ X} (hf : f ≫ s = s') (V : X.Opens)
    (hg : f ∣_ V ≫ V.ι ≫ s = (f ⁻¹ᵁ V).ι ≫ s') (j : ℕ) (U : X.Opens)
    (hle : (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ U))
    (b' : Sec s' (f ⁻¹ᵁ U)) (x : OmU s U j) :
    (pushRestrict s' f V j).app U (toOm s' j (f ⁻¹ᵁ U) (b' • formPull hf U j x)) =
      toOm ((f ⁻¹ᵁ V).ι ≫ s') j ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))
        (Sec.res ((f ⁻¹ᵁ V).ι ≫ s') hle
          (appSec s' ((f ⁻¹ᵁ V).ι ≫ s') (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ U) b') •
          formPull hg (V.ι ⁻¹ᵁ U) j (formPull (f := V.ι) (s' := V.ι ≫ s) rfl U j x)) := by
  refine (pushRestrict_app s' f V j U hle _).trans ?_
  change (Omega ((f ⁻¹ᵁ V).ι ≫ s') j).presheaf.map (homOfLE hle).op
    ((omegaPull (f := (f ⁻¹ᵁ V).ι) (s' := (f ⁻¹ᵁ V).ι ≫ s') rfl j).val.app (op (f ⁻¹ᵁ U))
      ((toOmega s' j).app (op (f ⁻¹ᵁ U)) (b' • formPull hf U j x))) = _
  rw [omegaPull_toOmega]
  refine (res_toOm ((f ⁻¹ᵁ V).ι ≫ s') j hle (formPull (f := (f ⁻¹ᵁ V).ι)
    (s' := (f ⁻¹ᵁ V).ι ≫ s') rfl (f ⁻¹ᵁ U) j (b' • formPull hf U j x))).trans ?_
  exact congrArg (toOm ((f ⁻¹ᵁ V).ι ≫ s') j ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
    (formRes_formPull_smul hf V hg j U hle b' x)

theorem trace_pull_app_rhs {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k}
    {s' : X' ⟶ Sp k} {f : X' ⟶ X} [IsFinite f] [Etale f] (hf : f ≫ s = s') (V : X.Opens)
    (hg : f ∣_ V ≫ V.ι ≫ s = (f ⁻¹ᵁ V).ι ≫ s') (j : ℕ) {U : X.Opens}
    (hU' : IsAffineOpen (V.ι ⁻¹ᵁ U))
    (hle : (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ U))
    (b' : Sec s' (f ⁻¹ᵁ U)) (x : OmU s U j) :
    (pushRestrict s' f V j ≫ (Scheme.Modules.pushforward V.ι).map (omegaTrace hg j)).app U
        (toOm s' j (f ⁻¹ᵁ U) (b' • formPull hf U j x)) = toOm (V.ι ≫ s) j (V.ι ⁻¹ᵁ U)
          (secTrace (f := f ∣_ V) (V.ι ≫ s) ((f ⁻¹ᵁ V).ι ≫ s') hU'
            (Sec.res ((f ⁻¹ᵁ V).ι ≫ s') hle
              (appSec s' ((f ⁻¹ᵁ V).ι ≫ s') (f ⁻¹ᵁ V).ι (f ⁻¹ᵁ U) b')) •
            formPull (f := V.ι) (s' := V.ι ≫ s) rfl U j x) := by
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaTrace hg j).app (V.ι ⁻¹ᵁ U) ((pushRestrict s' f V j).app U
    (toOm s' j (f ⁻¹ᵁ U) (b' • formPull hf U j x))) = _
  rw [pushRestrict_app_smul hf V hg j U hle, omegaTrace_toOm_smul_formPull hg j hU']

theorem omegaTrace_comp_omegaPull_ι {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k}
    {s' : X' ⟶ Sp k} {f : X' ⟶ X} [IsFinite f] [Etale f] (hf : f ≫ s = s') (V : X.Opens)
    (hg : f ∣_ V ≫ V.ι ≫ s = (f ⁻¹ᵁ V).ι ≫ s') (j : ℕ) :
    omegaTrace hf j ≫ omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl j =
      pushRestrict s' f V j ≫ (Scheme.Modules.pushforward V.ι).map (omegaTrace hg j) := by

  refine hom_ext_ι V _ _ fun U hU hUV y ↦ ?_
  have hU' : IsAffineOpen (V.ι ⁻¹ᵁ U) :=
    hU.preimage_of_isOpenImmersion V.ι (by rw [Scheme.Opens.opensRange_ι]; exact hUV)
  have hle : (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  obtain ⟨z, rfl⟩ := toOm_surjective (s := s') (j := j) (hU.preimage f) y
  refine formOm_induction (P := fun z ↦ (omegaTrace hf j ≫ omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl j).app U (toOm s' j (f ⁻¹ᵁ U) z) =
      (pushRestrict s' f V j ≫ (Scheme.Modules.pushforward V.ι).map (omegaTrace hg j)).app U
        (toOm s' j (f ⁻¹ᵁ U) z)) hf hU ?_ (fun y z hy hz ↦ ?_) (fun b' x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz

  · rw [trace_pull_app_lhs hf V j hU, trace_pull_app_rhs hf V hg j hU' hle,
      secTrace_restrict V hU hUV hU' hle b']

theorem hodgePull_hodgeTrace_ι : ∀ {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X} [IsFinite f] [Etale f] (hf : f ≫ s = s') (V : X.Opens) (j q : ℕ) (x : hodgeH s' j q), hodgePull (f := V.ι) (s' := V.ι ≫ s) rfl j q (hodgeTrace hf j q x) = hodgeTrace (f := f ∣_ V) (s := V.ι ≫ s) (s' := (f ⁻¹ᵁ V).ι ≫ s') (by rw [← hf, ← Category.assoc, morphismRestrict_ι, Category.assoc]) j q (hodgePull (f := (f ⁻¹ᵁ V).ι) rfl j q x) := by
  intro k _ X X' s s' f _ _ hf V j q x
  letI := algΓ s; letI := algΓ s'; letI := algΓ (V.ι ≫ s); letI := algΓ ((f ⁻¹ᵁ V).ι ≫ s')
  have hg : f ∣_ V ≫ V.ι ≫ s = (f ⁻¹ᵁ V).ι ≫ s' := by
    rw [← hf, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  obtain ⟨y, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega s' j) q).surjective x
  have e1 : hodgeTrace hf j q (coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega s' j) q y) =
      cohOn.map k (omegaTrace hf j) ⊤ q y :=
    congrArg (cohOn.map k (omegaTrace hf j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega s' j) q).symm_apply_apply y)
  have e4 := cohOn.pull_map (σ := RingHom.id k) (appTop_algebraMap (f := V.ι) (s := s) rfl)
    (omegaPull rfl j) (omegaTrace hf j) (le_refl (V.ι ⁻¹ᵁ ⊤)) (n := q) y
  rw [omegaTrace_comp_omegaPull_ι hf V hg j] at e4
  have e5 := cohOn.map_pull (σ := RingHom.id k) (appTop_algebraMap (f := V.ι) (s := s) rfl)
    (pushRestrict s' f V j) (omegaTrace hg j) (le_refl (V.ι ⁻¹ᵁ ⊤)) (n := q) y
  rw [e1]
  refine e4.trans (e5.symm.trans ?_)
  change _ = cohOn.map k (omegaTrace hg j) ⊤ q
      ((coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega ((f ⁻¹ᵁ V).ι ≫ s') j) q).symm _)
  congr 1
  refine ((coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega ((f ⁻¹ᵁ V).ι ≫ s') j) q).eq_symm_apply).2 ?_
  have hw : (f ⁻¹ᵁ V).ι ≫ f = f ∣_ V ≫ V.ι := (morphismRestrict_ι f V).symm
  have s1 := cohOn_pull_pull (appTop_algebraMap (f := V.ι) (s := s) rfl) (appTop_algebraMap hg)
    (appTop_algebraMap (f := f ∣_ V ≫ V.ι) (s := s) (s' := (f ⁻¹ᵁ V).ι ≫ s')
      (by rw [Category.assoc, hg]))
    (pushRestrict s' f V j) (𝟙 _) (le_refl (V.ι ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) q y
  have s2 := cohOn_pull_pull (appTop_algebraMap hf)
    (appTop_algebraMap (f := (f ⁻¹ᵁ V).ι) (s := s') rfl)
    (appTop_algebraMap (f := (f ⁻¹ᵁ V).ι ≫ f) (s := s) (s' := (f ⁻¹ᵁ V).ι ≫ s')
      (by rw [Category.assoc, hf]))
    (𝟙 _) (omegaPull rfl j) (le_refl (f ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) q y
  have s3 := cohOn_pull_congr hw
    (appTop_algebraMap (f := (f ⁻¹ᵁ V).ι ≫ f) (s := s) (s' := (f ⁻¹ᵁ V).ι ≫ s')
      (by rw [Category.assoc, hf]))
    (appTop_algebraMap (f := f ∣_ V ≫ V.ι) (s := s) (s' := (f ⁻¹ᵁ V).ι ≫ s')
      (by rw [Category.assoc, hg]))
    (G := Omega ((f ⁻¹ᵁ V).ι ≫ s') j)
    (𝟙 ((Scheme.Modules.pushforward f).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward f).map (omegaPull (f := (f ⁻¹ᵁ V).ι) rfl j) ≫
        (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ V).ι f).hom.app _)
    (V := ⊤) (W := (f ⁻¹ᵁ V).ι ⁻¹ᵁ (f ⁻¹ᵁ ⊤)) (le_refl _) (fun _ _ ↦ trivial) q y
  have hm : pushRestrict s' f V j ≫ (Scheme.Modules.pushforward V.ι).map (𝟙 _) ≫
        (Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).hom.app _ =
      (𝟙 ((Scheme.Modules.pushforward f).obj (Omega s' j)) ≫
        (Scheme.Modules.pushforward f).map (omegaPull (f := (f ⁻¹ᵁ V).ι) rfl j) ≫
          (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ V).ι f).hom.app _) ≫
        (Scheme.Modules.pushforwardCongr hw).hom.app _ := by
    simp [pushRestrict]
  refine Eq.trans (cohOn.pushforwardEquiv_apply k (appTop_algebraMap hg) _ ⊤ q _) (s1.trans ?_)
  rw [hm]
  refine s3.symm.trans ?_
  exact s2.symm

end GlobalTheory.HodgeCoh
