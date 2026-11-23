import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvFieldComm

section Rings

variable {S : Type} [CommRing S]

def fstH (S : Type) [CommRing S] : DualNumber S →+* S := (TrivSqZeroExt.fstHom S S S).toRingHom

@[simp] theorem fstH_apply (x : DualNumber S) : fstH S x = x.fst := rfl

def swap (S : Type) [CommRing S] : DualNumber (DualNumber S) →+* DualNumber (DualNumber S) where
  toFun x := TrivSqZeroExt.inl (TrivSqZeroExt.inl x.fst.fst + TrivSqZeroExt.inr x.snd.fst) +
    TrivSqZeroExt.inr (TrivSqZeroExt.inl x.fst.snd + TrivSqZeroExt.inr x.snd.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp <;> ring
  map_mul' a b := by ext <;> simp <;> ring

theorem swap_snd_snd (x : DualNumber (DualNumber S)) : (swap S x).snd.snd = x.snd.snd := by
  simp [swap]

end Rings

section Rings2

variable {R S : Type} [CommRing R] [CommRing S]

abbrev inc (S : Type) [CommRing S] : S →+* DualNumber S := algebraMap S (DualNumber S)

theorem dualMap_comp_inc (φ : R →+* S) : (dualMap φ).comp (inc R) = (inc S).comp φ := by
  refine RingHom.ext fun x => ?_; ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_inc : (fstH S).comp (inc S) = RingHom.id S := by
  refine RingHom.ext fun x => ?_; simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_inc_inc_comp (φ : R →+* S) : (swap S).comp ((inc (DualNumber S)).comp ((inc S).comp φ)) =
    (inc (DualNumber S)).comp ((inc S).comp φ) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_inc_dualMap (φ : R →+* S) : (swap S).comp ((inc (DualNumber S)).comp (dualMap φ)) = dualMap ((inc S).comp φ) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_dualMap_inc (φ : R →+* S) : (swap S).comp (dualMap ((inc S).comp φ)) = (inc (DualNumber S)).comp (dualMap φ) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : R →+* S) : (fstH S).comp (dualMap φ) = φ.comp (fstH R) := by
  refine RingHom.ext fun x => ?_; simp [dualMap]

theorem inc_comp_fst : (inc R).comp (fstH R) = ((tm (0 • LinearMap.id : R →ₗ[R] R)) : DualNumber R →+* DualNumber R) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [tm, TrivSqZeroExt.algebraMap_eq_inl]

end Rings2

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ψ' : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap ψ' = spMap (ψ.comp ψ') := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem dual_pt {S : Type} [CommRing S] (x : Sp (DualNumber S)) :
    (spMap (fstH S)) ((spMap (algebraMap S (DualNumber S))) x) = x := by
  apply PrimeSpectrum.ext
  ext y
  change algebraMap S (DualNumber S) (fstH S y) ∈ x.asIdeal ↔ y ∈ x.asIdeal
  have hn : (TrivSqZeroExt.inr y.snd : DualNumber S) ∈ x.asIdeal :=
    x.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)
  have hy : y = algebraMap S (DualNumber S) (fstH S y) + TrivSqZeroExt.inr y.snd :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq y).symm
  constructor
  · intro h; rw [hy]; exact add_mem h hn
  · intro h
    have e : algebraMap S (DualNumber S) (fstH S y) = y - TrivSqZeroExt.inr y.snd := by
      rw [eq_sub_iff_add_eq]; exact hy.symm
    rw [e]; exact sub_mem h hn

section Val

variable {A : Type} [CommRing A] {X : Scheme.{0}}

def evHom (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valR_eq_evHom (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = evHom x U h f := by
  unfold valR
  rw [dif_pos h]
  rfl

theorem top_le_spMap {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U := fun y _ => h (Set.mem_univ ((spMap ψ) y))

theorem valR_spMap_comp {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR (spMap ψ ≫ x) U f = ψ (valR x U f) := by
  have h' := top_le_spMap ψ x U h
  rw [valR_eq_evHom _ U h', valR_eq_evHom x U h]
  have e : (spMap ψ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap ψ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap ψ) x U ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f =
    (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f
  rw [e, Category.assoc, n]

theorem top_le_fromSpecStalk {x : X} {U : X.Opens} (hU : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
  have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU

theorem valR_fromSpecStalk {x : X} {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (A := X.presheaf.stalk x) (X.fromSpecStalk x) U a = X.presheaf.germ U x hU a := by
  have h := top_le_fromSpecStalk hU
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans
      (Category.comp_id _))
  unfold valR
  refine (dif_pos h).trans ?_
  change ((X.fromSpecStalk x).appLE U ⊤ h ≫ (Scheme.ΓSpecIso _).hom).hom a = _
  rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Val

section Tr

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem tv_hom (v : TanM (𝟙 (Sp R)) G) : (tv v).left ≫ G.hom = spMap (inc R) := by
  have := Over.w (tv v)
  simpa using this

theorem one_left' {T : Over (Sp R)} : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  show (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left, Over.toUnit_left]

theorem fst_tv (v : TanM (𝟙 (Sp R)) G) : spMap (fstH R) ≫ (tv v).left = η[G].left := by
  have h := congrArg (fun k => k.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
  simp only [smT, Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, one_left'] at h
  have gen : ∀ ψ : DualNumber R →+* DualNumber R, (∀ x, ψ x = inc R x.fst) →
      spMap ψ ≫ (tv v).left = (overAt (𝟙 (Sp R)) (DualNumber R)).hom ≫ η[G].left →
      spMap ((inc R).comp (fstH R)) ≫ (tv v).left = spMap (inc R) ≫ η[G].left := by
    intro ψ hψ hh
    have : ψ = (inc R).comp (fstH R) := RingHom.ext fun x => hψ x
    subst this
    simpa using hh
  have e2 := gen _ (fun x => by ext <;> simp [tm, TrivSqZeroExt.algebraMap_eq_inl]) h
  have h2 := congrArg (fun k => spMap (fstH R) ≫ k) e2
  simp only [← spMap_comp, ← Category.assoc] at h2
  simp only [spMap_comp, fst_comp_inc, spMap_id] at h2
  simpa using h2

variable {S : Type} [CommRing S]

def gW (g : Sp S ⟶ G.left) : tEpsG (g ≫ G.hom) ⟶ G :=
  Over.homMk (spMap (inc S) ≫ g) (by simp)

def vW (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    tEpsG (g ≫ G.hom) ⟶ G :=
  Over.homMk (spMap (dualMap φ) ≫ (tv v).left) (by
    simp only [tEpsG, Over.mk_hom, Category.assoc, tv_hom, hg, spMap_comp, dualMap_comp_inc])

def trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    Sp (DualNumber S) ⟶ G.left :=
  (gW G g * vW G φ g hg v).left

theorem isTr_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    GlobalTheory.Heat.IsTr G φ g v (trP G φ g hg v) :=
  ⟨_, _, rfl, rfl, rfl⟩

theorem translateTangent_comp_hom (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    trP G φ g hg v ≫ G.hom = spMap ((inc S).comp φ) := by
  rw [trP, Over.w]
  simp only [tEpsG, Over.mk_hom, hg, spMap_comp]

theorem fst_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    spMap (fstH S) ≫ trP G φ g hg v = g := by
  let E : Over.mk (g ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (fstH S)) (by
      show spMap (fstH S) ≫ spMap (inc S) ≫ g ≫ G.hom = g ≫ G.hom
      rw [← Category.assoc, spMap_comp, fst_comp_inc, spMap_id]; exact Category.id_comp _)
  have e1 : E ≫ gW G g = Over.homMk g rfl := by
    ext
    show spMap (fstH S) ≫ spMap (inc S) ≫ g = g
    rw [← Category.assoc, spMap_comp, fst_comp_inc, spMap_id]; exact Category.id_comp _
  have e2 : E ≫ vW G φ g hg v = 1 := by
    ext
    simp only [E, vW, Over.comp_left, Over.homMk_left, one_left', Over.mk_hom]
    rw [← Category.assoc, spMap_comp, fst_comp_dualMap, ← spMap_comp, Category.assoc, fst_tv, hg]
  have := congrArg (fun k => k.left) (MonObj.comp_mul E (gW G g) (vW G φ g hg v))
  simpa only [e1, e2, _root_.mul_one, Over.comp_left, Over.homMk_left, E, trP] using this

theorem top_le_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G)
    (O : G.left.Opens) (hO : ⊤ ≤ g ⁻¹ᵁ O) : ⊤ ≤ trP G φ g hg v ⁻¹ᵁ O := by
  intro x _
  rw [← dual_pt x]
  show (spMap (fstH S) ≫ trP G φ g hg v) _ ∈ O
  rw [fst_trP]
  exact hO (Set.mem_univ _)

end Tr

section Swap

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]

theorem swap_inc_inc : (swap S).comp ((inc (DualNumber S)).comp (inc S)) = (inc (DualNumber S)).comp (inc S) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v v' : TanM (𝟙 (Sp R)) G) :
    trP G ((inc S).comp φ) (trP G φ g hg v) (translateTangent_comp_hom G φ g hg v) v' =
      spMap (swap S) ≫ trP G ((inc S).comp φ) (trP G φ g hg v') (translateTangent_comp_hom G φ g hg v') v := by
  have hw := translateTangent_comp_hom G φ g hg v'
  have hu := translateTangent_comp_hom G φ g hg v
  let P : tEpsG (trP G φ g hg v' ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (inc (DualNumber S))) (by
      show spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g ≫ G.hom =
        spMap (inc (DualNumber S)) ≫ trP G φ g hg v' ≫ G.hom
      rw [trP, Over.w]; rfl)
  let P' : tEpsG (trP G φ g hg v ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (inc (DualNumber S))) (by
      show spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g ≫ G.hom =
        spMap (inc (DualNumber S)) ≫ trP G φ g hg v ≫ G.hom
      rw [trP, Over.w]; rfl)
  let Q : tEpsG (trP G φ g hg v ≫ G.hom) ⟶ tEpsG (trP G φ g hg v' ≫ G.hom) :=
    Over.homMk (spMap (swap S)) (by
      show spMap (swap S) ≫ spMap (inc (DualNumber S)) ≫ trP G φ g hg v' ≫ G.hom =
        spMap (inc (DualNumber S)) ≫ trP G φ g hg v ≫ G.hom
      rw [hw, hu, spMap_comp, spMap_comp, swap_inc_inc_comp])
  have e1 : gW G (trP G φ g hg v') = P ≫ (gW G g * vW G φ g hg v') := Over.OverMorphism.ext rfl
  have e2 : gW G (trP G φ g hg v) = P' ≫ (gW G g * vW G φ g hg v) := Over.OverMorphism.ext rfl
  have hx : Q ≫ P ≫ gW G g = P' ≫ gW G g := by
    ext
    show spMap (swap S) ≫ spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g =
      spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g
    simp only [← Category.assoc, spMap_comp]
    rw [swap_inc_inc]
  have hb : Q ≫ P ≫ vW G φ g hg v' = vW G ((inc S).comp φ) (trP G φ g hg v) hu v' := by
    ext
    show spMap (swap S) ≫ spMap (inc (DualNumber S)) ≫ spMap (dualMap φ) ≫ (tv v').left =
      spMap (dualMap ((inc S).comp φ)) ≫ (tv v').left
    simp only [← Category.assoc, spMap_comp]
    rw [swap_inc_dualMap]
  have hc : Q ≫ vW G ((inc S).comp φ) (trP G φ g hg v') hw v = P' ≫ vW G φ g hg v := by
    ext
    show spMap (swap S) ≫ spMap (dualMap ((inc S).comp φ)) ≫ (tv v).left =
      spMap (inc (DualNumber S)) ≫ spMap (dualMap φ) ≫ (tv v).left
    simp only [← Category.assoc, spMap_comp]
    rw [swap_dualMap_inc]
  have key : gW G (trP G φ g hg v) * vW G ((inc S).comp φ) (trP G φ g hg v) hu v' =
      Q ≫ (gW G (trP G φ g hg v') * vW G ((inc S).comp φ) (trP G φ g hg v') hw v) := by
    rw [MonObj.comp_mul, e1, e2, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, hx, hb, hc, mul_right_comm]
  exact congrArg (fun k => k.left) key

end Swap

end GlobalTheory.InvFieldComm

open GlobalTheory.InvFieldComm in
theorem GlobalTheory.InvFieldComm.invField_comm : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v v' : TanM (𝟙 (Sp R)) G) (dd dd' : Fld G.left), IsInv G v dd → IsInv G v' dd' → ∀ O f, dd O (dd' O f) = dd' O (dd O f) := by
  intro R _ G _ _ v v' dd dd' hv hv' O f
  have key : ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ),
      ⊤ ≤ g ⁻¹ᵁ O → valR g O (dd O (dd' O f)) = valR g O (dd' O (dd O f)) := by
    intro S _ φ g hg hO
    have hw1 := top_le_trP G φ g hg v' O hO
    have hu1 := top_le_trP G φ g hg v O hO
    have hw2 := top_le_trP G _ _ (translateTangent_comp_hom G φ g hg v') v O hw1
    have A1 := hv'.2 S φ g _ O (dd O f) hg hO (isTr_trP G φ g hg v')
    have A2 := hv.2 (DualNumber S) _ _ _ O f (translateTangent_comp_hom G φ g hg v') hw1 (isTr_trP G _ _ (translateTangent_comp_hom G φ g hg v') v)
    have B1 := hv.2 S φ g _ O (dd' O f) hg hO (isTr_trP G φ g hg v)
    have B2 := hv'.2 (DualNumber S) _ _ _ O f (translateTangent_comp_hom G φ g hg v) hu1 (isTr_trP G _ _ (translateTangent_comp_hom G φ g hg v) v')
    rw [← B1, ← B2, swap_trP, valR_spMap_comp _ _ _ hw2, swap_snd_snd, A2, A1]
  have hsub : ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left), g ≫ G.hom = spMap φ →
      ⊤ ≤ g ⁻¹ᵁ O → valR g O (dd O (dd' O f) - dd' O (dd O f)) = 0 := by
    intro S _ φ g hg hO
    rw [valR_eq_evHom g O hO, map_sub, ← valR_eq_evHom g O hO, ← valR_eq_evHom g O hO, key S φ g hg hO, sub_self]
  refine sub_eq_zero.1 (TopCat.Presheaf.section_ext G.left.sheaf O _ 0 fun y hy => ?_)
  have h0 := hsub (G.left.presheaf.stalk y) (Spec.preimage (G.left.fromSpecStalk y ≫ G.hom)).hom
    (G.left.fromSpecStalk y) (Spec.map_preimage _).symm (top_le_fromSpecStalk hy)
  exact ((valR_fromSpecStalk hy _).symm.trans h0).trans (map_zero (G.left.presheaf.germ O y hy).hom).symm
