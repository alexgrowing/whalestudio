import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobou
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogChernCocycleContractionInvariantFieldTriviali
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSLin

open GlobalTheory.Points (valR_eq valMap valR_add valR_mul valR_res valR_appLE le_preimage_mono le_preimage_comp)

theorem exists_sec {Z : Scheme.{0}} (O : Z.Opens) (F : ∀ (S : Type) [CommRing S], (Sp S ⟶ Z) → S)
    (hF : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ρ : S →+* S') (x : Sp S ⟶ Z), ⊤ ≤ x ⁻¹ᵁ O →
      F S' (spMap ρ ≫ x) = ρ (F S x)) :
    ∃ f : Γ(Z, O), ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Z), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = F S x := by
  obtain ⟨f, hf⟩ := GlobalTheory.CechKS.exists_sec_of_isNat ℤ Z (specZIsTerminal.from Z) Unit (fun _ => O) O
    (fun _ => le_rfl) (le_iSup (fun _ : Unit => O) ()) (fun P => F P.B P.x) (fun _ P Q φ hP => by
      have := hF P.B Q.B φ.ρ P.x hP
      rw [φ.pt] at this
      exact this)
  exact ⟨f, fun S _ x hx => (hf () ⟨S, x, specZIsTerminal.hom_ext _ _⟩ hx).symm⟩

theorem isField_mono {Z : Scheme.{0}} {W W' : Z.Opens} (h : W' ≤ W) {d : Fld Z} (hd : IsField W d) :
    IsField W' d :=
  ⟨fun O hO => hd.1 O (hO.trans h), fun O hO => hd.2.1 O (hO.trans h), fun O O' e hO => hd.2.2 O O' e (hO.trans h)⟩

theorem isField_add {Z : Scheme.{0}} {W : Z.Opens} {d d' : Fld Z} (hd : IsField W d) (hd' : IsField W d') :
    IsField W (fun O f => d O f + d' O f) :=
  ⟨fun O hO f f' => by simp only [hd.1 O hO, hd'.1 O hO]; ring,
    fun O hO f f' => by simp only [hd.2.1 O hO, hd'.2.1 O hO]; ring,
    fun O O' e hO f => by simp only [hd.2.2 O O' e hO, hd'.2.2 O O' e hO, map_add]⟩

theorem isField_sum {Z : Scheme.{0}} {W : Z.Opens} {I : Type} [Fintype I] {d : I → Fld Z}
    (hd : ∀ a, IsField W (d a)) : IsField W (fun O f => ∑ a, d a O f) :=
  ⟨fun O hO f f' => by simp only [fun a => (hd a).1 O hO, Finset.sum_add_distrib],
    fun O hO f f' => by simp only [fun a => (hd a).2.1 O hO, Finset.sum_add_distrib, Finset.mul_sum],
    fun O O' e hO f => by simp only [fun a => (hd a).2.2 O O' e hO, map_sum]⟩

open Classical in

def smulFld {Z : Scheme.{0}} {W : Z.Opens} (c : Γ(Z, W)) (d : Fld Z) : Fld Z :=
  fun O f => if h : O ≤ W then resG Z h c * d O f else 0

theorem smulFld_of_le {Z : Scheme.{0}} {W O : Z.Opens} (h : O ≤ W) (c : Γ(Z, W)) (d : Fld Z) (f : Γ(Z, O)) :
    smulFld c d O f = resG Z h c * d O f := dif_pos h

theorem isField_smul {Z : Scheme.{0}} {W : Z.Opens} (c : Γ(Z, W)) {d : Fld Z} (hd : IsField W d) :
    IsField W (smulFld c d) := by
  refine ⟨fun O hO f f' => ?_, fun O hO f f' => ?_, fun O O' e hO f => ?_⟩
  · simp only [smulFld_of_le hO, hd.1 O hO]; ring
  · simp only [smulFld_of_le hO, hd.2.1 O hO]; ring
  · rw [smulFld_of_le hO, smulFld_of_le (e.trans hO), hd.2.2 O O' e hO, map_mul]
    congr 1
    exact congrArg (fun k => k.hom c) (Z.presheaf.map_comp (homOfLE hO).op (homOfLE e).op)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}

section Translate

variable {R S : Type} [CommRing R] [CommRing S] {φ : R →+* S} {g : Sp S ⟶ t.G.left}
  {v : Sp (DualNumber R) ⟶ t.G.left} {w : Sp (DualNumber S) ⟶ t.G.left}

theorem translate_over (h : IsTranslate t φ g v w) :
    w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g ≫ t.G.hom := by
  obtain ⟨g', v', -, -, rfl⟩ := h
  exact Over.w (g' * v')

theorem translate_red {x : Sp R ⟶ X} (hv : IsTanAtG t x v) (hg : g ≫ t.G.hom = spMap φ ≫ x)
    (h : IsTranslate t φ g v w) : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := h
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', ← Spec.map_id]
    congr 1
  let s : Over.mk (g ≫ t.G.hom) ⟶ tEpsG (g ≫ t.G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      change _ ≫ _ ≫ _ = g ≫ t.G.hom
      rw [← Category.assoc, e, Category.id_comp])
  let k : Over.mk (g ≫ t.G.hom) ⟶ Over.mk x := Over.homMk (spMap φ) hg.symm
  have h1 : s ≫ v' = 1 := by
    rw [← MonObj.comp_one k]
    refine Over.OverMorphism.ext ?_
    change spMap _ ≫ v'.left = spMap φ ≫ (1 : Over.mk x ⟶ t.G).left
    rw [h₂, ← hv.2, ← Category.assoc, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp']
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  change (s ≫ (g' * v')).left = g
  rw [MonObj.comp_mul, h1, _root_.mul_one]
  change spMap _ ≫ g'.left = g
  rw [h₁, ← Category.assoc, e, Category.id_comp]

theorem translate_map (h : IsTranslate t φ g v w) {S' : Type} [CommRing S'] (ρ : S →+* S') :
    IsTranslate t (ρ.comp φ) (spMap ρ ≫ g) v (spMap (dualMap ρ) ≫ w) := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := h
  have e : spMap (dualMap ρ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ρ := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp']
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : tEpsG ((spMap ρ ≫ g) ≫ t.G.hom) ⟶ tEpsG (g ≫ t.G.hom) := Over.homMk (spMap (dualMap ρ)) (by
    change _ ≫ _ ≫ _ = _ ≫ (_ ≫ _) ≫ _
    rw [← Category.assoc, e]
    simp only [Category.assoc])
  refine ⟨k ≫ g', k ≫ v', ?_, ?_, ?_⟩
  · change spMap _ ≫ g'.left = _
    rw [h₁, ← Category.assoc, e, Category.assoc]
  · change spMap _ ≫ v'.left = _
    rw [h₂, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.dualMap_comp']
  · rw [← MonObj.comp_mul]
    rfl

end Translate

theorem valR_base (U : X.affineOpens) {O : t.G.left.Opens} (h : O ≤ t.G.hom ⁻¹ᵁ U.1) {S : Type} [CommRing S]
    {φ : Γ(X, U.1) →+* S} {g : Sp S ⟶ t.G.left} (hg : g ≫ t.G.hom = spMap φ ≫ chart U) (hO : ⊤ ≤ g ⁻¹ᵁ O)
    (r : Γ(X, U.1)) : valR g O ((t.G.hom.appLE U.1 O h).hom r) = φ r := by
  rw [valR_appLE g _ h hO, hg]
  exact (valR_eq _ _ (GlobalTheory.Points.le_preimage_specMap_fromSpec U.2 (CommRingCat.ofHom φ)) r).trans
    (congrArg (fun k => k.hom r) (GlobalTheory.Points.valMap_specMap_fromSpec U.2 (CommRingCat.ofHom φ) _))

theorem exists_translate (U : X.affineOpens) {v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left}
    (hv : IsTanAtG t (chart U) v) {S : Type} [CommRing S] (g : Sp S ⟶ t.G.left) (h : ⊤ ≤ g ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1)) :
    ∃ (φ : Γ(X, U.1) →+* S) (w : Sp (DualNumber S) ⟶ t.G.left),
      g ≫ t.G.hom = spMap φ ≫ chart U ∧ IsTranslate t φ g v w := by
  have hg : g ≫ t.G.hom = spMap (valMap (g ≫ t.G.hom) U.1 h).hom ≫ chart U :=
    (GlobalTheory.Points.specMap_valMap_fromSpec U.2 (g ≫ t.G.hom) h).symm
  obtain ⟨w, hw, -⟩ := existsUnique_isTranslate t _ hg hv
  exact ⟨_, w, hg, hw⟩

theorem translate_unique (U : X.affineOpens) {v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left}
    (hv : IsTanAtG t (chart U) v) {S : Type} [CommRing S] {g : Sp S ⟶ t.G.left} {φ φ' : Γ(X, U.1) →+* S}
    {w w' : Sp (DualNumber S) ⟶ t.G.left} (hg : g ≫ t.G.hom = spMap φ ≫ chart U)
    (hg' : g ≫ t.G.hom = spMap φ' ≫ chart U) (hw : IsTranslate t φ g v w) (hw' : IsTranslate t φ' g v w') :
    w = w' := by
  have hO : ⊤ ≤ g ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    change ⊤ ≤ (g ≫ t.G.hom) ⁻¹ᵁ U.1
    rw [hg]
    exact GlobalTheory.Points.le_preimage_specMap_fromSpec U.2 (CommRingCat.ofHom φ)
  obtain rfl : φ = φ' := RingHom.ext fun r => (valR_base U le_rfl hg hO r).symm.trans (valR_base U le_rfl hg' hO r)
  exact (existsUnique_isTranslate t φ hg hv).unique hw hw'

theorem exists_invField (U : X.affineOpens) {v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left}
    (hv : IsTanAtG t (chart U) v) :
    ∃ dd : Fld t.G.left, IsField (t.G.hom ⁻¹ᵁ U.1) dd ∧
      (∀ (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), dd O ((t.G.hom.appLE U.1 O h).hom r) = 0) ∧
      ∀ (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S]
        (φ : Γ(X, U.1) →+* S) (g : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left),
        g ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g ⁻¹ᵁ O → IsTranslate t φ g v w →
        valR g O (dd O f) = (valR w O f).snd := by
  classical
  let tr : ∀ (S : Type) [CommRing S], (Sp S ⟶ t.G.left) → (Sp (DualNumber S) ⟶ t.G.left) := fun S _ g =>
    if h : ⊤ ≤ g ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) then (exists_translate U hv g h).choose_spec.choose
    else spMap (algebraMap S (DualNumber S)) ≫ g
  have htr : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left), ⊤ ≤ g ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) →
      ∃ φ : Γ(X, U.1) →+* S, g ≫ t.G.hom = spMap φ ≫ chart U ∧ IsTranslate t φ g v (tr S g) := by
    intro S _ g h
    simp only [tr, dif_pos h]
    exact ⟨_, (exists_translate U hv g h).choose_spec.choose_spec⟩
  have hex : ∀ (O : t.G.left.Opens) (f : Γ(t.G.left, O)), ∃ s : Γ(t.G.left, O), O ≤ t.G.hom ⁻¹ᵁ U.1 →
      ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left), ⊤ ≤ g ⁻¹ᵁ O → valR g O s = (valR (tr S g) O f).snd := by
    intro O f
    by_cases hO : O ≤ t.G.hom ⁻¹ᵁ U.1
    · obtain ⟨s, hs⟩ := exists_sec O (fun S _ g => (valR (tr S g) O f).snd) (fun S S' _ _ ρ g hg => by
        obtain ⟨φ, h₁, h₂⟩ := htr S g (le_preimage_mono g hO hg)
        obtain ⟨φ', h₁', h₂'⟩ := htr S' (spMap ρ ≫ g) (fun p _ => hO (hg (Set.mem_univ (spMap ρ p))))
        have h₃ : (spMap ρ ≫ g) ≫ t.G.hom = spMap (ρ.comp φ) ≫ chart U := by
          rw [Category.assoc, h₁, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
        rw [translate_unique U hv h₁' h₃ h₂' (translate_map h₂ ρ), GlobalTheory.Points.valR_spMap_comp _ _ _
          (GlobalTheory.CechKS.le_preimage_of_red (translate_red hv h₁ h₂) hg)]
        simp [dualMap])
      exact ⟨s, fun _ => hs⟩
    · exact ⟨0, fun h => (hO h).elim⟩
  choose dd hdd using hex
  have hin : ∀ (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left),
      ⊤ ≤ g ⁻¹ᵁ O → ⊤ ≤ tr S g ⁻¹ᵁ O ∧ ∀ f, (valR (tr S g) O f).fst = valR g O f := by
    intro O hO S _ g hg
    obtain ⟨φ, h₁, h₂⟩ := htr S g (le_preimage_mono g hO hg)
    have hr := translate_red hv h₁ h₂
    have hw := GlobalTheory.CechKS.le_preimage_of_red hr hg
    refine ⟨hw, fun f => ?_⟩
    have e := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom S S S).toRingHom _ O hw f
    rw [hr] at e
    exact e.symm
  refine ⟨dd, ⟨fun O hO f f' => ?_, fun O hO f f' => ?_, fun O O' e hO f => ?_⟩, fun O hO r => ?_,
    fun O hO f S _ φ g w hg hgO hw => ?_⟩
  · refine GlobalTheory.CechInv.ext_of_valR O _ _ fun S _ g hg => ?_
    rw [valR_add _ _ hg, hdd O _ hO S g hg, hdd O _ hO S g hg, hdd O _ hO S g hg, valR_add _ _ (hin O hO S g hg).1,
      TrivSqZeroExt.snd_add]
  · refine GlobalTheory.CechInv.ext_of_valR O _ _ fun S _ g hg => ?_
    rw [valR_add _ _ hg, valR_mul _ _ hg, valR_mul _ _ hg, hdd O _ hO S g hg, hdd O _ hO S g hg, hdd O _ hO S g hg,
      valR_mul _ _ (hin O hO S g hg).1, DualNumber.snd_mul, (hin O hO S g hg).2, (hin O hO S g hg).2]
    ring
  · refine GlobalTheory.CechInv.ext_of_valR O' _ _ fun S _ g hg => ?_
    rw [valR_res _ e hg, hdd O' _ (e.trans hO) S g hg, hdd O _ hO S g (le_preimage_mono g e hg),
      valR_res _ e (hin O' (e.trans hO) S g hg).1]
  · refine GlobalTheory.CechInv.ext_of_valR O _ _ fun S _ g hg => ?_
    obtain ⟨φ, h₁, h₂⟩ := htr S g (le_preimage_mono g hO hg)
    rw [hdd O _ hO S g hg, GlobalTheory.Points.valR_zero _ _ hg, valR_appLE _ _ hO (hin O hO S g hg).1, translate_over h₂,
      GlobalTheory.Points.valR_spMap_comp _ _ _ (le_preimage_comp g _ hO hg)]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  · obtain ⟨φ', h₁, h₂⟩ := htr S g (le_preimage_mono g hO hgO)
    rw [hdd O _ hO S g hgO, translate_unique U hv h₁ hg h₂ hw]

theorem dlog_four {Z : Scheme.{0}} (L : LB Z) (hL : L.IsLB) {S : Type} [CommRing S] {g : Sp S ⟶ Z}
    {w : Sp (DualNumber S) ⟶ Z} (hw : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g) (a b a' b' : L.1)
    (ha : ⊤ ≤ g ⁻¹ᵁ L.U a) (hb : ⊤ ≤ g ⁻¹ᵁ L.U b) (ha' : ⊤ ≤ g ⁻¹ᵁ L.U a') (hb' : ⊤ ≤ g ⁻¹ᵁ L.U b') :
    (valR w _ (L.g a a').val).snd * valR g _ (L.g a a')⁻¹.val =
      (valR w _ (L.g b b').val).snd * valR g _ (L.g b b')⁻¹.val +
        ((valR w _ (L.g a b).val).snd * valR g _ (L.g a b)⁻¹.val -
          (valR w _ (L.g a' b').val).snd * valR g _ (L.g a' b')⁻¹.val) := by
  have h2 : ∀ {p q : L.1}, ⊤ ≤ g ⁻¹ᵁ L.U p → ⊤ ≤ g ⁻¹ᵁ L.U q → ⊤ ≤ g ⁻¹ᵁ (L.U p ⊓ L.U q) :=
    fun h h' _ hx => ⟨h hx, h' hx⟩
  have h3 : ∀ {p q s : L.1}, ⊤ ≤ g ⁻¹ᵁ L.U p → ⊤ ≤ g ⁻¹ᵁ L.U q → ⊤ ≤ g ⁻¹ᵁ L.U s →
      ⊤ ≤ w ⁻¹ᵁ (L.U p ⊓ L.U q ⊓ L.U s) :=
    fun h h' h'' => GlobalTheory.CechKS.le_preimage_of_red hw fun _ hx => ⟨⟨h hx, h' hx⟩, h'' hx⟩
  refine GlobalTheory.CechKS.dlog_of_mul_eq _ _ _ _ _ _ _ _ ?_ (GlobalTheory.CechKS.valR_fst_mul_inv hw (h2 ha hb) _)
    (GlobalTheory.CechKS.valR_fst_mul_inv hw (h2 ha' hb') _) (GlobalTheory.CechKS.valR_fst_mul_inv hw (h2 hb hb') _)
    (GlobalTheory.CechKS.valR_fst_mul_inv hw (h2 ha ha') _)
  rw [GlobalTheory.CechKS.PrismDlog.valR_cocycle L hL w a b b' (h3 ha hb hb'),
    GlobalTheory.CechKS.PrismDlog.valR_cocycle L hL w a a' b' (h3 ha ha' hb')]

theorem resG_appLE (U : X.affineOpens) {O O' : t.G.left.Opens} (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (e : O' ≤ O)
    (r : Γ(X, U.1)) :
    resG t.G.left e ((t.G.hom.appLE U.1 O h).hom r) = (t.G.hom.appLE U.1 O' (e.trans h)).hom r :=
  congrArg (fun k => k.hom r) (t.G.hom.appLE_map h (homOfLE e).op)

variable {V : X.Opens} {U : X.affineOpens} {n : ℕ} {v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)}
  {D D' : Γ(X, U.1) → Γ(X, U.1)} {Θ Θ' : Matrix (Fin n) (Fin n) Γ(X, U.1)}

theorem isKS_smul (h : IsKS t V U v D Θ) (r : Γ(X, U.1)) : IsKS t V U v (fun s => r * D s) (r • Θ) := by
  obtain ⟨J, W, j, d, hcov, hWj, hF, hD, hc⟩ := h
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup W i).trans (hcov.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, W, j, fun i => smulFld ((t.G.hom.appLE U.1 (W i) (hWU i)).hom r) (d i), hcov, hWj,
    fun i => isField_smul _ (hF i), fun i h s => ?_, fun i i' O hO f S _ φ g w hg hgO hw => ?_⟩
  · beta_reduce
    rw [smulFld_of_le le_rfl, resG_appLE, hD, map_mul]
  · beta_reduce
    rw [smulFld_of_le (hO.trans inf_le_left), smulFld_of_le (hO.trans inf_le_right), resG_appLE, resG_appLE,
      ← mul_sub, valR_mul _ _ hgO, valR_base U _ hg hgO, hc i i' O hO f S φ g w hg hgO hw]
    simp only [Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, map_mul, _root_.mul_assoc]

theorem isKS_add (hv : ∀ a, IsTanAtG t (chart U) (v a)) (h : IsKS t V U v D Θ) (h' : IsKS t V U v D' Θ') :
    IsKS t V U v (fun s => D s + D' s) (Θ + Θ') := by
  obtain ⟨J, W, j, d, hcov, hWj, hF, hD, hc⟩ := h
  obtain ⟨J', W', j', d', hcov', hWj', hF', hD', hc'⟩ := h'
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup W i).trans (hcov.le.trans (t.G.hom.preimage_mono inf_le_left))
  have hWU' : ∀ i, W' i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup W' i).trans (hcov'.le.trans (t.G.hom.preimage_mono inf_le_left))
  choose dd hdF hd0 hdv using fun a => exists_invField U (hv a)
  let Wp : J × J' → t.G.left.Opens := fun p => W p.1 ⊓ W' p.2
  have hpU : ∀ p, Wp p ≤ t.G.hom ⁻¹ᵁ U.1 := fun p => inf_le_left.trans (hWU p.1)
  have hpL : ∀ p, Wp p ≤ t.PP.L.U (j p.1) ⊓ t.PP.L.U (j' p.2) := fun p => inf_le_inf (hWj p.1) (hWj' p.2)
  let cf : ∀ p, Fin n → Γ(t.G.left, Wp p) := fun p a => ∑ b, (t.G.hom.appLE U.1 (Wp p) (hpU p)).hom (Θ' a b) *
    (dd b _ (resG _ (hpL p) (t.PP.L.g (j p.1) (j' p.2)).val) * resG _ (hpL p) (t.PP.L.g (j p.1) (j' p.2))⁻¹.val)
  refine ⟨J × J', Wp, fun p => j p.1,
    fun p O f => (d p.1 O f + d' p.2 O f) + ∑ a, smulFld (cf p a) (dd a) O f, ?_,
    fun p => inf_le_left.trans (hWj p.1),
    fun p => isField_add (isField_add (isField_mono inf_le_left (hF p.1)) (isField_mono inf_le_right (hF' p.2)))
      (isField_sum fun a => isField_smul _ (isField_mono (hpU p) (hdF a))), fun p h s => ?_,
    fun p q O hO f S _ φ g w hg hgO hw => ?_⟩
  · rw [iSup_prod]
    simp only [Wp]
    simp only [← inf_iSup_eq, ← iSup_inf_eq, hcov, hcov', inf_idem]
  · beta_reduce
    simp only [smulFld_of_le le_rfl, hd0, mul_zero, Finset.sum_const_zero, add_zero, map_add]
    congr 1
    · rw [← resG_appLE U (hWU p.1) (inf_le_left : Wp p ≤ W p.1), (hF p.1).2.2 _ _ _ le_rfl, hD, resG_appLE]
    · rw [← resG_appLE U (hWU' p.2) (inf_le_right : Wp p ≤ W' p.2), (hF' p.2).2.2 _ _ _ le_rfl, hD', resG_appLE]
  · have hp : O ≤ Wp p := hO.trans inf_le_left
    have hq : O ≤ Wp q := hO.trans inf_le_right
    have hred := fun a => translate_red (hv a) hg (hw a)
    have hcf : ∀ r, O ≤ Wp r → valR g O (∑ a, smulFld (cf r a) (dd a) O f) = ∑ a, ∑ b, φ (Θ' a b) *
        ((valR (w b) _ (t.PP.L.g (j r.1) (j' r.2)).val).snd * valR g _ (t.PP.L.g (j r.1) (j' r.2))⁻¹.val) *
        (valR (w a) O f).snd := by
      intro r hr
      have hgr := le_preimage_mono g hr hgO
      rw [valR_eq _ _ hgO, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← valR_eq _ _ hgO, smulFld_of_le hr, valR_mul _ _ hgO, valR_res _ hr hgO,
        hdv a O (hr.trans (hpU r)) f S φ g (w a) hg hgO (hw a), ← Finset.sum_mul, valR_eq _ _ hgr, map_sum]
      refine congrArg (· * _) (Finset.sum_congr rfl fun b _ => ?_)
      rw [← valR_eq _ _ hgr, valR_mul _ _ hgr, valR_mul _ _ hgr, valR_base U _ hg hgr, valR_res _ _ hgr,
        hdv b _ (hpU r) _ S φ g (w b) hg hgr (hw b),
        valR_res _ _ (GlobalTheory.CechKS.le_preimage_of_red (hred b) hgr)]
    have e₁ := hc p.1 q.1 O (le_inf (hp.trans inf_le_left) (hq.trans inf_le_left)) f S φ g w hg hgO hw
    have e₂ := hc' p.2 q.2 O (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right)) f S φ g w hg hgO hw
    have e₃ := fun b => dlog_four t.PP.L t.PP.isLB (hred b) (j p.1) (j' p.2) (j q.1) (j' q.2)
      (le_preimage_mono g ((hp.trans (hpL p)).trans inf_le_left) hgO)
      (le_preimage_mono g ((hp.trans (hpL p)).trans inf_le_right) hgO)
      (le_preimage_mono g ((hq.trans (hpL q)).trans inf_le_left) hgO)
      (le_preimage_mono g ((hq.trans (hpL q)).trans inf_le_right) hgO)
    beta_reduce
    rw [show d p.1 O f + d' p.2 O f + ∑ a, smulFld (cf p a) (dd a) O f -
        (d q.1 O f + d' q.2 O f + ∑ a, smulFld (cf q a) (dd a) O f) = (d p.1 O f - d q.1 O f) +
        (d' p.2 O f - d' q.2 O f) + (∑ a, smulFld (cf p a) (dd a) O f - ∑ a, smulFld (cf q a) (dd a) O f) by ring,
      valR_add _ _ hgO, valR_add _ _ hgO, e₁, e₂, GlobalTheory.CechInv.valR_sub _ _ hgO, hcf p hp, hcf q hq]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.add_apply, map_add]
    linear_combination (-(φ (Θ' a b) * (valR (w a) O f).snd)) * e₃ b

theorem isKS_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D D' : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (r : Γ(Y.X, U.1)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), IsKS Y.t (interior Y) U v D.1 Θ → IsKS Y.t (interior Y) U v D'.1 Θ' → IsKS Y.t (interior Y) U v (D + D').1 (Θ + Θ') ∧ IsKS Y.t (interior Y) U v (r • D).1 (r • Θ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ r _ _ h h' => ⟨isKS_add hv h h', isKS_smul h r⟩

end GlobalTheory.LogKSLin
