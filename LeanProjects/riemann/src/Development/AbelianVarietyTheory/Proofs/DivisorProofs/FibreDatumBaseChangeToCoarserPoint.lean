import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsTrans

theorem exists_refactor {X X₁ X₂ A : Scheme.{0}} {L : LB X} {M : LB A} (hL : L.IsLB) (hM : M.IsLB)
    {F₁ : X₁ ⟶ X} {F₂ : X₂ ⟶ X} {φ₁ : A ⟶ X₁} {φ₂ : A ⟶ X₂} (e : φ₁ ≫ F₁ = φ₂ ≫ F₂)
    (w₂ : LB.Iso M ((L.pull F₂).pull φ₂)) (hw₂ : PGen w₂) :
    ∃ w₁ : LB.Iso M ((L.pull F₁).pull φ₁), PGen w₁ ∧
      (∀ (z : A) (J : PUnit → L.ι) (k : M.ι), F₁ (φ₁ z) ∈ L.U (J PUnit.unit) → z ∈ M.U k →
        gw w₁ (𝟙 A) z J k = gw w₂ (𝟙 A) z J k) ∧
      ∀ {Y Y₁ Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₁ : Y₁ ⟶ X₁} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₁ : Y₁ ⟶ Y} {h₂ : Y₂ ⟶ Y}
        {g₁ : B ⟶ Y₁} {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₁ : LB.Gen (LB.LinComb (L.pull F₁) (fun _ : PUnit => u₁) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₁ = g₁ ≫ u₁ → v ≫ φ₂ = g₂ ≫ u₂ → g₁ ≫ h₁ = g₂ ≫ h₂ →
        PMaps (L := L) (F := F₁) (idIso (L.pull F₁)) (fun _ : PUnit => u₁) (fun _ => u) (fun _ => 1) t₁ t h₁ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w₁ (fun _ : PUnit => v) (fun _ => u₁) (fun _ => 1) a t₁ g₁ := by
  have hL₁ : (L.pull F₁).IsLB := LB.isLB_pull hL _
  have hL₂ : (L.pull F₂).IsLB := LB.isLB_pull hL _
  have p₁ := (isGen_iff (L := L) (F := F₁) (idIso _)).1 (idIso_isGen hL₁)
  have p₂ := (isGen_iff (L := L) (F := F₂) (idIso _)).1 (idIso_isGen hL₂)
  obtain ⟨w, T₂⟩ := exists_comp hL₂ (idIso (L.pull F₂)) w₂ p₂ hw₂ hL hM
  have pw := T₂.pgen_comp hL₂ p₂ hw₂
  have a₂ : ∀ (z : A) (J : PUnit → L.ι) (k : M.ι), (φ₂ ≫ F₂) z ∈ L.U (J PUnit.unit) → z ∈ M.U k →
      gw w (𝟙 A) z (J PUnit.unit) k = gw w₂ (𝟙 A) z J k := fun z J k hj hk => by
    have hJ : (𝟙 A ≫ φ₂) z ∈ (L.pull F₂).U J := mem_pull.2 hj
    rw [T₂ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₂) (idIso (L.pull F₂)) (𝟙 A ≫ φ₂) z (J PUnit.unit) J = 1 := gm_self hL₂ _ z hJ
    rw [this, _root_.one_mul]
  have b₂ : ∀ {Y Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₂ : Y₂ ⟶ Y}
        {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₂ = g₂ ≫ u₂ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w (fun _ : PUnit => v) (fun _ => u) (fun _ => 1) a t (g₂ ≫ h₂) :=
    fun t t₂ a hc H H' => T₂.pmaps_comp hL₂ (fun _ => hc) H H'
  clear T₂
  generalize φ₂ ≫ F₂ = H at e w pw a₂ b₂
  subst e
  obtain ⟨w₁, T₁⟩ := exists_cancel hL (idIso (L.pull F₁)) w p₁ pw hL₁ hM
  refine ⟨w₁, T₁.pgen_cancel hL p₁ pw, fun z J k hj hk => ?_, ?_⟩
  · have hJ : (𝟙 A ≫ φ₁) z ∈ (L.pull F₁).U J := mem_pull.2 hj
    rw [← a₂ z J k hj hk, T₁ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₁) (idIso (L.pull F₁)) (𝟙 A ≫ φ₁) z (J PUnit.unit) J = 1 := gm_self hL₁ _ z hJ
    rw [this, _root_.one_mul]
  · intro Y Y₁ Y₂ B u u₁ u₂ v h₁ h₂ g₁ g₂ t t₁ t₂ a c₁ c₂ c H₁ H₂ H
    exact T₁.pmaps_cancel hL (fun _ => c₁) H₁ (c ▸ b₂ t t₂ a c₂ H₂ H)

theorem gs_locSec {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {δ : LB S}
    {σ : (CechPic.tens L.L (δ.pull G.hom)).Sec} {i : δ.ι} {R : Type} [CommRing R] {ξ : Sp R ⟶ S}
    {t : (KeyVals.bL L ξ).L.Sec} (hξ : ⊤ ≤ ξ ⁻¹ᵁ δ.U i) (ht : KeyVals.IsLocSec σ i ξ t) {Z : Scheme.{0}}
    (q : Z ⟶ (KeyVals.bG G ξ).left) (z : Z) (J : (KeyVals.bL L ξ).L.ι) (hJ : q z ∈ (KeyVals.bL L ξ).L.U J) :
    gs q z _ (t.f J) = gs (q ≫ pullback.fst G.hom ξ) z _ (σ.f (J PUnit.unit, fun _ => i)) := by
  have hle : (KeyVals.bL L ξ).L.U J ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (J PUnit.unit, fun _ => i) := by
    intro p hp
    refine ⟨mem_pull.1 hp, mem_pull.2 ?_⟩
    have e := congrArg (fun g => g p) (pullback.condition (f := G.hom) (g := ξ))
    have h2 : ξ (pullback.snd G.hom ξ p) ∈ δ.U i := hξ (show pullback.snd G.hom ξ p ∈ (⊤ : (Sp R).Opens) from trivial)
    exact e.symm ▸ h2
  rw [ht J hle]
  exact gs_appLE _ _ _ hle q z hJ _

theorem pmaps_bL {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (ξ : Sp R ⟶ S) : PMaps (L := L.L) (F := pullback.fst G.hom ξ) (idIso (L.L.pull (pullback.fst G.hom ξ))) (K := PUnit)
      (fun _ => eSec (KeyVals.bG G ξ)) (fun _ => eSec G) (fun _ => 1) (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) :=
  (maps_iff _ _ _ _ (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) (KeyVals.bL L ξ).rig
    (rigPull_le (G' := KeyVals.bG G ξ) (pullback.fst G.hom ξ) (KeyVals.eb ξ) (KeyVals.eSec_bG G ξ) L.L)
    (fun _ => rfl)).1 (idIso_maps (KeyVals.bL L ξ))

theorem keyOn_trans : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R R' K : Type) [CommRing R]
    [CommRing R'] [CommRing K] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (f : R' →+* K)
    (t : (KeyVals.bL L ξ).L.Sec) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ)) (t' : (KeyVals.bL L ξ').L.Sec)
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')) (x : KeyIn K) (hg : x.P.g = g),
    spMap r ≫ ξ = ξ' → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → KeyVals.IsLocSec σ i ξ' t' →
    (∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ) →
    KeyOn f x (KeyVals.bG G ξ') (KeyVals.bL L ξ') t' (fun j => y' (j.cast hg)) →
    KeyOn (f.comp r) x (KeyVals.bG G ξ) (KeyVals.bL L ξ) t (fun j => y (j.cast hg)) := by
  intro S G _ _ g L δ σ i R R' K _ _ _ ξ r ξ' f t y t' y' x hg hξ hU ht ht' hy hK
  obtain ⟨φ', he', ψ', F', hφ', hψ', hrig', hsec', hF1, hF2, hFv⟩ := hK
  have hU' : ⊤ ≤ ξ' ⁻¹ᵁ δ.U i := by
    intro p _
    rw [← hξ]
    exact hU (show spMap r p ∈ (⊤ : (Sp R).Opens) from trivial)
  have hP := isGrpPullback_pullback G ξ
  have hP' := isGrpPullback_pullback G ξ'
  obtain ⟨m, hm, hfst, hsnd⟩ : ∃ m : (KeyVals.bG G ξ').left ⟶ (KeyVals.bG G ξ).left,
      IsGrpPullback (KeyVals.bG G ξ') (KeyVals.bG G ξ) (spMap r) m ∧ m ≫ pullback.fst G.hom ξ = pullback.fst G.hom ξ' ∧
        m ≫ (KeyVals.bG G ξ).hom = (KeyVals.bG G ξ').hom ≫ spMap r := by
    have sq : pullback.fst G.hom ξ' ≫ G.hom = (pullback.snd G.hom ξ' ≫ spMap r) ≫ ξ := by
      rw [Category.assoc, hξ]; exact pullback.condition
    refine ⟨pullback.lift _ _ sq, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    refine IsGrpPullback.cancel hP ?_ (pullback.lift_snd _ _ _)
    rw [pullback.lift_fst, hξ]
    exact hP'
  have hφ : IsGrpPullback x.P.A (KeyVals.bG G ξ) (spMap (f.comp r)) (φ' ≫ m) := by
    rw [spMap_comp]
    exact IsGrpPullback.comp hφ' hm
  have he : eSec x.P.A ≫ φ' ≫ m = spMap (f.comp r) ≫ eSec (KeyVals.bG G ξ) := PolBaseChange.eSec_comm hφ
  have e : (φ' ≫ m) ≫ pullback.fst G.hom ξ = φ' ≫ pullback.fst G.hom ξ' := by rw [Category.assoc, hfst]
  obtain ⟨ψ, pψ, hgw, hmap⟩ := exists_refactor L.isLB x.P.isLB e ψ' ((isGen_iff ψ').1 hψ')
  have H' : PMaps ψ' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec (KeyVals.bG G ξ')) (fun _ => 1) x.rig
      (KeyVals.bL L ξ').rig (spMap f) :=
    (maps_iff ψ' _ _ _ x.rig (KeyVals.bL L ξ').rig (spMap f) _
      (rigPull_le (G' := x.P.A) φ' (spMap f) he' (KeyVals.bL L ξ').L) (fun _ => rfl)).1 hrig'
  have c : spMap (f.comp r) ≫ ξ = spMap f ≫ ξ' := by rw [spMap_comp, Category.assoc, hξ]
  have H := hmap L.rig (KeyVals.bL L ξ).rig (KeyVals.bL L ξ').rig x.rig he he' c (pmaps_bL L ξ) (pmaps_bL L ξ') H'
  have hD1 : ∀ a, Chart.dualMapR r (algebraMap R _ a) = algebraMap R' _ (r a) := fun a => by
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have hD2 : Chart.dualMapR r DualNumber.eps = DualNumber.eps := by
    ext <;> simp [Chart.dualMapR]
  refine ⟨φ' ≫ m, he, ψ, F'.comp (Chart.dualMapR r), hφ, (isGen_iff ψ).2 pψ,
    (maps_iff ψ _ _ _ x.rig (KeyVals.bL L ξ).rig (spMap (f.comp r)) _
      (rigPull_le (G' := x.P.A) (φ' ≫ m) (spMap (f.comp r)) he (KeyVals.bL L ξ).L) (fun _ => rfl)).2 H,
    ?_, fun a => ?_, ?_, fun j => ?_⟩
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk ψ t x.th ?_
    intro z J k hJ hk
    have ha : ((φ' ≫ m) ≫ pullback.fst G.hom ξ) z ∈ L.L.U (J PUnit.unit) :=
      (mem_pull (F := pullback.fst G.hom ξ)).1 hJ
    have ha' : (φ' ≫ pullback.fst G.hom ξ') z ∈ L.L.U (J PUnit.unit) := e ▸ ha
    have hJ' : φ' z ∈ (KeyVals.bL L ξ').L.U J := (mem_pull (F := pullback.fst G.hom ξ')).2 ha'
    have hW : (𝟙 x.P.A.left) z ∈ ((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k := ⟨mem_pull.2 hJ', hk⟩
    have s2 : gs (𝟙 _ ≫ φ') z _ (t'.f J) = (gw ψ' (𝟙 _) z J k).val * gs (𝟙 _) z _ (x.th.f k) := by
      have e0 := congrArg (gs (𝟙 _) z (((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k))
        (hsec' (fun _ => J) k (fun x hx => mem_pull.1 hx.1))
      exact (gs_appLE φ' _ _ _ (𝟙 _) z hW _).symm.trans (e0.trans ((gs_mul _ z _ hW _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hW _) (gs_res _ z _ hW _))))
    have e1 := gs_locSec hU ht (𝟙 _ ≫ φ' ≫ m) z J hJ
    have e2 := gs_locSec hU' ht' (𝟙 _ ≫ φ') z J hJ'
    have e3 : (𝟙 _ ≫ φ' ≫ m) ≫ pullback.fst G.hom ξ = (𝟙 _ ≫ φ') ≫ pullback.fst G.hom ξ' := by
      rw [Category.id_comp, Category.id_comp, e]
    rw [e3] at e1
    exact e1.trans (e2.symm.trans (s2.trans (congrArg (fun u : _ˣ => u.val * _) (hgw z J k ha hk).symm)))
  · rw [RingHom.comp_apply, hD1, hF1]; rfl
  · rw [RingHom.comp_apply, hD2, hF2]
  · have hv : (y' (j.cast hg)).left ≫ m = spMap (Chart.dualMapR r) ≫ (y (j.cast hg)).left := by
      refine hP.1.hom_ext ?_ ?_
      · rw [Category.assoc, hfst, Category.assoc]
        exact hy _ hD1 hD2 _
      · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (y' _), Category.assoc, Over.w (y _)]
        show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact RingHom.ext fun a => (hD1 a).symm
    rw [← Category.assoc, hFv j, Category.assoc, hv, spMap_comp, Category.assoc]

end GlobalTheory.KeyValsTrans

end
