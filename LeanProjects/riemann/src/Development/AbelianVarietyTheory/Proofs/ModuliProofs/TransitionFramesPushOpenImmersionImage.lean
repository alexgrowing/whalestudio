import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionPowerTransportCartesianSquareStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ModelSum

theorem appIso_inv_topIso_inv {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (hle : W ≤ f ''ᵁ W') (v : W'.toScheme ⟶ W.toScheme) (hv : v ≫ W.ι = W'.ι ≫ f) :
    (f.appIso W').inv ≫ Z.presheaf.map (homOfLE hle).op ≫ W.topIso.inv ≫ v.appTop = W'.topIso.inv := by
  have e : W.topIso.inv = W.ι.appLE W ⊤ (by simp) := (Scheme.Opens.ι_appLE W W ⊤ _).symm
  have e' : W'.topIso.inv = W'.ι.appLE W' ⊤ (by simp) := (Scheme.Opens.ι_appLE W' W' ⊤ _).symm
  have e₂ : v.appTop = v.appLE ⊤ ⊤ (le_top (a := ⊤) |>.trans (Scheme.Hom.preimage_top v).ge) := (Scheme.Hom.appLE_eq_app v).symm
  rw [Iso.inv_comp_eq, Scheme.Hom.appIso_hom', e, e', e₂, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.map_appLE]
  simp only [hv]

theorem exists_iso_image {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (h : W = f ''ᵁ W') : ∃ v : W'.toScheme ≅ W.toScheme, v.hom ≫ W.ι = W'.ι ≫ f := by
  subst h
  exact ⟨f.isoImage W', Scheme.Hom.isoImage_hom_ι f W'⟩

theorem appTop_hom_inv {X Y : Scheme.{0}} (v : X ≅ Y) (a : Γ(X, ⊤)) :
    v.hom.appTop.hom (v.inv.appTop.hom a) = a := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, v.hom_inv_id, Scheme.Hom.id_appTop]; rfl

theorem appTop_inv_hom {X Y : Scheme.{0}} (v : X ≅ Y) (a : Γ(Y, ⊤)) :
    v.inv.appTop.hom (v.hom.appTop.hom a) = a := appTop_hom_inv v.symm a

theorem exists_transport {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hφ : IsPullback φ G'.hom G.hom f)
    (hw : LBIso L' (L.pull φ)) (N : ℕ) :
    ∃ e : ∀ {X' X : Scheme.{0}} (a' : X' ⟶ Z') (a : X ⟶ Z) (u : X' ≅ X), u.hom ≫ a = a' ≫ f →
      LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a')) → LB.Sec (Out.LPow G L (N : ℤ) (Over.mk a)),
    (∀ {X₁' X₂' X₁ X₂ : Scheme.{0}} {a₁' : X₁' ⟶ Z'} {a₂' : X₂' ⟶ Z'} {a₁ : X₁ ⟶ Z} {a₂ : X₂ ⟶ Z}
      (u₁ : X₁' ≅ X₁) (u₂ : X₂' ≅ X₂) (h₁ : u₁.hom ≫ a₁ = a₁' ≫ f) (h₂ : u₂.hom ≫ a₂ = a₂' ≫ f)
      (k' : X₂' ⟶ X₁') (k : X₂ ⟶ X₁) (hk' : k' ≫ a₁' = a₂') (hk : k ≫ a₁ = a₂), k' ≫ u₁.hom = u₂.hom ≫ k →
      ∀ (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₁'))) (c' : Fin n → Γ(X₂', ⊤))
        (c : Fin n → Γ(X₂, ⊤)), (∀ i, u₂.hom.appTop.hom (c i) = c' i) →
        ∀ s : LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₂')),
        Lin G' L' N (Over.homMk k' hk' : Over.mk a₂' ⟶ Over.mk a₁') b c' s →
          Lin G L N (Over.homMk k hk : Over.mk a₂ ⟶ Over.mk a₁) (fun i => e a₁' a₁ u₁ h₁ (b i)) c (e a₂' a₂ u₂ h₂ s)) ∧
    ∀ {X₁' X₁ Y : Scheme.{0}} {a₁' : X₁' ⟶ Z'} {a₁ : X₁ ⟶ Z} (u₁ : X₁' ≅ X₁) (h₁ : u₁.hom ≫ a₁ = a₁' ≫ f)
      (χ : Y ⟶ X₁) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₁'))),
      BasisAlong G' L' N (Over.homMk (χ ≫ u₁.inv) rfl : Over.mk ((χ ≫ u₁.inv) ≫ a₁') ⟶ Over.mk a₁') b →
        BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ a₁) ⟶ Over.mk a₁) (fun i => e a₁' a₁ u₁ h₁ (b i)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_sectionPower_transport_cartesian_square Z Z' G G' f φ L L' hL hL' hφ hw N
  refine ⟨fun a' a u h => e (Over.mk a') (Over.mk a) u h, ?_, ?_⟩
  · intro X₁' X₂' X₁ X₂ a₁' a₂' a₁ a₂ u₁ u₂ h₁ h₂ k' k hk' hk hc n b c' c hcc s H
    obtain rfl : c' = fun i => u₂.hom.appTop.hom (c i) := funext fun i => (hcc i).symm
    exact (he (Over.mk a₁') (Over.mk a₂') (Over.mk a₁) (Over.mk a₂) u₁ u₂ h₁ h₂ (Over.homMk k' hk') (Over.homMk k hk)
      hc n b c s).1 H
  · intro X₁' X₁ Y a₁' a₁ u₁ h₁ χ n b B σ
    have hc' : (Iso.refl Y).hom ≫ χ ≫ a₁ = ((χ ≫ u₁.inv) ≫ a₁') ≫ f := by
      simp [← h₁]
    have hk : (χ ≫ u₁.inv) ≫ u₁.hom = (Iso.refl Y).hom ≫ χ := by simp
    have hid : ∀ a : Γ(Y, ⊤), (Iso.refl Y).hom.appTop.hom a = a := fun a => by simp
    obtain ⟨σ', rfl⟩ := (e (Over.mk ((χ ≫ u₁.inv) ≫ a₁')) (Over.mk (χ ≫ a₁)) (Iso.refl Y) hc').surjective σ
    refine (existsUnique_congr fun c => ?_).1 (B σ')
    refine Iff.trans ?_ (he (Over.mk a₁') (Over.mk ((χ ≫ u₁.inv) ≫ a₁')) (Over.mk a₁)
      (Over.mk (χ ≫ a₁)) u₁ (Iso.refl Y) h₁ hc' (Over.homMk (χ ≫ u₁.inv) rfl) (Over.homMk χ rfl) hk n b c σ')
    exact iff_of_eq (congrArg (fun c => Lin G' L' N _ b c σ') (funext fun k => (hid (c k)).symm))

theorem unit_rel_push {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (hle : W ≤ f ''ᵁ W') (v : W'.toScheme ≅ W.toScheme) (hv : v.hom ≫ W.ι = W'.ι ≫ f) {n : ℕ} (r s : ℤ)
    (g : Γ(Z', W')) (c : Γ(W'.toScheme, ⊤)ˣ) (M : GL (Fin n) Γ(W'.toScheme, ⊤))
    (hg : W'.topIso.inv.hom g = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val) :
    W.topIso.inv.hom ((Z.presheaf.map (homOfLE hle).op).hom ((f.appIso W').inv.hom g)) =
      (Units.map v.inv.appTop.hom.toMonoidHom c ^ r *
        Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map v.inv.appTop.hom M) ^ s).val := by
  have E : v.hom.appTop.hom (W.topIso.inv.hom ((Z.presheaf.map (homOfLE hle).op).hom ((f.appIso W').inv.hom g))) =
      W'.topIso.inv.hom g := congrArg (fun k => k.hom g) (appIso_inv_topIso_inv f W' W hle v.hom hv)
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map v.inv.appTop.hom M) =
      Units.map v.inv.appTop.hom.toMonoidHom (Matrix.GeneralLinearGroup.det M) :=
    Units.ext (RingHom.map_det v.inv.appTop.hom M.val).symm
  rw [hd, ← map_zpow, ← map_zpow, ← map_mul]
  exact (appTop_inv_hom v _).symm.trans (congrArg v.inv.appTop.hom (E.trans hg))

theorem hasFrames_pushLB : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) [IsOpenImmersion f] (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → f ⁻¹' abLocus G ⊆ abLocus G' → ∀ (N : ℕ) (A : LB Z') (n : ℕ) (r s : ℤ), HasFrames G' L' N A n r s → HasFrames G L N (pushLB f A) n r s := by
  intro Z Z' G G' f _ φ L L' hL hL' hφ hw hab N A n r s ⟨th, b, h₁, h₂⟩
  obtain ⟨e₁, he₁, hb₁⟩ := exists_transport hL hL' hφ hw 1
  obtain ⟨eN, heN, hbN⟩ := exists_transport hL hL' hφ hw N
  choose u hu using fun i : A.ι => exists_iso_image f (A.U i) (f ''ᵁ A.U i) rfl
  refine ⟨fun i => e₁ (A.U i).ι (f ''ᵁ A.U i).ι (u i) (hu i) (th i),
    fun i k => eN (A.U i).ι (f ''ᵁ A.U i).ι (u i) (hu i) (b i k), fun (i j : A.ι) => ?_,
    fun (i : A.ι) W _ _ _ hW (χ : Sp W ⟶ (f ''ᵁ A.U i).toScheme) hχ => ?_⟩
  · obtain ⟨c, M, ⟨t, ht, ht'⟩, hb, hg⟩ := h₁ i j
    obtain ⟨v, hv⟩ := exists_iso_image f (A.U i ⊓ A.U j) (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j)
      (le_antisymm (image_inf_le f _ _) (le_inf (f.image_mono inf_le_left) (f.image_mono inf_le_right)))
    have ki : Z'.homOfLE (inf_le_left : A.U i ⊓ A.U j ≤ A.U i) ≫ (u i).hom =
        v.hom ≫ Z.homOfLE (inf_le_left : f ''ᵁ A.U i ⊓ f ''ᵁ A.U j ≤ _) := by
      rw [← cancel_mono (f ''ᵁ A.U i).ι, Category.assoc, Category.assoc, hu, Scheme.homOfLE_ι, hv, Scheme.homOfLE_ι_assoc]
    have kj : Z'.homOfLE (inf_le_right : A.U i ⊓ A.U j ≤ A.U j) ≫ (u j).hom =
        v.hom ≫ Z.homOfLE (inf_le_right : f ''ᵁ A.U i ⊓ f ''ᵁ A.U j ≤ _) := by
      rw [← cancel_mono (f ''ᵁ A.U j).ι, Category.assoc, Category.assoc, hu, Scheme.homOfLE_ι, hv, Scheme.homOfLE_ι_assoc]
    refine ⟨Units.map v.inv.appTop.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map v.inv.appTop.hom M,
      ⟨e₁ (A.U i ⊓ A.U j).ι (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j).ι v hv t, ?_, ?_⟩, fun k => ?_, ?_⟩
    · exact he₁ (u i) v (hu i) hv _ _ _ (Scheme.homOfLE_ι _ _) ki 1 (fun _ => th i) (fun _ => 1) (fun _ => 1)
        (fun _ => map_one _) t ht
    · exact he₁ (u j) v (hu j) hv _ _ _ (Scheme.homOfLE_ι _ _) kj 1 (fun _ => th j) (fun _ => c.val)
        (fun _ => v.inv.appTop.hom c.val) (fun _ => appTop_hom_inv v _) t ht'
    · obtain ⟨t, ht, ht'⟩ := hb k
      refine ⟨eN (A.U i ⊓ A.U j).ι (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j).ι v hv t, ?_, ?_⟩
      · exact heN (u i) v (hu i) hv _ _ _ (Scheme.homOfLE_ι _ _) ki 1 (fun _ => b i k) (fun _ => 1) (fun _ => 1)
          (fun _ => map_one _) t ht
      · exact heN (u j) v (hu j) hv _ _ _ (Scheme.homOfLE_ι _ _) kj n (b j) (fun k' => M.val k k')
          (fun k' => v.inv.appTop.hom (M.val k k')) (fun _ => appTop_hom_inv v _) t ht'
    · exact unit_rel_push f (A.U i ⊓ A.U j) _ (image_inf_le f _ _) v hv r s _ c M hg
  · have hc : ((Out.jK W ≫ (χ ≫ (u i).inv) ≫ (A.U i).ι) ≫ f) = Out.jK W ≫ χ ≫ (f ''ᵁ A.U i).ι := by
      simp only [Category.assoc]; rw [← hu i, Iso.inv_hom_id_assoc]
    obtain ⟨B₁, BN⟩ := h₂ i W hW (χ ≫ (u i).inv) (by
      rintro _ ⟨x, rfl⟩
      refine hab (hχ ⟨x, ?_⟩)
      exact (congrArg (fun k => k x) hc).symm.trans (Scheme.Hom.comp_apply _ _ _))
    exact ⟨hb₁ (u i) (hu i) χ 1 (fun _ => th i) B₁, hbN (u i) (hu i) χ n (b i) BN⟩

end GlobalTheory.ModelSum

end
