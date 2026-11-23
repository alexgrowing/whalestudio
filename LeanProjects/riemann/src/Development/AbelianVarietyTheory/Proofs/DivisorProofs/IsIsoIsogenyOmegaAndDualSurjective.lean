import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomSurjectiveIffFinrankKernelQuotientEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConnIsEtSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualIsConnOfIsEtPDivGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEtStatement

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

section Corner

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem comp_proj_eq_of_comp_eq_zero {X Y Y₀ Y₁ : PDivGroup p k} (f : X ⟶ Y) (r₀ : Y ⟶ Y₀)
    (j₀ : Y₀ ⟶ Y) (r₁ : Y ⟶ Y₁) (j₁ : Y₁ ⟶ Y) (hY : r₀ ≫ j₀ + r₁ ≫ j₁ = 𝟙 Y)
    (h : f ≫ r₁ = 0) : f ≫ r₀ ≫ j₀ = f := by
  have h' : f ≫ r₁ ≫ j₁ = 0 := by rw [← Category.assoc, h, Limits.zero_comp]
  calc f ≫ r₀ ≫ j₀ = f ≫ r₀ ≫ j₀ + f ≫ r₁ ≫ j₁ := by rw [h', add_zero]
    _ = f ≫ 𝟙 Y := by rw [← hY, Preadditive.comp_add]
    _ = f := Category.comp_id f

theorem proj_comp_eq_of_comp_eq_zero {X X₀ X₁ Y : PDivGroup p k} (f : X ⟶ Y) (π₀ : X ⟶ X₀)
    (i₀ : X₀ ⟶ X) (π₁ : X ⟶ X₁) (i₁ : X₁ ⟶ X) (hX : π₀ ≫ i₀ + π₁ ≫ i₁ = 𝟙 X)
    (h : i₀ ≫ f = 0) : π₁ ≫ i₁ ≫ f = f := by
  have h' : π₀ ≫ i₀ ≫ f = 0 := by rw [h, Limits.comp_zero]
  calc π₁ ≫ i₁ ≫ f = π₀ ≫ i₀ ≫ f + π₁ ≫ i₁ ≫ f := by rw [h', zero_add]
    _ = 𝟙 X ≫ f := by rw [← hX, Preadditive.add_comp, Category.assoc, Category.assoc]
    _ = f := Category.id_comp f

theorem isIsog_corner {G H G' H' : PDivGroup p k} (q : G ⟶ H) (hq : IsIsog q) (i : G' ⟶ G)
    (π : G ⟶ G') (j : H' ⟶ H) (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hjr : j ≫ r = 𝟙 H')
    (hq' : i ≫ q ≫ r ≫ j = i ≫ q) (hg : ∀ g : H ⟶ G, j ≫ g ≫ π ≫ i = j ≫ g) :
    IsIsog (i ≫ q ≫ r) := by
  obtain ⟨n, g, h1, h2⟩ := hq
  refine ⟨n, j ≫ g ≫ π, ?_, ?_⟩
  · calc (i ≫ q ≫ r) ≫ j ≫ g ≫ π = (i ≫ q ≫ r ≫ j) ≫ g ≫ π := by
          simp only [Category.assoc]
      _ = i ≫ (q ≫ g) ≫ π := by rw [hq']; simp only [Category.assoc]
      _ = _ := by rw [h1, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hiπ]
  · calc (j ≫ g ≫ π) ≫ i ≫ q ≫ r = (j ≫ g ≫ π ≫ i) ≫ q ≫ r := by
          simp only [Category.assoc]
      _ = j ≫ (g ≫ q) ≫ r := by rw [hg g]; simp only [Category.assoc]
      _ = _ := by rw [h2, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hjr]

theorem omegaMap_corner_surjective {G H G' H' : PDivGroup p k} (q : G ⟶ H)
    (hs : Function.Surjective (omegaMap G H q)) (i : G' ⟶ G) (π : G ⟶ G') (j : H' ⟶ H)
    (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hq' : i ≫ q ≫ r ≫ j = i ≫ q) :
    Function.Surjective (omegaMap G' H' (i ≫ q ≫ r)) := by
  intro w
  obtain ⟨v, hv⟩ := hs (omegaMap G G' π w)
  refine ⟨omegaMap H' H j v, ?_⟩
  have e1 : omegaMap G' H' (i ≫ q ≫ r) (omegaMap H' H j v) = omegaMap G' H (i ≫ q) v := by
    rw [← LinearMap.comp_apply, ← omegaMap_comp]
    simp only [Category.assoc]
    rw [hq']
  rw [e1, omegaMap_comp, LinearMap.comp_apply, hv, ← LinearMap.comp_apply, ← omegaMap_comp, hiπ,
    omegaMap_id, LinearMap.id_apply]

theorem isIsog_dualHom_of_isIsog {G H : PDivGroup p k} (f : G ⟶ H) (hf : IsIsog f) :
    IsIsog (dualHom G H f) := by
  obtain ⟨n, g, h1, h2⟩ := hf
  refine ⟨n, dualHom H G g, ?_, ?_⟩
  · rw [← dualHom_comp, h2, map_smul, dualHom_id]
  · rw [← dualHom_comp, h1, map_smul, dualHom_id]

theorem isIso_of_isIso_dualHom {G H : PDivGroup p k} (f : G ⟶ H) (h : IsIso (dualHom G H f)) :
    IsIso f := by
  obtain ⟨d, hd⟩ := (dualHom_bijective (G := H) (H := G)).2 (inv (dualHom G H f))
  refine ⟨⟨d, ?_, ?_⟩⟩
  · apply (dualHom_bijective (G := G) (H := G)).1
    rw [dualHom_comp, hd, IsIso.inv_hom_id, dualHom_id]
  · apply (dualHom_bijective (G := H) (H := H)).1
    rw [dualHom_comp, hd, IsIso.hom_inv_id, dualHom_id]

theorem isIso_of_isConn_of_omegaMap_surjective [CharP k p] {G H : PDivGroup p k} (f : G ⟶ H)
    (hG : G.IsConn) (hf : IsIsog f) (hs : Function.Surjective (omegaMap G H f)) : IsIso f := by
  have hsurj := GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected p k G H f hG hs
  have hdeg : HasLogDeg f 0 := ⟨0, fun n _ => by
    rw [pow_zero]
    exact (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k _ _ _).1 (hsurj n)⟩
  exact ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.2 H f hf).1 hdeg

end Corner

theorem isIso_of_isIsog_of_omegaMap_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q →
    Function.Surjective (omegaMap G H q) →
    Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  intro p _ k _ _ _ G H q hq hs hsd
  obtain ⟨G₀, G₁, i₀, π₀, i₁, π₁, hG₀, hG₁, hi₀, hi₁, hG⟩ := GlobalTheory.T.exists_connected_etale_splitting_pDivGroup p k G
  obtain ⟨H₀, H₁, j₀, r₀, j₁, r₁, hH₀, hH₁, hj₀, hj₁, hH⟩ := GlobalTheory.T.exists_connected_etale_splitting_pDivGroup p k H
  have z : ∀ {X Y : PDivGroup p k}, X.IsConn → Y.IsEt → (∀ f : X ⟶ Y, f = 0) ∧ ∀ f : Y ⟶ X, f = 0 :=
    fun {X Y} hX hY => GlobalTheory.T.hom_eq_zero_of_isConn_of_isEt' p k X Y hX hY

  have c₀ : i₀ ≫ q ≫ r₀ ≫ j₀ = i₀ ≫ q := by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₀ ≫ q) r₀ j₀ r₁ j₁ hH ((z hG₀ hH₁).1 _)
  have c₁ : i₁ ≫ q ≫ r₁ ≫ j₁ = i₁ ≫ q := by
    have hH' : r₁ ≫ j₁ + r₀ ≫ j₀ = 𝟙 H := by rw [add_comm, hH]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₁ ≫ q) r₁ j₁ r₀ j₀ hH' ((z hH₀ hG₁).2 _)
  have g₀ : ∀ g : H ⟶ G, j₀ ≫ g ≫ π₀ ≫ i₀ = j₀ ≫ g := fun g => by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₀ ≫ g) π₀ i₀ π₁ i₁ hG ((z hH₀ hG₁).1 _)
  have g₁ : ∀ g : H ⟶ G, j₁ ≫ g ≫ π₁ ≫ i₁ = j₁ ≫ g := fun g => by
    have hG' : π₁ ≫ i₁ + π₀ ≫ i₀ = 𝟙 G := by rw [add_comm, hG]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₁ ≫ g) π₁ i₁ π₀ i₀ hG' ((z hG₀ hH₁).2 _)

  have ha : IsIso (i₀ ≫ q ≫ r₀) :=
    isIso_of_isConn_of_omegaMap_surjective _ hG₀ (isIsog_corner q hq i₀ π₀ j₀ r₀ hi₀ hj₀ c₀ g₀)
      (omegaMap_corner_surjective q hs i₀ π₀ j₀ r₀ hi₀ c₀)

  have hb : IsIso (i₁ ≫ q ≫ r₁) := by
    apply isIso_of_isIso_dualHom
    have hdb : dualHom G₁ H₁ (i₁ ≫ q ≫ r₁) =
        dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ := by
      rw [dualHom_comp, dualHom_comp, Category.assoc]
    have hrj : dualHom H H₁ r₁ ≫ dualHom H₁ H j₁ = 𝟙 H₁.dual := by
      rw [← dualHom_comp, hj₁, dualHom_id]
    have hq'd : dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ ≫ dualHom G G₁ π₁ =
        dualHom H H₁ r₁ ≫ dualHom G H q := by
      have e : π₁ ≫ i₁ ≫ q ≫ r₁ = q ≫ r₁ :=
        proj_comp_eq_of_comp_eq_zero (q ≫ r₁) π₀ i₀ π₁ i₁ hG
          (by rw [← Category.assoc]; exact (z hG₀ hH₁).1 _)
      have e' := congrArg (dualHom G H₁) e
      simp only [dualHom_comp, Category.assoc] at e'
      exact e'
    have hs' : Function.Surjective (omegaMap H₁.dual G₁.dual (dualHom G₁ H₁ (i₁ ≫ q ≫ r₁))) := by
      rw [hdb]
      exact omegaMap_corner_surjective (dualHom G H q) hsd (dualHom H H₁ r₁) (dualHom H₁ H j₁)
        (dualHom G G₁ π₁) (dualHom G₁ G i₁) hrj hq'd
    exact isIso_of_isConn_of_omegaMap_surjective _ (GlobalTheory.T.dual_isConn_of_isEt_pDivGroup p k H₁ hH₁)
      (isIsog_dualHom_of_isIsog _ (isIsog_corner q hq i₁ π₁ j₁ r₁ hi₁ hj₁ c₁ g₁)) hs'

  have hqd : q = π₀ ≫ (i₀ ≫ q ≫ r₀) ≫ j₀ + π₁ ≫ (i₁ ≫ q ≫ r₁) ≫ j₁ := by
    simp only [Category.assoc, c₀, c₁]
    rw [← Category.assoc π₀, ← Category.assoc π₁, ← Preadditive.add_comp, hG, Category.id_comp]
  have hj01 : j₀ ≫ r₁ = 0 := (z hH₀ hH₁).1 _
  have hj10 : j₁ ≫ r₀ = 0 := (z hH₀ hH₁).2 _
  have hi01 : i₀ ≫ π₁ = 0 := (z hG₀ hG₁).1 _
  have hi10 : i₁ ≫ π₀ = 0 := (z hG₀ hG₁).2 _
  generalize i₀ ≫ q ≫ r₀ = a at ha hqd
  generalize i₁ ≫ q ≫ r₁ = b at hb hqd
  subst hqd
  refine ⟨⟨r₀ ≫ inv a ≫ i₀ + r₁ ≫ inv b ≫ i₁, ?_, ?_⟩⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hj₀,
      reassoc_of% hj₁, reassoc_of% hj01, reassoc_of% hj10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.hom_inv_id_assoc]
    exact hG
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hi₀,
      reassoc_of% hi₁, reassoc_of% hi01, reassoc_of% hi10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.inv_hom_id_assoc]
    exact hH

end GlobalTheory.Dieu
