import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic

namespace GlobalTheory.CechPic.Glue

def extUnit {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (V : W.Opens) : Γ(W, V)ˣ →* Γ(X, g ''ᵁ V)ˣ :=
  Units.map (g.appIso V).inv.hom.toMonoidHom

theorem gm_extUnit {X W T : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (V : W.Opens) (a : Γ(W, V)ˣ)
    (r : T ⟶ W) (t : T) (ht : r t ∈ V) : gm (r ≫ g) t (g ''ᵁ V) (extUnit g V a) = gm r t V a := by
  have hm : r t ∈ g ⁻¹ᵁ (g ''ᵁ V) := ⟨r t, ht, rfl⟩
  have e : pullU g (g ''ᵁ V) (extUnit g V a) = res (g.preimage_image_eq V).le a :=
    Units.ext (congrArg (fun q => q.hom a.val) (g.appIso_inv_app V))
  rw [← gm_pull r g t _ hm, e, gm_res r t _ hm]

theorem image_inf_le {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (A B : W.Opens) :
    g ''ᵁ A ⊓ g ''ᵁ B ≤ g ''ᵁ (A ⊓ B) := by
  rintro _ ⟨⟨a, ha, rfl⟩, hb⟩
  exact ⟨a, ⟨ha, (g.apply_mem_image_iff).1 hb⟩, rfl⟩

variable {Y : Scheme.{0}} {κ : Type} {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)]
  (L : ∀ i, LB (Z i))

def gT (i : κ) (k k' : (L i).ι) : Γ(Y, (f i) ''ᵁ (L i).U k ⊓ (f i) ''ᵁ (L i).U k')ˣ :=
  res (image_inf_le (f i) _ _) (extUnit (f i) _ ((L i).g k k'))

open Classical in

def gS : ∀ p q : (Σ i, (L i).ι),
    Γ(Y, (f p.1) ''ᵁ (L p.1).U p.2 ⊓ (f q.1) ''ᵁ (L q.1).U q.2)ˣ
  | ⟨i, k⟩, ⟨i', k'⟩ => if h : i = i' then by subst h; exact gT f L i k k' else 1

def glueLB : LB Y where
  ι := Σ i, (L i).ι
  U p := (f p.1) ''ᵁ (L p.1).U p.2
  g := gS f L

theorem glueLB_g (i : κ) (k k' : (L i).ι) : (glueLB f L).g ⟨i, k⟩ ⟨i, k'⟩ = gT f L i k k' := by
  show gS f L ⟨i, k⟩ ⟨i, k'⟩ = _
  simp [gS]

theorem gm_glueLB {T : Scheme.{0}} (i : κ) (r : T ⟶ Z i) (t : T) (k k' : (L i).ι) (hk : r t ∈ (L i).U k)
    (hk' : r t ∈ (L i).U k') :
    gm (r ≫ f i) t ((glueLB f L).U ⟨i, k⟩ ⊓ (glueLB f L).U ⟨i, k'⟩) ((glueLB f L).g ⟨i, k⟩ ⟨i, k'⟩) =
      gm r t ((L i).U k ⊓ (L i).U k') ((L i).g k k') := by
  rw [glueLB_g]
  have hm : (r ≫ f i) t ∈ (f i) ''ᵁ (L i).U k ⊓ (f i) ''ᵁ (L i).U k' :=
    ⟨(f i).apply_mem_image_iff.2 hk, (f i).apply_mem_image_iff.2 hk'⟩
  exact (gm_res _ t _ hm _).trans (gm_extUnit (f i) _ _ r t ⟨hk, hk'⟩)

theorem mem_image {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] {A : W.Opens} {y : X} (h : y ∈ g ''ᵁ A) :
    ∃ z ∈ A, g z = y := h

theorem same_of_mem {i i' : κ} (hd : Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) {y : Y}
    (h : y ∈ (f i).opensRange) (h' : y ∈ (f i').opensRange) : i = i' := by
  by_contra hne
  exact (hd hne).le_bot ⟨h, h'⟩

variable {L} in
theorem isLB_glueLB (hL : ∀ i, (L i).IsLB) (hcov : ⨆ i, (f i).opensRange = ⊤)
    (hd : Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) : (glueLB f L).IsLB where
  cover := by
    refine top_le_iff.1 fun y _ => ?_
    have hy : y ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    obtain ⟨i, z, rfl⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨k, hk⟩ := exists_chart (hL i) z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, k⟩, (f i).apply_mem_image_iff.2 hk⟩
  g_self := by
    rintro ⟨i, k⟩
    refine unit_ext fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := mem_image (f i) hy
    refine gm_inj (f i) z hy hy ?_
    have e := gm_glueLB f L i (𝟙 _) z k k hz hz
    rw [Category.id_comp] at e
    rw [map_one, gm_res _ z _ hy, e, gm_self (hL i) _ z hz]
  cocycle := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ ⟨i'', k''⟩
    refine unit_ext fun y hy => ?_
    have h1 : y ∈ (f i).opensRange := (f i).image_le_opensRange _ hy.1.1
    have h2 : y ∈ (f i').opensRange := (f i').image_le_opensRange _ hy.1.2
    have h3 : y ∈ (f i'').opensRange := (f i'').image_le_opensRange _ hy.2
    obtain rfl := same_of_mem f hd h1 h2
    obtain rfl := same_of_mem f hd h1 h3
    obtain ⟨z, hz, rfl⟩ := mem_image (f i) hy.1.1
    have hz' : z ∈ (L i).U k' := (f i).apply_mem_image_iff.1 hy.1.2
    have hz'' : z ∈ (L i).U k'' := (f i).apply_mem_image_iff.1 hy.2
    refine gm_inj (f i) z hy hy ?_
    have e1 := gm_glueLB f L i (𝟙 _) z k k' hz hz'
    have e2 := gm_glueLB f L i (𝟙 _) z k' k'' hz' hz''
    have e3 := gm_glueLB f L i (𝟙 _) z k k'' hz hz''
    rw [Category.id_comp] at e1 e2 e3
    rw [map_mul, gm_res _ z _ hy, gm_res _ z _ hy, gm_res _ z _ hy, e1, e2, e3,
      gm_cocycle (hL i) _ z hz hz' hz'']

theorem exists_pic_glue : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y)
    [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) →
    (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) →
    ∀ c : ∀ i, Pic (Z i), ∃ d : Pic Y, ∀ i, GlobalTheory.CechPic.pull (f i) d = c i := by
  intro Y κ _ Z f _ hcov hd c
  choose L hL hc using fun i => cls_surj (c i)
  have hG := isLB_glueLB f hL hcov hd
  refine ⟨cls (glueLB f L) hG, fun i => ?_⟩
  rw [← cls_pull hG (f i) (pull_isLB hG (f i)), ← hc i]
  refine Eq.symm ((cls_eq_iff (hL i) (pull_isLB hG (f i))).2 (iso_of_chart (pull_isLB hG (f i)) ?_))
  exact
    { idx := fun k _ => ⟨i, k⟩
      le := fun k z hz => mem_pull.2 ((f i).apply_mem_image_iff.2 hz)
      g := fun z k k' hk hk' => Eq.symm ((gm_pull_g (glueLB f L) (f i) (𝟙 _) z (fun _ => ⟨i, k⟩) (fun _ => ⟨i, k'⟩)
        (mem_pull.2 ((f i).apply_mem_image_iff.2 hk)) (mem_pull.2 ((f i).apply_mem_image_iff.2 hk'))).trans
        (gm_glueLB f L i (𝟙 _) z k k' hk hk')) }

end GlobalTheory.CechPic.Glue
