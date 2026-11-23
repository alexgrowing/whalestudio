import Development.EtaleCohomology.CohomologicalPurity.LeafDescPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

theorem sres_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res f (Sec.res g x) = Sec.res (f ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sres_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (f : V ⟶ U) :
    Sec.res (F := F) f 0 = 0 := map_zero ((F.obj.map f.op).hom)

theorem smap_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero ((φ.hom.app (op U)).hom)

theorem smap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (f : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res f x) = Sec.res f (Sec.map φ x) := by
  have := congrArg (fun h => h.hom x) (φ.hom.naturality f.op)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this

theorem le_comp' {Y Z X : Scheme.{0}} {W : Y.Opens} (f : Y ⟶ Z) (g : Z ⟶ X) (U : X.Opens) (k : Y ⟶ X)
    (hk : f ≫ g = k) (hW : W ≤ k ⁻¹ᵁ U) : W ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  subst hk; intro w hw; exact hW hw

theorem zc_res {R : Type} [CommRing R] {K : Cx R} {n : ℤ} {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens)
    (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) (a : Sec (K.X n) X) (ha : a ∈ Zc K U n) : Sec.res f a ∈ Zc K U' n := by
  rw [mem_Zc] at ha ⊢
  refine ⟨?_, ?_⟩
  · rw [sres_comp, ← Scheme.Hom.resLE_comp_ι f h, ← sres_comp, ha.1, sres_zero]
  · rw [smap_res, ha.2, sres_zero]

theorem res_inj (q : ℕ) (i : ℤ) : ∀ s, Injective ((res _ (tw q i)).X s) := fun s => by
  unfold res; infer_instance

theorem res_neg (q : ℕ) (i : ℤ) : ∀ s < 0, IsZero ((res _ (tw q i)).X s) := fun s hs => by
  unfold res; exact CochainComplex.isZero_of_isStrictlyGE _ 0 s hs

theorem LeafDescOSep_of : LeafDescOSep := by
  intro hD hF q X U m i hL s hs
  have h1 : ∀ n < m, ∀ (W : X.Opens), ∀ a ∈ Zc (res _ (tw q i)) (W.ι ⁻¹ᵁ U) n, ∀ x ∈ W,
      ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n (rs h a) := by
    intro n hn W a ha x hx
    obtain ⟨V, hVW, hxV, hV⟩ := hL x W hx
    obtain ⟨cls, -, hker, -⟩ := hD q n i
    have hz : rs hVW a ∈ Zc (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n :=
      zc_res _ _ _ (le_comp' _ _ U _ (Scheme.homOfLE_ι _ _) le_rfl) a ha
    refine ⟨V, hVW, hxV, (hker _ ⟨_, hz⟩).1 ?_⟩
    have := hV n hn
    exact Subsingleton.elim _ _
  obtain ⟨cls, hsurj, hker, hnat⟩ := hD q m i
  obtain ⟨a, rfl⟩ := hsurj U s
  have hFl := (hF _ (res _ (tw q i)) (res_inj q i) (res_neg q i) X U m h1).1
  have hza' : Sec.res (⊤ : X.Opens).ι a.1 ∈ Zc (res _ (tw q i)) ((⊤ : X.Opens).ι ⁻¹ᵁ U) m :=
    zc_res _ _ _ le_rfl a.1 a.2
  have hB : Bd (res _ (tw q i)) ((⊤ : X.Opens).ι ⁻¹ᵁ U) m (Sec.res (⊤ : X.Opens).ι a.1) := by
    apply hFl ⊤
    intro x _
    by_cases hxU : x ∈ U
    · refine ⟨U, le_top, hxU, ⟨0, sres_zero _, ?_⟩⟩
      have e : rs (le_top : U ≤ ⊤) (Sec.res (⊤ : X.Opens).ι a.1) = 0 := by
        unfold rs; rw [sres_comp, Scheme.homOfLE_ι]; exact a.2.1
      rw [e]; exact smap_zero _
    · obtain ⟨V, hxV, hV0⟩ := hs x hxU
      refine ⟨V, le_top, hxV, ?_⟩
      have e : rs (le_top : V ≤ ⊤) (Sec.res (⊤ : X.Opens).ι a.1) = Sec.res V.ι a.1 := by
        unfold rs; rw [sres_comp, Scheme.homOfLE_ι]
      have hz : Sec.res V.ι a.1 ∈ Zc (res _ (tw q i)) (V.ι ⁻¹ᵁ U) m := zc_res _ _ _ le_rfl a.1 a.2
      rw [e]
      refine (hker _ (⟨_, hz⟩ : Zc _ _ _)).1 ?_
      rw [← hnat V.ι (V.ι ⁻¹ᵁ U) U le_rfl a ⟨_, hz⟩ rfl]
      exact hV0
  have h0 := (hker _ (⟨_, hza'⟩ : Zc _ _ _)).2 hB
  rw [← hnat (⊤ : X.Opens).ι _ U le_rfl a ⟨_, hza'⟩ rfl] at h0
  have hle : U ≤ X.topIso.inv ⁻¹ᵁ ((⊤ : X.Opens).ι ⁻¹ᵁ U) :=
    le_comp' _ _ U (𝟙 X) (Scheme.toIso_inv_ι X) (fun x hx => hx)
  have hid : U ≤ (𝟙 X) ⁻¹ᵁ U := fun x hx => hx
  have key := pull_pull X.topIso.inv (⊤ : X.Opens).ι (Scheme.toIso_inv_ι X) U _ U hle le_rfl hid m i (cls U a)
  rw [h0, map_zero, Hs_pull_id] at key
  exact key.symm

end LateralTheory.CohomologicalPurity.Cl
