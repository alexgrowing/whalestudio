import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.IndPf

open LateralTheory.KummerTheory.ContCut

theorem isMV_opens {Y : Scheme.{0}} (U V : Y.Opens) (h : U ⊔ V = ⊤) :
    IsMV (Y.homOfLE inf_le_left) (Y.homOfLE inf_le_right) U.ι V.ι := by
  refine ⟨inferInstance, inferInstance, isPullback_opens_inf U V, fun x => ?_⟩
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  have hx : x ∈ (U ⊔ V) := by rw [h]; trivial
  exact hx

theorem inf_affine {Y : Scheme.{0}} {R : CommRingCat.{0}} (q : Y ⟶ Spec R) [IsSeparated q]
    {V₁ V₂ : Y.Opens} (h1 : IsAffineOpen V₁) (h2 : IsAffineOpen V₂) : IsAffineOpen (V₁ ⊓ V₂) :=
  (isAffineHom_diagonal_iff (f := q)).mp inferInstance ⊤ (isAffineOpen_top _) V₁ (by simp) V₂ (by simp) h1 h2

theorem iSup_fin_succ_eq {Y : Scheme.{0}} {n : ℕ} (V : Fin (n + 1) → Y.Opens) :
    (⨆ i, V i) = (⨆ i : Fin n, V i.castSucc) ⊔ V (Fin.last n) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact le_sup_right
    · exact le_sup_of_le_left (le_iSup (fun j : Fin n => V j.castSucc) j)
  · exact sup_le (iSup_le fun j => le_iSup V j.castSucc) (le_iSup V _)

theorem main (R : CommRingCat.{0}) (P : ∀ X : Scheme.{0}, (X ⟶ Spec R) → Prop)
    (hA : ∀ (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec R), P X p)
    (hM : ∀ {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) (p : X ⟶ Spec R), IsMV a b f g →
      P U (f ≫ p) → P V (g ≫ p) → P W (a ≫ f ≫ p) → P X p) :
    ∀ (n : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Spec R) [IsSeparated q] (V : Fin n → Y.Opens),
      (∀ i, IsAffineOpen (V i)) → (⨆ i, V i) = ⊤ → P Y q := by
  intro n
  induction n with
  | zero =>
    intro Y q _ V _ hV
    have : IsEmpty Y := by
      refine ⟨fun x => ?_⟩
      have hx : x ∈ (⊤ : Y.Opens) := trivial
      rw [← hV] at hx
      obtain ⟨i, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact i.elim0
    have : IsAffine Y := inferInstance
    exact hA Y q
  | succ n ih =>
    intro Y q _ V hA' hV
    set U : Y.Opens := ⨆ i : Fin n, V i.castSucc with hUdef
    set V' : Y.Opens := V (Fin.last n)
    have hUV : U ⊔ V' = ⊤ := by rw [← hV, iSup_fin_succ_eq]
    refine hM _ _ U.ι V'.ι q (isMV_opens U V' hUV) ?_ ?_ ?_
    ·
      refine ih U (U.ι ≫ q) (fun i => U.ι ⁻¹ᵁ V i.castSucc) (fun i => ?_) ?_
      · exact (hA' _).preimage_of_isOpenImmersion U.ι
          (by rw [Scheme.Opens.opensRange_ι]; exact le_iSup (fun j : Fin n => V j.castSucc) i)
      · rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]
    · have : IsAffine V' := hA' (Fin.last n)
      exact hA _ _
    ·
      rw [← Category.assoc, Scheme.homOfLE_ι]
      refine ih _ ((U ⊓ V').ι ≫ q) (fun i => (U ⊓ V').ι ⁻¹ᵁ (V i.castSucc ⊓ V')) (fun i => ?_) ?_
      · exact (inf_affine q (hA' _) (hA' _)).preimage_of_isOpenImmersion _
          (by rw [Scheme.Opens.opensRange_ι]
              exact inf_le_inf_right _ (le_iSup (fun j : Fin n => V j.castSucc) i))
      · rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq, Scheme.Opens.ι_preimage_self]

theorem Ind_of : LateralTheory.KummerTheory.ContCut.Ind := by
  intro R P hA hM X p _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨s, hs, hU⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X)
    (U := Set.univ)).mp ⟨isCompact_univ, isOpen_univ⟩
  have : Finite s := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  refine main R P hA hM n X p (fun i => ((e.symm i : s) : X.affineOpens)) (fun i => (e.symm i : s).1.2) ?_
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  have hx : x ∈ (Set.univ : Set X) := trivial
  rw [hU] at hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e ⟨a, ha⟩, ?_⟩
  simpa using hxa

end LateralTheory.KummerTheory.IndPf
