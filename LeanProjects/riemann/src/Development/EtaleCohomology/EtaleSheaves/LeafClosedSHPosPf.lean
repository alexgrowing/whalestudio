import Development.EtaleCohomology.EtaleSheaves.LeafVanBPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial IsLocalRing GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafClosedSHPosPf

theorem hens_of_surj {A B : Type} [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B]
    (φ : A →+* B) (hφ : Function.Surjective φ) : HenselianLocalRing B := by
  have := IsLocalHom.of_surjective φ hφ
  have : IsLocalRing B := IsLocalRing.of_surjective φ hφ
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  have hl : f ∈ Polynomial.lifts φ := (Polynomial.lifts_iff_coeff_lifts f).2 (fun n => hφ _)
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hf
  obtain ⟨b₀, rfl⟩ := hφ a₀
  have hev : ∀ (p : A[X]) (x : A), (p.map φ).eval (φ x) = φ (p.eval x) := fun p x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  subst hg
  have h1 : g.eval b₀ ∈ maximalIdeal A := by
    rw [hev] at h₁
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 h₁ (hu.map φ))
  have h2 : IsUnit (g.derivative.eval b₀) := by
    rw [derivative_map, hev] at h₂
    exact IsUnit.of_map φ _ h₂
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian g hgm b₀ h1 h2
  refine ⟨φ a, ?_, ?_⟩
  · rw [IsRoot, hev, ha.eq_zero, map_zero]
  · rw [← map_sub]
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 ham (IsUnit.of_map φ _ hu))

theorem sepClosed_of_surj {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ) [IsSepClosed (ResidueField A)] :
    IsSepClosed (ResidueField B) := by
  have hs : Function.Surjective (ResidueField.map φ) := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨residue A a, ResidueField.map_residue φ a⟩
  let e : ResidueField A ≃+* ResidueField B :=
    RingEquiv.ofBijective (ResidueField.map φ) ⟨(ResidueField.map φ).injective, hs⟩
  refine ⟨fun p hp => ?_⟩
  have h1 : (p.map (e.symm : ResidueField B →+* ResidueField A)).Separable := hp.map
  have h2 := (IsSepClosed.splits_of_separable _ h1).map (e : ResidueField A →+* ResidueField B)
  rw [Polynomial.map_map] at h2
  convert h2
  ext x; simp

theorem sub_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) (R : Type) [CommRing R] (F : Shv R) (n : ℤ)
    (h : Subsingleton (H R (sch.obj Y) F n)) : Subsingleton (H R (sch.obj X) F n) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : H R (sch.obj X) F n,
      z = pull R (sch.map e.hom) F n (pull R (sch.map e.inv) F n z) := by
    intro z
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key x, key y, Subsingleton.elim (pull R (sch.map e.inv) F n x) (pull R (sch.map e.inv) F n y)]

theorem sub_of_empty (hy : Hyps) (R : Type) [CommRing R] (F : Shv R) (W : Scheme.{0}) [IsEmpty W] (n : ℤ)
    (hn : 0 < n) : Subsingleton (H R (sch.obj W) F n) := by
  have a5 : A5 := hy.2.2.2.2.1
  suffices h : ∀ x : H R (sch.obj W) F n, x = 0 from ⟨fun a b => by rw [h a, h b]⟩
  intro x
  obtain ⟨Z, f, -, -, hf⟩ := a5 R W F n hn x
  have : IsEmpty Z := ⟨fun z => isEmptyElim (f.base z)⟩
  let g : W ⟶ Z := (isInitialOfIsEmpty (X := W)).to Z
  have hgf : g ≫ f = 𝟙 W := (isInitialOfIsEmpty (X := W)).hom_ext _ _
  have : pull R (sch.map (g ≫ f)) F n x = x := by rw [hgf, CategoryTheory.Functor.map_id, pull_id]
  rw [← this, CategoryTheory.Functor.map_comp, pull_comp, hf, map_zero]

theorem LeafClosedSHPos_of : LateralTheory.E.LeafVanBPf.LeafClosedSHPos := by
  intro hy q _ i A _ _ hA hq W' ι' _ n hn
  rcases isEmpty_or_nonempty W' with hW | ⟨⟨w⟩⟩
  · exact sub_of_empty hy _ _ W' n hn
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let B : Type := Γ(W', ⊤)
  let ψ : A →+* B := (ι'.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : Function.Surjective ψ := hsurj.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have : Nontrivial B := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    let p := W'.isoSpec.hom.base w
    exact p.isPrime.ne_top (Subsingleton.elim _ _)
  obtain ⟨hH, hS⟩ := hA
  have := IsLocalHom.of_surjective ψ hψ
  have hHB : HenselianLocalRing B := hens_of_surj ψ hψ
  have hSB : SH B := ⟨hHB, sepClosed_of_surj ψ hψ⟩
  have h2 := LateralTheory.E.LeafVanBPf.heightFunctionalStatement_of_pairingProperties hy (ZMod q) B hSB (tw q i) n hn
  exact sub_of_iso W'.isoSpec (ZMod q) (tw q i) n h2

end LateralTheory.E.LeafClosedSHPosPf
