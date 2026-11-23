import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

namespace UpperTheory.Gal.Int.Geo.Cut

private theorem multiset_map_pts {J P Q : Type} [Fintype J] {I : J → Type} [∀ j, Fintype (I j)] (a : J → ℕ)
    (v : (j : J) → I j → P) (g : P → Q) :
    Multiset.map g (crystallineComparison.pts a v) = crystallineComparison.pts a (fun j i => g (v j i)) := by
  simp only [crystallineComparison.pts]
  rw [show Multiset.map g = Multiset.mapAddMonoidHom g from rfl, map_sum]
  simp [Multiset.map_nsmul, Multiset.map_map]

private theorem identity_of_comp_injective_semiconj_image (q n : ℕ) {P Q : Type} (F' : P → P) (F : Q → Q) (g : P → Q)
    (hg : Function.Injective g) (hc : Function.Semiconj g F' F) {I : Fin (n + 1) → Type}
    [∀ j, Fintype (I j)] (v : (j : Fin (n + 1)) → I j → P)
    (h : crystallineComparison.AltId q n F (fun j i => g (v j i))) : crystallineComparison.AltId q n F' v := by
  unfold crystallineComparison.AltId at *
  apply Multiset.map_injective hg
  have e : ∀ (k : ℕ) (x : P), F^[k] (g x) = g (F'^[k] x) := fun k x => ((hc.iterate_right k) x).symm
  simp only [e] at h
  rw [multiset_map_pts, multiset_map_pts]
  exact h

private theorem genPt_openImmersion_of_genPt_appTop {Y' Y : Scheme} (j : Y' ⟶ Y) [IsOpenImmersion j] (π : Γ(Y, ⊤)) (x : Y')
    (h : crystallineComparison.GenPt ((ConcreteCategory.hom (Scheme.Hom.appTop j)) π) x) : crystallineComparison.GenPt π (j x) := by
  have key : ∀ y : Y', j y ∈ Y.basicOpen π ↔
      y ∈ Y'.basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop j)) π) := by
    intro y
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  refine ⟨fun hx => h.1 ((key x).1 hx), fun x' hx' hsp => ?_⟩
  obtain ⟨x'', rfl⟩ : x' ∈ Set.range j := hsp.mem_open j.isOpenEmbedding.isOpen_range ⟨x, rfl⟩
  have h2 : x'' ⤳ x := (j.isOpenEmbedding.toIsInducing.specializes_iff).1 hsp
  rw [h.2 x'' (fun hb => hx' ((key x'').2 hb)) h2]

private theorem range_subset_range_of_comp_eq_of_ne_zero {l : ℕ} {Y' Y : Scheme} (j : Y' ⟶ Y) (hP : Part j) (T : crystallineComparison.Corr l Y)
    (T' : crystallineComparison.Corr l Y') (i : T'.Z ⟶ T.Z) (hR : Res j T.p T.r i T'.p T'.r)
    (hr : ∀ x : T.Z, T.p x ∈ Set.range j → T.p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → T.r x ∈ Set.range j)
    (V : Type) [CommRing V] [IsDomain V] (hl : (l : V) ≠ 0) (y' : Spec (CommRingCat.of V) ⟶ Y')
    (z : Spec (CommRingCat.of V) ⟶ T.Z) (hz : z ≫ T.p = y' ≫ j) :
    Set.range z ⊆ Set.range i := by
  have hp : ∀ s, T.p (z s) = j (y' s) := fun s => by
    rw [← Scheme.Hom.comp_apply, hz, Scheme.Hom.comp_apply]
  let η : Spec (CommRingCat.of V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)
  have hη : T.p (z η) ∈ Y.basicOpen (l : Γ(Y, ⊤)) := by
    rw [← Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← Set.mem_preimage, ← Scheme.Hom.coe_preimage,
      Scheme.preimage_basicOpen_top, map_natCast, basicOpen_eq_of_affine', map_natCast]
    exact hl
  have hrη : T.r (z η) ∈ Set.range j := hr _ (by rw [hp]; exact ⟨_, rfl⟩) hη
  rintro _ ⟨s, rfl⟩
  have hsp : η ⤳ s := (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 bot_le
  have hrs : T.r (z s) ∈ Set.range j :=
    ((hsp.map z.continuous).map T.r.continuous).mem_closed hP.cl hrη
  rw [hR.rng]
  exact ⟨by rw [Set.mem_preimage, hp]; exact ⟨_, rfl⟩, hrs⟩

private theorem bijective_sec_comp_of_ne_zero {l : ℕ} {Y' Y : Scheme} (j : Y' ⟶ Y) (hP : Part j) (T : crystallineComparison.Corr l Y)
    (T' : crystallineComparison.Corr l Y') (i : T'.Z ⟶ T.Z) (hR : Res j T.p T.r i T'.p T'.r)
    (hr : ∀ x : T.Z, T.p x ∈ Set.range j → T.p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → T.r x ∈ Set.range j)
    (V : Type) [CommRing V] [IsDomain V] (hl : (l : V) ≠ 0) (y' : Spec (CommRingCat.of V) ⟶ Y') :
    Function.Bijective (fun u : T'.Sec y' => (⟨u.1 ≫ i, by
      rw [Category.assoc, ← hR.es, ← Category.assoc, u.2]⟩ : T.Sec (y' ≫ j))) := by
  haveI := hP.op
  haveI := hR.op
  constructor
  · intro u v h
    apply Subtype.ext
    exact (cancel_mono i).1 (congrArg Subtype.val h)
  · intro z
    have hsub := range_subset_range_of_comp_eq_of_ne_zero j hP T T' i hR hr V hl y' z.1 z.2
    refine ⟨⟨IsOpenImmersion.lift i z.1 hsub, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    apply (cancel_mono j).1
    rw [Category.assoc, hR.es, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact z.2

theorem ptIdCut : PtIdCut := by
  unfold PtIdCut
  intro l q n Y' Y j π T T' i hP hR hr hT
  unfold crystallineComparison.PtId at hT ⊢
  intro V _ _ _ _ hl y' hg φ hφ I _ z' hz'
  haveI := hP.op
  let w : (a : Fin (n + 1)) → I a → (T a).Sec (y' ≫ j) := fun a b =>
    ⟨(z' a b).1 ≫ i a, by rw [Category.assoc, ← (hR a).es, ← Category.assoc, (z' a b).2]⟩
  have hw : ∀ a, Function.Bijective (w a) := fun a =>
    (bijective_sec_comp_of_ne_zero j hP (T a) (T' a) (i a) (hR a) (hr a) V hl y').comp (hz' a)
  have hg' : crystallineComparison.GenPt π ((y' ≫ j) (IsLocalRing.closedPoint V)) := by
    have h0 := genPt_openImmersion_of_genPt_appTop j π _ hg
    convert h0 using 1
    exact Scheme.Hom.comp_apply y' j _
  have h := hT V hl (y' ≫ j) hg' φ hφ I w hw
  refine identity_of_comp_injective_semiconj_image q n (crystallineComparison.twist φ Y') (crystallineComparison.twist φ Y) (fun x => x ≫ j)
    (fun x y hxy => (cancel_mono j).1 hxy) (fun x => by simp [crystallineComparison.twist, Category.assoc]) _ ?_
  have e : (fun a b => (crystallineComparison.resPt V ≫ (z' a b).1 ≫ (T' a).r) ≫ j) =
      fun a b => crystallineComparison.resPt V ≫ (w a b).1 ≫ (T a).r := by
    funext a b
    simp only [w, Category.assoc, (hR a).et]
  rw [e]
  exact h

end UpperTheory.Gal.Int.Geo.Cut
