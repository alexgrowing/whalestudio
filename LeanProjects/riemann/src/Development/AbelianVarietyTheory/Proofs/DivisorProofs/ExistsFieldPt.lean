import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.Sat

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (s : Sp B ⟶ Sp A) : ∃ u : A →+* B, spMap u = s :=
  ⟨(Spec.preimage s).hom, Spec.map_preimage s⟩

theorem isDominant_gp (X : Scheme.{0}) [IsIntegral X] : IsDominant (gp X) := by
  constructor
  have h : genericPoint X ∈ Set.range (gp X) :=
    ⟨closedPoint (X.presheaf.stalk (genericPoint X)), Scheme.fromSpecStalk_closedPoint⟩
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_closure X
  exact h2.mono (Set.singleton_subset_iff.mpr h)

theorem pff_id {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {φ : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) φ θ) : gp Y ≫ φ = spMap θ ≫ gp X := by
  obtain ⟨l, h1, h2⟩ := h
  rw [Category.comp_id] at h1
  rw [← h1, h2]

theorem transfer (σ : Setup) (E : Emb σ) (hC : σ.Common) (x x' : Sp σ.R) (Ω : Type) [Field Ω]
    (s : Sp Ω ⟶ Sp (σ.C x).R) (s' : Sp Ω ⟶ Sp (σ.C x').R) (o : Sp Ω) (hs' : s' o = closedPoint (σ.C x').R)
    (h : s ≫ spMap (σ.ρ x) = s' ≫ spMap (σ.ρ x')) :
    (∀ t : Sp Ω ⟶ (σ.C x).G.left, t ≫ (σ.C x).G.hom = s →
      ∃ t' : Sp Ω ⟶ (σ.C x').G.left, t' ≫ (σ.C x').G.hom = s' ∧ t' ≫ E.emb x' = t ≫ E.emb x) ∧
    (∀ t' : Sp Ω ⟶ (σ.C x').G.left, t' ≫ (σ.C x').G.hom = s' →
      ∃ t : Sp Ω ⟶ (σ.C x).G.left, t ≫ (σ.C x).G.hom = s ∧ t ≫ E.emb x = t' ≫ E.emb x') := by
  obtain ⟨u, rfl⟩ := sp_surj s
  obtain ⟨u', rfl⟩ := sp_surj s'
  have hk : RingHom.ker u' = maximalIdeal _ := by
    obtain rfl : o = closedPoint Ω := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    have h1 : (maximalIdeal Ω).comap u' = maximalIdeal _ := congrArg PrimeSpectrum.asIdeal hs'
    rw [← h1, maximalIdeal_eq_bot]; rfl
  rw [sp_comp, sp_comp] at h
  obtain ⟨R', _, _, _, a, b, v, H, _, _, πa, πb, θa, θb, -, -, hab, -, hva, hvb, -, -, ⟨pa, -⟩, ⟨pb, -⟩, fa, fb, hθ⟩ :=
    hC x x' Ω u u' hk (sp_inj h)
  have key : πa ≫ E.emb x = πb ≫ E.emb x' := by
    haveI := E.sep
    haveI := isDominant_gp H.left
    obtain ⟨w, -⟩ := E.openIn x
    obtain ⟨w', -⟩ := E.openIn x'
    refine ext_of_isDominant_of_isSeparated E.p ?_ (gp H.left) ?_
    · rw [Category.assoc, Category.assoc, w, w', pa.w_assoc, pb.w_assoc, sp_comp, sp_comp, hab]
    · rw [← Category.assoc, ← Category.assoc, pff_id fa, pff_id fb, Category.assoc, Category.assoc,
        pff_id (E.ff x), pff_id (E.ff x'), ← Category.assoc, ← Category.assoc, sp_comp, sp_comp,
        ← RingHom.comp_assoc, ← RingHom.comp_assoc, hθ]
  have ea : spMap v ≫ spMap a = spMap u := by rw [sp_comp, hva]
  have eb : spMap v ≫ spMap b = spMap u' := by rw [sp_comp, hvb]
  constructor
  · intro t ht
    refine ⟨pa.lift t (spMap v) (ht.trans ea.symm) ≫ πb, ?_, ?_⟩
    · rw [Category.assoc, pb.w, pa.lift_snd_assoc, eb]
    · rw [Category.assoc, ← key, pa.lift_fst_assoc]
  · intro t ht
    refine ⟨pb.lift t (spMap v) (ht.trans eb.symm) ≫ πa, ?_, ?_⟩
    · rw [Category.assoc, pa.w, pb.lift_snd_assoc, ea]
    · rw [Category.assoc, key, pb.lift_fst_assoc]

theorem exists_field_pt {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (h : f x = g y) :
    ∃ (Ω : Type) (_ : Field Ω) (s : Sp Ω ⟶ X) (t : Sp Ω ⟶ Y) (o : Sp Ω), s ≫ f = t ≫ g ∧ s o = x ∧ t o = y := by
  obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y h
  let r : Sp ((pullback f g).residueField z) ⟶ pullback f g := (pullback f g).fromSpecResidueField z
  let o : Sp ((pullback f g).residueField z) := closedPoint _
  have hr : r o = z := Scheme.fromSpecResidueField_apply z _
  refine ⟨(pullback f g).residueField z, inferInstance, r ≫ pullback.fst f g, r ≫ pullback.snd f g, o, ?_, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition]
  · rw [Scheme.Hom.comp_apply, hr, h1]
  · rw [Scheme.Hom.comp_apply, hr, h2]

end GlobalTheory.Desc.Sat

namespace GlobalTheory.Desc

open Sat in

theorem Emb.fst_mem_U_iff : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ (x : Sp σ.R) (w : ↥(Limits.pullback E.p (spMap (σ.ρ x)))), (Limits.pullback.fst E.p (spMap (σ.ρ x)) w ∈ E.U ↔ ∃ y : (σ.C x).G.left, E.emb x y = Limits.pullback.fst E.p (spMap (σ.ρ x)) w ∧ (σ.C x).G.hom y = Limits.pullback.snd E.p (spMap (σ.ρ x)) w) := by
  intro σ E hC x w
  constructor
  · rintro ⟨x', y', hy', e⟩
    obtain ⟨Ω, _, s, t', o, hst, hs, ht⟩ := exists_field_pt (pullback.fst E.p (spMap (σ.ρ x))) (E.emb x') w y' e.symm
    obtain ⟨w', -⟩ := E.openIn x'
    obtain ⟨t, h1, h2⟩ := (transfer σ E hC x x' Ω (s ≫ pullback.snd _ _) (t' ≫ (σ.C x').G.hom) o
      (by rw [Scheme.Hom.comp_apply, ht]; exact hy')
      (by rw [Category.assoc, Category.assoc, ← pullback.condition, ← w', reassoc_of% hst])).2 t' rfl
    refine ⟨t o, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, ht, e]
    · rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, hs]
  · rintro ⟨y, e, -⟩
    rw [← e]
    let x' : Sp σ.R := ((σ.C x).G.hom ≫ spMap (σ.ρ x)) y
    have hx' : spMap (σ.ρ x') (closedPoint _) = x' := by rw [← σ.hρ]; exact (σ.C x').centre
    obtain ⟨Ω, _, t, s', o, hst, ht, hs⟩ :=
      exists_field_pt ((σ.C x).G.hom ≫ spMap (σ.ρ x)) (spMap (σ.ρ x')) y (closedPoint _) hx'.symm
    obtain ⟨t', h1, h2⟩ := (transfer σ E hC x x' Ω (t ≫ (σ.C x).G.hom) s' o hs
      (by rw [Category.assoc, hst])).1 t rfl
    refine ⟨x', t' o, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h1, hs]
    · rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, ht]

end GlobalTheory.Desc
