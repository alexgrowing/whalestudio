import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

set_option backward.isDefEq.respectTransparency false in
private theorem isFinite_sigma_desc_of_finite (ι : Type) [Finite ι] :
    ∀ {S : Scheme.{0}} (Z : ι → Scheme.{0}) (p : ∀ a, Z a ⟶ S), (∀ a, IsFinite (p a)) →
      IsFinite (Sigma.desc p) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro S Z p hp
    have := ih (fun a => Z (e a)) (fun a => p (e a)) (fun a => hp _)
    let i : (∐ fun a => Z (e a)) ≅ ∐ Z := Sigma.whiskerEquiv e (fun _ => Iso.refl _)
    have h : i.hom ≫ Sigma.desc p = Sigma.desc (fun a => p (e a)) := by
      apply Sigma.hom_ext
      intro a
      simp [i]
    have h' : Sigma.desc p = i.inv ≫ Sigma.desc (fun a => p (e a)) := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [h']
    infer_instance
  | h_empty =>
    intro S Z p hp
    have : IsEmpty (∐ Z : Scheme.{0}) := ⟨fun x => by
      obtain ⟨i, _, _⟩ := (sigmaOpenCover Z).exists_eq x
      exact i.elim⟩
    infer_instance
  | h_option ih =>
    intro S Z p hp
    have h1 := ih (fun a => Z (some a)) (fun a => p (some a)) (fun a => hp _)
    have h0 := hp none
    let i : (Z none ⨿ ∐ fun a => Z (some a)) ≅ ∐ Z :=
      { hom := coprod.desc (Sigma.ι Z none) (Sigma.desc fun a => Sigma.ι Z (some a))
        inv := Sigma.desc fun o => match o with
          | none => coprod.inl
          | some a => Sigma.ι (fun a => Z (some a)) a ≫ coprod.inr
        hom_inv_id := by
          apply coprod.hom_ext
          · simp
          · apply Sigma.hom_ext
            intro a
            simp
        inv_hom_id := by
          apply Sigma.hom_ext
          rintro (_ | a) <;> simp }
    have h : i.hom ≫ Sigma.desc p = coprod.desc (p none) (Sigma.desc fun a => p (some a)) := by
      apply coprod.hom_ext
      · simp [i]
      · apply Sigma.hom_ext
        intro a
        simp [i]
    have h' : Sigma.desc p = i.inv ≫ coprod.desc (p none) (Sigma.desc fun a => p (some a)) := by
      rw [← h, Iso.inv_hom_id_assoc]
    have c : IsFinite (coprod.desc (p none) (Sigma.desc fun a => p (some a))) := inferInstance
    have d0 : IsIso i.inv := ⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩
    have d : IsFinite i.inv := inferInstance
    rw [h']
    infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.Gal.TranscendenceTraces.imageFin_of :
    ImageOne → ImageFin := by
  intro hOne S Y B bS bY _ _ ι _ Z p f hp hf
  have hk : (Sigma.desc fun a => pullback.lift (f a) (p a) (hf a)) ≫ pullback.snd bY bS = Sigma.desc p := by
    apply Sigma.hom_ext
    intro a
    simp
  obtain ⟨k, hkdef⟩ : ∃ k : ∐ Z ⟶ pullback bY bS, k = Sigma.desc fun a => pullback.lift (f a) (p a) (hf a) := ⟨_, rfl⟩
  rw [← hkdef] at hk
  have hι : ∀ a, Sigma.ι Z a ≫ k = pullback.lift (f a) (p a) (hf a) := by
    intro a
    simp [hkdef]
  have hfin : IsFinite (k ≫ pullback.snd bY bS) := by
    rw [hk]
    exact isFinite_sigma_desc_of_finite ι Z p hp
  obtain ⟨h1, h2⟩ := hOne k (pullback.snd bY bS)
  have hh : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι = pullback.lift (f a) (p a) (hf a) := by
    intro a
    rw [Category.assoc, Scheme.Hom.toImage_imageι, hι]
  have hpa : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.snd bY bS = p a := by
    intro a
    rw [← Category.assoc, hh, pullback.lift_snd]
  have hfa : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.fst bY bS = f a := by
    intro a
    rw [← Category.assoc, hh, pullback.lift_fst]
  refine ⟨k.image, k.imageι ≫ pullback.snd bY bS, k.imageι ≫ pullback.fst bY bS,
    fun a => Sigma.ι Z a ≫ k.toImage, h1, fun a => ?_, hpa, hfa, ?_⟩
  · have : IsFinite ((Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.snd bY bS) := by
      rw [hpa]
      exact hp a
    exact IsFinite.of_comp _ (k.imageι ≫ pullback.snd bY bS)
  · intro T x y hs hf'
    rw [← cancel_mono k.imageι]
    apply pullback.hom_ext
    · simpa using hf'
    · simpa using hs
