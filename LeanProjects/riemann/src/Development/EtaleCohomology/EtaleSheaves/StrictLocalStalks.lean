import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.ULAStalkPf

def PolyPO : Prop := ∀ {A B : CommRingCat.{0}} (b : A ⟶ B),
  IsPushout (pC A) b (CommRingCat.ofHom (Polynomial.mapRingHom b.hom)) (pC B)

def IECob : Prop := ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D),
  IsPushout f g u v → IE f → IE v

def FracAIC : Prop := ∀ (T K : Type) [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K], AIC T → AIC K

def FracOf : Prop := ∀ (B C : Type) [CommRing B] [CommRing C] [IsDomain C] (j : B →+* C), Function.Injective j →
  (∀ z : C, ∃ s y : B, s ≠ 0 ∧ j s * z = j y) →
  @IsFractionRing B _ (FractionRing C) _ ((algebraMap C (FractionRing C)).comp j).toAlgebra

theorem ULAStalk_of (hI : IntClos) (hT : SHTensor) (hA : AICSH) (hE : SHEqv) (hC3 : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial)
    (p1 : PolyPO) (p2 : IECob) (p3 : FracAIC) (p4 : FracOf) : ULAStalk := by
  intro H q _ i A X h hq hA' hX hh hloc C c _ _ hCa hCr Y' w φ' sq
  obtain ⟨B, b, j, hbj, hbint, hjinj, hBloc, hBaic, hfr⟩ := hI c hA' hCa hCr
  have : IsDomain B := Function.Injective.isDomain j.hom hjinj
  let K := FractionRing C
  let l : C ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap C K)
  let algBK : Algebra B K := ((algebraMap C K).comp j.hom).toAlgebra
  have : IsFractionRing B K := p4 B C j.hom hjinj hfr
  have hKsh : SH K := hA K (p3 C K hCa)
  have hBsh : SH B := hA B hBaic
  have hCsh : SH C := hA C hCa
  have hqB : IsUnit (q : B) := by simpa using hq.map b.hom
  have hqC : IsUnit (q : C) := by simpa using hq.map c.hom

  let mB : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial B) := CommRingCat.ofHom (Polynomial.mapRingHom b.hom)
  have sB : IsPushout h mB (pushout.inl h mB) (pushout.inr h mB) := IsPushout.of_hasPushout _ _
  have hBIE : IE (pushout.inr h mB) := p2 _ _ _ _ sB hh
  have sBA : IsPushout (pC A ≫ h) b (pushout.inl h mB) (pC B ≫ pushout.inr h mB) := (p1 b).paste_horiz sB
  let ZB : CommRingCat.{0} := pushout h mB
  have hZBsh : SH ZB := hT _ _ _ _ sBA hA' hX hloc hbint hBloc
  have r1 : RE q i (pC B ≫ pushout.inr h mB) := hE H q i _ hqB hBsh hZBsh
  let bl : B ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap B K)
  have sL : IsPushout (pC B ≫ pushout.inr h mB) bl (pushout.inl _ bl) (pushout.inr _ bl) := IsPushout.of_hasPushout _ _
  have r2 : RE q i (pushout.inl (pC B ≫ pushout.inr h mB) bl) :=
    hC3 H q i B K hBaic hqB (pushout h mB) (pushout.inr h mB) hBIE _ _ _ sL.flip
  have r3 : RE q i bl := hE H q i bl hqB hBsh hKsh
  have r4 : RE q i (pushout.inr (pC B ≫ pushout.inr h mB) bl) :=
    RE.of_comp_left r3 (by rw [← pushout.condition]; exact r1.comp r2)

  let mC : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial C) := CommRingCat.ofHom (Polynomial.mapRingHom c.hom)
  let hC : CommRingCat.of (Polynomial C) ⟶ Y' := (p1 c).desc (h ≫ w) φ' (by rw [← Category.assoc]; exact sq.w)
  have e1 : mC ≫ hC = h ≫ w := (p1 c).inl_desc _ _ _
  have e2 : pC C ≫ hC = φ' := (p1 c).inr_desc _ _ _
  have sC : IsPushout h mC w hC := IsPushout.of_left (by rw [e2]; exact sq) e1.symm (p1 c)
  have hCIE : IE hC := p2 _ _ _ _ sC hh
  have sq' : IsPushout l (pC C ≫ hC) (pushout.inr φ' l) (pushout.inl φ' l) := by
    rw [e2]; exact (IsPushout.of_hasPushout φ' l).flip
  have r5 : RE q i (pushout.inl φ' l) := hC3 H q i C K hCa hqC Y' hC hCIE _ _ _ sq'
  have r6 : RE q i l := hE H q i l hqC hCsh hKsh
  have ebl : b ≫ bl = c ≫ l := by rw [← hbj]; rfl
  have PZ : IsPushout (pC A ≫ h) (c ≫ l) (pushout.inl h mB ≫ pushout.inl (pC B ≫ pushout.inr h mB) bl)
      (pushout.inr (pC B ≫ pushout.inr h mB) bl) := by
    rw [← ebl]; exact sBA.paste_vert sL
  have PZ' : IsPushout (pC A ≫ h) (c ≫ l) (w ≫ pushout.inl φ' l) (pushout.inr φ' l) :=
    sq.paste_vert (IsPushout.of_hasPushout φ' l)
  have r7 : RE q i (pushout.inr φ' l) := by
    rw [← PZ.inr_isoIsPushout_hom _ _ PZ']; exact r4.comp (RE.of_isIso q i _)
  exact RE.of_comp_right r5 (by rw [pushout.condition]; exact r6.comp r7)

end LateralTheory.E.ULAStalkPf
