import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsogOfSurjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientClassifyingMapIsogenyUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineHomOfIsAffineHomPullbackSndOfFpqc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem desc_pull {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)} (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (h : f ≫ s = s')
    (o : Ob D l s) : ∃ o' : Ob D l s', Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s s' f rfl rfl
    (by rw [h]; simp [spMap]) o

theorem desc_comp {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} (m : ObjMap o' o f)
    (m' : ObjMap o'' o' f') :
    ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ :=
  ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).1 m'

theorem desc_cancel {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {g : S'' ⟶ S} (m : ObjMap o' o f)
    (m'' : ObjMap o'' o g) (e : f' ≫ f = g) :
    ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  subst e
  exact ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).2 m''

theorem desc_cocycle (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S']
    {s : S ⟶ Sp (KA l)} (π : S' ⟶ S) [Etale π] (o : Ob D l s) (o' o₂' : Ob D l (π ≫ s)) (m : ObjMap o' o π)
    (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K) (ψ' : o'.t.G ⟶ o₂'.t.G)
    (hψ : IsIsog o' o₂' p ψ') (hker : KerSet ψ' (m.toSABMap.φ ⁻¹' K)) (f' : S' ⟶ Xo.X) (hf' : f' ≫ Xo.s = π ≫ s)
    (n' : ObjMap o₂' Xo.univ f') :
    (∀ {Z : Scheme.{0}} (x y : Z ⟶ S'), x ≫ π = y ≫ π → x ≫ f' = y ≫ f') ∧
    ∀ {Z : Scheme.{0}} (x y : Z ⟶ o'.t.G.left), x ≫ m.toSABMap.φ = y ≫ m.toSABMap.φ →
      x ≫ ψ'.left ≫ n'.toSABMap.φ = y ≫ ψ'.left ≫ n'.toSABMap.φ := by
  have hab : pullback.fst π π ≫ π = pullback.snd π π ≫ π := pullback.condition
  haveI : IsReduced (pullback π π) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst π π)
  obtain ⟨oT, ⟨mT⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.fst π π ≫ π) (by simp) o
  obtain ⟨ma, hma⟩ := desc_cancel (f' := pullback.fst π π) m mT rfl
  obtain ⟨mb, hmb⟩ := desc_cancel (f' := pullback.snd π π) m mT hab.symm
  obtain ⟨oa, ⟨na⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.fst π π) rfl o₂'
  obtain ⟨ob, ⟨nb⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.snd π π)
    (by rw [reassoc_of% hab]) o₂'
  obtain ⟨⟨ψa, hψa, -⟩, Ha⟩ := GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ _ o' o₂' oT oa ma na ψ'
  obtain ⟨⟨ψb, hψb, -⟩, Hb⟩ := GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ _ o' o₂' oT ob mb nb ψ'
  obtain ⟨ia, ka⟩ := Ha ψa hψa
  obtain ⟨ib, kb⟩ := Hb ψb hψb
  have ka' : KerSet ψa (mT.toSABMap.φ ⁻¹' K) := by
    have := ka _ hψ.1.1 hker
    rw [hma]; simpa [Set.preimage_comp] using this
  have kb' : KerSet ψb (mT.toSABMap.φ ⁻¹' K) := by
    have := kb _ hψ.1.1 hker
    rw [hmb]; simpa [Set.preimage_comp] using this
  have hKT : HeckeSet D oT.t 𝔓 p i (mT.toSABMap.φ ⁻¹' K) :=
    ((GlobalTheory.heckeSets_pull E H D 𝔓 p i _ _ o.t oT.t _ mT.toSABMap o.proper).2 K).1 hK
  obtain ⟨na', hna⟩ := desc_comp n' na
  obtain ⟨nb', hnb⟩ := desc_comp n' nb
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique E H D l Xo 𝔓 p i _ _ oT oa ob ψa ψb _ _ _ na' nb' hA hKT
    (by rw [Category.assoc, hf']) (by rw [Category.assoc, hf', reassoc_of% hab]) (ia hψ) (ib hψ) ka' kb'
  rw [hna, hnb, reassoc_of% hψa, reassoc_of% hψb] at e₂
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have := pullback.lift x y hxy ≫= e₁
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  · have pm : IsPullback m.toSABMap.φ o'.t.G.hom o.t.G.hom π := m.cart.1
    have pa : IsPullback ma.toSABMap.φ oT.t.G.hom o'.t.G.hom (pullback.fst π π) := ma.cart.1
    have pb : IsPullback mb.toSABMap.φ oT.t.G.hom o'.t.G.hom (pullback.snd π π) := mb.cart.1
    have h₀ : (x ≫ o'.t.G.hom) ≫ π = (y ≫ o'.t.G.hom) ≫ π := by
      simp only [Category.assoc, ← pm.w, reassoc_of% hxy]
    let w := pa.lift x (pullback.lift _ _ h₀) (pullback.lift_fst _ _ _).symm
    have wa : w ≫ ma.toSABMap.φ = x := pa.lift_fst _ _ _
    have wb : w ≫ mb.toSABMap.φ = y := by
      apply pm.hom_ext
      · rw [Category.assoc, ← hmb, hma, reassoc_of% wa, hxy]
      · rw [Category.assoc, pb.w, pa.lift_snd_assoc, pullback.lift_snd]
    rw [← wa, ← wb, Category.assoc, Category.assoc, e₂]

theorem hasQuot_descend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (π : S' ⟶ S) (o : Ob D l s) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → Etale π → Surjective π → QuasiCompact π → HasQuot o' p (m.toSABMap.φ ⁻¹' K) → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i S S' _ s π o o' m K hA hK hE hS hQ ⟨o₂', ψ', hψ, hker⟩
  haveI : IsReduced S' := GlobalTheory.isReduced_of_smooth_of_isReduced π
  obtain ⟨f', ⟨hf', ⟨n'⟩⟩, -⟩ := Xo.rep S' (π ≫ s) inferInstance o₂'
  obtain ⟨c₁, c₂⟩ := desc_cocycle Xo 𝔓 p i π o o' o₂' m K hA hK ψ' hψ hker f' hf' n'
  have pm : IsPullback m.toSABMap.φ o'.t.G.hom o.t.G.hom π := m.cart.1
  have pn' : IsPullback n'.toSABMap.φ o₂'.t.G.hom Xo.univ.t.G.hom f' := n'.cart.1
  haveI : Flat m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip (inferInstance : Flat π)
  haveI : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip hS
  haveI : QuasiCompact m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip hQ
  haveI : EffectiveEpi π := inferInstance
  haveI : EffectiveEpi m.toSABMap.φ := inferInstance
  obtain ⟨f, hf⟩ : ∃ f : S ⟶ Xo.X, π ≫ f = f' := ⟨_, EffectiveEpi.fac π f' c₁⟩
  obtain ⟨h, hh⟩ : ∃ h, m.toSABMap.φ ≫ h = ψ'.left ≫ n'.toSABMap.φ := ⟨_, EffectiveEpi.fac _ _ c₂⟩
  have hfs : f ≫ Xo.s = s := by rw [← cancel_epi π, reassoc_of% hf, hf']
  obtain ⟨o₂, ⟨n⟩⟩ := desc_pull s f hfs Xo.univ
  obtain ⟨n₂, hn₂⟩ := desc_cancel n n' hf
  have pn : IsPullback n.toSABMap.φ o₂.t.G.hom Xo.univ.t.G.hom f := n.cart.1
  have pn₂ : IsPullback n₂.toSABMap.φ o₂'.t.G.hom o₂.t.G.hom π := n₂.cart.1
  have hw : h ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ f := by
    rw [← cancel_epi m.toSABMap.φ, reassoc_of% hh, pn'.w, pm.w_assoc, hf, Over.w_assoc]
  let ψ : o.t.G ⟶ o₂.t.G := Over.homMk (pn.lift h _ hw) (pn.lift_snd _ _ _)
  have hψn : ψ.left ≫ n.toSABMap.φ = h := pn.lift_fst _ _ _
  have sq : ψ'.left ≫ n₂.toSABMap.φ = m.toSABMap.φ ≫ ψ.left := by
    apply pn.hom_ext
    · rw [Category.assoc, Category.assoc, ← hn₂, hψn, hh]
    · rw [Category.assoc, Category.assoc, pn₂.w, Over.w_assoc, Over.w, pm.w]
  have P : IsPullback m.toSABMap.φ ψ'.left ψ.left n₂.toSABMap.φ :=
    IsPullback.of_bot (by rw [Over.w, Over.w]; exact pm) sq.symm pn₂
  have q : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) n₂.toSABMap.φ :=
    ⟨⟨MorphismProperty.of_isPullback pn₂.flip hS,
      MorphismProperty.of_isPullback pn₂.flip (inferInstance : Flat π)⟩,
      MorphismProperty.of_isPullback pn₂.flip hQ⟩
  have hEt : Etale ψ.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale) P.flip q hψ.1.2.2.1
  haveI : IsFinite ψ'.left := hψ.1.2.1
  haveI : IsAffineHom ψ.left := by
    refine GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ ψ.left n₂.toSABMap.φ q.1.1 q.1.2 q.2 ?_
    rw [← P.isoPullback_inv_snd]
    infer_instance
  haveI := o₂.proper
  haveI : IsProper (ψ.left ≫ o₂.t.G.hom) := by rw [Over.w]; exact o.proper
  haveI : IsProper ψ.left := IsProper.of_comp ψ.left o₂.t.G.hom
  have hFin : IsFinite ψ.left := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨r₁, r₂⟩ := GlobalTheory.isIsog_of_surjective_baseChange E H D l p S S' s _ π o o₂ o' o₂' m n₂ ψ ψ' hS sq hψ hFin hEt
  exact ⟨o₂, ψ, r₁, r₂ K hker⟩

end GlobalTheory.HkFam
