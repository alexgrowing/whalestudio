import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatFactorThroughLocalSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenOfSaturatedLocalSchemeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfOpenBaseChangeEqPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothNhdsOfSmoothOverLocalSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpUnitsAndInversesAgreeOfLawsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGrpLawAgreesWithAbelianSchemeLawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFiniteTypeNearGenerisationOfPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMorphismToLocalSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadMorphismBasicOpenAgreeFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjOfLawUnitInverseAgreeAwayStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.Spread

theorem isPullback_sq {S U Z X : Scheme.{0}} {s : Z ⟶ S} {j : U ⟶ S} {p : X ⟶ U} {φ : X ⟶ Z}
    (h : IsPullback φ p s j) :
    IsPullback (pullback.map p p s s φ φ j h.w.symm h.w.symm) (pullback.fst p p ≫ p) (pullback.fst s s ≫ s) j := by
  have h₁ : IsPullback (pullback.map p p s s φ φ j h.w.symm h.w.symm) (pullback.fst p p) (pullback.fst s s) φ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd s s) (v₁₃ := s) (h₂₂ := s) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback s s).flip
    rw [pullback.lift_snd, h.w]
    exact (IsPullback.of_hasPullback p p).flip.paste_horiz h
  exact h₁.paste_vert h

theorem lift_left_eq {S : Scheme.{0}} {T G : Over S} (a b : T ⟶ G) (t : T.left ⟶ pullback G.hom G.hom)
    (h₁ : t ≫ pullback.fst _ _ = a.left) (h₂ : t ≫ pullback.snd _ _ = b.left) : (lift a b).left = t := by
  apply pullback.hom_ext
  · exact (congrArg (fun z => z.left) (lift_fst a b)).trans h₁.symm
  · exact (congrArg (fun z => z.left) (lift_snd a b)).trans h₂.symm

theorem mul_left_eq {S : Scheme.{0}} {T G : Over S} [GrpObj G] (a b : T ⟶ G) (t : T.left ⟶ pullback G.hom G.hom)
    (h₁ : t ≫ pullback.fst _ _ = a.left) (h₂ : t ≫ pullback.snd _ _ = b.left) : (a * b).left = t ≫ (μ[G]).left := by
  rw [← lift_left_eq a b t h₁ h₂]; rfl

theorem inv_left_eq {S : Scheme.{0}} {T G : Over S} [GrpObj G] (a : T ⟶ G) : (a⁻¹).left = a.left ≫ (ι[G]).left := rfl

theorem one_left_eq {S T : Scheme.{0}} {G : Over S} [GrpObj G] (t : T ⟶ S) :
    (1 : Over.mk t ⟶ G).left = t ≫ (η[G]).left := by
  have : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  exact (show (1 : Over.mk t ⟶ G).left = (toUnit (Over.mk t)).left ≫ (η[G]).left from rfl).trans
    (congrArg (· ≫ (η[G]).left) this)

theorem exists_ext {R : Type} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0) (x : Sp R) {S₁ B Z B₀ B₁ : Scheme.{0}}
    (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)) [Flat ξ'] [Surjective ξ'] [QuasiCompact ξ'] (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R)
    [Flat pB] [QuasiCompact pB] [QuasiSeparated pB] [IsSeparated pZ] [LocallyOfFinitePresentation pZ]
    {φ₀ : B₀ ⟶ B} {q₀ : B₀ ⟶ Sp (Localization.Away f)} (u₀ : B₀ ⟶ Z) {φ₁ : B₁ ⟶ B} {q₁ : B₁ ⟶ S₁} (u₁ : B₁ ⟶ Z)
    (h₀ : IsPullback φ₀ q₀ pB (awayMap f)) (h₁ : IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x))
    (w₀ : u₀ ≫ pZ = φ₀ ≫ pB) (w₁ : u₁ ≫ pZ = φ₁ ≫ pB)
    (ag : ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) :
    ∃ g : R, g ∉ x.asIdeal ∧ ∀ (Y : Scheme.{0}) (a : Y ⟶ B), (∀ y : Y, g ∉ (pB (a y)).asIdeal) →
      ∃ u' : Y ⟶ Z, u' ≫ pZ = a ≫ pB ∧
        ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Y), t₀ ≫ φ₀ = t ≫ a → t₀ ≫ u₀ = t ≫ u' := by
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.exists_descent_morphism_to_local_scheme R f hf x S₁ B Z B₀ B₁ ξ' ‹_› ‹_› ‹_› pB pZ ‹_› ‹_› φ₀ q₀ u₀ φ₁ q₁ u₁ h₀ h₁ w₁ ag
  exact GlobalTheory.T.exists_spread_morphism_basicOpen_agree_flat R x B Z B₀ pB pZ ‹_› ‹_› ‹_› ‹_› ‹_› φ₀ u₀
    (MorphismProperty.of_isPullback (P := @Flat) h₀.flip inferInstance) w₀ u hu hu'

theorem not_mem_of_dvd {R : Type} [CommRing R] {g g' : R} (hg : g' ∣ g) {Y B : Scheme.{0}} {a : Y ⟶ B} {pB : B ⟶ Sp R}
    {c : Y ⟶ Sp (Localization.Away g)} (w : a ≫ pB = c ≫ awayMap g) (y : Y) : g' ∉ (pB (a y)).asIdeal := by
  rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  intro h
  have h' : algebraMap R (Localization.Away g) g ∈ (c y).asIdeal := Ideal.mem_of_dvd (awayMap g (c y)).asIdeal hg h
  exact (c y).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (IsLocalization.Away.algebraMap_isUnit g))

theorem exists_grp_near : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R) (S₁ X : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ q : X ⟶ Sp R, Smooth q → QuasiCompact q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ (G : Over S₁) [GrpObj G] (i : A.left ⟶ X) (e : G.left ⟶ X), IsPullback i A.hom q (awayMap f) → IsPullback e G.hom q (ξ' ≫ (Sp R).fromSpecStalk x) → MulAgree G A e i → ∃ g : R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) ∧ MulAgree H A h i := by
  intro R _ _ f hf x S₁ X ξ' _ _ _ q _ _ _ A _ hc G _ i e hi he hm
  obtain ⟨hone, hinv⟩ := GlobalTheory.T.grpUnits_and_inverses_agree_of_laws_agree _ _ _ X q _ _ A G i e hi he.w hm
  obtain ⟨g₁, hg₁, H₁⟩ := exists_ext hf x ξ' (pullback.fst q q ≫ q) q ((μ[A]).left ≫ i) ((μ[G]).left ≫ e)
    (isPullback_sq hi) (isPullback_sq he)
    (by rw [(isPullback_sq hi).w, Category.assoc, hi.w, Over.w_assoc]; rfl)
    (by rw [(isPullback_sq he).w, Category.assoc, he.w, Over.w_assoc]; rfl)
    (fun T t₀ t₁ h => by
      have k₁ := congrArg (· ≫ pullback.fst q q) h
      have k₂ := congrArg (· ≫ pullback.snd q q) h
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at k₁ k₂
      have := hm T (t₁ ≫ pullback.fst _ _ ≫ G.hom) (t₀ ≫ pullback.fst _ _ ≫ A.hom)
        (Over.homMk (t₁ ≫ pullback.fst _ _) (by simp)) (Over.homMk (t₁ ≫ pullback.snd _ _) (by simp [pullback.condition]))
        (Over.homMk (t₀ ≫ pullback.fst _ _) (by simp)) (Over.homMk (t₀ ≫ pullback.snd _ _) (by simp [pullback.condition]))
        (by simpa using k₁.symm) (by simpa using k₂.symm)
      rw [mul_left_eq _ _ t₁ rfl rfl, mul_left_eq _ _ t₀ rfl rfl] at this
      exact (Category.assoc _ _ _).symm.trans (this.symm.trans (Category.assoc _ _ _)))
  obtain ⟨g₂, hg₂, H₂⟩ := exists_ext hf x ξ' q q ((ι[A]).left ≫ i) ((ι[G]).left ≫ e) hi he
    (by rw [Category.assoc, hi.w, Over.w_assoc]) (by rw [Category.assoc, he.w, Over.w_assoc])
    (fun T t₀ t₁ h => by
      have := hinv T (t₁ ≫ G.hom) (t₀ ≫ A.hom) (Over.homMk t₁ rfl) (Over.homMk t₀ rfl) h.symm
      rw [inv_left_eq, inv_left_eq] at this
      exact (Category.assoc _ _ _).symm.trans (this.symm.trans (Category.assoc _ _ _)))
  obtain ⟨g₃, hg₃, H₃⟩ := exists_ext hf x ξ' (𝟙 _) q ((η[A]).left ≫ i) ((η[G]).left ≫ e)
    (IsPullback.id_vert (awayMap f)) (IsPullback.id_vert (ξ' ≫ (Sp R).fromSpecStalk x))
    (by rw [Category.assoc, hi.w, Over.w_assoc]; simp) (by rw [Category.assoc, he.w, Over.w_assoc]; simp)
    (fun T t₀ t₁ h => by
      have := hone T t₁ t₀ h.symm
      rw [one_left_eq, one_left_eq] at this
      exact (Category.assoc _ _ _).symm.trans (this.symm.trans (Category.assoc _ _ _)))
  let g := g₁ * g₂ * g₃
  have hg : g ∉ x.asIdeal := fun h => by
    rcases x.isPrime.mem_or_mem h with h | h
    · exact (x.isPrime.mem_or_mem h).elim hg₁ hg₂
    · exact hg₃ h
  let H : Over (Sp (Localization.Away g)) := Over.mk (pullback.snd q (awayMap g))
  let h : H.left ⟶ X := pullback.fst q (awayMap g)
  have hH : IsPullback h H.hom q (awayMap g) := IsPullback.of_hasPullback _ _
  obtain ⟨m, hm₁, hm₂⟩ := H₁ _ _ (not_mem_of_dvd ⟨g₂ * g₃, mul_assoc _ _ _⟩ (isPullback_sq hH).w)
  obtain ⟨n, hn₁, hn₂⟩ := H₂ _ _ (not_mem_of_dvd ⟨g₁ * g₃, by simp only [g]; ring⟩ hH.w)
  obtain ⟨o, ho₁, ho₂⟩ := H₃ _ (awayMap g) (not_mem_of_dvd (c := 𝟙 _) ⟨g₁ * g₂, mul_comm _ _⟩ (by simp))
  have L : ∀ (Y : Over (Sp (Localization.Away g))) (u : Y.left ⟶ X), u ≫ q = Y.hom ≫ awayMap g →
      ∃ v : Y ⟶ H, v.left ≫ h = u :=
    fun Y u w => ⟨Over.homMk (hH.lift u Y.hom w) (hH.lift_snd _ _ _), hH.lift_fst _ _ _⟩
  obtain ⟨m', hm'⟩ := L (H ⊗ H) m (hm₁.trans (isPullback_sq hH).w)
  obtain ⟨n', hn'⟩ := L H n (hn₁.trans hH.w)
  obtain ⟨o', ho'⟩ := L (𝟙_ _) o (ho₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  obtain ⟨_, hfin⟩ := GlobalTheory.T.grpObj_of_law_unit_inverse_agree_away R f g hf X q inferInstance ‹_› A hc i hi H h hH m' n' o'
    (fun T t₁ t₀ a b a' b' k₁ k₂ => by
      have := hm₂ T (lift a' b').left (lift a b).left (by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z.left ≫ i) (lift_fst a' b')).trans
            (k₁.symm.trans ((congrArg (fun z => z.left ≫ h) (lift_fst a b)).symm.trans (Category.assoc _ _ _))))
        · simp only [Category.assoc, pullback.lift_snd]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z.left ≫ i) (lift_snd a' b')).trans
            (k₂.symm.trans ((congrArg (fun z => z.left ≫ h) (lift_snd a b)).symm.trans (Category.assoc _ _ _)))))
      rw [Over.comp_left, Category.assoc, hm']
      exact this.symm.trans (Category.assoc _ _ _).symm)
    (fun T t₁ t₀ a a' k => by
      rw [Over.comp_left, Category.assoc, hn', inv_left_eq, Category.assoc]
      exact (hn₂ T a'.left a.left k.symm).symm)
    (fun T t₁ t₀ k => by
      rw [one_left_eq]
      exact (congrArg (t₁ ≫ ·) ho').trans ((ho₂ T t₀ t₁ k.symm).symm.trans (Category.assoc _ _ _).symm))
  exact ⟨g, hg, H, inferInstance, h, hH, hfin⟩

theorem fst_mem_U_iff_range (σ : Setup) (E : Emb σ) (hC : σ.Common) (x : Sp σ.R)
    (hw : E.emb x ≫ E.p = (σ.C x).G.hom ≫ spMap (σ.ρ x)) (w : ↥(pullback E.p (spMap (σ.ρ x)))) :
    pullback.fst E.p (spMap (σ.ρ x)) w ∈ E.U ↔ w ∈ Set.range (pullback.lift (E.emb x) (σ.C x).G.hom hw) := by
  constructor
  · rintro ⟨x', y', hy', e⟩
    obtain ⟨Ω, _, s, t', o, hst, hs, ht⟩ :=
      Sat.exists_field_pt (pullback.fst E.p (spMap (σ.ρ x))) (E.emb x') w y' e.symm
    obtain ⟨w', -⟩ := E.openIn x'
    obtain ⟨t, h1, h2⟩ := (Sat.transfer σ E hC x x' Ω (s ≫ pullback.snd _ _) (t' ≫ (σ.C x').G.hom) o
      (by rw [Scheme.Hom.comp_apply, ht]; exact hy')
      (by rw [Category.assoc, Category.assoc, ← pullback.condition, ← w', reassoc_of% hst])).2 t' rfl
    have h3 : t ≫ pullback.lift (E.emb x) (σ.C x).G.hom hw = s := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, h2, hst]
      · rw [Category.assoc, pullback.lift_snd, h1]
    exact ⟨t o, by rw [← Scheme.Hom.comp_apply, h3, hs]⟩
  · rintro ⟨y, rfl⟩
    refine (Emb.fst_mem_U_iff σ E hC x _).2 ⟨y, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    · rw [← Scheme.Hom.comp_apply, pullback.lift_snd]

theorem smooth_of_forall {P S : Scheme.{0}} (p : P ⟶ S) (V : P.Opens)
    (h : ∀ z ∈ V, ∃ W : P.Opens, z ∈ W ∧ Smooth (W.ι ≫ p)) : Smooth (V.ι ≫ p) := by
  choose W hW hs using h
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) (fun z : V => V.ι ⁻¹ᵁ W z.1 z.2) ?_ fun z => ?_
  · rw [eq_top_iff]
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨z, hW z.1 z.2⟩
  · have := hs z.1 z.2
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance

theorem isPullback_of_mono {A V P S S₀ : Scheme.{0}} {i : A ⟶ V} {j : V ⟶ P} [Mono j] {a : A ⟶ S₀} {p : P ⟶ S}
    {s : S₀ ⟶ S} (h : IsPullback (i ≫ j) a p s) : IsPullback i a (j ≫ p) s := by
  have h₁ : IsPullback i (𝟙 A) j (i ≫ j) :=
    ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.snd)
      (fun c => by rw [← cancel_mono j, Category.assoc, c.condition]) (fun c => by simp)
      (fun c m _ h2 => by simpa using h2)⟩⟩
  simpa using h₁.paste_vert h

theorem exists_open (σ : Setup) (E : Emb σ) (hC : σ.Common) (x : Sp σ.R)
    (ξ' : Sp (σ.C x).R ⟶ Spec ((Sp σ.R).presheaf.stalk x)) (hξ : ξ' ≫ (Sp σ.R).fromSpecStalk x = spMap (σ.ρ x))
    [Flat ξ'] [Surjective ξ'] [QuasiCompact ξ'] :
    ∃ V : E.P.Opens, Smooth (V.ι ≫ E.p) ∧ QuasiCompact (V.ι ≫ E.p) ∧ Set.range E.ιA ⊆ (V : Set E.P) ∧
      (∀ w, pullback.fst E.p (spMap (σ.ρ x)) w ∈ E.U → pullback.fst E.p (spMap (σ.ρ x)) w ∈ V) ∧
      ∃ e : (σ.C x).G.left ⟶ V.toScheme, e ≫ V.ι = E.emb x ∧ IsPullback e (σ.C x).G.hom (V.ι ≫ E.p) (spMap (σ.ρ x)) := by
  obtain ⟨hw, hop⟩ := E.openIn x
  have sat := fst_mem_U_iff_range σ E hC x hw
  have hx : spMap (σ.ρ x) (closedPoint _) = x := by rw [← σ.hρ]; exact (σ.C x).centre
  obtain ⟨V', hV'⟩ := GlobalTheory.T.exists_open_of_saturated_local_scheme_baseChange _ _ _ E.p x ξ' _ hξ ‹_› ‹_› ‹_› _
    (pullback.lift (E.emb x) (σ.C x).G.hom hw).isOpenEmbedding.isOpen_range
    (fun w w' h hm => by rw [← sat] at hm ⊢; rwa [← h])
  obtain ⟨e', he', pb'⟩ := GlobalTheory.T.isPullback_of_open_baseChange_eq_preimage _ _ _ _ E.p _ _ _ hw hop V' hV'
  have hG : Smooth (σ.C x).G.hom := (σ.C x).semi.smooth
  have hGq : QuasiCompact (σ.C x).G.hom := (σ.C x).semi.quasiCompact
  have hA : Smooth σ.A.hom := σ.ab.smooth
  have hAp : IsProper σ.A.hom := σ.ab.proper
  have hιA : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback (P := @IsOpenImmersion) E.cartA.flip inferInstance
  have hsm : Smooth (pullback.snd (V'.ι ≫ E.p) ((Sp σ.R).fromSpecStalk x)) := by
    rw [← hξ] at pb'
    have sq : IsPullback (pullback.lift e' ((σ.C x).G.hom ≫ ξ') (by rw [pb'.w, Category.assoc])) (σ.C x).G.hom
        (pullback.snd (V'.ι ≫ E.p) ((Sp σ.R).fromSpecStalk x)) ξ' :=
      IsPullback.of_right (by rwa [pullback.lift_fst]) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      sq.flip ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ hG
  have hemb : ∀ y, pullback.fst E.p (spMap (σ.ρ x)) (pullback.lift (E.emb x) (σ.C x).G.hom hw y) = E.emb x y :=
    fun y => by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  have loc : ∀ y : (σ.C x).G.left, ∃ W : E.P.Opens, IsAffineOpen W ∧ E.emb x y ∈ W ∧ W ≤ V' ∧ Smooth (W.ι ≫ E.p) := by
    intro y
    have h1 : E.emb x y ∈ V' := by rw [← hemb, hV']; exact ⟨y, rfl⟩
    have h2 : (E.p (E.emb x y)).asIdeal ≤ x.asIdeal := by
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
      conv_rhs => rw [← hx]
      exact Ideal.comap_mono (f := σ.ρ x) (le_maximalIdeal ((σ.C x).G.hom y).isPrime.ne_top)
    obtain ⟨W₁, a₁, b₁, c₁⟩ := GlobalTheory.T.locallyOfFiniteType_near_generisation_of_point σ.R σ.f E.P σ.A.left E.p E.ιA σ.A.hom E.cartA inferInstance x V' inferInstance _ h1 h2
    obtain ⟨W₂, a₂, b₂, c₂⟩ := GlobalTheory.T.exists_smooth_nhds_of_smooth_over_local_scheme σ.R E.P E.p x V' W₁ b₁ hsm c₁ _ a₁ h2
    obtain ⟨W, a, b, c : W ≤ W₂⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp E.P.isBasis_affineOpens a₂
    refine ⟨W, a, b, c.trans (b₂.trans b₁), ?_⟩
    rw [← E.P.homOfLE_ι c, Category.assoc]
    infer_instance
  choose W hWa hWm hWle hWs using loc
  have : CompactSpace (Sp (σ.C x).R) := inferInstanceAs (CompactSpace (PrimeSpectrum _))
  have : CompactSpace (σ.C x).G.left := QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom
  have : CompactSpace σ.A.left := QuasiCompact.compactSpace_of_compactSpace σ.A.hom
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y : (σ.C x).G.left => ((E.emb x ⁻¹ᵁ W y : (σ.C x).G.left.Opens) : Set (σ.C x).G.left))
    (fun y => (E.emb x ⁻¹ᵁ W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hWm y⟩)
  let V : E.P.Opens := (⨆ y : s, W y) ⊔ E.ιA.opensRange
  have hmem : ∀ z, z ∈ V ↔ (∃ y : s, z ∈ W y) ∨ z ∈ Set.range E.ιA := fun z => by
    simp only [V, TopologicalSpace.Opens.mem_sup, TopologicalSpace.Opens.mem_iSup]; rfl
  have hV : ∀ w, pullback.fst E.p (spMap (σ.ρ x)) w ∈ V ↔ w ∈ Set.range (pullback.lift (E.emb x) (σ.C x).G.hom hw) := by
    intro w
    rw [hmem]
    constructor
    · rintro (⟨y, hy⟩ | ⟨a, ha⟩)
      · exact (hV' w).1 (hWle _ hy)
      · obtain ⟨v, hv₁, hv₂⟩ := Scheme.exists_preimage_of_isPullback (σ.cart x) a (pullback.snd E.p (spMap (σ.ρ x)) w) (by
          rw [← E.cartA.w, Scheme.Hom.comp_apply, ha, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
            pullback.condition])
        refine (sat w).1 ((Emb.fst_mem_U_iff σ E hC x w).2 ⟨(σ.V x).ι v, ?_, ?_⟩)
        · rw [← Scheme.Hom.comp_apply, ← E.onV, Scheme.Hom.comp_apply, hv₁, ha]
        · rw [← Scheme.Hom.comp_apply, hv₂]
    · rintro ⟨y, rfl⟩
      obtain ⟨y', hy', h⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
      exact Or.inl ⟨⟨y', hy'⟩, by rw [hemb]; exact h⟩
  refine ⟨V, smooth_of_forall _ _ fun z hz => ?_, ?_, fun z hz => (hmem z).2 (Or.inr hz),
    fun w h => (hV w).2 ((sat w).1 h), GlobalTheory.T.isPullback_of_open_baseChange_eq_preimage _ _ _ _ E.p _ _ _ hw hop V hV⟩
  · rcases (hmem z).1 hz with ⟨y, hy⟩ | h
    · exact ⟨_, hy, hWs _⟩
    · refine ⟨E.ιA.opensRange, h, ?_⟩
      rw [← E.ιA.isoOpensRange_inv_comp, Category.assoc, E.cartA.w]
      infer_instance
  · have hc : IsCompact (V : Set E.P) := by
      simp only [V, TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_iSup]
      exact (isCompact_iUnion fun y => (hWa _).isCompact).union (isCompact_range E.ιA.continuous)
    have : CompactSpace V.toScheme := isCompact_iff_compactSpace.1 hc
    exact (quasiCompact_iff_compactSpace _).2 this

end GlobalTheory.Desc.Spread

namespace GlobalTheory.Desc

open Spread in

theorem Emb.exists_locGrp : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ ∀ z : E.P, z ∈ E.U → x.asIdeal ≤ (E.p z).asIdeal → (E.p z).asIdeal ≤ x.asIdeal → z ∈ Set.range h := by
  intro σ E hC x
  have hx : spMap (σ.ρ x) (closedPoint _) = x := by rw [← σ.hρ]; exact (σ.C x).centre
  obtain ⟨ξ', hξ, _, _, _⟩ := GlobalTheory.T.exists_faithfullyFlat_factor_through_local_scheme _ (σ.C x).R (spMap (σ.ρ x)) x hx
    ((HasRingHomProperty.Spec_iff (P := @Flat)).2 (σ.flat x))
  obtain ⟨V, hs, hq, hA, hU, e, he, pb⟩ := exists_open σ E hC x ξ' hξ
  have := E.sep
  have hιA : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback (P := @IsOpenImmersion) E.cartA.flip inferInstance
  let i : σ.A.left ⟶ V.toScheme := IsOpenImmersion.lift V.ι E.ιA (by rwa [Scheme.Opens.range_ι])
  have hi : i ≫ V.ι = E.ιA := IsOpenImmersion.lift_fac _ _ _
  have pA : IsPullback i σ.A.hom (V.ι ≫ E.p) (awayMap σ.f) := isPullback_of_mono (hi ▸ E.cartA)
  obtain ⟨g, hg, H, _, h, ph, hm⟩ := exists_grp_near σ.R σ.f σ.hf x _ _ ξ' ‹_› ‹_› ‹_› (V.ι ≫ E.p) hs hq inferInstance σ.A σ.ab.comm
    (σ.C x).G i e pA (by rwa [hξ]) (fun T t₁ t₂ a b a' b' h₁ h₂ => by
      rw [← cancel_mono V.ι, Category.assoc, Category.assoc, he, hi]
      refine GlobalTheory.T.chart_grpLaw_agrees_with_abelian_scheme_law σ E x T t₁ t₂ a b a' b' ?_ ?_
      · rw [← he, ← hi, reassoc_of% h₁]
      · rw [← he, ← hi, reassoc_of% h₂])
  have : IsOpenImmersion h := MorphismProperty.of_isPullback (P := @IsOpenImmersion) ph.flip inferInstance
  refine ⟨g, hg, H, inferInstance, h ≫ V.ι, ⟨MorphismProperty.of_isPullback (P := @Smooth) ph hs,
    MorphismProperty.of_isPullback (P := @QuasiCompact) ph hq, inferInstance, by rw [Category.assoc, ph.w],
    fun T t₁ t₂ a b a' b' h₁ h₂ => ?_⟩, fun z hz h₁ h₂ => ?_⟩
  · rw [← hi, ← Category.assoc, ← Category.assoc, cancel_mono] at h₁ h₂ ⊢
    exact hm T t₁ t₂ a b a' b' h₁ h₂
  · have hz' : E.p z = x := PrimeSpectrum.ext (le_antisymm h₂ h₁)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := E.p) (g := spMap (σ.ρ x)) z (closedPoint _)
      (hz'.trans hx.symm)
    have hV : z ∈ V := hw ▸ hU w (hw ▸ hz)
    obtain ⟨u, hu⟩ : x ∈ Set.range (awayMap g) := by
      change x ∈ Set.range (PrimeSpectrum.comap (algebraMap σ.R (Localization.Away g)))
      rw [PrimeSpectrum.localization_away_comap_range _ g]
      exact hg
    obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback ph (⟨z, hV⟩ : V.toScheme) u (by
      rw [hu]; exact (Scheme.Hom.comp_apply _ _ _).trans hz')
    exact ⟨v, by rw [Scheme.Hom.comp_apply, hv]; rfl⟩

end GlobalTheory.Desc
