import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRepresents
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsDerivAtOfSurjective
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

noncomputable section

namespace GlobalTheory.ExpTan

section General

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HolHom GlobalTheory.TorusModel GlobalTheory.ArcQ

section Deriv

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
  {X : Scheme.{0}}

theorem isDerivAt_precomp {c : V → (Sp ℂ ⟶ X)} (L : V' →L[ℂ] V) (h : HolAt c 0) (w : V')
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt (fun t => c (L t)) 0 w v ↔ IsDerivAt c 0 (L w) v := by
  unfold IsDerivAt
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_)
  have h₁ : HasFDerivAt (fun t => valAt' (c t) U f) (fderiv ℂ (fun t => valAt' (c t) U f) 0) (L 0) := by
    rw [map_zero]; exact ((h U hU).2 f).hasFDerivAt
  have h₂ := (h₁.comp 0 L.hasFDerivAt).fderiv
  rw [show fderiv ℂ (fun t => valAt' (c (L t)) U f) 0 = _ from h₂]
  rfl

theorem isDerivAt_smul {c : V → (Sp ℂ ⟶ X)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt c z w v) (a : ℂ) :
    IsDerivAt c z (a • w) (spMap (epsScaleR a) ≫ v) := by
  refine ⟨Eq.trans ?_ h.1, fun U hU f => ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => spMap q ≫ v) (RingHom.ext fun x => by simp [epsScaleR])
  · rw [valR_spMap _ _ _ ((le_preimage_dual_iff h.1 U).2 hU), map_smul, ← h.2 U hU f]
    simp [epsScaleR]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {e : V → (Over.mk y ⟶ G)}

theorem isDerivAt_add (he : ∀ z w, e (z + w) = e z * e w) (hol : HolAt (fun z => (e z).left) 0)
    {s : Sp (DualNumber ℂ) ⟶ S} (hs : s = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) {v v' : Over.mk s ⟶ G} {w w' : V}
    (h : IsDerivAt (fun z => (e z).left) 0 w v.left) (h' : IsDerivAt (fun z => (e z).left) 0 w' v'.left) :
    IsDerivAt (fun z => (e z).left) 0 (w + w') (v * v').left := by
  subst hs
  have := isDerivAt_mul (a := fun p : V × V => e p.1) (b := fun p : V × V => e p.2) (z := 0) (w := (w, w'))
    (HolAt.precomp (c := fun z => (e z).left) (k := fun p : V × V => p.1) hol differentiableAt_fst)
    (HolAt.precomp (c := fun z => (e z).left) (k := fun p : V × V => p.2) hol differentiableAt_snd)
    ((isDerivAt_precomp (ContinuousLinearMap.fst ℂ V V) hol (w, w') _).2 h)
    ((isDerivAt_precomp (ContinuousLinearMap.snd ℂ V V) hol (w, w') _).2 h')
  simp only [← he] at this
  exact (isDerivAt_precomp (ContinuousLinearMap.fst ℂ V V + ContinuousLinearMap.snd ℂ V V) hol (w, w') _).1 this

theorem eq_of_isDerivAt (he : ∀ z w, e (z + w) = e z * e w) (hol : IsHolTo Set.univ (fun z => (e z).left))
    {v : Sp (DualNumber ℂ) ⟶ G.left} {w w' : V}
    (h : IsDerivAt (fun z => (e z).left) 0 w v) (h' : IsDerivAt (fun z => (e z).left) 0 w' v) (t : ℂ) :
    e (t • w) = e (t • w') := by
  have H := fun z => holAt_of_isHolTo hol (Set.mem_univ z)
  have key : ∀ w : V, IsDerivAt (fun z => (e z).left) 0 w v →
      IsDerivAt (fun t : ℂ => (e (t • w)).left) 0 1 v := fun w h =>
    (isDerivAt_precomp (ContinuousLinearMap.toSpanSingleton ℂ w) (H 0) 1 v).2 (by simpa using h)
  have hh : ∀ w : V, IsHolTo Set.univ (fun t : ℂ => (e (t • w)).left) := fun w =>
    isHolTo_of_holAt isOpen_univ fun t _ => HolAt.precomp (c := fun z => (e z).left) (k := fun t : ℂ => t • w) (H _)
      (differentiableAt_id.smul_const w)
  refine congrFun (eq_of_fderiv_eq (e := fun t : ℂ => e (t • w)) (e' := fun t : ℂ => e (t • w'))
    (fun a b => by rw [add_smul, he]) (fun a b => by rw [add_smul, he]) (hh w) (hh w') fun U hU f => ?_) t
  refine ContinuousLinearMap.ext_ring (((key w h).2 U hU f).symm.trans ((key w' h').2 U ?_ f))
  simpa using hU

end Deriv

section Pts

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Sp R)}

theorem isZero_unique {g g' : GtPt D T} (h : g.IsZero) (h' : g'.IsZero) : g = g' :=
  pt_ext (h.1.trans h'.1.symm) fun χ _ _ hJ => (val_corr hJ (h.2 χ) _).trans (val_corr hJ (h'.2 χ) _).symm

variable {H : Over (Sp R)} [GrpObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

theorem isZero_one (hΦ : Represents Φ) (T : Over (Sp R)) : (Φ T 1).IsZero := by
  have h := hΦ.2 T 1 1
  rw [_root_.mul_one, TorusModel.isAdd_iff] at h
  have hb : (Φ T 1).b = 1 := left_eq_mul.1 h.1
  refine ⟨hb, fun χ => corr_of_val D.P.isLB fun y J hJ => Eq.trans ?_ (val_one _).symm⟩
  have := h.2 χ y J hJ
  have C : IsCub (DVR.th D (T := T) y J) := isCub_cubV D.cub hJ
  rw [show DVR.th D y J (DVR.cP D T χ) (Φ T 1).b (Φ T 1).b = 1 by rw [hb, C.face₃]] at this
  exact (mul_left_cancel this).symm

theorem isZero_iff_eq_one (hΦ : Represents Φ) (x : T ⟶ H) : (Φ T x).IsZero ↔ x = 1 :=
  ⟨fun h => (Φ T).injective (isZero_unique h (isZero_one hΦ T)), fun h => h ▸ isZero_one hΦ T⟩

theorem univ_val (hΦ : Represents Φ) {A : Type} [CommRing A] {s : Sp A ⟶ Sp R} (x : Over.mk s ⟶ H) :
    (Φ _ x).b.left = x.left ≫ (Φ H (𝟙 H)).b.left ∧ ∀ χ j,
      (⊤ ≤ LB.wchart D.P.L (DegPre.gtφT D _ (Φ _ x).b χ) j ↔
        ⊤ ≤ x.left ⁻¹ᵁ LB.wchart D.P.L (DegPre.gtφT D H (Φ H (𝟙 H)).b χ) j) ∧
      valR (A := A) (𝟙 _) (LB.wchart D.P.L (DegPre.gtφT D _ (Φ _ x).b χ) j) (((Φ _ x).s χ).s j).val =
        valR (A := A) x.left (LB.wchart D.P.L (DegPre.gtφT D H (Φ H (𝟙 H)).b χ) j) (((Φ H (𝟙 H)).s χ).s j).val := by
  have h := hΦ.1 _ _ x (𝟙 H)
  rw [Category.comp_id] at h
  refine ⟨h.1, fun χ j => ?_⟩
  have hφ : DegPre.gtφT D _ (Φ _ x).b χ = fun k => x.left ≫ DegPre.gtφT D H (Φ H (𝟙 H)).b χ k :=
    funext fun k => (ConstTanRed.comp_gtφT D x _ _ (Over.OverMorphism.ext h.1.symm) χ k).symm
  exact ⟨by rw [hφ]; exact le_wchart_iff _ _ _ _,
    valR_of_corr (A := A) D.P.isLB ((Φ _ x).isGen χ) ((Φ H (𝟙 H)).isGen χ) x.left hφ (h.2 χ) j⟩

end Pts

variable {D : DegPre ℂ} {y : Sp ℂ ⟶ Sp ℂ} {g : ℕ}

def coordVal (p : GtPt D (Over.mk y)) (x : D.X) (j : Fin 4 → D.P.L.ι) : ℂ :=
  valR (A := ℂ) (𝟙 _) (LB.wchart D.P.L (DegPre.gtφT D _ p.b x) j) ((p.s x).s j).val

def IsJet (ex : (Fin g → ℂ) → GtPt D (Over.mk y)) (ν : GtPt D (epsR ℂ)) (w : Fin g → ℂ) : Prop :=
  IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) w ν.b.left ∧
    ∀ x j, ⊤ ≤ LB.wchart D.P.L (DegPre.gtφT D (epsR ℂ) ν.b x) j →
      valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val =
        TrivSqZeroExt.inl (coordVal (ex 0) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => coordVal (ex z) x j) 0 w)

theorem IsJet.unique {ex : (Fin g → ℂ) → GtPt D (Over.mk y)} {ν ν' : GtPt D (epsR ℂ)} {w : Fin g → ℂ}
    (h : IsJet ex ν w) (h' : IsJet ex ν' w) : ν = ν' := by
  obtain ⟨b, s, _, _, _⟩ := ν
  obtain ⟨b', s', _, _, _⟩ := ν'
  obtain rfl : b = b' := Over.OverMorphism.ext
    (((isDerivAt0_iff _ _ _).1 h.1).unique ((isDerivAt0_iff _ _ _).1 h'.1))
  have hs : ∀ χ j, (s χ).s j = (s' χ).s j := fun χ j => unit_ext fun p hp => by
    have hp' : ∀ q : Sp (DualNumber ℂ), q = p := fun q => by
      obtain ⟨q, rfl⟩ := TangentOrigin.spMap_fst_surjective q
      obtain ⟨p, rfl⟩ := TangentOrigin.spMap_fst_surjective p
      exact congrArg _ (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _)
    have hj : ⊤ ≤ 𝟙 (Sp (DualNumber ℂ)) ⁻¹ᵁ LB.wchart D.P.L (DegPre.gtφT D (epsR ℂ) b χ) j := fun q _ => (hp' q).symm ▸ hp
    refine Units.ext ((toStkA_valR (A := DualNumber ℂ) (𝟙 _) _ p hj _).symm.trans (Eq.trans ?_
      (toStkA_valR (A := DualNumber ℂ) (𝟙 _) _ p hj _)))
    exact congrArg _ ((h.2 χ j hj).trans (h'.2 χ j hj).symm)
  obtain rfl : s = s' := funext fun χ => congrArg LB.Gen.mk (funext (hs χ))
  rfl

variable {H : Over (Sp ℂ)} [GrpObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T} {e : (Fin g → ℂ) → (Over.mk y ⟶ H)}

theorem isJet_of_isDerivAt (hΦ : Represents Φ) {v : epsR ℂ ⟶ H} {w : Fin g → ℂ}
    (h : IsDerivAt (fun z => (e z).left) 0 w v.left) : IsJet (fun z => Φ _ (e z)) (Φ _ v) w := by
  refine ⟨(isDerivAt0_iff _ _ _).2 ?_, fun x j hj => ?_⟩
  · have := h.comp (Φ H (𝟙 H)).b.left
    rw [(univ_val hΦ v).1]
    simpa only [(univ_val hΦ (e _)).1] using this
  · have hU := (le_preimage_dual_iff h.1 _).1 ((((univ_val hΦ v).2 x j).1).1 hj)
    refine ((univ_val hΦ v).2 x j).2.trans ?_
    simp only [coordVal, ((univ_val hΦ (e _)).2 x j).2]
    ext
    · exact (fst_valR h.1 hU _).trans (by rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]; rfl)
    · exact (h.2 _ hU _).trans (by rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]; rfl)

theorem exists_isDerivAt' (hy : y = 𝟙 _) (hol : HolAt (fun z => (e z).left) 0) (w : Fin g → ℂ) :
    ∃ v : epsR ℂ ⟶ H, IsDerivAt (fun z => (e z).left) 0 w v.left := by
  obtain ⟨v, hv⟩ := hol.exists_isDerivAt w
  exact ⟨Over.homMk v (hv.over.trans (by subst hy; exact Category.comp_id _)), hv⟩

theorem isJet_iff (hΦ : Represents Φ) (hy : y = 𝟙 _) (hol : HolAt (fun z => (e z).left) 0) (v : epsR ℂ ⟶ H)
    (w : Fin g → ℂ) : IsJet (fun z => Φ _ (e z)) (Φ _ v) w ↔ IsDerivAt (fun z => (e z).left) 0 w v.left := by
  refine ⟨fun h => ?_, isJet_of_isDerivAt hΦ⟩
  obtain ⟨v', hv'⟩ := exists_isDerivAt' hy hol w
  rwa [(Φ _).injective (h.unique (isJet_of_isDerivAt hΦ hv'))]

theorem gtTanR_iff (hΦ : Represents Φ) (v : epsR ℂ ⟶ H) : GtTanR (Φ _ v) ↔
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ H).left := by
  let ρ : Over.mk (𝟙 (Sp ℂ)) ⟶ epsR ℂ := Over.homMk (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    ((congrArg _ (Category.comp_id _).symm).trans (fst_constVec (𝟙 (Sp ℂ))))
  have h := hΦ.1 _ _ ρ v
  constructor
  · rintro ⟨g₀, h₀, h₁⟩
    obtain rfl := isPull_unique (k := ρ) h h₁
    exact congrArg (fun q => q.left) ((isZero_iff_eq_one hΦ _).1 h₀)
  · exact fun h₀ => ⟨_, (isZero_iff_eq_one hΦ _).2 (Over.OverMorphism.ext h₀), h⟩

theorem core (hG : GlobalFnsSt) (hy : y = 𝟙 _) (ex : (Fin g → ℂ) → GtPt D (Over.mk y))
    (add : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) (onto : Function.Surjective ex)
    (hb : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)))
    (hs : ∀ x j, DifferentiableOn ℂ (fun z => coordVal (ex z) x j)
      {z | ⊤ ≤ LB.wchart D.P.L (DegPre.gtφT D _ (ex z).b x) j})
    (ker : {z | (ex z).IsZero}.Countable) :
    (∀ ν, GtTanR ν → ∃! z₀, IsJet ex ν z₀) ∧ (∀ z₀, ∃! ν, IsJet ex ν z₀) ∧ (∀ ν z₀, IsJet ex ν z₀ → GtTanR ν) ∧
      ∀ (m : ℕ) (cf : Fin m → ℂ) (v : Fin m → GtPt D (epsR ℂ)) (z : Fin m → (Fin g → ℂ)) ν,
        (∀ i, IsJet ex (v i) (z i)) → (GtComb cf v ν ↔ IsJet ex ν (∑ i, cf i • z i)) := by
  subst hy
  obtain ⟨H, _, Φ, hsm, hΦ, hH⟩ := exists_model hG D
  obtain ⟨e, rfl⟩ : ∃ e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ H), ex = fun z => Φ _ (e z) :=
    ⟨fun z => (Φ _).symm (ex z), funext fun z => ((Φ _).apply_symm_apply _).symm⟩
  have he : ∀ z w, e (z + w) = e z * e w := fun z w => (Φ _).injective (isAdd_unique (add z w) (hΦ.2 _ _ _))
  have he0 : e 0 = 1 := map_zero_eq_one he
  have hol : ∀ z, HolAt (fun z => (e z).left) z := fun z => by
    refine hH _ _ e z (holAt_of_isHolTo hb (Set.mem_univ z)) fun χ j hj => (hs χ j).differentiableAt ?_
    have key : ∀ t, ⊤ ≤ LB.wchart D.P.L (DegPre.gtφT D _ (Φ _ (e t)).b χ) j ↔
        ⊤ ≤ (Φ _ (e t)).b.left ⁻¹ᵁ LB.wchart D.P.L (DegPre.gtφT D _ (𝟙 D.P.A) χ) j := fun t => by
      rw [← le_wchart_iff, funext (ConstTanRed.comp_gtφT D (Φ _ (e t)).b _ _ (Category.comp_id _) χ)]
    exact (holAt_of_isHolTo hb (Set.mem_univ z) _ ((key z).1 hj)).1.mono fun t ht => (key t).2 ht
  have hol' : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (e z).left)) :=
    isHolTo_of_holAt isOpen_univ fun z _ => hol z
  have iff := isJet_iff hΦ rfl (hol 0)
  have ex₁ : ∀ w, ∃ ν, IsJet (fun z => Φ _ (e z)) ν w := fun w =>
    let ⟨v, hv⟩ := exists_isDerivAt' rfl (hol 0) w
    ⟨_, (iff v w).2 hv⟩
  refine ⟨fun ν hν => ?_, fun w => existsUnique_of_exists_of_unique (ex₁ w) fun _ _ => IsJet.unique,
    fun ν w h => ?_, fun m cf v z ν hv => ?_⟩
  · obtain ⟨v, rfl⟩ := (Φ _).surjective ν
    obtain ⟨w, hw⟩ := GlobalTheory.HolHomOnto.exists_isDerivAt_of_surjective H _ rfl hsm g e he
      (fun x => let ⟨z, hz⟩ := onto (Φ _ x); ⟨z, (Φ _).injective hz⟩) hol' v.left (Over.w v)
      (((gtTanR_iff hΦ v).1 hν).trans (by rw [he0]))
    refine ⟨w, (iff v w).2 hw, fun w' h' => by_contra fun hne => ?_⟩
    have h₁ : ∀ t : ℂ, t • (w' - w) ∈ {z | (Φ _ (e z)).IsZero} := fun t => by
      refine (isZero_iff_eq_one hΦ _).2 (mul_right_cancel (b := e (t • w)) ?_)
      rw [← he, _root_.one_mul, ← smul_add, sub_add_cancel]
      exact eq_of_isDerivAt he hol' ((iff v w').1 h') hw t
    have h₂ : (Set.univ : Set ℂ).Countable :=
      (ker.preimage_of_injOn (f := fun t : ℂ => t • (w' - w))
        (smul_left_injective ℂ (sub_ne_zero.2 hne)).injOn).mono fun t _ => h₁ t
    exact not_countable_complex h₂
  · obtain ⟨v, rfl⟩ := (Φ _).surjective ν
    exact (gtTanR_iff hΦ v).2 (((iff v w).1 h).1.trans (congrArg (fun q => q.left) he0))
  · have zero : ∀ p : GtPt D (epsR ℂ), p.IsZero → IsJet (fun z => Φ _ (e z)) p 0 := fun p hp => by
      rw [isZero_unique hp (isZero_one hΦ _), iff]
      have : (1 : epsR ℂ ⟶ H).left = constVec (e 0).left := by
        rw [he0]
        exact congrArg (fun q : epsR ℂ ⟶ H => q.left) (MonObj.comp_one
          (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) (Category.comp_id _) : epsR ℂ ⟶ Over.mk (𝟙 (Sp ℂ)))).symm
      rw [this]
      exact isDerivAt_constVec_iff.2 fun _ _ _ => map_zero _
    have plus : ∀ p p' p'' w w', IsJet (fun z => Φ _ (e z)) p w → IsJet (fun z => Φ _ (e z)) p' w' →
        (GtPt.IsAdd p p' p'' ↔ IsJet (fun z => Φ _ (e z)) p'' (w + w')) := fun p p' p'' w w' h h' => by
      obtain ⟨a, rfl⟩ := (Φ _).surjective p
      obtain ⟨a', rfl⟩ := (Φ _).surjective p'
      have h₁ := (iff _ _).2 (isDerivAt_add he (hol 0) (Category.comp_id _).symm ((iff _ _).1 h) ((iff _ _).1 h'))
      exact ⟨fun q => isAdd_unique (hΦ.2 _ a a') q ▸ h₁, fun q => h₁.unique q ▸ hΦ.2 _ a a'⟩
    have scale : ∀ (c : ℂ) p p' w, IsJet (fun z => Φ _ (e z)) p w →
        (GtPt.IsPull (spMap (epsScaleR c)) p p' ↔ IsJet (fun z => Φ _ (e z)) p' (c • w)) := fun c p p' w h => by
      obtain ⟨a, rfl⟩ := (Φ _).surjective p
      let κ : epsR ℂ ⟶ epsR ℂ := Over.homMk (spMap (epsScaleR c)) (by
        show spMap (epsScaleR c) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = spMap (algebraMap ℂ (DualNumber ℂ))
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg spMap (RingHom.ext fun x => (TrivSqZeroExt.map _).commutes x))
      have h₁ := (iff (κ ≫ a) _).2 (isDerivAt_smul ((iff _ _).1 h) c)
      exact ⟨fun q => isPull_unique (k := κ) (hΦ.1 _ _ κ a) q ▸ h₁, fun q => h₁.unique q ▸ hΦ.1 _ _ κ a⟩
    let ps : Fin (m + 1) → (Fin g → ℂ) := Fin.partialSum fun i => cf i • z i
    have hl : ps (Fin.last m) = ∑ i, cf i • z i := by
      simp only [ps, Fin.partialSum, Fin.val_last]
      rw [List.take_of_length_le (by simp), List.sum_ofFn]
    constructor
    · rintro ⟨u, p, hu, h₀, hp, rfl⟩
      rw [← hl]
      refine Fin.induction (motive := fun k => IsJet (fun z => Φ _ (e z)) (p k) (ps k)) ?_ (fun i ih => ?_) _
      · simpa only [ps, Fin.partialSum_zero] using zero _ h₀
      · simpa only [ps, Fin.partialSum_succ] using (plus _ _ _ _ _ ih ((scale _ _ _ _ (hv i)).1 (hu i))).1 (hp i)
    · intro h
      choose J hJ using ex₁
      refine ⟨fun i => J (cf i • z i), fun k => J (ps k), fun i => (scale _ _ _ _ (hv i)).2 (hJ _), ?_,
        fun i => (plus _ _ _ _ _ (hJ _) (hJ _)).2 ?_, (hJ _).unique (hl ▸ h)⟩
      · have := (zero _ (isZero_one hΦ _)).unique (hJ 0)
        simp only [ps, Fin.partialSum_zero, ← this]
        exact isZero_one hΦ _
      · simpa only [ps, Fin.partialSum_succ] using hJ (ps i.succ)

def toPt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (p : GtPtF D F) : GtPt D (TF (R := R) F) := ⟨p.b, p.s, p.isGen, p.s_zero, p.mult⟩

end General

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem anVec_bijective : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), (∀ ν, GtTanR ν → ∃! z₀, AnVec Ha ν z₀) ∧ (∀ z₀, ∃! ν, AnVec Ha ν z₀) ∧ (∀ ν z₀, AnVec Ha ν z₀ → GtTanR ν) ∧ ∀ (m : ℕ) (cf : Fin m → ℂ) (e : Fin m → Out.GtPt a.D₀ (epsR ℂ)) (z : Fin m → (Fin g → ℂ)) ν, (∀ i, AnVec Ha (e i) (z i)) → (GtComb cf e ν ↔ AnVec Ha ν (∑ i, cf i • z i)) := by
  intro hG E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha
  have hy : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact Spec.map_id _
  have hO : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  have := (Fu.Di Ha.i).fin
  have hL : Countable (Fu.Di Ha.i).La := Finsupp.Countable.of_moduleFinite (R := 𝓞 E)
  exact core hG hy (fun z => toPt (Ha.ex₀ z)) Ha.add
    (fun p => let ⟨z, hz⟩ := Ha.onto ⟨p.b, p.s, p.isGen, p.s_zero, p.mult⟩; ⟨z, congrArg toPt hz⟩) Ha.hol_b Ha.hol_chi
    ((Set.countable_range Ha.P₀).mono fun z hz => ((Ha.ker z).1 hz).elim fun v h => Set.mem_range.2 ⟨v, h.2.symm⟩)

end GlobalTheory.ExpTan
