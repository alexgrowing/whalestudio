import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrVal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntGaugePull

theorem top_le_of_redE {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp (DualNumber A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (redE A ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro z _
  let w : Sp A := (Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A)))).base z
  have hw : (redE A).base w = z := by
    simp only [w, redE, spMap, Spec.map_base]
    refine PrimeSpectrum.ext (Ideal.ext fun t => ?_)
    simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      CommRingCat.hom_ofHom]
    have hn : TrivSqZeroExt.inr (TrivSqZeroExt.snd t) ∈ z.asIdeal := by
      apply z.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact z.asIdeal.zero_mem
    have ht : t = algebraMap A (DualNumber A) ((TrivSqZeroExt.fstHom A A A).toRingHom t) +
        TrivSqZeroExt.inr (TrivSqZeroExt.snd t) := by
      rw [TrivSqZeroExt.algebraMap_eq_inl]; exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq t).symm
    constructor
    · intro h1; rw [ht]; exact z.asIdeal.add_mem h1 hn
    · intro h1
      have e : algebraMap A (DualNumber A) ((TrivSqZeroExt.fstHom A A A).toRingHom t) =
          t - TrivSqZeroExt.inr (TrivSqZeroExt.snd t) := eq_sub_of_add_eq ht.symm
      change algebraMap A (DualNumber A) ((TrivSqZeroExt.fstHom A A A).toRingHom t) ∈ z.asIdeal
      rw [e]; exact z.asIdeal.sub_mem h1 hn
  have := h (show w ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← hw]
  exact this

theorem sep_unique {C : Type} [Field C] (S : ValuationSubring C) {X Y : Scheme.{0}} (p : X ⟶ Y) [IsSeparated p]
    (x₁ x₂ : Sp S ⟶ X) (h₁ : x₁ ≫ p = x₂ ≫ p) (h : spMap S.subtype ≫ x₁ = spMap S.subtype ≫ x₂) : x₁ = x₂ := by
  have hU : ValuativeCriterion.Uniqueness p := IsSeparated.valuativeCriterion p
  let Q : ValuativeCommSq p :=
    { R := S, K := C, i₁ := Spec.map (CommRingCat.ofHom (algebraMap S C)) ≫ x₁, i₂ := x₁ ≫ p,
      commSq := ⟨by rw [Category.assoc]⟩ }
  have := (hU Q).elim ⟨x₁, rfl, rfl⟩ ⟨x₂, h.symm, h₁.symm⟩
  exact congrArg CommSq.LiftStruct.l this

theorem spMap_subtype_cancel {C : Type} [Field C] (S : ValuationSubring C) {A : Type} [CommRing A]
    (f g : Sp S ⟶ Sp A) (h : spMap S.subtype ≫ f = spMap S.subtype ≫ g) : f = g := by
  obtain ⟨f', rfl⟩ := Spec.map_surjective f
  obtain ⟨g', rfl⟩ := Spec.map_surjective g
  simp only [spMap, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  have := congrArg (fun u => u.hom a) h'
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

end GlobalTheory.IntGaugePull

namespace GlobalTheory.IntGaugePull

theorem spMap_comp_spMap {A B E : Type} [CommRing A] [CommRing B] [CommRing E] (f : B →+* E) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem redE_dual {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    redE B ≫ spMap (dualMap f) = spMap f ≫ redE A := by
  simp only [redE, spMap_comp_spMap]
  congr 1
  ext z <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp {A B E : Type} [CommRing A] [CommRing B] [CommRing E] (f : B →+* E) (g : A →+* B) :
    spMap (dualMap f) ≫ spMap (dualMap g) = spMap (dualMap (f.comp g)) := by
  rw [spMap_comp_spMap]
  congr 1
  ext z <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem famφB_hom {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (β : D.X) (i : Fin 4) :
    D.famφB β i ≫ D.P.A.hom = D.P.A.hom := by
  fin_cases i
  · exact Category.id_comp _
  all_goals exact Over.w _

end GlobalTheory.IntGaugePull

namespace GlobalTheory.IntGaugePull

theorem sE_norm_le_one_of_pull : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ) (β : D.toPre.X) (σ : D.toPre.SecB k β) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) σF (D.toPre.famφB β) (DegPre.famε k) σ (DegPre.prB D.toPre C).left 1 → ∀ (Q : Sp (DualNumber V) ⟶ D.toPre.P.A.left), Q ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) → ∀ (r : Sp (DualNumber C) ⟶ (DegPre.BF D.toPre C).left), r ≫ (DegPre.prB D.toPre C).left = spMap (dualMap (toF V C)) ≫ Q → ‖(sE σF r ν.J).fst‖ ≤ 1 ∧ ‖(sE σF r ν.J).snd‖ ≤ 1 := by
  intro V _ _ _ D C _ _ hC N ν hI k β σ σF hS Q hQ r hr
  obtain ⟨S, hSmem, hInt⟩ := hI
  have hle : ∀ v : V, toF V C v ∈ S := fun v => (hSmem _).2 (hC.1 v)
  let toS : V →+* S := (toF V C).codRestrict S hle
  have htoS : S.subtype.comp toS = toF V C := by ext v; rfl
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have hpt : ∀ i : Fin 4, ⊤ ≤ (spMap (dualMap toS) ≫ Q ≫ D.toPre.famφB β i) ⁻¹ᵁ
      D.toPre.P.L.U (ν.J (redE C ≫ spMap (dualMap (toF V C)) ≫ Q ≫ D.toPre.famφB β i)) := by
    intro i
    have hQi : (Q ≫ D.toPre.famφB β i) ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) := by
      rw [Category.assoc, famφB_hom, hQ]
    let xi : TF (R := V) C ⟶ D.toPre.P.A :=
      Over.homMk (redE C ≫ spMap (dualMap (toF V C)) ≫ Q ≫ D.toPre.famφB β i) (by
        simp only [Category.assoc]
        rw [famφB_hom, hQ, spMap_comp_spMap, redE, spMap_comp_spMap]
        simp only [TF, Over.mk_hom, jFK, jK]
        rw [← Spec.map_comp]
        congr 1
        ext v
        simp [dualMap, toF, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl)
    obtain ⟨x₀, hx₀, hU⟩ := hInt xi
    have hxy : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ (spMap toS ≫ redE V ≫ Q ≫ D.toPre.famφB β i) := by
      rw [hx₀]
      simp only [xi, Over.homMk_left]
      rw [← Category.assoc (spMap S.subtype), spMap_comp_spMap, htoS, ← Category.assoc, redE_dual, Category.assoc]
    have heq : x₀ = spMap toS ≫ redE V ≫ Q ≫ D.toPre.famφB β i :=
      sep_unique S D.toPre.P.A.hom _ _ (spMap_subtype_cancel S _ _ (by simp only [← Category.assoc] at hxy ⊢; rw [hxy])) hxy
    apply top_le_of_redE
    rw [← Category.assoc, redE_dual, Category.assoc, ← heq]
    exact hU

  have hj : ∀ i, ν.J (redE C ≫ r ≫ D.toPre.famφ C β i) =
      ν.J (redE C ≫ spMap (dualMap (toF V C)) ≫ Q ≫ D.toPre.famφB β i) := by
    intro i; rw [ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq, ← Category.assoc r, hr, Category.assoc]
  unfold sE
  set j : Fin 4 → D.toPre.P.L.ι := fun k => ν.J (redE C ≫ r ≫ D.toPre.famφ C β k) with hjdef
  have hQ' : ⊤ ≤ (spMap (dualMap toS) ≫ Q) ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := by
    intro z _
    show (spMap (dualMap toS) ≫ Q).base z ∈ ⋂ k, (D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _)
    refine Set.mem_iInter.2 fun i => ?_
    have := hpt i (show z ∈ (⊤ : (Sp (DualNumber S)).Opens) from trivial)
    rw [← hj i] at this
    exact this
  obtain ⟨hrB0, hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (dualMap S.subtype) (spMap (dualMap toS) ≫ Q) _ hQ'
  have hrq : spMap (dualMap S.subtype) ≫ spMap (dualMap toS) ≫ Q = r ≫ (D.toPre.prB C).left := by
    rw [← Category.assoc, dualMap_comp, htoS, hr]
  rw [hrq] at hrB0 hval

  have hW2 : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j :=
by
    intro z hz
    have h' : (r ≫ (D.toPre.prB C).left).base z ∈
        ⋂ k, (D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _) := hrB0 hz
    show r.base z ∈ ⋂ k, ((D.toPre.prB C).left ≫ D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _)
    exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 h' k
  have hWeq : LB.wchart D.toPre.P.L (D.toPre.famφ C β) j =
      LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j :=
    congrArg (fun φ => LB.wchart D.toPre.P.L φ j) (funext (ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq D.toPre C β))
  have hW1 : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφ C β) j := hWeq ▸ hW2
  have hW : ⊤ ≤ r ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφ C β) j ⊓
      LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j) :=
    fun z hz => ⟨hW1 hz, hW2 hz⟩
  have hcoh : D.toPre.P.L.Coh (Sum.elim (D.toPre.famφ C β) fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k)
      (Sum.elim j j) := by
    have key : ∀ a, Sum.elim j j a = ν.J (redE C ≫ r ≫ (Sum.elim (D.toPre.famφ C β)
        (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) a)) := by
      rintro (a | a)
      · rfl
      · simp only [Sum.elim_inr, hjdef]; rw [ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq]
    intro a b hab; rw [key a, key b, hab]
  have E := hS j j hcoh
  simp only [map_one, _root_.one_mul] at E

  have hv : valR r (LB.wchart D.toPre.P.L (D.toPre.famφ C β) j) (σF.f j) =
      dualMap S.subtype (valR (spMap (dualMap toS) ≫ Q) (LB.wchart D.toPre.P.L (D.toPre.famφB β) j) (σ.f j)) := by
    refine Eq.trans ?_ (hval (σ.f j))
    have hrB1 : ⊤ ≤ r ⁻¹ᵁ (D.toPre.prB C).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) j :=
      fun z hz => hrB0 hz
    refine Eq.trans ?_ (GlobalTheory.ZH.EvCrd.valR_comp r (D.toPre.prB C).left
      (LB.wchart D.toPre.P.L (D.toPre.famφB β) j) hrB1 (σ.f j))
    have hle2 : LB.wchart D.toPre.P.L (D.toPre.famφ C β) j ⊓
        LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j ≤
        (D.toPre.prB C).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := by
      intro z hz
      have h' : z ∈ ⋂ k, ((D.toPre.prB C).left ≫ D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _) := hz.2
      show (D.toPre.prB C).left.base z ∈ ⋂ k, (D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _)
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 h' k
    refine Eq.trans (GlobalTheory.ZH.CrdCalc.valR_res r inf_le_left hW (σF.f j)).symm ?_
    refine Eq.trans ?_ (GlobalTheory.ZH.CrdCalc.valR_res r hle2 hW _)
    congr 1
    exact E.symm
  rw [hv]
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add]
  exact ⟨(hSmem _).1 (Subtype.prop _), (hSmem _).1 (Subtype.prop _)⟩

end GlobalTheory.IntGaugePull

end
