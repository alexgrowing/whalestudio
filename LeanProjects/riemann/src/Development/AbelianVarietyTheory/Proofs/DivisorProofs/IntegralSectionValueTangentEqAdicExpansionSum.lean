import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

open IsLocalRing GlobalTheory.FormalValue

theorem isLocalRing_dualNumber (V : Type) [CommRing V] [IsLocalRing V] : IsLocalRing (DualNumber V) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

theorem thick_closedPoint (V : Type) [CommRing V] [IsLocalRing V] [IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1))] :
    thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))) = closedPoint V := by
  show PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal V ^ (0 + 1))) (closedPoint _) = closedPoint V
  refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
  haveI : (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem pow_map_le_ker (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    (m.map (algebraMap V (DualNumber V))) ^ (e + 1) ≤
      RingHom.ker ((Ideal.Quotient.mk (m ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) := by
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact ha

theorem ker_dualMap_le (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    RingHom.ker (dualMap (Ideal.Quotient.mk (m ^ (e + 1)))) ≤ (m.map (algebraMap V (DualNumber V))) ^ (e + 1) := by
  intro z hz
  rw [RingHom.mem_ker] at hz
  have h₁ : Ideal.Quotient.mk (m ^ (e + 1)) z.fst = 0 := by
    have := congrArg TrivSqZeroExt.fst hz
    simpa [dualMap] using this
  have h₂ : Ideal.Quotient.mk (m ^ (e + 1)) z.snd = 0 := by
    have := congrArg TrivSqZeroExt.snd hz
    simpa [dualMap] using this
  rw [Ideal.Quotient.eq_zero_iff_mem] at h₁ h₂
  rw [← Ideal.map_pow]
  have hz' : z = algebraMap V (DualNumber V) z.fst + algebraMap V (DualNumber V) z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hz']
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem dualMap_surjective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (dualMap f) := by
  intro w
  obtain ⟨a, ha⟩ := hf w.fst
  obtain ⟨b, hb⟩ := hf w.snd
  refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, ?_⟩
  ext <;> simp [dualMap, ha, hb]

theorem value_mul_sumI : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → ∀ (k : ℕ) (jG : U.LG.L.ι) (J : (Sp (DualNumber V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J ψ)) → ∃ W : (DualNumber V)ˣ, (W : DualNumber V).fst * GlobalTheory.MBLow.TanExp.rigVal U.LG jG = GlobalTheory.MBLow.TanExp.rigValD D.toPre (J gm₀.b.left) ∧ ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.toUnifPre.ExpandsAt e k σ f) → GlobalTheory.UT.SumI (IsLocalRing.maximalIdeal V) (fun α => GlobalTheory.MBLow.TanExp.termV J gm₀ (f α)) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) (σ.f fun _ => jG)) := by
  intro V _ _ _ _ hV D A G _ _ _ U y gm₀ hy hT k jG J hjG hJ
  haveI : IsLocalRing (DualNumber V) := isLocalRing_dualNumber V
  haveI : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  haveI : IsAdicComplete (maximalIdeal V) V := hV
  haveI hJd : IsAdicComplete ((maximalIdeal V).map (algebraMap V (DualNumber V))) (DualNumber V) :=
    InertNorm.isAdicComplete_map_of_finite (maximalIdeal V) (DualNumber V)
  have hx : IsFormalPt U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) gm₀ y.left :=
    isFormalPt_of_surjective _ fun e => by
      obtain ⟨ye, h₁, h₂, h₃⟩ := hT e
      exact ⟨DualNumber (V ⧸ maximalIdeal V ^ (e + 1)), inferInstance, dualMap (Ideal.Quotient.mk _), ye,
        dualMap_surjective _ Ideal.Quotient.mk_surjective, ker_dualMap_le V _ e, h₁, h₂, h₃⟩
  have hL : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG := hjG
  have hM : ⊤ ≤ basePt gm₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := hJ _
  refine ⟨(tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹,
    ?_, fun σ f hE => ?_⟩
  · obtain ⟨g₀, hg₀⟩ := exists_isZero D.toPre (Over.mk (spMap (RingHom.id V)))
    haveI : IsAdicComplete ((maximalIdeal V).map (RingHom.id V)) V := by rw [Ideal.map_id]; exact hV
    have h₀ := isFormalPt_zero U.toUnifPre (RingHom.id V) hg₀
    have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := by
      show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    have hb₀ : basePt g₀ = spMap (RingHom.id V) ≫ eSec D.toPre.P.A := by
      refine (congrArg Over.Hom.left hg₀.1).trans ?_
      exact congrArg (· ≫ eSec D.toPre.P.A)
        ((Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap (RingHom.id V))))))
    have hyE : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ y.left = eSec G := hy
    have hL₀ : ⊤ ≤ (spMap (RingHom.id V) ≫ eSec G) ⁻¹ᵁ U.LG.L.U jG := by
      rw [← hyE, ← Category.assoc]; exact top_le_comp hL _
    have hxe : ∀ e, eSec (thickObj V (maximalIdeal V) e G) ≫ (fstG (maximalIdeal V) e G).left =
        spMap ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) ≫
          y.left := fun e => by
      rw [ExpansionValueZero.eSec_fstG, ← hyE]
      show _ = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp
        (TrivSqZeroExt.fstHom V V V).toRingHom)) ≫ _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hM₀ : ⊤ ≤ basePt g₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
      haveI : IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1)) :=
        isLocalRing_quotient_pow (IsLocalRing.maximalIdeal.isMaximal V).ne_top 0
      have HC := hx.hasCoords (e := 0) _ (pow_map_le_ker V _ 0) (hxe 0)
      have h₂ : thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A = spMap _ ≫ gm₀.b.left :=
        (ExpansionValueZero.eSec_pG _ (U.gt 0)).symm.trans HC.2.1
      have h₃ : ⊤ ≤ (thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A) ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
        rw [h₂]; exact top_le_comp hM _
      have h₄ : eSec D.toPre.P.A (thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1)))) ∈
          D.toPre.P.L.U (J gm₀.b.left) := h₃ (Set.mem_univ _)
      rw [thick_closedPoint] at h₄
      rw [hb₀]
      exact top_le_comp (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of V) _ h₄).ge _
    have hfst : (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left) : DualNumber V).fst =
        (tau U.toUnifPre ((maximalIdeal V).map (RingHom.id V)) (spMap (RingHom.id V) ≫ eSec G) jG
          (J gm₀.b.left) : V) := by
      refine eq_of_forall_mk_eq (maximalIdeal V) fun e => ?_
      have a₁ := map_tau_mul_wVal hx hL hM _ (pow_map_le_ker V _ e) (hxe e)
      have a₂ := map_tau_mul_wVal h₀ hL₀ hM₀ (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))
        (by rw [Ideal.map_id, Ideal.mk_ker]) (xe := eSec (thickObj V (maximalIdeal V) e G))
        (by rw [hid, Category.id_comp]; exact ExpansionValueZero.eSec_fstG _ e G)
      exact (IsUnit.of_mul_eq_one_right _ a₂).mul_right_cancel (a₁.trans a₂.symm)
    have r₀ := tau_rig h₀ hb₀ hL₀ hM₀
    have hv : ∀ (U' : (Sp V).Opens) (f : Γ(Sp V, U')),
        valR (spMap (RingHom.id V)) U' f = valR (𝟙 (Sp V)) U' f := fun _ _ => by rw [hid]
    rw [hv, hv] at r₀
    have hW : (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left))⁻¹ : (DualNumber V)ˣ) : DualNumber V).fst *
        (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
          (J gm₀.b.left) : DualNumber V).fst = 1 := by
      rw [← TrivSqZeroExt.fst_mul, Units.inv_mul, TrivSqZeroExt.fst_one]
    unfold rigVal rigValD
    rw [← r₀, ← _root_.mul_assoc, ← hfst, hW, _root_.one_mul]
    rfl
  · refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
    haveI : IsLocalRing (DualNumber V ⧸ ((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1)) :=
      isLocalRing_quotient_pow (ne_top_of_isHausdorff _) n
    obtain ⟨F, hF⟩ := map_secVal_eq U.toUnifPre (hE n)
    obtain ⟨-, h₁⟩ := hF (DualNumber V) ((maximalIdeal V).map (algebraMap V (DualNumber V))) _ gm₀ y.left hx _
      (Ideal.Quotient.mk (((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1))) (by rw [Ideal.mk_ker])
    refine ⟨F, fun T hT => ?_⟩
    have hc : ∀ α ∈ T, CohCharts gm₀ α (J gm₀.b.left) (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
        (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) := fun α _ => by
      refine ⟨fun p _ => Set.mem_iInter.2 fun i => hJ (gm₀.b.left ≫ D.toPre.famφB α i) (Set.mem_univ p),
        fun p _ => Set.mem_iInter.2 fun i => hJ (D.toPre.gtφT (epsR V) gm₀.b α i) (Set.mem_univ p), ?_⟩
      have c : ∀ a, Sum.elim (fun _ : PUnit.{1} => J gm₀.b.left) (Sum.elim (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
          (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i))) a = J (Sum.elim (fun _ : PUnit.{1} => basePt gm₀)
            (Sum.elim (fun a => basePt gm₀ ≫ D.toPre.famφB α a) (coordφ gm₀ α)) a) := by
        rintro (a | a | a) <;> rfl
      exact fun a b hab => (c a).trans ((congrArg J hab).trans (c b).symm)
    have e := h₁ T jG (J gm₀.b.left) (fun α i => J (gm₀.b.left ≫ D.toPre.famφB α i))
      (fun α i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) hT hL hM hc
    rw [Ideal.Quotient.eq] at e
    have key := Ideal.mul_mem_left _
      (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹ :
        (DualNumber V)ˣ) ^ k : DualNumber V) e
    rw [mul_sub, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul] at key
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) key

end GlobalTheory.MBLow.TanExp

end
