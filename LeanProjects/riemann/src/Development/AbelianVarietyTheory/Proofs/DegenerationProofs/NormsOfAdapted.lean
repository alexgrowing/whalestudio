import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistBaseChangeOfFinrankSectionsOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.NormsPf
open GlobalTheory.ZH

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem sum_smul_f {I : Type} (A : Finset I) (a : I → F) (s : I → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ A, a i • s i).s α).f j = ∑ i ∈ A, resTop _ (gF D F (a i)) * ((s i).s α).f j := by
  classical
  induction A using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i A hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, DVR.add_f, DVR.smul_f, ih]

theorem sum_smul_subtype {I : Type} [Fintype I] (p : I → Prop) [Fintype {i // p i}] (a : I → F) (s : I → Fam D F k)
    (α : D.X) (h : ∀ i, ¬ p i → ∀ j, ((s i).s α).f j = 0) :
    (∑ i, a i • s i).s α = (∑ i : {i // p i}, a i • s i).s α := by
  classical
  refine SecOps.sec_ext fun j => ?_
  rw [sum_smul_f, sum_smul_f, ← Finset.sum_subtype (Finset.univ.filter p) (by simp)
    (fun i => resTop _ (gF D F (a i)) * ((s i).s α).f j), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rfl
  · rw [h i hi j, mul_zero]

theorem zero_of_famOf {s : Fam D F k} {f : ∀ α, D.SecB k α} (hs : FamOf D F f s) {α : D.X}
    (h : ∀ j, (f α).f j = 0) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  rw [← SectionScalarValuation.secScal_sval (hs α) _ y hJ, UUA.sval_zero_of h _ y J (hJ.mem _ _),
    UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]

theorem basis_of_eq (hT : TwistBaseChangeStatement) [IsLocalRing R] [IsNoetherianRing R] (hk : 1 ≤ k) {α : D.X}
    {R' : Type} [CommRing R'] (φ : R →+* R') {B : Scheme.{0}} {pB : B ⟶ Sp R'} {π : B ⟶ D.P.A.left}
    (H : IsPullback π pB D.P.A.hom (spMap φ)) {I : Type} [Fintype I] {β : I → D.SecB k α} (hβ : IsBasisB D β)
    (ψ : Fin 4 → (B ⟶ D.P.A.left)) (hψ : ψ = fun i => π ≫ D.famφB α i)
    (t : I → LB.Sec (LB.LinComb D.P.L ψ (DegPre.famε k)))
    (ht : ∀ i, GeneratorPullback.SecScal D.P.L ψ (DegPre.famε k) (t i) (D.famφB α) (DegPre.famε k) (β i) π 1)
    (b : LB.Sec (LB.LinComb D.P.L ψ (DegPre.famε k))) : ∃! a : I → R', IsLin pB t a b := by
  subst hψ
  have e : t = fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (β i) π := funext fun i =>
    SecOps.sec_ext fun j => sec_ext_val D.P.isLB (fun y J hJ =>
      (SectionScalarValuation.secScal_sval (ht i) _ y hJ).symm.trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm) j
  rw [e]
  exact BasisBaseChange.basis_pullback hT R D k hk α R' φ B pB π H I β hβ b

theorem component_basis (hT : TwistBaseChangeStatement) [IsLocalRing R] [IsNoetherianRing R] (hk : 1 ≤ k) {α : D.X}
    {I : Type} [Fintype I] {β : I → D.SecB k α} (hβ : IsBasisB D β) (s : I → Fam D F k)
    (hs : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) ((s i).s α)
      (D.famφB α) (DegPre.famε k) (β i) (DegPre.prB D F).left 1)
    (b : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    ∃! a : I → F, b = (∑ i, a i • s i).s α := by
  let f : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hTF : jFK (R := R) F ≫ jK R = spMap f := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have H : IsPullback (DegPre.prB D F).left (fst (TF (R := R) F) D.P.A).left D.P.A.hom (spMap f) := by
    rw [← hTF]
    exact (IsPullback.of_hasPullback (jFK (R := R) F ≫ jK R) D.P.A.hom).flip
  have h := basis_of_eq hT hk f H hβ (DegPre.famφ D F α) (funext fun i => GC.famφ_eq D F α i)
    (fun i => (s i).s α) hs b
  refine (existsUnique_congr fun a => ?_).1 h
  exact ⟨fun h => SecOps.sec_ext fun j => (h j).trans (sum_smul_f _ a s α j).symm,
    fun h j => (congrArg (fun x => x.f j) h).trans (sum_smul_f _ a s α j)⟩

end

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
  {k : ℕ}

theorem vge_comb_iff (hT : TwistBaseChangeStatement) (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (hk : 1 ≤ k)
    {α : D.toPre.X} {I : Type} [Fintype I] {β : I → D.toPre.SecB k α} (hβ : IsBasisB D.toPre β)
    (s : I → Fam D.toPre F k)
    (hs : ∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) ((s i).s α)
      (D.toPre.famφB α) (DegPre.famε k) (β i) (DegPre.prB D.toPre F).left 1) (a : I → F) (q : ℚ) :
    VGe D F v k α ((∑ i, a i • s i).s α) q ↔ ∀ i, (q : WithTop ℚ) ≤ v (a i) := by
  constructor
  · intro h
    obtain ⟨b, hb, e⟩ := GlobalTheory.TermSize.exists_comb hϖ hv hβ s hs h
    rw [(component_basis hT hk hβ s hs _).unique rfl e]
    exact hb
  · intro h
    let e := (Fintype.equivFin I).symm
    refine ⟨_, fun i => a (e i), fun i => β (e i), fun i => (s (e i)).s α, fun i => hs _, fun i => h _, fun j => ?_⟩
    rw [sum_smul_f]
    exact (Equiv.sum_comp e _).symm

end

theorem norms_of_adapted : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k : ℕ, 1 ≤ k → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α) (s : Fin r → Fam D.toPre F k), AdFam D Q k cls mu f → (∀ i, GlobalTheory.ZH.FamOf D.toPre F (f i) (s i)) → Norms D Q v k cls s := by
  intro hLL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk r cls mu f s hA hs
  classical
  obtain ⟨⟨hshort, hcls, hcov, -⟩, -, hzero, hbas⟩ := hA
  have hG := hLL.1.globalFns
  have hT : TwistBaseChangeStatement := GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hLL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _)
  have hsub : ∀ (a : Fin r → F) i₀, (∑ i, a i • s i).s (cls i₀) =
      (∑ i : {i // cls i = cls i₀}, a i • s i).s (cls i₀) := fun a i₀ =>
    sum_smul_subtype (fun i => cls i = cls i₀) a s _ fun i hi =>
      zero_of_famOf (hs i) (hzero i _ fun z hz => hi (hcls i₀ i ⟨z, hz⟩).symm)
  have hB := fun i₀ => component_basis (F := F) hT hk (hbas i₀) (fun i => s i) (fun i => hs i _)
  have hV : ∀ (a : Fin r → F) (q : ℚ) i₀, VGe D F v k (cls i₀) ((∑ i, a i • s i).s (cls i₀)) q ↔
      ∀ i : {i // cls i = cls i₀}, (q : WithTop ℚ) ≤ v (a i) := fun a q i₀ => by
    rw [hsub]
    exact vge_comb_iff hT hϖ hv hk (hbas i₀) (fun i => s i) (fun i => hs i _) (fun i => a i) q
  refine ⟨fun s' => ?_, fun a q => ⟨?_, ⟨fun h i => (hV a q i).1 (h _) ⟨i, rfl⟩, fun h α => ?_⟩,
    fun i h => (hV a q i).1 h ⟨i, rfl⟩⟩⟩
  · have ex : ∀ α, ∃ c : {i // cls i = α} → F, (∃ i₀, cls i₀ = α) →
        s'.s α = (∑ i : {i // cls i = α}, c i • s i).s α := fun α => by
      by_cases h : ∃ i₀, cls i₀ = α
      · obtain ⟨i₀, rfl⟩ := h
        obtain ⟨c, hc⟩ := (hB i₀ (s'.s (cls i₀))).exists
        exact ⟨c, fun _ => by convert hc⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    choose c hc using ex
    refine existsUnique_of_exists_of_unique ⟨fun i => c (cls i) ⟨i, rfl⟩, fam_ext fun α j => ?_⟩ fun a a' ha ha' => ?_
    · obtain ⟨i₀, z, rfl⟩ := hcov α
      refine congrArg (fun x => x.f j) (GlobalTheory.FamFree.eq_of_eq_add_nsmul hG _ _ ⟨z, rfl⟩ ?_)
      rw [hsub, hc _ ⟨i₀, rfl⟩]
      have e : ∀ α (i : {i // cls i = α}), c α i = c (cls i) ⟨i, rfl⟩ := by rintro _ ⟨i, rfl⟩; rfl
      simp only [← e]
    · funext i
      have h := (hB i (s'.s (cls i))).unique (y₁ := fun i' => a i') (y₂ := fun i' => a' i')
        (by rw [ha, hsub]) (by rw [ha', hsub])
      exact congrFun h ⟨i, rfl⟩
  · rw [n1a V ϖ hϖ D Q hQ F v hv k hk (Finset.univ.image cls) (fun χ => by
      obtain ⟨i, hi⟩ := hcov χ
      exact ⟨cls i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) _ q]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff, hV]
    exact ⟨fun h i => h i ⟨i, rfl⟩, fun h i₀ i => by have := h i; rwa [i.2] at this⟩
  · obtain ⟨i₀, z, rfl⟩ := hcov α
    refine (SectionScalarValuation.fe_move hϖ hQ hv k z (cls i₀) _ ((hV a q i₀).2 fun i => h i)).mono ?_
    have h1 := hshort i₀ z
    rw [q_shift hϖ hQ] at h1
    have h2 : (0 : ℤ) ≤ k * Q z + QForm.bOf D.toPre Q z (cls i₀) :=
      nonneg_of_mul_nonneg_right (a := (k : ℤ)) (by linarith) (by omega)
    have h3 : (0 : ℚ) ≤ ((k * Q z + QForm.bOf D.toPre Q z (cls i₀) : ℤ) : ℚ) := by exact_mod_cast h2
    linarith

end GlobalTheory.OneBasis.NormsPf
end
