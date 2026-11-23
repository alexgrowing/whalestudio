import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnramifiedQuasiFiniteOfTangent

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegUnram

open GlobalTheory.FamRep

theorem iso_up {Y Y' : Scheme.{0}} {M N : LB Y} {M' N' : LB Y'} {h : Y' ⟶ Y} (hM : M.IsLB) (hN : N.IsLB)
    (hM' : M'.IsLB) (hN' : N'.IsLB) (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (H : LBIso M N) :
    LBIso M' N' :=
  LBIso.trans hM' (pull_isLB hM h) hN' a (LBIso.trans (pull_isLB hM h) (pull_isLB hN h) hN' (lbIso_pull H h) b.symm)

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}

include h in

theorem iso_cubeLB_pull {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T) (H : LBIso L' (L.pull φ))
    {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : a'.left ≫ φ = U.left ≫ a.left) (hb : b'.left ≫ φ = U.left ≫ b.left) :
    LBIso (cubeLB G' ![a', b'] L') ((cubeLB G ![a, b] L).pull U.left) := by
  obtain ⟨w, hw⟩ := H
  refine LBIso.chartPull (chartPullId _) (chartPullOut L _ _ U.left _ fun I => ?_)
    (iso_linComb ((isGen_iff w).1 hw) _ _)
  refine psum_push h _ _ U (fun i => ?_) I.down
  fin_cases i
  exacts [Over.OverMorphism.ext ha, Over.OverMorphism.ext hb]

include h in

theorem prim_up (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) {w v : G ⟶ G} {w' v' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (hv : v'.left ≫ φ = φ ≫ v.left) (A₁ : w * v = 𝟙 G)
    (A₂ : LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ v] L))
    (A₃ : LBIso L (cubeLB G ![𝟙 G, w] L)) :
    w' * v' = 𝟙 G' ∧ LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ v'] L') ∧
      LBIso L' (cubeLB G' ![𝟙 G', w'] L') := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  let V : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have e₁ : (fst G' G').left ≫ φ = V.left ≫ (fst G G).left :=
    congrArg (fun q => q.left) (show pushPt h.1.w (fst G' G') = V ≫ fst G G from (lift_fst _ _).symm)
  have e₂ : (snd G' G').left ≫ φ = V.left ≫ (snd G G).left :=
    congrArg (fun q => q.left) (show pushPt h.1.w (snd G' G') = V ≫ snd G G from (lift_snd _ _).symm)
  refine ⟨Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w])), ?_, ?_⟩
  · rw [← h.2 G' w' v' (U ≫ w) (U ≫ v) hw.symm hv.symm, ← MonObj.comp_mul, A₁]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact iso_up (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
      (DVR.linComb_isLB _ hL' _ _)
      (iso_cubeLB_pull h V H (by rw [Over.comp_left, Over.comp_left, Category.assoc, hw, reassoc_of% e₁]) e₂)
      (iso_cubeLB_pull h V H e₁ (by rw [Over.comp_left, Over.comp_left, Category.assoc, hv, reassoc_of% e₂])) A₂
  · have i : LBIso (cubeLB G' ![𝟙 G', w'] L') ((cubeLB G ![𝟙 G, w] L).pull φ) :=
      iso_cubeLB_pull h U H ((Category.id_comp _).trans (Category.comp_id _).symm) hw
    have a : (cubeLB G ![𝟙 G, w] L).IsLB := DVR.linComb_isLB _ hL _ _
    have a' : (cubeLB G' ![𝟙 G', w'] L').IsLB := DVR.linComb_isLB _ hL' _ _
    exact iso_up hL a hL' a' H i A₃

end Group

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem prim_of_isPEL {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {a : J → 𝓞 E}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o} {t : TObj g k J b s} {τ : SAB H S} {w w' : J} (hw : a w = H.w0)
    (hw' : a w' = H.bar H.w0) (h : IsPEL D a bas ρ t τ) : t.Prim w w' := by
  obtain ⟨e, he, hL, hact, -⟩ := h
  letI := t.ab.comm
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have h₁ : IsGrpPullback t.A τ.G (𝟙 _) e.inv.left := isGrpPullback_of_iso e.symm
  have ih : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hL₁ : LBIso t.L (τ.PP.L.pull e.inv.left) :=
    LBIso.chartPull (chartPullSec t.L _ _ ih) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull τ.PP.L _ _ rfl) hL.symm
  have hj : ∀ j, (t.act j).left ≫ e.inv.left = e.inv.left ≫ (τ.act.act (a j)).left := fun j => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Iso.comp_inv_eq, Category.assoc, hact, e.inv_hom_id_assoc]
  refine prim_up h₁ τ.PP.isLB t.isLB hL₁ (hj w) (hj w') ?_ ?_ ?_
  · rw [hw, hw', ← τ.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, τ.act.one]
  · rw [hw, hw']; exact τ.adj _
  · rw [hw]; exact τ.prim

theorem prim_of_tMap {t : TObj g k J b s} {t' : TObj g k J b s'} {f : S' ⟶ S} {w w' : J} (T : TMap t' t f)
    (prim : t.Prim w w') : t'.Prim w w' := by
  obtain ⟨ψ, h', hL', -, hact'⟩ := T
  letI := t.ab.comm
  letI := t'.ab.comm
  exact prim_up h' t.isLB t'.isLB hL' (hact' w) (hact' w') prim.1 prim.2.1 prim.2.2

theorem locallyOfFiniteType_of_isQProjOver (h : IsQProjOver s) : LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have := isProper_str o N
  infer_instance

theorem tMap_constPt (L₁ : Out.Laws) (L₂ : Out.Laws2)
    (L₃ : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {K : Type} [Field K] {s : Sp (DualNumber K) ⟶ Sp o} (t : TObj g k J b s) {w w' : J} (prim : t.Prim w w')
    {Y : Scheme.{0}} {G : Over Y} [GrpObj G] {y : Sp (DualNumber K) ⟶ Y} {χ : t.A.left ⟶ G.left}
    (h : IsGrpPullback t.A G y χ) (hy : y = constPt y) : TMap t t (constPt (𝟙 _)) := by
  let q : Sp K ⟶ Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom
  let r : Sp (DualNumber K) ⟶ Sp K := spMap (algebraMap K (DualNumber K))
  have hqr : q ≫ r = 𝟙 _ := GlobalTheory.ConstTheta.fst_comp_const
  have hy' : y = r ≫ q ≫ y := hy
  obtain ⟨t₀, io, c₁, c₂, c₃, c₄⟩ := GlobalTheory.tObj_pull o g k J b _ _ s (q ≫ s) q t rfl
  have h₀ : IsGrpPullback t₀.A G (q ≫ y) (io ≫ χ) := c₁.comp h
  let ψ : t.A.left ⟶ t₀.A.left := h₀.1.lift χ (t.A.hom ≫ r) (by rw [h.1.w, Category.assoc, ← hy'])
  have i₁ : ψ ≫ io ≫ χ = χ := h₀.1.lift_fst _ _ _
  have i₂ : ψ ≫ t₀.A.hom = t.A.hom ≫ r := h₀.1.lift_snd _ _ _
  have k₀ : IsGrpPullback t.A t₀.A r ψ := h₀.cancel (h.congr hy' i₁.symm) i₂
  have k₁ : io ≫ ψ = 𝟙 _ := by
    apply h₀.1.hom_ext
    · rw [Category.assoc, i₁, Category.id_comp]
    · rw [Category.assoc, i₂, ← Category.assoc, c₁.1.w, Category.assoc, hqr, Category.id_comp, Category.comp_id]
  have T₁ := GlobalTheory.ConstTheta.tMap_of_const L₁ L₂ L₃ o g k J b w w' K _ _ t t₀ io ψ prim c₁ c₂ c₃ c₄ k₀ k₁
  have T₂ := tMap_comp T₁ ⟨io, c₁, c₂, c₃, c₄⟩
  unfold constPt
  rw [Category.comp_id]
  exact T₂

theorem formallyUnramified_and_locallyQuasiFinite : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X), IsPullback f sT s (spMap bb) → ∀ (tT : TObj g k J b (sT ≫ spMap bb)) (c : SiegPre g k (zetaZP p k) (sT ≫ spMap z)) (u : T ⟶ pullback Ag.s (spMap z)), TMap tT t f → TSieg bas bas' tT c → u ≫ pullback.snd _ _ = sT → SiegPB c Ag.univ (u ≫ pullback.fst _ _) → FormallyUnramified u ∧ LocallyQuasiFinite u := by
  intro L₁ L₂ L₃ E _ _ _ H D g J _ a w w' bas _ _ hw hw' _ k o _ b em ρ _ _ _ _ _ _ X s t τ hrep hpel p Ag _ _ _ bas' _
    O _ i z bb _ _ _ T sT f hT tT c u hm ⟨e, he, _⟩ hu ⟨φ, _, hφ, _⟩
  have h₁ := locallyOfFiniteType_of_isQProjOver hrep.qproj
  have h₂ : LocallyOfFiniteType (u ≫ pullback.snd _ _) := by
    rw [hu]; exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hT h₁
  refine GlobalTheory.TangentCriterion.unramified_quasiFinite_of_tangent _ _ u (locallyOfFiniteType_of_comp u (pullback.snd _ _)) fun K _ x hx => ?_
  have hc : ∀ {Y Z : Scheme.{0}} (y : Sp (DualNumber K) ⟶ Y) (v : Y ⟶ Z), constPt y ≫ v = constPt (y ≫ v) :=
    fun y v => by simp only [constPt, Category.assoc]
  obtain ⟨tx, Tx⟩ := GlobalTheory.tObj_pull o g k J b _ _ _ _ x tT rfl
  obtain ⟨ψ, hψ, -⟩ := id Tx
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have g₁ := (hψ.comp (isGrpPullback_of_iso e.symm)).comp hφ
  have Tf := tMap_comp Tx hm
  have T₁ := tMap_constPt L₁ L₂ L₃ tx (prim_of_tMap Tf (prim_of_isPEL hw hw' hpel)) g₁ (by
    rw [Category.comp_id, ← hc, ← Category.assoc, hx, Category.assoc])
  have T₂ := tMap_comp T₁ Tf
  rw [hc, Category.id_comp, ← hc] at T₂
  have hs : x ≫ sT = constPt x ≫ sT := by rw [← hu, ← Category.assoc, hx, Category.assoc]
  refine hT.hom_ext (hrep.inj _ _ _ _ tx ?_ Tf T₂) hs
  rw [Category.assoc, Category.assoc, hT.w, ← Category.assoc, hs, Category.assoc]

end GlobalTheory.SiegUnram
