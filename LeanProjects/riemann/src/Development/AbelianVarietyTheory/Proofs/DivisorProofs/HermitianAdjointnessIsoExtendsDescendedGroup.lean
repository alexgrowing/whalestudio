import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPowersCartesianGroupSquare
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ExtAdj

section Gen
variable {X Y B : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_normalized {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B)
    (s : LB.Gen (LB.LinComb L ψ ε)) (hs : s.IsGen) :
    ∃ s₂ : LB.Gen (LB.LinComb L (Sum.elim ψ (fun k => p ≫ e ≫ ψ k)) (Sum.elim ε (fun k => -ε k))),
      s₂.IsGen ∧ ∀ y J, Good L y J → val s₂ e y J = 1 := by
  refine ⟨LB.mulGen L _ _ _ _ s (LB.pullGen L _ _ (LB.invGen L _ _ (LB.pullGen L ψ ε s e)) p),
    DVR.mulGen_isGen _ _ _ _ _ _ _ hs (DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hs e)) p), fun y J hJ => ?_⟩
  rw [val_mul hJ, val_pull hJ, val_inv, val_pull hJ, he, Category.id_comp, mul_inv_cancel]

theorem formEq_sec {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B) :
    FormEq (K := PEmpty) (PEmpty.elim : PEmpty → (B ⟶ X)) PEmpty.elim
      (fun k => e ≫ Sum.elim ψ (fun k => p ≫ e ≫ ψ k) k) (Sum.elim ε (fun k => -ε k)) := by
  intro U _ h
  rw [Fintype.prod_empty, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ← Category.assoc, he, Category.id_comp, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_cancel]
end Gen

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S}

def cφ (x : Fin 2 → (T ⟶ G)) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ G.left) := fun I => (psum G x I.down).left

def cε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem cls_diff {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (h : (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))).IsLB) :
    CechPic.cls _ h = CechPic.cls (LB.LinComb L (cφ x₁) cε) (LB.isLB_linComb hL _ _) -
      CechPic.cls (LB.LinComb L (cφ x₂) cε) (LB.isLB_linComb hL _ _) := by
  rw [CechPic.cls_linComb hL, CechPic.cls_linComb hL, CechPic.cls_linComb hL, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem lbIso_of_gen {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I)))) (ht : t.IsGen) :
    LBIso (cubeLB G x₁ L) (cubeLB G x₂ L) := by
  have z := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_diff hL x₁ x₂, sub_eq_zero] at z
  exact (CechPic.cls_eq_iff _ _).1 z

theorem gen_of_lbIso {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (H : LBIso (cubeLB G x₁ L) (cubeLB G x₂ L)) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))), t.IsGen := by
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [cls_diff hL x₁ x₂, sub_eq_zero]
  exact (CechPic.cls_eq_iff (LB.isLB_linComb hL (cφ x₁) cε) (LB.isLB_linComb hL (cφ x₂) cε)).2 H

end Cube

section Origin
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem eSec_cφ (x : Fin 2 → (G2 G ⟶ G)) (hx : ∀ i, η[G2 G] ≫ x i = 1) (I : ULift.{0} (Finset (Fin 2))) :
    eSec (G2 G) ≫ cφ x I = eSec G := by
  have h1 : η[G2 G] ≫ psum G x I.down = 1 := by
    have a := psum_hom (preHom (G := G) η[G2 G]) x I.down
    have b := psum_hom (1 : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S) ⟶ G)) (fun _ => 1) I.down
    simp only [MonoidHom.one_apply] at b
    exact a.trans ((congrArg (fun z => psum G z I.down) (funext hx)).trans b.symm)
  have h2 := congrArg (fun z => z.left) h1
  simp only [Over.comp_left] at h2
  refine h2.trans ?_
  simp [Hom.one_def, eSec]

theorem eSec_x2 (i : Fin 2) : η[G2 G] ≫ x2 G i = η[G] := by
  fin_cases i <;> simp [x2]

theorem one_cube₁ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G ≫ f, snd G G] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]

theorem one_cube₂ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G, snd G G ≫ f] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]
end Origin

section Push
variable {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
  {A : Over U} [GrpObj A] [IsCommMonObj A] {e : A.left ⟶ G.left}

abbrev jTwo (he : IsGrpPullback A G j e) : (G2 A).left ⟶ (G2 G).left :=
  (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A))).left

theorem doubleProductMapOfGrpPullback_comp_doubleCoordinate (he : IsGrpPullback A G j e) (i : Fin 2) : jTwo he ≫ (x2 G i).left = (x2 A i).left ≫ e := by
  fin_cases i
  · exact congrArg (fun z => z.left) (lift_fst (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
  · exact congrArg (fun z => z.left) (lift_snd (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))

theorem eSec_jTwo (he : IsGrpPullback A G j e) : eSec (G2 A) ≫ jTwo he = j ≫ eSec (G2 G) := by
  refine GlobalTheory.Mum.PowCart.square_over_hom_ext _ fun i => ?_
  have a : eSec (G2 A) ≫ (x2 A i).left = eSec A := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := A) i)
  have b : eSec (G2 G) ≫ (x2 G i).left = eSec G := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := G) i)
  rw [Category.assoc, doubleProductMapOfGrpPullback_comp_doubleCoordinate, ← Category.assoc, a, Category.assoc, b]
  exact (cubeMapOf he).e_comm

theorem cφ_push (he : IsGrpPullback A G j e) (x' : Fin 2 → (G2 A ⟶ A)) (x : Fin 2 → (G2 G ⟶ G))
    (hx : ∀ i, (x' i).left ≫ e = jTwo he ≫ (x i).left) (I : ULift.{0} (Finset (Fin 2))) :
    cφ x' I ≫ e = jTwo he ≫ cφ x I :=
  psum_push he x' x (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
    (fun i => Over.OverMorphism.ext (by rw [Over.comp_left]; exact hx i)) I.down
end Push

section Drop
variable {X Y B : Scheme.{0}} {K0 : Type} [Fintype K0]

theorem formEq_drop {ψ : K0 ⊕ K0 → (Y ⟶ X)} {ε₀ : K0 → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (z : B ⟶ X)
    (hz : ∀ k, e ≫ ψ k = z) :
    FormEq (Sum.elim ψ (fun k => p ≫ e ≫ ψ k))
      (Sum.elim (Sum.elim ε₀ (fun k => -ε₀ k)) (fun k => -(Sum.elim ε₀ (fun k => -ε₀ k)) k))
      ψ (Sum.elim ε₀ (fun k => -ε₀ k)) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hz, zpow_neg, neg_neg, inv_inv,
    Finset.prod_inv_distrib]
  group
end Drop

theorem adj_extends : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] PP.L) (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar a)] PP.L) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU _ tF _ G _ _ e hsa he _ act hact PP cub cm hF _ hpc a
  obtain ⟨⟨-, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU
  have := hsa.smooth
  have := hsa.geomConnected
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  haveI : IsDominant j := ⟨hdense⟩
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  obtain ⟨w, hw, -, -⟩ := hpc
  have hw' := (isGen_iff w).1 hw
  haveI := act.hom a
  haveI := act.hom (H.bar a)
  haveI := tF.act.hom a
  haveI := tF.act.hom (H.bar a)
  let x₁ : Fin 2 → (G2 G ⟶ G) := ![fst G G ≫ act.act a, snd G G]
  let x₂ : Fin 2 → (G2 G ⟶ G) := ![fst G G, snd G G ≫ act.act (H.bar a)]
  let y₁ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G ≫ tF.act.act a, snd tF.G tF.G]
  let y₂ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G, snd tF.G tF.G ≫ tF.act.act (H.bar a)]
  let ψ := Sum.elim (cφ x₁) (cφ x₂)
  let ψ' := Sum.elim (cφ y₁) (cφ y₂)
  let ε₁ : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → ℤ := Sum.elim cε (fun I => -cε I)
  obtain ⟨s, hs⟩ := gen_of_lbIso tF.PP.isLB y₁ y₂ (tF.adj a)
  obtain ⟨s₂, hs₂, h1⟩ := exists_normalized (G2 tF.G).hom (eSec (G2 tF.G)) (CubeExtension.eSec_comp _) s hs
  have hsm := CubeExtension.smooth_tensor G G
  have hgc := CubeExtension.geometricallyConnected_tensor G G
  have hpb : IsPullback (jTwo he) (G2 tF.G).hom (G2 G).hom j := GlobalTheory.Mum.PowCart.isPullback_two he.1
  have f0 : jTwo he ≫ (fst G G).left = (fst tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 0
  have f1 : jTwo he ≫ (snd G G).left = (snd tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 1
  have hψ : ∀ k, ψ' k ≫ e = jTwo he ≫ ψ k := by
    rintro (I | I)
    · refine cφ_push he y₁ x₁ (fun i => ?_) I
      fin_cases i
      · show (fst tF.G tF.G ≫ tF.act.act a).left ≫ e = jTwo he ≫ (fst G G ≫ act.act a).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact a, ← Category.assoc, ← f0, Category.assoc]
      · exact f1.symm
    · refine cφ_push he y₂ x₂ (fun i => ?_) I
      fin_cases i
      · exact f0.symm
      · show (snd tF.G tF.G ≫ tF.act.act (H.bar a)).left ≫ e = jTwo he ≫ (snd G G ≫ act.act (H.bar a)).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact (H.bar a), ← Category.assoc, ← f1, Category.assoc]
  have hφ : ∀ k, Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k) k ≫ cm.F =
      jTwo he ≫ Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k) k := by
    rw [hF]
    rintro (k | k)
    · exact hψ k
    · simp only [Sum.elim_inr, Category.assoc]
      rw [hψ k, ← Category.assoc (eSec (G2 tF.G)), eSec_jTwo he, Category.assoc, ← Category.assoc (G2 tF.G).hom,
        ← hpb.w, Category.assoc]
  obtain ⟨c', hc', -⟩ := DenseCubeExt.exists_extension hS j (G2 G).hom (eSec (G2 G)) (jTwo he) (G2 tF.G).hom
    (eSec (G2 tF.G)) hsm hgc (CubeExtension.eSec_comp _) hpb (eSec_jTwo he) PP.isLB tF.PP.isLB hw'
    (Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k)) (Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k))
    (Sum.elim ε₁ (fun k => -ε₁ k)) hφ (formEq_sec _ _ (CubeExtension.eSec_comp _))
    (formEq_sec _ _ (CubeExtension.eSec_comp _)) s₂ hs₂ h1
  have hz : ∀ k, eSec (G2 G) ≫ ψ k = eSec G := by
    rintro (I | I)
    · exact eSec_cφ x₁ (one_cube₁ (act.act a)) I
    · exact eSec_cφ x₂ (one_cube₂ (act.act (H.bar a))) I
  obtain ⟨t, ht, -⟩ := exists_gen PP.isLB (formEq_drop (ε₀ := cε) (G2 G).hom (eSec (G2 G)) (eSec G) hz) c' hc'
  exact lbIso_of_gen PP.isLB x₁ x₂ t ht

end GlobalTheory.ExtAdj
