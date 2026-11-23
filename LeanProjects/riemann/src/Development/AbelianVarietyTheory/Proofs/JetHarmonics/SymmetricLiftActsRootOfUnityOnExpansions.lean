import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoValuesConstantOfSameCubeTheta
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.SymActExpansion

theorem exists_isos {X₀ X' XG XK XA : Scheme.{0}} {L₀ : LB X₀} {L' : LB X'} {LG : LB XG} {LA : LB XA}
    (h₀ : L₀.IsLB) (h' : L'.IsLB) (hG : LG.IsLB) (hA : LA.IsLB) {m₁ : X' ⟶ X₀} {m₂ : X' ⟶ XG}
    {w₁ : LB.Iso L' (L₀.pull m₁)} {w₂ : LB.Iso L' (LG.pull m₂)} (g₁ : w₁.IsGen) (g₂ : w₂.IsGen)
    {π : XK ⟶ XG} {a : XK ⟶ XA} {a' : XA ⟶ XK} (ha' : a' ≫ a = 𝟙 _) (ha : a ≫ a' = 𝟙 _) {g : XA ⟶ X'}
    (hg : g ≫ m₂ = a' ≫ π) (ext : LBIso (LA.pull a) (LG.pull π)) :
    ∃ (W : LB.Iso (LA.pull a) (LG.pull π)) (ω : LB.Iso LA (L₀.pull (g ≫ m₁))), W.IsGen ∧ ω.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ XK) (z : Z) j₀ j' jG jA, m₁ (g (a (r z))) ∈ L₀.U j₀ → g (a (r z)) ∈ L'.U j' →
        m₂ (g (a (r z))) ∈ LG.U jG → a (r z) ∈ LA.U jA →
        Geo.Tor.gw ω (r ≫ a) z j₀ jA * Geo.Tor.gw w₂ ((r ≫ a) ≫ g) z jG j' =
          BoxExpansion.pw W r z jA jG * Geo.Tor.gw w₁ ((r ≫ a) ≫ g) z j₀ j' := by
  obtain ⟨ω₂, hω₂⟩ : LBIso LA (LG.pull (g ≫ m₂)) :=
    LBIso.chartPull (chartPullSec LA a a' ha')
      (chartPullSame LG (fun _ : PUnit => g ≫ m₂) (fun _ => π) (fun _ => 1) a' fun _ => hg) ext
  obtain rfl : π = a ≫ g ≫ m₂ := by rw [hg, ← Category.assoc, ha, Category.id_comp]
  obtain ⟨W, hW, vW⟩ := IsoValConst.exists_iso_pull hω₂ a
  rw [isGen_iff] at g₁ g₂ hω₂
  obtain ⟨ω', T'⟩ := Geo.Tor.exists_cancel hG w₂ ω₂ g₂ hω₂ h' hA
  have hω' := T'.pgen_cancel hG g₂ hω₂
  obtain ⟨ω, T⟩ := Geo.Tor.exists_comp h' w₁ ω' g₁ hω' h₀ hA
  refine ⟨W, ω, hW, (isGen_iff _).2 (T.pgen_comp h' g₁ hω'), fun Z r z j₀ j' jG jA k₀ k' kG kA => ?_⟩
  have e : BoxExpansion.pw W r z jA jG = Geo.Tor.gw ω₂ (r ≫ a) z jG jA := vW Z r z jG jA kG kA
  rw [e, T Z (r ≫ a) z j₀ j' jA k₀ k' kA, T' Z (r ≫ a) z jG j' jA kG k' kA]
  simp only [mul_comm, mul_left_comm, _root_.mul_assoc]

theorem isoCast_isGen {X Y : Scheme.{0}} {L L' : LB X} (h : L = L') {M : LB Y} (f : Y ⟶ X) {w : LB.Iso M (L.pull f)}
    (hw : w.IsGen) : (isoCast h f w).IsGen := by
  subst h; exact hw

theorem exists_root_of_unity (hL : Laws) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ} (hk : 1 ≤ k)
    {W : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK V)))} (hW : W.IsGen)
    (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := V) F)) {p : QkPt D.toPre F k} (hp : QkToAkU U.toUnifPre F k p θ.pt)
    (hc : LB.Gen.Corr A.L _ _ _ _ (Out.powGen A.A A.L (k : ℤ) θ k) (LB.oneGen A.L))
    {t t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))} {s s₀ s₁ : Fam D.toPre F k}
    (hs : U.ExpandsF F k W t s) (hact : IsActOf A.A A.L (k : ℤ) θ t t')
    {w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))} (hw : w.IsGen) {ζ : F}
    (hf : FinOrd D F k p w ζ) (r₀ : PhiRel D.toPre F k p w s s₀) (r₁ : Fam.IsSmul D.toPre F ζ s₀ s₁) :
    ∃ (u : F) (s' : Fam D.toPre F k), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ Fam.IsSmul D.toPre F u s₁ s' ∧
      U.ExpandsF F k W t' s' := by
  obtain ⟨hx, hp⟩ := hp W hW
  obtain ⟨w₀, hw₀, hΦθ⟩ := hp θ rfl
  obtain ⟨hB₁, hB₂⟩ := expansion_bijective_over_fields hL.globalFns V (maximalIdeal V) D A G U F k hk W hW
  obtain ⟨Φ₀, hΦ⟩ := phiFun_of hL V (maximalIdeal V) D F k hk p w₀ hw₀
  obtain ⟨Φ, hΦw⟩ := phiFun_of hL V (maximalIdeal V) D F k hk p w hw
  choose act hact' using fun x : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)) =>
    (VVRank.exists_isTwistPull A.A A.isLB θ.isGen x : ∃ y, IsActOf A.A A.L (k : ℤ) θ x y)
  have key : ∀ i : ℕ, U.ExpandsF F k W (act^[i] t) (((Φ₀ : Module.End F (Fam D.toPre F k)) ^ i) s) := by
    intro i
    induction i with
    | zero => exact hs
    | succ i ih =>
      obtain ⟨s₁, hs₁, -⟩ := hB₁ (act^[i + 1] t)
      have h₁ := (hΦ _ _).1 (hΦθ _ _ _ _ ih hs₁ (by rw [Function.iterate_succ_apply']; exact hact' _))
      rw [pow_succ', Module.End.mul_apply, ← h₁]; exact hs₁
  have hcyc := thetaGrp_act_iterate_eq_of_pow_eq_one _ A.A A.L A.isLB (k : ℤ) _ θ k hx hc
    (fun i => act^[i.val] t) (fun i => by
      show IsActOf _ _ _ _ (act^[i.val] t) (act^[i.val + 1] t)
      rw [Function.iterate_succ_apply']; exact hact' _)
  have he : act^[k] t = t := by
    have ext : ∀ a b : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)), (∀ j, a.f j = b.f j) → a = b := by
      rintro ⟨a, _⟩ ⟨b, _⟩ h
      obtain rfl : a = b := funext h
      rfl
    exact ext _ _ hcyc
  have h₅ := key k
  rw [he] at h₅
  have h₆ : ((Φ₀ : Module.End F (Fam D.toPre F k)) ^ k) s = s := (hB₁ t).unique h₅ hs
  obtain ⟨s', hs', -⟩ := hB₁ t'
  obtain rfl : s' = Φ₀ s := (hΦ _ _).1 (hΦθ _ _ _ _ hs hs' hact)
  obtain rfl : s₀ = Φ s := (hΦw _ _).1 r₀
  obtain rfl : s₁ = ζ • Φ s := (DVR.isSmul_iff _ _ _).1 r₁
  obtain ⟨M, hM, hζ⟩ := (ThetaFinOrd.finOrd_iff p w ζ Φ hΦw).1 hf
  obtain ⟨c, rfl⟩ := ThetaFinOrd.exists_scalar hL.globalFns p w₀ w hw₀ hw Φ₀ Φ (fun _ => (hΦ _ _).2 rfl)
    (fun _ => (hΦw _ _).2 rfl)
  by_cases h0 : s = 0
  · refine ⟨1, _, ⟨1, one_pos, one_pow _⟩, (DVR.isSmul_iff _ _ _).2 ?_, hs'⟩
    simp [h0]
  have a₁ : ∀ n : ℕ, (((c • Φ : Module.End F (Fam D.toPre F k)) ^ k) ^ n) s = s := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, Module.End.mul_apply, h₆, ih]
  have a₂ : ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (k * M)) s = s := by
    rw [mul_comm k M, pow_mul, hζ, one_pow]; rfl
  have a₃ := a₁ M
  rw [← pow_mul] at a₃
  rw [smul_pow, LinearMap.smul_apply] at a₂ a₃
  have hkM : 0 < k * M := Nat.mul_pos hk hM
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hkM.ne', zero_smul] at a₂
    exact h0 a₂.symm
  have hv : ((Φ : Module.End F (Fam D.toPre F k)) ^ (k * M)) s ≠ 0 := fun e => by
    rw [e, smul_zero] at a₂
    exact h0 a₂.symm
  have a₄ : c ^ (k * M) = ζ ^ (k * M) := smul_left_injective F hv (a₃.trans a₂.symm)
  refine ⟨c / ζ, _, ⟨k * M, hkM, by rw [div_pow, a₄, div_self (pow_ne_zero _ hζ0)]⟩,
    (DVR.isSmul_iff _ _ _).2 ?_, hs'⟩
  rw [smul_smul, div_mul_cancel₀ _ hζ0, LinearMap.smul_apply]

open scoped CategoryTheory.Obj in

theorem exists_expandsG_of_isSymAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ (q : ℕ), 1 ≤ q → ∀ (σ σ' : P.U.toUnifPre.SecGF F q) (hh hh' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (s t₀ t : Fam P.D.toPre F q) (x : TFK (R := T.V) F ⟶ P.A.A) (b : ptO Xo xF ⟶ Xo.univ.t.G) (p : QkPt P.D.toPre F q) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε q))) (ζ : F), SecTieF I P F xF q σ hh → SecTieF I P F xF q σ' hh' → P.U.toUnifPre.ExpandsG F q σ s → IsSymAct Xo.univ.t.G Xo.univ.t.PP q b hh hh' → PtTieF I P F xF x b → P.ToA F q p x → w.IsGen → FinOrd P.D F q p w ζ → PhiRel P.D.toPre F q p w s t₀ → Fam.IsSmul P.D.toPre F ζ t₀ t → ∃ (u : F) (t' : Fam P.D.toPre F q), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ Fam.IsSmul P.D.toPre F u t t' ∧ P.U.toUnifPre.ExpandsG F q σ' t' := by
  intro E _ _ _ H Dw l Xo c T io y I P F _ _ _ xF hxF q hq σ σ' hh hh' s t₀ t x b p w ζ tσ tσ' hσ
    ⟨_, U, hU, hUa⟩ ⟨r, hr, hr1, hr2⟩ hp hw hf r₀ r₁
  letI := H.starRing
  letI := io.toAlgebra
  have hL : Laws := abelianSchemeLaws_all.1
  have := P.U.gen_hom
  have := P.A.isAb.comm
  have gpG : IsGrpPullback P.A.A I.G.G (jK T.V) (P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback I.G.G (jK T.V))).congr
      (Category.id_comp _) rfl
  obtain ⟨e, he, eφ⟩ := grpPullback_iso gpG I.m2.cart
  have gp : IsGrpPullback P.A.A Xo.univ.t.G y.x (e.hom.left ≫ I.m1.φ) :=
    ((isGrpPullback_of_iso e).comp I.m1.cart).congr (Category.id_comp _) rfl
  have i₁ : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have i₂ : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have h₀ := Xo.univ.t.PP.isLB
  obtain ⟨W, ω, hW, hω, rel⟩ := exists_isos h₀ I.t'.PP.isLB P.U.LG.isLB P.A.isLB I.rig1.1
    (isoCast_isGen (congrArg RigLB.L P.bundle).symm _ I.rig2.1) i₁ i₂ eφ P.U.ext
  have hr' : r = x.left ≫ e.hom.left := by
    refine I.m2.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, eφ]
      exact hr2.trans (by rw [Over.comp_left, Category.assoc])
    · rw [Category.assoc, Over.w, Over.w]
      exact hr
  have hx : (𝟙 (Sp F) : (TFK (R := T.V) F).left ⟶ (ptO Xo xF).left) ≫ b.left = x.left ≫ e.hom.left ≫ I.m1.φ := by
    rw [← Category.assoc, ← hr', hr1]
    exact Category.id_comp _
  have hb := TranslMove.base_comm gp (T := TFK (R := T.V) F) (T₀ := ptO Xo xF) (τ := 𝟙 (Sp F)) (x := x) (x₀ := b) hx
  obtain ⟨Ψ, h₁, h₂⟩ : ∃ Ψ : (TFK (R := T.V) F ⊗ P.A.A).left ⟶ (ptO Xo xF ⊗ Xo.univ.t.G).left,
      Ψ ≫ (fst _ Xo.univ.t.G).left = (fst _ P.A.A).left ≫ 𝟙 (Sp F) ∧
        Ψ ≫ (snd _ Xo.univ.t.G).left = (snd _ P.A.A).left ≫ e.hom.left ≫ I.m1.φ :=
    ⟨pullback.lift ((fst _ P.A.A).left ≫ 𝟙 (Sp F)) ((snd _ P.A.A).left ≫ e.hom.left ≫ I.m1.φ) (by
      rw [Category.assoc, Category.assoc, hb, gp.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨θ, hθ, a⟩ := TranslMove.exists_symLift gp (T := TFK (R := T.V) F) (T₀ := ptO Xo xF) (τ := 𝟙 (Sp F)) h₀ P.A.isLB hω h₁ h₂
    (fun θ => TranslMove.pt_pow_eq_one hL.kerPow P.A q rfl θ) hx hU
  obtain ⟨t₁, R₁⟩ : ∃ t₁ : LB.Sec (LPow P.A.A P.A.L (q : ℤ) (TFK (R := T.V) F)), TranslMove.SecRel ω Ψ hh t₁ := by
    obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => (snd (TFK (R := T.V) F) P.A.A).left)
      (φ := fun _ => (snd (ptO Xo xF) Xo.univ.t.G).left) (ε := fun _ => (q : ℤ)) hω h₀ P.A.isLB (fun _ => h₂.symm) hh
    refine ⟨s, fun Z r z J J' hJ hJ' => (hs.sval (fun _ => h₂.symm) r hJ hJ').trans ?_⟩
    rw [Fin.prod_univ_one]
    rfl
  obtain ⟨t₂, act, R₂⟩ := a _ _ _ hUa R₁
  have g₁ : (P.U.genF F).left ≫ (snd (TFK (R := T.V) F) P.A.A).left =
      (snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left ≫ P.U.gen.hom.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have g₂ : (P.U.genF F).left ≫ (fst (TFK (R := T.V) F) P.A.A).left =
      (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left := by
    rw [← Over.comp_left, lift_fst]
  have key : ∀ (σ : P.U.toUnifPre.SecGF F q) (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF)))
      (t : LB.Sec (LPow P.A.A P.A.L (q : ℤ) (TFK (R := T.V) F))), SecTieF I P F xF q σ hh →
      TranslMove.SecRel ω Ψ hh t → GeneratorPullback.IsoRelM P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst I.G.G.hom (jK T.V)) W
        (snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left q
        (snd (TFK (R := T.V) F) P.A.A).left (P.U.genF F).left t
        (UnifPre.gFK (R := T.V) (G := I.G.G) F) (𝟙 _) σ := by
    intro σ hh t tσ R
    refine BoxExpansion.isoRel_of_val P.A.isLB P.U.LG.isLB g₁ (Category.id_comp _) fun z JA JG hJA hJG => ?_
    obtain ⟨J₀, hJ₀⟩ := TranslMove.exists_good_pt h₀ z
    obtain ⟨J', hJ'⟩ := TranslMove.exists_good_pt I.t'.PP.isLB z
    obtain ⟨m, hm⟩ : ∃ m, m = (snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left := ⟨_, rfl⟩
    have c₂ : ((m ≫ P.U.gen.hom.left) ≫ e.hom.left) ≫ I.m2.φ = m ≫ pullback.fst I.G.G.hom (jK T.V) := by
      rw [Category.assoc, eφ, Category.assoc, ← Category.assoc P.U.gen.hom.left, i₂, Category.id_comp]
    have a₁ := tσ.2 _ ((m ≫ P.U.gen.hom.left) ≫ e.hom.left) (𝟙 _) ((P.U.genF F).left ≫ Ψ)
      (by rw [c₂, hm, Category.id_comp])
      (by rw [Category.assoc, h₂, ← Category.assoc, g₁, hm]; simp only [Category.assoc])
      (by rw [Category.assoc, h₁, ← Category.assoc, g₂, Category.id_comp]; exact (Category.comp_id _).symm)
      (by
        rw [← Category.assoc, Category.assoc _ Ψ, h₁, ← Category.assoc, g₂, Category.assoc _ e.hom.left, Over.w,
          Category.assoc m, Over.w, hm, Over.w]
        exact (congrArg (· ≫ _) (Category.comp_id _)).trans (Over.w (fst (TFK (R := T.V) F) _)))
      z J₀ JG (J' ((m ≫ P.U.gen.hom.left) ≫ e.hom.left)) hJ₀ hJG (hJ' _)
    have a₂ := R _ (P.U.genF F).left z J₀ JA hJ₀ hJA
    have a₃ := rel _ m z (J₀ (((m ≫ P.U.gen.hom.left) ≫ e.hom.left) ≫ I.m1.φ))
      (J' ((m ≫ P.U.gen.hom.left) ≫ e.hom.left)) (JG (((m ≫ P.U.gen.hom.left) ≫ e.hom.left) ≫ I.m2.φ))
      (JA (m ≫ P.U.gen.hom.left)) (hJ₀ (((m ≫ P.U.gen.hom.left) ≫ e.hom.left) ≫ I.m1.φ))
      (hJ' ((m ≫ P.U.gen.hom.left) ≫ e.hom.left)) (hJG (((m ≫ P.U.gen.hom.left) ≫ e.hom.left) ≫ I.m2.φ))
      (hJA (m ≫ P.U.gen.hom.left))
    rw [g₁, ← hm, TranslMove.wv, ← Category.assoc _ e.hom.left, zpow_natCast] at a₂
    rw [← hm, ← c₂]
    have alg : ∀ {S : Type} [CommRing S] (n : ℕ) (o w₂ W w₁ : Sˣ) (s h t : S), o * w₂ = W * w₁ →
        h = (o ^ n).val * t → s * w₁.val ^ n = h * w₂.val ^ n → s = (W ^ n).val * t := by
      intro S _ n o w₂ W w₁ s h t e₁ e₂ e₃
      refine (Units.mul_left_inj (w₁ ^ n)).1 ?_
      rw [mul_right_comm, ← Units.val_mul, ← mul_pow, ← e₁, mul_pow, Units.val_mul, mul_right_comm, ← e₂,
        Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, e₃]
    exact alg q _ _ _ _ _ _ _ a₃ a₂ a₁
  obtain ⟨u, s', hu, hs, σ'', k₁, k₂⟩ := exists_root_of_unity hL P.U hq hW θ (hθ.pt_eq ▸ hp) hθ.pow_eq
    ⟨σ, key σ hh t₁ tσ R₁, hσ⟩ act hw hf r₀ r₁
  obtain rfl : σ' = σ'' := FieldBaseChange.sec_ext' P.U.LG.isLB fun z JG hJG => by
    obtain ⟨JA, hJA⟩ := TranslMove.exists_good_pt P.A.isLB z
    have a₁ := BoxExpansion.isoRel_val (key σ' hh' t₂ tσ' R₂) (𝟙 _) z hJA hJG
    have a₂ := BoxExpansion.isoRel_val k₁ (𝟙 _) z hJA hJG
    have := a₁.trans a₂.symm
    rwa [Category.id_comp] at this
  exact ⟨u, s', hu, hs, k₂⟩

end GlobalTheory.SymActExpansion
