import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphism
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlphaFormHarmonicValueAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueNormalisedPullbackRationalNorm
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumSupportCMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueEqChartValue
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullback
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortThetaValueFieldEqMapSubfieldData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StdCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l l₂ : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂}

section Chart

open GlobalTheory.ChartPush

set_option maxHeartbeats 800000 in

theorem hv_push [StarRing (𝓞 E)] {nab : NabV Xo c} {nab₂ : NabV Xo₂ c₂} (hn : IsNab Xo c nab)
    (hn₂ : IsNab Xo₂ c₂ nab₂) {ρ : Xo₂.X ⟶ Xo.X} (ν : SABMap Xo₂.univ.t Xo.univ.t ρ) {S : Type} [Field S]
    [Algebra c.F S] [Algebra c₂.F S] {y : FrPt Xo c S} {y₂ : FrPt Xo₂ c₂ S} {pm : Gx y₂.x ⟶ Gx y.x}
    {w : LB.Iso Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)} (h0 : y₂.x ≫ ρ = y.x)
    (p₁ : pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y₂.x) Xo₂.univ.t.G).left)
    (p₂ : pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y₂.x) Xo₂.univ.t.G).left ≫ ν.φ)
    (hw : w.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec Xo₂.univ.t.G) (fun _ => 1)) Xo₂.univ.t.PP.rig
      (ν.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig))
    (hu : ∀ τ i, y₂.u τ i ≫ ν.φ = y.u τ i) (f : c.F →+* c₂.F)
    (hf : ∀ a, algebraMap c₂.F S (f a) = algebraMap c.F S a) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ HH c a n) (k : ℕ) (b : ℤ) (hb : b = k)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L b (ptO Xo y.x)))
    (F₂ : Fin n → LB.Sec (LPow Xo₂.univ.t.G Xo₂.univ.t.PP.L b (ptO Xo₂ y₂.x)))
    (hF : ∀ i, TranslMove.SecRel (T := ptO Xo₂ y₂.x) (T₀ := ptO Xo y.x) w pm (F i) (F₂ i)) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ i, nab y b (F i) (colOf m i) =
      ∑ m ∈ (MvPolynomial.map f P).support, algebraMap c₂.F S ((MvPolynomial.map f P).coeff m) *
        ∏ i, nab₂ y₂ b (F₂ i) (colOf m i) := by
  subst hb
  let _ : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨w', hw', hr', hcub⟩ := ν.lin
  obtain rfl : w = w' := rigidified_iso_unique hG (UnivPol.pol Xo₂) Xo.univ.t.PP.isLB ν.φ w w' hw hw' _ _ hr hr'
  obtain ⟨C, hex, hpin⟩ := hn₂.2 S y₂
  obtain ⟨C', -, -⟩ := hn.2 S y
  choose g hg using fun i => hex k (F₂ i)
  have hA := isAbelianScheme_univ Xo₂
  have hc := (isChart_iff y₂ C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart
  have hfr := (isFrame_iff y₂ C.d C.x _ _ _ _ _ _ C.e).1 C.frame
  have hP₂ := (isPrim_iff C.wP).1 C.prim
  have hP₁ := (isPrim_iff C'.wP).1 C'.prim
  have hc₁ := isChart_push (ν := ν) h0 hc
  have hx : ∀ m, (C.x m).left ≫ ν.φ = (pu ν h0 _ (C.x m)).left := fun _ => rfl
  obtain ⟨e, he₀, he⟩ := exists_frRel (x := fun m => pu ν h0 _ (C.x m)) hw hx C.e hfr.gen
  have g₁ := isFrame_push hG hA hw hcub hc hx he he₀ (const_ad C.B) hfr
  have r₀ : LB.Gen.Corr Xo₂.univ.t.PP.L _ _ _ _ (LB.pullGen Xo₂.univ.t.PP.L _ _
      (eLG Xo₂.univ.t y₂.x C.d C.x C.B.A.act C.e C.wP 0)
        (homAt y₂.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
      (rigT Xo₂.univ.t.G Xo₂.univ.t.PP.L Xo₂.univ.t.PP.rig (overAt y₂.x S) 1) := C.rig0
  have g₂ := rig_push hG hA hw h0 hr hP₁ hP₂ hc hx he r₀
  have e₁ : (fun ℓ : Lt1 Dw => y.u ℓ.1 ℓ.2) = fun ℓ => y₂.u ℓ.1 ℓ.2 ≫ ν.φ := funext fun ℓ => (hu _ _).symm
  have h₁ : IsChart y C.d C.B.G.F C.B.A.act C.uvec (fun m => pu ν h0 _ (C.x m)) := by
    refine (isChart_iff y C.d _ _ _ _).2 ?_
    rw [e₁]
    exact hc₁
  let C₁ : ChartAt Xo c y := ⟨C.d, C.B, C.uvec, fun m => pu ν h0 _ (C.x m), e, C'.wP, C.h, h₁,
    (isFrame_iff y C.d _ _ _ _ _ _ _ e).2 g₁, C'.prim, C.gauge, g₂⟩
  have hg₁ : ∀ i, IsGerm y C₁.d C₁.x C₁.B.A.act C₁.e C₁.wP k (F i) (g i) := fun i =>
    (isGerm_iff y C.d _ _ e _ k (F i) (g i)).2 (isGerm_push hG hA hw hr hP₁ hP₂ hc hc₁ hx he he₀ p₁ p₂
      (fun Z r z J J' hJ hJ' => (hF i Z r z J J' hJ hJ').trans (by rw [zpow_natCast]; rfl))
      ((isGerm_iff y₂ C.d _ _ _ _ k (F₂ i) (g i)).1 (hg i)))
  refine (GlobalTheory.PlaceInt.hv_eq_chartVal E H Dw l Xo c hn.1 nab hn S y C₁ k n F g hg₁ a P hP).trans ?_
  rw [MvPolynomial.support_map_of_injective P f.injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, hf]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => (hpin k (F₂ i) (g i) (hg i) (colOf m i)).symm)

end Chart

theorem comp_act_natCast {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (n : ℕ) :
    t ≫ Xo.univ.t.act.act (n : 𝓞 E) = t ^ n := by
  rw [TwoLifts.act_natCast_eq, mulA, MonObj.comp_pow, Category.comp_id]

theorem natCast_mul_bar (H : Host E) (n : ℕ) : (n : 𝓞 E) * H.bar (n : 𝓞 E) = ((n ^ 2 : ℕ) : 𝓞 E) := by
  rw [map_natCast, Nat.cast_pow, sq]

theorem pulls_of_uu {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {M κ : ℕ} (hN : Odd (M * κ)) (s : SecN Xo x 1)
    {z t : ptO Xo x ⟶ Xo.univ.t.G} (hz : z ^ (M * κ) = 1) (ht : t ^ (M * κ) ^ 2 = 1) (ht' : (t ^ κ) ^ M ^ 2 = 1)
    {F G} (hF : IsUUOver Xo.univ.t.G Xo.univ.t.PP (M * κ) s z t F)
    (hG : IsUUOver Xo.univ.t.G Xo.univ.t.PP M s 1 (t ^ κ) G) :
    Pulls Xo (κ : 𝓞 E) (sqN Xo M G) (sqN Xo (M * κ) F) := by
  have hM : Odd M := (Nat.odd_mul.1 hN).1
  have hz2 : z ^ (M * κ) ^ 2 = 1 := by rw [sq, pow_mul, hz, one_pow]
  obtain ⟨F₀, F₁, a₁, a₂, a₃⟩ := ((uu_through_moves E H Dw l Xo S x _ hN s).1 z t F hz2 ht).1 hF
  obtain ⟨G₀, G₁, b₁, b₂, b₃⟩ := ((uu_through_moves E H Dw l Xo S x _ hM s).1 1 _ G (one_pow _) ht').1 hG
  have mv := fun (k : ℕ) (hk : Odd k) => GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk
  obtain rfl : G₁ = G₀ := (mv _ hM.pow 1 (one_pow _) G₀).1.unique b₂ (mv _ hM.pow 1 (one_pow _) G₀).2
  have a₄ : Moves Xo z F₀ F₀ := moves_of_pulls E H Dw l Xo S x ((M * κ : ℕ) : 𝓞 E) ((M * κ) ^ 2) 1 _
    (natCast_mul_bar H _) (_root_.one_mul _).symm hN.pow 1 z ((comp_act_natCast z _).trans hz) hz2 s s F₀ F₀
    (mv 1 odd_one 1 (one_pow _) s).2 a₁ a₁
  obtain rfl : F₁ = F₀ := (mv _ hN.pow z hz2 F₀).1.unique a₂ a₄
  have pl := fun F => GlobalTheory.existsUnique_pulls E H Dw l Xo S x (κ : 𝓞 E) (κ ^ 2) (M ^ 2) ((M * κ) ^ 2)
    (natCast_mul_bar H _) (mul_pow _ _ _) F
  obtain ⟨A, hA, -⟩ := pl G₁
  obtain ⟨B, hB, -⟩ := pl (sqN Xo M G)
  have hA' := GlobalTheory.PullComp.pulls_mul E H Dw l Xo S x _ _ _ _ _ s G₁ A b₁ hA
  rw [← Nat.cast_mul] at hA'
  obtain rfl : A = F₁ := (GlobalTheory.existsUnique_pulls E H Dw l Xo S x _ ((M * κ) ^ 2) 1 ((M * κ) ^ 2)
    (natCast_mul_bar H _) (_root_.one_mul _).symm s).unique hA' a₁
  have hm := moves_of_pulls E H Dw l Xo S x (κ : 𝓞 E) (κ ^ 2) (M ^ 2) _ (natCast_mul_bar H _) (mul_pow _ _ _) hN.pow
    _ t (comp_act_natCast t κ) ht _ _ A B b₃ hA hB
  rwa [(mv _ hN.pow t ht A).1.unique a₃ hm]

theorem exists_vt_of {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (N : ℕ) {T : Over X}
    (s : LB.Sec (LPow A L.L 1 T)) (t : T ⟶ A) (k : ℤ) (h : (N : ℤ) ^ 2 = k) (F₀ F₁ : LB.Sec (LPow A L.L k T))
    (h₀ : IsNormPull A L (mulA A N) k 1 s F₀) (U : ThetaGrp A L.L k T) (hU : SymLift A L.L k (N ^ 2) t U)
    (h₁ : IsActOf A L.L k U F₀ F₁) : ∃ F, IsVtOver A L N (· = t) s (t ^ N) F := by
  subst h
  obtain ⟨α₀, α, a1, a2, a3, a4⟩ := (TwoLifts.normPull_iff A L N s F₀).1 h₀
  exact ⟨F₁, t, α₀, α, F₀, U, rfl, rfl, a1, a2, a3, a4, hU, h₁⟩

theorem exists_vt {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {M : ℕ} (hM : Odd M) (s : SecN Xo x 1)
    {t : ptO Xo x ⟶ Xo.univ.t.G} (ht : t ^ M ^ 2 = 1) :
    ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP M (· = t) s (t ^ M) F := by
  obtain ⟨F₀, h₀, -⟩ := GlobalTheory.existsUnique_pulls E H Dw l Xo S x _ (M ^ 2) 1 (M ^ 2)
    (natCast_mul_bar H M) (_root_.one_mul _).symm s
  obtain ⟨F₁, ⟨-, U, hU, h₁⟩, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x _ hM.pow t ht F₀).1
  unfold Pulls at h₀
  rw [TwoLifts.act_natCast_eq] at h₀
  exact exists_vt_of _ _ M s t _ (Nat.cast_pow M 2).symm F₀ F₁ h₀ U hU h₁

theorem killedBy_sq {T : Over Xo.X} {t : T ⟶ Xo.univ.t.G} (h₁ : KilledBy Xo l.Mb (t ^ l.M)) {J : Ideal (𝓞 E)}
    (hJ : J ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (h₂ : KilledBy Xo J t) : KilledBy Xo (l.Mb ^ 2) t := by
  let K : Ideal (𝓞 E) :=
    { carrier := {a | t ≫ Xo.univ.t.act.act a = 1}
      add_mem' := fun {a b} ha hb => by
        show t ≫ _ = 1
        rw [Xo.univ.t.act.add, MonObj.comp_mul, show t ≫ _ = 1 from ha, show t ≫ _ = 1 from hb, _root_.mul_one]
      zero_mem' := by
        show t ≫ _ = 1
        rw [← Nat.cast_zero, comp_act_natCast, pow_zero]
      smul_mem' := fun r a ha => by
        have := Xo.univ.t.act.hom r
        show t ≫ _ = 1
        rw [smul_eq_mul, mul_comm, Xo.univ.t.act.mul, ← Category.assoc, show t ≫ _ = 1 from ha, MonObj.one_comp] }
  have k₁ : Ideal.span {(l.M : 𝓞 E)} * l.Mb ≤ K := Ideal.span_singleton_mul_le_iff.2 fun a ha => by
    show t ≫ _ = 1
    rw [Xo.univ.t.act.mul, ← Category.assoc, comp_act_natCast, h₁ a ha]
  have k₂ : J ≤ K := h₂
  show l.Mb ^ 2 ≤ K
  rw [← Ideal.mul_top (l.Mb ^ 2), ← hJ, Ideal.mul_sup]
  refine sup_le (Ideal.mul_le_right.trans k₂) (le_of_eq_of_le ?_ k₁)
  rw [← l.prod, sq, mul_right_comm]

theorem pow_eq_one_of_inZh {m N : ℕ} {T : Over Xo.X} {z : Fin m → (T ⟶ Xo.univ.t.G)}
    (hz : InZh Xo (⟨stdLat E m⟩ : GenLat E m) N z) (b : Fin m) : z b ^ N = 1 := by
  have h := hz.2 1 (fun v hv => by rwa [Matrix.one_mulVec]) (fun i j => if i = j then (N : 𝓞 E) else 0)
    (fun i j => by by_cases e : i = j <;> simp [Matrix.one_apply, e]) b
  rw [List.prod_ofFn, Finset.prod_eq_single b (fun j _ hj => by
    rw [if_neg hj.symm, ← Nat.cast_zero, comp_act_natCast, pow_zero]) (by simp), if_pos rfl, comp_act_natCast] at h
  exact h

section Cover

variable {n : ℕ} (d : DeltaDat Xo c n)

theorem levPt_push (hd : d.IsLev) {S : Type} [CommRing S] {x₂ : Sp S ⟶ d.Xo₂.X} {x₀ : Sp S ⟶ Xo.X}
    (h0 : x₂ ≫ d.r = x₀) (e : (ptO d.Xo₂ x₂ ⟶ d.Xo₂.univ.t.G) →* (ptO Xo x₀ ⟶ Xo.univ.t.G))
    (he : ∀ u, (e u).left = u.left ≫ d.m.φ) {q x : Dw.La} (hq : q ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La))
    (hx : q - (d.pd : 𝓞 E) • x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt d.Xo₂ x₂ q ^ l.M = 1 ∧ e (levPt d.Xo₂ x₂ q) = levPt Xo x₀ x := by
  obtain ⟨-, -, hcop, hMb, -, ⟨heta, -⟩, -⟩ := hd
  have h₁ : levPt d.Xo₂ x₂ q ^ l.M = 1 := by
    rw [levPt, ← MonObj.comp_pow, ← LevelPoints.eta_nsmul, d.Xo₂.univ.eta_ker, MonObj.comp_one]
    rw [hMb, ← Nat.cast_smul_eq_nsmul (𝓞 E), Submodule.mul_smul]
    exact Submodule.smul_mem_smul (LevelPoints.natCast_mem l) hq
  have h₂ : levPt Xo x₀ x ^ l.M = 1 := by
    rw [levPt, ← MonObj.comp_pow, LevelPoints.eta_pow, MonObj.comp_one]
  have h₃ : e (levPt d.Xo₂ x₂ q) ^ d.pd = levPt Xo x₀ x ^ d.pd := by
    have a : Xo.univ.eta q = Xo.univ.eta x ^ d.pd := by
      have := Xo.univ.eta_add (q - (d.pd : 𝓞 E) • x) ((d.pd : 𝓞 E) • x)
      rwa [sub_add_cancel, Xo.univ.eta_ker _ hx, _root_.one_mul, Nat.cast_smul_eq_nsmul,
        LevelPoints.eta_nsmul] at this
    rw [← map_pow, levPt, levPt, ← MonObj.comp_pow, ← MonObj.comp_pow, ← a]
    refine Over.OverMorphism.ext ?_
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, heta, Over.toUnit_left, Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h0)
  refine ⟨h₁, ?_⟩
  have h₄ : e (levPt d.Xo₂ x₂ q) ^ l.M = levPt Xo x₀ x ^ l.M := by rw [← map_pow, h₁, map_one, h₂]
  rw [← div_eq_one, ← pow_one (_ / _), ← hcop, pow_gcd_eq_one, div_pow, div_pow, h₃, h₄, div_self', div_self']
  exact ⟨rfl, rfl⟩

theorem exists_column (hd : d.IsLev) {S : Type} [CommRing S] {x₂ : Sp S ⟶ d.Xo₂.X} {x₀ : Sp S ⟶ Xo.X}
    (h0 : x₂ ≫ d.r = x₀) {w : LB.Iso d.Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull d.m.φ)} (hw : FrameLift.IsRig d w)
    {p : Gx x₂ ⟶ Gx x₀}
    (p₂ : p ≫ (snd (Over.mk x₀) Xo.univ.t.G).left = (snd (Over.mk x₂) d.Xo₂.univ.t.G).left ≫ d.m.φ)
    (p₁ : p ≫ (fst (Over.mk x₀) Xo.univ.t.G).left = (fst (Over.mk x₂) d.Xo₂.univ.t.G).left)
    {s₂ : LB.Sec (PPx x₂)} {s : LB.Sec (PPx x₀)}
    (hs : FrameLift.Rel (q₂ := (snd (Over.mk x₂) d.Xo₂.univ.t.G).left) (q := (snd (Over.mk x₀) Xo.univ.t.G).left)
      w p s₂ s) {q x : Dw.La} (hq : q ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La))
    (hx : q - (d.pd : 𝓞 E) • x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) {κ : ℕ} (hN : Odd (l.M * κ))
    {t : ptO d.Xo₂ x₂ ⟶ d.Xo₂.univ.t.G} (ht : t ^ (l.M * κ) = levPt d.Xo₂ x₂ q) {j : ℕ}
    (hj : KilledBy d.Xo₂ (d.l₂.Mb ^ j) t) :
    ∃ G G₂, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (levPt Xo x₀ x) G ∧
      TranslMove.SecRel (T := ptO d.Xo₂ x₂) (T₀ := ptO Xo x₀) w p G G₂ ∧
      ∀ z F, z ^ (l.M * κ) = 1 → IsUUOver d.Xo₂.univ.t.G d.Xo₂.univ.t.PP (l.M * κ) s₂ z t F →
        Pulls d.Xo₂ (κ : 𝓞 E) (sqN d.Xo₂ l.M G₂) (sqN d.Xo₂ (l.M * κ) F) := by
  have hLaw : Laws := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨e, he⟩ := FrameLift.exists_push d.m.cart h0
  obtain ⟨a₁, a₂⟩ := levPt_push d hd h0 e he hq hx
  have b₁ : (t ^ κ) ^ l.M = levPt d.Xo₂ x₂ q := by rw [← pow_mul, mul_comm, ht]
  have b₂ : (t ^ κ) ^ l.M ^ 2 = 1 := by rw [sq, pow_mul, b₁, a₁]
  have b₃ : t ^ (l.M * κ) ^ 2 = 1 := by rw [sq, pow_mul, ht, pow_mul, a₁, one_pow]
  have b₄ : e (t ^ κ) ^ l.M = levPt Xo x₀ x := by rw [← map_pow, b₁, a₂]
  have b₅ : e (t ^ κ) ^ l.M ^ 2 = 1 := by rw [← map_pow, b₂, map_one]
  have hact : ∀ u b, e (u ≫ d.Xo₂.univ.t.act.act b) = e u ≫ Xo.univ.t.act.act b := fun u b =>
    Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, d.m.act])
  have b₆ : KilledBy Xo (l.Mb ^ 2) (e (t ^ κ)) := by
    refine killedBy_sq (J := d.l₂.Mb ^ j) (fun b hb => ?_) ?_ fun b hb => ?_
    · rw [b₄, levPt, Category.assoc, (GlobalTheory.moduli_univ_eta_killed hLaw E H Dw l Xo x).1 b hb, MonObj.comp_one]
    · refine Ideal.pow_sup_eq_top (top_le_iff.1 (d.l₂.coprime.ge.trans (sup_le_sup_left (Ideal.map_mono hd.1.2.1) _)))
    · rw [← hact, ← comp_act_natCast, Category.assoc, ← d.Xo₂.univ.t.act.mul, hj _ (Ideal.mul_mem_left _ _ hb),
        map_one]
  obtain ⟨G, hG⟩ := exists_vt l.odd s b₅
  obtain ⟨t', -, rfl, hU⟩ := (uu_through_moves E H Dw l Xo S x₀ _ l.odd s).2 _ _ G
    (by rw [← pow_mul, ← sq, b₅]) hG
  have := UnivPol.isLocallyNoetherian d.Xo₂
  have hρ := (maps_iff w _ (fun _ => eSec Xo.univ.t.G) _ d.Xo₂.univ.t.PP.rig Xo.univ.t.PP.rig d.m.cm.e _
    (rigPull_le d.m.cm.F d.m.cm.e d.m.cm.e_comm Xo.univ.t.PP.L) (fun _ => rfl)).1 hw.2
  have hR : TranslMove.SecRel (T := ptO d.Xo₂ x₂) (T₀ := ptO Xo x₀) w p s s₂ := fun Z r z J₀ J hJ₀ hJ => by
    refine (sval_of s (r ≫ p) z J₀ (fun _ => J₀ ((r ≫ (snd (Over.mk x₂) d.Xo₂.univ.t.G).left) ≫ d.m.φ))
      (fun _ => by rw [Category.assoc, p₂, Category.assoc])).trans ?_
    rw [zpow_one]
    exact hs Z r z _ _ (hJ₀ ((r ≫ (snd (Over.mk x₂) d.Xo₂.univ.t.G).left) ≫ d.m.φ))
      (hJ (r ≫ (snd (Over.mk x₂) d.Xo₂.univ.t.G).left))
  obtain ⟨G₂, hG₂, hR₂⟩ := TranslMove.exists_isUUOver d.m.cart (T := ptO d.Xo₂ x₂) (T₀ := ptO Xo x₀) (τ := 𝟙 (Sp S))
    hw.1 (p₁.trans (Category.comp_id _).symm) p₂ d.m.cm.e_comm hρ l.M
    (fun θ => TranslMove.pt_pow_eq_one hLaw.kerPow (UnivPol.pol d.Xo₂) (l.M ^ 2) (Nat.cast_pow l.M 2).symm θ) hR
    (x₁ := 1) (x₂ := t ^ κ) ((Category.id_comp _).trans (by rw [← he, map_one]))
    ((Category.id_comp _).trans (he _)) hU
  refine ⟨G, G₂, ?_, hR₂, fun z F hz hF => pulls_of_uu hN s₂ hz b₃ b₂ hF hG₂⟩
  obtain ⟨t', α₀, α, s₁, U, -, rfl, hrest⟩ := hG
  exact ⟨_, α₀, α, s₁, U, b₄, b₆, hrest⟩

end Cover

theorem nrm_natCast (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (κ : ℕ) :
    nrm Dw c a (κ : 𝓞 E) = (κ : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) := by
  have h := AlphaForm.nrm_mul_nrm Dw c a (κ : 𝓞 E) 1 κ (_root_.mul_one _)
  have h₁ : nrm Dw c a 1 = 1 := by simp [nrm]
  rwa [h₁, _root_.mul_one] at h

theorem exists_value [StarRing (𝓞 E)] {nab : NabV Xo c} {n : ℕ} {d : DeltaDat Xo c n} (hd : d.IsLev)
    (hn : IsNab Xo c nab) (hn₂ : IsNab d.Xo₂ d.c₂ d.nab₂) {m N : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} {x q : Fin m → Dw.La}
    {P : MvPolynomial (LtN Dw m) c.F} (hN : Odd N) (hMN : l.M ∣ N) (hP : P ∈ harmA c a m)
    (hq : ∀ b, q b ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) ∧
      q b - (d.pd : 𝓞 E) • x b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La))
    {k : Type} [Field k] [Algebra c.F k] [Algebra d.c₂.F k]
    (hk : ∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t) {y : FrPt Xo c k} {y₂ : FrPt d.Xo₂ d.c₂ k}
    (hy : FrOver d y₂ y) {t : Fin m → (ptO d.Xo₂ y₂.x ⟶ d.Xo₂.univ.t.G)}
    (ht : ∀ b, t b ^ N = levPt d.Xo₂ y₂.x (q b) ∧ ∃ j : ℕ, KilledBy d.Xo₂ (d.l₂.Mb ^ j) (t b)) :
    ∃ v, ThValAt Xo c nab y x P v ∧ ∀ (z : Fin m → (ptO d.Xo₂ y₂.x ⟶ d.Xo₂.univ.t.G))
      (F : Fin m → LB.Sec (LPow d.Xo₂.univ.t.G d.Xo₂.univ.t.PP.L ((N : ℤ) ^ 2) (ptO d.Xo₂ y₂.x))),
      (∀ b, z b ^ N = 1) → (∀ b, IsUUOver d.Xo₂.univ.t.G d.Xo₂.univ.t.PP N y₂.s (z b) (t b) (F b)) →
      ∑ e ∈ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).support,
        algebraMap d.c₂.F k ((MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).coeff e) *
          ∏ b, d.nab₂ y₂ ((N : ℤ) ^ 2) (F b) (colOf e b) =
        (N : k) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree * v := by
  obtain ⟨κ, rfl⟩ := hMN
  obtain ⟨h0, hu, w, p, hw, p₂, p₁, hs⟩ := (FrameLift.frOver_iff d _ _).1 hy
  choose j hj using fun b => (ht b).2
  choose G G₂ hG hR hpl using fun b => exists_column d hd h0 hw p₂ p₁ hs (hq b).1 (hq b).2 hN (ht b).1 (hj b)
  refine ⟨thExpr Xo c nab y P G, ⟨k, inferInstance, inferInstance, AlgHom.id _ _, y, G,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id, PullbackSections.frMap_refl y, hG, rfl⟩, fun z F hz hF => ?_⟩
  have hs' : Function.Surjective (d.eF : c.F →+* d.c₂.F) := fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
  have hk' : ∀ t : c.F, algebraMap d.c₂.F k ((d.eF : c.F →+* d.c₂.F) t) = algebraMap c.F k t := hk
  generalize (d.eF : c.F →+* d.c₂.F) = f at hs' hk' ⊢
  have hP₂ : MvPolynomial.map f P ∈ HH d.c₂ a m := GlobalTheory.map_mem_HHa Dw.mult m f hs' _ _ _ P hP.1
  have lin := (hv_linear E H Dw d.l₂ d.Xo₂ d.c₂ hn.1 d.nab₂ hn₂ k y₂ m (MvPolynomial.map f P)).2.2
  have e₁ := hv_push hn hn₂ d.m h0 p₁ p₂ hw.1 hw.2 hu f hk' hP.1 (l.M ^ 2) _ (Nat.cast_pow l.M 2).symm G G₂ hR
  have e₂ := hv_pulls E H Dw d.l₂ d.Xo₂ d.c₂ hn.1 d.nab₂ hn₂ k y₂ (κ : 𝓞 E) (κ ^ 2) (l.M ^ 2) ((l.M * κ) ^ 2)
    (natCast_mul_bar H κ) (mul_pow _ _ _) m _ _ (fun b => hpl b (z b) (F b) (hz b) (hF b)) a _ hP₂
  rw [lin, e₂, ← lin, ← e₁, thExpr]
  by_cases hP0 : P = 0
  · simp [hP0]
  have hdeg : (MvPolynomial.map f P).totalDegree = P.totalDegree := by
    rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective P f.injective]
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  have hM : (l.M : k) ≠ 0 := Nat.cast_ne_zero.2 l.odd.pos.ne'
  rw [nrm_natCast, ← AlphaForm.totalDegree_harm c hP hP0, hdeg]
  simp only [map_inv₀, map_pow, map_natCast, Nat.cast_mul, mul_pow]
  field_simp

end GlobalTheory.StdCover

open GlobalTheory.StdCover in
open scoped Classical in

theorem GlobalTheory.shortValAt_std_cover_eq_thValAt : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → IsNab Xo c nab → IsNab d.Xo₂ d.c₂ d.nab₂ → ∀ (m N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (x : Fin m → Dw.La) (P : MvPolynomial (LtN Dw m) c.F) (q₀ : Fin m → LevQ Dw d.l₂), GenLat.LevOK (⟨stdLat E m⟩ : GenLat E m) N d.l₂.M → P ∈ harmA c a m → (∀ b, levRep (q₀ b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) ∧ levRep (q₀ b) - (d.pd : 𝓞 E) • x b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t) → ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∀ v v' : k, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q : Fin m → LevQ Dw d.l₂ => if q = q₀ then (Nat.card (Fin m → LevQ Dw d.l₂) : d.c₂.F) else 0) (⟨stdLat E m⟩ : GenLat E m) 1 N (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) y₂ v → ThValAt Xo c nab y x P v' → v = v' := by
  intro hCI E _ _ _ H Dw l Xo c _ nab n d hd hn hn₂ m N a x P q₀ hN hP hq k _ _ _ _ hk y y₂ hy v v' hv hv'
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := ShortAtField.finite_levQ Dw d.l₂
  obtain ⟨S₁, _, _, φ₁, y₁, z₁, t₁, F₁, hf₁, hm₁, hz₁, hg₁, ht₁, hu₁, e₁⟩ := hv
  beta_reduce at e₁
  have : Nontrivial S₁ := hf₁.injective.nontrivial
  obtain ⟨Ω, _, _, ⟨χ⟩⟩ := ShortAtField.exists_algHom_field d.c₂.F S₁
  obtain ⟨u₂, hu₂⟩ := FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂ S₁ Ω χ y₁
  have hP₂ : MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ HH d.c₂ a m :=
    GlobalTheory.map_mem_HHa Dw.mult m (d.eF : c.F →+* d.c₂.F) (fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩) _ _ _ P hP.1
  obtain ⟨z, t, F, hz, -, ht, hF, e₂⟩ :=
    ShortAtField.exists_pull d.nab₂ hn₂ _ N a _ hP₂ χ y₁ u₂ hu₂ z₁ t₁ F₁ hz₁ hg₁ ht₁ hu₁
  let _ : Algebra c.F Ω := ((algebraMap d.c₂.F Ω).comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  let ψ : k →ₐ[c.F] Ω := ⟨(χ.comp φ₁).toRingHom, fun r => by
    rw [← hk]; exact (χ.comp φ₁).commutes _⟩
  obtain ⟨u, hu⟩ := FramedBaseChange.exists_frMap hL E H Dw l Xo c k Ω ψ y
  have hy' : FrOver d u₂ u :=
    FrameLift.frOver_map d (ψ := ψ) (ψ₂ := χ.comp φ₁) rfl hy hu (FramedBaseChange.trans φ₁ χ hm₁ hu₂)
  obtain ⟨w, hw, e₃⟩ := exists_value hd hn hn₂ hN.1 (hd.1.1.trans hN.2.1) hP hq (fun _ => rfl) hy' (ht q₀)
  have e₄ := GlobalTheory.thetaValue_natural hL hCI E H Dw l Xo c nab hn k Ω ψ y u hu a m x P hP v' w hv' hw
  apply ψ.toRingHom.injective
  change χ (φ₁ v) = ψ v'
  rw [e₄, e₁, finsum_eq_single _ q₀ (fun q hq => by rw [if_neg hq, map_zero, zero_mul]), if_pos rfl, map_mul,
    map_mul χ, e₂, χ.commutes, χ.commutes,
    Finset.sum_congr rfl fun i _ => e₃ (z i) (F q₀ i) (pow_eq_one_of_inZh (hz i)) (hF q₀ i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h₁ : GenLat.zCard (⟨stdLat E m⟩ : GenLat E m) N (Dw.p + Dw.q) =
      GenLat.mIdx (⟨stdLat E m⟩ : GenLat E m) N (Dw.p + Dw.q) := by
    unfold GenLat.zCard GenLat.mIdx GenLat.Ln
    rw [inf_idem]
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap d.c₂.F Ω).injective
  have h₂ : (GenLat.mIdx (⟨stdLat E m⟩ : GenLat E m) N (Dw.p + Dw.q) : Ω) ≠ 0 := Nat.cast_ne_zero.2
    (TrivLattice.index_part _ N _ 2 1 hN Nat.prime_two (Nat.coprime_one_left 2) (fun v hv => by rwa [one_smul]) _).2
  have h₃ : (Nat.card (Fin m → LevQ Dw d.l₂) : Ω) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h₄ : (N : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN.1.pos.ne'
  rw [h₁, nsmul_eq_mul]
  simp only [map_mul, map_inv₀, map_natCast, map_pow, map_one]
  field_simp
