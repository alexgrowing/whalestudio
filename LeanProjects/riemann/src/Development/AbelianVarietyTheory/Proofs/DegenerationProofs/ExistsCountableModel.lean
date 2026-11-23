import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCountableClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompRel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOverSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPairDescentAlgClosedSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesIsoFieldPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsPullQk
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull GlobalTheory.TorusExt GlobalTheory.QkPullEquiv

attribute [local instance] gtGroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Exact
variable {R R' R'' F F' F'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R'']
  [Field F] [Field F'] [Field F''] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F']
  [Algebra (FractionRing R'') F'']

def Exact (f : F →+* F') (A : ArcF D R F) (A' : ArcF D R' F') : Prop :=
  ∃ I : NumD.Hom f A.N A'.N, f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧
    (∀ a y, I.e (A.act a y) = A'.act a (I.e y)) ∧
    ∀ n a, 0 < n → (A'.q n a).1.1.toAdd = I.e (A.q n a).1.1.toAdd ∧ I.Rel (A.q n a).1.2 (A'.q n a).1.2

theorem Exact.over {f : F →+* F'} {A : ArcF D R F} {A' : ArcF D R' F'} (h : Exact f A A') : A.Over f A' := by
  obtain ⟨I, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨I, h₁, h₂, h₃, fun n a hn => ⟨_, (h₄ n a hn).1, (h₄ n a hn).2, (A'.N.qEq_equivalence n).refl _⟩⟩

theorem Exact.comp {f : F →+* F'} {g : F' →+* F''} {A : ArcF D R F} {A' : ArcF D R' F'} {A'' : ArcF D R'' F''}
    (h : Exact f A A') (h' : Exact g A' A'') : Exact (g.comp f) A A'' := by
  obtain ⟨I, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨I', k₁, k₂, k₃, k₄⟩ := h'
  exact ⟨HomCalc.comp I I', (congrArg g h₁).trans k₁, fun n hn => (congrArg g (h₂ n hn)).trans (k₂ n hn),
    fun a y => (congrArg I'.e (h₃ a y)).trans (k₃ a _), fun n a hn =>
      ⟨(k₄ n a hn).1.trans (congrArg I'.e (h₄ n a hn).1), HomCalc.comp_rel (h₄ n a hn).2 (k₄ n a hn).2⟩⟩
end Exact

section Pull
variable {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing K) F] {φ : R →+* K}

theorem exact_of_pull (hG : GlobalFnsSt) {A : ArcF D R F} {A' : ArcF D K F} (hD : IsPullDeg φ A.D₀ A'.D₀)
    (hF : ArcPull.Compat φ F) (hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y) (hρ : A.ρ = A'.ρ) (hζ : A.I.ζ = A'.I.ζ)
    (hev : ∀ n a, A'.I.ev n a = pullQk hD hG hF A.bimult A'.bimult (A.I.ev n a)) :
    Exact (RingHom.id F) A A' ∧ Exact (RingHom.id F) A' A := by
  obtain ⟨I, he, hr⟩ := GlobalTheory.T.exists_degenerationValuesIso_fieldPullback hG R K φ _ _ hD F hF _ _ A.ν A'.ν
  have act : ∀ a y, I.e (A'.act a y) = A.act a (I.e y) := fun a y => A.ν.eX.injective (by
    rw [he, ArcF.act, ArcF.act, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, he, hx])
  have hq : ∀ n a, (A.q n a).1.1.toAdd = I.e (A'.q n a).1.1.toAdd ∧ I.Rel (A'.q n a).1.2 (A.q n a).1.2 := fun n a => by
    obtain ⟨a₁, a₂⟩ := (eq_pullQk_iff hD hG hF _ _ _ _).1 (hev n a)
    refine ⟨A.ν.eX.injective ?_, hr _ _ _ _ (A.hq n a).2 (A'.hq n a).2 a₂⟩
    rw [he, (A.hq n a).1, (A'.hq n a).1, a₁, AddEquiv.apply_symm_apply]
  refine ⟨⟨HomCalc.inv I, hρ, fun n _ => congrArg (fun z => ((z n : Fˣ) : F)) hζ, fun a y => ?_, fun n a _ =>
    ⟨I.e.eq_symm_apply.2 (hq n a).1.symm, HomCalc.inv_rel (hq n a).2⟩⟩,
    ⟨TateInh.homOfIso I, hρ.symm, fun n _ => congrArg (fun z => ((z n : Fˣ) : F)) hζ.symm, act, fun n a _ => hq n a⟩⟩
  refine I.e.symm_apply_eq.2 ?_
  rw [act]
  exact congrArg (A.act a) (I.e.apply_symm_apply y).symm

theorem exists_pushTate (hG : GlobalFnsSt) {D₀ : DegPre R} {D' : DegPre K} (hD : IsPullDeg φ D₀ D')
    [Module (𝓞 E) D₀.X] [Module (𝓞 E) D'.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {oa' : letI := H.starRing; D'.OAct (𝓞 E)}
    (hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y)
    (ho : letI := H.starRing; ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left)
    (hB : D₀.TauBimult) (hB' : D'.TauBimult) (hF : ArcPull.Compat φ F) (I' : TateIsoQ D D' oa' F) :
    ∃ I : TateIsoQ D D₀ oa F, I.ζ = I'.ζ ∧ ∀ n a, I'.ev n a = pullQk hD hG hF hB hB' (I.ev n a) := by
  let _ := H.starRing
  choose ev hev using fun n a => pullQk_surjective hD hG hF hB hB' (I'.ev n a)
  refine ⟨{ ζ := I'.ζ, ζ_prim := I'.ζ_prim, ζ_pow := I'.ζ_pow, ev := ev, add := fun n hn a b => ?_,
            lin := fun n hn x a => ?_, ker := fun n hn a b => ?_, onto := fun n hn p => ?_,
            tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ }, rfl, fun n a => (hev n a).symm⟩
  · rw [qkAdd_pullQk_iff hD hG hF hB hB', hev, hev, hev]; exact I'.add n hn a b
  · rw [qkAct_pullQk_iff hD hG hF hB hB' hx ho, hev, hev]; exact I'.lin n hn x a
  · rw [← equiv_pullQk hD hG hF hB hB', hev, hev]; exact I'.ker n hn a b
  · obtain ⟨a, ha⟩ := I'.onto n hn (pullQk hD hG hF hB hB' p)
    exact ⟨a, by rw [← equiv_pullQk hD hG hF hB hB', hev]; exact ha⟩
  · obtain ⟨q', h₁, h₂, h₃⟩ := I'.tower n m hn hm a
    obtain ⟨q, rfl⟩ := pullQk_surjective hD hG hF hB hB' q'
    rw [← hev] at h₁ h₂ h₃
    refine ⟨q, hD.xe.symm.injective h₁, (isNsmul_iff_eq _ _ _).2 (pullGt_injective hD hG hF ?_),
      (equiv_pullQk hD hG hF hB hB' _ _).1 h₃⟩
    rw [map_nsmul]; exact (isNsmul_iff_eq _ _ _).1 h₂
  · rw [weilQkIs_pullQk_iff hD hG hF hB hB', hev, hev]; exact I'.isom n hn a b

theorem det_iff {D₀ : DegPre R} {D' : DegPre K} (hD : IsPullDeg φ D₀ D') [Module (𝓞 E) D₀.X] [Module (𝓞 E) D'.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {oa' : letI := H.starRing; D'.OAct (𝓞 E)}
    (hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y)
    (ho : letI := H.starRing; ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left)
    (hF : ArcPull.Compat φ F) (τ : 𝓞 E →+* F) (m : ℕ) : letI := H.starRing
    (∃ n, LieMult (ofRingAct oa'.onB.toRingAct) (spMap ((algebraMap (FractionRing K) F).comp (algebraMap K _))) τ n ∧
      n + Module.finrank (𝓞 E) D'.X = m) ↔
    ∃ n, LieMult (ofRingAct oa.onB.toRingAct) (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧
      n + Module.finrank (𝓞 E) D₀.X = m := by
  let _ := H.starRing
  refine exists_congr fun n => and_congr ?_ ?_
  · rw [LiePull.lieMult_pull _ _ _ _ _ _ _ (ofRingAct oa.onB.toRingAct) _ (pull_grp hD) ho F _ τ n, ← spMap_comp,
      show ((algebraMap (FractionRing K) F).comp (algebraMap K _)).comp φ =
        (algebraMap (FractionRing R) F).comp (algebraMap R _) from RingHom.ext fun r => (hF r).symm]
  · rw [(({ hD.xe with map_smul' := hx } : D'.X ≃ₗ[𝓞 E] D₀.X)).finrank_eq]

theorem exists_values (hL : Laws) (hGt : BrGtSt) [IsAlgClosed F] (D' : DegPre K) (he : D'.PsiEven) (hB : D'.TauBimult) :
    ∃ (N : NumD F) (ν : NumOf D' F N), ∀ k (p : QkPt D' F k), ∃ q, ν.QPt p q := by
  obtain ⟨N, ν, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL K D' he hB F ⊤ fun _ => trivial
  exact ⟨N, ν, fun k p => (((hGt K D' he hB F N ν).2.2.2.2 k).1 p).exists⟩

theorem exists_up (hL : Laws) (hGt : BrGtSt) [IsAlgClosed F] (hF : ArcPull.Compat φ F) (A : ArcF D R F) :
    ∃ A' : ArcF D K F, Exact (RingHom.id F) A' A := by
  let _ := H.starRing
  have hG := hL.globalFns
  have hφ : Function.Injective φ := fun x y h => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective ((hF x).trans (h ▸ (hF y).symm)))
  obtain ⟨W, hW, hψ⟩ := PsiSpread.exists_psiOn A.D₀ A.bimult
  obtain ⟨D', hD, -, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange R K φ A.D₀ W hψ (by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of K))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ hφ)
    rw [this]; exact hW)
  let _ : Module (𝓞 E) D'.X := hD.xe.module (𝓞 E)
  have hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y := fun a y => hD.xe.apply_symm_apply _
  have hB' := TauPull.tauBimult_pull hG hD A.bimult
  have he' := psiEven_pull hG _ _ φ _ _ hD A.even
  obtain ⟨oa', ho⟩ := exists_oAct hD hG hφ A.oa hx
  obtain ⟨N, ν, hq⟩ := exists_values (F := F) hL hGt D' he' hB'
  choose q hq using hq
  let A' : ArcF D K F :=
    { D₀ := D', oa := oa', even := he', bimult := hB', w0 := traceFormTwistIso_of_pullback hD hφ hx ho A.w0, ρ := A.ρ, ρ_sq := A.ρ_sq,
      det := fun τ => (det_iff hD hx ho hF τ _).2 (A.det τ), I := pullTate hG hD hx ho A.bimult hB' hF A.I,
      N := N, ν := ν, q := fun n a => q n _, hq := fun n a => hq n _, closed := inferInstance }
  exact ⟨A', (exact_of_pull hG (A := A) (A' := A') hD hF hx rfl rfl fun _ _ => rfl).2⟩

end Pull

theorem exists_down (hL : Laws) (hGt : BrGtSt) {K F : Type} [Field K] [IsAlgClosed K] [Field F] [IsAlgClosed F]
    [Algebra (FractionRing K) F] (A' : ArcF D K F) :
    ∃ (K₁ : Type) (_ : Field K₁) (_ : IsAlgClosed K₁) (_ : Countable K₁) (_ : Algebra (FractionRing K₁) F)
      (A : ArcF D K₁ F), Exact (RingHom.id F) A A' := by
  let _ := H.starRing
  have hG := hL.globalFns
  obtain ⟨K₁, _, _, _, β, D₁, hD, _, oa, hx, ho, he, hB, hw⟩ := exists_data hL A'.D₀ A'.oa
  let _ : Algebra (FractionRing K₁) F := ((algebraMap (FractionRing K) F).comp (fracMap β.injective)).toAlgebra
  have hF : ArcPull.Compat β F := fun x => congrArg (algebraMap (FractionRing K) F) (fracMap_algebraMap β.injective x)
  obtain ⟨I, hζ, hev⟩ := exists_pushTate hG hD hx ho (hB A'.bimult) A'.bimult hF A'.I
  obtain ⟨N, ν, hq⟩ := exists_values (F := F) hL hGt D₁ (he A'.even) (hB A'.bimult)
  choose q hq using hq
  let A : ArcF D K₁ F :=
    { D₀ := D₁, oa := oa, even := he A'.even, bimult := hB A'.bimult, w0 := hw _ A'.w0, ρ := A'.ρ, ρ_sq := A'.ρ_sq,
      det := fun τ => (det_iff hD hx ho hF τ _).1 (A'.det τ), I := I,
      N := N, ν := ν, q := fun n a => q n _, hq := fun n a => hq n _, closed := inferInstance }
  exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, A,
    (exact_of_pull hG (A := A) (A' := A') hD hF hx rfl hζ hev).1⟩

theorem mem_range_of_pow_eq {F F' : Type} [Field F] [IsAlgClosed F] [Field F'] (f : F →+* F') {n : ℕ} (hn : 0 < n)
    {x : F'} {c : F} (h : x ^ n = f c) : ∃ y, f y = x :=
  (IsAlgClosed.splits (Polynomial.X ^ n - Polynomial.C c)).mem_range_of_isRoot
    (Polynomial.X_pow_sub_C_ne_zero hn c) (i := f) (x := x) (by simp [h])

theorem exists_sub (hL : Laws) (hGt : BrGtSt) (hWp : BrWpSt) {R F F' : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (A' : ArcF D R F') :
    ∃ A : ArcF D R F, Exact f A A' := by
  let _ := H.starRing
  have hG := hL.globalFns
  have hB := A'.bimult
  obtain ⟨N, ν, I, he, hr⟩ := GlobalTheory.T.exists_degenerationValues_over_subfield hG R A'.D₀ A'.even hB F F' f hf _ A'.ν
  choose q hq using fun k (p : QkPt A'.D₀ F k) => (((hGt R _ A'.even hB F N ν).2.2.2.2 k).1 p).exists
  obtain ⟨ρ, hρ⟩ := mem_range_of_pow_eq f two_pos (c := -(H.d : F)) (A'.ρ_sq.trans (by simp))
  have : ∀ n, ∃ z : Fˣ, 0 < n → f z = A'.I.ζ n := fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨1, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨y, hy⟩ := mem_range_of_pow_eq f hn (x := A'.I.ζ n) (c := 1) (by
        rw [← Units.val_pow_eq_pow_val, (A'.I.ζ_prim n hn).pow_eq_one, map_one, Units.val_one])
      exact ⟨Units.mk0 y fun h => (A'.I.ζ n).ne_zero (by rw [← hy, h, map_zero]), fun _ => hy⟩
  choose ζ hζ using this
  have hζ' : ∀ n, 0 < n → Units.map f.toMonoidHom (ζ n) = A'.I.ζ n := fun n hn => Units.ext (hζ n hn)
  have inj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have : ∀ n a, ∃ p : QkPt A'.D₀ F n, 0 < n → qkExt hB f hf p = A'.I.ev n a := fun n a => by
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨qkZero hB F 0, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨p, hp⟩ := GlobalTheory.T.exists_torsionPair_descent_algClosed_subfield hL R _ hB F F' f hf n hn (A'.I.ev n a)
      exact ⟨p, fun _ => ((qkExt_iff hB f hf _ _).1 hp).symm⟩
  choose ev hev using this
  have eqv : ∀ {n} (p p' : QkPt A'.D₀ F n), QkPt.Equiv _ F' (qkExt hB f hf p) (qkExt hB f hf p') ↔ QkPt.Equiv _ F p p' :=
    fun p p' => ⟨fun h => by
      obtain ⟨z, h₁, h₂⟩ := (equiv_iff hB _ _).1 h
      refine (equiv_iff hB _ _).2 ⟨z, h₁, Balanced.gtExt_injective f hf _ ?_⟩
      rw [map_add, gtExt_iota]; exact h₂, qkExt_congr hB f hf⟩
  have rel : ∀ n a, 0 < n → (A'.q n a).1.1.toAdd = I.e (q n (ev n a)).1.1.toAdd ∧
      I.Rel (q n (ev n a)).1.2 (A'.q n a).1.2 := fun n a hn =>
    ⟨A'.ν.eX.injective (by rw [he, (hq n _).1, (A'.hq n a).1, ← hev n a hn]; rfl),
      hr n _ _ _ _ ((qkExt_iff hB f hf _ _).2 (hev n a hn).symm) (hq n _).2 (A'.hq n a).2⟩
  let T : TateIsoQ D A'.D₀ A'.oa F :=
    { ζ := ζ
      ζ_prim := fun n hn => IsPrimitiveRoot.of_map_of_injective (hζ' n hn ▸ A'.I.ζ_prim n hn) inj
      ζ_pow := fun n m hn hm => inj (by
        rw [map_pow, hζ' _ (Nat.mul_pos hn hm), hζ' n hn, A'.I.ζ_pow n m hn hm])
      ev := ev
      add := fun n hn a b => by
        rw [qkAdd_iff hB, ← eqv, qkExt_qkAdd, ← qkAdd_iff hB, hev n _ hn, hev n _ hn, hev n _ hn]
        exact A'.I.add n hn a b
      lin := fun n hn x a => by
        rw [qkAct_iff hB hG, ← eqv, qkExt_qkSmul, ← qkAct_iff hB hG, hev n _ hn, hev n _ hn]
        exact A'.I.lin n hn x a
      ker := fun n hn a b => by rw [← eqv, hev n _ hn, hev n _ hn]; exact A'.I.ker n hn a b
      onto := fun n hn p => by
        obtain ⟨a, ha⟩ := A'.I.onto n hn (qkExt hB f hf p)
        exact ⟨a, by rw [← eqv, hev n _ hn]; exact ha⟩
      tower := fun n m hn hm a => by
        obtain ⟨q', h₁, h₂, h₃⟩ := A'.I.tower n m hn hm a
        rw [← hev _ _ (Nat.mul_pos hn hm)] at h₁ h₂
        rw [← hev _ _ hn] at h₃
        let p := qkMk hB (k := n) (ev (n * m) a).y (m • (ev (n * m) a).g) (by rw [← mul_nsmul', qk_nsmul hB])
        have e : qkExt hB f hf p = q' :=
          qk_ext h₁.symm ((map_nsmul (gtExt _ f hf) _ _).trans ((isNsmul_iff_eq _ _ _).1 h₂).symm)
        exact ⟨p, rfl, (isNsmul_iff_eq _ _ _).2 rfl, (eqv _ _).1 (e ▸ h₃)⟩
      isom := fun n hn a b => by
        refine (hWp R _ A'.even hB F N ν n hn _ _ _ _ _ (hq n _) (hq n _)).2 (congrArg Units.val (inj ?_))
        have u := (hWp R _ A'.even hB F' _ A'.ν n hn _ _ _ _ _ (A'.hq n a) (A'.hq n b)).1 (A'.I.isom n hn a b)
        rw [map_zpow, hζ' n hn, Units.ext u]
        exact (NumD.hom_transport _ _ f _ _ I).2.2.2.1 n _ _ _ _ (rel n a hn).1 (rel n a hn).2 (rel n b hn).1
          (rel n b hn).2 }
  let A : ArcF D R F :=
    { D₀ := A'.D₀, oa := A'.oa, even := A'.even, bimult := hB, w0 := A'.w0, ρ := ρ
      ρ_sq := f.injective (by rw [map_pow, hρ, A'.ρ_sq]; simp)
      det := fun τ => by
        obtain ⟨n, h₁, h₂⟩ := A'.det (f.comp τ)
        have := A'.D₀.P.isAb.smooth
        refine ⟨n, (DetExtend.lieMult_extend f _ _ τ n).1 ?_, h₂.trans ?_⟩
        · rw [← spMap_comp, ← RingHom.comp_assoc, hf]; exact h₁
        · rw [← hρ, RingHom.comp_apply, f.injective.eq_iff]
      I := T, N := N, ν := ν, q := fun n a => q n _, hq := fun n a => hq n _, closed := inferInstance }
  refine ⟨A, I, hρ, hζ, fun a y => A'.ν.eX.injective ?_, rel⟩
  rw [he, ArcF.act, ArcF.act, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, he]

theorem exists_countable_model : Laws → BrGtSt → BrWpSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (A : ArcF D R F), ∃ (R₁ F₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (_ : Algebra (FractionRing R₁) F₁) (f : F₁ →+* F) (A₁ : ArcF D R₁ F₁), A₁.Over f A := by
  intro hL hGt hWp E _ _ _ H D R _ _ F _ _ _ _ A
  let _ : Algebra (FractionRing F) F := (FractionRing.algEquiv F F).toRingHom.toAlgebra
  obtain ⟨A₃, h₃⟩ := exists_up (K := F) (φ := (algebraMap (FractionRing R) F).comp (algebraMap R _)) hL hGt
    (fun r => ((FractionRing.algEquiv F F).commutes _).symm) A
  obtain ⟨K₁, _, _, _, _, A₂, h₂⟩ := exists_down hL hGt A₃
  let _ : Algebra (FractionRing K₁) K₁ := (FractionRing.algEquiv K₁ K₁).toRingHom.toAlgebra
  let f : K₁ →+* F := (algebraMap (FractionRing K₁) F).comp (FractionRing.algEquiv K₁ K₁).symm.toRingHom
  have : CharZero K₁ := f.charZero
  obtain ⟨A₁, h₁⟩ := exists_sub hL hGt hWp f (RingHom.ext fun x =>
    congrArg (algebraMap (FractionRing K₁) F) ((FractionRing.algEquiv K₁ K₁).symm_apply_apply x)) A₂
  exact ⟨K₁, K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, A₁,
    ((h₁.comp h₂).comp h₃).over⟩

end GlobalTheory.FieldPull
end
