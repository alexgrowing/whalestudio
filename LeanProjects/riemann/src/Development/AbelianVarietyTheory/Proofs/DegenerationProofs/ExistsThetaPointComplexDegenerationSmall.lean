import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValues
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AnalyticDictionaryIsPointPeriodOrigin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PeriodConstantPartEqZeroInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubNFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxStOfPtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSumAppellHumbert
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullEndo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VFEqGenValMul
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymPmaps
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StalkUnitsSymmGm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DifferentiableQuot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValIsoChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibLieOfLaws
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VFCorr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLogFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPtNsmul
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraceEqSumFinrank
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TripleStOfLaws
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Reframe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ObjStOfTripleReframe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem isThetaPt_classical (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (P : PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (N : ℕ)
    {I : Type} (x : I → (baseOver (Sp ℂ) ⟶ P.A)) (l : I → u.Λ) (hN : Odd N) (hAH : u.IsAH Hm χ)
    (hθ : u.IsThetaFn Hm χ 1 θ) (h0 : θ ≠ 0) (hx : ∀ i, x i = u.ex (((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))) :
    IsThetaPt P N x fun i => fnOf (χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i)) *
      θ ((N : ℂ)⁻¹ • (l i : Fin P.g → ℂ))) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  refine ⟨hN, isUnit_natCast_sp hN0, fun q => ⟨⊤, trivial, ?_⟩⟩
  let T : Over (Sp ℂ) := overRes (T := baseOver (Sp ℂ)) ⊤
  haveI : IsIso T.hom := by
    show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id]
    exact inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ T := Over.homMk (inv T.hom) (by simp)
  have hp : p ≫ overResι (T := baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by
    ext1
    show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _
    rw [IsIso.inv_comp_eq]
    rfl
  have htor : ∀ i, x i ^ (N ^ 2) = 1 := fun i => by
    rw [hx]
    refine (ThetaClassical.ex_nsmul u _ _).symm.trans ((u.ker _).2 ?_)
    rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_pow, smul_inv_smul₀ (pow_ne_zero _ hN0)]
    exact (l i).2
  have key := ThetaClassical.isThetaPtOver hL hL2 hT P u Hm χ θ N T p (fun i => overResι ⊤ ≫ x i) l
    hN hAH hθ h0 (fun i => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x i) hp).trans
      ((Category.id_comp _).trans (hx i))))
    (fun i => ThetaClassical.exists_symLift hL P (N ^ 2) _ (by push_cast; rfl) hN.pow (x i) (htor i))
  convert key using 2 with i
  exact ThetaClassical.constFn_top _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso (D : Datum H) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La)
    (Q : PolAV (Sp ℂ)) (act : 𝓞 E → (Q.A ⟶ Q.A)) (hact : ∀ c, IsMonHom (act c)) {g : ℕ} (u : HolUnif Q.A Q.L g)
    (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P) (hker : ∀ z, z ∈ u.Λ ↔ ∃ a, z = P a)
    (hlin : ∀ (c : 𝓞 E) (s : ℂ) a, u.ex (s • P (c • a)) = u.ex (s • P a) ≫ act c)
    (hW : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (ζ : ℕ → ℂˣ) (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (f : ℕ → D.La → La) (hf : IsTower D EF ζ f) :
    ∃ I : TateIso D ℂ (baseOver (Sp ℂ) ⟶ Q.A) (fun a x => x ≫ act a) (fun n x x' c => WeilIs Q.A Q.L n x x' (unitOn c)),
      I.ζ = ζ ∧ ∀ (n : ℕ) a, I.ev n a = u.ex ((n : ℂ)⁻¹ • P (f n a)) := by
  let e : (Fin g → ℂ) → (baseOver (Sp ℂ) ⟶ Q.A) := u.ex
  have eadd : ∀ z w, e (z + w) = e z * e w := u.ex_add
  have eker : ∀ z, e z = 1 ↔ ∃ a, z = P a := fun z => (u.ker z).trans (hker z)
  have epow : ∀ z (n : ℕ), e z ^ n = e (n • z) := fun z n => (ThetaClassical.ex_nsmul u z n).symm
  have e0 : e 0 = 1 := (eker 0).2 ⟨0, (map_zero P).symm⟩
  have hn : ∀ n : ℕ, 0 < n → (n : ℂ) ≠ 0 := fun n h => Nat.cast_ne_zero.2 h.ne'
  have sm : ∀ n : ℕ, 0 < n → ∀ a, (n : ℂ)⁻¹ • P (n • a) = P a := fun n h a => by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  have sm' : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n h z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (hn n h)]
  have md : ∀ n : ℕ, 0 < n → ∀ a b, e ((n : ℂ)⁻¹ • P (a + n • b)) = e ((n : ℂ)⁻¹ • P a) := fun n h a b => by
    rw [map_add, smul_add, eadd, sm n h, (eker _).2 ⟨b, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := ζ, ζ_prim := hp, ζ_pow := hc, ev := fun n a => e ((n : ℂ)⁻¹ • P (f n a)), add := fun n a b => ?_,
            lin := fun n c a => ?_, ker := fun n h a => ?_, onto := fun n h x => ⟨fun hx => ?_, ?_⟩,
            tower := fun n m h h' a => ?_, isom := fun n h a b => ?_ }, rfl, fun _ _ => rfl⟩
  · rcases n.eq_zero_or_pos with rfl | h
    · simp only [Nat.cast_zero, inv_zero, zero_smul, e0, _root_.mul_one]
    · obtain ⟨c, hc⟩ := (hf n h).1 a b
      rw [hc, md n h, map_add, smul_add, eadd]
  · rcases n.eq_zero_or_pos with rfl | h
    · haveI := hact c
      simp only [Nat.cast_zero, inv_zero, zero_smul, e0, MonObj.one_comp]
    · obtain ⟨b, hb⟩ := (hf n h).2.1 c a
      rw [hb, md n h]
      exact hlin c _ _
  · rw [← (hf n h).2.2.1 a, eker]
    refine exists_congr fun b => ⟨fun hb => hinj ?_, fun hb => by rw [hb, sm n h]⟩
    rw [map_nsmul, ← hb, sm' n h]
  · obtain ⟨z, rfl⟩ : ∃ z, e z = x := u.ex_onto x
    rw [epow, eker] at hx
    obtain ⟨b, hb⟩ := hx
    obtain ⟨a, c, rfl⟩ := (hf n h).2.2.2.1 b
    refine ⟨a, ?_⟩
    rw [← md n h _ c, ← hb, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  · rintro ⟨a, rfl⟩
    rw [epow, sm' n h]
    exact (eker _).2 ⟨_, rfl⟩
  · obtain ⟨b, hb⟩ := (hf n h).2.2.2.2.1 m h' a
    rw [epow, hb, Nat.cast_mul, mul_inv, mul_comm, mul_smul, sm' m h', md n h]
  · exact hW n _ _ _ h ((hf n h).2.2.2.2.2 a b)

theorem exists_log (T : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ < Real.exp (-(2 * Real.pi * T))) :
    ∃ w : ℂ, T < w.im ∧ (u : ℂ) = eTwoPi w := by
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : (u : ℂ) = eTwoPi (Complex.log u / (2 * Real.pi * Complex.I)) := by
    rw [eTwoPi, mul_div_cancel₀ _ h2, Complex.exp_log u.ne_zero]
  refine ⟨_, ?_, e⟩
  generalize Complex.log u / (2 * Real.pi * Complex.I) = w at e
  rw [e, eTwoPi, Complex.norm_exp, Real.exp_lt_exp] at hu
  simp at hu
  have := Real.pi_pos
  nlinarith

theorem of_steps (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (hdict : DictSt) (htow : TowerSt) (hty : TypeSt)
    (hobj : ObjSt) (hth : ThetaSt) (htx : TxSt) : AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := by
  intro E _ _ _ H D R _ _ _ A hρ k β hβ m hm hodd
  letI := H.starRing
  obtain ⟨B, d, hact, hbe, hprim, hth0, hsig⟩ := hdict E H D R A k β hβ
  obtain ⟨f, hf, hrep⟩ := htow E H D R A B d hact
  obtain ⟨g, ty, h, htyp, hh⟩ := hty E H D B (hρ ▸ hsig)
  obtain ⟨-, hbij, hadj, T₁, hT₁⟩ := B.periods_polarised
  obtain ⟨T₂, hT₂⟩ := B.exists_convergence
  have hmem : d.th ∈ B.Theta 1 0 := d.ab.2.2.2.2.2.2.2.1
  obtain ⟨-, hsum, -, hdiff, -⟩ := hT₂ 1 0 d.th hmem
  refine ⟨Real.exp (-(2 * Real.pi * max T₁ T₂)), Real.exp_pos _, fun u hu => ?_⟩
  obtain ⟨w, hw, huw⟩ := exists_log _ u hu
  have hw₁ : T₁ < w.im := (le_max_left _ _).trans_lt hw
  have hw₂ : T₂ < w.im := (le_max_right _ _).trans_lt hw
  have hm2 : 0 < m ^ 2 := pow_pos hodd.pos 2
  have hterm := fun x => htx (𝓞 E) A.N B d H.w0 hprim k β hbe m hm hodd w u huw _ _ (hrep _ hm2 x)
  refine ⟨fun x => ?_, ?_⟩
  · refine (d.eX.toEquiv.summable_iff (f := fun χ : A.N.X => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖)).1 ?_
    exact ((hsum w hw₂ ((m : ℂ)⁻¹ • B.Pw w (f (m ^ 2) x))).mul_left _).congr fun y =>
      (norm_mul _ _).symm.trans (congrArg norm (hterm x y).symm)
  obtain ⟨-, -, hlin, -, hspan, -, -, -, hper⟩ := hT₁ w hw₁
  let P : B.La →+ (Fin g → ℂ) := h.toLinearMap.toAddMonoidHom.comp (B.Pw w)
  obtain ⟨hinj, hdisc, hsp, Hm, hherm, hpos, him⟩ := hper g h P fun _ => rfl
  have hPlin : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x i =>
    (congrArg (fun v => h v i) (hlin a x)).trans (hh a _ i)
  obtain ⟨Q, oa, U, Hm', χ, F, hΛ, hpr, hdet, hAH, hΛ', him', hχ, hex, hW⟩ :=
    hobj E H D B.La B.EF g ty P Hm htyp hbij hadj hPlin hinj hdisc hsp hherm hpos him
  let P' : B.La →+ (Fin Q.g → ℂ) := F.toLinearMap.toAddMonoidHom.comp P
  obtain ⟨I, hI, hev⟩ := exists_tateIso D B.EF Q oa.act oa.hom U P' (F.injective.comp hinj)
    (fun z => ⟨hΛ' z, fun ⟨a, ha⟩ => ha ▸ hΛ a⟩) (fun c s a => by
      have := hex c (s • P a)
      rw [map_smul] at this
      refine Eq.trans (congrArg U.ex ?_) this
      refine (map_smul F s _).symm.trans (congrArg F (funext fun i => ?_))
      simp only [Pi.smul_apply, hPlin, smul_eq_mul]
      ring) hW A.I.ζ A.I.ζ_prim A.I.ζ_pow f hf
  have hS : Differentiable ℂ (B.Sum 1 0 d.th w) := fun v =>
    ((hdiff.differentiableAt ((isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).mem_nhds
      (show T₂ < ((w, v) : ℂ × B.V).1.im from hw₂))).comp v
      ((differentiableAt_const w).prodMk differentiableAt_id) :)
  obtain ⟨Θ, hΘ, hΘ0, hΘp, hΘv⟩ := hth (𝓞 E) B H.w0 hprim d.th hmem w hS Q.g (h.trans F) Hm' hAH.1 hspan him'
  have hne : Θ ≠ 0 := by
    obtain ⟨v, hv⟩ := B.exists_Sum_ne_zero one_ne_zero 0 hth0 (w := w) fun z => (hsum w hw₂ _).of_norm
    exact fun e => hv ((hΘ0 v).1 (congrFun e _))
  have hfn : U.IsThetaFn Hm' χ 1 Θ := ⟨hΘ, fun l z => by
    obtain ⟨l, hl⟩ := l
    obtain ⟨a, rfl⟩ := hΛ' l hl
    rw [pow_one, hχ]
    exact hΘp a z⟩
  refine ⟨⟨Q, oa, hpr, H.rt0, H.sqrt_neg_disc_sq, hdet, I, inferInstance⟩, rfl, congrFun hI _, ?_⟩
  have key := isThetaPt_classical hL hL2 hT Q U Hm' χ Θ m (I.ev (m ^ 2)) (fun x => ⟨F (P (f _ x)), hΛ _⟩) hodd hAH hfn hne
    fun x => by rw [hev, Nat.cast_pow]; rfl
  refine Eq.mp (congrArg (IsThetaPt Q m (I.ev (m ^ 2))) (funext fun x => congrArg fnOf ?_)) key
  rw [hχ, _root_.mul_assoc]
  refine (congrArg (_ * ·) (hΘv _ m hodd.pos.ne')).trans ?_
  rw [← _root_.mul_assoc, AnArc.Sum, ← tsum_mul_left]
  exact (tsum_congr fun y => (hterm x y).symm).trans
    (d.eX.toEquiv.tsum_eq fun χ : A.N.X => (A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ)

theorem exists_full_of_small : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := fun hV _ _ _ _ _ hT =>
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  have hF : BrFamSt := _root_.GlobalTheory.Ex.brFam hL hL2
  of_steps hL hL2 hT
    (_root_.GlobalTheory.Ex.Arch.dict_of_val (_root_.GlobalTheory.ActValues.brAct hL) (_root_.GlobalTheory.Ex.Arch.AbVal.valSt hL hF (_root_.GlobalTheory.Ex.Arch.FibEx.fibEx hL hT) _root_.GlobalTheory.Ex.Arch.fibGrp (_root_.GlobalTheory.Ex.Arch.fibCubeSt hL) (_root_.GlobalTheory.Ex.Arch.FibSym.fibSymSt hL)
      (_root_.GlobalTheory.Ex.Arch.FibRos.fibRosSt hL) (_root_.GlobalTheory.Ex.Arch.FibPrim.fibPrim_of_laws hL) _root_.GlobalTheory.Ex.Arch.fibSec (_root_.GlobalTheory.Ex.Arch.fibLie_of_laws hL)))
    (_root_.GlobalTheory.Ex.Arch.towerSt_of _root_.GlobalTheory.Ex.GtValues.points_correspond (_root_.GlobalTheory.WeilValues.weil_eq_values _root_.GlobalTheory.Ex.GtValues.points_correspond hF) _root_.GlobalTheory.Ex.Arch.ptSt (_root_.GlobalTheory.Ex.Arch.qkSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt) _root_.GlobalTheory.Ex.Arch.Wp.wp_eq)
    _root_.GlobalTheory.Ex.Arch.typeSt (_root_.GlobalTheory.Ex.Arch.objSt_of_triple_reframe hL (_root_.GlobalTheory.Ex.Arch.tripleSt_of_laws hL hT) (_root_.GlobalTheory.Ex.Arch.reframe hT)) _root_.GlobalTheory.Ex.Arch.theta_sum_appellHumbert (_root_.GlobalTheory.Ex.Arch.txSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt)

end GlobalTheory.Ex.Arch
end
