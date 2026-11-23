import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticTorusPointBaseEqHolUnifEx
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcLiftExtensionLargerClosedField

noncomputable section

namespace GlobalTheory.ArcOfModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TorusExt ArcExt
open scoped CategoryTheory.Obj

theorem weilQkIs_qkExt (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] {D : DegPre R} (he : D.PsiEven) (hB : D.TauBimult) {F F' : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (k : ℕ) (hk : 1 ≤ k)
    (p p' : QkPt D F k) (z : F) (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F' k (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  have hGt := Ex.GtValues.points_correspond
  have hWp := WeilValues.weil_eq_values hGt (Ex.brFam hL hL₂)
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D he hB F ⊤ fun _ => trivial
  obtain ⟨J', hg, hJ₀⟩ := exists_gauge f D.P.isLB ν.good
  obtain ⟨N', ν', e₁, hth⟩ := GaugeValues.exists_numOf hL R D he hB F' J' hg ν.th ν.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = ν.J ψ := e₁ ▸ hJ₀
  have G := (hGt R D he hB F N ν).2.2.2.2
  have G' := (hGt R D he hB F' N' ν').2.2.2.2
  obtain ⟨q, hq, -⟩ := (G k).1 p
  obtain ⟨q', hq', -⟩ := (G k).1 p'
  obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt hB f hf p)
  obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt hB f hf p')
  have a := numHom_qPt f hf hB ν ν' hJ hth hq hr
  have a' := numHom_qPt f hf hB ν ν' hJ hth hq' hr'
  rw [hWp R D he hB F' N' ν' k hk _ _ _ _ _ hr hr',
    (Ex.NumD.hom_transport F F' f N N' (numHom f hf ν ν' hJ hth)).2.2.2.1 k q q' r r' a.1 a.2 a'.1 a'.2,
    (hWp R D he hB F N ν k hk _ _ _ _ _ hq hq').1 h]
  rfl

def root (n : ℕ) (x : ℤ) : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / n)) (Complex.exp_ne_zero _)

theorem root_congr {n : ℕ} (hn : 0 < n) {x y : ℤ} (h : (n : ℤ) ∣ x - y) : root n x = root n y := by
  obtain ⟨c, hc⟩ := h
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  refine Units.ext (Complex.exp_eq_exp_iff_exists_int.2 ⟨-c, ?_⟩)
  rw [sub_eq_iff_eq_add.1 hc]
  push_cast
  field_simp
  ring

theorem root_zpow (n : ℕ) (x y : ℤ) : root n x ^ y = root n (x * y) := Units.ext (by
  rw [Units.val_zpow_eq_zpow_val, root, root, Units.val_mk0, Units.val_mk0, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring)

theorem root_pow {n m : ℕ} (hm : 0 < m) (x : ℤ) : root (n * m) x ^ m = root n x := Units.ext (by
  have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  rw [Units.val_pow_eq_pow_val, root, root, Units.val_mk0, Units.val_mk0, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [← div_div, mul_div_assoc', mul_div_cancel_left₀ _ this])

theorem isPrimitiveRoot_root {n : ℕ} (hn : 0 < n) {x y : ℤ} (h : (n : ℤ) ∣ 1 - x * y) :
    IsPrimitiveRoot (root n x) n := by
  have h₁ : IsPrimitiveRoot (root n (-1)) n := IsPrimitiveRoot.coe_units_iff.1 (by
    convert Complex.isPrimitiveRoot_exp n hn.ne' using 1
    simp [root])
  obtain ⟨c, hc⟩ := h
  have := h₁.zpow_of_gcd_eq_one (-x) (Int.isCoprime_iff_gcd_eq_one.1 ⟨-y, c, by linear_combination -hc⟩)
  rwa [root_zpow, neg_mul_neg, _root_.one_mul] at this

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

section Torsion

variable {O : Type} [CommRing O] [StarRing O] {D₀ : DegPre ℂ} [Module O D₀.X] {oa : D₀.OAct O} (d : GtDict D₀ oa)

theorem qkAdd_qk (k : ℕ) [NeZero k] (a b : d.A.La) : QkAdd (d.qk k a) (d.qk k b) (d.qk k (a + b)) :=
  ⟨_, map_add d.eX _ _, by rw [d.qk_g, d.qk_g, d.qk_g, map_add, smul_add]; exact d.add _ _,
    qk_equiv_refl (AnPairing.tauBimult d) _⟩

theorem qkAct_qk (k : ℕ) [NeZero k] (x : O) (a : d.A.La) : QkAct oa x (d.qk k a) (d.qk k (x • a)) :=
  ⟨_, map_smul d.eX _ _, by rw [d.qk_g, d.qk_g, d.A.degeneratingTori_basePeriodMap_smul, ← map_smul (d.A.actV x)]; exact d.lin _ _,
    qk_equiv_refl (AnPairing.tauBimult d) _⟩

theorem isNsmul_qk (n m : ℕ) [NeZero n] [NeZero m] (a : d.A.La) :
    GtPtF.IsNsmul m (d.qk (n * m) a).g (d.qk n a).g := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have := d.isNsmul_ex₀ m (((n * m : ℕ) : ℂ)⁻¹ • d.A.P0 a)
  rwa [← Nat.cast_smul_eq_nsmul ℂ m, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm, mul_inv_cancel₀ hm,
    _root_.mul_one, ← mul_inv, ← Nat.cast_mul] at this

def evPt : ∀ n : ℕ, d.A.La → QkPt D₀ ℂ n
  | 0, _ => qkZero (AnPairing.tauBimult d) ℂ 0
  | n + 1, a => d.qk (n + 1) a

theorem evPt_eq (n : ℕ) [NeZero n] (a : d.A.La) : evPt d n a = d.qk n a := by
  cases n with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ n => rfl

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem exists_EF_eq_one (A : AnArc O) [Nontrivial A.X] : ∃ a b : A.La, A.EF a b = 1 := by
  let e := Module.Free.chooseBasis ℤ A.X
  obtain ⟨i⟩ := e.index_nonempty
  exact ⟨.mk (e i) 0 0, .mk 0 (e.coord i).toAddMonoidHom 0, by simp [AnArc.EF_apply]⟩

theorem algebraMap_comp : (algebraMap ℂ (FractionRing ℂ)).comp (algebraMap (FractionRing ℂ) ℂ) =
    algebraMap (FractionRing ℂ) (FractionRing ℂ) :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℂ) (RingHom.ext fun x =>
    congrArg (algebraMap ℂ (FractionRing ℂ)) (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm)

def fracPt (k : ℕ) [NeZero k] (a : d.A.La) : QkPt D₀ (FractionRing ℂ) k :=
  qkExt (AnPairing.tauBimult d) (algebraMap ℂ (FractionRing ℂ)) algebraMap_comp (d.qk k a)

theorem qkExt_of_fracPt (k : ℕ) [NeZero k] (a : d.A.La) {F : Type} [Field F] [Algebra (FractionRing ℂ) F]
    {q : QkPt D₀ F k} (h : QkExt (algebraMap _ F) (fracPt d k a) q) :
    QkExt ((algebraMap (FractionRing ℂ) F).comp (algebraMap ℂ _)) (d.qk k a) q :=
  LiftExt.qkExt_trans ((qkExt_iff _ _ _ _ _).2 rfl) h

theorem qkExt_fracPt (k : ℕ) [NeZero k] (a : d.A.La) : QkExt (algebraMap _ ℂ) (fracPt d k a) (d.qk k a) := by
  have hB := AnPairing.tauBimult d
  obtain ⟨q, hq, -⟩ := existsUnique_qkExt hB (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) (fracPt d k a)
  have h₁ := qkExt_of_fracPt d k a hq
  rw [← IsScalarTower.algebraMap_eq] at h₁
  have e : spMap (algebraMap ℂ ℂ) = 𝟙 _ := Spec.map_id _
  have h₂ : QkExt (algebraMap ℂ ℂ) (d.qk k a) (d.qk k a) :=
    ⟨rfl, by rw [e, Category.id_comp], fun χ => corr_of_val D₀.P.isLB fun y J hJ => by
      rw [val_pull hJ, e, Category.id_comp]; rfl⟩
  rwa [(existsUnique_qkExt hB (algebraMap ℂ ℂ) (RingHom.id_comp _) _).unique h₂ h₁]

end Torsion

section Tate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {D₀ : DegPre ℂ}
  [Module (𝓞 E) D₀.X] {oa : letI := H.starRing; D₀.OAct (𝓞 E)} (d : letI := H.starRing; GtDict D₀ oa)

theorem exists_tateIsoQ : letI := H.starRing
    ∀ (_ : Nontrivial d.A.X) (f : ℕ → D.La →ₗ[𝓞 E] d.A.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) →
      (∀ n : ℕ, 0 < n → ∀ a, (∃ e, f n a = n • e) → ∃ e, a = n • e) →
      (∀ n : ℕ, 0 < n → ∀ a', ∃ a e, a' = f n a + n • e) →
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ d.A.EF (f n a) (f n a') - ν n * D.EF a a') →
      ∃ I : TateIsoQ D D₀ oa ℂ, (∀ n, I.ζ n = root n (ν n)) ∧ ∀ n a, I.ev n a = evPt d n (f n a) := by
  let _ := H.starRing
  intro _ f ν tow inj sur mul
  have hB := AnPairing.tauBimult d
  obtain ⟨x, y, hxy⟩ := exists_EF_eq_one d.A
  have cong : ∀ (n : ℕ) (a b e e' : d.A.La), (n : ℤ) ∣ d.A.EF (a + n • e) (b + n • e') - d.A.EF a b := fun n a b e e' =>
    ⟨d.A.EF e b + d.A.EF a e' + n * d.A.EF e e', by
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]; ring⟩
  have unit : ∀ n : ℕ, 0 < n → ∃ a b, (n : ℤ) ∣ 1 - d.A.EF (f n a) (f n b) := fun n hn => by
    obtain ⟨a, e, ha⟩ := sur n hn x
    obtain ⟨b, e', hb⟩ := sur n hn y
    exact ⟨a, b, by rw [← hxy, ha, hb]; exact cong _ _ _ _ _⟩
  refine ⟨{ ζ := fun n => root n (ν n), ζ_prim := fun n hn => ?_, ζ_pow := fun n m hn hm => ?_,
            ev := fun n a => evPt d n (f n a), add := fun n hn a b => ?_, lin := fun n hn x a => ?_,
            ker := fun n hn a b => ?_, onto := fun n hn p => ?_, tower := fun n m hn hm a => ?_,
            isom := fun n hn a b => ?_ }, fun _ => rfl, fun _ _ => rfl⟩
  · obtain ⟨a, b, h⟩ := unit n hn
    exact isPrimitiveRoot_root hn (y := D.EF a b) (by simpa using h.add (mul n hn a b))
  · rw [root_pow hm]
    obtain ⟨a, b, h⟩ := unit _ (Nat.mul_pos hn hm)
    have hd : (n : ℤ) ∣ ((n * m : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (dvd_mul_right n m)
    have h₁ := hd.trans (h.add (mul _ (Nat.mul_pos hn hm) a b))
    obtain ⟨e, he⟩ := tow n m hn hm a
    obtain ⟨e', he'⟩ := tow n m hn hm b
    have h₃ : (n : ℤ) ∣ d.A.EF (f (n * m) a) (f (n * m) b) - d.A.EF (f n a) (f n b) := by
      rw [he, he']; exact cong _ _ _ _ _
    obtain ⟨x₁, h₁⟩ := h₁
    obtain ⟨x₂, h₂⟩ := ((hd.trans h).add h₃).add (mul n hn a b)
    exact root_congr hn ⟨ν (n * m) * x₂ - ν n * x₁, by linear_combination ν (n * m) * h₂ - ν n * h₁⟩
  all_goals have : NeZero n := ⟨hn.ne'⟩
  · simp only [evPt_eq, map_add]
    exact qkAdd_qk d n _ _
  · simp only [evPt_eq, map_smul]
    exact qkAct_qk d n _ _
  · simp only [evPt_eq, d.qk_equiv_iff]
    refine ⟨fun ⟨e, he⟩ => ?_, fun ⟨e, he⟩ => ⟨-f n e, by simp [he]⟩⟩
    obtain ⟨e', he'⟩ := inj n hn (a - b) ⟨-e, by simp [he]⟩
    exact ⟨e', by rw [← he', add_sub_cancel]⟩
  · obtain ⟨a', rfl⟩ := d.qk_surjective n p
    obtain ⟨a, e, h⟩ := sur n hn a'
    exact ⟨a, by rw [evPt_eq, d.qk_equiv_iff]; exact ⟨e, h⟩⟩
  · have : NeZero m := ⟨hm.ne'⟩
    obtain ⟨e, he⟩ := tow n m hn hm a
    simp only [evPt_eq]
    exact ⟨d.qk n (f (n * m) a), rfl, isNsmul_qk d n m _, (d.qk_equiv_iff _ _ _).2 ⟨-e, by simp [he]⟩⟩
  · simp only [evPt_eq]
    rw [root_zpow, ← root_congr hn (mul n hn a b)]
    exact d.weilQkIs_qk n _ _

theorem exists_tateIsoQ_ext (hL : Laws) (hL₂ : Laws2) (he : D₀.PsiEven) (I : TateIsoQ D D₀ oa ℂ) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing ℂ) F] : letI := H.starRing
    ∃ I' : TateIsoQ D D₀ oa F,
      (∀ n, (I'.ζ n : F) = algebraMap (FractionRing ℂ) F (algebraMap ℂ _ (I.ζ n : ℂ))) ∧
      ∀ (k : ℕ) [NeZero k] (v : D.La) (a : d.A.La), QkPt.Equiv D₀ ℂ (d.qk k a) (I.ev k v) →
        ∀ q, QkExt (algebraMap _ F) (fracPt d k a) q → QkPt.Equiv D₀ F q (I'.ev k v) := by
  let _ := H.starRing
  have hB := AnPairing.tauBimult d
  have hf : ((algebraMap (FractionRing ℂ) F).comp (algebraMap ℂ _)).comp (algebraMap (FractionRing ℂ) ℂ) =
      algebraMap (FractionRing ℂ) F := by
    rw [RingHom.comp_assoc, algebraMap_comp]; rfl
  refine ⟨tateExt _ hf hB hL I (weilQkIs_qkExt hL hL₂ he hB _ hf), fun _ => rfl, fun k _ v a h q hq => ?_⟩
  rw [(qkExt_iff hB _ hf _ _).1 (qkExt_of_fracPt d k a hq)]
  exact qkExt_congr hB _ hf h

end Tate

theorem exists_arcIn (hL : Laws) (hL₂ : Laws2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) (l : Geo.Tor.Level H) {c : Coeff l} {O : Type} [CommRing O] (β : O →+* c.F) (b : O →+* ℂ)
    (P : PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))) (rig_gen : rig.IsGen)
    (cub : CubicalStr P.A ⟨P.L, rig, P.isLB, rig_gen⟩)
    (sym : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(ι[P.A]).left, 𝟙 P.A.left] ![1, -1])) (sym_gen : sym.IsGen)
    (sym_rig : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ sym (eSec P.A)) (LB.oneGen P.L)) :
    letI := H.starRing
    ∀ (oa : P.OAct (𝓞 E)),
      (∃ w : LB.Gen (LB.LinComb P.L (K := Fin 4)
          ![(padd P.A (𝟙 _) (oa.act H.w0)).left, 𝟙 P.A.left, (oa.act H.w0).left, (toUnit P.A ≫ η[P.A]).left]
          ![1, -2, -1, 2]),
        w.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ w (eSec P.A)) (LB.oneGen P.L)) →
    ∀ (A : AnArc (𝓞 E)) (u : HolUnif P.A P.L A.gB) (lam : u.Λ = A.abelian₂),
      u.IsAH A.Hm (fun m => A.chi ⟨m, lam.le m.2⟩) → u.IsRig rig →
      (∀ j : ℕ, 1 ≤ j → ∀ θ, u.IsThetaFn A.Hm (fun m => A.chi ⟨m, lam.le m.2⟩) j θ → ∃ s, u.IsFnPow j s θ) →
      (∀ (x : 𝓞 E) z, u.ex (A.F x z) = u.ex z ≫ oa.act x) →
      (∀ y, (A.psi y : ℂ) = eTwoPi (A.T y (H.w0 • y))) → Nontrivial A.X → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') →
    ∀ (D' : Datum H) (gam : D'.La ≃ₗ[𝓞 E] A.La), (∀ v v', A.EF (gam v) (gam v') = D'.EF v v') →
    ∀ (t : D.La → D'.La) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ v, ∃ e, f (n * m) v = f n v + n • e) →
      (∀ n : ℕ, 0 < n → ∀ v, (∃ e, f n v = n • e) → ∃ e, v = n • e) →
      (∀ n : ℕ, 0 < n → ∀ v', ∃ v e, v' = f n v + n • e) →
      (∀ n : ℕ, 0 < n → ∀ v v', (n : ℤ) ∣ D'.EF (f n v) (f n v') - ν n * D.EF v v') →
      (∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M v = t v + l.M • e) →
      (∀ v, ∃ e, f l.A v = t v + l.A • e) →
      (∀ z : O, ((β z : c.F) : ℂ) = zeta l.A → b z = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A)) →
      (∀ r : O, ((β r : c.F) : ℂ) = H.rt0 → ∀ τ : 𝓞 E →+* ℂ, ∃ n, LieMult (ofRingAct oa.toRingAct) (𝟙 (Sp ℂ)) τ n ∧
        n + Module.finrank (𝓞 E) A.X = if τ H.rt = b r then D.p else D.q) →
    ∃ (a : ArcIn D l β ℂ b) (Λ : GtAn a) (hA : Λ.A = A),
      a.D₀.P = P ∧ HEq a.D₀.rig rig ∧ HEq a.D₀.cub cub ∧ HEq a.D₀.sym sym ∧ HEq a.oa.onB oa ∧ HEq Λ.u u ∧
      (∀ v, QkExt (algebraMap _ ℂ) (a.eta v) (Λ.toGtDict.qk l.M (cast (congrArg AnArc.La hA.symm) (gam (t v))))) ∧
      ∀ v, QkExt (algebraMap _ ℂ) (a.etaA v) (Λ.toGtDict.qk l.A (cast (congrArg AnArc.La hA.symm) (gam (t v)))) := by
  let _ := H.starRing
  intro oa ⟨w, hw, hw₀⟩ A u lam ah hrig hθ hact hT hX hbe D' gam hgam t f ν tow inj sur mul levM levA hζ hLie
  let D₀ := degPre A P rig rig_gen cub sym sym_gen sym_rig u
  let d := dict A P rig rig_gen cub sym sym_gen sym_rig u lam ah hrig oa hact
  have hψ := degPre_psi A P rig rig_gen cub sym sym_gen sym_rig u
  have he : D₀.PsiEven := psiEven (D := D₀) (ε := LinearEquiv.refl _ A.X) lam ah (fun _ => rfl) hψ
  obtain ⟨I, hIζ, hI⟩ := exists_tateIsoQ (D := D) d hX (fun n => gam.toLinearMap ∘ₗ f n) ν
    (fun n m hn hm v => (tow n m hn hm v).elim fun e h =>
      ⟨gam e, (congrArg gam h).trans (by rw [map_add, map_nsmul]; rfl)⟩)
    (fun n hn v ⟨e, h⟩ => inj n hn v ⟨gam.symm e, gam.injective (h.trans
      ((map_nsmul gam _ _).trans (congrArg (n • ·) (gam.apply_symm_apply e))).symm)⟩)
    (fun n hn v' => by
      obtain ⟨v, e, h⟩ := sur n hn (gam.symm v')
      exact ⟨v, gam e, (gam.apply_symm_apply v').symm.trans ((congrArg gam h).trans (by rw [map_add, map_nsmul]; rfl))⟩)
    (fun n hn v v' => hgam _ _ ▸ mul n hn v v')
  have lev : ∀ (k : ℕ) [NeZero k] (v : D.La), (∃ e, f k v = t v + k • e) →
      QkPt.Equiv D₀ ℂ (d.qk k (gam (t v))) (I.ev k v) := fun k _ v ⟨e, h⟩ => by
    rw [hI, evPt_eq]
    exact (d.qk_equiv_iff _ _ _).2 ⟨gam e, (congrArg gam h).trans (by rw [map_add, map_nsmul]; rfl)⟩
  let a : ArcIn D l β ℂ b :=
    { D₀ := D₀
      oa := oAct A P rig rig_gen cub sym sym_gen sym_rig u lam ah hrig oa hact
      nontriv := hX
      even := he
      bimult := AnPairing.tauBimult d
      gen := psiUnitOn (D := D₀) (ε := LinearEquiv.refl _ A.X) (fun _ => rfl) hψ
      w0 := psi_weight_zero_linear_combination (D := D₀) (ε := LinearEquiv.refl _ A.X) lam ah hrig (fun _ => rfl) hψ _
        (show H.w0 + H.bar H.w0 = 1 by rw [HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]) (hact _) hT w hw hw₀
      be := A.be
      be_symm := A.be_symm
      be_pos := A.be_pos
      be_adj := A.be_adj
      be_dvd := hbe
      eta := fun v => fracPt d l.M (gam (t v))
      etaA := fun v => fracPt d l.A (gam (t v))
      geom := fun F _ _ _ r z hr hz g hg => by
        obtain ⟨I', hζ', hI'⟩ := exists_tateIsoQ_ext d hL hL₂ he I F
        refine ⟨fun σ => ?_, I', ?_, fun v => hI' _ v _ (lev _ v (levA v)), fun v hv => hI' _ v _ (lev _ v (levM v hv))⟩
        · obtain ⟨τ, rfl⟩ := DetExtend.exists_factor g σ
          obtain ⟨n, h₁, h₂⟩ := hLie r hr τ
          have := P.isAb.smooth
          refine ⟨n, ?_, h₂.trans ?_⟩
          · have := (DetExtend.lieMult_extend g _ _ τ n).2 h₁
            rwa [Category.comp_id] at this
          · simp only [RingHom.comp_apply, g.injective.eq_iff]
        · rw [hζ', hIζ, hζ z hz, hg]; rfl }
  obtain ⟨σ⟩ := nonempty_secFn d hθ
  exact ⟨a, ⟨⟨d, fun _ _ => rfl⟩, σ⟩, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    fun v => qkExt_fracPt d _ _, fun v => qkExt_fracPt d _ _⟩

section Toric

open HostModel ToricData ToricDict Out.Inh Out.InhTate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Geo.Tor.Level H)

def traceArc : letI := H.starRing; AnArc (𝓞 E) :=
  letI := H.starRing
  AnArc.ofForm (𝓞 E) (𝓞 E) (arcForm l) (fun y z => congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z))
    (fun _ hy => mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy))
    (fun a y z => congrArg ((2 * l.M' : ℤ) * ·) (trForm_adj H a y z)) fun y => ⟨l.M' * trForm H y y, mul_assoc _ _ _⟩

def traceIso : letI := H.starRing; (hypDatum H).La ≃ₗ[𝓞 E] (traceArc l).La :=
  letI := H.starRing
  { toFun v := .mk v.1 (ConjDual.toDual H (-v.2)).toAddMonoidHom 0
    invFun w := (w.y, -(ConjDual.toDual H).symm (AddMonoidHom.toIntLinearMap w.n))
    map_add' _ _ := AnArc.La.ext rfl (AddMonoidHom.ext fun _ => neg_add _ _) (add_zero _).symm
    map_smul' _ _ := AnArc.La.ext rfl (AddMonoidHom.ext fun _ => rfl) (Subtype.ext (Subsingleton.elim (α := Fin 0 → ℂ) _ _))
    left_inv _ := Prod.ext rfl (neg_neg _)
    right_inv _ := AnArc.La.ext rfl (AddMonoidHom.ext fun _ => neg_neg _)
      (Subtype.ext (Subsingleton.elim (α := Fin 0 → ℂ) _ _)) }

end Toric

end GlobalTheory.ArcOfModel
