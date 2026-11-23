import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieMultIffFinrank
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.UnifObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def negZeta (n : ℕ) : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / n)) (Complex.exp_ne_zero _)

theorem negZeta_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (negZeta n) n := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have := (Complex.isPrimitiveRoot_exp n hn.ne').inv
  rwa [← Complex.exp_neg, ← neg_div] at this

theorem negZeta_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : negZeta (n * m) ^ m = negZeta n := by
  have h₁ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h₂ : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, negZeta, negZeta, Units.val_mk0, Units.val_mk0, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem negZeta_zpow (n : ℕ) (j : ℤ) :
    ((negZeta n ^ j : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (j : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, negZeta, Units.val_mk0, ← Complex.exp_int_mul]
  congr 1
  ring

theorem exists_tateIso (D D' : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P' : D'.La →+ (Fin g → ℂ))
    {Q : Type} [Group Q] (act : 𝓞 E → Q → Q) (w : ℕ → Q → Q → ℂˣ → Prop) (e : (Fin g → ℂ) → Q)
    (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (hlin : ∀ (a : 𝓞 E) x i, P' (a • x) i = ty i (a : E) * P' x i)
    (hinj : Function.Injective P') (hadd : ∀ z z', e (z + z') = e z * e z') (hsur : Function.Surjective e)
    (hker : ∀ z, e z = 1 ↔ z ∈ P'.range) (hact : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = act a (e z))
    (hw : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      w k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) c)
    (htow : ∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e)
    (hbij : ∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e)
    (hiso : ∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') :
    ∃ I : TateIso D ℂ Q act w, ∀ n a, I.ev n a = e ((n : ℂ)⁻¹ • P' (f n a)) := by
  have e0 : e 0 = 1 := (hker 0).2 (zero_mem _)
  have epow : ∀ (m : ℕ) z, e z ^ m = e ((m : ℂ) • z) := fun m z => by
    induction m with
    | zero => simp [e0]
    | succ m ih => rw [pow_succ, ih, ← hadd, Nat.cast_succ, add_smul, one_smul]
  have eP : ∀ a, e (P' a) = 1 := fun a => (hker _).2 ⟨a, rfl⟩
  have div : ∀ n : ℕ, 0 < n → ∀ a, (n : ℂ)⁻¹ • P' (n • a) = P' a := fun n hn a => by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
  have md : ∀ n : ℕ, 0 < n → ∀ a c, e ((n : ℂ)⁻¹ • P' (a + n • c)) = e ((n : ℂ)⁻¹ • P' a) := fun n hn a c => by
    rw [map_add, smul_add, hadd, div n hn, eP, _root_.mul_one]
  refine ⟨{ ζ := negZeta
            ζ_prim := fun n hn => negZeta_prim hn
            ζ_pow := fun n m hn hm => negZeta_pow hn hm
            ev := fun n a => e ((n : ℂ)⁻¹ • P' (f n a))
            add := fun n a b => by rw [map_add, map_add, smul_add, hadd]
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => hw n _ _ _ hn ?_ }, fun _ _ => rfl⟩
  · rw [← hact, map_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, hlin, smul_eq_mul, smul_eq_mul, mul_left_comm]
  · rw [← (hbij n hn).1, hker]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, hinj ?_⟩
      rw [map_nsmul, hc, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, div n hn]⟩
  · constructor
    · intro hx
      obtain ⟨z, rfl⟩ := hsur x
      rw [epow, hker] at hx
      obtain ⟨a', ha'⟩ := hx
      obtain ⟨a, c, rfl⟩ := (hbij n hn).2 a'
      exact ⟨a, by rw [← md n hn _ c, ha', inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]⟩
    · rintro ⟨a, rfl⟩
      rw [epow, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne'), eP]
  · obtain ⟨c, hc⟩ := htow n m hn hm a
    have h₂ : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [epow, smul_smul, ← md n hn _ c, ← hc, Nat.cast_mul, mul_inv, mul_left_comm, mul_inv_cancel₀ h₂,
      _root_.mul_one]
  · rw [← negZeta_zpow]
    congr 1
    obtain ⟨j, hj⟩ := hiso n hn a b
    rw [sub_eq_iff_eq_add.1 hj, zpow_add, zpow_mul, zpow_natCast, (negZeta_prim hn).pow_eq_one, one_zpow,
      _root_.one_mul]

def tateExtend {D : Datum H} {k K : Type} [Field k] [Field K] (φ : k →+* K) {Q Q' : Type} [Group Q] [Group Q']
    {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'} {w : ℕ → Q → Q → kˣ → Prop} {w' : ℕ → Q' → Q' → Kˣ → Prop}
    (I : TateIso D k Q act w) (j : Q →* Q') (hj : Function.Injective j)
    (htor : ∀ n : ℕ, 0 < n → ∀ y, y ^ n = 1 → ∃ x, j x = y) (hact : ∀ a x, j (act a x) = act' a (j x))
    (hw : ∀ n x y c, w n x y c → w' n (j x) (j y) (Units.map φ.toMonoidHom c)) : TateIso D K Q' act' w' where
  ζ n := Units.map φ.toMonoidHom (I.ζ n)
  ζ_prim n hn := (I.ζ_prim n hn).map_of_injective (Units.map_injective φ.injective)
  ζ_pow n m hn hm := by rw [← map_pow, I.ζ_pow n m hn hm]
  ev n a := j (I.ev n a)
  add n a b := by rw [I.add, map_mul]
  lin n c a := by rw [I.lin, hact]
  ker n hn a := by rw [← I.ker n hn, map_eq_one_iff j hj]
  onto n hn y := by
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := htor n hn y hy
      rw [← map_pow, map_eq_one_iff j hj] at hy
      obtain ⟨a, rfl⟩ := (I.onto n hn x).1 hy
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]
  tower n m hn hm a := by rw [← map_pow, I.tower n m hn hm]
  isom n hn a b := by
    rw [← map_zpow]
    exact hw _ _ _ _ (I.isom n hn a b)

theorem unitOn_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (c : Aˣ) :
    Units.map (spMap φ).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map φ.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom (c : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem exists_smul_eq {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {I J : Ideal O} {n : ℕ}
    (h : I * J = Ideal.span {(n : O)}) {c : O} (hc : c ∈ I) {a : M} (ha : a ∈ J • (⊤ : Submodule O M)) :
    ∃ b : M, c • a = n • b := by
  have := Submodule.smul_mem_smul hc ha
  rw [← Submodule.mul_smul, h, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at this
  obtain ⟨b, -, hb⟩ := this
  exact ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩

theorem exists_obj (hL : Out.Laws) {D : Datum H} {l : Level H} (hA : l.A = 1) {B k : Type} [CommRing B] [Field k]
    [IsAlgClosed k] [CharZero k] (b : Base l B) (σ : B →+* k) (t : SAB H (Sp k)) {g : ℕ} (hp : IsProper t.G.hom)
    (hg : SmoothOfRelativeDimension g t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (hdet : DetCond D t.act (𝟙 (Sp k)) (σ b.ρ))
    (I : TateIso D k (𝟙_ (Over (Sp k)) ⟶ t.G) (fun a x => x ≫ t.act.act a)
      (fun n x y c => Out.WeilIs t.G t.PP.L n x y (unitOn c))) :
    ∃ (o : Obj D l b (spMap σ)) (m : SABMap t o.t (𝟙 _)),
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        (I.ev l.M a).left ≫ m.φ = (o.eta a).left := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨u, hu, π, hπ, huπ⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hη : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      I.ev l.M (π • a) = I.ev l.M a := fun a h => by
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huπ, add_smul, I.add,
      (I.ker _ hM _).2 (exists_smul_eq l.prod hu h), _root_.one_mul]
  have := t.semi.smooth
  refine ⟨{ t := t
            proper := hp
            ample := ha
            ktriv := hk
            eta := fun a => I.ev l.M (π • a)
            eta_add := fun a c => by rw [smul_add, I.add]
            eta_ker := fun a h => (I.ker _ hM _).2 (exists_smul_eq ((mul_comm _ _).trans l.prod) hπ h)
            etaA := fun _ => 1
            etaA_add := fun _ _ => (_root_.mul_one _).symm
            etaA_ker := fun _ => rfl
            geom := fun K _ _ x β hx => ?_ }, LevelTwist.sabMapId t, fun a h => ?_⟩
  · obtain ⟨φ, rfl⟩ : ∃ φ : k →+* K, x = spMap φ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
    obtain rfl : φ.comp σ = β :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
    have : CharZero K := charZero_of_injective_ringHom φ.injective
    let J : TateIso D K (Over.mk (spMap φ) ⟶ t.G) (fun a x => x ≫ t.act.act a)
        (fun n x y c => Out.WeilIs t.G t.PP.L n x y (unitOn c)) :=
      tateExtend φ I (MonoidHom.mk' (fun z => toUnit (Over.mk (spMap φ)) ≫ z) fun _ _ => MonObj.comp_mul _ _ _)
        (HeckePoint.toUnit_comp_injective _ _)
        (fun n hn y hy => HeckePoint.exists_of_torsion hL.mulN (HeckePoint.polOf t hp ha hk hg) _
          (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 hn.ne') y hy)
        (fun a z => (Category.assoc (toUnit _) z _).symm) (fun n y z c h => by
          have := CommPairing.weilIs_pull hL.globalFns (HeckePoint.isAbelianScheme_of_proper t hp) t.PP.isLB
            (toUnit (Over.mk (spMap φ))) h
          rw [Over.toUnit_left] at this
          rw [← unitOn_map]
          exact this)
    refine ⟨LieExt.detCond_extend D φ t.G t.act hdet, J, ?_, fun a => ?_, fun a h => ?_⟩
    · have h₁ := J.ζ_prim _ l.A_pos
      have h₂ := b.ζ_prim
      rw [hA, IsPrimitiveRoot.one_right_iff] at h₁ h₂
      rw [hA, h₁, h₂, map_one, Units.val_one]
    · rw [hA, MonObj.comp_one]
      exact ((J.ker 1 one_pos a).2 ⟨a, (one_smul _ _).symm⟩).symm
    · exact congrArg (toUnit (Over.mk (spMap φ)) ≫ ·) (hη a h)
  · exact (Category.comp_id _).trans (congrArg (fun q => q.left) (hη a h).symm)

theorem exists_obj_of_uniformised : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (l : Level H) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), l.A = 1 → σ (baseKA l).ρ = H.rt0 → D'.p = D.p → D'.q = D.q → IsPeriod D' ty P' → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D' t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) (unitOn c)) → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') → ∃ (o : Obj D l (baseKA l) (spMap σ)) (m : SABMap t o.t (𝟙 _)), ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), (e ((l.M : ℂ)⁻¹ • P' (f l.M a))).left ≫ m.φ = (o.eta a).left := by
  intro hL E _ _ _ H D D' l σ g ty P' t e f hA hσ hp hq hP ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, _, hw⟩ ⟨htow, hbij⟩ hiso
  have hd : DetCond D t.act (𝟙 (Sp ℂ)) (σ (baseKA l).ρ) := fun τ => by
    rw [hσ, ← hp, ← hq]
    exact h₅ τ
  obtain ⟨I, hI⟩ := exists_tateIso D D' ty P' (fun a x => x ≫ t.act.act a)
    (fun n x y c => Out.WeilIs t.G t.PP.L n x y (unitOn c)) e f hP.1 hP.2.1 h₆ h₇ h₈ h₉ (fun k a b c hk hc => by have := hw k a b c hk hc; beta_reduce; exact this) htow hbij hiso
  obtain ⟨o, m, h⟩ := exists_obj hL hA (baseKA l) σ t h₁ h₂ h₃ h₄ hd I
  refine ⟨o, m, fun a ha => ?_⟩
  exact (congrArg (fun q => q.left ≫ m.φ) (hI l.M a).symm).trans (h a ha)

end GlobalTheory.UnifObj
