import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingProperties
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

open GlobalTheory.Ex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_nsmul_of_dvd (D : Datum H) {n : ℕ} (hn : 0 < n) {b : D.La} (h : ∀ a, (n : ℤ) ∣ D.EF b a) :
    ∃ e, b = n • e := by
  choose f hf using h
  have hn' : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hn.ne'
  let g : D.La →ₗ[ℤ] ℤ :=
    { toFun := f
      map_add' := fun a a' => mul_left_cancel₀ hn' (by rw [mul_add, ← hf, ← hf, ← hf, map_add])
      map_smul' := fun c a => mul_left_cancel₀ hn' (by
        rw [← hf, map_smul, hf, smul_eq_mul, RingHom.id_apply, smul_eq_mul, mul_left_comm]) }
  obtain ⟨e, he⟩ := D.unimod.2 g
  refine ⟨e, D.unimod.1 (LinearMap.ext fun a => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, he, nsmul_eq_mul]
  exact hf a

theorem exists_linear_lift {R M X : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup X] [Module R X] (n : ℕ) (Y : M → X) (hadd : ∀ a b, ∃ e, Y (a + b) = Y a + Y b + n • e)
    (hsmul : ∀ (c : R) a, ∃ e, Y (c • a) = c • Y a + n • e) : ∃ y : M →ₗ[R] X, ∀ a, ∃ e, y a = Y a + n • e := by
  let S : Submodule R X := LinearMap.range (n • LinearMap.id : X →ₗ[R] X)
  have mem : ∀ x : X, x ∈ S ↔ ∃ e, n • e = x := fun x => Iff.rfl
  have h0 : ∀ e : X, S.mkQ (n • e) = 0 := fun e => (Submodule.Quotient.mk_eq_zero S).2 ((mem _).2 ⟨e, rfl⟩)
  let g : M →ₗ[R] X ⧸ S :=
    { toFun := fun a => S.mkQ (Y a)
      map_add' := fun a b => by
        obtain ⟨e, he⟩ := hadd a b
        rw [he, map_add, h0, add_zero, map_add]
      map_smul' := fun c a => by
        obtain ⟨e, he⟩ := hsmul c a
        rw [he, map_add, h0, add_zero, map_smul, RingHom.id_apply] }
  obtain ⟨h, hh⟩ := Module.projective_lifting_property S.mkQ g (Submodule.mkQ_surjective S)
  refine ⟨h, fun a => ?_⟩
  have := congrArg (fun φ : M →ₗ[R] X ⧸ S => φ a) hh
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, g, LinearMap.coe_mk, AddHom.coe_mk] at this
  obtain ⟨e, he⟩ := (mem _).1 ((Submodule.Quotient.eq S).1 this)
  exact ⟨e, by rw [he, add_sub_cancel]⟩

theorem torus_pair (D : Datum H) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)) (hev : D₀.PsiEven)
    (hB : D₀.TauBimult) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F)
    (n : ℕ) (hn : 0 < n) (t t' : Multiplicative D₀.X →* Fˣ) (ht : t ^ n = 1) (ht' : t' ^ n = 1) :
    ∃ b b' : D.La, (∃ e, (I.ev n b).y = n • e) ∧
      (∀ a, I.ζ n ^ D.EF b a = t (Multiplicative.ofAdd (I.ev n a).y)) ∧
      (∀ a, I.ζ n ^ D.EF b' a = t' (Multiplicative.ofAdd (I.ev n a).y)) ∧ ((∃ e, b = b' + n • e) → t = t') := by
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D₀ hev hB F ⊤ fun _ => trivial
  have hGt := GtValues.points_correspond R D₀ hev hB F N ν
  have hWp := WeilValues.weil_eq_values GtValues.points_correspond (brFam hL hL₂) R D₀ hev hB F N ν n hn
  have G := hGt.2.2.2.2 n
  choose Q hQ using fun a => (G.1 (I.ev n a)).exists
  let tr : (Multiplicative D₀.X →* Fˣ) → (Multiplicative N.X →* Fˣ) := fun s =>
    s.comp (AddEquiv.toMultiplicative ν.eX).toMonoidHom
  have trn : ∀ s : Multiplicative D₀.X →* Fˣ, s ^ n = 1 → tr s ^ n = 1 := fun s hs => by
    refine MonoidHom.ext fun χ => ?_
    have := congrArg (fun g : Multiplicative D₀.X →* Fˣ => g ((AddEquiv.toMultiplicative ν.eX).toMonoidHom χ)) hs
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this ⊢
    exact this
  have one : ∀ (s : Multiplicative D₀.X →* Fˣ) (hs : s ^ n = 1), ∃ b, N.QEq (Q b) (N.qTor (tr s) (trn s hs)) ∧
      ∀ a, I.ζ n ^ D.EF b a = s (Multiplicative.ofAdd (I.ev n a).y) := by
    intro s hs
    obtain ⟨p₀, hp₀⟩ := G.2.1 (N.qTor (tr s) (trn s hs))
    obtain ⟨b, hb⟩ := I.onto n hn p₀
    have hq := (G.2.2 _ _ _ _ (hQ b) hp₀).1 hb
    refine ⟨b, hq, fun a => Units.ext ?_⟩
    have h1 := (hWp _ _ _ _ _ (hQ b) (hQ a)).1 (I.isom n hn b a)
    rw [h1, WpPairing.wp_congr_left N hq, NumD.wp_qTor, ← (hQ a).1]
    rfl
  obtain ⟨b, hq, hb⟩ := one t ht
  obtain ⟨b', hq', hb'⟩ := one t' ht'
  refine ⟨b, b', ?_, hb, hb', fun hbb => ?_⟩
  · obtain ⟨z, hz, -⟩ := hq
    refine ⟨ν.eX (-z), ?_⟩
    rw [← (hQ b).1, map_neg, smul_neg, ← map_nsmul, eq_neg_iff_add_eq_zero, ← map_add, ← hz]
    exact map_zero _
  · have h₁ := (G.2.2 _ _ _ _ (hQ b) (hQ b')).1 ((I.ker n hn b b').2 hbb)
    have h₂ := (N.qEq_equivalence n).trans ((N.qEq_equivalence n).trans ((N.qEq_equivalence n).symm hq) h₁) hq'
    obtain ⟨z, hz, hz'⟩ := h₂
    have hz0 : z = 0 := by
      have e : (n : ℤ) • z = 0 := by
        rw [natCast_zsmul]
        have : (0 : N.X) = 0 + n • z := hz
        rw [zero_add] at this
        exact this.symm
      exact (smul_eq_zero.1 e).resolve_left (Int.natCast_ne_zero.2 hn.ne')
    subst hz0
    have e : N.tor (tr t') = N.tor (tr t) := by
      have h := hz'
      rw [NumD.io_zero, _root_.mul_one] at h
      exact h
    have e' := NumD.tor_injective N e
    refine MonoidHom.ext fun χ => ?_
    have := congrArg (fun s : Multiplicative N.X →* Fˣ => s (Multiplicative.ofAdd (ν.eX.symm χ.toAdd))) e'
    simpa [tr] using this.symm

theorem exists_char {X F : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Field F] {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) (S : AddSubgroup X) (x : X) (hx : ∀ s ∈ S, ∀ e, s ≠ x + n • e) :
    ∃ t : Multiplicative X →* Fˣ, t ^ n = 1 ∧ (∀ s ∈ S, t (Multiplicative.ofAdd s) = 1) ∧ t (Multiplicative.ofAdd x) ≠ 1 := by
  let T : AddSubgroup X := S ⊔ (nsmulAddMonoidHom (α := X) n).range
  have hxT : (QuotientAddGroup.mk x : X ⧸ T) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    intro h
    obtain ⟨s, hs, z, ⟨w, rfl⟩, hsz⟩ := AddSubgroup.mem_sup.1 h
    exact hx s hs (-w) (by rw [← hsz, nsmulAddMonoidHom_apply, smul_neg, add_neg_cancel_right])
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hxT
  let g : X →ₗ[ℤ] AddCircle (1 : ℚ) := c ∘ₗ (QuotientAddGroup.mk' T).toIntLinearMap
  have gS : ∀ v ∈ T, g v = 0 := fun v hv => by
    change c (QuotientAddGroup.mk v) = 0
    rw [(QuotientAddGroup.eq_zero_iff v).2 hv, map_zero]
  have gn : ∀ v, n • g v = 0 := fun v => by
    rw [← map_nsmul]
    exact gS _ (AddSubgroup.mem_sup_right ⟨v, rfl⟩)
  let b := Module.Free.chooseBasis ℤ X
  choose r hr using fun i => QuotientAddGroup.mk_surjective (g (b i))
  have hm : ∀ i, ∃ m : ℤ, (m : ℚ) = n * r i := fun i => by
    have := gn (b i)
    rw [← hr i, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, by rw [← nsmul_eq_mul, ← hm, zsmul_eq_mul, _root_.mul_one]⟩
  choose m hm using hm
  let φ : X →ₗ[ℤ] ℚ := b.constr ℤ r
  let ψ : X →ₗ[ℤ] ℤ := b.constr ℤ m
  have hψ : ∀ v, (ψ v : ℚ) = n * φ v := by
    have : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ ψ = (n : ℤ) • φ := b.ext fun i => by
      simp [ψ, φ, hm]
    intro v
    have := congrArg (fun f : X →ₗ[ℤ] ℚ => f v) this
    simpa using this
  have hφ : ∀ v, (QuotientAddGroup.mk (φ v) : AddCircle (1 : ℚ)) = g v := by
    have : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap ∘ₗ φ = g := b.ext fun i => by
      simp [φ, hr]
    intro v
    exact congrArg (fun f : X →ₗ[ℤ] AddCircle (1 : ℚ) => f v) this
  have key : ∀ v, g v = 0 ↔ (n : ℤ) ∣ ψ v := fun v => by
    rw [← hφ, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have : (ψ v : ℚ) = ((n * k : ℤ) : ℚ) := by rw [hψ, ← hk]; push_cast; ring
      exact_mod_cast this
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have := hψ v
      rw [hk] at this
      push_cast at this
      rw [zsmul_eq_mul, _root_.mul_one]
      exact mul_left_cancel₀ hn' this
  let ζu : Fˣ := (hζ.isUnit hn.ne').unit
  have hζu : IsPrimitiveRoot ζu n := IsPrimitiveRoot.coe_units_iff.1 (by simpa [ζu] using hζ)
  let t : Multiplicative X →* Fˣ :=
    { toFun := fun χ => ζu ^ ψ (Multiplicative.toAdd χ)
      map_one' := by simp
      map_mul' := fun a a' => by simp [zpow_add] }
  have tv : ∀ v, t (Multiplicative.ofAdd v) = 1 ↔ (n : ℤ) ∣ ψ v := fun v => hζu.zpow_eq_one_iff_dvd _
  refine ⟨t, MonoidHom.ext fun χ => ?_, fun s hs => (tv s).2 ((key s).1 (gS s (AddSubgroup.mem_sup_left hs))),
    fun h => hc ((key x).2 ((tv x).1 h))⟩
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  change (ζu ^ ψ (Multiplicative.toAdd χ)) ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζu.pow_eq_one, one_zpow]

theorem tateIsoQ_y_cois : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type)
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F),
    ∃ y : ℕ → D.La →ₗ[𝓞 E] D₀.X, (∀ n, 0 < n → ∀ a, ∃ e, y n a = (I.ev n a).y + n • e) ∧
      ∀ n, 0 < n → Cois D (y n) n := by
  intro E _ _ _ H D R _ _ _ _ D₀ _ oa hev hB F _ _ _ _ I
  letI := H.starRing
  haveI := D.proj
  have lift : ∀ n, ∃ y : D.La →ₗ[𝓞 E] D₀.X, 0 < n → ∀ a, ∃ e, y a = (I.ev n a).y + n • e := fun n => by
    by_cases hn : 0 < n
    · have h₁ : ∀ a b, ∃ e, (I.ev n (a + b)).y = (I.ev n a).y + (I.ev n b).y + n • e := fun a b => by
        obtain ⟨q, hq, -, z, hz, -⟩ := I.add n hn a b
        exact ⟨z, by rw [hz, hq]⟩
      have h₂ : ∀ (c : 𝓞 E) a, ∃ e, (I.ev n (c • a)).y = c • (I.ev n a).y + n • e := fun c a => by
        obtain ⟨q, hq, -, z, hz, -⟩ := I.lin n hn c a
        exact ⟨z, by rw [hz, hq]⟩
      obtain ⟨y, hy⟩ := exists_linear_lift (R := 𝓞 E) (M := D.La) n (fun a => (I.ev n a).y) h₁ h₂
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose y hy using lift
  refine ⟨y, hy, fun n hn => ?_⟩
  have hζ : IsPrimitiveRoot ((I.ζ n : Fˣ) : F) n := IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)
  have tv : ∀ t : Multiplicative D₀.X →* Fˣ, t ^ n = 1 → ∀ a,
      t (Multiplicative.ofAdd (I.ev n a).y) = t (Multiplicative.ofAdd (y n a)) := by
    intro t ht a
    obtain ⟨e, he⟩ := hy n hn a
    rw [he, ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, ht, MonoidHom.one_apply, _root_.mul_one]
  have dv : ∀ c : D.La, (∀ a, I.ζ n ^ D.EF c a = 1) → ∃ e, c = n • e := fun c h =>
    exists_nsmul_of_dvd D hn fun a => ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).1 (h a)
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · by_contra hx
    push_neg at hx
    obtain ⟨t, ht, hS, hx'⟩ := exists_char hζ hn (LinearMap.range (y n)).toAddSubgroup x (by
      rintro s ⟨a, rfl⟩ e
      exact hx a e)
    obtain ⟨b, b', -, h1, h2, h3⟩ := torus_pair D D₀ oa hev hB F I n hn t 1 ht (one_pow n)
    obtain ⟨e, he⟩ := dv b fun a => by rw [h1, tv t ht]; exact hS _ ⟨a, rfl⟩
    obtain ⟨e', he'⟩ := dv b' fun a => by rw [h2]; rfl
    exact hx' (by rw [h3 ⟨e - e', by rw [he, he', smul_sub, add_sub_cancel]⟩]; rfl)
  · by_contra hne
    push_neg at hne
    obtain ⟨t, ht, -, hx'⟩ := exists_char hζ hn ⊥ (y n a) (by
      intro s hs e h
      rw [AddSubgroup.mem_bot] at hs
      subst hs
      exact hne (-e) (by rw [smul_neg]; exact eq_neg_of_add_eq_zero_left h.symm))
    obtain ⟨b, -, ⟨e, he⟩, h1, -⟩ := torus_pair D D₀ oa hev hB F I n hn t 1 ht (one_pow n)
    obtain ⟨e', he'⟩ := hy n hn b
    obtain ⟨k, hk⟩ := ha b ⟨e + e', by rw [he', he, smul_add]⟩
    apply hx'
    rw [← tv t ht, ← h1, ef_swap, hk]
    exact ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).2 ⟨-k, by ring⟩

end GlobalTheory.LowFilt
