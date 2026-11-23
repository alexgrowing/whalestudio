import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mem_iff (k : ℕ) (a : Dw.La) :
    a ∈ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) ↔ ∃ b, a = k • b := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, Nat.cast_smul_eq_nsmul _ _ _⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, Nat.cast_smul_eq_nsmul _ _ _⟩

theorem finite_quot {O M : Type} [CommRing O] [Module.Finite ℤ O] [AddCommGroup M] [Module O M] [Module.Finite O M]
    (N : Submodule O M) {k : ℕ} (hk : k ≠ 0) (h : ∀ a : M, k • a ∈ N) : Finite (M ⧸ N) := by
  haveI : Module.Finite ℤ (M ⧸ N) := Module.Finite.trans O (M ⧸ N)
  refine Module.finite_of_fg_torsion (M ⧸ N) fun x =>
    ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)⟩, ?_⟩
  obtain ⟨a, rfl⟩ := N.mkQ_surjective x
  show (k : ℤ) • N.mkQ a = 0
  rw [natCast_zsmul, ← map_nsmul]
  exact (Submodule.Quotient.mk_eq_zero _).2 (h a)

theorem finite_latMod {k : ℕ} (hk : k ≠ 0) : Finite (LatMod Dw k) :=
  haveI := Dw.fin
  finite_quot _ hk fun a => (mem_iff k _).2 ⟨a, rfl⟩

theorem finite_levGrp {k : ℕ} (hk : k ≠ 0) : Finite (LevGrp Dw k) :=
  haveI := finite_latMod (Dw := Dw) hk
  Finite.of_injective (fun g : LevGrp Dw k => (g : LatMod Dw k → LatMod Dw k)) DFunLike.coe_injective

theorem etaExpr_comp {S : Type} [CommRing S] (k : ℕ) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) (h : LevGrp Dw k) :
    etaExpr k cf x (fun q => w (h q)) = etaExpr k cf x w :=
  finprod_comp_equiv (Equiv.mulLeft h) (f := fun g : LevGrp Dw k => ∑ j, (cf j : S) * ∏ b, w (g (x j b)))

theorem etaExpr_smul {S : Type} [CommRing S] {k : ℕ} (hk : k ≠ 0) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) (t : S) :
    etaExpr k cf x (fun q => t * w q) = t ^ (n * Nat.card (LevGrp Dw k)) * etaExpr k cf x w := by
  haveI := finite_levGrp (Dw := Dw) hk
  haveI := Fintype.ofFinite (LevGrp Dw k)
  unfold etaExpr
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, pow_mul,
    ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem exists_isFullLev {k : ℕ} (hk : 0 < k) {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K]
    (y : FrPt Xo c K) : ∃ ev, IsFullLev Xo k y.x ev ∧ ∀ z : ptO Xo y.x ⟶ Xo.univ.t.G, z ^ k = 1 ↔ ∃ q, ev q = z := by
  obtain ⟨-, I, -⟩ := Xo.univ.geom K y.x _ y.x_over
  have h0 : I.ev k 0 = 1 := (I.ker k hk 0).2 ⟨0, by simp⟩
  have key : ∀ a b, I.ev k a = I.ev k b ↔ (Submodule.Quotient.mk a : LatMod Dw k) = Submodule.Quotient.mk b := by
    intro a b
    rw [Submodule.Quotient.eq, mem_iff, ← I.ker k hk]
    have : I.ev k a = I.ev k (a - b) * I.ev k b := by rw [← I.add, sub_add_cancel]
    rw [this]
    exact ⟨fun h => by simpa using h, fun h => by rw [h, _root_.one_mul]⟩
  have hq : ∀ q : LatMod Dw k, (Submodule.Quotient.mk (qRep q) : LatMod Dw k) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  refine ⟨fun q => I.ev k (qRep q), ⟨fun a b => ?_, fun o a => ?_, fun L _ χ a b h => ?_⟩, fun z => ?_⟩
  · rw [← I.add, key, Submodule.Quotient.mk_add, hq, hq, hq]
  · refine Eq.trans ?_ (I.lin k o (qRep a))
    rw [key, Submodule.Quotient.mk_smul, hq, hq]
  · haveI : Epi (spMap χ) := by
      letI := χ.toAlgebra
      haveI : Flat (spMap χ) := by
        rw [HasRingHomProperty.Spec_iff (P := @Flat)]
        exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat K L))
      haveI : Surjective (spMap χ) := ⟨fun p => ⟨default, Subsingleton.elim _ _⟩⟩
      exact Flat.epi_of_flat_of_surjective _
    rw [← hq a, ← hq b, ← key]
    exact Over.OverMorphism.ext ((cancel_epi _).1 h)
  · rw [I.onto k hk]
    exact ⟨fun ⟨a, ha⟩ => ⟨Submodule.Quotient.mk a, ((key _ _).2 (hq _)).trans ha⟩, fun ⟨q, h⟩ => ⟨_, h⟩⟩

theorem exists_isNullVal (hL : Laws) {N : ℕ} (hN : Odd N) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (hp : p ^ (N ^ 2) = 1) : ∃ w, IsNullVal Xo c N y p w := by
  obtain ⟨F, hF⟩ := (GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hN _ y.s).1
    (fun t => t = p) (p ^ N) p rfl hp rfl
  obtain ⟨v, hv⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_value _ _ Xo.univ.t.PP.isLB ((N : ℤ) ^ 2) F 1
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (ptO Xo y.x) ((N : ℤ) ^ 2)) (GlobalTheory.ThetaReal.NormMul.rigT_isGen Xo.univ.t.PP.rigGen _)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom v, F, hF, ?_⟩
  have : toΓ S ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom v) = v := by
    unfold toΓ
    exact (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply v
  rw [this]
  exact hv

open GlobalTheory.TranslExist in
theorem isNullVal_unique (hL : Laws) {N : ℕ} (hN : Odd N) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (hp : p ^ (N ^ 2) = 1) {w w' : S} (h : IsNullVal Xo c N y p w)
    (h' : IsNullVal Xo c N y p w') : w = w' := by
  have hB := Xo.univ.t.PP.isLB
  obtain ⟨F, ⟨_, α₀, α, s₁, U, -, rfl, g₀, n₀, cα, tw, hU, a₁⟩, hv⟩ := h
  obtain ⟨F', ⟨_, β₀, β, r₁, V, -, rfl, gβ, nβ, cβ, tw', hV, b₁⟩, hv'⟩ := h'
  obtain ⟨g₁, -, -, u₀, -⟩ := GlobalTheory.T.universal_normalised_mulByNat_pullback_iso hL E H Dw l Xo N
  obtain rfl : r₁ = s₁ := twist_congr hB (fun z J hJ =>
    (val_corr hJ cβ _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (u₀ β₀ gβ nβ) _).trans
      ((val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans (val_corr hJ (u₀ α₀ g₀ n₀) _))).symm))) tw' tw
  obtain rfl : F = F' := act_congr hB (hU.pt_eq.trans hV.pt_eq.symm)
    ((GlobalTheory.T.universal_symLift_exists_unique_global hL E H Dw l Xo N hN _ _ hp).2 _ _ hU hV) a₁ b₁
  exact Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.toΓ_injective _ (Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.value_unique _ _ hB _ _ _ _ _ _ hv hv')

theorem exists_etaValAt (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) :
    ∃ v, EtaValAt Xo c R cf x y v := by
  obtain ⟨ev, hev, ht⟩ := exists_isFullLev Xo c (pow_pos hR.pos 4) y
  have : ∀ q, ∃ w, IsNullVal Xo c (R ^ 2) y (ev q) w := fun q =>
    exists_isNullVal Xo c hL hR.pow y (ev q) (by rw [← pow_mul]; exact (ht _).2 ⟨q, rfl⟩)
  choose w hw using this
  exact ⟨_, K, inferInstance, inferInstance, AlgHom.id _ _, y, ev, w,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
    (GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).1 K y, hev, hw, rfl⟩

theorem pow_eq_one_of_isFullLev {k : ℕ} {S : Type} [CommRing S] {x0 : Sp S ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (h : IsFullLev Xo k x0 ev) (q : LatMod Dw k) : ev q ^ k = 1 := by
  have h0 : ev 0 = 1 := by
    have := h.1 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hn : ∀ m : ℕ, ev (m • q) = ev q ^ m := fun m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ m ih => rw [succ_nsmul, h.1, ih, pow_succ]
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [← hn, ← map_nsmul, ← h0]
  exact congrArg ev ((Submodule.Quotient.mk_eq_zero _).2 ((mem_iff k _).2 ⟨a, rfl⟩))

theorem exists_cover (hL : Laws) {R : ℕ} (hR : Odd R) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
      (ev : LatMod Dw (R ^ 4) → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → S'),
      φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ IsFullLev Xo (R ^ 4) y'.x ev ∧
      ∀ q, IsNullVal Xo c (R ^ 2) y' (ev q) (w q) := by
  obtain ⟨B, _, ψ, e, hψ, ha, hl, hk, hi⟩ :=
    GlobalTheory.exists_faithfullyFlat_linear_level hL E H Dw l Xo S y.x (R ^ 4) (pow_pos hR.pos 4)
  letI : Algebra c.F B := (ψ.comp (algebraMap c.F S)).toAlgebra
  let φ : S →ₐ[c.F] B := { ψ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S B φ y
  obtain ⟨x', p1, p2, p3, p4, p5, p6, p7⟩ := y'
  obtain rfl : x' = spMap ψ ≫ y.x := hy'.1
  have hq : ∀ q : LatMod Dw (R ^ 4), (Submodule.Quotient.mk (qRep q) : LatMod Dw (R ^ 4)) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  have key : ∀ a b, (Submodule.Quotient.mk a : LatMod Dw (R ^ 4)) = Submodule.Quotient.mk b → e a = e b := by
    intro a b h
    obtain ⟨d, hd⟩ := (mem_iff _ _).1 ((Submodule.Quotient.eq _).1 h)
    rw [← sub_add_cancel a b, hd, ha, hk, _root_.one_mul]
  have hev : IsFullLev Xo (R ^ 4) (spMap ψ ≫ y.x) fun q => e (qRep q) := by
    refine ⟨fun a b => ?_, fun o a => ?_, fun L _ χ a b h => ?_⟩
    · rw [← ha]
      exact key _ _ (by rw [Submodule.Quotient.mk_add, hq, hq, hq])
    · rw [← hl]
      exact key _ _ (by rw [Submodule.Quotient.mk_smul, hq, hq])
    · rw [← hq a, ← hq b, Submodule.Quotient.eq, mem_iff]
      exact hi L χ _ _ h
  have : ∀ q, ∃ w, IsNullVal Xo c (R ^ 2) ⟨_, p1, p2, p3, p4, p5, p6, p7⟩ (e (qRep q)) w := fun q =>
    exists_isNullVal Xo c hL hR.pow _ _ (by rw [← pow_mul]; exact pow_eq_one_of_isFullLev Xo hev q)
  choose w hw using this
  exact ⟨B, inferInstance, inferInstance, φ, _, _, w, hψ, hy', hev, hw⟩

theorem isEtaRule_zero_columns (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] (cf : J → ℤ)
    (x : J → Fin 0 → LatMod Dw (R ^ 4)) :
    IsEtaRule Xo c R cf x fun p _ => ((∑ j, cf j : ℤ) : p.R) ^ Nat.card (LevGrp Dw (R ^ 4)) := by
  intro p y
  obtain ⟨S', _, _, φ, y', ev, w, h1, h2, h3, h4⟩ := exists_cover Xo c hL hR y
  refine ⟨S', _, _, φ, y', ev, w, h1, h2, h3, h4, ?_⟩
  haveI := finite_levGrp (Dw := Dw) (pow_pos hR.pos 4).ne'
  haveI := Fintype.ofFinite (LevGrp Dw (R ^ 4))
  unfold etaExpr
  rw [finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card]
  simp

theorem exists_isEtaRule_one (hL : Laws) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (1 ^ 4)) : ∃ f, IsEtaRule Xo c 1 cf x f := by
  have hs : ∀ a b : LatMod Dw (1 ^ 4), a = b := fun a b => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact (Submodule.Quotient.eq _).2 ((mem_iff _ _).2 ⟨a - b, by simp⟩)
  have : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃ v, EtaValAt Xo c 1 cf x y v := fun p y => by
    obtain ⟨w, hw⟩ := exists_isNullVal Xo c hL (N := 1 ^ 2) odd_one.pow y 1 (one_pow _)
    exact ⟨_, p.R, inferInstance, inferInstance, AlgHom.id _ _, y, fun _ => 1, fun _ => w,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      (GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).1 _ y,
      ⟨fun _ _ => (_root_.one_mul _).symm, fun o _ => by
        haveI := Xo.univ.t.act.hom o
        exact (MonObj.one_comp _).symm, fun _ _ _ a b _ => hs a b⟩, fun _ => hw, rfl⟩
  choose f hf using this
  exact ⟨f, hf⟩

end GlobalTheory.EtaForm.Model
