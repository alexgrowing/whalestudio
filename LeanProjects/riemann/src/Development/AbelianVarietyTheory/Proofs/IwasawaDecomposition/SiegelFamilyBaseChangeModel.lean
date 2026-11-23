import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmFamilyFiniteUnramifiedOverSiegelFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionSectionsOfRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfCommonGenericFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnramifiedQuasiFiniteOfTangent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModN
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexPrimeMemNonunits

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelPoint

open GlobalTheory.LevCover GlobalTheory.TorsionSections

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {pr : ℕ → Q → Q → kˣ → Prop}

theorem ptCond_explicit (I : TateIso D k Q act pr) {M : ℕ} (hM : 0 < M) {w : kˣ} {v : ℤ} (hv : w = I.ζ M ^ v)
    {e f t : 𝓞 E} (ht : e * (1 - e) = M * t) (hf : ∀ x c, D.EF x (f • c) = D.EF ((1 - e) • x) c) {J : Type}
    (rep : J → D.La) (a b : D.La) : PtCond I M w e f rep a b (I.ev M (e • a + (1 - e) • v • b)) := by
  have hs : ∀ x : D.La, (e * (1 - e)) • x = M • (t • x) := fun x => by
    rw [ht, mul_smul, Nat.cast_smul_eq_nsmul]
  refine ⟨(I.onto M hM _).2 ⟨_, rfl⟩, ?_, fun j => ?_⟩
  · rw [← I.lin, tateIso_ev_eq_iff I hM]
    refine ⟨t • (v • b - a), ?_⟩
    rw [← hs]
    module
  · have h := I.isom M hM (e • a + (1 - e) • v • b) (f • rep j)
    rw [hv, ← zpow_mul]
    refine (zpow_congr (I.ζ_prim M hM)).2 ?_ ▸ h
    have e1 : (1 - e) • (e • a + (1 - e) • v • b) = v • (1 - e) • b + M • (t • (a - v • b)) := by
      rw [← hs]
      module
    rw [hf, hf, e1]
    refine ⟨D.EF (t • (a - v • b)) (rep j), ?_⟩
    simp only [map_add, map_nsmul, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, smul_eq_mul]
    ring

theorem dvd_similitude (l : Level H) {e : 𝓞 E} (he : e ∈ Mc l) (he' : 1 - e ∈ l.Mb) (v : ℤ) (a c : D.La) :
    (l.M : ℤ) ∣ D.EF (e • a + (1 - e) • v • a) (e • c + (1 - e) • v • c) - v * D.EF a c := by
  have key : ∀ u ∈ l.Mb, ∀ u' ∈ Mc l, ∀ x y : D.La, (l.M : ℤ) ∣ D.EF x ((u * u') • y) := fun u hu u' hu' x y => by
    have : u * u' ∈ Ideal.span {(l.M : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul hu hu'
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 this
    rw [ht, mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    exact dvd_mul_right _ _
  have hbar : ∀ x : 𝓞 E, H.bar (H.bar x) = x := fun x => by
    apply Subtype.ext
    change ((H.bar (H.bar x) : 𝓞 E) : E) = (x : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have hb : H.bar e ∈ l.Mb := by
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 he
    change H.bar (H.bar x) ∈ _
    rwa [hbar]
  have h1 : (l.M : ℤ) ∣ D.EF (e • a) (e • c) := by
    rw [D.adj, ← mul_smul]
    exact key _ hb _ he _ _
  have h2 : (l.M : ℤ) ∣ D.EF ((1 - e) • a) ((1 - e) • c) := by
    rw [D.adj, ← mul_smul, mul_comm]
    exact key _ he' _ (Ideal.mem_map_of_mem _ he') _ _
  have e1 : a = e • a + (1 - e) • a := by module
  have e2 : c = e • c + (1 - e) • c := by module
  have e3 : D.EF a c = D.EF (e • a + (1 - e) • a) (e • c + (1 - e) • c) := by rw [← e1, ← e2]
  rw [e3, smul_comm (1 - e) v, smul_comm (1 - e) v]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  rw [hp, hq]
  exact ⟨(1 - v) * p + (v * v - v) * q, by ring⟩

end Lattice

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B F : Type} [CommRing B] [Field F] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem secCond_mul (hL : Out.Laws) [IsLocallyNoetherian S] {o : Obj D l b s} {sF : S ⟶ Sp F} {z : Fˣ} {e f : 𝓞 E}
    {J : Type} {rep : J → D.La} {a a' c c' : D.La} {T : Over S} {y y' : T ⟶ o.t.G}
    (h : SecCond o sF z e f rep a a' T y) (h' : SecCond o sF z e f rep c c' T y') :
    SecCond o sF z e f rep (a + c) (a' + c') T (y * y') := by
  have := o.t.act.hom e
  refine ⟨by rw [mul_pow, h.1, h'.1, _root_.mul_one], ?_, fun j => ?_⟩
  · rw [MonObj.mul_comp, h.2.1, h'.2.1, smul_add, o.eta_add, MonObj.comp_mul]
  · rw [map_add, LinearMap.add_apply, zpow_add, map_mul]
    exact (hL.weil S (Obj.toPolAV o) l.M T).2.1 _ _ _ _ _ (h.2.2 j) (h'.2.2 j)

theorem exists_level (hL : Out.Laws) [IsLocallyNoetherian S] (o : Obj D l b s) (sF : S ⟶ Sp F) {z : Fˣ}
    (hz : IsPrimitiveRoot z l.M) {n m : ℕ} (hnm : l.M = n * m) :
    ∃ lev : D.La → (𝟙_ (Over S) ⟶ o.t.G), (∀ a c, lev (a + c) = lev a * lev c) ∧ (∀ a, lev a ^ n = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (δ : F →+* k), x ≫ sF = spMap δ → ∀ a c,
        Out.WeilIs o.t.G o.t.PP.L n (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev c)
          (unitOn ((Units.map δ.toMonoidHom z ^ m) ^ D.EF a c)) := by
  have hM := M_pos l
  have hn : 0 < n := Nat.pos_of_mul_pos_right (hnm ▸ hM)
  have hm : 0 < m := Nat.pos_of_mul_pos_left (hnm ▸ hM)
  obtain ⟨e, he, he'⟩ := LevCover.exists_idem l
  obtain ⟨_, _⟩ := datum_free D
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod D.La hM
  let rep : Set.range q → D.La := fun c => c.2.choose
  have hrep : ∀ a, ∃ j d, a = rep j + l.M • d := fun a =>
    ⟨⟨q a, a, rfl⟩, hq _ _ (⟨a, rfl⟩ : q a ∈ Set.range q).choose_spec⟩
  choose σ hσ using exists_section_secCond hL o sF hz he he' hrep
  have h0 : ∀ a a', SecCond o sF z e (H.bar (1 - e)) rep a a' _ (σ a a') := fun a a' =>
    (hσ a a' _ _).2 (by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
  obtain ⟨t, ht⟩ : ∃ t, e * (1 - e) = l.M * t := by
    have : (1 - e) * e ∈ Ideal.span {(l.M : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul he' he
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 this
    exact ⟨t, by rw [mul_comm e, ht]⟩
  have hf : ∀ x c, D.EF x (H.bar (1 - e) • c) = D.EF ((1 - e) • x) c := fun x c => (D.adj _ _ _).symm
  refine ⟨fun a => σ a a ^ m, fun a c => ?_, fun a => ?_, fun k _ _ x δ hδ a c => ?_⟩
  · have h := (hσ _ _ _ _).1 (secCond_mul hL (h0 a a) (h0 c c))
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp] at h
    beta_reduce
    rw [← h, mul_pow]
  · rw [← pow_mul, mul_comm, ← hnm]
    exact (h0 a a).1
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x β hβ
  have hw : IsPrimitiveRoot (Units.map δ.toMonoidHom z) l.M := hz.map_of_injective (Units.map_injective δ.injective)
  obtain ⟨v, -, hv⟩ := exists_coprime_zpow hM (I.ζ_prim _ hM) hw
  have hf' : H.bar (1 - e) ∈ Mc l := Ideal.mem_map_of_mem _ he'
  have val : ∀ a, toUnit (Over.mk x) ≫ σ a a = I.ev l.M (e • a + (1 - e) • v • a) := fun a => by
    have h := ptCond_explicit I hM hv ht hf rep a a
    refine ((hσ _ _ _ _).1 ⟨h.1, ?_, fun j => ?_⟩).symm
    · rw [hI _ (Submodule.smul_mem_smul he Submodule.mem_top)]
      exact h.2.1
    · rw [hI _ (Submodule.smul_mem_smul hf' Submodule.mem_top)]
      refine (congrArg (Out.WeilIs o.t.G o.t.PP.L l.M _ _) ?_).mpr (h.2.2 j)
      show Units.map (fnOn (x ≫ sF)).toMonoidHom _ = _
      rw [hδ, map_fnOn_spMap, map_zpow]
  have val' : ∀ a, toUnit (Over.mk x) ≫ σ a a ^ m = I.ev n (e • a + (1 - e) • v • a) := fun a => by
    rw [MonObj.comp_pow, val, hnm, I.tower n m hn hm]
  have h := I.isom n hn (e • a + (1 - e) • v • a) (e • c + (1 - e) • v • c)
  have e1 : (Units.map δ.toMonoidHom z ^ m) ^ D.EF a c =
      I.ζ n ^ D.EF (e • a + (1 - e) • v • a) (e • c + (1 - e) • v • c) := by
    have e0 : (I.ζ l.M ^ v) ^ m = I.ζ n ^ v := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm v, zpow_mul, zpow_natCast, hnm, I.ζ_pow n m hn hm]
    rw [hv, e0, ← zpow_mul, eq_comm, zpow_congr (I.ζ_prim n hn)]
    exact (Int.natCast_dvd_natCast.2 ⟨m, hnm⟩).trans (dvd_similitude l he he' v a c)
  rw [val', val', e1]
  exact h

end Level

section Point

open GlobalTheory.CechPic GlobalTheory.FullSiegel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B F : Type} [CommRing B] [Field F] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem exists_point (hL : Out.Laws) [IsLocallyNoetherian S] [IsReduced S] (o : Obj D l b s) (sF : S ⟶ Sp F) {z : Fˣ}
    (hz : IsPrimitiveRoot z l.M) {n m : ℕ} (hnm : l.M = n * m) {R : Type} [CommRing R] {ζ : R} (κ : R →+* F)
    (hκ : Function.Injective κ) (hζ : κ ζ = (z : F) ^ m)
    (Fm : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n ζ) :
    ∃ (y : S ⟶ Fm.X) (α : o.t.G.left ⟶ Fm.univ.A.left) (α₂ : (G2 o.t.G).left ⟶ (G2 Fm.univ.A).left),
      y ≫ Fm.s = sF ≫ spMap κ ∧ IsGrpPullback o.t.G Fm.univ.A y α ∧ IsSquare α α₂ ∧
        LBIso (abelian₂ o.t.G o.t.PP.L) (Fm.univ.P.pull α₂) := by
  have hM := M_pos l
  have hn : 0 < n := Nat.pos_of_mul_pos_right (hnm ▸ hM)
  obtain ⟨lev, hadd, htors, hweil⟩ := exists_level hL o sF hz hnm
  obtain ⟨bas₀, hbas₀⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  obtain ⟨-, bas, hbas⟩ := GlobalTheory.ZM.sympBasis_std E H D (Module.finrank ℚ E / 2 * (D.p + D.q)) bas₀ hbas₀
  have hA : IsAbelianScheme o.t.G := ObjDim.isAbelianScheme o
  have hLB := o.t.PP.isLB
  let P : Out.PolAV S := Obj.toPolAV o
  have hΔ := cls_diag hL.mulPull P
  have hΔ' := pull_isLB (isLB_lam hLB) (lift (𝟙 o.t.G) (𝟙 o.t.G)).left
  let c : SiegPre (Module.finrank ℚ E / 2 * (D.p + D.q)) n ζ (sF ≫ spMap κ) :=
    { A := o.t.G, ab := hA, P := abelian₂ o.t.G o.t.PP.L, isLB := isLB_lam hLB
      rig₁ := (cls_eq_zero_iff (pull_isLB (isLB_lam hLB) _)).1 ((cls_lam_pull hLB _ _).trans (lam_one_left _ _))
      rig₂ := (cls_eq_zero_iff (pull_isLB (isLB_lam hLB) _)).1 ((cls_lam_pull hLB _ _).trans (lam_one_right _ _))
      symm := lam_symm hLB
      lev := fun a => lev (bas a)
      lev_add := fun a c => by rw [map_add, hadd]
      lev_tors := fun a => htors _
      geom := by
        intro k _ _ x β v hx hv
        obtain ⟨δ, hδ⟩ := exists_spMap (x ≫ sF)
        obtain ⟨β₀, -⟩ := exists_spMap (x ≫ s)
        obtain rfl : β = δ.comp κ := by
          rw [reassoc_of% hδ, ← spMap_comp] at hx
          exact congrArg CommRingCat.Hom.hom (Spec.map_injective hx.symm)
        obtain rfl : v = Units.map δ.toMonoidHom z ^ m := Units.ext (by
          rw [hv, RingHom.comp_apply, hζ, map_pow]; rfl)
        have hk : (n : k) ≠ 0 := by simpa using ((b.unit n hn).map β₀).ne_zero
        have hw : IsPrimitiveRoot (Units.map δ.toMonoidHom z ^ m) n :=
          (hz.map_of_injective (Units.map_injective δ.injective)).pow hM (hnm.trans (mul_comm _ _))
        obtain ⟨h₁, h₂⟩ := GlobalTheory.TorsIsometry.ker_and_onto E H D k (Over.mk x ⟶ o.t.G)
          (fun y y' c => Out.WeilIs o.t.G o.t.PP.L n y y' (unitOn c)) n _ (fun a => toUnit _ ≫ lev a) hn
          (by rw [finrank_int_lattice D]; exact (hL.mulN S P n hn).2.2.2.2 k x hk)
          (fun _ _ _ h => FullSpread.eq_one_of_weilIs_one P hL.weil h) hw
          (fun a c => by rw [hadd, MonObj.comp_mul])
          (fun a => by rw [← MonObj.comp_pow, htors, MonObj.comp_one]) (hweil k x δ hδ)
        refine ⟨fun a => (h₁ _).trans ⟨?_, ?_⟩, fun g hg => ?_, fun a c => ?_⟩
        · rintro ⟨c, hc⟩
          exact ⟨bas.symm c, bas.injective (by rw [hc, map_nsmul, bas.apply_symm_apply])⟩
        · rintro ⟨c, rfl⟩
          exact ⟨bas c, map_nsmul _ _ _⟩
        · obtain ⟨a, ha⟩ := (h₂ g).1 hg
          exact ⟨bas.symm a, by rw [bas.apply_symm_apply]; exact ha⟩
        · have i := weilIs_sq hL.globalFns hA hLB hΔ' hΔ (hweil k x δ hδ (bas a) (bas c))
          rwa [unitOn, ← map_pow, ← zpow_natCast, ← zpow_mul, hbas, mul_comm (omegaStd a c)] at i }
  have hpr : c.Principal := by
    refine ⟨?_, eq_one_of_lam_triv hLB P.rigid o.ktriv⟩
    have R := relAmple_finite_pow_iso S o.t.G o.t.G (𝟙 _) o.t.PP.L 2 two_pos hA hA hLB
      (inferInstanceAs (IsFinite (𝟙 _)))
    have R' := relAmple_finite_pow_iso S o.t.G o.t.G (𝟙 _) (lbPow o.t.PP.L 2) 2 two_pos hA hA (isLB_lbPow hLB 2)
      (inferInstanceAs (IsFinite (𝟙 _)))
    exact R'.2.2.2 _ hΔ' ((cls_eq_iff (isLB_lbPow hLB 2) hΔ').1 ((cls_lbPow hLB 2 _).trans hΔ.symm))
      (R.2.1.2 o.ample)
  have hd : Dense {x : S | ((sF ≫ spMap κ) x).asIdeal = ⊥} := by
    refine dense_univ.mono fun x _ => ?_
    change Ideal.comap κ (sF x).asIdeal = ⊥
    have : (sF x).asIdeal.IsPrime := (sF x).isPrime
    rw [Ideal.eq_bot_of_prime (sF x).asIdeal, Ideal.comap_bot_of_injective _ hκ]
  obtain ⟨y, hy, α, α₂, h₁, h₂, h₃, -⟩ := Fm.rep S _ c inferInstance hd hpr
  exact ⟨y, α, α₂, hy, h₁, h₂, h₃⟩

end Point

section Finite

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem torsion_eq_of_surjective {S : Scheme.{0}} {G : Over S} [GrpObj G] (hG : IsAbelianScheme G) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) {T T' : Over S} {x y : T ⟶ G} (hx : x ^ n = 1) (hy : y ^ n = 1) (h : T' ⟶ T)
    (hs : Function.Surjective h.left) (e : h ≫ x = h ≫ y) : x = y := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  obtain ⟨U, -, hU⟩ := clopenCond_torsion_eq hx hy
  have := (hU _ (𝟙 T)).2 (fun p _ => (hU _ h).1 e (hs p))
  simpa using this

theorem eq_constPt (hL : Out.Laws) (Xo : Moduli D l) {T Y : Scheme.{0}} {f : T ⟶ Xo.X}
    (o : Obj D l (baseKA l) (f ≫ Xo.s)) (m0 : ObjMap o Xo.univ f) {A : Over Y} [GrpObj A] {P : LB (G2 A).left}
    (hP : P.IsLB) {y : T ⟶ Y} {θ : o.t.G.left ⟶ A.left} {θ₂ : (G2 o.t.G).left ⟶ (G2 A).left}
    (hθ : IsGrpPullback o.t.G A y θ) (hsq : IsSquare θ θ₂) (hiso : LBIso (abelian₂ o.t.G o.t.PP.L) (P.pull θ₂))
    {k : Type} [Field k] (x : Sp (DualNumber k) ⟶ T) (hx : x ≫ y = constPt x ≫ y) : x ≫ f = constPt x ≫ f := by
  obtain ⟨o', ⟨κ⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (f ≫ Xo.s)
    ((x ≫ f) ≫ Xo.s) x rfl rfl (by
      rw [show spMap (RingHom.id (KA l)) = 𝟙 _ from Spec.map_id _, Category.comp_id, Category.assoc]) o
  obtain ⟨κ', hκ'⟩ := FamSiegel.exists_sabMap_constPt hL E H k _ _ o.t A inferInstance P y θ θ₂ x o'.t κ.toSABMap
    o.proper hP hθ hsq hiso hx
  let r := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  have hc : r ≫ constPt x = r ≫ x := by
    rw [constPt, ← Category.assoc]
    exact (congrArg (· ≫ _) (TangentCrit.dualPt_dualBase k)).trans (Category.id_comp _)
  have hr : Function.Surjective r := fun p => by
    have hp : p ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      rw [range_comap_of_surjective _ _ fun a => ⟨TrivSqZeroExt.inl a, rfl⟩]
      intro a ha
      have ha' : TrivSqZeroExt.fst a = 0 := ha
      have e : a * a = 0 := by ext <;> simp [ha']
      exact (p.isPrime.mem_or_mem (e ▸ p.asIdeal.zero_mem)).elim id id
    exact hp
  have key : ∀ (σ' : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G) (σ : 𝟙_ (Over T) ⟶ o.t.G) (n : ℕ), 0 < n →
      σ' ^ n = 1 → σ ^ n = 1 → σ'.left ≫ κ.cm.F = x ≫ σ.left → σ'.left ≫ κ'.φ = constPt x ≫ σ.left := by
    intro σ' σ n hn h₁ h₂ h₃
    have hu : IsUnit (n : Γ(T, ⊤)) := by
      have := ((baseKA l).unit n hn).map (fnOn (f ≫ Xo.s))
      rwa [map_natCast] at this
    have e := torsion_eq_of_surjective (ObjDim.isAbelianScheme o) hu (x := pushHom κ'.cart _ σ')
      (y := toUnit _ ≫ σ) (by rw [← map_pow, h₁, map_one]) (by rw [← MonObj.comp_pow, h₂, MonObj.comp_one])
      (T' := Over.mk (r ≫ constPt x)) (Over.homMk r (by simp)) hr (by
        apply Over.OverMorphism.ext
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _), Over.comp_left, Over.comp_left,
          ObjPull.toUnit_left']
        change r ≫ σ'.left ≫ κ'.φ = (r ≫ constPt x) ≫ σ.left
        refine hθ.1.hom_ext ?_ ?_
        · rw [hc, Category.assoc, Category.assoc, hκ', reassoc_of% h₃]
          simp only [Category.assoc]
        · rw [Category.assoc, Category.assoc, κ'.cart.1.w, Over.w_assoc σ', Category.assoc, Over.w σ]
          simp)
    have e' := congrArg Over.Hom.left e
    rw [Over.comp_left, ObjPull.toUnit_left'] at e'
    exact e'.trans (congrArg (· ≫ _) (Category.id_comp _))
  have etaA_pow : ∀ {S : Scheme.{0}} {s : S ⟶ Sp (KA l)} (o : Obj D l (baseKA l) s) (a : D.La),
      o.etaA a ^ l.A = 1 := fun o a => by rw [← add_map_nsmul o.etaA_add, o.etaA_ker]
  obtain ⟨m, hm⟩ := ObjMaps.exists_sab_comp m0.toSABMap κ.toSABMap
  have e' : constPt x ≫ f = constPt (x ≫ f) := by simp only [constPt, Category.assoc]
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap o'.t Xo.univ.t (constPt (x ≫ f)), m'.φ = κ'.φ ≫ m0.toSABMap.φ := by
    rw [← e']; exact ObjMaps.exists_sab_comp m0.toSABMap κ'
  refine (Xo.unram k _ o' ⟨⟨m, fun a => ?_, fun a => ?_⟩⟩ ⟨⟨m', fun a => ?_, fun a => ?_⟩⟩).trans e'.symm
  · exact (congrArg _ hm).trans (ObjComp.sec_comp (m0.eta a) (κ.eta a))
  · exact (congrArg _ hm).trans (ObjComp.sec_comp (m0.etaA a) (κ.etaA a))
  · exact ((congrArg _ hm').trans (ObjComp.sec_comp (m0.eta a)
      (key _ _ l.M (M_pos l) (eta_pow o' a) (eta_pow o a) (κ.eta a)))).trans (congrArg (· ≫ _) e')
  · exact ((congrArg _ hm').trans (ObjComp.sec_comp (m0.etaA a)
      (key _ _ l.A l.A_pos (etaA_pow o' a) (etaA_pow o a) (κ.etaA a)))).trans (congrArg (· ≫ _) e')

theorem exists_model (hr : 1 ≤ D.p + D.q) (Xo : Moduli D l) (c : Coeff l) :
    ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F), Nonempty (Model Xo c β) := by
  classical
  obtain ⟨hP, hN⟩ := GlobalTheory.Moduli.jointExistence_and_moduliScheme
  obtain ⟨Y, -⟩ := hP.2 E H D hr (Function.update (fun l' => Classical.choice (hN E H D l' hr)) l Xo)
  obtain ⟨W, hW⟩ := GlobalTheory.exists_valuationSubring_complex_prime_mem_nonunits 2 Nat.prime_two
  have hg : l.GoodAt 2 := by
    rw [Level.GoodAt, Nat.factorization_eq_zero_of_not_dvd l.odd.not_two_dvd_nat, pow_zero, Nat.div_one]
    exact l.three_le
  have h : Nonempty (Model (Function.update (fun l' => Classical.choice (hN E H D l' hr)) l Xo l) c
      (c.V W).subtype) := ⟨Y 2 W Nat.prime_two hW ⟨l, c, hg⟩⟩
  rw [Function.update_self] at h
  exact ⟨_, _, _, h⟩

theorem exists_extension (hr : 1 ≤ D.p + D.q) (Xo : Moduli D l) (c : Coeff l)
    (o : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))
    (m0 : ObjMap o Xo.univ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)))
    {Z : Scheme.{0}} {A : Over Z} [GrpObj A] (hA : IsAbelianScheme A) {y : Xo.XF c ⟶ Z} {θ : o.t.G.left ⟶ A.left}
    (hθ : IsGrpPullback o.t.G A y θ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Z) (δ : c.F →+* V)
    (hz : x ≫ y = spMap (algebraMap V K) ≫ z) (hδ : x ≫ pullback.snd _ _ = spMap (algebraMap V K) ≫ spMap δ) :
    ∃ x' : Sp V ⟶ Xo.XF c, spMap (algebraMap V K) ≫ x' = x := by
  obtain ⟨O, _, β, ⟨Y⟩⟩ := exists_model hr Xo c
  obtain ⟨y', t, m, hs, hj, hab⟩ := model_point_extends E H D l Xo c O β Y V K (δ.comp β) x (by
    rw [Model.j, Category.assoc, pullback.condition, reassoc_of% Y.jQ_over, reassoc_of% hδ, spMap_comp])

  have fac : ∀ {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
      {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : G''.left ⟶ G.left}, IsGrpPullback G' G f φ →
      IsGrpPullback G'' G (g ≫ f) ψ → ∃ φ', IsGrpPullback G'' G' g φ' := by
    intro S S' S'' G G' G'' _ _ _ f g φ ψ h₁ h₂
    have w : ψ ≫ G.hom = (G''.hom ≫ g) ≫ f := by rw [h₂.1.w, Category.assoc]
    exact ⟨h₁.1.lift ψ _ w, h₁.cancel (h₂.congr rfl (h₁.1.lift_fst _ _ w).symm) (h₁.1.lift_snd _ _ w)⟩
  have hK := isGrpPullback_pullback o.t.G x
  obtain ⟨φ₂, h₂⟩ := fac Y.m0.cart (hK.comp m0.cart)
  obtain ⟨φ₃, h₃⟩ := fac m.cart ((h₂.comp Y.m.cart).congr hj.symm rfl)
  have hV := isGrpPullback_pullback A z
  obtain ⟨φ₁, h₁⟩ := fac hV ((hK.comp hθ).congr hz rfl)
  have := hA.comm
  have hab' : IsAbelianScheme ((Over.pullback z).obj A) :=
    ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) hV.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hV.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hV.1 hA.geomConnected⟩
  have hloc := hab (isAbelianScheme_of_common_generic_fibre _ t.G hab' t.semi (fun f hf => by
    obtain ⟨F, hF, -⟩ := GlobalTheory.homExtension_semiAbelian_dvr V K _ t.G (isSemiAbelian_of_isAbelianScheme _ hab') t.semi f hf
    exact ⟨F, hF.2⟩) _ h₁ h₃)
  have w : y' ≫ Y.s = spMap δ ≫ spMap β := by rw [hs, spMap_comp]
  have := Y.jQ_open
  have hrange : Set.range (pullback.lift y' (spMap δ) w) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Y.ab_gen]
    refine hloc ⟨p, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  refine ⟨IsOpenImmersion.lift Y.jQ _ hrange, (cancel_mono Y.jQ).1 ?_⟩
  rw [Category.assoc, IsOpenImmersion.lift_fac]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, hj, Model.j, Category.assoc]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, Y.jQ_over, hδ]

end Finite

open GlobalTheory.SiegelTor in

theorem exists_finite_siegel_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (κF : cycAway n →+* c.F) (o : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) (m0 : ObjMap o Xo.univ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → (∀ x, ((κF x : c.F) : ℂ) = (x : ℂ)) → ∃ (y : Xo.XF c ⟶ F.X) (α : o.t.G.left ⟶ F.univ.A.left) (α₂ : (G2 o.t.G).left ⟶ (G2 F.univ.A).left) (h : y ≫ F.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap κF), IsGrpPullback o.t.G F.univ.A y α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ o.t.G o.t.PP.L) (F.univ.P.pull α₂) ∧ IsFinite (pullback.lift y _ h) := by
  intro E _ _ _ H D l Xo c n κF o m0 F hr _ _ ⟨m, hnm⟩ hκ
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hM := M_pos l
  have pw : ∀ a b : ℕ, a * b ≠ 0 → zeta (a * b) ^ b = zeta a := fun a b h => by
    have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (left_ne_zero_of_mul h)
    have hb : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul h)
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hmem : zeta l.M ∈ c.F := by
    obtain ⟨d, hd⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    rw [← pw l.M d (hd ▸ Nat.lcm_ne_zero hM.ne' l.A_pos.ne'), ← hd]
    exact pow_mem c.zeta_mem d
  have hz₀ : IsPrimitiveRoot (⟨zeta l.M, hmem⟩ : c.F) l.M :=
    IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (Complex.isPrimitiveRoot_exp l.M hM.ne')
      Subtype.val_injective
  obtain ⟨z, hz⟩ := hz₀.isUnit hM.ne'
  have hz' : IsPrimitiveRoot z l.M := IsPrimitiveRoot.coe_units_iff.1 (hz ▸ hz₀)
  have hζ : κF (zetaAway n) = (z : c.F) ^ m := by
    apply Subtype.ext
    rw [hκ, hz]
    change zeta n = zeta l.M ^ m
    rw [hnm, pw n m (hnm ▸ hM.ne')]
  have hinj : Function.Injective κF := fun x y e => Subtype.ext (by rw [← hκ x, ← hκ y, e])
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨hred, -, hnoe⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance
  obtain ⟨y, α, α₂, h, h₁, h₂, h₃⟩ := exists_point hL o
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hz' hnm κF hinj hζ F
  refine ⟨y, α, α₂, h, h₁, h₂, h₃, ?_⟩
  have e₁ := pullback.lift_fst y _ h
  have e₂ := pullback.lift_snd y _ h
  generalize pullback.lift y _ h = w at e₁ e₂
  have := F.isSeparated
  have := FamSiegel.locallyOfFiniteType_of_qproj F.qproj
  have : IsProper w := by
    refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic c.F _ _ w (pullback.snd _ _) inferInstance ?_ ?_
    · rw [e₂]
      exact (GlobalTheory.isQProjOver_finite_and_baseChange _ _ Xo.s Xo.qproj).2 _ _
    intro V K _ _ _ _ _ _ _ x v _ hxv
    obtain ⟨δ, hδ⟩ := exists_spMap (v ≫ pullback.snd F.s (spMap κF))
    exact exists_extension hr Xo c o m0 F.univ.ab h₁ V K x (v ≫ pullback.fst _ _) δ
      (by rw [← e₁, reassoc_of% hxv]) (by rw [← e₂, reassoc_of% hxv, hδ])
  have : LocallyQuasiFinite w := by
    refine (GlobalTheory.TangentCriterion.unramified_quasiFinite_of_tangent _ _ w inferInstance fun K _ x hx => ?_).2
    refine pullback.hom_ext (eq_constPt hL Xo o m0 F.univ.isLB h₁ h₂ h₃ x ?_) ?_
    · rw [← e₁, reassoc_of% hx]
    · rw [← e₂, reassoc_of% hx]
  exact IsFinite.of_isProper_of_locallyQuasiFinite w

end GlobalTheory.SiegelPoint
