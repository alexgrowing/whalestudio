import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0
open GlobalTheory.Adelic (cutIdeal mem_support_cutIdeal)

variable {k : Type} [CommRing k] {Y T : Scheme.{0}}

theorem memTop (y : Y) : y ∈ (⊤ : Y.Opens) := by
  simp

section Division

variable {p : Y ⟶ Sp k} {P B N : LB Y} {O O' : Y.Opens}

def Regular (f : H0 p P O) : Prop := ∀ y hy i hi, germ i y hy hi f ∈ nonZeroDivisors (Y.presheaf.stalk y)

theorem Regular.injective_mul {τ : H0 p P O} (hτ : Regular τ) (C : ProdChart P B N) :
    Function.Injective (C.mul τ) := by
  refine (injective_iff_map_eq_zero (C.mul τ)).2 fun f hf => ?_
  refine ext_germ fun y hy => ?_
  obtain ⟨t, ha, hb, hc⟩ := C.cover y
  refine ⟨C.b t, hb, ?_⟩
  have e := C.germ_mul τ f t y hy ha hb hc
  rw [hf, map_zero] at e
  rw [map_zero]
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff (hτ y hy (C.a t) ha)).1 e.symm

theorem Regular.exists_mul_eq {τ : H0 p P O} (hτ : Regular τ) (C : ProdChart P B N) (g : H0 p N O)
    (h : ∀ t y hy ha hc, y ∈ B.U (C.b t) → germ (C.a t) y hy ha τ ∣ germ (C.c t) y hy hc g) :
    ∃ f, C.mul τ f = g := by
  classical
  have key : ∀ y : O, ∃ (t : C.τ) (V : Y.Opens) (u : Γ(Y, V)) (_ : (y : Y) ∈ V)
      (hV : V ≤ O ⊓ (P.U (C.a t) ⊓ B.U (C.b t) ⊓ N.U (C.c t))),
      ∀ z (hz : z ∈ V), germ (C.c t) z (hV hz).1 (hV hz).2.2 g =
        germ (C.a t) z (hV hz).1 (hV hz).2.1.1 τ * ger z hz u := by
    rintro ⟨y, hy⟩
    obtain ⟨t, ha, hb, hc⟩ := C.cover y
    obtain ⟨q, hq⟩ := h t y hy ha hc hb
    obtain ⟨U, hyU, s, hs⟩ := Y.presheaf.germ_exist q
    let V0 : Y.Opens := (O ⊓ (P.U (C.a t) ⊓ B.U (C.b t) ⊓ N.U (C.c t))) ⊓ U
    have hy0 : y ∈ V0 := ⟨⟨hy, ⟨ha, hb⟩, hc⟩, hyU⟩
    have h1 : V0 ≤ O ⊓ N.U (C.c t) := fun z hz => ⟨hz.1.1, hz.1.2.2⟩
    have h2 : V0 ≤ O ⊓ P.U (C.a t) := fun z hz => ⟨hz.1.1, hz.1.2.1.1⟩
    have h3 : V0 ≤ U := fun z hz => hz.2
    let A : Γ(Y, V0) := resG Y h1 (g.loc (C.c t)) - resG Y h2 (τ.loc (C.a t)) * resG Y h3 s
    have gA : ∀ z (hz : z ∈ V0), ger z hz A = germ (C.c t) z (h1 hz).1 (h1 hz).2 g -
        germ (C.a t) z (h2 hz).1 (h2 hz).2 τ * ger z (h3 hz) s := by
      intro z hz
      simp only [A, map_sub, map_mul, ger_resG, germ_apply]
    have hA : ger y hy0 A = ger y hy0 0 := by
      rw [gA, map_zero, hq]
      have : ger y (h3 hy0) s = q := hs
      rw [this, sub_self]
    obtain ⟨V1, hyV1, i1, i2, hV1⟩ := Y.presheaf.germ_eq y hy0 hy0 A 0 hA
    have hle : V1 ≤ V0 := i1.le
    refine ⟨t, V1, resG Y (hle.trans h3) s, hyV1, fun z hz => (hle hz).1, fun z hz => ?_⟩
    have e0 : ger z (hle hz) A = 0 := by
      have e1 : ger z hz (Y.presheaf.map i1.op A) = ger z hz (Y.presheaf.map i2.op 0) := congrArg _ hV1
      rw [map_zero] at e1
      erw [ger_resG] at e1
      simpa using e1
    rw [gA, sub_eq_zero] at e0
    rw [e0, ger_resG]
  choose t V u hyV hV hu using key
  obtain ⟨f, hf⟩ := exists_of_germs (p := p) (O := O) C.isLB₂ V (fun s => C.b (t s))
    (fun s _ hz => (hV s hz).1) (fun s _ hz => (hV s hz).2.1.2) (fun y hy => ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩) u
    (fun z s s' h h' => by
      have hn := hτ z (hV s h).1 (C.a (t s)) (hV s h).2.1.1
      have E1 := germ_change (p := p) (C.c (t s)) (C.c (t s')) z (hV s h).1 (hV s h).2.2 (hV s' h').2.2 g
      have E2 := germ_change (p := p) (C.a (t s)) (C.a (t s')) z (hV s h).1 (hV s h).2.1.1 (hV s' h').2.1.1 τ
      have R := congrArg Units.val (C.rule z (t s) (t s') ⟨(hV s h).2.1.1, (hV s h).2.1.2, (hV s h).2.2⟩
        ⟨(hV s' h').2.1.1, (hV s' h').2.1.2, (hV s' h').2.2⟩)
      rw [Units.val_mul] at R
      have h1 := hu s z h
      have h2 := hu s' z h'
      have key : germ (C.a (t s)) z (hV s h).1 (hV s h).2.1.1 τ *
          (ger z h (u s) - (tr B z (C.b (t s)) (C.b (t s')) : Y.presheaf.stalk z) * ger z h' (u s')) = 0 := by
        linear_combination (-1 : Y.presheaf.stalk z) * h1 + E1 + (tr N z (C.c (t s)) (C.c (t s')) : Y.presheaf.stalk z) * h2 +
          (germ (C.a (t s')) z (hV s' h').1 (hV s' h').2.1.1 τ * ger z h' (u s')) * R -
          ((tr B z (C.b (t s)) (C.b (t s')) : Y.presheaf.stalk z) * ger z h' (u s')) * E2
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hn).1 key))
  refine ⟨f, C.sec_ext fun t' y hy ha hb hc => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : O, s = ⟨y, hy⟩ := ⟨_, rfl⟩
  have hz : y ∈ V s := hs ▸ hyV ⟨y, hy⟩
  have E1 := germ_change (p := p) (C.c t') (C.c (t s)) y hy hc (hV s hz).2.2 g
  have E2 := germ_change (p := p) (C.a t') (C.a (t s)) y hy ha (hV s hz).2.1.1 τ
  have E3 := germ_change (p := p) (C.b t') (C.b (t s)) y hy hb (hV s hz).2.1.2 f
  have E4 := hf s y hz
  have R := congrArg Units.val (C.rule y t' (t s) ⟨ha, hb, hc⟩ ⟨(hV s hz).2.1.1, (hV s hz).2.1.2, (hV s hz).2.2⟩)
  rw [Units.val_mul] at R
  have h1 := hu s y hz
  rw [C.germ_mul _ _ t' y hy ha hb hc]
  linear_combination germ (C.b t') y hy hb f * E2 +
    ((tr P y (C.a t') (C.a (t s)) : Y.presheaf.stalk y) * germ (C.a (t s)) y (hV s hz).1 (hV s hz).2.1.1 τ) * E3 +
    ((tr P y (C.a t') (C.a (t s)) : Y.presheaf.stalk y) * germ (C.a (t s)) y (hV s hz).1 (hV s hz).2.1.1 τ *
      (tr B y (C.b t') (C.b (t s)) : Y.presheaf.stalk y)) * E4 - E1 -
    (tr N y (C.c t') (C.c (t s)) : Y.presheaf.stalk y) * h1 -
    (germ (C.a (t s)) y (hV s hz).1 (hV s hz).2.1.1 τ * ger y hz (u s)) * R

theorem restr_injective_of_dense [IsReduced Y] (h : O' ≤ O) (hd : Dense (O' : Set Y)) :
    Function.Injective (restr h : H0 p B O → H0 p B O') := by
  have ext : ∀ f g : H0 p B O, (∀ i, f.loc i = g.loc i) → f = g := fun f g e => Subtype.ext (funext e)
  have ext2 : ∀ f g : H0 p B O, (∀ i z (hz : z ∈ O) (hi : z ∈ B.U i), germ i z hz hi f = germ i z hz hi g) → f = g :=
    fun f g e => ext f g fun i => fun_ext_ger fun z hz =>
      (germ_apply i z hz.1 hz.2 f).symm.trans ((e i z hz.1 hz.2).trans (germ_apply i z hz.1 hz.2 g))
  refine (injective_iff_map_eq_zero (restr h : H0 p B O →ₗ[k] H0 p B O')).2 fun f hf => ext2 f 0 fun i => ?_
  have h0 : f.loc i = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨w, hw1, hw2⟩ := hd.inter_open_nonempty _ (Y.basicOpen (f.loc i)).isOpen ⟨x, hx⟩
    have hwW : w ∈ O ⊓ B.U i := Y.basicOpen_le _ hw1
    have hu : IsUnit (ger w hwW (f.loc i)) := (Y.mem_basicOpen (f.loc i) w hwW).1 hw1
    have e : ger w hwW (f.loc i) = 0 :=
      (germ_apply i w hwW.1 hwW.2 f).symm.trans ((germ_restr h i w hw2 hwW.2 f).symm.trans (by rw [hf, map_zero]))
    exact (not_isUnit_zero (e ▸ hu)).elim
  intro z hz hi
  rw [map_zero, germ_apply, h0, map_zero]

def IsoOver (r : T ⟶ Y) (O : Y.Opens) : Prop := ∀ V ≤ O, IsIso (r.app V)

theorem isoOver_of_isOpenImmersion (r : T ⟶ Y) [IsOpenImmersion r] (h : O ≤ r.opensRange) : IsoOver r O := by
  intro V hV
  exact r.isIso_app V (hV.trans h)

theorem isoOver_of_isIso (r : T ⟶ Y) [IsIso (r ∣_ O)] : IsoOver r O := by
  intro V hV
  have hι : ∀ W : T.Opens, W ≤ r ⁻¹ᵁ O → IsIso ((r ⁻¹ᵁ O).ι.app W) := fun W hW =>
    (r ⁻¹ᵁ O).ι.isIso_app W (by rwa [Scheme.Opens.opensRange_ι])
  have hc : IsIso (((r ⁻¹ᵁ O).ι ≫ r).app V) := by
    rw [← morphismRestrict_ι]
    exact isoOver_of_isOpenImmersion _ (by rwa [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]) V le_rfl
  rw [Scheme.Hom.comp_app] at hc
  have h2 := hι (r ⁻¹ᵁ V) (r.preimage_mono hV)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 hc

theorem IsoOver.bijective {r : T ⟶ Y} (h : IsoOver r O) {V : Y.Opens} (hV : V ≤ O) {W : T.Opens}
    (e : W ≤ r ⁻¹ᵁ V) (e' : r ⁻¹ᵁ V ≤ W) : Function.Bijective (r.appLE V W e).hom := by
  obtain rfl := le_antisymm e e'
  have := h V hV
  rw [← Scheme.Hom.app_eq_appLE]
  exact (asIso (r.app V)).commRingCatIsoToRingEquiv.bijective

def pIdx (B : LB Y) (r : T ⟶ Y) (i : B.ι) : (B.pull r).ι := fun _ => i

theorem mem_pIdx {r : T ⟶ Y} {i : B.ι} {z : T} : z ∈ (B.pull r).U (pIdx B r i) ↔ r z ∈ B.U i := by
  exact mem_pull

theorem IsoOver.bijective_pull {r : T ⟶ Y} (h : IsoOver r O) (hB : B.IsLB) {W : T.Opens} (e : W ≤ r ⁻¹ᵁ O)
    (e' : r ⁻¹ᵁ O ≤ W) : Function.Bijective (H0.pull (p := p) (B := B) r e) := by
  obtain rfl := le_antisymm e e'
  have extY : ∀ f g : H0 p B O, (∀ i, f.loc i = g.loc i) → f = g := fun f g hfg => Subtype.ext (funext hfg)
  have extT : ∀ f g : H0 (r ≫ p) (B.pull r) (r ⁻¹ᵁ O), (∀ i, f.loc i = g.loc i) → f = g :=
    fun f g hfg => Subtype.ext (funext hfg)
  have hle : ∀ i : B.ι, r ⁻¹ᵁ O ⊓ (B.pull r).U (pIdx B r i) ≤ r ⁻¹ᵁ (O ⊓ B.U i) :=
    fun i z hz => ⟨hz.1, mem_pIdx.1 hz.2⟩
  have hge : ∀ i : B.ι, r ⁻¹ᵁ (O ⊓ B.U i) ≤ r ⁻¹ᵁ O ⊓ (B.pull r).U (pIdx B r i) :=
    fun i z hz => ⟨hz.1, mem_pIdx.2 hz.2⟩
  have bij : ∀ i : B.ι, Function.Bijective (r.appLE (O ⊓ B.U i) _ (hle i)).hom := fun i =>
    h.bijective inf_le_left (hle i) (hge i)
  have hloc : ∀ (f : H0 p B O) (i : B.ι), (H0.pull r e f).loc (pIdx B r i) =
      (r.appLE (O ⊓ B.U i) _ (hle i)).hom (f.loc i) := by
    intro f i
    refine fun_ext_ger fun z hz => ?_
    rw [ger_appLE]
    refine (germ_apply (pIdx B r i) z hz.1 hz.2 (H0.pull r e f)).symm.trans ?_
    refine (germ_pull r e (pIdx B r i) z hz.1 hz.2 f).trans ?_
    exact congrArg _ (germ_apply i (r z) _ _ f)
  refine ⟨fun f g hfg => extY f g fun i => (bij i).1 ?_, fun g => ?_⟩
  · rw [← hloc, ← hloc, hfg]
  choose a ha using fun i => (bij i).2 (g.loc (pIdx B r i))
  have hg : ∀ (i : B.ι) (z : T) (hz : z ∈ r ⁻¹ᵁ O) (hzi : z ∈ (B.pull r).U (pIdx B r i)),
      (r.stalkMap z).hom (ger (r z) (show r z ∈ O ⊓ B.U i from ⟨hz, mem_pIdx.1 hzi⟩) (a i)) =
        germ (pIdx B r i) z hz hzi g := by
    intro i z hz hzi
    refine (ger_appLE r (hle i) z ⟨hz, hzi⟩ (a i)).symm.trans ?_
    rw [ha i]
    exact (germ_apply _ _ _ _ g).symm
  obtain ⟨f, hf⟩ := exists_of_germs (p := p) (O := O) hB (fun i => O ⊓ B.U i) id (fun _ => inf_le_left)
    (fun _ => inf_le_right) (fun y hy => (exists_chart hB y).imp fun _ hi => ⟨hy, hi⟩) a
    (fun y i i' hy hy' => by
      let V2 : Y.Opens := O ⊓ B.U i ⊓ B.U i'
      have l1 : V2 ≤ O ⊓ B.U i := fun x hx => hx.1
      have l2 : V2 ≤ B.U i ⊓ B.U i' := fun x hx => ⟨hx.1.2, hx.2⟩
      have l3 : V2 ≤ O ⊓ B.U i' := fun x hx => ⟨hx.1.1, hx.2⟩
      let F : Γ(Y, V2) := resG Y l1 (a i) - resG Y l2 (B.g i i').val * resG Y l3 (a i')
      have gF : ∀ x (hx : x ∈ V2), ger x hx F =
          ger x (l1 hx) (a i) - ger x (l2 hx) (B.g i i').val * ger x (l3 hx) (a i') := by
        intro x hx
        simp only [F, map_sub, map_mul, ger_resG]
      have hF : F = 0 := by
        apply (h.bijective (V := V2) (fun x hx => hx.1.1) le_rfl le_rfl).1
        rw [map_zero]
        refine fun_ext_ger fun z hz => ?_
        rw [ger_appLE, map_zero]
        refine (congrArg (r.stalkMap z).hom (gF (r z) hz)).trans ?_
        rw [map_sub, map_mul]
        have hz1 : z ∈ r ⁻¹ᵁ O := hz.1.1
        have hzi : z ∈ (B.pull r).U (pIdx B r i) := mem_pIdx.2 hz.1.2
        have hzi' : z ∈ (B.pull r).U (pIdx B r i') := mem_pIdx.2 hz.2
        have E1 := hg i z hz1 hzi
        have E2 := hg i' z hz1 hzi'
        have E3 := germ_change (p := r ≫ p) (pIdx B r i) (pIdx B r i') z hz1 hzi hzi' g
        have E6 : ((tr (B.pull r) z (pIdx B r i) (pIdx B r i') : T.presheaf.stalk z)) =
            (r.stalkMap z).hom (ger (r z) (l2 hz) (B.g i i').val) := by
          have E4 := congrArg Units.val (tr_pull B r z hzi hzi')
          rw [Units.coe_map] at E4
          rw [E4]
          exact congrArg (fun x => (r.stalkMap z).hom x) (val_tr B (r z) (l2 hz))
        linear_combination E1 + E3 + germ (pIdx B r i') z hz1 hzi' g * E6 -
          (r.stalkMap z).hom (ger (r z) (l2 hz) (B.g i i').val) * E2
      have e0 := gF y ⟨hy, hy'.2⟩
      rw [hF, map_zero] at e0
      show ger y hy (a i) = (tr B y i i' : Y.presheaf.stalk y) * ger y hy' (a i')
      rw [val_tr B y (l2 ⟨hy, hy'.2⟩)]
      exact (sub_eq_zero.1 e0.symm))
  have hfa : ∀ i, f.loc i = a i := fun i => fun_ext_ger fun y hy =>
    (germ_apply i y hy.1 hy.2 f).symm.trans (hf i y hy)
  refine ⟨f, extT _ _ fun j => ?_⟩
  show (H0.pull r e f).loc (pIdx B r (j PUnit.unit)) = g.loc (pIdx B r (j PUnit.unit))
  rw [hloc, hfa, ha]

def toSec (f : H0 p B ⊤) : B.Sec := (Equiv.ofBijective _ (bijective_ofSec_top (p := p) (B := B))).symm f

@[simp] theorem ofSec_toSec (f : H0 p B ⊤) : ofSec p ⊤ (toSec f) = f := by
  exact (Equiv.ofBijective _ (bijective_ofSec_top (p := p) (B := B))).apply_symm_apply f

theorem ofSec_toSec' (O : Y.Opens) (f : H0 p B ⊤) : ofSec p O (toSec f) = restr le_top f := by
  rw [← restr_ofSec (le_top : O ≤ ⊤), ofSec_toSec]

theorem ger_toSec (f : H0 p B ⊤) (i : B.ι) (y : Y) (hi : y ∈ B.U i) :
    ger y hi ((toSec f).f i) = germ i y (memTop y) hi f := by
  rw [← germ_ofSec (p := p) i y (memTop y) hi, ofSec_toSec]

theorem ger_secToPow (t : P.Sec) (n : ℕ) (i : P.ι) (y : Y) (hi : y ∈ P.U i) (h : y ∈ (lbZPow P n).U fun _ => i) :
    ger y h ((secToPow t n).f fun _ => i) = ger y hi (t.f i) ^ n := by
  show ger y h (powFn (secToPow t n) fun _ => i) = _
  rw [secToPow, powFn_powSecMk]
  erw [ger_resG]
  exact map_pow _ _ _

end Division

structure Common {Λ : Type} [AddCommGroup Λ] (B : Λ → LB Y) where

  isLB : ∀ a, (B a).IsLB

  J : Type

  U : J → Y.Opens

  cover : ∀ y, ∃ j, y ∈ U j

  idx : ∀ a, J → (B a).ι

  mem : ∀ a j y, y ∈ (B a).U (idx a j) ↔ y ∈ U j

  add : ∀ a b y j j', y ∈ U j → y ∈ U j' → tr (B (a + b)) y (idx _ j) (idx _ j') =
    tr (B a) y (idx _ j) (idx _ j') * tr (B b) y (idx _ j) (idx _ j')

namespace Common

variable {Λ Λ' : Type} [AddCommGroup Λ] [AddCommGroup Λ'] {B : Λ → LB Y} (C : Common B)

abbrev θ (a : Λ) (y : Y) (j j' : C.J) : (Y.presheaf.stalk y)ˣ := tr (B a) y (C.idx a j) (C.idx a j')

theorem nsmul (a : Λ) (n : ℕ) {y : Y} {j j' : C.J} (h : y ∈ C.U j) (h' : y ∈ C.U j') :
    C.θ (n • a) y j j' = C.θ a y j j' ^ n := by
  induction n with
  | zero =>
    have e := C.add 0 0 y j j' h h'
    rw [add_zero] at e
    rw [zero_nsmul, pow_zero]
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  | succ n ih =>
    rw [succ_nsmul, pow_succ, ← ih]
    exact C.add (n • a) a y j j' h h'

def pull (r : T ⟶ Y) : Common fun a => (B a).pull r where
  isLB a := LB.isLB_pull (C.isLB a) r
  J := C.J
  U j := r ⁻¹ᵁ C.U j
  cover z := C.cover (r z)
  idx a j := pIdx (B a) r (C.idx a j)
  mem a j z := mem_pIdx.trans (C.mem a j (r z))
  add a b z j j' h h' := by
    rw [tr_pull _ r z (mem_pIdx.2 ((C.mem _ _ _).2 h)) (mem_pIdx.2 ((C.mem _ _ _).2 h')),
      tr_pull _ r z (mem_pIdx.2 ((C.mem _ _ _).2 h)) (mem_pIdx.2 ((C.mem _ _ _).2 h')),
      tr_pull _ r z (mem_pIdx.2 ((C.mem _ _ _).2 h)) (mem_pIdx.2 ((C.mem _ _ _).2 h')), ← map_mul]
    exact congrArg _ (C.add a b (r z) j j' h h')

def comap (f : Λ' → Λ) (hf : ∀ a b, f (a + b) = f a + f b) : Common fun a => B (f a) where
  isLB a := C.isLB (f a)
  J := C.J
  U := C.U
  cover := C.cover
  idx a := C.idx (f a)
  mem a := C.mem (f a)
  add a b y j j' h h' := (congrArg (fun x => C.θ x y j j') (hf a b)).trans (C.add _ _ y j j' h h')

def powers {L : LB Y} (hL : L.IsLB) : Common (lbZPow L) where
  isLB := Twist.isLB_lbZPow hL
  J := L.ι
  U := L.U
  cover := exists_chart hL
  idx _ j _ := j
  mem _ _ _ := mem_zpow_U
  add a b y j j' h h' := by
    rw [tr_zpow L _ y (mem_zpow_U.2 h) (mem_zpow_U.2 h'), tr_zpow L _ y (mem_zpow_U.2 h) (mem_zpow_U.2 h'),
      tr_zpow L _ y (mem_zpow_U.2 h) (mem_zpow_U.2 h'), zpow_add]

abbrev addChart {a b s : Λ} (h : a + b = s) : ProdChart (B a) (B b) (B s) where
  isLB₁ := C.isLB a
  isLB₂ := C.isLB b
  isLB₃ := C.isLB s
  τ := C.J
  a := C.idx a
  b := C.idx b
  c := C.idx s
  cover y := (C.cover y).imp fun _ hj => ⟨(C.mem _ _ _).2 hj, (C.mem _ _ _).2 hj, (C.mem _ _ _).2 hj⟩
  rule y j j' e e' := h ▸ C.add a b y j j' ((C.mem _ _ _).1 e.1) ((C.mem _ _ _).1 e'.1)

variable {K P P₂ : LB Y}

abbrev canChart (hK : K.IsLB) {a b s : Λ} (h : a + b = s) : ProdChart (LB.div K (B a)) (B s) (tens K (B b)) where
  isLB₁ := LB.isLB_div hK (C.isLB a)
  isLB₂ := C.isLB s
  isLB₃ := isLB_tens hK (C.isLB b)
  τ := K.ι × C.J
  a t := (t.1, C.idx a t.2)
  b t := C.idx s t.2
  c t := (t.1, C.idx b t.2)
  cover y := let ⟨i, hi⟩ := exists_chart hK y; let ⟨j, hj⟩ := C.cover y
    ⟨(i, j), ⟨hi, (C.mem _ _ _).2 hj⟩, (C.mem _ _ _).2 hj, hi, (C.mem _ _ _).2 hj⟩
  rule y t t' e e' := by
    subst h
    rw [tr_tens K _ y e.2.2 e'.2.2, tr_div K _ y e.1 e'.1,
      C.add a b y t.2 t'.2 ((C.mem _ _ _).1 e.2.1) ((C.mem _ _ _).1 e'.2.1), mul_assoc, inv_mul_cancel_left]

abbrev poleChart (hK : K.IsLB) (hP : P.IsLB) {a b s : Λ} {n : ℕ} (h : b + n • a = s) :
    ProdChart (lbZPow P n) (tw (tens K (B b)) (LB.div (B a) P) n) (tens K (B s)) where
  isLB₁ := Twist.isLB_lbZPow hP n
  isLB₂ := isLB_tw (isLB_tens hK (C.isLB b)) (LB.isLB_div (C.isLB a) hP) n
  isLB₃ := isLB_tens hK (C.isLB s)
  τ := K.ι × C.J × P.ι
  a t _ := t.2.2
  b t := twIdx (M := tens K (B b)) (L := LB.div (B a) P) n (t.1, C.idx b t.2.1) (C.idx a t.2.1, t.2.2)
  c t := (t.1, C.idx s t.2.1)
  cover y := let ⟨i, hi⟩ := exists_chart hK y; let ⟨j, hj⟩ := C.cover y; let ⟨m, hm⟩ := exists_chart hP y
    ⟨(i, j, m), mem_zpow_U.2 hm, mem_tw_U.2 ⟨⟨hi, (C.mem _ _ _).2 hj⟩, (C.mem _ _ _).2 hj, hm⟩,
      hi, (C.mem _ _ _).2 hj⟩
  rule y t t' e e' := by
    subst h
    have h₁ := (C.mem _ _ _).1 e.2.2.2
    have h₂ := (C.mem _ _ _).1 e'.2.2.2
    have := C.nsmul a n h₁ h₂
    rw [tr_tens K _ y e.2.2 e'.2.2, tr_tw y e.2.1 e'.2.1, tr_zpow P n y e.1 e'.1,
      tr_tens K _ y (mem_tw_U.1 e.2.1).1 (mem_tw_U.1 e'.2.1).1,
      tr_div _ P y (mem_tw_U.1 e.2.1).2 (mem_tw_U.1 e'.2.1).2, C.add _ _ y _ _ h₁ h₂]
    rw [θ] at this
    rw [this, zpow_natCast, zpow_natCast, mul_pow, inv_pow, mul_left_comm (_ ^ n), mul_left_comm (_ ^ n),
      mul_inv_cancel, mul_one, mul_assoc]

abbrev effChart (hP : P.IsLB) (hP₂ : P₂.IsLB) {a b s : Λ} {n : ℕ} (h : b + n • a = s) :
    ProdChart P₂ (lbZPow P n) (LB.div (B s) (tw (LB.div (B b) P₂) (LB.div (B a) P) n)) where
  isLB₁ := hP₂
  isLB₂ := Twist.isLB_lbZPow hP n
  isLB₃ := LB.isLB_div (C.isLB s) (isLB_tw (LB.isLB_div (C.isLB b) hP₂) (LB.isLB_div (C.isLB a) hP) n)
  τ := P₂.ι × C.J × P.ι
  a t := t.1
  b t _ := t.2.2
  c t := (C.idx s t.2.1,
    twIdx (M := LB.div (B b) P₂) (L := LB.div (B a) P) n (C.idx b t.2.1, t.1) (C.idx a t.2.1, t.2.2))
  cover y := let ⟨i, hi⟩ := exists_chart hP₂ y; let ⟨j, hj⟩ := C.cover y; let ⟨m, hm⟩ := exists_chart hP y
    ⟨(i, j, m), hi, mem_zpow_U.2 hm, (C.mem _ _ _).2 hj,
      mem_tw_U.2 ⟨⟨(C.mem _ _ _).2 hj, hi⟩, (C.mem _ _ _).2 hj, hm⟩⟩
  rule y t t' e e' := by
    subst h
    have h₁ := (C.mem _ _ _).1 e.2.2.1
    have h₂ := (C.mem _ _ _).1 e'.2.2.1
    have := C.nsmul a n h₁ h₂
    rw [tr_div _ _ y e.2.2 e'.2.2, tr_tw y e.2.2.2 e'.2.2.2, tr_zpow P n y e.2.1 e'.2.1,
      tr_div _ P₂ y (mem_tw_U.1 e.2.2.2).1 (mem_tw_U.1 e'.2.2.2).1,
      tr_div _ P y (mem_tw_U.1 e.2.2.2).2 (mem_tw_U.1 e'.2.2.2).2, C.add _ _ y _ _ h₁ h₂]
    rw [θ] at this
    rw [this, zpow_natCast, zpow_natCast, mul_pow, inv_pow, mul_mul_mul_comm (tr (B b) y _ _), mul_inv,
      mul_inv_cancel_left, mul_inv, inv_inv, inv_inv]

end Common

abbrev divChart {B P : LB Y} (hB : B.IsLB) (hP : P.IsLB) : ProdChart P (LB.div B P) B where
  isLB₁ := hP
  isLB₂ := LB.isLB_div hB hP
  isLB₃ := hB
  τ := B.ι × P.ι
  a t := t.2
  b t := t
  c t := t.1
  cover y := let ⟨i, hi⟩ := exists_chart hB y; let ⟨j, hj⟩ := exists_chart hP y
    ⟨(i, j), hj, ⟨hi, hj⟩, hi⟩
  rule y _ _ e e' := by rw [tr_div B P y e.2.1 e'.2.1, mul_left_comm, mul_inv_cancel, mul_one]

section Base

variable {p : Y ⟶ Sp k} {B : LB Y} (hB : B.IsLB)

theorem ideal_ext_stalk {I I' : Y.IdealSheafData} (h : ∀ y, stalkId I y = stalkId I' y) : I = I' := by
  ext U a
  rw [mem_ideal_iff_ger I U a, mem_ideal_iff_ger I' U a]
  simp only [h]

def baseIdeal (W : Submodule k (H0 p B ⊤)) : Y.IdealSheafData := cutIdeal hB fun s : W => toSec s.1

theorem stalkId_baseIdeal (W : Submodule k (H0 p B ⊤)) (i : B.ι) (y : Y) (hi : y ∈ B.U i) :
    stalkId (baseIdeal hB W) y = Ideal.span (Set.range fun s : W => germ i y (memTop y) hi s.1) := by
  rw [baseIdeal, stalkId_cutIdeal hB _ i y hi]
  congr 2
  funext s
  exact ger_toSec s.1 i y hi

theorem mem_support_baseIdeal (W : Submodule k (H0 p B ⊤)) (y : Y) :
    y ∈ (baseIdeal hB W).support ↔ ∀ s ∈ W, y ∉ nonzeroLocus (toSec s) := by
  rw [baseIdeal, mem_support_cutIdeal]
  exact ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s.1 s.2⟩

theorem baseIdeal_span {ι : Type} (v : ι → B.Sec) :
    baseIdeal hB (Submodule.span k (Set.range fun i => ofSec p ⊤ (v i))) = cutIdeal hB v := by
  refine ideal_ext_stalk fun y => ?_
  obtain ⟨j, hj⟩ := exists_chart hB y
  rw [stalkId_baseIdeal hB _ j y hj, stalkId_cutIdeal hB v j y hj]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨⟨s, hs⟩, rfl⟩
    show germ j y (memTop y) hj s ∈ _
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Ideal.subset_span ⟨i, (germ_ofSec j y (memTop y) hj (v i)).symm⟩
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Ideal.add_mem _ ha hb
    | smul c a _ ha => rw [germ_smul]; exact Ideal.mul_mem_left _ _ ha
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨⟨ofSec p ⊤ (v i), Submodule.subset_span ⟨i, rfl⟩⟩, germ_ofSec j y (memTop y) hj (v i)⟩

theorem stalkId_comap_baseIdeal (W : Submodule k (H0 p B ⊤)) (r : T ⟶ Y) (j : (B.pull r).ι) (z : T)
    (hj : z ∈ (B.pull r).U j) : stalkId ((baseIdeal hB W).comap r) z =
      Ideal.span (Set.range fun s : W => germ j z (memTop z) hj (H0.pull r le_top s.1)) := by
  have e := eq_comap_of_stalk (I := baseIdeal hB W) (I' := cutIdeal (LB.isLB_pull hB r) fun s : W => secPull (toSec s.1) r)
    (φ := r) (fun z => stalkId_cutIdeal_secPull hB _ z)
  rw [← e, stalkId_cutIdeal _ _ j z hj]
  congr 2
  funext s
  refine (secGer_chartSec (chartPullPull B r) (fun s : W => toSec s.1) j z hj s).trans ?_
  refine Eq.trans ?_ (germ_pull r le_top j z (memTop z) hj s.1).symm
  congr 1
  exact ger_toSec s.1 _ _ _

structure Cartier (I : Y.IdealSheafData) where

  P : LB Y

  isLB : P.IsLB

  t : P.Sec

  reg : ∀ i y hi, ger y hi (t.f i) ∈ nonZeroDivisors (Y.presheaf.stalk y)

  cut : cutIdeal isLB (fun _ : Unit => t) = I

namespace Cartier

def ofSec [IsIntegral Y] {P : LB Y} (hP : P.IsLB) (t : P.Sec) {y₀ : Y} (ht : y₀ ∈ nonzeroLocus t) :
    Cartier (cutIdeal hP fun _ : Unit => t) where
  P := P
  isLB := hP
  t := t
  reg i y hi := mem_nonZeroDivisors_of_ne_zero fun e => by
    have h₀ : t.f i = 0 := germ_injective_of_isIntegral Y y hi (e.trans (map_zero _).symm)
    obtain ⟨z, hz, hz'⟩ := nonempty_preirreducible_inter (P.U i).isOpen (nonzeroLocus t).isOpen ⟨y, hi⟩ ⟨y₀, ht⟩
    have := (isUnit_ger_iff t hz).2 hz'
    rw [h₀, map_zero] at this
    exact not_isUnit_zero this
  cut := rfl

variable {I : Y.IdealSheafData} (Δ : Cartier I)

theorem stalkId_eq (i : Δ.P.ι) (y : Y) (hi : y ∈ Δ.P.U i) : stalkId I y = Ideal.span {ger y hi (Δ.t.f i)} := by
  have e := stalkId_cutIdeal Δ.isLB (fun _ : Unit => Δ.t) i y hi
  rw [Δ.cut] at e
  rw [e]
  exact congrArg Ideal.span Set.range_const

theorem mem_nonzeroLocus (y : Y) : y ∈ nonzeroLocus Δ.t ↔ y ∉ I.support := by
  have e := mem_support_cutIdeal Δ.isLB (fun _ : Unit => Δ.t) y
  rw [Δ.cut] at e
  rw [e]
  simp

theorem regular (p : Y ⟶ Sp k) (O : Y.Opens) : Regular (H0.ofSec p O Δ.t) := by
  intro y hy i hi
  rw [germ_ofSec]
  exact Δ.reg i y hi

def pow (n : ℕ) : (lbZPow Δ.P n).Sec := secToPow Δ.t n

theorem germ_pow (p : Y ⟶ Sp k) {O : Y.Opens} (n : ℕ) (i : Δ.P.ι) (y : Y) (hy : y ∈ O) (hi : y ∈ Δ.P.U i)
    (h : y ∈ (lbZPow Δ.P n).U fun _ => i) :
    germ (fun _ => i) y hy h (H0.ofSec p O (Δ.pow n)) = ger y hi (Δ.t.f i) ^ n := by
  have e := germ_ofSec (p := p) (O := O) (B := lbZPow Δ.P n) (fun _ => i) y hy h (Δ.pow n)
  exact e.trans (ger_secToPow Δ.t n i y hi h)

theorem nowhereZero_pow (p : Y ⟶ Sp k) {O : Y.Opens} (hO : ∀ y ∈ O, y ∉ I.support) (n : ℕ) :
    NowhereZero (H0.ofSec p O (Δ.pow n)) := by
  intro y hy j hj
  have hi : y ∈ Δ.P.U (j PUnit.unit) := (mem_zpow_U (j := j PUnit.unit)).1 hj
  have e := Δ.germ_pow p n (j PUnit.unit) y hy hi hj
  have u := ((isUnit_ger_iff Δ.t hi).2 ((Δ.mem_nonzeroLocus y).2 (hO y hy))).pow n
  rw [← e] at u
  exact u

end Cartier

variable {hB} {W : Submodule k (H0 p B ⊤)} {r : T ⟶ Y} (Δ : Cartier ((baseIdeal hB W).comap r))

namespace Cartier

abbrev moving : LB T := LB.div (B.pull r) Δ.P

theorem isLB_moving : Δ.moving.IsLB := by
  exact LB.isLB_div (LB.isLB_pull hB r) Δ.isLB

def incl (O : T.Opens) : H0 (r ≫ p) Δ.moving O →ₗ[k] H0 (r ≫ p) (B.pull r) O :=
  (divChart (LB.isLB_pull hB r) Δ.isLB).mul (H0.ofSec _ O Δ.t)

theorem incl_injective (O : T.Opens) : Function.Injective (Δ.incl O) := by
  exact Regular.injective_mul (Δ.regular _ O) _

theorem pull_mem_range (w : W) : H0.pull r le_top w.1 ∈ LinearMap.range (Δ.incl ⊤) := by
  obtain ⟨f, hf⟩ := Regular.exists_mul_eq (Δ.regular _ ⊤) (divChart (LB.isLB_pull hB r) Δ.isLB) (H0.pull r le_top w.1)
    (fun t' z hz ha hc _ => by
      rw [germ_ofSec, ← Ideal.mem_span_singleton, ← Δ.stalkId_eq t'.2 z ha, stalkId_comap_baseIdeal hB W r t'.1 z hc]
      exact Ideal.subset_span ⟨w, rfl⟩)
  exact ⟨f, hf⟩

def lift : W →ₗ[k] H0 (r ≫ p) Δ.moving ⊤ :=
  (LinearEquiv.ofInjective _ (Δ.incl_injective ⊤)).symm.toLinearMap ∘ₗ
    (H0.pull r le_top ∘ₗ W.subtype).codRestrict _ Δ.pull_mem_range

theorem incl_lift (w : W) : Δ.incl ⊤ (Δ.lift w) = H0.pull r le_top w.1 := by
  show Δ.incl ⊤ ((LinearEquiv.ofInjective _ (Δ.incl_injective ⊤)).symm ⟨H0.pull r le_top w.1, Δ.pull_mem_range w⟩) = _
  exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (Δ.incl_injective ⊤)).apply_symm_apply ⟨H0.pull r le_top w.1, Δ.pull_mem_range w⟩)

theorem germ_lift (w : W) (j : Δ.moving.ι) (z : T) (hj : z ∈ Δ.moving.U j) :
    ger z hj.2 (Δ.t.f j.2) * germ j z (memTop z) hj (Δ.lift w) =
      germ j.1 z (memTop z) hj.1 (H0.pull r le_top w.1) := by
  rw [← germ_ofSec (p := r ≫ p) j.2 z (memTop z) hj.2, ← Δ.incl_lift w]
  exact ((divChart (LB.isLB_pull hB r) Δ.isLB).germ_mul _ _ j z (memTop z) hj.2 hj hj.1).symm

theorem iSup_nonzeroLocus {ι : Type} {v : ι → W} (hv : Submodule.span k (Set.range v) = ⊤) :
    ⨆ i, nonzeroLocus (toSec (Δ.lift (v i))) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  rw [Opens.mem_iSup]
  obtain ⟨j, hj⟩ := exists_chart Δ.isLB_moving z
  have hG : ∀ w : W, ger z hj.2 (Δ.t.f j.2) * germ j z (memTop z) hj (Δ.lift w) =
      germ j.1 z (memTop z) hj.1 (H0.pull r le_top w.1) := fun w => Δ.germ_lift w j z hj
  let J : Ideal (T.presheaf.stalk z) := Ideal.span (Set.range fun i => germ j z (memTop z) hj (Δ.lift (v i)))
  have hJ : ∀ w : W, germ j z (memTop z) hj (Δ.lift w) ∈ J := by
    intro w
    have hw : w ∈ Submodule.span k (Set.range v) := by rw [hv]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Ideal.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero, map_zero]; exact J.zero_mem
    | add a b _ _ ha hb => rw [map_add, map_add]; exact J.add_mem ha hb
    | smul c a _ ha => rw [map_smul, germ_smul]; exact J.mul_mem_left _ ha
  have hT : ger z hj.2 (Δ.t.f j.2) ∈
      Ideal.span (Set.range fun s : W => germ j.1 z (memTop z) hj.1 (H0.pull r le_top s.1)) := by
    rw [← stalkId_comap_baseIdeal hB W r j.1 z hj.1, Δ.stalkId_eq j.2 z hj.2]
    exact Ideal.mem_span_singleton_self _
  have hsub : Ideal.span (Set.range fun s : W => germ j.1 z (memTop z) hj.1 (H0.pull r le_top s.1)) ≤
      Ideal.span {ger z hj.2 (Δ.t.f j.2)} * J := by
    rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    show germ j.1 z (memTop z) hj.1 (H0.pull r le_top s.1) ∈ _
    rw [← hG s]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (hJ s)
  obtain ⟨x, hx, hx'⟩ := Ideal.mem_span_singleton_mul.1 (hsub hT)
  have hn := Δ.reg j.2 z hj.2
  have h1 : x = 1 := by
    have e : ger z hj.2 (Δ.t.f j.2) * (x - 1) = 0 := by rw [mul_sub, hx', mul_one, sub_self]
    exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hn).1 e)
  have htop : J = ⊤ := (Ideal.eq_top_iff_one _).2 (h1 ▸ hx)
  by_contra hne
  push_neg at hne
  have hle : J ≤ IsLocalRing.maximalIdeal _ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hne i
    rw [← isUnit_ger_iff _ hj, ger_toSec]
    exact hu
  rw [htop] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)

end Cartier

end Base

structure Modif (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ) where

  X : Scheme.{0}

  σ : X ⟶ Y

  smooth : SmoothOfRelativeDimension D (σ ≫ p)

  proj : IsProjOver (σ ≫ p)

  iso : IsIso (σ ∣_ U)

  dense : Dense ((σ ⁻¹ᵁ U : X.Opens) : Set X)

namespace Modif

variable {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}

def refl (hs : SmoothOfRelativeDimension D p) (hp : IsProjOver p) (hd : Dense (U : Set Y)) : Modif p U D where
  X := Y
  σ := 𝟙 Y
  smooth := by rwa [Category.id_comp]
  proj := by rwa [Category.id_comp]
  iso := inferInstance
  dense := hd

variable (M : Modif p U D)

abbrev str : M.X ⟶ Sp k := M.σ ≫ p

abbrev opn : M.X.Opens := M.σ ⁻¹ᵁ U

instance : SmoothOfRelativeDimension D M.str := M.smooth

theorem bijective_pull {B : LB Y} (hB : B.IsLB) :
    Function.Bijective (H0.pull (p := p) (B := B) M.σ (le_refl M.opn)) := by
  have := M.iso
  exact (isoOver_of_isIso M.σ).bijective_pull hB (le_refl _) (le_refl _)

theorem existsUnique_lift {S : Scheme.{0}} (x : S ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ U) : ∃! z : S ⟶ M.X, z ≫ M.σ = x := by
  have hr : Set.range x.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hx (show s ∈ (⊤ : S.Opens) from trivial)
  let x' := IsOpenImmersion.lift U.ι x hr
  have hx' : x' ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  have := M.iso
  refine ⟨x' ≫ inv (M.σ ∣_ U) ≫ M.opn.ι, ?_, fun z hz => ?_⟩
  · show (x' ≫ inv (M.σ ∣_ U) ≫ M.opn.ι) ≫ M.σ = x
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hx']
  · have hz : z ≫ M.σ = x := hz
    have hr' : Set.range z.base ⊆ Set.range M.opn.ι.base := by
      rintro _ ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι]
      have h1 : x.base s ∈ U := hx (show s ∈ (⊤ : S.Opens) from trivial)
      rw [← hz] at h1
      exact h1
    let z' := IsOpenImmersion.lift M.opn.ι z hr'
    have hz' : z' ≫ M.opn.ι = z := IsOpenImmersion.lift_fac _ _ _
    have e : z' ≫ (M.σ ∣_ U) = x' := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hz', hz, hx']
    rw [← hz', ← e, Category.assoc, IsIso.hom_inv_id_assoc]

def trans (M' : Modif M.str M.opn D) : Modif p U D where
  X := M'.X
  σ := M'.σ ≫ M.σ
  smooth := by rw [Category.assoc]; exact M'.smooth
  proj := by rw [Category.assoc]; exact M'.proj
  iso := by
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ M'.iso M.iso
  dense := M'.dense

end Modif

example : ∃ (W : Submodule ℚ (H0 (PSpace.str ℚ 1) (ProjSpace.O1 ℚ 1) ⊤))
    (M : Modif (PSpace.str ℚ 1) (ProjSpace.chart ℚ 1 1) 1)
    (Δ : Cartier ((baseIdeal (ProjSpace.O1_isLB ℚ 1) W).comap M.σ)), nonzeroLocus Δ.t = M.opn ∧ M.opn ≠ ⊤ := by
  have hv := Adelic.projSys.isVariety ℚ 1 le_rfl
  have : IsIntegral (PSpace ℚ 1) := hv.isIntegral
  have hg := Adelic.projSys.gen_mem ℚ 1 1
  have e := ProjSpace.nonzeroLocus_coord ℚ 1 1
  let M := Modif.refl hv.smooth hv.proj ((ProjSpace.chart ℚ 1 1).isOpen.dense ⟨_, hg⟩)
  let Δ := Cartier.ofSec (ProjSpace.O1_isLB ℚ 1) (ProjSpace.coord ℚ 1 1) (e.ge hg)
  exact ⟨_, M, { Δ with cut := (baseIdeal_span _ _).symm.trans (Scheme.IdealSheafData.comap_id _).symm }, e,
    fun h => AmpleModel.coord_ne_top ℚ (e.trans h)⟩

end GlobalTheory.CompHS
