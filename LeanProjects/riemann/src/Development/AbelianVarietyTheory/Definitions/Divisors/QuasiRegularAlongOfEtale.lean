import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map mem_support_iff_stalkId)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open GlobalTheory.TopForm (le_preimage_inf)
open GlobalTheory.Adelic (cutIdeal ideal_cutIdeal mem_support_cutIdeal)
open H0

variable {k : Type} [CommRing k] {Y T : Scheme.{0}}

section Fil

variable {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens} {I : Y.IdealSheafData} {a b : ℕ}

variable (I a) in

def VanishesTo (f : H0 p B O) : Prop :=
  ∀ y ∈ I.support, ∀ hy i hi, germ i y hy hi f ∈ stalkId I y ^ a

theorem vanishesTo_iff_forall {f : H0 p B O} :
    VanishesTo I a f ↔ ∀ y hy i hi, germ i y hy hi f ∈ stalkId I y ^ a := by
  refine ⟨fun h y hy i hi => ?_, fun h y _ => h y⟩
  by_cases hs : y ∈ I.support
  · exact h y hs hy i hi
  · rw [stalkId_eq_top I hs, Ideal.top_pow]
    trivial

theorem vanishesTo_of_exists {f : H0 p B O} (h : ∀ y ∈ I.support, ∀ hy : y ∈ O,
    ∃ i hi, germ i y hy hi f ∈ stalkId I y ^ a) : VanishesTo I a f := fun y hs hy j hj => by
  obtain ⟨i, hi, e⟩ := h y hs hy
  rw [germ_change j i y hy hj hi]
  exact Ideal.mul_mem_left _ _ e

theorem vanishesTo_iff_affine {f : H0 p B O} : VanishesTo I a f ↔
    ∀ (W : Y.affineOpens) (i : B.ι) (h : W.1 ≤ O ⊓ B.U i), resG Y h (f.loc i) ∈ I.ideal W ^ a := by
  refine ⟨fun hf W i h => (mem_ideal_iff_ger (I ^ a) W _).2 fun y hy => ?_,
    fun hf y _ hy i hi => ?_⟩
  · rw [stalkId_pow, ger_resG]
    exact vanishesTo_iff_forall.1 hf y (h hy).1 i (h hy).2
  · obtain ⟨W, hW, h⟩ := exists_affine (memInf hy hi)
    have := (mem_ideal_iff_ger (I ^ a) W _).1 (hf W i h) y hW
    rwa [stalkId_pow, ger_resG] at this

theorem vanishesTo_zero (f : H0 p B O) : VanishesTo I 0 f := fun _ _ _ _ _ => by simp

theorem VanishesTo.mono {f : H0 p B O} (h : VanishesTo I b f) (e : a ≤ b) : VanishesTo I a f :=
  fun y hs hy i hi => Ideal.pow_le_pow_right e (h y hs hy i hi)

theorem VanishesTo.restr {f : H0 p B O} (h : VanishesTo I a f) (e : O' ≤ O) :
    VanishesTo I a (restr e f) := fun y hs hy i hi => by
  rw [germ_restr]
  exact h y hs _ i hi

theorem VanishesTo.mul {P N : LB Y} (C : ProdChart P B N) {σ : H0 p P O} {f : H0 p B O}
    (hσ : VanishesTo I a σ) (hf : VanishesTo I b f) : VanishesTo I (a + b) (C.mul σ f) :=
  vanishesTo_of_exists fun y hs hy => by
    obtain ⟨t, ha, hb, hc⟩ := C.cover y
    refine ⟨_, hc, ?_⟩
    rw [C.germ_mul σ f t y hy ha hb hc, pow_add]
    exact Ideal.mul_mem_mul (hσ y hs hy _ ha) (hf y hs hy _ hb)

variable (I O) in

def SuppIn : Prop := ∀ y ∈ I.support, y ∈ O

theorem suppIn_top : SuppIn ⊤ I := fun _ _ => trivial

theorem SuppIn.le (h : SuppIn O I) : ⊤ ≤ I.subschemeι ⁻¹ᵁ O := fun z _ => h _ (ι_mem_support I z)

theorem vanishesTo_restr_iff (h : SuppIn O' I) (e : O' ≤ O) {f : H0 p B O} :
    VanishesTo I a (restr e f) ↔ VanishesTo I a f :=
  ⟨fun hf y hs _ i hi => germ_restr e i y (h y hs) hi f ▸ hf y hs (h y hs) i hi, (·.restr e)⟩

variable (p B O I a) in

def filTop : Submodule k (H0 p B O) where
  carrier := {f | VanishesTo I a f}
  zero_mem' y _ hy i hi := by rw [map_zero]; exact zero_mem _
  add_mem' hf hg y hs hy i hi := by
    rw [map_add]; exact add_mem (hf y hs hy i hi) (hg y hs hy i hi)
  smul_mem' c f hf y hs hy i hi := by
    rw [germ_smul]; exact Ideal.mul_mem_left _ _ (hf y hs hy i hi)

@[simp] theorem mem_filTop {f : H0 p B O} : f ∈ filTop p B O I a ↔ VanishesTo I a f := Iff.rfl

variable (I a) in

def Fil (V : Submodule k (H0 p B O)) : Submodule k (H0 p B O) := V ⊓ filTop p B O I a

variable {V V' : Submodule k (H0 p B O)}

@[simp] theorem mem_Fil {f : H0 p B O} : f ∈ Fil I a V ↔ f ∈ V ∧ VanishesTo I a f := Iff.rfl

theorem Fil_le : Fil I a V ≤ V := inf_le_left

theorem Fil_le_filTop : Fil I a V ≤ filTop p B O I a := inf_le_right

@[simp] theorem Fil_top : Fil I a (⊤ : Submodule k (H0 p B O)) = filTop p B O I a := top_inf_eq _

@[simp] theorem Fil_zero : Fil I 0 V = V := inf_eq_left.2 fun f _ => vanishesTo_zero f

theorem Fil_anti (e : a ≤ b) : Fil I b V ≤ Fil I a V := fun _ h => ⟨h.1, VanishesTo.mono h.2 e⟩

variable (I a V) in

abbrev gr : Type := Fil I a V ⧸ (Fil I (a + 1) V).submoduleOf (Fil I a V)

variable (p I B) in

abbrev sectionsOnClosedSubscheme : Type := H0 (I.subschemeι ≫ p) (B.pull I.subschemeι) ⊤

def resTo (h : SuppIn O I) : H0 p B O →ₗ[k] sectionsOnClosedSubscheme p B I := H0.pull I.subschemeι h.le

theorem germ_resTo (h : SuppIn O I) (j : (B.pull I.subschemeι).ι) (z : I.subscheme)
    (hj : z ∈ (B.pull I.subschemeι).U j) (f : H0 p B O) : germ j z (Opens.mem_top z) hj (resTo h f) =
      (I.subschemeι.stalkMap z).hom
        (germ (j PUnit.unit) _ (h _ (ι_mem_support I z)) (mem_pull.1 hj) f) :=
  germ_pull _ _ j z _ hj f

@[simp] theorem resTo_restr (h : SuppIn O' I) (e : O' ≤ O) (f : H0 p B O) :
    resTo h (restr e f) = resTo (fun y hy => e (h y hy)) f := pull_restr _ e _ f

theorem resTo_mul {P N : LB Y} (C : ProdChart P B N) (h : SuppIn O I) (σ : H0 p P O)
    (f : H0 p B O) : resTo h (C.mul σ f) = (C.pull I.subschemeι).mul (resTo h σ) (resTo h f) :=
  C.pull_mul _ _ σ f

theorem resTo_eq_zero_iff (h : SuppIn O I) {f : H0 p B O} : resTo h f = 0 ↔ VanishesTo I 1 f := by
  refine ⟨fun e y hs hy i hi => ?_, fun hf => LB.sec_ext fun j => fun_ext_ger fun z hz => ?_⟩
  · obtain ⟨z, rfl⟩ := exists_ι_eq hs
    rw [pow_one, ← ker_stalkMap]
    exact (germ_resTo h (fun _ => i) z (mem_pull.2 hi) f).symm.trans (by rw [e, map_zero])
  · have := hf _ (ι_mem_support I z) (h _ (ι_mem_support I z)) _ (mem_pull.1 hz.2)
    rw [pow_one, ← ker_stalkMap] at this
    exact ((germ_resTo h j z hz.2 f).trans this).trans (map_zero (germ j z (Opens.mem_top z) hz.2)).symm

variable (p I) in

def secOn (σ : LB.Sec B) : sectionsOnClosedSubscheme p B I := resTo suppIn_top (H0.ofSec p ⊤ σ)

@[simp] theorem resTo_ofSec (h : SuppIn O I) (σ : LB.Sec B) :
    resTo h (H0.ofSec p O σ) = secOn p I σ := by
  rw [← restr_ofSec (le_top : O ≤ ⊤), resTo_restr, secOn]

theorem germ_secOn (j : (B.pull I.subschemeι).ι) (z : I.subscheme)
    (hj : z ∈ (B.pull I.subschemeι).U j) (σ : LB.Sec B) : germ j z (Opens.mem_top z) hj (secOn p I σ) =
      (I.subschemeι.stalkMap z).hom (ger _ (mem_pull.1 hj) (σ.f (j PUnit.unit))) :=
  (germ_resTo _ j z hj _).trans (congrArg _ (germ_ofSec _ _ _ _ σ))

theorem nowhereZero_secOn {σ : LB.Sec B} (h : SuppIn (nonzeroLocus σ) I) :
    NowhereZero (secOn p I σ) := nowhereZero_pull_ofSec σ _ _ h.le

section Val

variable {R : Type} [CommRing R]

def valOn (x : Sp R ⟶ I.subscheme) (i : B.ι) (hi : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ B.U i) :
    sectionsOnClosedSubscheme p B I →+ R :=
  val x (fun _ => i) le_top fun z hz => mem_pull.2 (hi hz)

theorem valOn_resTo (h : SuppIn O I) (x : Sp R ⟶ I.subscheme) (i : B.ι)
    (hi : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ B.U i) (hO : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ O) (f : H0 p B O) :
    valOn x i hi (resTo h f) = val (x ≫ I.subschemeι) i hO hi f :=
  val_pull _ _ x _ _ _ hO hi f

theorem valOn_secOn (x : Sp R ⟶ I.subscheme) (i : B.ι)
    (hi : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ B.U i) (σ : LB.Sec B) :
    valOn x i hi (secOn p I σ) = evalPt (x ≫ I.subschemeι) _ hi (σ.f i) :=
  (valOn_resTo _ x i hi le_top _).trans (val_ofSec _ _ _ _ σ)

theorem valOn_mul {P N : LB Y} (C : ProdChart P B N) (σ : sectionsOnClosedSubscheme p P I) (f : sectionsOnClosedSubscheme p B I) (t : C.τ)
    (x : Sp R ⟶ I.subscheme) (ha : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ P.U (C.a t))
    (hb : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ B.U (C.b t)) (hc : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ N.U (C.c t)) :
    valOn x (C.c t) hc ((C.pull I.subschemeι).mul σ f) =
      valOn x (C.a t) ha σ * valOn x (C.b t) hb f :=
  (C.pull I.subschemeι).val_mul σ f t x _ _ _ _

end Val

end Fil

section Mul

variable {p : Y ⟶ Sp k} {L M : LB Y} (hM : M.IsLB) (hL : L.IsLB) {O : Y.Opens}
  {I : Y.IdealSheafData} {n l : ℤ} {a b : ℕ} {ι : Type}

def mulSec (w : L.Sec) (h : n + 1 = l) : H0 p (tw M L n) O →ₗ[k] H0 p (tw M L l) O :=
  (oneChart hM hL h).mul (H0.ofSec p O w)

def mulSecOn (w : L.Sec) (h : n + 1 = l) : sectionsOnClosedSubscheme p (tw M L n) I →ₗ[k] sectionsOnClosedSubscheme p (tw M L l) I :=
  ((oneChart hM hL h).pull I.subschemeι).mul (secOn p I w)

theorem germ_mulSec (w : L.Sec) (h : n + 1 = l) (f : H0 p (tw M L n) O) (i : M.ι) (j : L.ι) (y : Y)
    (hy : y ∈ O) (hi : y ∈ M.U i) (hj : y ∈ L.U j) :
    germ (twIdx l i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) (mulSec hM hL w h f) =
      ger y hj (w.f j) * germ (twIdx n i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) f :=
  ((oneChart hM hL h).germ_mul _ f (i, j) y hy hj _ _).trans
    (congrArg (· * _) (germ_ofSec _ _ _ _ w))

theorem resTo_mulSec (hO : SuppIn O I) (w : L.Sec) (h : n + 1 = l) (f : H0 p (tw M L n) O) :
    resTo hO (mulSec hM hL w h f) = mulSecOn hM hL w h (resTo hO f) := by
  rw [mulSec, resTo_mul, resTo_ofSec, mulSecOn]

theorem valOn_mulSecOn {R : Type} [CommRing R] (w : L.Sec) (h : n + 1 = l) (g : sectionsOnClosedSubscheme p (tw M L n) I)
    (x : Sp R ⟶ I.subscheme) (i : M.ι) (j : L.ι) (hj : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ L.U j)
    (h₁ : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ (tw M L n).U (twIdx n i j))
    (h₂ : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ (tw M L l).U (twIdx l i j)) :
    valOn x (twIdx l i j) h₂ (mulSecOn hM hL w h g) =
      evalPt (x ≫ I.subschemeι) _ hj (w.f j) * valOn x (twIdx n i j) h₁ g :=
  (valOn_mul (oneChart hM hL h) _ g (i, j) x hj h₁ h₂).trans
    (congrArg (· * _) (valOn_secOn x j hj w))

theorem monoVal_const {R : Type*} [CommMonoid R] (c : R) (α : MonoDeg ι a) :
    monoVal (fun _ => c) α.1 = c ^ a :=
  (Finset.prod_pow_eq_pow_sum _ _ _).trans (congrArg (c ^ ·) α.2)

def monoSec (s : ι → L.Sec) (α : MonoDeg ι a) : (lbZPow L a).Sec :=
  Twist.zmkGlobal (fun j => monoVal (fun i => (s i).f j) α.1) fun j j' => by
    rw [map_monoVal, map_monoVal, zpow_natCast, Units.val_pow_eq_pow_val, ← monoVal_const _ α,
      ← monoVal_mul]
    exact congrArg (monoVal · α.1) (funext fun i => (s i).compat j j')

theorem zfun_monoSec (s : ι → L.Sec) (α : MonoDeg ι a) (j : L.ι) :
    Twist.zfun (monoSec s α) j = monoVal (fun i => (s i).f j) α.1 := Twist.zfun_zmkGlobal _ _ j

def mulMono (s : ι → L.Sec) (α : MonoDeg ι a) (h : n + a = l) :
    H0 p (tw M L n) O →ₗ[k] H0 p (tw M L l) O :=
  (powChart hM hL h).mul (H0.ofSec p O (monoSec s α))

theorem germ_mulMono (s : ι → L.Sec) (α : MonoDeg ι a) (h : n + a = l) (m : H0 p (tw M L n) O)
    (i : M.ι) (j : L.ι) (y : Y) (hy : y ∈ O) (hi : y ∈ M.U i) (hj : y ∈ L.U j) :
    germ (twIdx l i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) (mulMono hM hL s α h m) =
      monoVal (secGer s j y hj) α.1 * germ (twIdx n i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) m := by
  refine ((powChart hM hL h).germ_mul _ m (i, j) y hy (mem_zpow_U.2 hj) _ _).trans
    (congrArg (· * _) ((germ_ofSec _ _ _ _ _).trans ?_))
  refine (congrArg _ (Twist.f_eq_zfun (monoSec s α) fun _ => j)).trans ((ger_resG _ _ _ _).trans ?_)
  exact (congrArg _ (zfun_monoSec s α j)).trans (map_monoVal _ _ _)

theorem tw_ext (hM : M.IsLB) (hL : L.IsLB) {f g : H0 p (tw M L n) O}
    (h : ∀ i j y hy (hi : y ∈ M.U i) (hj : y ∈ L.U j),
      germ (twIdx n i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) f =
        germ (twIdx n i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) g) : f = g :=
  ext_germ fun y hy => let ⟨i, hi⟩ := exists_chart hM y; let ⟨j, hj⟩ := exists_chart hL y
    ⟨_, _, h i j y hy hi hj⟩

theorem mulMono_succ (s : ι → L.Sec) (α : MonoDeg ι a) (β : MonoDeg ι (a + 1)) (i : ι)
    (e : β.1 = α.1 + Finsupp.single i 1) {l' : ℤ} (h : n + a = l) (h' : l + 1 = l')
    (h'' : n + (a + 1 : ℕ) = l') (m : H0 p (tw M L n) O) :
    mulMono hM hL s β h'' m = mulSec hM hL (s i) h' (mulMono hM hL s α h m) :=
  tw_ext hM hL fun c j y hy hc hj => by
    rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hj, germ_mulSec _ _ _ _ _ _ _ _ _ hc hj,
      germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hj, e, monoVal_add, monoVal_single, pow_one]
    ring

theorem mulMono_zero (s : ι → L.Sec) (α : MonoDeg ι 0) (h : n + (0 : ℕ) = n)
    (m : H0 p (tw M L n) O) : mulMono hM hL s α h m = m :=
  tw_ext hM hL fun c j y hy hc hj => by
    rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hj, (Finsupp.degree_eq_zero_iff _).1 α.2, monoVal_zero,
      one_mul]

theorem VanishesTo.mulMono (s : ι → L.Sec) (α : MonoDeg ι a) (h : n + a = l) {m : H0 p (tw M L n) O}
    (hm : VanishesTo (cutIdeal hL s) b m) :
    VanishesTo (cutIdeal hL s) (a + b) (mulMono hM hL s α h m) :=
  vanishesTo_of_exists fun y hs hy => by
    obtain ⟨i, hi⟩ := exists_chart hM y
    obtain ⟨j, hj⟩ := exists_chart hL y
    refine ⟨twIdx l i j, mem_tw_U.2 ⟨hi, hj⟩, ?_⟩
    rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hi hj, pow_add]
    exact Ideal.mul_mem_mul (stalkId_cutIdeal hL s j y hj ▸ monoVal_mem_pow _ α) (hm y hs hy _ _)

theorem vanishesTo_mulMono (s : ι → L.Sec) (α : MonoDeg ι a) (h : n + a = l)
    (m : H0 p (tw M L n) O) : VanishesTo (cutIdeal hL s) a (mulMono hM hL s α h m) :=
  (vanishesTo_zero m).mulMono hM hL s α h

theorem zone_f (j : (lbZPow L 0).ι) : (Twist.zone L).f j = 1 := by
  rw [Twist.f_eq_zfun, Twist.zfun_zone, map_one]

theorem nonzeroLocus_zone : nonzeroLocus (Twist.zone L) = ⨆ j, L.U j := by
  refine le_antisymm (fun y hy => ?_) (iSup_le fun j y hj => ?_)
  · obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact Opens.mem_iSup.2 ⟨_, Twist.zpow_U_le j hj⟩
  · exact (isUnit_ger_iff (i := fun _ => j) _ (mem_zpow_U.2 hj)).1
      (zone_f (L := L) _ ▸ isUnit_one.map _)

def toTwZero : H0 p M O ≃ₗ[k] H0 p (tw M L 0) O :=
  (baseChart hM hL 0).mulEquiv (σ := H0.ofSec p O (Twist.zone L)) fun y hy i hi => by
    rw [germ_ofSec, isUnit_ger_iff, nonzeroLocus_zone, hL.cover]
    trivial

def toTwZeroOn : sectionsOnClosedSubscheme p M I ≃ₗ[k] sectionsOnClosedSubscheme p (tw M L 0) I :=
  ((baseChart hM hL 0).pull I.subschemeι).mulEquiv (σ := secOn p I (Twist.zone L))
    (nowhereZero_secOn fun y _ => by rw [nonzeroLocus_zone, hL.cover]; trivial)

end Mul

section Alg

variable {R S : Type*} [CommRing R] [CommRing S] {ι : Type} [Finite ι] {φ : R →+* S} {x : ι → R}
  {a : ℕ} {f f' : R} {γ γ' : MonoDeg ι a → S}

variable (φ x f γ) in

def LeadAt : Prop := ∃ m : MonoDeg ι a → R, (∀ α, φ (m α) = γ α) ∧
  f - ∑ α, monoVal x α.1 * m α ∈ Ideal.span (Set.range x) ^ (a + 1)

theorem leadAt_sum (m : MonoDeg ι a → R) : LeadAt φ x (∑ α, monoVal x α.1 * m α) fun α => φ (m α) :=
  ⟨m, fun _ => rfl, by rw [sub_self]; exact zero_mem _⟩

theorem LeadAt.add (h : LeadAt φ x f γ) (h' : LeadAt φ x f' γ') : LeadAt φ x (f + f') (γ + γ') := by
  obtain ⟨m, e, hm⟩ := h
  obtain ⟨m', e', hm'⟩ := h'
  refine ⟨m + m', fun α => by simp [e, e'], ?_⟩
  simpa only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_sub_add_comm] using add_mem hm hm'

theorem LeadAt.mul (h : LeadAt φ x f γ) (r : R) : LeadAt φ x (r * f) fun α => φ r * γ α := by
  obtain ⟨m, e, hm⟩ := h
  refine ⟨fun α => r * m α, fun α => by simp [e], ?_⟩
  simpa only [mul_sub, Finset.mul_sum, mul_left_comm] using Ideal.mul_mem_left _ r hm

theorem LeadAt.unit_mul (h : LeadAt φ x f γ) (u : Rˣ) :
    LeadAt φ (fun i => u * x i) (u ^ a * f) γ := by
  obtain ⟨m, e, hm⟩ := h
  have hI : Ideal.span (Set.range x) ≤ Ideal.span (Set.range fun i => u * x i) :=
    Ideal.span_le.2 (Set.range_subset_iff.2 fun i =>
      (Ideal.unit_mul_mem_iff_mem _ u.isUnit).1 (Ideal.subset_span ⟨i, rfl⟩))
  refine ⟨m, e, Ideal.pow_right_mono hI _ ?_⟩
  simpa only [monoVal_mul, monoVal_const, mul_sub, Finset.mul_sum, mul_assoc] using
    Ideal.mul_mem_left _ (u.val ^ a) hm

theorem leadAt_zero_iff (hφ : RingHom.ker φ ≤ Ideal.span (Set.range x)) :
    LeadAt φ x f (0 : MonoDeg ι a → S) ↔ f ∈ Ideal.span (Set.range x) ^ (a + 1) := by
  refine ⟨fun ⟨m, e, hm⟩ => (Submodule.sub_mem_iff_left _ (sum_mem fun α _ => ?_)).1 hm,
    fun h => ⟨0, fun _ => map_zero φ, by simpa using h⟩⟩
  rw [pow_succ]
  exact Ideal.mul_mem_mul (monoVal_mem_pow x α) (hφ (e α))

theorem LeadAt.unique (hq : IsQuasiRegularSeq R x) (hφ : Ideal.span (Set.range x) ≤ RingHom.ker φ)
    (h : LeadAt φ x f γ) (h' : LeadAt φ x f γ') : γ = γ' := by
  obtain ⟨m, e, hm⟩ := h
  obtain ⟨m', e', hm'⟩ := h'
  funext α
  have := hq a (m - m') (by
    simpa only [smul_eq_mul, Ideal.mul_top, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
      sub_sub_sub_cancel_left] using sub_mem hm' hm) α
  rw [smul_eq_mul, Ideal.mul_top] at this
  rw [← e, ← e', ← sub_eq_zero, ← map_sub]
  exact hφ this

end Alg

section Lead

variable {p : Y ⟶ Sp k} {L M : LB Y} (hL : L.IsLB) {ι : Type} [Finite ι] (s : ι → L.Sec)
  {O : Y.Opens} (hO : SuppIn O (cutIdeal hL s)) {n l : ℤ} {a : ℕ} (h : n + a = l)

abbrev LeadIn (f : H0 p (tw M L l) O) (c : MonoDeg ι a → sectionsOnClosedSubscheme p (tw M L n) (cutIdeal hL s))
    (z : (cutIdeal hL s).subscheme) (i : M.ι) (j : L.ι)
    (hi : (cutIdeal hL s).subschemeι z ∈ M.U i) (hj : (cutIdeal hL s).subschemeι z ∈ L.U j) : Prop :=
  LeadAt ((cutIdeal hL s).subschemeι.stalkMap z).hom (secGer s j _ hj)
    (germ (twIdx l i j) _ (hO _ (ι_mem_support _ z)) (mem_tw_U.2 ⟨hi, hj⟩) f)
    fun α => germ (fun _ => twIdx n i j) z (Opens.mem_top z)
      (mem_pull.2 (mem_tw_U.2 ⟨hi, hj⟩)) (c α)

def HasLead (_h : n + a = l) (f : H0 p (tw M L l) O)
    (c : MonoDeg ι a → sectionsOnClosedSubscheme p (tw M L n) (cutIdeal hL s)) : Prop :=
  ∀ z i j hi hj, LeadIn hL s hO f c z i j hi hj

variable {hL s hO h} {f f' : H0 p (tw M L l) O}
  {c c' : MonoDeg ι a → sectionsOnClosedSubscheme p (tw M L n) (cutIdeal hL s)}

theorem leadAt_change (h : n + a = l) {S : Type*} [CommRing S] {y : Y}
    {φ : Y.presheaf.stalk y →+* S} (hy : y ∈ O) {i i' : M.ι} {j j' : L.ι} (hi : y ∈ M.U i)
    (hj : y ∈ L.U j) (hi' : y ∈ M.U i') (hj' : y ∈ L.U j') {γ : MonoDeg ι a → S}
    (e : LeadAt φ (secGer s j' y hj') (germ (twIdx l i' j') y hy (mem_tw_U.2 ⟨hi', hj'⟩) f) γ) :
    LeadAt φ (secGer s j y hj) (germ (twIdx l i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) f)
      fun α => φ (tr (tw M L n) y (twIdx n i j) (twIdx n i' j')).val * γ α := by
  have e₁ := (e.mul (tr (tw M L n) y (twIdx n i j) (twIdx n i' j')).val).unit_mul (tr L y j j')
  rw [← funext (secGer_change s j j' y hj hj')] at e₁
  rw [germ_change _ (twIdx l i' j') y hy _ (mem_tw_U.2 ⟨hi', hj'⟩)]
  convert e₁ using 1
  rw [tr_tw y (mem_tw_U.2 ⟨hi, hj⟩) (mem_tw_U.2 ⟨hi', hj'⟩),
    tr_tw y (mem_tw_U.2 ⟨hi, hj⟩) (mem_tw_U.2 ⟨hi', hj'⟩),
    show tr L y j j' ^ l = tr L y j j' ^ n * tr L y j j' ^ a by rw [← h, zpow_add, zpow_natCast]]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  ring

theorem hasLead_of_exists (e : ∀ z, ∃ i j hi hj, LeadIn hL s hO f c z i j hi hj) :
    HasLead hL s hO h f c := fun z i j hi hj => by
  obtain ⟨i', j', hi', hj', e⟩ := e z
  refine (congrArg (LeadAt _ _ _) (funext fun α => ?_)).mp (leadAt_change h _ hi hj hi' hj' e)
  have e₁ := mem_pull (J := fun _ => twIdx n i j).2 (mem_tw_U.2 ⟨hi, hj⟩)
  have e₂ := mem_pull (J := fun _ => twIdx n i' j').2 (mem_tw_U.2 ⟨hi', hj'⟩)
  exact ((germ_change _ _ z _ e₁ e₂ (c α)).trans (by rw [tr_pull _ _ z e₁ e₂]; rfl)).symm

theorem HasLead.add (e : HasLead hL s hO h f c) (e' : HasLead hL s hO h f' c') :
    HasLead hL s hO h (f + f') (c + c') := fun z i j hi hj =>
  (congrArg₂ (LeadAt _ _) (map_add _ _ _).symm (funext fun _ => (map_add _ _ _).symm)).mp
    ((e z i j hi hj).add (e' z i j hi hj))

theorem HasLead.smul (e : HasLead hL s hO h f c) (r : k) : HasLead hL s hO h (r • f) (r • c) :=
  fun z i j hi hj => (congrArg₂ (LeadAt _ _) (germ_smul _ _ _ _ _ _).symm (funext fun _ =>
    (congrArg (· * _) (stalkMap_const _ z r)).trans (germ_smul _ _ _ _ _ _).symm)).mp
      ((e z i j hi hj).mul (const p _ r))

theorem hasLead_zero_iff (hM : M.IsLB) :
    HasLead hL s hO h f 0 ↔ VanishesTo (cutIdeal hL s) (a + 1) f := by
  have key (z i j hi hj) : LeadIn hL s hO f (0 : MonoDeg ι a → sectionsOnClosedSubscheme p (tw M L n) _) z i j hi hj ↔
      germ (twIdx l i j) _ (hO _ (ι_mem_support _ z)) (mem_tw_U.2 ⟨hi, hj⟩) f ∈
        stalkId (cutIdeal hL s) _ ^ (a + 1) := by
    rw [stalkId_cutIdeal hL s j _ hj, ← leadAt_zero_iff
      ((ker_stalkMap _ z).trans (stalkId_cutIdeal hL s j _ hj)).le]
    exact iff_of_eq (congrArg (LeadAt _ _ _) (funext fun _ => map_zero _))
  refine ⟨fun e => vanishesTo_of_exists fun y hs _ => ?_,
    fun e z i j hi hj => (key z i j hi hj).2 (e _ (ι_mem_support _ z) _ _ _)⟩
  obtain ⟨z, rfl⟩ := exists_ι_eq hs
  obtain ⟨i, hi⟩ := exists_chart hM ((cutIdeal hL s).subschemeι z)
  obtain ⟨j, hj⟩ := exists_chart hL ((cutIdeal hL s).subschemeι z)
  exact ⟨twIdx l i j, _, (key z i j hi hj).1 (e z i j hi hj)⟩

variable (hL s hO h) in

theorem hasLead_sum (hM : M.IsLB) (m : MonoDeg ι a → H0 p (tw M L n) O) :
    HasLead hL s hO h (∑ α, mulMono hM hL s α h (m α)) fun α => resTo hO (m α) :=
  fun z i j hi hj => by
    simp only [LeadIn, map_sum, germ_mulMono hM hL s _ h _ i j _ _ hi hj]
    exact (congrArg (LeadAt _ _ _) (funext fun α =>
      (germ_resTo hO (fun _ => twIdx n i j) z _ (m α)).symm)).mp (leadAt_sum _)

variable (hL s) in

def QuasiRegularAlong : Prop :=
  ∀ y ∈ (cutIdeal hL s).support, ∀ j hj, IsQuasiRegularSeq (Y.presheaf.stalk y) (secGer s j y hj)

theorem HasLead.unique (hM : M.IsLB) (hq : QuasiRegularAlong hL s) (e : HasLead hL s hO h f c)
    (e' : HasLead hL s hO h f c') : c = c' := funext fun α => ext_germ fun z _ => by
  obtain ⟨i, hi⟩ := exists_chart hM ((cutIdeal hL s).subschemeι z)
  obtain ⟨j, hj⟩ := exists_chart hL ((cutIdeal hL s).subschemeι z)
  exact ⟨fun _ => twIdx n i j, _, congrFun (LeadAt.unique (hq _ (ι_mem_support _ z) j hj)
    ((ker_stalkMap _ z).trans (stalkId_cutIdeal hL s j _ hj)).ge (e z i j hi hj) (e' z i j hi hj)) α⟩

variable (hO h) in

theorem exists_hasLead (hM : M.IsLB) (hq : QuasiRegularAlong hL s)
    (hf : VanishesTo (cutIdeal hL s) a f) : ∃ c, HasLead hL s hO h f c := by
  let τ := {t : Y.affineOpens × M.ι × L.ι // t.1.1 ≤ O ⊓ (tw M L l).U (twIdx l t.2.1 t.2.2)}
  have hi (t : τ) : t.1.1.1 ≤ M.U t.1.2.1 := fun y hy => (mem_tw_U.1 (t.2 hy).2).1
  have hj (t : τ) : t.1.1.1 ≤ L.U t.1.2.2 := fun y hy => (mem_tw_U.1 (t.2 hy).2).2
  have ex (t : τ) : ∃ μ : MonoDeg ι a → Γ(Y, t.1.1.1),
      ∑ α, monoVal (fun i => resG Y (hj t) ((s i).f _)) α.1 • μ α = resG Y t.2 (f.loc _) := by
    rw [← mem_pow_smul_top_iff, ← ideal_cutIdeal hL s, smul_eq_mul, Ideal.mul_top]
    exact vanishesTo_iff_affine.1 hf _ _ t.2
  choose μ hμ using ex
  have key (t : τ) (z) (hz : (cutIdeal hL s).subschemeι z ∈ t.1.1.1) :
      LeadAt ((cutIdeal hL s).subschemeι.stalkMap z).hom (secGer s _ _ (hj t hz))
        (germ (twIdx l _ _) _ (t.2 hz).1 (mem_tw_U.2 ⟨hi t hz, hj t hz⟩) f) fun α =>
          ((cutIdeal hL s).subschemeι.stalkMap z).hom (ger _ hz (μ t α)) := by
    have e := congrArg (ger _ hz) (hμ t)
    simp only [map_sum, smul_eq_mul, map_mul, map_monoVal, ger_resG] at e
    exact (congrArg (LeadAt _ _ · _) e).mp (leadAt_sum _)
  have cover (z : (cutIdeal hL s).subscheme) : ∃ t : τ, (cutIdeal hL s).subschemeι z ∈ t.1.1.1 := by
    obtain ⟨i, hi⟩ := exists_chart hM ((cutIdeal hL s).subschemeι z)
    obtain ⟨j, hj⟩ := exists_chart hL ((cutIdeal hL s).subschemeι z)
    obtain ⟨W, hW, e⟩ := exists_affine
      (memInf (hO _ (ι_mem_support _ z)) ((mem_tw_U (n := l)).2 ⟨hi, hj⟩))
    exact ⟨⟨(W, i, j), e⟩, hW⟩
  have hc (t : τ) : (cutIdeal hL s).subschemeι ⁻¹ᵁ t.1.1.1 ≤
      ((tw M L n).pull (cutIdeal hL s).subschemeι).U fun _ => twIdx n t.1.2.1 t.1.2.2 :=
    fun z hz => mem_pull.2 (mem_tw_U.2 ⟨hi t hz, hj t hz⟩)
  choose c hc' using fun α => exists_of_germs (p := (cutIdeal hL s).subschemeι ≫ p) (O := ⊤)
    (LB.isLB_pull (isLB_tw hM hL n) _) (fun t : τ => (cutIdeal hL s).subschemeι ⁻¹ᵁ t.1.1.1)
    (fun t _ => twIdx n t.1.2.1 t.1.2.2) (fun _ => le_top) hc (fun z _ => cover z)
    (fun t => ((cutIdeal hL s).subschemeι.appLE _ _ le_rfl).hom (μ t α)) fun z t t' hz hz' => by
      rw [ger_appLE, ger_appLE, tr_pull _ _ z (hc t hz) (hc t' hz')]
      exact congrFun (LeadAt.unique (hq _ (ι_mem_support _ z) _ (hj t hz))
        ((ker_stalkMap _ z).trans (stalkId_cutIdeal hL s _ _ (hj t hz))).ge (key t z hz)
        (leadAt_change h _ (hi t hz) (hj t hz) (hi t' hz') (hj t' hz') (key t' z hz'))) α
  refine ⟨c, hasLead_of_exists fun z => ?_⟩
  obtain ⟨t, hz⟩ := cover z
  exact ⟨_, _, hi t hz, hj t hz, (congrArg (LeadAt _ _ _) (funext fun α =>
    ((hc' α t z hz).trans (ger_appLE _ _ _ _ _)).symm)).mp (key t z hz)⟩

variable (hO h) in

def lead (hM : M.IsLB) (hq : QuasiRegularAlong hL s) : filTop p (tw M L l) O (cutIdeal hL s) a →ₗ[k]
    (MonoDeg ι a → sectionsOnClosedSubscheme p (tw M L n) (cutIdeal hL s)) where
  toFun f := (exists_hasLead hO h hM hq f.2).choose
  map_add' f g := (exists_hasLead hO h hM hq (f + g).2).choose_spec.unique hM hq
    ((exists_hasLead hO h hM hq f.2).choose_spec.add (exists_hasLead hO h hM hq g.2).choose_spec)
  map_smul' r f := (exists_hasLead hO h hM hq (r • f).2).choose_spec.unique hM hq
    ((exists_hasLead hO h hM hq f.2).choose_spec.smul r)

theorem lead_eq_iff (hM : M.IsLB) (hq : QuasiRegularAlong hL s)
    (f : filTop p (tw M L l) O (cutIdeal hL s) a) :
    lead hO h hM hq f = c ↔ HasLead hL s hO h f.1 c :=
  ⟨fun e => e ▸ (exists_hasLead hO h hM hq f.2).choose_spec,
    (exists_hasLead hO h hM hq f.2).choose_spec.unique hM hq⟩

end Lead

section Symbol

variable {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) {L A B : LB Y}
  (hL : L.IsLB) (hA : A.IsLB) (hB : B.IsLB) (s : Fin D → L.Sec)

def dsOn : sectionsOnClosedSubscheme p (tw K.bundle L D) (cutIdeal hL s) :=
  H0.ofSec _ ⊤ (K.dSec s (cutIdeal hL s).subschemeι (vanishesAlong_cutIdeal hL s))

theorem germ_dsOn (z : (cutIdeal hL s).subscheme) (i : K.bundle.ι) (j : L.ι)
    (hi : (cutIdeal hL s).subschemeι z ∈ K.bundle.U i) (hj : (cutIdeal hL s).subschemeι z ∈ L.U j) :
    germ (fun _ => twIdx D i j) z (Opens.mem_top z) (mem_pull.2 (mem_tw_U.2 ⟨hi, hj⟩)) (dsOn K hL s) =
      ((cutIdeal hL s).subschemeι.stalkMap z).hom (ger _ (memInf hi hj) (K.jacFun s i j)) :=
  (germ_ofSec _ _ _ _ _).trans (ger_appLE _ _ z _ _)

theorem valOn_dsOn {R : Type} [CommRing R] (x : Sp R ⟶ (cutIdeal hL s).subscheme) (i : K.bundle.ι)
    (j : L.ι) (hi : ⊤ ≤ (x ≫ (cutIdeal hL s).subschemeι) ⁻¹ᵁ K.bundle.U i)
    (hj : ⊤ ≤ (x ≫ (cutIdeal hL s).subschemeι) ⁻¹ᵁ L.U j)
    (h : ⊤ ≤ (x ≫ (cutIdeal hL s).subschemeι) ⁻¹ᵁ (tw K.bundle L D).U (twIdx D i j)) :
    valOn x (twIdx D i j) h (dsOn K hL s) =
      K.jacVal s (x ≫ (cutIdeal hL s).subschemeι) i j hi hj := by
  have h' : ⊤ ≤ x ⁻¹ᵁ ((tw K.bundle L D).pull (cutIdeal hL s).subschemeι).U fun _ => twIdx D i j :=
    fun z hz => mem_pull.2 (h hz)
  refine (val_ofSec x _ _ h' _).trans ?_
  exact congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom (K.jacFun s i j))
    (Scheme.Hom.appLE_comp_appLE x _ _ _ ⊤ _ h')

variable (hS : Etale ((cutIdeal hL s).subschemeι ≫ p))

include hS in

theorem nowhereZero_dsOn : NowhereZero (dsOn K hL s) := nowhereZero_of_exists fun z _ => by
  obtain ⟨i, hi⟩ := exists_chart K.isLB ((cutIdeal hL s).subschemeι z)
  obtain ⟨j, hj⟩ := exists_chart hL ((cutIdeal hL s).subschemeι z)
  exact ⟨fun _ => twIdx D i j, _, (congrArg IsUnit (germ_dsOn K hL s z i j hi hj)).mpr
    ((isUnit_ger_jacFun hL K s inferInstance (ι_mem_support _ z) i j _).map _)⟩

omit K in
include hS in

theorem quasiRegularAlong_of_etale : QuasiRegularAlong hL s := fun _ hy j hj =>
  isQuasiRegularSeq_secGer hL s (p := p) inferInstance hy j hj

variable {n l : ℤ} {O : Y.Opens}

def mulDs (h : n + D = l) : sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s) ≃ₗ[k]
    sectionsOnClosedSubscheme p (tw (tens K.bundle B) L l) (cutIdeal hL s) :=
  ((adjChart K.isLB hB hL h).pull _).mulEquiv (nowhereZero_dsOn K hL s hS)

def resDs (hO : SuppIn O (cutIdeal hL s)) (h : n + D = l) :
    H0 p (tw (tens K.bundle B) L l) O →ₗ[k] sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s) :=
  (mulDs K hL hB s hS h).symm.toLinearMap ∘ₗ resTo hO

theorem resDs_eq_iff (hO : SuppIn O (cutIdeal hL s)) (h : n + D = l)
    (f : H0 p (tw (tens K.bundle B) L l) O) (g : sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s)) :
    resDs K hL hB s hS hO h f = g ↔ resTo hO f = mulDs K hL hB s hS h g :=
  (mulDs K hL hB s hS h).symm_apply_eq

variable (e : (LB.div A (tw B L D)).Sec)

def mulE (h : n + D = l) :
    H0 p (tw (tens K.bundle B) L l) O →ₗ[k] H0 p (tw (tens K.bundle A) L n) O :=
  (quotChart K.isLB hA hB hL h).mul (H0.ofSec p O e)

variable (he : SuppIn (nonzeroLocus e) (cutIdeal hL s))

def mulEOn (h : n + D = l) : sectionsOnClosedSubscheme p (tw (tens K.bundle B) L l) (cutIdeal hL s) ≃ₗ[k]
    sectionsOnClosedSubscheme p (tw (tens K.bundle A) L n) (cutIdeal hL s) :=
  ((quotChart K.isLB hA hB hL h).pull _).mulEquiv (nowhereZero_secOn he)

theorem resTo_mulE (hO : SuppIn O (cutIdeal hL s)) (h : n + D = l)
    (f : H0 p (tw (tens K.bundle B) L l) O) :
    resTo hO (mulE K hL hA hB e h f) = mulEOn K hL hA hB s e he h (resTo hO f) := by
  rw [mulE, resTo_mul, resTo_ofSec]
  rfl

variable (n) in

def mulEDs : sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s) ≃ₗ[k]
    sectionsOnClosedSubscheme p (tw (tens K.bundle A) L n) (cutIdeal hL s) :=
  (mulDs K hL hB s hS rfl).trans (mulEOn K hL hA hB s e he rfl)

theorem germ_mulEDs (g : sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s)) (z : (cutIdeal hL s).subscheme)
    (i : K.bundle.ι) (a : A.ι) (b : B.ι) (j : L.ι)
    (hi : (cutIdeal hL s).subschemeι z ∈ K.bundle.U i) (ha : (cutIdeal hL s).subschemeι z ∈ A.U a)
    (hb : (cutIdeal hL s).subschemeι z ∈ B.U b) (hj : (cutIdeal hL s).subschemeι z ∈ L.U j) :
    germ (fun _ => twIdx (M := tens K.bundle A) n (i, a) j) z (Opens.mem_top z)
        (mem_pull.2 ((mem_tw_U (M := tens K.bundle A)).2 ⟨⟨hi, ha⟩, hj⟩))
        (mulEDs K hL hA hB s hS n e he g) =
      ((cutIdeal hL s).subschemeι.stalkMap z).hom
          (ger _ (memInf ha (mem_tw_U.2 ⟨hb, hj⟩)) (e.f (a, twIdx D b j)) *
            ger _ (memInf hi hj) (K.jacFun s i j)) *
        germ (fun _ => twIdx n b j) z (Opens.mem_top z) (mem_pull.2 (mem_tw_U.2 ⟨hb, hj⟩)) g := by
  rw [map_mul, mul_assoc]
  exact (((quotChart K.isLB hA hB hL rfl).pull _).germ_mul _ _ (i, a, b, j) z _
    (mem_pull.2 (memInf ha (mem_tw_U.2 ⟨hb, hj⟩)))
    (mem_pull.2 ((mem_tw_U (M := tens K.bundle B)).2 ⟨⟨hi, hb⟩, hj⟩)) _).trans
    (congrArg₂ (· * ·) (germ_secOn _ z _ e)
      ((((adjChart K.isLB hB hL rfl).pull _).germ_mul _ g (i, b, j) z _
        (mem_pull.2 (mem_tw_U.2 ⟨hi, hj⟩)) _ _).trans
          (congrArg (· * _) (germ_dsOn K hL s z i j hi hj))))

theorem valOn_mulEDs {R : Type} [CommRing R] (g : sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s))
    (x : Sp R ⟶ (cutIdeal hL s).subscheme) (i : K.bundle.ι) (a : A.ι) (b : B.ι) (j : L.ι)
    (hi : ⊤ ≤ (x ≫ (cutIdeal hL s).subschemeι) ⁻¹ᵁ K.bundle.U i)
    (hj : ⊤ ≤ (x ≫ (cutIdeal hL s).subschemeι) ⁻¹ᵁ L.U j)
    (h₁ : ⊤ ≤ (x ≫ (cutIdeal hL s).subschemeι) ⁻¹ᵁ
      (tw (tens K.bundle A) L n).U (twIdx (M := tens K.bundle A) n (i, a) j))
    (h₂ : ⊤ ≤ (x ≫ (cutIdeal hL s).subschemeι) ⁻¹ᵁ (LB.div A (tw B L D)).U (a, twIdx D b j))
    (h₃ : ⊤ ≤ (x ≫ (cutIdeal hL s).subschemeι) ⁻¹ᵁ (tw B L n).U (twIdx n b j)) :
    valOn x (twIdx (M := tens K.bundle A) n (i, a) j) h₁ (mulEDs K hL hA hB s hS n e he g) =
      evalPt (x ≫ (cutIdeal hL s).subschemeι) _ h₂ (e.f (a, twIdx D b j)) *
        K.jacVal s (x ≫ (cutIdeal hL s).subschemeι) i j hi hj * valOn x (twIdx n b j) h₃ g := by
  rw [mul_assoc]
  exact (valOn_mul (quotChart K.isLB hA hB hL rfl) _ _ (i, a, b, j) x h₂
    (fun z hz => mem_tw_U.2 ⟨⟨hi hz, (h₃ hz).1⟩, hj hz⟩) h₁).trans
    (congrArg₂ (· * ·) (valOn_secOn x _ _ e) ((valOn_mul (adjChart K.isLB hB hL rfl) _ g (i, b, j) x
      (fun z hz => mem_tw_U.2 ⟨hi hz, hj hz⟩) h₃ _).trans
        (congrArg (· * _) (valOn_dsOn K hL s x i j hi hj _))))

theorem mulEDs_mulSecOn (w : L.Sec) (h : n + 1 = l) (g : sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s)) :
    mulEDs K hL hA hB s hS l e he (mulSecOn hB hL w h g) =
      mulSecOn (isLB_tens K.isLB hA) hL w h (mulEDs K hL hA hB s hS n e he g) :=
  ext_germ fun z _ => by
    obtain ⟨⟨i, a, b, j⟩, ⟨ha, -⟩, h', -⟩ :=
      (quotChart K.isLB hA hB hL (n := n) (d := 0) rfl).cover ((cutIdeal hL s).subschemeι z)
    obtain ⟨⟨hi, hb⟩, hj⟩ := mem_tw_U.1 h'
    refine ⟨_, _, (germ_mulEDs K hL hA hB s hS e he _ z i a b j hi ha hb hj).trans ?_⟩
    refine (congrArg (_ * ·) (((oneChart hB hL h).pull _).germ_mul _ g (b, j) z _ (mem_pull.2 hj)
      (mem_pull.2 (mem_tw_U.2 ⟨hb, hj⟩)) _)).trans ((mul_left_comm _ _ _).trans (Eq.symm ?_))
    exact (((oneChart (isLB_tens K.isLB hA) hL h).pull _).germ_mul _ _ ((i, a), j) z _
      (mem_pull.2 hj) _ _).trans
      (congrArg (_ * ·) (germ_mulEDs K hL hA hB s hS e he _ z i a b j hi ha hb hj))

variable (hO : SuppIn O (cutIdeal hL s))

variable (n) in

def Res : H0 p (tw (tens K.bundle A) L n) O →ₗ[k] sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s) :=
  (mulEDs K hL hA hB s hS n e he).symm.toLinearMap ∘ₗ resTo hO

theorem Res_eq_iff (m : H0 p (tw (tens K.bundle A) L n) O) (g : sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s)) :
    Res K hL hA hB s hS n e he hO m = g ↔ resTo hO m = mulEDs K hL hA hB s hS n e he g :=
  (mulEDs K hL hA hB s hS n e he).symm_apply_eq

theorem mulEDs_Res (m : H0 p (tw (tens K.bundle A) L n) O) :
    mulEDs K hL hA hB s hS n e he (Res K hL hA hB s hS n e he hO m) = resTo hO m :=
  ((Res_eq_iff K hL hA hB s hS e he hO m _).1 rfl).symm

theorem Res_mulSec (w : L.Sec) (h : n + 1 = l) (m : H0 p (tw (tens K.bundle A) L n) O) :
    Res K hL hA hB s hS l e he hO (mulSec (isLB_tens K.isLB hA) hL w h m) =
      mulSecOn hB hL w h (Res K hL hA hB s hS n e he hO m) := by
  rw [Res_eq_iff, mulEDs_mulSecOn, mulEDs_Res, resTo_mulSec]

theorem Res_mulE (h : n + D = l) (f : H0 p (tw (tens K.bundle B) L l) O) :
    Res K hL hA hB s hS n e he hO (mulE K hL hA hB e h f) = resDs K hL hB s hS hO h f := by
  subst h
  rw [Res_eq_iff, resTo_mulE K hL hA hB s e he]
  exact congrArg _ ((resDs_eq_iff K hL hB s hS hO rfl f _).1 rfl)

theorem Res_restr {O' : Y.Opens} (hO' : SuppIn O' (cutIdeal hL s)) (h : O' ≤ O)
    (m : H0 p (tw (tens K.bundle A) L n) O) :
    Res K hL hA hB s hS n e he hO' (restr h m) = Res K hL hA hB s hS n e he hO m :=
  congrArg (mulEDs K hL hA hB s hS n e he).symm (resTo_restr hO' h m)

theorem Res_eq_zero_iff (m : H0 p (tw (tens K.bundle A) L n) O) :
    Res K hL hA hB s hS n e he hO m = 0 ↔ VanishesTo (cutIdeal hL s) 1 m := by
  rw [Res_eq_iff, map_zero, resTo_eq_zero_iff]

variable (p B) in

abbrev SymTarget (a : ℕ) (n : ℤ) : Type := MonoDeg (Fin D) a → sectionsOnClosedSubscheme p (tw B L n) (cutIdeal hL s)

variable {a : ℕ} (h : n + a = l)

def HasSymbol (f : H0 p (tw (tens K.bundle A) L l) O) (g : SymTarget p B hL s a n) : Prop :=
  HasLead hL s hO h f fun α => mulEDs K hL hA hB s hS n e he (g α)

variable (V : Submodule k (H0 p (tw (tens K.bundle A) L l) O))

def sym : Fil (cutIdeal hL s) a V →ₗ[k] SymTarget p B hL s a n :=
  (mulEDs K hL hA hB s hS n e he).symm.toLinearMap.compLeft _ ∘ₗ
    lead hO h (isLB_tens K.isLB hA) (quasiRegularAlong_of_etale hL s hS) ∘ₗ
      Submodule.inclusion Fil_le_filTop

variable {V}

theorem sym_eq_iff (f : Fil (cutIdeal hL s) a V) (g : SymTarget p B hL s a n) :
    sym K hL hA hB s hS e he hO h V f = g ↔ HasSymbol K hL hA hB s hS e he hO h f.1 g :=
  (funext_iff.trans ((forall_congr' fun _ =>
    (mulEDs K hL hA hB s hS n e he).symm_apply_eq).trans funext_iff.symm)).trans
      (lead_eq_iff (isLB_tens K.isLB hA) (quasiRegularAlong_of_etale hL s hS) _)

theorem sym_eq_zero_iff (f : Fil (cutIdeal hL s) a V) :
    sym K hL hA hB s hS e he hO h V f = 0 ↔ f.1 ∈ Fil (cutIdeal hL s) (a + 1) V := by
  rw [sym_eq_iff, mem_Fil, and_iff_right (Fil_le f.2), ← hasLead_zero_iff (hO := hO) (h := h)
    (isLB_tens K.isLB hA)]
  exact iff_of_eq (congrArg _ (funext fun _ => map_zero _))

variable (V) in

theorem ker_sym : LinearMap.ker (sym K hL hA hB s hS e he hO h V) =
    (Fil (cutIdeal hL s) (a + 1) V).submoduleOf (Fil (cutIdeal hL s) a V) :=
  Submodule.ext (sym_eq_zero_iff K hL hA hB s hS e he hO h)

theorem sym_sum (m : MonoDeg (Fin D) a → H0 p (tw (tens K.bundle A) L n) O)
    (f : Fil (cutIdeal hL s) a V) (hf : f.1 = ∑ α, mulMono (isLB_tens K.isLB hA) hL s α h (m α)) :
    sym K hL hA hB s hS e he hO h V f = fun α => Res K hL hA hB s hS n e he hO (m α) := by
  rw [sym_eq_iff, hf, HasSymbol]
  simp only [mulEDs_Res]
  exact hasLead_sum hL s hO h _ m

theorem sym_mulMono (α : MonoDeg (Fin D) a) (m : H0 p (tw (tens K.bundle A) L n) O)
    (f : Fil (cutIdeal hL s) a V) (hf : f.1 = mulMono (isLB_tens K.isLB hA) hL s α h m) :
    sym K hL hA hB s hS e he hO h V f = Pi.single α (Res K hL hA hB s hS n e he hO m) := by
  rw [sym_sum K hL hA hB s hS e he hO h (Pi.single α m) f]
  · exact funext fun β => Pi.apply_single (fun _ => Res K hL hA hB s hS n e he hO)
      (fun _ => map_zero _) α m β
  · rw [hf, Finset.sum_eq_single α (fun β _ hβ => by rw [Pi.single_eq_of_ne hβ, map_zero])
      (by simp), Pi.single_eq_same]

variable (V) in

def symGr : gr (cutIdeal hL s) a V →ₗ[k] SymTarget p B hL s a n :=
  Submodule.liftQ _ (sym K hL hA hB s hS e he hO h V) (ker_sym K hL hA hB s hS e he hO h V).ge

end Symbol

section BaseChange

variable {k' : Type} [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'} {r : T ⟶ Y}
  {A B : LB Y} {A' B' : LB T} {O : Y.Opens} {W : T.Opens}

theorem tr_chartPull (a : ChartPull B' B r) (z : T) {i j : B'.ι} (hi : z ∈ B'.U i)
    (hj : z ∈ B'.U j) : tr B' z i j =
      Units.map (r.stalkMap z).hom.toMonoidHom (tr B (r z) (a.idx i) (a.idx j)) := by
  have h := memInf (a.le i hi) (a.le j hj)
  refine (a.g z i j hi hj).trans (Units.ext ((gm_val r z _ h _).trans ?_))
  exact (Scheme.Hom.germ_stalkMap_apply r _ z h _).symm.trans
    (congrArg (r.stalkMap z).hom (val_tr B _ h).symm)

def chartPullTens (a : ChartPull A' A r) (b : ChartPull B' B r) :
    ChartPull (tens A' B') (tens A B) r where
  idx t := (a.idx t.1, b.idx t.2)
  le t _ hz := ⟨a.le _ hz.1, b.le _ hz.2⟩
  g z i j hi hj := (gm_tens A' B' (𝟙 T) z i j hi hj).trans ((congrArg₂ (· * ·)
    (a.g z _ _ hi.1 hj.1) (b.g z _ _ hi.2 hj.2)).trans (gm_tens A B r z (a.idx i.1, b.idx i.2)
      (a.idx j.1, b.idx j.2) ⟨a.le _ hi.1, b.le _ hi.2⟩ ⟨a.le _ hj.1, b.le _ hj.2⟩).symm)

def chartPullQuot (a : ChartPull A' A r) (b : ChartPull B' B r) :
    ChartPull (LB.div A' B') (LB.div A B) r where
  idx t := (a.idx t.1, b.idx t.2)
  le t _ hz := ⟨a.le _ hz.1, b.le _ hz.2⟩
  g z i j hi hj := (gm_div' A' B' (𝟙 T) z i j hi hj).trans ((congrArg₂ (· * ·⁻¹)
    (a.g z _ _ hi.1 hj.1) (b.g z _ _ hi.2 hj.2)).trans (gm_div' A B r z (a.idx i.1, b.idx i.2)
      (a.idx j.1, b.idx j.2) ⟨a.le _ hi.1, b.le _ hi.2⟩ ⟨a.le _ hj.1, b.le _ hj.2⟩).symm)

def chartPullZPow (b : ChartPull B' B r) (n : ℤ) : ChartPull (lbZPow B' n) (lbZPow B n) r where
  idx t _ := b.idx (t PUnit.unit)
  le t _ hz := (mem_zpow_U (n := n)).2 (b.le _ (Twist.zpow_U_le t hz))
  g z i j hi hj := by
    have e := gm_linComb B (fun _ : PUnit => 𝟙 Y) (fun _ => n) r z (fun _ => b.idx (i PUnit.unit))
      (fun _ => b.idx (j PUnit.unit)) (mem_zpow_U (n := n).2 (b.le _ (Twist.zpow_U_le i hi)))
      (mem_zpow_U (n := n).2 (b.le _ (Twist.zpow_U_le j hj)))
    rw [Fintype.prod_unique, Category.comp_id] at e
    exact (tr_zpow B' n z hi hj).trans ((congrArg (· ^ n)
      (b.g z _ _ (Twist.zpow_U_le i hi) (Twist.zpow_U_le j hj))).trans e.symm)

abbrev chartPullTwist (a : ChartPull A' A r) (b : ChartPull B' B r) (n : ℤ) :
    ChartPull (tw A' B' n) (tw A B n) r := chartPullTens a (chartPullZPow b n)

def pullChartFun (a : ChartPull B' B r) (q : T ⟶ Sp k') (h : W ≤ r ⁻¹ᵁ O) (f : H0 p B O) :
    H0 q B' W :=
  mkSec (fun i => (r.appLE (O ⊓ B.U (a.idx i)) _ (inf_le_inf h (a.le i))).hom (f.loc _))
    fun i j => fun_ext_ger fun z hz => by
      rw [map_mul, ger_resG, ger_resG, ger_resG, ← val_tr, tr_chartPull a z hz.1.2 hz.2]
      exact (ger_appLE r _ z _ _).trans <|
        (congrArg _ (germ_change _ _ (r z) (h hz.1.1) (a.le i hz.1.2) (a.le j hz.2) f)).trans
          ((map_mul _ _ _).trans (congrArg (_ * ·) (ger_appLE r (U := O ⊓ B.U (a.idx j))
            (inf_le_inf h (a.le j)) z (memInf hz.1.1 hz.2) (f.loc _)).symm))

theorem germ_pullChartFun (a : ChartPull B' B r) (h : W ≤ r ⁻¹ᵁ O) (f : H0 p B O) (i : B'.ι) (z : T)
    (hz : z ∈ W) (hi : z ∈ B'.U i) : germ i z hz hi (pullChartFun a q h f) =
      (r.stalkMap z).hom (germ (a.idx i) (r z) (h hz) (a.le i hi) f) :=
  ger_appLE r _ z (memInf hz hi) _

theorem stalkMap_const_of_comm (hq : r ≫ p = q ≫ spMap φ) (z : T) (c : k) :
    (r.stalkMap z).hom (const p (r z) c) = const q z (φ c) := by
  rw [stalkMap_const, hq]
  refine congrArg (ger (U := ⊤) z trivial) ?_
  have e₂ := Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ ⊤ le_top le_top
  have e₃ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at e₃
  have e₅ := ((congrArg (· ≫ q.appLE ⊤ ⊤ le_top) e₃).trans (Category.assoc _ _ _)).trans
    (congrArg (_ ≫ ·) e₂)
  exact (congrArg (fun g => g.hom c) e₅).symm

def pullChart (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) :
    H0 p B O →ₛₗ[φ] H0 q B' W where
  toFun := pullChartFun a q h
  map_add' f g := LB.sec_ext fun _ => map_add _ _ _
  map_smul' c f := LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_smul, germ_pullChartFun, germ_pullChartFun, ← stalkMap_const_of_comm hq, ← map_mul]
    exact congrArg _ (germ_smul _ _ _ _ _ _)

theorem germ_pullChart (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O)
    (f : H0 p B O) (i : B'.ι) (z : T) (hz : z ∈ W) (hi : z ∈ B'.U i) :
    germ i z hz hi (pullChart a hq h f) =
      (r.stalkMap z).hom (germ (a.idx i) (r z) (h hz) (a.le i hi) f) :=
  germ_pullChartFun a h f i z hz hi

theorem VanishesTo.pullChart {I : Y.IdealSheafData} {J : T.IdealSheafData} {n : ℕ} {f : H0 p B O}
    (hf : VanishesTo I n f) (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O)
    (hI : ∀ z, (stalkId I (r z)).map (r.stalkMap z).hom ≤ stalkId J z) :
    VanishesTo J n (pullChart a hq h f) := fun z _ hz i hi => by
  rw [germ_pullChart]
  refine Ideal.pow_right_mono (hI z) n ?_
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (vanishesTo_iff_forall.1 hf _ _ _ _)

end BaseChange

namespace AffineExample

open MvPolynomial CanonLB

variable {D : ℕ}

abbrev triv (k : Type) [CommRing k] (D : ℕ) : LB (Sp (MvPolynomial (Fin D) k)) := Out.Inh.trivLB _

theorem isLB_triv : (triv k D).IsLB :=
  ⟨iSup_const (ι := PUnit), fun _ => map_one _, fun _ _ _ => by
    exact (congrArg₂ (· * ·) (map_one _) (map_one _)).trans ((mul_one _).trans (map_one _).symm)⟩

theorem bijective_polyFn : Function.Bijective (polyFn (k := k) (D := D)) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv

abbrev ideal (g : Fin D → MvPolynomial (Fin D) k) : (Sp (MvPolynomial (Fin D) k)).IdealSheafData :=
  cutIdeal isLB_triv fun a => polySec (g a)

theorem ideal_top (g : Fin D → MvPolynomial (Fin D) k) :
    (ideal g).ideal ⟨⊤, isAffineOpen_top _⟩ = (Ideal.span (Set.range g)).map polyFn := by
  rw [ideal_cutIdeal _ _ _ PUnit.unit le_rfl, Ideal.map_span, ← Set.range_comp]
  exact congrArg (fun f => Ideal.span (Set.range f)) (funext fun _ => resG_self _ _)

theorem vanishesTo_iff (g : Fin D → MvPolynomial (Fin D) k) (a : ℕ) (f : MvPolynomial (Fin D) k) :
    VanishesTo (ideal g) a (H0.ofSec (affStr k D) ⊤ (polySec f)) ↔
      f ∈ Ideal.span (Set.range g) ^ a := by
  rw [← Ideal.comap_map_of_bijective _ bijective_polyFn (I := _ ^ a), Ideal.mem_comap,
    Ideal.map_pow, ← ideal_top]
  refine Iff.trans ?_ (mem_ideal_iff_ger (ideal g ^ a) ⟨⊤, isAffineOpen_top _⟩ _).symm
  simp only [vanishesTo_iff_forall, germ_ofSec, stalkId_pow]
  exact ⟨fun h y hy => h y hy PUnit.unit hy, fun h y hy _ _ => h y hy⟩

theorem isIso_of_span {g : Fin D → MvPolynomial (Fin D) k}
    (hg : Ideal.span (Set.range g) = Ideal.span (Set.range X)) :
    IsIso ((ideal g).subschemeι ≫ affStr k D) := by
  have hk (f : MvPolynomial (Fin D) k) :
      ((ideal g).subschemeι.app ⊤).hom (polyFn f) = 0 ↔ constantCoeff f = 0 := by
    rw [← RingHom.mem_ker, (ideal g).ker_subschemeι_app ⟨⊤, isAffineOpen_top _⟩, ideal_top, hg,
      ← Ideal.mem_comap, Ideal.comap_map_of_bijective _ bijective_polyFn, ← pow_one (Ideal.span _)]
    refine (mem_pow_idealOfVars_iff' 1 f).trans ?_
    simp [constantCoeff_eq, Finsupp.degree_eq_zero_iff]
  have hk' (f f' : MvPolynomial (Fin D) k) : ((ideal g).subschemeι.app ⊤).hom (polyFn f) =
      ((ideal g).subschemeι.app ⊤).hom (polyFn f') ↔ constantCoeff f = constantCoeff f' := by
    rw [← sub_eq_zero, ← map_sub, ← map_sub, hk, map_sub, sub_eq_zero]
  have he (c : k) : (((ideal g).subschemeι ≫ affStr k D).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) =
        ((ideal g).subschemeι.app ⊤).hom (polyFn (C c)) :=
    congrArg ((ideal g).subschemeι.app ⊤).hom (congrArg (fun q => CommRingCat.Hom.hom q c)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin D) k))))).symm
  have : IsAffine (ideal g).subscheme := isAffine_of_isAffineHom (ideal g).subschemeι
  suffices IsIso ((ideal g).subschemeι ≫ affStr k D).appTop from
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
      (arrowIsoSpecΓOfIsAffine _)).mpr (inferInstanceAs (IsIso (Spec.map _)))
  rw [ConcreteCategory.isIso_iff_bijective, ← Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv)]
  refine ⟨fun c c' e => ?_, fun b => ?_⟩
  · simpa using (hk' _ _).1 ((he c).symm.trans (e.trans (he c')))
  · obtain ⟨b, rfl⟩ := (ideal g).subschemeι_app_surjective ⟨⊤, isAffineOpen_top _⟩ b
    obtain ⟨f, rfl⟩ := bijective_polyFn.2 b
    exact ⟨constantCoeff f, (he _).trans ((hk' _ _).2 (by simp))⟩

theorem etale_of_span {g : Fin D → MvPolynomial (Fin D) k}
    (hg : Ideal.span (Set.range g) = Ideal.span (Set.range X)) :
    Etale ((ideal g).subschemeι ≫ affStr k D) :=
  have := isIso_of_span hg
  inferInstance

def funSec {N : LB Y} (h : ∀ y i j, y ∈ N.U i → y ∈ N.U j → tr N y i j = 1) (f : Γ(Y, ⊤)) :
    N.Sec where
  f _ := resG Y le_top f
  compat i j := fun_ext_ger fun y hy => by
    rw [map_mul, ← val_tr, h y i j hy.1 hy.2, Units.val_one, one_mul, ger_resG, ger_resG, ger_resG,
      ger_resG]

theorem tr_triv (y) (i j : (triv k D).ι) : tr (triv k D) y i j = 1 := map_one _

theorem mem_tw_triv (n : ℤ) (y : Sp (MvPolynomial (Fin D) k)) :
    y ∈ (tw (triv k D) (triv k D) n).U (twIdx n PUnit.unit PUnit.unit) :=
  mem_tw_U.2 ⟨trivial, trivial⟩

def one : (LB.div (triv k D) (tw (triv k D) (triv k D) D)).Sec :=
  funSec (fun y i j hi hj => by
    rw [tr_div _ _ y hi hj, tr_tens _ _ y hi.2 hj.2, tr_zpow _ _ y hi.2.2 hj.2.2]
    simp only [tr_triv, one_zpow, mul_one, inv_one]) 1

theorem suppIn_one (I) : SuppIn (nonzeroLocus (one (k := k) (D := D))) I := fun y _ =>
  (isUnit_ger_iff (i := (PUnit.unit, twIdx D PUnit.unit PUnit.unit)) _
    (memInf (Opens.mem_top y) (mem_tw_triv D y))).1 ((isUnit_one.map _).map _)

def form (n : ℤ) (f : MvPolynomial (Fin D) k) :
    H0 (affStr k D) (tw (tens (affineSpace k D).bundle (triv k D)) (triv k D) n) ⊤ :=
  H0.ofSec _ ⊤ (funSec (fun y i j hi hj => by
    rw [tr_tens _ _ y hi hj, tr_tens _ _ y hi.1 hj.1, tr_zpow _ _ y hi.2 hj.2,
      show tr (affineSpace k D).bundle y i.1.1 j.1.1 = 1 from
        gm_self (affineSpace k D).isLB (𝟙 _) y hi.1.1]
    simp only [tr_triv, one_zpow, mul_one]) (polyFn f))

theorem det_mul_valOn_Res {R : Type} [CommRing R] {g : Fin D → MvPolynomial (Fin D) k}
    (hS : Etale ((ideal g).subschemeι ≫ affStr k D)) (n : ℤ) (f : MvPolynomial (Fin D) k)
    (x : Sp R ⟶ (ideal g).subscheme) (φ : MvPolynomial (Fin D) k →+* R)
    (hx : x ≫ (ideal g).subschemeι = spMap φ) :
    φ (Matrix.of fun a b => pderiv b (g a)).det *
      valOn x (twIdx n PUnit.unit PUnit.unit) (fun _ _ => mem_tw_triv _ _)
        (Res (affineSpace k D) isLB_triv isLB_triv isLB_triv _ hS n one (suppIn_one _) suppIn_top
          (form n f)) = φ f := by
  have h₁ : ∀ y, y ∈ (tw (tens (affineSpace k D).bundle (triv k D)) (triv k D) n).U
      (twIdx (M := tens (affineSpace k D).bundle (triv k D)) n (PUnit.unit, PUnit.unit) PUnit.unit) :=
    fun _ => mem_tw_U.2 ⟨⟨trivial, trivial⟩, trivial⟩
  have e := valOn_mulEDs (affineSpace k D) isLB_triv isLB_triv isLB_triv _ hS one (suppIn_one _)
    (Res _ isLB_triv isLB_triv isLB_triv _ hS n one (suppIn_one _) suppIn_top (form n f)) x
    PUnit.unit PUnit.unit PUnit.unit PUnit.unit le_top le_top (fun _ _ => h₁ _)
    (fun _ _ => memInf (Opens.mem_top _) (mem_tw_triv D _))
    (fun _ _ => mem_tw_triv _ _)
  rw [mulEDs_Res] at e
  replace e := (valOn_resTo _ _ _ _ le_top _).symm.trans e
  have key (y : Sp R ⟶ Sp (MvPolynomial (Fin D) k)) (hy : y = spMap φ) :
      (affineSpace k D).jacVal (fun a => polySec (g a)) y PUnit.unit PUnit.unit le_top le_top =
        φ (Matrix.of fun a b => pderiv b (g a)).det ∧ evalPt y ⊤ le_top (polyFn f) = φ f := by
    subst hy
    exact ⟨jacVal_affineSpace k D φ g, evalPt_spMap φ f⟩
  refine Eq.trans ?_ ((e.symm.trans ((val_ofSec _ _ _ _ _).trans
    (evalPt_res _ le_top le_top _ _))).trans (key _ hx).2)
  exact congrArg (· * _) ((key _ hx).1.symm.trans ((one_mul _).symm.trans
    (congrArg (· * _) ((congrArg _ (map_one _)).trans (map_one _)).symm)))

example : VanishesTo (ideal X) 2 (H0.ofSec (affStr ℚ 2) ⊤ (polySec (X 0 * X 1))) ∧
    ¬ VanishesTo (ideal X) 3 (H0.ofSec (affStr ℚ 2) ⊤ (polySec (X 0 * X 1))) := by
  simp only [vanishesTo_iff]
  refine ⟨?_, fun h => ?_⟩
  · rw [pow_two]
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨0, rfl⟩) (Ideal.subset_span ⟨1, rfl⟩)
  have := (mem_pow_idealOfVars_iff' 3 _).1 h (Finsupp.single 0 1 + Finsupp.single 1 1) (by simp)
  simp [X, monomial_mul] at this

example {R : Type} [CommRing R] (hS : Etale ((ideal ![X 1, X 0]).subschemeι ≫ affStr k 2))
    (f : MvPolynomial (Fin 2) k) (x : Sp R ⟶ (ideal ![X 1, X 0]).subscheme)
    (φ : MvPolynomial (Fin 2) k →+* R) (hx : x ≫ (ideal ![X 1, X 0]).subschemeι = spMap φ) :
    valOn x (twIdx 0 PUnit.unit PUnit.unit) (fun _ _ => mem_tw_triv _ _)
      (Res (affineSpace k 2) isLB_triv isLB_triv isLB_triv _ hS 0 one (suppIn_one _) suppIn_top
        (form 0 f)) = -φ f := by
  rw [← det_mul_valOn_Res hS 0 f x φ hx]
  simp [Matrix.det_fin_two]

example : Etale ((ideal ![X 1, X 0]).subschemeι ≫ affStr k 2) :=
  etale_of_span (congrArg Ideal.span (by simp [Set.pair_comm, Set.ext_iff, Fin.exists_fin_two, eq_comm, or_comm]))

end AffineExample

end GlobalTheory.Vanishing
