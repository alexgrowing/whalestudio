import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.DualOrthSum
import Formalism.HermitianLattices.NeighbourConstruct
import Formalism.SatakeDualWeyl.StatementB
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.HermitianLatticesTheory

abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E

section Space

variable (E : Type) [Field E] [StarRing E] (n : ℕ)

def hStd : Sp E n →ₗ⋆[E] Sp E n →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => ∑ i, star (x i) * y i)
    (by intro x y z; simp [add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (by intro x y z; simp [mul_add, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_left_comm])

abbrev UF : Subgroup (Sp E n ≃ₗ[E] Sp E n) := isom (hStd E n)

def incl : Sp E n →ₗ[E] Sp E (n + 1) where
  toFun x := Fin.snoc (α := fun _ => E) x 0
  map_add' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def initL : Sp E (n + 1) →ₗ[E] Sp E n := LinearMap.funLeft E E Fin.castSucc

def eLast : Sp E (n + 1) := Pi.single (Fin.last n) 1

def z0 (pi : E) : Sp E (n + 1) := pi • eLast E n

end Space

def lastIdx (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) one_pos⟩

section Red

variable {E : Type} [Field E] [NumberField E]

def redP (P : HeightOneSpectrum (𝓞 E)) (a : E) : 𝓞 E ⧸ P.asIdeal :=
  open Classical in
  if h : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r
  then h.choose else 0

end Red

section Deco

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
  (ST SG : Finset (HeightOneSpectrum (𝓞 E)))

@[ext] structure Deco where

  N : Submodule (𝓞 E) (Sp E n)

  f : ∀ P : ST, Sp E n → 𝓞 E ⧸ P.1.asIdeal

  be : ∀ w : SG, Sp E n → (Fin n → 𝓞 E ⧸ w.1.asIdeal)

variable {E n ST SG}

abbrev Deco.at (d : Deco E n ST SG) (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E n) :=
  localization₂ P.asIdeal d.N

structure Deco.Ok (d : Deco E n ST SG) : Prop where
  lat : Submodule.IsLattice E d.N
  uni : IsUnimodular (hStd E n) d.N
  f_add : ∀ (P : ST), ∀ x ∈ d.at P.1, ∀ y ∈ d.at P.1, d.f P (x + y) = d.f P x + d.f P y
  f_smul : ∀ (P : ST) (a : 𝓞 E), ∀ x ∈ d.at P.1,
    d.f P (a • x) = Ideal.Quotient.mk P.1.asIdeal a * d.f P x
  f_off : ∀ (P : ST) (x : Sp E n), x ∉ d.at P.1 → d.f P x = 0
  f_ne : ∀ P : ST, ∃ x ∈ d.N, d.f P x ≠ 0
  be_add : ∀ (w : SG), ∀ x ∈ d.at w.1, ∀ y ∈ d.at w.1, d.be w (x + y) = d.be w x + d.be w y
  be_smul : ∀ (w : SG) (a : 𝓞 E), ∀ x ∈ d.at w.1,
    d.be w (a • x) = Ideal.Quotient.mk w.1.asIdeal a • d.be w x
  be_off : ∀ (w : SG) (x : Sp E n), x ∉ d.at w.1 → d.be w x = 0
  be_surj : ∀ (w : SG) (c : Fin n → 𝓞 E ⧸ w.1.asIdeal), ∃ x ∈ d.N, d.be w x = c
  be_ker : ∀ (w : SG), ∀ x ∈ d.N, d.be w x = 0 → x ∈ w.1.asIdeal • d.N

variable (E n ST SG) in

abbrev DecoSet : Type := {d : Deco E n ST SG // d.Ok}

variable (E n SG) in

abbrev GLG : Type := ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)

variable (E ST) in

abbrev DiaG : Type := ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ

def Deco.act (ga : Sp E n ≃ₗ[E] Sp E n) (h : GLG E n SG) (d : Deco E n ST SG) : Deco E n ST SG where
  N := gmap ga d.N
  f P x := d.f P (ga.symm x)
  be w x := (h w).1.mulVec (d.be w (ga.symm x))

def Deco.dia (c : DiaG E ST) (d : Deco E n ST SG) : Deco E n ST SG where
  N := d.N
  f P x := (c P).1 * d.f P x
  be := d.be

def Deco.kerAt (d : Deco E n ST SG) (P : ST) : Submodule (𝓞 E) (Sp E n) :=
  Submodule.span (𝓞 E) {x | x ∈ d.N ∧ d.f P x = 0}

def Deco.L (d : Deco E n ST SG) : Submodule (𝓞 E) (Sp E n) :=
  Submodule.span (𝓞 E) {x | x ∈ d.N ∧ ∀ P : ST, d.f P x = 0}

def Deco.Lsh (d : Deco E n ST SG) : Submodule (𝓞 E) (Sp E n) := dual (hStd E n) d.L

variable (E n) in

def stdLat : Submodule (𝓞 E) (Sp E n) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

variable (E n ST SG) in

def Deco.base [NeZero n] : Deco E n ST SG where
  N := stdLat E n
  f P x := open Classical in
    if x ∈ localization₂ P.1.asIdeal (stdLat E n) then redP P.1 (x (lastIdx n)) else 0
  be w x := open Classical in
    if x ∈ localization₂ w.1.asIdeal (stdLat E n) then fun i => redP w.1 (x i) else 0

def upA (P : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) : Submodule (𝓞 E) (Sp E n) :=
  N ⊔ Submodule.span (𝓞 E) {z | ∃ a ∈ invIdeal (K := E) P, z = a • x}

def upN (P : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) : Submodule (𝓞 E) (Sp E n) :=
  dual (hStd E n) (upA P N x) ⊔ conjIdeal (K := E) P • upA P N x

def Deco.up (d : Deco E n ST SG) (P : ST) (q : 𝓞 E) (x : Sp E n) : Deco E n ST SG where
  N := upN P.1.asIdeal d.N x
  f := open Classical in Function.update d.f P fun y =>
    if y ∈ localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) then d.f P (q • y) else 0
  be := d.be

def Deco.dnN (d : Deco E n ST SG) (P : ST) : Submodule (𝓞 E) (Sp E n) :=
  d.kerAt P ⊔ P.1.asIdeal • dual (hStd E n) (d.kerAt P)

def Deco.dn (d : Deco E n ST SG) (P : ST) (f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal) : Deco E n ST SG where
  N := d.dnN P
  f := open Classical in Function.update d.f P f'
  be := d.be

def Deco.IsUp (P : ST) (q : 𝓞 E) (d d' : Deco E n ST SG) : Prop :=
  ∃ x ∈ d.N, d.f P x = 1 ∧ d' = d.up P q x

def Deco.IsDn (P : ST) (q : 𝓞 E) (d d' : Deco E n ST SG) : Prop :=
  d' = d.dn P (d'.f P) ∧ ∀ e ∈ d.N, d.f P e = 1 → d'.f P (q • e) = 1

def tilN (N : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) (Sp E (n + 1)) :=
  N.map ((incl E n).restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {eLast E n}

def Deco.til (pi : 𝓞 E) (d : Deco E n ∅ SG) : Deco E (n + 1) ST SG where
  N := tilN d.N
  f P x := open Classical in
    if x ∈ localization₂ P.1.asIdeal (tilN d.N)
    then redP P.1 (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) x) else 0
  be w x := open Classical in
    if x ∈ localization₂ w.1.asIdeal (tilN d.N)
    then Fin.snoc (α := fun _ => 𝓞 E ⧸ w.1.asIdeal) (d.be w (initL E n x))
      (redP w.1 (x (Fin.last n) / algebraMap (𝓞 E) E pi))
    else 0

end Deco

section Lemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem hStd_apply (x y : Sp E n) : hStd E n x y = ∑ i, star (x i) * y i := rfl

theorem hStd_isSymm : (hStd E n).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp [hStd_apply, mul_comm, starRingEnd_apply]

theorem mem_locP {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (P : HeightOneSpectrum (𝓞 E))
    (L : Submodule (𝓞 E) W) (x : W) :
    x ∈ localization₂ P.asIdeal L ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ L := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, hx⟩

theorem le_locP {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (P : HeightOneSpectrum (𝓞 E))
    (L : Submodule (𝓞 E) W) : L ≤ localization₂ P.asIdeal L := fun x hx =>
  (mem_locP P L x).2 ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩

theorem mem_gmap (g : Sp E n ≃ₗ[E] Sp E n) (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) :
    x ∈ gmap g L ↔ g.symm x ∈ L := by
  unfold gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g.symm x, h, by simp⟩

theorem equiv_osmul (g : Sp E n ≃ₗ[E] Sp E n) (s : 𝓞 E) (x : Sp E n) : g (s • x) = s • g x := by
  rw [← algebraMap_smul E s x, map_smul, algebraMap_smul]

theorem mem_localization_gmap (P : HeightOneSpectrum (𝓞 E)) (g : Sp E n ≃ₗ[E] Sp E n)
    (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) :
    x ∈ localization₂ P.asIdeal (gmap g L) ↔ g.symm x ∈ localization₂ P.asIdeal L := by
  simp only [mem_locP, mem_gmap, equiv_osmul]

theorem gmap_lattice (g : Sp E n ≃ₗ[E] Sp E n) (L : Submodule (𝓞 E) (Sp E n))
    (hL : Submodule.IsLattice E L) : Submodule.IsLattice E (gmap g L) := by
  constructor
  · exact hL.fg.map _
  · have h1 : ((gmap g L : Submodule (𝓞 E) (Sp E n)) : Set (Sp E n)) = (g : Sp E n →ₗ[E] Sp E n) '' L := by
      ext x
      simp [gmap]
    rw [h1, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem mem_dual (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) :
    x ∈ dual (hStd E n) L ↔ ∀ y ∈ L, hStd E n y x ∈ (1 : Submodule (𝓞 E) E) := by
  unfold dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]

theorem dual_gmap (g : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ UF E n) (L : Submodule (𝓞 E) (Sp E n)) :
    dual (hStd E n) (gmap g L) = gmap g (dual (hStd E n) L) := by
  ext x
  rw [mem_gmap, mem_dual, mem_dual]
  constructor
  · intro H y hy
    have := H (g y) (by rw [mem_gmap]; simpa using hy)
    rw [← hg y (g.symm x)]
    simpa using this
  · intro H y hy
    have := H (g.symm y) ((mem_gmap g L y).1 hy)
    rw [← hg (g.symm y) (g.symm x)] at this
    simpa using this

theorem Deco.Ok.act {d : Deco E n ST SG} (hd : d.Ok) {ga : Sp E n ≃ₗ[E] Sp E n} (hga : ga ∈ UF E n)
    (h : GLG E n SG) : (d.act ga h).Ok where
  lat := gmap_lattice ga d.N hd.lat
  uni := by
    change dual (hStd E n) (gmap ga d.N) = gmap ga d.N
    rw [dual_gmap ga hga, hd.uni]
  f_add P x hx y hy := by
    change d.f P (ga.symm (x + y)) = _
    rw [map_add]
    exact hd.f_add P _ ((mem_localization_gmap _ _ _ _).1 hx) _ ((mem_localization_gmap _ _ _ _).1 hy)
  f_smul P a x hx := by
    change d.f P (ga.symm (a • x)) = _
    rw [equiv_osmul]
    exact hd.f_smul P a _ ((mem_localization_gmap _ _ _ _).1 hx)
  f_off P x hx := hd.f_off P _ fun h' => hx ((mem_localization_gmap _ _ _ _).2 h')
  f_ne P := by
    obtain ⟨x, hx, hne⟩ := hd.f_ne P
    refine ⟨ga x, (mem_gmap _ _ _).2 (by simpa using hx), ?_⟩
    change d.f P (ga.symm (ga x)) ≠ 0
    simpa using hne
  be_add w x hx y hy := by
    change (h w).1.mulVec (d.be w (ga.symm (x + y))) = _
    rw [map_add, hd.be_add w _ ((mem_localization_gmap _ _ _ _).1 hx) _ ((mem_localization_gmap _ _ _ _).1 hy),
      Matrix.mulVec_add]
    rfl
  be_smul w a x hx := by
    change (h w).1.mulVec (d.be w (ga.symm (a • x))) = _
    rw [equiv_osmul, hd.be_smul w a _ ((mem_localization_gmap _ _ _ _).1 hx), Matrix.mulVec_smul]
    rfl
  be_off w x hx := by
    change (h w).1.mulVec (d.be w (ga.symm x)) = 0
    rw [hd.be_off w _ fun h' => hx ((mem_localization_gmap _ _ _ _).2 h'), Matrix.mulVec_zero]
  be_surj w c := by
    obtain ⟨x, hx, hc⟩ := hd.be_surj w ((h w)⁻¹.1.mulVec c)
    refine ⟨ga x, (mem_gmap _ _ _).2 (by simpa using hx), ?_⟩
    change (h w).1.mulVec (d.be w (ga.symm (ga x))) = c
    rw [LinearEquiv.symm_apply_apply, hc, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  be_ker w x hx h0 := by
    have h1 : d.be w (ga.symm x) = 0 := by
      have h2 : (h w)⁻¹.1.mulVec ((h w).1.mulVec (d.be w (ga.symm x))) = 0 := by
        rw [show (h w).1.mulVec (d.be w (ga.symm x)) = 0 from h0, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] at h2
    have h3 := hd.be_ker w _ ((mem_gmap _ _ _).1 hx) h1
    change x ∈ w.1.asIdeal • (d.N.map ((ga : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)))
    rw [← Submodule.map_smul'']
    exact ⟨ga.symm x, h3, by simp⟩

theorem Deco.Ok.dia {d : Deco E n ST SG} (hd : d.Ok) (c : DiaG E ST) : (d.dia c).Ok where
  lat := hd.lat
  uni := hd.uni
  f_add P x hx y hy := by
    change (c P).1 * d.f P (x + y) = (c P).1 * d.f P x + (c P).1 * d.f P y
    rw [hd.f_add P x hx y hy, mul_add]
  f_smul P a x hx := by
    change (c P).1 * d.f P (a • x) = _ * ((c P).1 * d.f P x)
    rw [hd.f_smul P a x hx, mul_left_comm]
  f_off P x hx := by
    change (c P).1 * d.f P x = 0
    rw [hd.f_off P x hx, mul_zero]
  f_ne P := by
    obtain ⟨x, hx, hne⟩ := hd.f_ne P
    refine ⟨x, hx, ?_⟩
    change (c P).1 * d.f P x ≠ 0
    rwa [Ne, Units.mul_right_eq_zero]
  be_add := hd.be_add
  be_smul := hd.be_smul
  be_off := hd.be_off
  be_surj := hd.be_surj
  be_ker := hd.be_ker

theorem Deco.act_one (d : Deco E n ST SG) : d.act 1 1 = d := by
  ext1
  · change d.N.map _ = d.N
    exact Submodule.map_id d.N
  · rfl
  · funext w x
    change (1 : Matrix _ _ _).mulVec (d.be w x) = _
    rw [Matrix.one_mulVec]

theorem Deco.act_mul (d : Deco E n ST SG) (ga ga' : Sp E n ≃ₗ[E] Sp E n) (h h' : GLG E n SG) :
    d.act (ga * ga') (h * h') = (d.act ga' h').act ga h := by
  ext1
  · change d.N.map _ = (d.N.map _).map _
    rw [← Submodule.map_comp]
    rfl
  · rfl
  · funext w x
    change ((h w).1 * (h' w).1).mulVec _ = (h w).1.mulVec ((h' w).1.mulVec _)
    rw [Matrix.mulVec_mulVec]
    rfl

instance : MulAction (UF E n × GLG E n SG) (DecoSet E n ST SG) where
  smul a d := ⟨d.1.act a.1.1 a.2, d.2.act a.1.2 a.2⟩
  one_smul d := Subtype.ext (Deco.act_one d.1)
  mul_smul a b d := Subtype.ext (Deco.act_mul d.1 a.1.1 b.1.1 a.2 b.2)

theorem DecoSet.smul_val (a : UF E n × GLG E n SG) (d : DecoSet E n ST SG) :
    (a • d).1 = d.1.act a.1.1 a.2 := rfl

def DecoSet.dia (c : DiaG E ST) (d : DecoSet E n ST SG) : DecoSet E n ST SG := ⟨d.1.dia c, d.2.dia c⟩

def DecoSet.dia1 (P : ST) (c : (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : DecoSet E n ST SG) : DecoSet E n ST SG :=
  open Classical in d.dia (Pi.mulSingle P c)

theorem DecoSet.dia_one (d : DecoSet E n ST SG) : d.dia 1 = d := by
  apply Subtype.ext
  ext1
  · rfl
  · funext P x
    change (1 : 𝓞 E ⧸ P.1.asIdeal) * _ = _
    rw [one_mul]
  · rfl

theorem DecoSet.dia_mul (c c' : DiaG E ST) (d : DecoSet E n ST SG) :
    d.dia (c * c') = (d.dia c').dia c := by
  apply Subtype.ext
  ext1
  · rfl
  · funext P x
    change ((c P).1 * (c' P).1) * _ = (c P).1 * ((c' P).1 * _)
    rw [mul_assoc]
  · rfl

theorem DecoSet.dia_smul (c : DiaG E ST) (a : UF E n × GLG E n SG) (d : DecoSet E n ST SG) :
    (a • d).dia c = a • d.dia c := rfl

end Lemmas

section RedLemmas

variable {E : Type} [Field E] [NumberField E]

def IntAt (P : HeightOneSpectrum (𝓞 E)) (a : E) : Prop :=
  ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r

theorem mk_ne_zero {P : HeightOneSpectrum (𝓞 E)} {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
  rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]

theorem one_notMem (P : HeightOneSpectrum (𝓞 E)) : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

instance (P : HeightOneSpectrum (𝓞 E)) : IsDomain (𝓞 E ⧸ P.asIdeal) :=
  Ideal.Quotient.isDomain _

theorem reduction_spec (P : HeightOneSpectrum (𝓞 E)) {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  classical
  have := P.isMaximal
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (mk_ne_zero hs)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨b * Ideal.Quotient.mk P.asIdeal r, r, s, hs, h, by rw [← mul_assoc, hb, one_mul]⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc⟩ := hex.choose_spec
  have e : s * r' = s' * r := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E (s * r') = algebraMap (𝓞 E) E (s' * r)
    simp only [map_mul, map_add]
    rw [← h', ← h]
    ring
  apply mul_left_cancel₀ (mk_ne_zero hs')
  rw [mul_left_comm, hc, ← map_mul, ← map_mul, e]

theorem redP_eq (P : HeightOneSpectrum (𝓞 E)) {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) {c : 𝓞 E ⧸ P.asIdeal}
    (hc : Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r) : redP P a = c :=
  mul_left_cancel₀ (mk_ne_zero hs) ((reduction_spec P hs h).trans hc.symm)

theorem reduction_coe (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    redP P (algebraMap (𝓞 E) E r) = Ideal.Quotient.mk P.asIdeal r :=
  redP_eq P (one_notMem P) (r := r) (by simp) (by simp)

theorem reduction_eq_zero_of_not_integral (P : HeightOneSpectrum (𝓞 E)) {a : E} (h : ¬ IntAt P a) : redP P a = 0 := by
  classical
  unfold redP
  rw [dif_neg]
  rintro ⟨c, r, s, hs, h', -⟩
  exact h ⟨r, s, hs, h'⟩

theorem IntAt.coe (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E r) :=
  ⟨r, 1, one_notMem P, by simp⟩

theorem IntAt.add {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    IntAt P (a + b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨s' * r + s * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  simp only [map_mul, map_add]
  rw [← h, ← h']
  ring

theorem IntAt.mul {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    IntAt P (a * b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  simp only [map_mul, map_add]
  rw [← h, ← h']
  ring

theorem reduction_add {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    redP P (a + b) = redP P a + redP P b := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine redP_eq P (r := s' * r + s * r') (s := s * s')
    (fun hm => (P.isPrime.mem_or_mem hm).elim hs hs') ?_ ?_
  · simp only [map_mul, map_add]
    rw [← h, ← h']
    ring
  · rw [map_add, map_mul, map_mul, map_mul, ← reduction_spec P hs h, ← reduction_spec P hs' h']
    ring

theorem reduction_mul {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    redP P (a * b) = redP P a * redP P b := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine redP_eq P (r := r * r') (s := s * s')
    (fun hm => (P.isPrime.mem_or_mem hm).elim hs hs') ?_ ?_
  · simp only [map_mul, map_add]
    rw [← h, ← h']
    ring
  · rw [map_mul, map_mul, ← reduction_spec P hs h, ← reduction_spec P hs' h']
    ring

theorem redP_osmul {P : HeightOneSpectrum (𝓞 E)} (c : 𝓞 E) {a : E} (ha : IntAt P a) :
    redP P (c • a) = Ideal.Quotient.mk P.asIdeal c * redP P a := by
  rw [Algebra.smul_def, reduction_mul (IntAt.coe P c) ha]
  congr 1
  exact reduction_coe P c

end RedLemmas

section BaseLemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem mem_stdLat (x : Sp E n) : x ∈ stdLat E n ↔ ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]

theorem single_mem_stdLat (i : Fin n) (r : 𝓞 E) : (Pi.single i (algebraMap (𝓞 E) E r) : Sp E n) ∈ stdLat E n := by
  rw [mem_stdLat]
  intro j
  by_cases h : j = i
  · subst h
    exact ⟨r, by simp⟩
  · exact ⟨0, by simp [h]⟩

theorem stdLat_eq_span :
    stdLat E n = Submodule.span (𝓞 E) (Set.range fun i : Fin n => (Pi.single i (1 : E) : Sp E n)) := by
  apply le_antisymm
  · intro x hx
    rw [mem_stdLat] at hx
    choose r hr using hx
    have : x = ∑ i, r i • (Pi.single i (1 : E) : Sp E n) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using single_mem_stdLat (E := E) i 1

theorem stdLat_lattice : Submodule.IsLattice E (stdLat E n) := by
  constructor
  · rw [stdLat_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    simpa using single_mem_stdLat (E := E) i 1

theorem star_coe_mem_one (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ (1 : Submodule (𝓞 E) E) :=
  Submodule.mem_one.2 ⟨RingOfIntegers.mapRingHom (starRingEnd E) r, rfl⟩

theorem hStd_single_left (i : Fin n) (x : Sp E n) : hStd E n (Pi.single i 1) x = x i := by
  rw [hStd_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem stdLat_unimodular : IsUnimodular (hStd E n) (stdLat E n) := by
  change dual (hStd E n) (stdLat E n) = stdLat E n
  ext x
  rw [mem_dual]
  constructor
  · intro H
    rw [mem_stdLat]
    intro i
    have := H (Pi.single i 1) (by simpa using single_mem_stdLat (E := E) i 1)
    rw [hStd_single_left] at this
    exact Submodule.mem_one.1 this
  · intro hx y hy
    rw [mem_stdLat] at hx hy
    rw [hStd_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, hr⟩ := hx i
    obtain ⟨r', hr'⟩ := hy i
    rw [← hr, ← hr', mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (star_coe_mem_one r')

theorem mem_localization_standardLattice (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ localization₂ P.asIdeal (stdLat E n) ↔ ∀ i, IntAt P (x i) := by
  constructor
  · intro hx i
    obtain ⟨s, hs, h⟩ := (mem_locP P _ x).1 hx
    obtain ⟨r, hr⟩ := (mem_stdLat _).1 h i
    exact ⟨r, s, hs, by rw [hr, Pi.smul_apply, Algebra.smul_def]⟩
  · intro H
    have : x = ∑ i, (Pi.single i (x i) : Sp E n) := (Finset.univ_sum_single x).symm
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, s, hs, h⟩ := H i
    refine (mem_locP P _ _).2 ⟨s, hs, ?_⟩
    have e : s • (Pi.single i (x i) : Sp E n) = Pi.single i (algebraMap (𝓞 E) E r) := by
      rw [← Pi.single_smul, Algebra.smul_def, ← h]
    rw [e]
    exact single_mem_stdLat i r

theorem Deco.base_ok [NeZero n] : (Deco.base E n ST SG).Ok where
  lat := stdLat_lattice
  uni := stdLat_unimodular
  f_add P x hx y hy := by
    replace hx : x ∈ localization₂ P.1.asIdeal (stdLat E n) := hx
    replace hy : y ∈ localization₂ P.1.asIdeal (stdLat E n) := hy
    have hxy : x + y ∈ localization₂ P.1.asIdeal (stdLat E n) := Submodule.add_mem _ hx hy
    simp only [Deco.base]
    rw [if_pos hxy, if_pos hx, if_pos hy]
    exact reduction_add ((mem_localization_standardLattice _ _).1 hx _) ((mem_localization_standardLattice _ _).1 hy _)
  f_smul P a x hx := by
    replace hx : x ∈ localization₂ P.1.asIdeal (stdLat E n) := hx
    have hax : a • x ∈ localization₂ P.1.asIdeal (stdLat E n) := Submodule.smul_mem _ a hx
    simp only [Deco.base]
    rw [if_pos hax, if_pos hx]
    exact redP_osmul a ((mem_localization_standardLattice _ _).1 hx _)
  f_off P x hx := by
    replace hx : x ∉ localization₂ P.1.asIdeal (stdLat E n) := hx
    simp only [Deco.base]
    rw [if_neg hx]
  f_ne P := by
    have h1 : (Pi.single (lastIdx n) (algebraMap (𝓞 E) E 1) : Sp E n) ∈ stdLat E n := single_mem_stdLat _ 1
    refine ⟨_, h1, ?_⟩
    simp only [Deco.base]
    rw [if_pos (le_locP _ _ h1), Pi.single_eq_same, reduction_coe, map_one]
    exact one_ne_zero
  be_add w x hx y hy := by
    replace hx : x ∈ localization₂ w.1.asIdeal (stdLat E n) := hx
    replace hy : y ∈ localization₂ w.1.asIdeal (stdLat E n) := hy
    have hxy : x + y ∈ localization₂ w.1.asIdeal (stdLat E n) := Submodule.add_mem _ hx hy
    simp only [Deco.base]
    rw [if_pos hxy, if_pos hx, if_pos hy]
    funext i
    exact reduction_add ((mem_localization_standardLattice _ _).1 hx _) ((mem_localization_standardLattice _ _).1 hy _)
  be_smul w a x hx := by
    replace hx : x ∈ localization₂ w.1.asIdeal (stdLat E n) := hx
    have hax : a • x ∈ localization₂ w.1.asIdeal (stdLat E n) := Submodule.smul_mem _ a hx
    simp only [Deco.base]
    rw [if_pos hax, if_pos hx]
    funext i
    exact redP_osmul a ((mem_localization_standardLattice _ _).1 hx _)
  be_off w x hx := by
    replace hx : x ∉ localization₂ w.1.asIdeal (stdLat E n) := hx
    simp only [Deco.base]
    rw [if_neg hx]
  be_surj w c := by
    choose r hr using fun i => Ideal.Quotient.mk_surjective (c i)
    have h1 : (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) ∈ stdLat E n :=
      (mem_stdLat _).2 fun i => ⟨r i, rfl⟩
    refine ⟨_, h1, ?_⟩
    simp only [Deco.base]
    rw [if_pos (le_locP _ _ h1)]
    funext i
    rw [reduction_coe, hr]
  be_ker w x hx h0 := by
    replace hx : x ∈ stdLat E n := hx
    simp only [Deco.base] at h0
    rw [if_pos (le_locP _ _ hx)] at h0
    have hx' := (mem_stdLat _).1 hx
    choose r hr using hx'
    have hmem : ∀ i, r i ∈ w.1.asIdeal := by
      intro i
      have := congrFun h0 i
      rw [← hr i, reduction_coe] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    have : x = ∑ i, r i • (Pi.single i (algebraMap (𝓞 E) E 1) : Sp E n) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (hmem i) (single_mem_stdLat i 1)

variable (E n ST SG) in

def DecoSet.base [NeZero n] : DecoSet E n ST SG := ⟨Deco.base E n ST SG, Deco.base_ok⟩

theorem Deco.Ok.ext_on {d d' : Deco E n ST SG} (hd : d.Ok) (hd' : d'.Ok) (hN : d.N = d'.N)
    (hf : ∀ (P : ST), ∀ x ∈ d.N, d.f P x = d'.f P x)
    (hbe : ∀ (w : SG), ∀ x ∈ d.N, d.be w x = d'.be w x) : d = d' := by
  ext1
  · exact hN
  · funext P x
    by_cases hx : x ∈ d.at P.1
    · have hx' : x ∈ d'.at P.1 := by
        rw [Deco.at, ← hN]; exact hx
      obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      apply mul_left_cancel₀ (mk_ne_zero hs)
      rw [← hd.f_smul P s x hx, ← hd'.f_smul P s x hx', hf P _ h]
    · have hx' : x ∉ d'.at P.1 := by
        rw [Deco.at, ← hN]; exact hx
      rw [hd.f_off P x hx, hd'.f_off P x hx']
  · funext w x
    by_cases hx : x ∈ d.at w.1
    · have hx' : x ∈ d'.at w.1 := by
        rw [Deco.at, ← hN]; exact hx
      obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have e := hbe w _ h
      rw [hd.be_smul w s x hx, hd'.be_smul w s x hx'] at e
      funext i
      exact mul_left_cancel₀ (mk_ne_zero hs) (congrFun e i)
    · have hx' : x ∉ d'.at w.1 := by
        rw [Deco.at, ← hN]; exact hx
      rw [hd.be_off w x hx, hd'.be_off w x hx']

end BaseLemmas

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.upSet (P : ST) (q : 𝓞 E) (d : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  {d' | Deco.IsUp P q d.1 d'.1}

def DecoSet.dnSet (P : ST) (q : 𝓞 E) (d : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  {d' | Deco.IsDn P q d.1 d'.1}

def DecoSet.up (d : DecoSet E n ST SG) (P : ST) (q : 𝓞 E) (x : Sp E n) : DecoSet E n ST SG :=
  open Classical in if h : (d.1.up P q x).Ok then ⟨_, h⟩ else d

def DecoSet.dn (d : DecoSet E n ST SG) (P : ST) (f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal) :
    DecoSet E n ST SG :=
  open Classical in if h : (d.1.dn P f').Ok then ⟨_, h⟩ else d

def DecoSet.til (pi : 𝓞 E) (d : DecoSet E n ∅ SG) : DecoSet E (n + 1) ST SG :=
  open Classical in if h : (d.1.til (ST := ST) pi).Ok then ⟨_, h⟩ else DecoSet.base E (n + 1) ST SG

end Moves

section Inst

variable (X : Fields) (Pr : Primes X)

abbrev ColDeco (u : Pr.Word) (n : ℕ) : Type := DecoSet X.E n (Pr.vT u) Pr.vGs

abbrev RowDeco (n : ℕ) : Type := DecoSet X.E n ∅ Pr.vGs

variable {X Pr}

def tilD (u : Pr.Word) {n : ℕ} (d : RowDeco X Pr n) : ColDeco X Pr u (n + 1) := DecoSet.til (Pr.piT u) d

def upD (u : Pr.Word) {n : ℕ} (P : Pr.vT u) (d : ColDeco X Pr u n) : Set (ColDeco X Pr u n) :=
  d.upSet P (Pr.T u : 𝓞 X.E)

def dnD (u : Pr.Word) {n : ℕ} (P : Pr.vT u) (d : ColDeco X Pr u n) : Set (ColDeco X Pr u n) :=
  d.dnSet P (Pr.T u : 𝓞 X.E)

end Inst

end Formalism.L2.Col
