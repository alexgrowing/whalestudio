import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

section Points

variable {R : Type} [CommRing R] {X : Scheme.{0}}

structure Pt (s : X ⟶ Sp R) : Type 1 where

  B : Type
  [ring : CommRing B]
  [alg : Algebra R B]

  x : Sp B ⟶ X
  w : x ≫ s = spMap (algebraMap R B)

attribute [instance] Pt.ring Pt.alg

variable {s : X ⟶ Sp R}

@[reducible] def Pt.aff (s : X ⟶ Sp R) (U : X.affineOpens) : Pt s where
  B := CechDR.Sec s U.1
  x := CechDR.affPt s U
  w := CechDR.affPt_w s U

structure Pt.Hom (P Q : Pt s) : Type where

  ρ : P.B →ₐ[R] Q.B
  pt : spMap (ρ : P.B →+* Q.B) ≫ P.x = Q.x

def Pt.affHom (s : X ⟶ Sp R) {U V : X.affineOpens} (h : V.1 ≤ U.1) : (Pt.aff s U).Hom (Pt.aff s V) :=
  ⟨CechDR.Sec.res s h, CechDR.affPt_res s h⟩

def Pt.Hom.id (P : Pt s) : P.Hom P := ⟨AlgHom.id R _, by
  change spMap (RingHom.id _) ≫ _ = _
  rw [Cris.spMap_id, Category.id_comp]⟩

def Pt.Hom.comp {P Q T : Pt s} (φ : P.Hom Q) (ψ : Q.Hom T) : P.Hom T := ⟨ψ.ρ.comp φ.ρ, by
  change spMap ((ψ.ρ : Q.B →+* T.B).comp (φ.ρ : P.B →+* Q.B)) ≫ _ = _
  rw [Cris.spMap_comp, Category.assoc, φ.pt, ψ.pt]⟩

def Pt.In (P : Pt s) (U : X.Opens) : Prop := ⊤ ≤ P.x ⁻¹ᵁ U

theorem Pt.In.map {P Q : Pt s} {U : X.Opens} (h : P.In U) (φ : P.Hom Q) : Q.In U := by
  change ⊤ ≤ Q.x ⁻¹ᵁ U
  rw [← φ.pt]
  exact fun y _ ↦ h trivial

theorem Pt.In.mono {P : Pt s} {U V : X.Opens} (h : P.In U) (e : U ≤ V) : P.In V := fun _ hy ↦ e (h hy)

theorem Pt.In.inf {P : Pt s} {U V : X.Opens} (h : P.In U) (h' : P.In V) : P.In (U ⊓ V) := fun _ hy ↦ ⟨h hy, h' hy⟩

abbrev Pt.triv (P : Pt s) : Thick (dp0 R) s := Thick.triv P.B P.x P.w

def Pt.Hom.triv {P Q : Pt s} (φ : P.Hom Q) : P.triv ⟶ Q.triv := Thick.trivHom φ.ρ φ.pt

abbrev Pt.ext (P : Pt s) : Thick (dp0 R) s := (SqExt.ofModule R P.B P.B).thick P.x P.w

def dualAlg {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (ρ : B →ₐ[R] B') :
    DualNumber B →ₐ[R] DualNumber B' :=
  { dualMap (ρ : B →+* B') with
    commutes' := fun r ↦ by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl'] }

@[simp] theorem fst_dualAlg {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (ρ : B →ₐ[R] B')
    (c : DualNumber B) : (dualAlg ρ c).fst = ρ c.fst := by
  simp [dualAlg, dualMap]

@[simp] theorem snd_dualAlg {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (ρ : B →ₐ[R] B')
    (c : DualNumber B) : (dualAlg ρ c).snd = ρ c.snd := by
  simp [dualAlg, dualMap]

def Pt.Hom.dual {P Q : Pt s} (φ : P.Hom Q) : P.ext ⟶ Q.ext :=
  SqExt.thickHom (SqExt.ofModule R P.B P.B) (SqExt.ofModule R Q.B Q.B) (dualAlg φ.ρ) φ.ρ
    (fun c ↦ (fst_dualAlg φ.ρ c).symm) P.w Q.w φ.pt

def Pt.sec (P : Pt s) : P.triv ⟶ P.ext :=
  (SqExt.ofModule R P.B P.B).secHom P.w (TrivSqZeroExt.inlAlgHom R P.B P.B) fun _ ↦ rfl

abbrev PtFn (s : X ⟶ Sp R) : Type 1 := ∀ P : Pt s, P.B

def IsNat (U : X.Opens) (F : PtFn s) : Prop := ∀ (P Q : Pt s) (φ : P.Hom Q), P.In U → F Q = φ.ρ (F P)

def IsRep {J : Type} (W : J → X.Opens) (c : Z1 (O (dp0 R) s)) (F : J → J → PtFn s) : Prop :=
  ∃ G : J → PtFn s, (∀ j (P Q : Pt s) (φ : P.Hom Q), P.In (W j) → ev c φ.triv = G j Q - φ.ρ (G j P)) ∧
    ∀ j j' (P : Pt s), P.In (W j) → P.In (W j') → G j P - G j' P = F j j' P

theorem IsRep.add {J : Type} {W : J → X.Opens} {c c' : Z1 (O (dp0 R) s)} {F F' : J → J → PtFn s}
    (h : IsRep W c F) (h' : IsRep W c' F') : IsRep W (c + c') (F + F') := by
  obtain ⟨G, hG, hF⟩ := h
  obtain ⟨G', hG', hF'⟩ := h'
  refine ⟨G + G', fun j P Q φ hP ↦ ?_, fun j j' P hj hj' ↦ ?_⟩
  · change ev c φ.triv + ev c' φ.triv = _
    rw [hG j P Q φ hP, hG' j P Q φ hP]
    simp only [Pi.add_apply, map_add]
    abel
  · simp only [Pi.add_apply]
    rw [← hF j j' P hj hj', ← hF' j j' P hj hj']
    abel

theorem IsRep.smul {J : Type} {W : J → X.Opens} {c : Z1 (O (dp0 R) s)} {F : J → J → PtFn s}
    (h : IsRep W c F) (r : R) : IsRep W (r • c) (r • F) := by
  obtain ⟨G, hG, hF⟩ := h
  refine ⟨r • G, fun j P Q φ hP ↦ ?_, fun j j' P hj hj' ↦ ?_⟩
  · change r • ev c φ.triv = _
    rw [hG j P Q φ hP]
    simp only [Pi.smul_apply, map_smul, smul_sub]
  · simp only [Pi.smul_apply]
    rw [← hF j j' P hj hj', smul_sub]

theorem IsRep.zero {J : Type} (W : J → X.Opens) : IsRep (s := s) W 0 0 := ⟨0, fun j P Q φ _ ↦ by simp [ev], fun _ _ _ _ _ ↦ by simp⟩

theorem IsRep.sum {J I : Type} {W : J → X.Opens} (t : Finset I) {c : I → Z1 (O (dp0 R) s)}
    {F : I → J → J → PtFn s} (h : ∀ k ∈ t, IsRep W (c k) (F k)) : IsRep W (∑ k ∈ t, c k) (∑ k ∈ t, F k) := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _
    simpa only [Finset.sum_empty] using IsRep.zero W
  · intro a t ha ih h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add (ih fun k hk ↦ h k (Finset.mem_insert_of_mem hk))

theorem IsRep.refine {J J' : Type} {W : J → X.Opens} {W' : J' → X.Opens} (τ : J' → J) (hτ : ∀ j, W' j ≤ W (τ j))
    {c : Z1 (O (dp0 R) s)} {F : J → J → PtFn s} (h : IsRep W c F) :
    IsRep W' c fun j j' ↦ F (τ j) (τ j') := by
  obtain ⟨G, hG, hF⟩ := h
  exact ⟨fun j ↦ G (τ j), fun j P Q φ hP ↦ hG (τ j) P Q φ (hP.mono (hτ j)),
    fun j j' P hj hj' ↦ hF (τ j) (τ j') P (hj.mono (hτ j)) (hj'.mono (hτ j'))⟩

theorem IsRep.congr {J : Type} {W : J → X.Opens} {c : Z1 (O (dp0 R) s)} {F F' : J → J → PtFn s}
    (h : IsRep W c F) (e : ∀ j j' (P : Pt s), P.In (W j) → P.In (W j') → F j j' P = F' j j' P) : IsRep W c F' := by
  obtain ⟨G, hG, hF⟩ := h
  exact ⟨G, hG, fun j j' P hj hj' ↦ (hF j j' P hj hj').trans (e j j' P hj hj')⟩

def idLift (T : Thick (dp0 R) s) (y : Sp T.B ⟶ X) (hy : y ≫ s = spMap (algebraMap R T.B))
    (e : spMap T.π ≫ y = T.x) : Thick.triv T.B y hy ⟶ T :=
  Thick.trivHom (AlgHom.id R _) e

end Points

section Transl

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem dualMap_comp_algebraMap {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') :
    (dualMap φ).comp (algebraMap B (DualNumber B)) = (algebraMap B' (DualNumber B')).comp φ := by
  ext b <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']

theorem dualMap_comp_dualMap {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] (φ : B →+* B')
    (ψ : B' →+* B'') : (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) := by
  ext c <;> simp [dualMap]

theorem exists_isTransl {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ)
    (v : epsR K ⟶ A) : ∃ w, IsTransl φ x v w := by
  have e1 : (spMap (algebraMap B (DualNumber B)) ≫ x) ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp φ) := by
    rw [Category.assoc, hx, ← Cris.spMap_comp]
  have e2 : (spMap (dualMap φ) ≫ v.left) ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp φ) := by
    rw [Category.assoc, Over.w v, ← dualMap_comp_algebraMap, Cris.spMap_comp] <;> rfl
  exact ⟨_, Over.homMk _ e1, Over.homMk _ e2, rfl, rfl, rfl⟩

theorem IsTransl.unique {B : Type} [CommRing B] {φ : K →+* B} {x : Sp B ⟶ A.left} {v : epsR K ⟶ A}
    {w w' : Sp (DualNumber B) ⟶ A.left} (h : IsTransl φ x v w) (h' : IsTransl φ x v w') : w = w' := by
  obtain ⟨x₁, v₁, hx₁, hv₁, rfl⟩ := h
  obtain ⟨x₂, v₂, hx₂, hv₂, rfl⟩ := h'
  have e1 : x₁ = x₂ := Over.OverMorphism.ext (hx₁.trans hx₂.symm)
  have e2 : v₁ = v₂ := Over.OverMorphism.ext (hv₁.trans hv₂.symm)
  rw [e1, e2]

theorem IsTransl.w {B : Type} [CommRing B] {φ : K →+* B} {x : Sp B ⟶ A.left} {v : epsR K ⟶ A}
    {w : Sp (DualNumber B) ⟶ A.left} (h : IsTransl φ x v w) :
    w ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp φ) := by
  obtain ⟨x', v', -, -, rfl⟩ := h
  exact Over.w (x' * v')

theorem IsTransl.map {B B' : Type} [CommRing B] [CommRing B'] {φ : K →+* B} {x : Sp B ⟶ A.left} {v : epsR K ⟶ A}
    {w : Sp (DualNumber B) ⟶ A.left} (h : IsTransl φ x v w) (ρ : B →+* B') :
    IsTransl (ρ.comp φ) (spMap ρ ≫ x) v (spMap (dualMap ρ) ≫ w) := by
  obtain ⟨x', v', hx', hv', rfl⟩ := h
  have eg : spMap (dualMap ρ) ≫ spMap ((algebraMap B (DualNumber B)).comp φ) =
      spMap ((algebraMap B' (DualNumber B')).comp (ρ.comp φ)) := by
    rw [← Cris.spMap_comp]
    congr 1
    ext b <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']
  let g : Over.mk (spMap ((algebraMap B' (DualNumber B')).comp (ρ.comp φ))) ⟶
      Over.mk (spMap ((algebraMap B (DualNumber B)).comp φ)) := Over.homMk (spMap (dualMap ρ)) eg
  refine ⟨g ≫ x', g ≫ v', ?_, ?_, ?_⟩
  · change spMap (dualMap ρ) ≫ x'.left = _
    rw [hx', ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp, dualMap_comp_algebraMap]
  · change spMap (dualMap ρ) ≫ v'.left = _
    rw [hv', ← Category.assoc, ← Cris.spMap_comp, dualMap_comp_dualMap]
  · have e : g ≫ x' * g ≫ v' = g ≫ (x' * v') := by
      first
        | exact (comp_mul g x' v').symm
        | exact (Hom.comp_mul g x' v').symm
        | exact (MonObj.comp_mul g x' v').symm
        | simp
    rw [e]
    rfl

theorem IsTransl.red {B : Type} [CommRing B] {φ : K →+* B} {x : Sp B ⟶ A.left} {v : epsR K ⟶ A}
    {w : Sp (DualNumber B) ⟶ A.left} (h : IsTransl φ x v w) (hv : IsTangent v) :
    spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x := by
  obtain ⟨x', v', hx', hv', rfl⟩ := h
  have eg : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap ((algebraMap B (DualNumber B)).comp φ) =
      spMap φ := by
    rw [← Cris.spMap_comp]
    congr 1 <;> (ext b; simp [TrivSqZeroExt.algebraMap_eq_inl'])
  let g : Over.mk (spMap φ) ⟶ Over.mk (spMap ((algebraMap B (DualNumber B)).comp φ)) := Over.homMk _ eg
  have e1 : g ≫ v' = 1 := by
    apply Over.OverMorphism.ext
    change spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ v'.left = (toUnit (Over.mk (spMap φ)) ≫ η).left
    rw [Over.comp_left, hv', ← Category.assoc, ← Cris.spMap_comp]
    have e3 : (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMap φ) =
        φ.comp (TrivSqZeroExt.fstHom K K K).toRingHom := by
      exact RingHom.ext fun c ↦ by simp [dualMap]
    rw [e3, Cris.spMap_comp, Category.assoc, hv]
    congr 1
    all_goals first
      | exact (Over.toUnit_left _).symm
      | exact (Over.w (toUnit (Over.mk (spMap φ)))).symm.trans (Category.comp_id _)
      | (have h1 := Over.w (toUnit (Over.mk (spMap φ))); simpa using h1.symm)
  have e : g ≫ x' * g ≫ v' = g ≫ (x' * v') := by
    first
          | exact (comp_mul g x' v').symm
          | exact (Hom.comp_mul g x' v').symm
          | exact (MonObj.comp_mul g x' v').symm
          | simp
  have e4 : (TrivSqZeroExt.fstHom B B B).toRingHom.comp (algebraMap B (DualNumber B)) = RingHom.id B := by
    ext b
    simp [TrivSqZeroExt.algebraMap_eq_inl']
  calc spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (x' * v').left = (g ≫ (x' * v')).left := rfl
    _ = (g ≫ x' * g ≫ v').left := by rw [e]
    _ = (g ≫ x').left := by rw [e1, _root_.mul_one]
    _ = x := by
      change spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ x'.left = x
      rw [hx', ← Category.assoc, ← Cris.spMap_comp, e4, Cris.spMap_id, Category.id_comp]

abbrev GPt (A : Over (Sp K)) : Type 1 := Pt (A.hom ≫ 𝟙 (Sp K))

def Pt.trx (P : GPt A) (v : epsR K ⟶ A) : Sp (DualNumber P.B) ⟶ A.left :=
  (exists_isTransl (algebraMap K P.B) P.x ((congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w) v).choose

theorem Pt.isTransl_trx (P : GPt A) (v : epsR K ⟶ A) : IsTransl (algebraMap K P.B) P.x v (P.trx v) := (exists_isTransl (algebraMap K P.B) P.x ((congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w) v).choose_spec

@[reducible] def Pt.tr (P : GPt A) (v : epsR K ⟶ A) : GPt A where
  B := DualNumber P.B
  x := P.trx v
  w := (congrArg (P.trx v ≫ ·) (Category.comp_id _)).trans (P.isTransl_trx v).w

def Pt.Hom.tr {P Q : GPt A} (φ : P.Hom Q) (v : epsR K ⟶ A) : (P.tr v).Hom (Q.tr v) :=
  ⟨dualAlg φ.ρ, by
    have h := (P.isTransl_trx v).map (φ.ρ : P.B →+* Q.B)
    rw [φ.pt, φ.ρ.comp_algebraMap] at h
    exact h.unique (Q.isTransl_trx v)⟩

def Pt.red (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) : (P.tr v).Hom P :=
  ⟨TrivSqZeroExt.fstHom K P.B P.B, (P.isTransl_trx v).red hv⟩

theorem Pt.In.tr {P : GPt A} {U : A.left.Opens} (h : P.In U) {v : epsR K ⟶ A} (hv : IsTangent v) :
    (P.tr v).In U := by
  intro y _
  have key : ∀ p : PrimeSpectrum (DualNumber P.B),
      PrimeSpectrum.comap ((algebraMap P.B (DualNumber P.B)).comp (TrivSqZeroExt.fstHom P.B P.B P.B).toRingHom) p = p := by
    intro p
    apply PrimeSpectrum.ext
    ext c
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.comp_apply]
    have hn : (TrivSqZeroExt.inr c.snd : DualNumber P.B) ∈ p.asIdeal :=
      p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact p.asIdeal.zero_mem)
    have hc : TrivSqZeroExt.inl c.fst + TrivSqZeroExt.inr c.snd = c := TrivSqZeroExt.inl_fst_add_inr_snd_eq c
    have e5 : (algebraMap P.B (DualNumber P.B)) ((TrivSqZeroExt.fstHom P.B P.B P.B).toRingHom c) =
        TrivSqZeroExt.inl c.fst := by
      simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [e5]
    constructor
    · intro h1
      rw [← hc]
      exact add_mem h1 hn
    · intro h1
      have e6 : c - TrivSqZeroExt.inr c.snd = TrivSqZeroExt.inl c.fst := by
        rw [sub_eq_iff_eq_add, hc]
      rw [← e6]
      exact sub_mem h1 hn
  have hy : (spMap (algebraMap P.B (DualNumber P.B)) ≫ spMap (TrivSqZeroExt.fstHom P.B P.B P.B).toRingHom).base y = y := by
    rw [← Cris.spMap_comp]
    first
      | exact key y
      | (simp only [spMap]; exact key y)
      | (simp only [spMap, Scheme.Spec_map_base]; exact key y)
      | (simp [spMap]; exact key y)
      | (simp only [spMap]; done)
  have h1 : (spMap (TrivSqZeroExt.fstHom P.B P.B P.B).toRingHom ≫ P.trx v).base
      ((spMap (algebraMap P.B (DualNumber P.B))).base y) ∈ U := by
    rw [(P.isTransl_trx v).red hv]
    exact h trivial
  rw [← hy]
  simpa using h1

def Pt.tan (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) : (P.tr v).triv ⟶ P.ext :=
  Thick.trivHom (AlgHom.id K _) ((P.isTransl_trx v).red hv)

def dlog (L : LB A.left) (v : epsR K ⟶ A) (i i' : L.ι) : PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ (valR (Pt.trx P v) _ (L.g i i').val).snd * valR P.x _ (L.g i i')⁻¹.val

abbrev Small {I : Type} (U : I → A.left.Opens) : Type 1 :=
  (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) U).FullSubcategory

abbrev OSmall {I : Type} (U : I → A.left.Opens) : Small U ⥤ CommAlgCat.{0} K :=
  (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) U).ι ⋙ O (dp0 K) (A.hom ≫ 𝟙 (Sp K))

def ev2 {I : Type} {U : I → A.left.Opens} (z : C2 (OSmall U)) {T T' T'' : Thick (dp0 K) (A.hom ≫ 𝟙 (Sp K))}
    (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : ∃ i, ⊤ ≤ T.x ⁻¹ᵁ U i) : T''.B :=
  z ⟨T, h⟩ ⟨T', h.imp fun _ ↦ φ.le_preimage⟩ ⟨T'', h.imp fun _ e ↦ ψ.le_preimage (φ.le_preimage e)⟩ ⟨φ⟩ ⟨ψ⟩

def prism {I : Type} {U : I → A.left.Opens} (z : C2 (OSmall U)) {v : epsR K ⟶ A} (hv : IsTangent v)
    {P Q : GPt A} (φ : P.Hom Q) (h : ∃ i, P.In (U i)) : Q.B :=
  TrivSqZeroExt.snd (R := Q.B) ((ev2 z φ.triv Q.sec h - ev2 z P.sec φ.dual h) -
    (ev2 z (φ.tr v).triv (Q.tan hv) (h.imp fun _ e ↦ e.tr hv) -
      ev2 z (P.tan hv) φ.dual (h.imp fun _ e ↦ e.tr hv)))

end Transl

section Deform

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A']
  {i : A.left ⟶ A'.left}

theorem fibMor (h : IsGrpPullback A A' (DeRham.epsRed K) i) : GrpMor (dp0 (DualNumber K)) (𝟙 _) A' (dp0 K) (𝟙 _) A
    (TrivSqZeroExt.fstHom K K K).toRingHom (DeRham.epsRed K) i := GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
  (by rw [Category.comp_id, Category.id_comp] <;> rfl) h

omit [GrpObj A] in

@[reducible] def Pt.eps (P : GPt A) : Thick (epsDP K) (A.hom ≫ DeRham.epsRed K) where
  B := DualNumber P.B
  alg := (dualMap (algebraMap K P.B)).toAlgebra
  J := RingHom.ker (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B)
  δ := divided₂ (SqExt.ofModule K P.B P.B).sq
  nil := isDPNilpotent_squareZero _
  dp := isDPMorphism_sqDP (SqExt.dual K).sq (SqExt.ofModule K P.B P.B).sq _ fun a ha ↦ by
    have ha' : a.fst = 0 := ha
    change (dualMap (algebraMap K P.B) a).fst = 0
    simp [dualMap, ha']
  B₀ := P.B
  π := (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B)
  surj := fun b ↦ ⟨TrivSqZeroExt.inl b, rfl⟩
  ker := fun _ ↦ Iff.rfl
  x := P.x
  w := by
    have e : P.x ≫ A.hom = spMap (algebraMap K P.B) :=
      (congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w
    rw [← Category.assoc, e, ← Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun c ↦ (add_zero _).symm)

def IsLift (i : A.left ⟶ A'.left) (P : GPt A) (y : Sp (DualNumber P.B) ⟶ A'.left) : Prop :=
  y ≫ A'.hom ≫ 𝟙 _ = spMap (dualMap (algebraMap K P.B)) ∧
    spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ y = P.x ≫ i

def liftVal (h : IsGrpPullback A A' (DeRham.epsRed K) i) (f : Z1 (O (dp0 (DualNumber K)) (A'.hom ≫ 𝟙 _))) {P : GPt A}
    {y : Sp (DualNumber P.B) ⟶ A'.left} (hy : IsLift i P y) : DualNumber P.B :=
  ev f (idLift ((liftMor (epsDP K) h).isMor.obj P.eps) y hy.1 hy.2)

end Deform

end GlobalTheory.CechKS
