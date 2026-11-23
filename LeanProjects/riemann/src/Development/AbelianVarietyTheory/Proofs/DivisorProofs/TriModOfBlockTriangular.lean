import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open Filter Topology

namespace GlobalTheory.LatChain

section Alg

variable {K : Type} [Field K] {N : ℕ}

def TriMod (R : Subring K) (h : K) (A : Matrix (Fin N) (Fin N) K) (d : Fin N → K) : Prop :=
  ∃ E ∈ R.matrix, (A - h • E).BlockTriangular id ∧ ∀ i, (A - h • E) i i = d i

def Small (R : Subring K) (h : K) : Prop := h ∈ R ∧ ∀ r ∈ R, ∃ s ∈ R, (1 + h * r) * s = 1

def Fr (R : Subring K) (M : Matrix (Fin N) (Fin N) K) : Prop := M.det ≠ 0 ∧ M ∈ R.matrix ∧ M⁻¹ ∈ R.matrix

def Lc (R : Subring K) {σ : Type} [Fintype σ] (f : σ → K) (a : K) : Prop :=
  ∃ α : σ → K, (∀ s, α s ∈ R) ∧ a = ∑ s, α s * f s

def Gen (R : Subring K) {σ : Type} [Fintype σ] (f : σ → K) (η : K) : Prop :=
  η ≠ 0 ∧ (∀ s, f s / η ∈ R) ∧ Lc R f η

def gens (γ : K) (y : Fin N → K) (i : Fin (N + 1)) : Option (Fin N) → K :=
  fun s => s.elim γ fun k => if (i : ℕ) ≤ k then y k else 0

def dg (j : Fin N) (γ : K) : Matrix (Fin N) (Fin N) K := Matrix.diagonal (Function.update 1 j γ)

def PInt (p : ℕ) (f : K) : Prop := ∃ r : ℕ, r.Coprime p ∧ IsIntegral ℤ ((r : K) * f)

theorem TriMod.of_mul {R : Subring K} {h b : K} {A : Matrix (Fin N) (Fin N) K} {d : Fin N → K} (H : TriMod R (h * b) A d)
    (hb : b ∈ R) : TriMod R h A d := by
  obtain ⟨E, hE, h₁, h₂⟩ := H
  refine ⟨b • E, fun i j => R.mul_mem hb (hE i j), ?_, ?_⟩ <;> rwa [smul_smul]

theorem Fr.mul {R : Subring K} {A B : Matrix (Fin N) (Fin N) K} (hA : Fr R A) (hB : Fr R B) : Fr R (A * B) :=
  ⟨by rw [Matrix.det_mul]; exact mul_ne_zero hA.1 hB.1, mul_mem hA.2.1 hB.2.1,
    by rw [Matrix.mul_inv_rev]; exact mul_mem hB.2.2 hA.2.2⟩

theorem Fr.inv {R : Subring K} {A : Matrix (Fin N) (Fin N) K} (hA : Fr R A) : Fr R A⁻¹ :=
  ⟨by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hA.1, hA.2.2,
    by rw [Matrix.nonsing_inv_nonsing_inv _ hA.1.isUnit]; exact hA.2.1⟩

variable {K' : Type} [Field K'] {R : Subring K} {R' : Subring K'} (φ : K →+* K') (hφ : ∀ f ∈ R, φ f ∈ R')
include hφ

theorem TriMod.map {h : K} {A : Matrix (Fin N) (Fin N) K} {d : Fin N → K} (H : TriMod R h A d) :
    TriMod R' (φ h) (A.map φ) fun i => φ (d i) := by
  obtain ⟨E, hE, h₁, h₂⟩ := H
  have e (i j) : (A.map φ - φ h • E.map φ) i j = φ ((A - h • E) i j) := by simp
  exact ⟨E.map φ, fun i j => hφ _ (hE i j), fun i j hij => by rw [e, h₁ hij, map_zero], fun i => by rw [e, h₂]⟩

theorem Fr.map {A : Matrix (Fin N) (Fin N) K} (H : Fr R A) : Fr R' (A.map φ) :=
  ⟨by rw [show (A.map φ).det = φ A.det from (RingHom.map_det φ A).symm]; exact (map_ne_zero φ).2 H.1,
    fun i j => hφ _ (H.2.1 i j), by rw [GlobalTheory.FrameGlue.Pull.matrix_map_inv]; exact fun i j => hφ _ (H.2.2 i j)⟩

end Alg

section Sch

variable {X : Scheme.{0}} [IsIntegral X] {N : ℕ}

def Ov (p : ℕ) {X : Scheme.{0}} (x : X) : Prop := ¬ IsUnit (p : X.presheaf.stalk x)

def loc (x : X) : Subring X.functionField := (algebraMap (X.presheaf.stalk x) X.functionField).range

theorem mem_loc {x : X} {f : X.functionField} : f ∈ loc x ↔ RegAt x f := Iff.rfl

theorem eventually_regAt {x : X} {f : X.functionField} (h : RegAt x f) : ∀ᶠ z in 𝓝 x, RegAt z f := by
  obtain ⟨U, hx, a, rfl⟩ := h.exists_fnOf
  exact Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun z hz => regAt_fnOf hz _ a

theorem eventually_unitAt {x : X} {f : X.functionField} (h : UnitAt x f) : ∀ᶠ z in 𝓝 x, UnitAt z f := by
  obtain ⟨U, hx, hU⟩ := h.exists_nhds
  exact Filter.eventually_of_mem (U.isOpen.mem_nhds hx) hU

theorem eventually_mem_matrix {x : X} {M : Matrix (Fin N) (Fin N) X.functionField} (h : M ∈ (loc x).matrix) :
    ∀ᶠ z in 𝓝 x, M ∈ (loc z).matrix := by
  have : ∀ᶠ z in 𝓝 x, ∀ i j, RegAt z (M i j) :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_regAt (h i j)
  exact this

theorem Fr.eventually {x : X} {M : Matrix (Fin N) (Fin N) X.functionField} (h : Fr (loc x) M) :
    ∀ᶠ z in 𝓝 x, Fr (loc z) M :=
  ((eventually_mem_matrix h.2.1).and (eventually_mem_matrix h.2.2)).mono fun _ hz => ⟨h.1, hz⟩

theorem small_pow {p : ℕ} {x : X} (hx : Ov p x) (k : ℕ) : Small (loc x) ((p : X.functionField) ^ (k + 1)) := by
  refine ⟨pow_mem (natCast_mem _ p) _, ?_⟩
  rintro _ ⟨r, rfl⟩
  have h : IsUnit (1 + (p : X.presheaf.stalk x) ^ (k + 1) * r) := by
    refine (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right fun h => hx ?_
    rw [sub_add_cancel_left, IsUnit.neg_iff, pow_succ', mul_assoc] at h
    exact isUnit_of_mul_isUnit_left h
  obtain ⟨s, hs⟩ := h.exists_right_inv
  refine ⟨_, ⟨s, rfl⟩, ?_⟩
  have := congrArg (algebraMap _ X.functionField) hs
  simpa using this

def Coh (p k : ℕ) (M : X → Matrix (Fin N) (Fin N) X.functionField) (c : X → Fin N → X.functionFieldˣ) : Prop :=
  ∀ x, Ov p x → Fr (loc x) (M x) ∧ ∀ᶠ z in 𝓝 x, Ov p z →
    TriMod (loc z) ((p : X.functionField) ^ k) ((M x)⁻¹ * M z) fun i => (c x i : X.functionField) / c z i

def Cross (p k : ℕ) (M M' : X → Matrix (Fin N) (Fin N) X.functionField) (c c' : X → Fin N → X.functionFieldˣ)
    (P : Matrix (Fin N) (Fin N) X.functionField) : Prop :=
  ∀ x, Ov p x → Fr (loc x) (M x) ∧ Fr (loc x) (M' x) ∧ ∀ᶠ z in 𝓝 x, Ov p z →
    TriMod (loc z) ((p : X.functionField) ^ k) ((M' x)⁻¹ * P * M z) (fun i => (c' x i : X.functionField) / c z i) ∧
    TriMod (loc z) ((p : X.functionField) ^ k) ((M' z)⁻¹ * P * M x) fun i => (c' z i : X.functionField) / c x i

def VEq (p : ℕ) (η : X → X.functionFieldˣ) : Prop :=
  ∀ x, Ov p x → RegAt x (η x : X.functionField) ∧ (∃ a : ℕ, RegAt x ((p : X.functionField) ^ a / η x)) ∧
    ∀ᶠ z in 𝓝 x, Ov p z → UnitAt z ((η x : X.functionField) / η z)

def TrivOn (p : ℕ) (e b : X → X.functionField) : Prop :=
  ∃ t : X → X.functionFieldˣ, ∀ x, Ov p x → (¬ UnitAt x (e x) → UnitAt x (t x * b x)) ∧
    ∀ᶠ z in 𝓝 x, Ov p z → ¬ UnitAt z (e z) → RegAt z (((t x : X.functionField) / t z - 1) / e z)

def Link (p : ℕ) (c c' : X → Fin N → X.functionFieldˣ) : Prop :=
  ∃ (η : X → Fin (N + 1) → X.functionFieldˣ) (γ : X.functionFieldˣ), (∀ j, VEq p fun x => η x j) ∧
    (∀ x, Ov p x → UnitAt x (η x 0 : X.functionField) ∧ UnitAt x ((η x (Fin.last N) : X.functionField) / γ) ∧
      ∀ i : Fin N, RegAt x ((η x i.succ : X.functionField) / η x i.castSucc) ∧
        UnitAt x ((c' x i : X.functionField) / c x i / ((η x i.succ : X.functionField) / η x i.castSucc))) ∧
    ∀ i : Fin N, TrivOn p (fun x => (η x i.succ : X.functionField) / η x i.castSucc)
      fun x => (c x i : X.functionField) / η x i.castSucc

theorem link_of_unitAt {p : ℕ} {c c' : X → Fin N → X.functionFieldˣ}
    (h : ∀ x, Ov p x → ∀ i, UnitAt x ((c' x i : X.functionField) / c x i)) : Link p c c' := by
  refine ⟨fun _ _ => 1, 1, fun j x _ => ⟨(unitAt_one x).regAt, ⟨0, by simpa using (unitAt_one x).regAt⟩,
    .of_forall fun z _ => by simpa using unitAt_one z⟩, fun x hx => ⟨unitAt_one x, by simpa using unitAt_one x,
      fun i => ⟨by simpa using (unitAt_one x).regAt, by simpa using h x hx i⟩⟩, fun i => ⟨fun _ => 1, fun x _ =>
        ⟨fun hn => absurd (by simpa using unitAt_one x) hn, .of_forall fun z _ hn => absurd (by simpa using unitAt_one z) hn⟩⟩⟩

variable {X' X'' : Scheme.{0}} [IsIntegral X'] [IsIntegral X'']

def pf (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) (c : X → Fin N → X.functionFieldˣ) :
    X' → Fin N → X'.functionFieldˣ := fun x i => Units.map (SmallSec.fnMap π hπ).toMonoidHom (c (π x) i)

def pm (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) (M : X → Matrix (Fin N) (Fin N) X.functionField) :
    X' → Matrix (Fin N) (Fin N) X'.functionField := fun x => (M (π x)).map (SmallSec.fnMap π hπ)

@[simp] theorem val_pf (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) (c : X → Fin N → X.functionFieldˣ) (x : X')
    (i : Fin N) : (pf π hπ c x i : X'.functionField) = SmallSec.fnMap π hπ (c (π x) i) := rfl

theorem pf_comp (a : X'' ⟶ X') (b : X' ⟶ X) (ha : a (genericPoint X'') ⤳ genericPoint X')
    (hb : b (genericPoint X') ⤳ genericPoint X) (hab : (a ≫ b) (genericPoint X'') ⤳ genericPoint X)
    (c : X → Fin N → X.functionFieldˣ) : pf (a ≫ b) hab c = pf a ha (pf b hb c) :=
  funext fun x => funext fun i => Units.ext (ProjSpace.fnMap_comp a b ha hb hab _)

theorem pm_comp (a : X'' ⟶ X') (b : X' ⟶ X) (ha : a (genericPoint X'') ⤳ genericPoint X')
    (hb : b (genericPoint X') ⤳ genericPoint X) (hab : (a ≫ b) (genericPoint X'') ⤳ genericPoint X)
    (M : X → Matrix (Fin N) (Fin N) X.functionField) : pm (a ≫ b) hab M = pm a ha (pm b hb M) :=
  funext fun x => Matrix.ext fun i j => ProjSpace.fnMap_comp a b ha hb hab _

section Pull

open GlobalTheory.FrameGlue.Pull

variable (π : X' ⟶ X) (hπ : π (genericPoint X') ⤳ genericPoint X) {p : ℕ}

omit [IsIntegral X] [IsIntegral X'] in

theorem Ov.map {x : X'} (h : Ov p x) : Ov p (π x) := fun hu => h (by simpa using hu.map (π.stalkMap x).hom)

theorem map_mem_loc (x : X') : ∀ f ∈ loc (π x), SmallSec.fnMap π hπ f ∈ loc x := fun _ h => regAt_fnMap π hπ h

theorem Coh.pull {k : ℕ} {M : X → Matrix (Fin N) (Fin N) X.functionField} {c : X → Fin N → X.functionFieldˣ}
    (h : Coh p k M c) : Coh p k (pm π hπ M) (pf π hπ c) := fun x hx => by
  obtain ⟨h₁, h₂⟩ := h _ (hx.map π)
  refine ⟨h₁.map _ (map_mem_loc π hπ x), (π.continuous.tendsto x).eventually h₂ |>.mono fun z hz hz' => ?_⟩
  have := (hz (hz'.map π)).map _ (map_mem_loc π hπ z)
  rw [Matrix.map_mul, ← matrix_map_inv, map_pow, map_natCast] at this
  (have H := this; simp only [map_div₀] at H; exact H)

theorem VEq.pull {η : X → X.functionFieldˣ} (h : VEq p η) :
    VEq p fun x => Units.map (SmallSec.fnMap π hπ).toMonoidHom (η (π x)) := fun x hx => by
  obtain ⟨h₁, ⟨a, h₂⟩, h₃⟩ := h _ (hx.map π)
  refine ⟨regAt_fnMap π hπ h₁, ⟨a, ?_⟩, (π.continuous.tendsto x).eventually h₃ |>.mono fun z hz hz' => ?_⟩
  · (have H := regAt_fnMap π hπ h₂; simp only [map_div₀, map_pow, map_natCast] at H; exact H)
  · (have H := unitAt_fnMap π hπ (hz (hz'.map π)); simp only [map_div₀] at H; exact H)

theorem TrivOn.pull {e b : X → X.functionField} (h : TrivOn p e b) :
    TrivOn p (fun x => SmallSec.fnMap π hπ (e (π x))) fun x => SmallSec.fnMap π hπ (b (π x)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨fun x => Units.map (SmallSec.fnMap π hπ).toMonoidHom (t (π x)), fun x hx => ?_⟩
  obtain ⟨h₁, h₂⟩ := ht _ (hx.map π)
  refine ⟨fun hn => ?_, (π.continuous.tendsto x).eventually h₂ |>.mono fun z hz hz' hn => ?_⟩
  · (have H := unitAt_fnMap π hπ (h₁ fun hu => hn (unitAt_fnMap π hπ hu)); simp only [map_mul] at H; exact H)
  · (have H := regAt_fnMap π hπ (hz (hz'.map π) fun hu => hn (unitAt_fnMap π hπ hu)); simp only [map_div₀, map_sub, map_one] at H; exact H)

theorem Link.pull {c c' : X → Fin N → X.functionFieldˣ} (h : Link p c c') : Link p (pf π hπ c) (pf π hπ c') := by
  obtain ⟨η, γ, h₁, h₂, h₃⟩ := h
  refine ⟨pf π hπ η, Units.map (SmallSec.fnMap π hπ).toMonoidHom γ, fun j => (h₁ j).pull π hπ, fun x hx => ?_,
    fun i => by (have H := (h₃ i).pull π hπ; simp only [map_div₀] at H; exact H)⟩
  obtain ⟨a, b, d⟩ := h₂ _ (hx.map π)
  refine ⟨unitAt_fnMap π hπ a, by (have H := unitAt_fnMap π hπ b; simp only [map_div₀] at H; exact H), fun i => ⟨?_, ?_⟩⟩
  · (have H := regAt_fnMap π hπ (d i).1; simp only [map_div₀] at H; exact H)
  · (have H := unitAt_fnMap π hπ (d i).2; simp only [map_div₀] at H; exact H)

theorem eqvGen_pull {c c' : X → Fin N → X.functionFieldˣ} (h : Relation.EqvGen (Link p) c c') :
    Relation.EqvGen (Link p) (pf π hπ c) (pf π hπ c') := by
  induction h with
  | rel _ _ h => exact .rel _ _ (h.pull π hπ)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'

end Pull

end Sch

section Num

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {N : ℕ}

def Can (M : HermLB q) (E : CartierDiv X) : Prop :=
  ∃ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), M.div hr = E ∧
    ∀ σ (y : CxPts q σ), y ∈ offSupp q σ E ∧ logNorm (M.φ σ) r y = 0

def Vert (p : ℕ) (E : CartierDiv X) : Prop := ∀ x, ¬ Ov p x → E.IsEqn x 1

def Rep (p : ℕ) (L : HermLB q) (b : X → X.functionFieldˣ) : Prop :=
  ∃ (ρ : L.B.ι → X.functionFieldˣ) (hρ : IsRatSec L.B ρ), ∀ x, Ov p x → (L.div hρ).IsEqn x (b x)

def bil {E : Type 1} [AddCommGroup E] [Module ℝ E] {n : ℕ} (num : Form E (n + 1)) (G : Fin n → E) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => num (Fin.cons a (Fin.cons b G))) (fun a a' b => num.cons_add _ a a')
    (fun t a b => num.cons_smul _ t a) (fun a b b' => (num.curryLeft a).cons_add G b b')
    fun t a b => (num.curryLeft a).cons_smul G t b

section Bil

variable {E : Type 1} [AddCommGroup E] [Module ℝ E] {n : ℕ} {num : Form E (n + 1)} (G : Fin n → E)

theorem bil_apply (a b : E) : bil num G a b = num (Fin.cons a (Fin.cons b G)) := rfl

theorem bil_rad_left {a : E} (ha : a ∈ rad num) (b : E) : bil num G a b = 0 := by
  have := ha (Fin.cons a (Fin.cons b G)) 0
  rwa [Fin.update_cons_zero] at this

theorem bil_symm (hs : IsSymm num) (a b : E) : bil num G a b = bil num G b a := by
  rw [bil_apply, bil_apply, ← hs _ (Equiv.swap 0 1)]
  congr 1
  funext j
  refine Fin.cases rfl (fun j => Fin.cases rfl (fun j => ?_) j) j
  rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
  rfl

theorem bil_rad_right (hs : IsSymm num) (a : E) {b : E} (hb : b ∈ rad num) : bil num G a b = 0 :=
  (bil_symm G hs a b).trans (bil_rad_left G hb a)

theorem bil_congr (hs : IsSymm num) {a a' b b' : E} (ha : a - a' ∈ rad num) (hb : b - b' ∈ rad num) :
    bil num G a b = bil num G a' b' := by
  have h₁ := bil_rad_left G ha b
  have h₂ := bil_rad_right G hs a' hb
  rw [map_sub, LinearMap.sub_apply] at h₁
  rw [map_sub] at h₂
  linarith

end Bil

def Moves {n : ℕ} (num : Form (Cl q) (n + 1)) (G : Fin n → HermLB q) (p m : ℕ) (c c' : X → Fin N → X.functionFieldˣ) : Prop :=
  ∃ (Δ : Fin N → HermLB q) (E : Fin N → CartierDiv X),
    (∀ i, Can (Δ i) (E i) ∧ Vert p (E i) ∧ ∀ x, Ov p x → (E i).IsEqn x ((c' x i / c x i) ^ m)) ∧
    ∀ L : Fin N → HermLB q, (∀ i, Rep p (L i) fun x => c x i ^ m) →
      ∑ i, bil num (fun j => cl (G j)) (cl (L i) + cl (Δ i)) (cl (L i) + cl (Δ i)) =
        ∑ i, bil num (fun j => cl (G j)) (cl (L i)) (cl (L i))

end Num

section Cov

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

abbrev jm (V : Cover Y) (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) : V.X.functionField →+* V.G.functionField :=
  SmallSec.fnMap V.j hη

def Reads {C : CxSt F} (V : Cover Y) (p : ℕ) (A : Adl C Y) (c : V.X → V.X.functionFieldˣ) : Prop :=
  ∃ (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) (W : Y.X.Opens) (U : V.X → V.X.Opens), genericPoint Y.X ∈ W ∧
    (∀ x, Ov p x → x ∈ U x) ∧
    (∀ x (z : V.G), V.j z ∈ U x → UnitAt z (V.φ (genAt A.D (V.π z)) * jm V hη (c x))) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ x, ⊤ ≤ yt ⁻¹ᵁ U x → A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) * jm V hη (c x))))

def NormsX (V : Cover Y) (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ)
    (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r) : Prop :=
  (∀ σ (y : CxPts V.p σ), y ∈ offSupp V.p σ (M.div hr) ∧ logNorm (M.φ σ) r y = 0) ∧
    (∀ i (z : V.G), V.j z ∈ M.B.U i → UnitAt (V.j z) (r i : V.X.functionField)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G)
      (yt : Sp e.O ⟶ V.X) (i : M.B.ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ M.B.U i →
      lg v e y = Real.log (e.w (valAt (z ≫ V.j) (r i : V.X.functionField)))

theorem lies_comp {V₁ V₂ V₃ : Cover Y} {a : V₁.X ⟶ V₂.X} {b : V₂.X ⟶ V₃.X} (ha : Lies V₁ V₂ a) (hb : Lies V₂ V₃ b) :
    Lies V₁ V₃ (a ≫ b) := by
  obtain ⟨e', he₁', he₂'⟩ := ha
  obtain ⟨e, he₁, he₂⟩ := hb
  exact ⟨e' ≫ e, by rw [Category.assoc, he₁, ← Category.assoc, he₁', Category.assoc], by rw [Category.assoc, he₂, he₂']⟩

end Cov

end GlobalTheory.LatChain

end
