import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Matrix ComplexOrder Topology ContDiff

namespace GlobalTheory.GoodMetric.RepBundle

variable {ι : Type} {m : ι → ℕ}

section Alg

theorem evEnt_map {M : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ)) {R S : Type} [CommRing R]
    [CommRing S] (φ : R →+* S) (A : Mat m R) : evEnt P (A.map φ) = (evEnt P A).map φ := by
  ext i j
  simp only [evEnt, Matrix.map_apply, Mat.map]
  rw [map_aeval, aeval_def, coe_eval₂Hom, Subsingleton.elim (φ.comp (algebraMap ℤ R)) (algebraMap ℤ S)]

variable (ρ : PolyRep m)

theorem ev_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (A : Mat m R) :
    ρ.ev (A.map φ) = (ρ.ev A).map φ :=
  evEnt_map ρ.ent φ A

theorem ev_mul {R : Type} [CommRing R] (A B : Mat m R) : ρ.ev (A * B) = ρ.ev A * ρ.ev B := ρ.mul R A B

theorem ev_one {R : Type} [CommRing R] : ρ.ev (1 : Mat m R) = 1 := ρ.one R

theorem ev_mem {K : Type} [Field K] {O : Subring K} {g : Mat m K} (hg : ∀ τ i j, g τ i j ∈ O) (i j : Fin ρ.M) :
    ρ.ev g i j ∈ O := by
  let gO : Mat m O := fun τ i j => ⟨g τ i j, hg τ i j⟩
  have e : g = gO.map O.subtype := rfl
  rw [e, ev_map]
  exact (ρ.ev gO i j).2

theorem ev_map_of {K K' : Type} [Field K] [CommRing K'] {O : Subring K} {g : Mat m K} (hg : ∀ τ i j, g τ i j ∈ O)
    (v : K → K') (ψ : O →+* K') (hv : ∀ x : O, v x = ψ x) : (ρ.ev g).map v = ρ.ev (g.map v) := by
  let gO : Mat m O := fun τ i j => ⟨g τ i j, hg τ i j⟩
  have e : g = gO.map O.subtype := rfl
  have e' : g.map v = gO.map ψ := funext fun τ => by ext i j; exact hv (gO τ i j)
  rw [e', e, ev_map, ev_map, Matrix.map_map]
  ext i j
  exact hv _

variable {K : Type} [Field K] {A : Mat m K}

theorem ev_mul_ev_inv (hA : ∀ τ, (A τ).det ≠ 0) : ρ.ev A * ρ.ev A⁻¹ = 1 := by
  rw [← ev_mul, Mat.mul_inv hA, ev_one]

theorem ev_inv (hA : ∀ τ, (A τ).det ≠ 0) : (ρ.ev A)⁻¹ = ρ.ev A⁻¹ :=
  Matrix.inv_eq_right_inv (ev_mul_ev_inv ρ hA)

theorem det_ev_ne (hA : ∀ τ, (A τ).det ≠ 0) : (ρ.ev A).det ≠ 0 := by
  have := congrArg Matrix.det (ev_mul_ev_inv ρ hA)
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact left_ne_zero_of_mul_eq_one this

abbrev lift {R : Type} [CommRing R] (A : Mat m R) : Mat (fun _ : Unit => ρ.M) R := fun _ => ρ.ev A

theorem lift_mul {R : Type} [CommRing R] (A B : Mat m R) : lift ρ (A * B) = lift ρ A * lift ρ B :=
  funext fun _ => ev_mul ρ A B

theorem lift_inv (hA : ∀ τ, (A τ).det ≠ 0) : (lift ρ A)⁻¹ = lift ρ A⁻¹ := funext fun _ => ev_inv ρ hA

theorem lift_det_ne (hA : ∀ τ, (A τ).det ≠ 0) : ∀ τ, (lift ρ A τ).det ≠ 0 := fun _ => det_ev_ne ρ hA

theorem par_lift {O : Subring K} {g : Mat m K} (hg : Par 0 O g) : Par 0 O (lift ρ g) := fun _ => by
  have hd := congrArg Matrix.det (ev_mul_ev_inv ρ hg.det_ne)
  rw [Matrix.det_mul, Matrix.det_one] at hd
  refine ⟨ev_mem ρ fun τ i j => (hg τ).1 i j, left_ne_zero_of_mul_eq_one hd, ?_, fun i j hi _ => absurd hi (Nat.not_lt_zero _)⟩
  show (ρ.ev g).det⁻¹ ∈ O
  rw [inv_eq_of_mul_eq_one_right hd]
  exact det_mem (ev_mem ρ fun τ i j => (hg.inv τ).1 i j)

theorem ev_conjTranspose (A : Mat m ℂ) : ρ.ev (fun τ => (A τ)ᴴ) = (ρ.ev A)ᴴ := by
  have e : (fun τ => (A τ)ᴴ) = Mat.map (fun τ => (A τ)ᵀ) (starRingEnd ℂ) := rfl
  rw [e, ev_map]
  show (evEnt ρ.ent fun τ => (A τ)ᵀ).map _ = _
  rw [ρ.transp]
  rfl

theorem exists_eq_conjTranspose_mul_self' {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.PosSemidef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, T = Bᴴ * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

theorem exists_ev_posDef {H : Mat m ℂ} (hH : ∀ τ, (H τ).PosDef) :
    ∃ P : Matrix (Fin ρ.M) (Fin ρ.M) ℂ, P.det ≠ 0 ∧ ρ.ev H = Pᴴ * P := by
  choose B hB using fun τ => exists_eq_conjTranspose_mul_self' (hH τ).posSemidef
  have hd (τ : ι) : (B τ).det ≠ 0 := fun h => by
    have := (hH τ).det_pos
    rw [hB τ, Matrix.det_mul, h, mul_zero] at this
    exact lt_irrefl _ this
  have e : H = (fun τ => (B τ)ᴴ) * B := funext hB
  refine ⟨ρ.ev B, det_ev_ne ρ hd, ?_⟩
  rw [e, ev_mul, ev_conjTranspose]

theorem posDef_conj {n : ℕ} {T P : Matrix (Fin n) (Fin n) ℂ} (hT : T.det ≠ 0) (hP : P.det ≠ 0) :
    (T * (Pᴴ * P) * Tᴴ).PosDef := by
  have e : T * (Pᴴ * P) * Tᴴ = (T * Pᴴ) * (T * Pᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
  have hd : (T * Pᴴ).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero hT (by simpa using hP)
  rw [e]
  exact Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 hd.isUnit))

end Alg

end GlobalTheory.GoodMetric.RepBundle

namespace GlobalTheory.GoodMetric.RepBundle

open Filter

variable {ι : Type} {m : ι → ℕ} {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ}

section Smooth

def CS (u : CxPts X.str σ → ℂ) (y : CxPts X.str σ) : Prop :=
  CInfAt (fun z => (u z).re) y ∧ CInfAt (fun z => (u z).im) y

variable {y : CxPts X.str σ} {u v : CxPts X.str σ → ℂ}

theorem CS.congr (h : CS u y) (e : v =ᶠ[𝓝 y] u) : CS v y :=
  ⟨h.1.congr (e.mono fun z hz => by simp only [hz]), h.2.congr (e.mono fun z hz => by simp only [hz])⟩

theorem cs_const (c : ℂ) : CS (fun _ => c) y := ⟨cInfAt_const c.re y, cInfAt_const c.im y⟩

theorem CS.add (h : CS u y) (h' : CS v y) : CS (fun z => u z + v z) y :=
  ⟨(h.1.add h'.1).congr (Eventually.of_forall fun z => Complex.add_re _ _),
    (h.2.add h'.2).congr (Eventually.of_forall fun z => Complex.add_im _ _)⟩

theorem CS.mul (h : CS u y) (h' : CS v y) : CS (fun z => u z * v z) y := by
  have hm : ContDiff ℝ ∞ fun x : ℝ × ℝ => x.1 * x.2 := contDiff_fst.mul contDiff_snd
  refine ⟨((h.1.comp₂ h'.1 hm).comp₂ (h.2.comp₂ h'.2 hm) (G := fun x => x.1 - x.2)
      (contDiff_fst.sub contDiff_snd)).congr (Eventually.of_forall fun z => Complex.mul_re _ _),
    ((h.1.comp₂ h'.2 hm).comp₂ (h.2.comp₂ h'.1 hm) (G := fun x => x.1 + x.2)
      (contDiff_fst.add contDiff_snd)).congr (Eventually.of_forall fun z => Complex.mul_im _ _)⟩

theorem CS.star (h : CS u y) : CS (fun z => star (u z)) y :=
  ⟨h.1.congr (Eventually.of_forall fun z => Complex.conj_re _),
    h.2.neg.congr (Eventually.of_forall fun z => Complex.conj_im _)⟩

theorem cs_sum {α : Type} (s : Finset α) {w : α → CxPts X.str σ → ℂ} (h : ∀ a ∈ s, CS (w a) y) :
    CS (fun z => ∑ a ∈ s, w a z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cs_const (y := y) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem cs_aeval {κ : Type} (P : MvPolynomial κ ℤ) {w : κ → CxPts X.str σ → ℂ} (h : ∀ a, CS (w a) y) :
    CS (fun z => aeval (fun a => w a z) P) y := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using cs_const (y := y) (a : ℂ)
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p a hp => simpa only [map_mul, aeval_X] using hp.mul (h a)

theorem cs_ratVal {f : X.Fn} (hf : RegAt (under y) f) : CS (fun z => ratVal f z) y :=
  ⟨cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf) (G := fun w => (w ()).re)
      (Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ ())),
    cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf) (G := fun w => (w ()).im)
      (Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ ()))⟩

theorem cs_conj_entry {n : ℕ} {T R : CxPts X.str σ → Matrix (Fin n) (Fin n) ℂ} (hT : ∀ i j, CS (fun z => T z i j) y)
    (hR : ∀ i j, CS (fun z => R z i j) y) (i j : Fin n) : CS (fun z => (T z * R z * (T z)ᴴ) i j) y := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact cs_sum _ fun l _ => (cs_sum _ fun k _ => (hT i k).mul (hR k l)).mul (hT j l).star

theorem eventually_regAt {f : X.Fn} (hf : RegAt (under y) f) : ∀ᶠ z in 𝓝 y, RegAt (under z) f := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
  exact regAt_fnOf (mem_ptsIn.1 hz) _ a

theorem eventually_par [Fintype ι] {g : Mat m X.Fn} (hg : Par 0 ((ratOf X).O (under y)).toSubring g) :
    ∀ᶠ z in 𝓝 y, Par 0 ((ratOf X).O (under z)).toSubring g := by
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ i j, RegAt (under z) (g τ i j) :=
    eventually_all.2 fun τ => eventually_all.2 fun i => eventually_all.2 fun j =>
      eventually_regAt (mem_O_ratOf.1 ((hg τ).1 i j))
  have h2 : ∀ᶠ z in 𝓝 y, ∀ τ, RegAt (under z) (g τ).det⁻¹ :=
    eventually_all.2 fun τ => eventually_regAt (mem_O_ratOf.1 (hg τ).2.2.1)
  filter_upwards [h1, h2] with z hz hz'
  exact fun τ => ⟨fun i j => mem_O_ratOf.2 (hz τ i j), (hg τ).2.1, mem_O_ratOf.2 (hz' τ),
    fun i j hi => absurd hi (Nat.not_lt_zero _)⟩

theorem eventually_mem [Fintype ι] {E : Fr (ratOf X) m 0} {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) :
    ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  obtain ⟨U, A₀, hy, -, h⟩ := E.loc (under y)
  filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hy), eventually_par ((h _ hy A).1 hA)] with z hz hz'
  exact (h _ (mem_ptsIn.1 hz) A).2 hz'

end Smooth

end GlobalTheory.GoodMetric.RepBundle

namespace GlobalTheory.GoodMetric.RepBundle

open Filter

variable {ι : Type} {m : ι → ℕ} {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} (ρ : PolyRep m)

section Bundle

theorem par_of_exists {E : Fr (ratOf X) m 0} {z : X.X} {B : Mat (fun _ : Unit => ρ.M) X.Fn}
    (hB : ∃ A ∈ E.S z, Par 0 ((ratOf X).O z).toSubring (B * (lift ρ A)⁻¹)) {A : Mat m X.Fn} (hA : A ∈ E.S z) :
    Par 0 ((ratOf X).O z).toSubring (B * (lift ρ A)⁻¹) := by
  obtain ⟨A₂, hA₂, h⟩ := hB
  have e : B * (lift ρ A)⁻¹ = B * (lift ρ A₂)⁻¹ * lift ρ (A₂ * A⁻¹) := by
    rw [lift_mul, ← lift_inv ρ (Fr.det_ne hA), ← mul_assoc, mul_assoc B, Mat.inv_mul (lift_det_ne ρ (Fr.det_ne hA₂)),
      mul_one]
  rw [e]
  exact h.mul (par_lift ρ ((Fr.mem_iff hA).1 hA₂))

def repFr (E : Fr (ratOf X) m 0) : Fr (ratOf X) (fun _ : Unit => ρ.M) 0 where
  S z := {B | ∃ A ∈ E.S z, Par 0 ((ratOf X).O z).toSubring (B * (lift ρ A)⁻¹)}
  loc z := by
    obtain ⟨U, A₀, hz, hA₀, h⟩ := E.loc z
    refine ⟨U, lift ρ A₀, hz, lift_det_ne ρ hA₀, fun z' hz' B => ⟨fun hB => ?_, fun hB => ?_⟩⟩
    · exact par_of_exists ρ hB ((h z' hz' A₀).2 (by rw [Mat.mul_inv hA₀]; exact Par.one))
    · exact ⟨A₀, (h z' hz' A₀).2 (by rw [Mat.mul_inv hA₀]; exact Par.one), hB⟩

variable {E : Fr (ratOf X) m 0}

theorem lift_mem {z : X.X} {A : Mat m X.Fn} (hA : A ∈ E.S z) : lift ρ A ∈ (repFr ρ E).S z :=
  ⟨A, hA, by rw [Mat.mul_inv (lift_det_ne ρ (Fr.det_ne hA))]; exact Par.one⟩

variable (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)

def gramIn (B : Mat (fun _ : Unit => ρ.M) X.Fn) (A : Mat m X.Fn) (y : CxPts X.str σ) : Matrix (Fin ρ.M) (Fin ρ.M) ℂ :=
  (B * (lift ρ A)⁻¹).map (ratVal · y) () * ρ.ev (H A y) * ((B * (lift ρ A)⁻¹).map (ratVal · y) ())ᴴ

def repMetric (E : Fr (ratOf X) m 0) (B : Mat (fun _ : Unit => ρ.M) X.Fn) (y : CxPts X.str σ) :
    Mat (fun _ : Unit => ρ.M) ℂ :=
  fun _ => gramIn ρ H B (E.nonempty (under y)).choose y

variable {H} {O : X.X.Opens}

theorem gramIn_eq (hH : IsMetricOn E O H) {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O)
    {B : Mat (fun _ : Unit => ρ.M) X.Fn} (hB : B ∈ (repFr ρ E).S (under y)) {A A₁ : Mat m X.Fn}
    (hA : A ∈ E.S (under y)) (hA₁ : A₁ ∈ E.S (under y)) : gramIn ρ H B A₁ y = gramIn ρ H B A y := by
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
  have hC := par_of_exists ρ hB hA
  have hg := (Fr.mem_iff hA₁).1 hA
  have e1 : B * (lift ρ A₁)⁻¹ = B * (lift ρ A)⁻¹ * lift ρ (A * A₁⁻¹) := by
    rw [lift_mul, ← lift_inv ρ (Fr.det_ne hA₁), ← mul_assoc, mul_assoc B, Mat.inv_mul (lift_det_ne ρ (Fr.det_ne hA)),
      mul_one]
  have e2 := Par.map_mul_of hC (par_lift ρ hg) (ratVal · y) ψ hψ
  have e3 : (lift ρ (A * A₁⁻¹)).map (ratVal · y) () = ρ.ev ((A * A₁⁻¹).map (ratVal · y)) :=
    ev_map_of ρ (fun τ i j => (hg τ).1 i j) (ratVal · y) ψ hψ
  have e4 : H A y = (A * A₁⁻¹).map (ratVal · y) * H A₁ y * fun τ => ((A * A₁⁻¹).map (ratVal · y) τ)ᴴ :=
    funext fun τ => hH.trans y hy A₁ hA₁ A hA τ
  unfold gramIn
  rw [e1, e2, e4, ev_mul, ev_mul, ev_conjTranspose]
  simp only [Pi.mul_apply, e3, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem repMetric_eq (hH : IsMetricOn E O H) {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O)
    {B : Mat (fun _ : Unit => ρ.M) X.Fn} (hB : B ∈ (repFr ρ E).S (under y)) {A : Mat m X.Fn}
    (hA : A ∈ E.S (under y)) : repMetric ρ H E B y () = gramIn ρ H B A y :=
  gramIn_eq ρ hH hy hB hA (E.nonempty (under y)).choose_spec

theorem isMetricOn_repMetric [Fintype ι] (hH : IsMetricOn E O H) : IsMetricOn (repFr ρ E) O (repMetric ρ H E) := by
  refine ⟨fun y hy B hB τ => ?_, fun y hy B hB τ i j => ?_, fun y hy B hB B' hB' τ => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    have hA := (E.nonempty (under y)).choose_spec
    have hT := ((par_of_exists ρ hB hA).map_of (ratVal · y) ψ hψ).det_ne ()
    obtain ⟨P, hP, e⟩ := exists_ev_posDef ρ (hH.posDef y hy _ hA)
    show (gramIn ρ H B _ y).PosDef
    unfold gramIn
    rw [e]
    exact posDef_conj hT hP
  · obtain ⟨A, hA, hC⟩ := hB
    have hev : ∀ᶠ z in 𝓝 y, repMetric ρ H E B z τ = gramIn ρ H B A z := by
      filter_upwards [(isOpen_ptsIn O).mem_nhds hy, eventually_mem hA, eventually_par hC] with z hz hAz hCz
      exact repMetric_eq ρ hH hz ⟨A, hAz, hCz⟩ hAz
    have hT : ∀ k l, CS (fun z => (B * (lift ρ A)⁻¹).map (ratVal · z) () k l) y := fun k l =>
      cs_ratVal (mem_O_ratOf.1 ((hC ()).1 k l))
    have hR : ∀ k l, CS (fun z => ρ.ev (H A z) k l) y := fun k l =>
      cs_aeval (ρ.ent k l) fun v => ⟨(hH.smooth y hy A hA v.1 v.2.1 v.2.2).1, (hH.smooth y hy A hA v.1 v.2.1 v.2.2).2⟩
    exact CS.congr (v := fun z => repMetric ρ H E B z τ i j) (cs_conj_entry hT hR i j)
      (hev.mono fun z hz => by show repMetric ρ H E B z τ i j = gramIn ρ H B A z i j; rw [hz])
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    have hA := (E.nonempty (under y)).choose_spec
    have hC := par_of_exists ρ hB hA
    have hC' := par_of_exists ρ hB' hA
    have hD : Par 0 ((ratOf X).O (under y)).toSubring (B' * B⁻¹) := by
      have e : B' * B⁻¹ = B' * (lift ρ (E.nonempty (under y)).choose)⁻¹ * (B * (lift ρ (E.nonempty (under y)).choose)⁻¹)⁻¹ := by
        rw [Mat.mul_inv_rev, Mat.inv_inv (lift_det_ne ρ (Fr.det_ne hA)), mul_assoc, ← mul_assoc _ (lift ρ (E.nonempty (under y)).choose),
          Mat.inv_mul (lift_det_ne ρ (Fr.det_ne hA)), one_mul]
      rw [e]
      exact hC'.mul hC.inv
    have e1 : B' * (lift ρ (E.nonempty (under y)).choose)⁻¹ =
        B' * B⁻¹ * (B * (lift ρ (E.nonempty (under y)).choose)⁻¹) := by
      rw [← mul_assoc, mul_assoc B', Mat.inv_mul (fun τ h => ?_), mul_one]
      have := hC.det_ne τ
      rw [Pi.mul_apply, Matrix.det_mul, h, zero_mul] at this
      exact this rfl
    have e2 := Par.map_mul_of hD hC (ratVal · y) ψ hψ
    show gramIn ρ H B' _ y = _ * gramIn ρ H B _ y * _
    unfold gramIn
    rw [e1, e2]
    simp only [Pi.mul_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Bundle

end GlobalTheory.GoodMetric.RepBundle

namespace GlobalTheory.GoodMetric.RepBundle

theorem exists_repBundle : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (E : Fr (ratOf X) m 0), ∃ E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0, (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) ∧ ∀ (σ : F →+* ℂ) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∃ H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ, IsMetricOn E' O H' ∧ ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y) := by
  intro F _ X ι _ m ρ E
  refine ⟨repFr ρ E, fun z A hA => lift_mem ρ hA, fun σ O H hH =>
    ⟨repMetric ρ H E, isMetricOn_repMetric ρ hH, fun y hy A hA => ?_⟩⟩
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
  rw [repMetric_eq ρ hH hy (lift_mem ρ hA) hA]
  unfold gramIn
  have e : (lift ρ A * (lift ρ A)⁻¹).map (ratVal · y) () = 1 := by
    rw [Mat.mul_inv (lift_det_ne ρ (Fr.det_ne hA))]
    exact Matrix.map_one _ ((hψ 0).trans (map_zero ψ)) ((hψ 1).trans (map_one ψ))
  rw [e, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.GoodMetric.RepBundle

end
