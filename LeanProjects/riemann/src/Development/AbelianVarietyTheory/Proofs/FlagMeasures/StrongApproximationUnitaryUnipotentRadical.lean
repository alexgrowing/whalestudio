import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring

open Formalism.MainNotions.S Matrix NumberField Topology Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnipApprox

section Ring

open GlobalTheory.TwoStepUnipotent

variable {S : Type} [Ring S]

def Cond (st : S →+ S) (e g : S) : Prop :=
  st g * g = 1 ∧ (g - 1) * e = 0 ∧ (1 - e) * (g - 1) * (1 - st e) = 0

theorem Cond.mul {st : S →+ S} {e g g' : S} (hm : ∀ x y, st (x * y) = st y * st x)
    (h : Cond st e g) (h' : Cond st e g') : Cond st e (g * g') := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h'
  have c1 : g * e = e := by rwa [sub_mul, one_mul, sub_eq_zero] at a2
  have c2 : g' * e = e := by rwa [sub_mul, one_mul, sub_eq_zero] at b2
  have c3 : (g' - 1) * (1 - st e) = e * ((g' - 1) * (1 - st e)) := by
    rwa [mul_assoc, sub_mul 1 e, one_mul, sub_eq_zero] at b3
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, mul_assoc, ← mul_assoc (st g), a1, one_mul, b1]
  · rw [sub_mul, mul_assoc, c2, c1, one_mul, sub_self]
  · have : (g * g' - 1) * (1 - st e) = g * ((g' - 1) * (1 - st e)) + (g - 1) * (1 - st e) := by noncomm_ring
    rw [mul_assoc, this, c3, ← mul_assoc g, c1, ← c3, mul_add, ← mul_assoc, ← mul_assoc, a3, b3, add_zero]

theorem Cond.inv {st : S →+ S} {e : S} {g : Sˣ} (hi : ∀ x, st (st x) = x)
    (h : Cond st e (g : S)) : Cond st e ((g⁻¹ : Sˣ) : S) := by
  obtain ⟨a1, a2, a3⟩ := h
  have c1 : (g : S) * e = e := by rwa [sub_mul, one_mul, sub_eq_zero] at a2
  have c2 : ((g⁻¹ : Sˣ) : S) * e = e := by
    conv_lhs => rw [← c1, ← mul_assoc, Units.inv_mul, one_mul]
  have c3 : ((g : S) - 1) * (1 - st e) = e * (((g : S) - 1) * (1 - st e)) := by
    rwa [mul_assoc, sub_mul 1 e, one_mul, sub_eq_zero] at a3
  have c4 : ((g⁻¹ : Sˣ) : S) = st g := (Units.eq_inv_of_mul_eq_one_right a1).symm
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => enter [1]; rw [c4, hi]
    exact Units.mul_inv g
  · rw [sub_mul, c2, one_mul, sub_self]
  · have : (((g⁻¹ : Sˣ) : S) - 1) = -(((g⁻¹ : Sˣ) : S) * ((g : S) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [mul_assoc, this, neg_mul, mul_assoc, c3, ← mul_assoc _ e, c2, ← c3, mul_neg, ← mul_assoc, a3, neg_zero]

theorem Cond.map_iff {R : Type} [Ring R] {st : S →+ S} {st₀ : R →+ R} (f : R →+* S)
    (hf : Function.Injective f) (hst : ∀ x, f (st₀ x) = st (f x)) {e g : R} :
    Cond st (f e) (f g) ↔ Cond st₀ e g := by
  unfold Cond
  rw [← hf.eq_iff, ← hf.eq_iff (a := (g - 1) * e), ← hf.eq_iff (a := (1 - e) * (g - 1) * (1 - st₀ e))]
  simp only [map_mul, map_sub, map_one, map_zero, hst]

theorem exists_idem {st : S →+ S} {p h : S} (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hh : h + h = 1) (hc : ∀ x, h * x = x * h) (hp : p * p = p) (h0 : st p * p = 0) :
    ∃ e, e * e = e ∧ e * st e = 0 ∧ st e * e = 0 ∧ e * p = p ∧ p * e = e := by
  have hq : st p * st p = st p := by rw [← hm, hp]
  have hs : st (p * (1 - h * st p)) = (1 - h * p) * st p := by
    rw [hm, map_sub, hm, hi, st_one hm hi, st_half hm hi hh hc, hc]
  have e1 : p * (1 - h * st p) * p = p := by
    rw [mul_assoc, sub_mul, mul_assoc, h0, mul_zero, sub_zero, one_mul, hp]
  refine ⟨p * (1 - h * st p), by rw [← mul_assoc, e1], ?_, ?_, e1, by rw [← mul_assoc, hp]⟩
  · have e2 : p * (1 - h * st p) * (1 - h * p) = p * (1 - h * st p) - h * p := by
      rw [mul_sub _ 1, mul_one, ← mul_assoc, ← hc, mul_assoc h, e1]
    rw [hs, ← mul_assoc, e2, sub_mul, mul_assoc p, sub_mul, mul_assoc h, hq, one_mul, mul_sub, ← mul_assoc p h,
      ← hc p, sub_sub, ← add_mul, ← add_mul, hh, one_mul, sub_self]
  · rw [hs, mul_assoc, ← mul_assoc (st p), h0, zero_mul, mul_zero]

theorem exists_param [TopologicalSpace S] [IsTopologicalRing S]
    (st : S →+ S) (S₀ : Subring S) (e₁ h : S) (hcont : Continuous st)
    (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (he : e₁ ∈ S₀) (hh0 : h ∈ S₀) (h11 : e₁ * e₁ = e₁)
    (h13 : e₁ * st e₁ = 0) (h31 : st e₁ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h) :
    ∃ U : S × S → Sˣ, Continuous U ∧ U 0 = 1 ∧ (∀ p, Cond st e₁ (U p : S)) ∧
      ∀ K : Set S, (∀ x, ∃ y ∈ S₀, x - y ∈ K) → ∀ g : Sˣ, Cond st e₁ (g : S) →
        ∃ γ : Sˣ, Cond st e₁ (γ : S) ∧ (γ : S) ∈ S₀ ∧ ((γ⁻¹ : Sˣ) : S) ∈ S₀ ∧ γ * g ∈ U '' (K ×ˢ K) := by
  unfold Cond
  obtain ⟨e₃, hs⟩ : ∃ e₃, st e₁ = e₃ := ⟨_, rfl⟩
  rw [hs] at h13 h31 ⊢
  have hs' : st e₃ = e₁ := by rw [← hs, hi]
  have h33 : e₃ * e₃ = e₃ := by rw [← hs, ← hm, h11]
  have he3 : e₃ ∈ S₀ := hs ▸ h0 _ he
  have hsh : st h = h := st_half hm hi hh hc
  obtain ⟨B, hB⟩ : ∃ B : S → S, ∀ x, B x = (1 - e₁ - e₃) * x * e₃ := ⟨_, fun _ => rfl⟩
  obtain ⟨Wd, hW⟩ : ∃ Wd : S → S, ∀ y, Wd y = h * (e₁ * (y - st y) * e₃) := ⟨_, fun _ => rfl⟩
  have Bc : Continuous B := by
    rw [show B = fun x => (1 - e₁ - e₃) * x * e₃ from funext hB]; fun_prop
  have Wc : Continuous Wd := by
    rw [show Wd = fun y => h * (e₁ * (y - st y) * e₃) from funext hW]; fun_prop
  have Bp : ∀ x, e₁ * B x = 0 ∧ e₃ * B x = 0 ∧ B x * e₃ = B x := fun x => by
    refine ⟨?_, ?_, ?_⟩
    · rw [hB, ← mul_assoc, ← mul_assoc, mul_sub, mul_sub, h11, h13]; simp
    · rw [hB, ← mul_assoc, ← mul_assoc, mul_sub, mul_sub, h31, h33]; simp
    · rw [hB, mul_assoc _ e₃, h33]
  have Wp : ∀ y, e₁ * Wd y = Wd y ∧ Wd y * e₃ = Wd y ∧ st (Wd y) = - Wd y := fun y => by
    refine ⟨?_, ?_, ?_⟩
    · rw [hW, ← mul_assoc, ← hc, mul_assoc, ← mul_assoc e₁, ← mul_assoc e₁, h11]
    · rw [hW, mul_assoc, mul_assoc _ e₃, h33]
    · rw [hW, hm, hm, hm, hs, hs', hsh, ← hc, map_sub, hi, ← neg_sub y]
      simp only [mul_neg, neg_mul, mul_assoc]
  have Bfix : ∀ b, (e₁ * b = 0 ∧ e₃ * b = 0 ∧ b * e₃ = b) → B b = b := fun b hb => by
    rw [hB, sub_mul _ e₃, sub_mul _ e₁, hb.1, hb.2.1, one_mul, sub_zero, sub_zero, hb.2.2]
  have Wfix : ∀ w, (e₁ * w = w ∧ w * e₃ = w ∧ st w = -w) → Wd w = w := fun w hw => by
    rw [hW, hw.2.2, sub_neg_eq_add, mul_add, hw.1, add_mul, hw.2.1, mul_add, ← add_mul, hh,
      one_mul]
  have Bsub : ∀ x y, B (x - y) = B x - B y := fun x y => by
    rw [hB, hB, hB, mul_sub, sub_mul]
  have Wsub : ∀ x y, Wd (x - y) = Wd x - Wd y := fun x y => by
    rw [hW, hW, hW, map_sub]; noncomm_ring
  have B0 : ∀ x ∈ S₀, B x ∈ S₀ := fun x hx => by
    rw [hB]
    exact S₀.mul_mem (S₀.mul_mem (S₀.sub_mem (S₀.sub_mem S₀.one_mem he) he3) hx) he3
  have W0 : ∀ x ∈ S₀, Wd x ∈ S₀ := fun x hx => by
    rw [hW]
    exact S₀.mul_mem hh0 (S₀.mul_mem (S₀.mul_mem he (S₀.sub_mem hx (h0 _ hx))) he3)
  have E0 : ∀ b ∈ S₀, ∀ w ∈ S₀, elt st h b w ∈ S₀ := fun b hb w hw =>
    S₀.add_mem (S₀.add_mem (S₀.sub_mem S₀.one_mem (h0 _ hb)) hb)
      (S₀.sub_mem hw (S₀.mul_mem hh0 (S₀.mul_mem (h0 _ hb) hb)))
  let U : S × S → Sˣ := fun p =>
    ⟨elt st h (B p.1) (Wd p.2), elt st h (-B p.1) (-Wd p.2),
      elt_mul_neg hm hi hs h31 hh hc (Bp _).2 ⟨(Wp _).1, (Wp _).2.1⟩,
      elt_neg_mul hm hi hs h31 hh hc (Bp _).2 ⟨(Wp _).1, (Wp _).2.1⟩⟩
  have Uc : Continuous U := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous fun p : S × S => elt st h (B p.1) (Wd p.2)
      unfold elt
      fun_prop
    · change Continuous fun p : S × S => elt st h (-B p.1) (-Wd p.2)
      unfold elt
      fun_prop
  have Up : ∀ p, st (U p : S) * (U p : S) = 1 ∧ ((U p : S) - 1) * e₁ = 0 ∧
      (1 - e₁) * ((U p : S) - 1) * (1 - e₃) = 0 := fun p =>
    elt_cond hm hi hs h31 hh hc (Bp _) (Wp _)
  refine ⟨U, Uc, ?_, Up, fun K hcov => ?_⟩
  · ext
    change elt st h (B 0) (Wd 0) = 1
    simp [elt, hB, hW]
  · rintro g ⟨g1, g2, g3⟩
    obtain ⟨b, w, hb, hw, hg⟩ := exists_elt hm hi h11 hs h31 hh hc g1 g2 g3
    obtain ⟨β, hβ, hβK⟩ := hcov b
    have hb' := Bp (-β)
    obtain ⟨w₂, hw₂⟩ : ∃ w₂, w₂ = w + h * (st b * B (-β) - st (B (-β)) * b) := ⟨_, rfl⟩
    have q1 : e₁ * st b = st b := by rw [← hs', ← hm, hb.2.2]
    have q2 : e₁ * st (B (-β)) = st (B (-β)) := by rw [← hs', ← hm, hb'.2.2]
    have hw₂p : e₁ * w₂ = w₂ ∧ w₂ * e₃ = w₂ ∧ st w₂ = -w₂ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hw₂, mul_add, hw.1, ← mul_assoc, ← hc, mul_assoc, mul_sub, ← mul_assoc e₁,
          ← mul_assoc e₁, q1, q2]
      · rw [hw₂, add_mul, hw.2.1, mul_assoc, sub_mul, mul_assoc, mul_assoc, hb.2.2, hb'.2.2]
      · rw [hw₂, map_add, hm, hsh, ← hc, map_sub, hm, hm, hi, hi, hw.2.2]
        noncomm_ring
    obtain ⟨ω, hω, hωK⟩ := hcov w₂
    have Bn : B (-β) = - B β := by rw [hB, hB]; simp
    have Wn : Wd (-ω) = - Wd ω := by rw [hW, hW, map_neg]; noncomm_ring
    refine ⟨U (-β, -ω), Up _, E0 _ (B0 _ (S₀.neg_mem hβ)) _ (W0 _ (S₀.neg_mem hω)),
      E0 _ (S₀.neg_mem (B0 _ (S₀.neg_mem hβ))) _ (S₀.neg_mem (W0 _ (S₀.neg_mem hω))),
      (b - β, w₂ - ω), ⟨hβK, hωK⟩, ?_⟩
    ext
    change elt st h (B (b - β)) (Wd (w₂ - ω)) = elt st h (B (-β)) (Wd (-ω)) * (g : S)
    rw [hg, elt_mul hm hi hs h31 hh hc hb'.2 hb.2 (Wp _).2.1 hw.1, add_assoc, ← hw₂,
      Bsub, Wsub, Bfix b hb, Wfix w₂ hw₂p, Bn, Wn, neg_add_eq_sub, neg_add_eq_sub]

theorem exists_param' [TopologicalSpace S] [IsTopologicalRing S] {R : Type} [Ring R]
    (st : S →+ S) (st₀ : R →+ R) (f : R →+* S) (hf : Function.Injective f) (hst : ∀ x, f (st₀ x) = st (f x))
    (e h : R) (hcont : Continuous st)
    (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) (h11 : e * e = e)
    (h13 : e * st₀ e = 0) (h31 : st₀ e * e = 0) (hh : h + h = 1) (hc : ∀ x, f h * x = x * f h) :
    ∃ U : S × S → Sˣ, Continuous U ∧ U 0 = 1 ∧ (∀ p, Cond st (f e) (U p : S)) ∧
      ∀ K : Set S, (∀ x, ∃ y, x - f y ∈ K) → ∀ g : Sˣ, Cond st (f e) (g : S) →
        ∃ γ : Rˣ, Cond st₀ e (γ : R) ∧ Units.map (f : R →* S) γ * g ∈ U '' (K ×ˢ K) := by
  obtain ⟨U, h1, h2, h3, h4⟩ := exists_param st f.range (f e) (f h) hcont hm hi
    (by rintro _ ⟨x, rfl⟩; exact ⟨_, hst x⟩) ⟨e, rfl⟩ ⟨h, rfl⟩ (by rw [← map_mul, h11])
    (by rw [← hst, ← map_mul, h13, map_zero]) (by rw [← hst, ← map_mul, h31, map_zero])
    (by rw [← map_add, hh, map_one]) hc
  refine ⟨U, h1, h2, h3, fun K hK g hg => ?_⟩
  obtain ⟨γ, c1, ⟨a, ha⟩, ⟨b, hb⟩, c2⟩ := h4 K (fun x => (hK x).elim fun y hy => ⟨_, ⟨y, rfl⟩, hy⟩) g hg
  refine ⟨⟨a, b, hf (by simp [ha, hb]), hf (by simp [ha, hb])⟩, (Cond.map_iff f hf hst).1 (by rwa [← ha] at c1), ?_⟩
  convert c2 using 2
  ext
  exact ha

end Ring

section Mat

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def adj (s : A →+* A) (J K : Matrix n n A) : Matrix n n A →+ Matrix n n A where
  toFun x := K * cT s x * J
  map_zero' := by simp [cT]
  map_add' x y := by simp [cT, Matrix.map_add, Matrix.transpose_add, mul_add, add_mul]

theorem adj_apply (s : A →+* A) (J K x : Matrix n n A) : adj s J K x = K * cT s x * J := rfl

theorem adj_mul {s : A →+* A} {J K : Matrix n n A} (hJK : J * K = 1) (x y : Matrix n n A) :
    adj s J K (x * y) = adj s J K y * adj s J K x := by
  simp only [adj_apply, cT_mul, mul_assoc]
  rw [← mul_assoc J K, hJK, one_mul]

omit [Fintype n] [DecidableEq n] in
theorem cT_cT {s : A →+* A} (hs : ∀ a, s (s a) = a) (x : Matrix n n A) : cT s (cT s x) = x := by
  ext i j
  simp [cT, hs]

theorem adj_adj {s : A →+* A} {J K : Matrix n n A} (hs : ∀ a, s (s a) = a) (hJ : cT s J = J)
    (hJK : J * K = 1) (x : Matrix n n A) : adj s J K (adj s J K x) = x := by
  have h1 : cT s K * J = 1 := by rw [← hJ, ← cT_mul, hJK, cT_one]
  simp only [adj_apply, cT_mul, cT_cT hs, hJ, mul_assoc, h1, mul_one]
  rw [← mul_assoc, mul_eq_one_comm.1 hJK, one_mul]

theorem adj_unitary {s : A →+* A} {J K : Matrix n n A} (hJK : J * K = 1) (g : Matrix n n A) :
    adj s J K g * g = 1 ↔ cT s g * J * g = J := by
  rw [adj_apply]
  constructor
  · intro h
    have := congrArg (J * ·) h
    simpa only [← mul_assoc, hJK, one_mul, mul_one] using this
  · intro h
    rw [mul_assoc, mul_assoc, ← mul_assoc (cT s g), h, mul_eq_one_comm.1 hJK]

theorem map_adj {B : Type} [CommRing B] {s : A →+* A} {s' : B →+* B} (ι : A →+* B)
    (h : ∀ a, ι (s a) = s' (ι a)) (J K x : Matrix n n A) :
    (adj s J K x).map ι = adj s' (J.map ι) (K.map ι) (x.map ι) := by
  have : (cT s x).map ι = cT s' (x.map ι) := by
    ext i j
    simp [cT, h]
  simp only [adj_apply, Matrix.map_mul, this]

theorem continuous_adj [TopologicalSpace A] [IsTopologicalRing A] {s : A →+* A} (hs : Continuous s)
    (J K : Matrix n n A) : Continuous (adj s J K) :=
  (continuous_const.matrix_mul (continuous_id.matrix_map hs).matrix_transpose).matrix_mul continuous_const

omit [DecidableEq n] in
theorem hform_eq (s : A →+* A) (J : Matrix n n A) (x y : n → A) :
    hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem forall_hform_iff (s : A →+* A) {J K : Matrix n n A} (hJK : J * K = 1) (e : Matrix n n A) (y : n → A) :
    (∀ x, hform s J (e *ᵥ x) y = 0) ↔ adj s J K e *ᵥ y = 0 := by
  have key : ∀ x, hform s J (e *ᵥ x) y = (s ∘ x) ⬝ᵥ ((cT s e * J) *ᵥ y) := fun x => by
    have : s ∘ (e *ᵥ x) = (e.map s) *ᵥ (s ∘ x) := funext fun i => RingHom.map_mulVec s e x i
    rw [hform_eq, this, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (s ∘ x), cT, Matrix.vecMul_transpose]
  constructor
  · intro h
    have : (cT s e * J) *ᵥ y = 0 := by
      funext i
      have h1 := h (Pi.single i 1)
      have h2 : s ∘ (Pi.single i 1 : n → A) = Pi.single i 1 := by
        funext j
        by_cases hj : j = i <;> simp [hj]
      rwa [key, h2, single_one_dotProduct] at h1
    rw [adj_apply, mul_assoc, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero]
  · intro h x
    have := congrArg (J *ᵥ ·) h
    simp only [adj_apply, Matrix.mulVec_mulVec, ← mul_assoc, hJK, one_mul, Matrix.mulVec_zero] at this
    rw [key, this, dotProduct_zero]

omit [DecidableEq n] in
theorem eq_zero_of_mulVec {m : Matrix n n A} (h : ∀ y, m *ᵥ y = 0) : m = 0 :=
  Matrix.ext_iff_mulVec.2 fun y => by rw [h, Matrix.zero_mulVec]

theorem rad_iff {s : A →+* A} {J K e g : Matrix n n A} (hs : ∀ a, s (s a) = a) (hJ : cT s J = J)
    (hJK : J * K = 1) (he : e * e = e) (W : Submodule A (n → A)) (hW : ∀ x, x ∈ W ↔ e *ᵥ x = x)
    (hg : cT s g * J * g = J) :
    ((∀ x ∈ W, (g - 1) *ᵥ x = 0) ∧ (∀ y ∈ {y | ∀ x ∈ W, hform s J x y = 0}, (g - 1) *ᵥ y ∈ W) ∧
      ∀ y, (g - 1) *ᵥ y ∈ {y | ∀ x ∈ W, hform s J x y = 0}) ↔ Cond (adj s J K) e g := by
  have hu := (adj_unitary hJK g).2 hg
  have hm := adj_mul (s := s) hJK
  have hi := adj_adj hs hJ hJK
  have heW : ∀ x, e *ᵥ x ∈ W := fun x => (hW _).2 (by rw [Matrix.mulVec_mulVec, he])
  have hp : ∀ y, y ∈ {y | ∀ x ∈ W, hform s J x y = 0} ↔ adj s J K e *ᵥ y = 0 := fun y => by
    rw [← forall_hform_iff s hJK]
    exact ⟨fun h x => h _ (heW x), fun h x hx => by rw [← (hW x).1 hx]; exact h x⟩
  have h33 : adj s J K e * adj s J K e = adj s J K e := by rw [← hm, he]
  simp only [hp]
  constructor
  · rintro ⟨h1, h2, -⟩
    refine ⟨hu, eq_zero_of_mulVec fun y => ?_, eq_zero_of_mulVec fun y => ?_⟩
    · rw [← Matrix.mulVec_mulVec, h1 _ (heW y)]
    · have := (hW _).1 (h2 ((1 - adj s J K e) *ᵥ y) (by
        rw [Matrix.mulVec_mulVec, mul_sub, h33, mul_one, sub_self, Matrix.zero_mulVec]))
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec 1 e, this, Matrix.one_mulVec, sub_self]
  · rintro ⟨-, h2, h3⟩
    refine ⟨fun x hx => ?_, fun y hy => (hW _).2 ?_, fun y => ?_⟩
    · rw [← (hW x).1 hx, Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec]
    · have := congrArg (· *ᵥ y) h3
      simp only [← Matrix.mulVec_mulVec, Matrix.zero_mulVec] at this
      rw [Matrix.sub_mulVec 1 (adj s J K e), hy, Matrix.one_mulVec, sub_zero, Matrix.sub_mulVec 1 e,
        Matrix.one_mulVec, sub_eq_zero] at this
      exact this.symm
    · have c1 : g * e = e := by rwa [sub_mul, one_mul, sub_eq_zero] at h2
      have c2 : adj s J K e * g = adj s J K e := by
        conv_lhs => rw [← c1, hm, mul_assoc, hu, mul_one]
      rw [Matrix.mulVec_mulVec, mul_sub, c2, mul_one, sub_self, Matrix.zero_mulVec]

theorem mem_span_iff {B : Type} [CommRing B] (ι : A →+* B) {e : Matrix n n A} (he : e * e = e)
    (W : Submodule A (n → A)) (hW : ∀ x, x ∈ W ↔ e *ᵥ x = x) (x : n → B) :
    x ∈ Submodule.span B ((fun w : n → A => fun i => ι (w i)) '' (W : Set _)) ↔ e.map ι *ᵥ x = x := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      funext i
      exact (RingHom.map_mulVec ι e w i).symm.trans (congrArg ι (congrFun ((hW w).1 hw) i))
    | zero => exact Matrix.mulVec_zero _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul a x _ hx => rw [Matrix.mulVec_smul, hx]
  · intro h
    have : e.map ι *ᵥ x = ∑ j, x j • fun i => ι ((e *ᵥ Pi.single j 1) i) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm, Pi.single_apply]
    rw [← h, this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, (hW _).2 (by rw [Matrix.mulVec_mulVec, he]), rfl⟩)

theorem exists_idem_mat {E : Type} [Field E] [CharZero E] {s : E →+* E} {J K : Matrix n n E}
    (hs : ∀ a, s (s a) = a) (hJ : cT s J = J) (hJK : J * K = 1) (W : Submodule E (n → E))
    (hW : ∀ x ∈ W, ∀ y ∈ W, hform s J x y = 0) :
    ∃ e : Matrix n n E, e * e = e ∧ e * adj s J K e = 0 ∧ adj s J K e * e = 0 ∧ ∀ x, x ∈ W ↔ e *ᵥ x = x := by
  obtain ⟨W', hc⟩ := W.exists_isCompl
  obtain ⟨p, hp⟩ : ∃ p : Matrix n n E, ∀ x, p *ᵥ x = Submodule.projection W W' hc x :=
    ⟨LinearMap.toMatrix' _, fun x => LinearMap.toMatrix'_mulVec _ x⟩
  have h1 : ∀ x, p *ᵥ x ∈ W := fun x => hp x ▸ Submodule.projection_apply_mem hc x
  have h2 : ∀ x ∈ W, p *ᵥ x = x := fun x hx => (hp x).trans (Submodule.projection_apply_of_mem_left hc hx)
  obtain ⟨e, e1, e2, e3, e4, e5⟩ := exists_idem (p := p) (h := (2⁻¹ : E) • (1 : Matrix n n E))
    (adj_mul (s := s) hJK) (adj_adj hs hJ hJK) (by rw [← add_smul]; norm_num) (fun x => by simp)
    (Matrix.ext_iff_mulVec.2 fun y => by rw [← Matrix.mulVec_mulVec, h2 _ (h1 y)])
    (eq_zero_of_mulVec fun y => by
      rw [← Matrix.mulVec_mulVec]
      exact (forall_hform_iff s hJK p _).1 fun x => hW _ (h1 x) _ (h1 y))
  refine ⟨e, e1, e2, e3, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · conv_lhs => rw [← h2 x hx, Matrix.mulVec_mulVec, e4, h2 x hx]
  · rw [← hx, ← e5, ← Matrix.mulVec_mulVec]
    exact h1 _

end Mat

section Arith

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sub_mem_int (x : E ⊗[F] Af F) :
    ∃ y : E, x - Formalism.UG.inclE (F := F) (Af F) y ∈ IntAf F E := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, add_sub_add_comm]; exact add_mem ha hb⟩
  | tmul e a =>
    have halg : Algebra.IsAlgebraic ℤ E :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
    obtain ⟨m, hm0, hm⟩ := (halg.1 e).exists_integral_multiple
    have hm' : IsIntegral ℤ (m.natAbs • e) := by
      rcases Int.natAbs_eq m with h | h
      · rwa [h, natCast_zsmul] at hm
      · rw [h, neg_smul, natCast_zsmul] at hm
        simpa using hm.neg
    obtain ⟨x, b, hb, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F m.natAbs (Int.natAbs_pos.2 hm0)).1 a
    refine ⟨x • e, ?_⟩
    have : e ⊗ₜ[F] (algebraMap F (Af F) x + m.natAbs • b) - Formalism.UG.inclE (F := F) (Af F) (x • e) =
        algebraMap (𝓞 E) E ⟨m.natAbs • e, hm'⟩ ⊗ₜ[F] b := by
      rw [show algebraMap (𝓞 E) E ⟨m.natAbs • e, hm'⟩ = m.natAbs • e from rfl, TensorProduct.smul_tmul,
        show Formalism.UG.inclE (F := F) (Af F) (x • e) = (x • e) ⊗ₜ[F] (1 : Af F) from rfl, TensorProduct.smul_tmul,
        TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one, add_sub_cancel_left]
    rw [this]
    exact Formalism.UG.P.levelaf_tmul_mem _ hb

omit [NumberField F] in

theorem exists_compact_arch [IsTotallyComplex E] (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) :
    ∃ C : Set (InfinitePlace F → ℂ), IsCompact C ∧
      ∀ z : InfinitePlace F → ℂ, ∃ y : 𝓞 E, (z - fun v => φ v y) ∈ C := by
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.AdeleCocompact.exists_compact_infinite E
  have hc : ∀ v, ∃ c : ℂ →+* ℂ, Continuous c ∧ (∀ z, c (c z) = z) ∧
      ∀ y, c ((InfinitePlace.mk (φ v)).embedding y) = φ v y := fun v => by
    rcases InfinitePlace.embedding_mk_eq (φ v) with h | h
    · exact ⟨RingHom.id ℂ, continuous_id, fun _ => rfl, fun y => by rw [h]; rfl⟩
    · exact ⟨starRingEnd ℂ, Complex.continuous_conj, Complex.conj_conj, fun y => by rw [h]; simp⟩
  choose c hc1 hc2 hc3 using hc
  have hv : ∀ v, (InfinitePlace.mk (φ v)).comap (algebraMap F E) = v := fun v => by
    rw [InfinitePlace.comap_mk, show (φ v).comp (algebraMap F E) = v.embedding from RingHom.ext (hφ v),
      InfinitePlace.mk_embedding]
  let T : InfiniteAdeleRing E → InfinitePlace F → ℂ := fun a v =>
    c v (InfinitePlace.Completion.extensionEmbedding _ (a (InfinitePlace.mk (φ v))))
  have hT : Continuous T := continuous_pi fun v => (hc1 v).comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp (continuous_apply _))
  refine ⟨T '' K, hK.image hT, fun z => ?_⟩
  choose a ha using fun w : InfinitePlace E =>
    InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w)
      (c (w.comap (algebraMap F E)) (z (w.comap (algebraMap F E))))
  obtain ⟨y, hy⟩ := hK' a
  refine ⟨y, _, hy, funext fun v => ?_⟩
  change c v (InfinitePlace.Completion.extensionEmbedding _ (a _ - algebraMap E (InfiniteAdeleRing E) y _)) = _
  rw [map_sub, map_sub, ha, hv, hc2, InfiniteAdeleRing.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbedding_coe]
  exact congrArg (z v - ·) (hc3 v y)

end Arith

section Inst

open Formalism.UG

theorem unitary_conj_iff {n : Type} [Fintype n] [DecidableEq n] {P Q J D : Matrix n n ℂ} (h : P * Q = 1)
    (hD : Pᴴ * J * P = D) (u : Matrix n n ℂ) :
    (Q * u * P)ᴴ * D * (Q * u * P) = D ↔ cT (starRingEnd ℂ) u * J * u = J := by
  have h' : Qᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h, conjTranspose_one]
  have e : (Q * u * P)ᴴ * D * (Q * u * P) = Pᴴ * (uᴴ * J * u) * P := by
    rw [← hD]
    simp only [conjTranspose_mul, mul_assoc]
    rw [← mul_assoc Qᴴ, h', one_mul, ← mul_assoc P Q, h, one_mul]
  rw [e, show cT (starRingEnd ℂ) u = uᴴ from rfl]
  refine ⟨fun k => ?_, fun k => by rw [k, hD]⟩
  have := congrArg (fun m => Qᴴ * m * Q) (k.trans hD.symm)
  simp only [mul_assoc, h, mul_one] at this
  simpa only [← mul_assoc, h', one_mul] using this

variable (I : AutInst)

abbrev Bf : Type := I.E ⊗[I.F] Af I.F

abbrev inc : I.E →+* Bf I := inclE (F := I.F) (Af I.F)

abbrev sf : Bf I →+* Bf I := sigR I.cm.sig (Af I.F)

abbrev MA : Type := (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) × Matrix (Fin I.n) (Fin I.n) (Bf I)

def diag : Matrix (Fin I.n) (Fin I.n) I.E →+* MA I :=
  (RingHom.pi fun v => (I.φ v).mapMatrix).prod (inc I).mapMatrix

abbrev adjE := adj (starRingEnd I.E) I.J I.J⁻¹

abbrev adjV (v : InfinitePlace I.F) := adj (starRingEnd ℂ) (I.J.map (I.φ v)) (I.J⁻¹.map (I.φ v))

abbrev adjF := adj (sf I) (I.J.map (inc I)) (I.J⁻¹.map (inc I))

def adjA : MA I →+ MA I :=
  (AddMonoidHom.pi fun v => (adjV I v).comp (Pi.evalAddMonoidHom _ v)).prodMap (adjF I)

theorem mul_inv_J : I.J * I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ I.J_det.isUnit

theorem mul_inv_J_map {A : Type} [CommRing A] (ι : I.E →+* A) : I.J.map ι * I.J⁻¹.map ι = 1 := by
  rw [← Matrix.map_mul, mul_inv_J, Matrix.map_one _ (map_zero ι) (map_one ι)]

theorem herm_map {A : Type} [CommRing A] {s : A →+* A} (ι : I.E →+* A)
    (h : ∀ a, ι (starRingEnd I.E a) = s (ι a)) : cT s (I.J.map ι) = I.J.map ι := by
  ext i j
  have : starRingEnd I.E (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  change s (ι (I.J j i)) = ι (I.J i j)
  rw [← h, this]

theorem phi_star (v : InfinitePlace I.F) (a : I.E) :
    I.φ v (starRingEnd I.E a) = starRingEnd ℂ (I.φ v a) := I.cm.cmUnram.2.1 _ a

theorem inc_star (a : I.E) : inc I (starRingEnd I.E a) = sf I (inc I a) := rfl

theorem sf_sf (a : Bf I) : sf I (sf I a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul e a => exact congrArg (· ⊗ₜ[I.F] a) (star_star e)

theorem inc_injective : Function.Injective (inc I) := by
  haveI : Nontrivial (Af I.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 I.F)
    have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) := ⟨P, hP.isPrime, hne⟩
    exact ⟨0, 1, fun h => zero_ne_one (α := v.adicCompletion I.F) (congrArg (fun a : Af I.F => a v) h)⟩
  exact Algebra.TensorProduct.includeLeft_injective (S := I.F) (algebraMap I.F (Af I.F)).injective

theorem incM_injective : Function.Injective ((inc I).mapMatrix (m := Fin I.n)) :=
  Matrix.map_injective (inc_injective I)

theorem diag_injective : Function.Injective (diag I) := fun _ _ h => incM_injective I (congrArg Prod.snd h)

theorem diag_adj (x) : diag I (adjE I x) = adjA I (diag I x) :=
  Prod.ext (funext fun v => map_adj _ (phi_star I v) _ _ _) (map_adj _ (inc_star I) _ _ _)

theorem adjA_mul (x y : MA I) : adjA I (x * y) = adjA I y * adjA I x :=
  Prod.ext (funext fun _ => adj_mul (mul_inv_J_map I _) _ _) (adj_mul (mul_inv_J_map I _) _ _)

theorem adjF_adjF (x) : adjF I (adjF I x) = x :=
  adj_adj (sf_sf I) (herm_map I _ (inc_star I)) (mul_inv_J_map I _) _

theorem adjA_adjA (x : MA I) : adjA I (adjA I x) = x :=
  Prod.ext (funext fun v => adj_adj Complex.conj_conj (herm_map I _ (phi_star I v)) (mul_inv_J_map I _) _)
    (adjF_adjF I _)

theorem cond_iff (e g : MA I) : Cond (adjA I) e g ↔
    (∀ v, Cond (adjV I v) (e.1 v) (g.1 v)) ∧ Cond (adjF I) e.2 g.2 :=
  ⟨fun h => ⟨fun v => ⟨congrFun (congrArg Prod.fst h.1) v, congrFun (congrArg Prod.fst h.2.1) v,
      congrFun (congrArg Prod.fst h.2.2) v⟩,
      congrArg Prod.snd h.1, congrArg Prod.snd h.2.1, congrArg Prod.snd h.2.2⟩,
    fun h => ⟨Prod.ext (funext fun v => (h.1 v).1) h.2.1, Prod.ext (funext fun v => (h.1 v).2.1) h.2.2.1,
      Prod.ext (funext fun v => (h.1 v).2.2) h.2.2.2⟩⟩

theorem frame_mul_inv (v) : I.P v * (I.P v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))

theorem frame_inv_mul (v) : (I.P v)⁻¹ * I.P v = 1 := mul_eq_one_comm.1 (frame_mul_inv I v)

theorem frame_cancel (v) (m : Matrix (Fin I.n) (Fin I.n) ℂ) :
    (I.P v)⁻¹ * (I.P v * m * (I.P v)⁻¹) * I.P v = m := by
  rw [← mul_assoc, ← mul_assoc, frame_inv_mul, one_mul, mul_assoc, frame_inv_mul, mul_one]

theorem frame_cancel' (v) (m : Matrix (Fin I.n) (Fin I.n) ℂ) :
    I.P v * ((I.P v)⁻¹ * m * I.P v) * (I.P v)⁻¹ = m := by
  rw [← mul_assoc, ← mul_assoc, frame_mul_inv, one_mul, mul_assoc, frame_mul_inv, mul_one]

def toMA : I.GA →* MA I where
  toFun x := (fun v => I.P v * uMat (x.1 v) * (I.P v)⁻¹, I.fmat x.2)
  map_one' := Prod.ext (funext fun v => by
    change I.P v * 1 * (I.P v)⁻¹ = 1
    rw [mul_one, frame_mul_inv]) rfl
  map_mul' x y := Prod.ext (funext fun v => by
    change I.P v * (uMat (x.1 v) * uMat (y.1 v)) * (I.P v)⁻¹ =
      I.P v * uMat (x.1 v) * (I.P v)⁻¹ * (I.P v * uMat (y.1 v) * (I.P v)⁻¹)
    simp only [mul_assoc]
    rw [← mul_assoc (I.P v)⁻¹, frame_inv_mul, one_mul]) rfl

theorem toMA_injective : Function.Injective (toMA I) := fun x y h =>
  Prod.ext (funext fun v => Subtype.ext (Units.ext (by
    have := congrArg (fun m => (I.P v)⁻¹ * m * I.P v) (congrFun (congrArg Prod.fst h) v)
    exact (frame_cancel I v _).symm.trans (this.trans (frame_cancel I v _)))))
    (Subtype.ext (Units.ext (congrArg Prod.snd h)))

def atPlace (v : InfinitePlace I.F) : MA I →* Matrix (Fin I.n) (Fin I.n) ℂ where
  toFun g := (I.P v)⁻¹ * g.1 v * I.P v
  map_one' := by
    change (I.P v)⁻¹ * 1 * I.P v = 1
    rw [mul_one, frame_inv_mul]
  map_mul' x y := by
    change (I.P v)⁻¹ * (x.1 v * y.1 v) * I.P v = _
    simp only [mul_assoc]
    rw [← mul_assoc (I.P v), frame_mul_inv, one_mul]

theorem unitary_inf {g : MA I} (h : adjA I g * g = 1) (v : InfinitePlace I.F) :
    Formalism.REAL.inUJ (I.ε v) (atPlace I v g) :=
  have h1 : adjV I v (g.1 v) * g.1 v = 1 := congrFun (congrArg Prod.fst h) v
  (unitary_conj_iff (frame_mul_inv I v) (I.P_spec v) (g.1 v)).2 ((adj_unitary (mul_inv_J_map I _) _).1 h1)

theorem unitary_fin {g : MA I} (h : adjA I g * g = 1) :
    cT (sf I) g.2 * I.J.map (inc I) * g.2 = I.J.map (inc I) :=
  have h1 : adjF I g.2 * g.2 = 1 := congrArg Prod.snd h
  (adj_unitary (mul_inv_J_map I _) _).1 h1

def finPart : MA I →* Matrix (Fin I.n) (Fin I.n) (Bf I) := MonoidHom.snd _ _

theorem mem_Gf {g : GL (Fin I.n) (Bf I)} {m : Matrix (Fin I.n) (Fin I.n) (Bf I)} (hm : g.val = m)
    (h : cT (sf I) m * I.J.map (inc I) * m = I.J.map (inc I)) : g ∈ UPts I.cm.sig I.J (Af I.F) := by
  subst hm
  exact h

def ofMA (g : (MA I)ˣ) (h : adjA I g * g = 1) : I.GA :=
  (fun v => ⟨Units.map (atPlace I v) g, unitary_inf I h v⟩,
    ⟨Units.map (finPart I) g, mem_Gf I rfl (unitary_fin I h)⟩)

theorem toMA_ofMA (g : (MA I)ˣ) (h : adjA I g * g = 1) : toMA I (ofMA I g h) = g :=
  Prod.ext (funext fun v => frame_cancel' I v _) rfl

variable {I}

theorem mem_NA_iff {W : Submodule I.E (Fin I.n → I.E)} {e : Matrix (Fin I.n) (Fin I.n) I.E} (he : e * e = e)
    (hW : ∀ x, x ∈ W ↔ e *ᵥ x = x) (x : I.GA) : x ∈ I.NA W ↔ Cond (adjA I) (diag I e) (toMA I x) := by
  rw [cond_iff]
  refine and_congr (forall_congr' fun v => ?_) ?_
  · have h1 : cT (starRingEnd ℂ) (I.P v * uMat (x.1 v) * (I.P v)⁻¹) * I.J.map (I.φ v) *
        (I.P v * uMat (x.1 v) * (I.P v)⁻¹) = I.J.map (I.φ v) :=
      (unitary_conj_iff (frame_mul_inv I v) (I.P_spec v) _).1 (by rw [frame_cancel]; exact (x.1 v).2)
    have h2 := rad_iff (e := e.map (I.φ v)) Complex.conj_conj (herm_map I _ (phi_star I v)) (mul_inv_J_map I _)
      (by rw [← Matrix.map_mul, he]) _ (mem_span_iff (I.φ v) he W hW) h1
    exact h2
  · have h1 : cT (sf I) (I.fmat x.2) * I.J.map (inc I) * I.fmat x.2 = I.J.map (inc I) := x.2.2
    have h2 := rad_iff (e := e.map (inc I)) (sf_sf I) (herm_map I _ (inc_star I)) (mul_inv_J_map I _)
      (by rw [← Matrix.map_mul, he]) _ (mem_span_iff (inc I) he W hW) h1
    exact h2

theorem exists_rat {W : Submodule I.E (Fin I.n → I.E)} {e : Matrix (Fin I.n) (Fin I.n) I.E} (he : e * e = e)
    (hW : ∀ x, x ∈ W ↔ e *ᵥ x = x) (γ : (Matrix (Fin I.n) (Fin I.n) I.E)ˣ) (h : Cond (adjE I) e γ.val) :
    ∃ x ∈ I.GFset ∩ I.NA W, toMA I x⁻¹ = diag I γ := by
  have h1 := h.inv (adj_adj (fun a => star_star a) I.J_herm (mul_inv_J I))
  have h2 := (Cond.map_iff (diag I) (diag_injective I) (diag_adj I)).2 h1
  let u : (MA I)ˣ := Units.map (diag I : _ →* MA I) γ⁻¹
  have h4 : adjA I u * u = 1 := h2.1
  have h3 : toMA I (ofMA I u h4) = diag I γ⁻¹.val := toMA_ofMA I u h4
  have h5 : γ⁻¹ ∈ UJ (starRingEnd I.E) I.J := (adj_unitary (mul_inv_J I) _).1 h1.1
  generalize ofMA I u h4 = x at h3
  refine ⟨x, ⟨⟨γ⁻¹, h5, fun v => ?_, congrArg Prod.snd h3⟩, ?_⟩, ?_⟩
  · exact (frame_cancel I v _).symm.trans
      (congrArg (fun m => (I.P v)⁻¹ * m * I.P v) (congrFun (congrArg Prod.fst h3) v))
  · rw [mem_NA_iff he hW, h3]
    exact h2
  · refine left_inv_eq_right_inv (a := toMA I x) (by rw [← map_mul, inv_mul_cancel, map_one]) ?_
    rw [h3, ← map_mul, Units.inv_mul, map_one]

end Inst

section Top

open Formalism.UG

variable (I : AutInst)

theorem exists_top : ∃ _ : TopologicalSpace (Bf I), IsTopologicalRing (Bf I) ∧ T2Space (Bf I) ∧
    IsCompact (IntAf I.F I.E : Set (Bf I)) ∧ Continuous (sf I) ∧
    (∀ W ∈ 𝓝 (0 : Bf I), ∃ g : ℕ, 1 ≤ g ∧ (g : Bf I) ∈ W) ∧
    IsInducing (fun x : I.Gf => (x : GL (Fin I.n) (Bf I))) := by
  obtain ⟨t, hr, h2, -, ho, hc, hσ, h0⟩ := GlobalTheory.CongTop.exists_topology I.F I.E I.cm.sig
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  obtain ⟨c, hc0, hlow⟩ := Formalism.UG.P.adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨d, hd0, hup⟩ := Formalism.UG.P.adelstabL_upper (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)
  rw [← hL] at hlow hup
  have hun : ∀ g : ℕ, 1 ≤ g → IsUnit (g : I.E ⊗[I.F] Af I.F) := fun g hg => by
    have : (g : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have := this.isUnit.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rwa [map_natCast] at this
  obtain ⟨u, hu⟩ := GlobalTheory.CongTop.isUnit_levelafC I.F I.E hc0
  obtain ⟨v, hv⟩ := GlobalTheory.CongTop.isUnit_levelafC I.F I.E hd0
  rw [← hu] at hlow
  rw [← hv] at hup
  obtain ⟨hΛo, hΛc⟩ := GlobalTheory.CongTop.isOpen_isCompact_of_bounds (IntAf I.F I.E) ho hc I.Lf u v hlow hup
  have hsing : ∀ j, (Pi.single j (u : Bf I) : Fin I.n → Bf I) ∈ I.Lf := fun j => by
    convert hlow (Pi.single j 1) fun i => ?_ using 1
    · funext i
      by_cases h : i = j <;> simp [h]
    · rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
  exact ⟨t, hr, h2, hc, hσ, h0,
    ⟨GlobalTheory.CongTop.top_eq hΛo hΛc u hsing hun h0 _ I.topf I.topf_group I.topf_open I.topf_basis⟩⟩

def intM : Set (Matrix (Fin I.n) (Fin I.n) (Bf I)) := {m | ∀ i j, m i j ∈ IntAf I.F I.E}

theorem exists_sub_mem_intM (x : Matrix (Fin I.n) (Fin I.n) (Bf I)) :
    ∃ y : Matrix (Fin I.n) (Fin I.n) I.E, x - y.map (inc I) ∈ intM I := by
  choose y hy using fun i j => exists_sub_mem_int I.F I.E (x i j)
  exact ⟨Matrix.of y, hy⟩

variable [TopologicalSpace (Bf I)] [IsTopologicalRing (Bf I)]

omit [IsTopologicalRing (Bf I)] in
theorem isCompact_intM (hc : IsCompact (IntAf I.F I.E : Set (Bf I))) : IsCompact (intM I) := by
  have : intM I = Set.pi Set.univ fun _ : Fin I.n => Set.pi Set.univ fun _ : Fin I.n =>
      (IntAf I.F I.E : Set (Bf I)) :=
    Set.ext fun m => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [this]
  exact isCompact_univ_pi fun _ : Fin I.n => isCompact_univ_pi fun _ : Fin I.n => hc

theorem exists_sub_mem_nhds (hc : IsCompact (IntAf I.F I.E : Set (Bf I)))
    (h0 : ∀ W ∈ 𝓝 (0 : Bf I), ∃ g : ℕ, 1 ≤ g ∧ (g : Bf I) ∈ W)
    {K : Set (Matrix (Fin I.n) (Fin I.n) (Bf I))} (hK : K ∈ 𝓝 0) (x : Matrix (Fin I.n) (Fin I.n) (Bf I)) :
    ∃ y : Matrix (Fin I.n) (Fin I.n) I.E, x - (inc I).mapMatrix y ∈ K := by
  have h : ∀ᶠ a : Bf I in 𝓝 0, ∀ m ∈ intM I, a • m ∈ K := by
    refine (isCompact_intM I hc).eventually_forall_of_forall_eventually fun m _ => ?_
    have hc : Continuous fun p : Bf I × Matrix (Fin I.n) (Fin I.n) (Bf I) => p.1 • p.2 :=
      continuous_fst.smul continuous_snd
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hK
  obtain ⟨g, hg, hg'⟩ := h0 _ h
  have hg0 : (g : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨y, hy⟩ := exists_sub_mem_intM I (inc I (g : I.E)⁻¹ • x)
  refine ⟨(g : I.E) • y, ?_⟩
  convert hg' _ hy using 1
  rw [smul_sub, smul_smul, ← map_natCast (inc I) g, ← map_mul, mul_inv_cancel₀ hg0, map_one, one_smul]
  congr 1
  ext i j
  simp

omit [IsTopologicalRing (Bf I)] in

theorem exists_compact_MA (hc : IsCompact (IntAf I.F I.E : Set (Bf I))) :
    ∃ K : Set (MA I), IsCompact K ∧ ∀ x, ∃ y, x - diag I y ∈ K := by
  haveI : IsTotallyComplex I.E := I.cm.cmUnram.1
  obtain ⟨C, hC, hC'⟩ := exists_compact_arch I.F I.E I.φ I.φ_over
  let T : (Fin I.n → Fin I.n → InfinitePlace I.F → ℂ) → InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ :=
    fun m v => Matrix.of fun i j => m i j v
  have hT : Continuous T := continuous_pi fun v => continuous_matrix fun i j =>
    (continuous_apply v).comp (continuous_apply_apply i j)
  refine ⟨(T '' Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C) ×ˢ intM I,
    ((isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC).image hT).prod (isCompact_intM I hc), fun x => ?_⟩
  obtain ⟨y, hy⟩ := exists_sub_mem_intM I x.2
  choose z hz using fun i j => hC' fun v => x.1 v i j - I.φ v (y i j)
  refine ⟨y + Matrix.of fun i j => (z i j : I.E), ⟨_, fun i _ j _ => hz i j, ?_⟩, fun i j => ?_⟩
  · funext v
    ext i j
    change x.1 v i j - I.φ v (y i j) - I.φ v (z i j) = x.1 v i j - I.φ v (y i j + z i j)
    rw [map_add, sub_sub]
  · change x.2 i j - inc I (y i j + z i j) ∈ IntAf I.F I.E
    rw [map_add, ← sub_sub]
    exact sub_mem (hy i j) (Formalism.UG.P.adelstab_incl_int (F := I.F) (z i j))

theorem continuous_adjA (hσ : Continuous (sf I)) : Continuous (adjA I) :=
  (continuous_pi fun v => (continuous_adj Complex.continuous_conj _ _).comp (continuous_apply v)).prodMap
    (continuous_adj hσ _ _)

omit [IsTopologicalRing (Bf I)] in
theorem continuous_toMA (hind : IsInducing (fun x : I.Gf => (x : GL (Fin I.n) (Bf I)))) : Continuous (toMA I) :=
  (continuous_pi fun v => (continuous_const.matrix_mul (Units.continuous_val.comp
    (continuous_subtype_val.comp ((continuous_apply v).comp continuous_fst)))).matrix_mul continuous_const).prodMk
    (Units.continuous_val.comp (hind.continuous.comp continuous_snd))

omit [IsTopologicalRing (Bf I)] in
theorem continuous_ofMA (hind : IsInducing (fun x : I.Gf => (x : GL (Fin I.n) (Bf I)))) {X : Type}
    [TopologicalSpace X] {u : X → (MA I)ˣ} (hu : Continuous u) (h : ∀ p, adjA I (u p) * u p = 1) :
    Continuous fun p => ofMA I (u p) (h p) := by
  refine Continuous.prodMk (continuous_pi fun v => Continuous.subtype_mk ?_ _) ?_
  · have h1 : Continuous fun g : MA I => g.1 v := (continuous_apply v).comp continuous_fst
    have h2 : Continuous fun g : MA I => (I.P v)⁻¹ * g.1 v * I.P v :=
      (continuous_const.matrix_mul h1).matrix_mul continuous_const
    have : Continuous (atPlace I v) := h2
    exact (Continuous.units_map _ this).comp hu
  · rw [hind.continuous_iff]
    have : Continuous (finPart I) := continuous_snd
    exact (Continuous.units_map _ this).comp hu

end Top

theorem strong_approximation : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → (∃ N : Subgroup I.GA, (N : Set I.GA) = I.NA W) ∧ IsClosed (I.NA W) ∧ (∀ m ∈ I.NA W, ((m.1, 1) : I.GA) ∈ I.NA W ∧ ((1, m.2) : I.GA) ∈ I.NA W) ∧ (∀ U : Set I.Gf, U ∈ nhds (1 : I.Gf) → ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, (γ⁻¹ * m).2 ∈ U) ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, γ⁻¹ * m ∈ Cp := by
  intro I W hW
  obtain ⟨t, hr, h2, hc, hσ, h0, hind⟩ := exists_top I
  obtain ⟨e, he, h13, h31, heW⟩ := exists_idem_mat (K := I.J⁻¹) (fun a => star_star a) I.J_herm (mul_inv_J I) W hW.2
  have hN := mem_NA_iff he heW
  have hone : (1 : I.GA) ∈ I.NA W := by
    rw [hN, map_one]
    exact ⟨by rw [GlobalTheory.TwoStepUnipotent.st_one (adjA_mul I) (adjA_adjA I), mul_one], by simp, by simp⟩
  have hh : (2⁻¹ : I.E) • (1 : Matrix (Fin I.n) (Fin I.n) I.E) + (2⁻¹ : I.E) • 1 = 1 := by
    rw [← add_smul]; norm_num
  have hcen : ∀ {A : Type} [CommRing A] (ι : I.E →+* A) (x : Matrix (Fin I.n) (Fin I.n) A),
      ι.mapMatrix ((2⁻¹ : I.E) • 1) * x = x * ι.mapMatrix ((2⁻¹ : I.E) • 1) := by
    intro A _ ι x
    have : ι.mapMatrix ((2⁻¹ : I.E) • (1 : Matrix (Fin I.n) (Fin I.n) I.E)) = ι 2⁻¹ • 1 := by
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [this, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  refine ⟨⟨⟨⟨⟨I.NA W, fun {a b} ha hb => ?_⟩, hone⟩, fun {a} ha => ?_⟩, rfl⟩, ?_,
    fun m hm => ⟨⟨hm.1, hone.2⟩, ⟨hone.1, hm.2⟩⟩, fun V hV m hm => ?_, ?_⟩
  · rw [hN, map_mul]
    exact ((hN a).1 ha).mul (adjA_mul I) ((hN b).1 hb)
  · exact (hN _).2 (Cond.inv (g := (toMA I).toHomUnits a) (adjA_adjA I) ((hN a).1 ha))
  · have c1 := continuous_toMA I hind
    have c2 := continuous_adjA I hσ
    rw [show I.NA W = _ from Set.ext hN]
    exact (isClosed_eq ((c2.comp c1).mul c1) continuous_const).inter
      ((isClosed_eq ((c1.sub continuous_const).mul continuous_const) continuous_const).inter
        (isClosed_eq ((continuous_const.mul (c1.sub continuous_const)).mul continuous_const) continuous_const))
  · obtain ⟨U, u1, u2, -, u4⟩ := exists_param' (adjF I) (adjE I) (inc I).mapMatrix (incM_injective I)
      (map_adj _ (inc_star I) _ _) e _ (continuous_adj hσ _ _) (adj_mul (mul_inv_J_map I _)) (adjF_adjF I)
      he h13 h31 hh (hcen _)
    rw [hind.nhds_eq_comap, mem_comap] at hV
    obtain ⟨V', hV', hVV⟩ := hV
    have h1 : U ⁻¹' V' ∈ 𝓝 (0, 0) := u1.continuousAt.preimage_mem_nhds (by rw [show U (0, 0) = 1 from u2]; exact hV')
    obtain ⟨K₁, k1, K₂, k2, hK⟩ := mem_nhds_prod_iff.1 h1
    obtain ⟨γ, g1, p, hp, g2⟩ := u4 (K₁ ∩ K₂) (exists_sub_mem_nhds I hc h0 (inter_mem k1 k2)) m.2.1
      ((cond_iff I _ _).1 ((hN m).1 hm)).2
    obtain ⟨x, hx, hx'⟩ := exists_rat he heW γ g1
    refine ⟨x, hx, hVV ?_⟩
    have h3 : U p ∈ V' := hK ⟨hp.1.1, hp.2.2⟩
    have h4 : I.fmat (x⁻¹).2 = γ.val.map (inc I) := congrArg Prod.snd hx'
    have h5 : U p = (x⁻¹ * m).2.1 := g2.trans (Units.ext (congrArg (· * I.fmat m.2) h4.symm))
    rwa [h5] at h3
  · obtain ⟨U, u1, -, u3, u4⟩ := exists_param' (adjA I) (adjE I) (diag I) (diag_injective I)
      (diag_adj I) e _ (continuous_adjA I hσ) (adjA_mul I) (adjA_adjA I)
      he h13 h31 hh fun x => Prod.ext (funext fun v => hcen (I.φ v) _) (hcen (inc I) _)
    obtain ⟨K, hK, hK'⟩ := exists_compact_MA I hc
    refine ⟨(fun p => ofMA I (U p) (u3 p).1) '' (K ×ˢ K),
      (hK.prod hK).image (continuous_ofMA I hind u1 fun p => (u3 p).1), ?_, fun m hm => ?_⟩
    · rintro _ ⟨p, -, rfl⟩
      rw [hN, toMA_ofMA]
      exact u3 p
    · obtain ⟨γ, g1, p, hp, g2⟩ := u4 K hK' ((toMA I).toHomUnits m) ((hN m).1 hm)
      obtain ⟨x, hx, hx'⟩ := exists_rat he heW γ g1
      refine ⟨x, hx, p, hp, toMA_injective I ?_⟩
      rw [toMA_ofMA, map_mul, hx', g2]
      rfl

end GlobalTheory.UnipApprox
