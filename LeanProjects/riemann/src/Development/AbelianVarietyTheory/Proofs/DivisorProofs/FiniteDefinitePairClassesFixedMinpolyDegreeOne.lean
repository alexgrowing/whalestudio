import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkolemNoetherConjugacy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOutsideFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicConjugateOfTrivialisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldInvolutionSimilitudeCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairsRatioLocallyRationalTimesNormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKDefFin

open GlobalTheory.LKDef GlobalTheory.LKMid.PairConj

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem form_conj (v : InfinitePlace G.F) (β y : G.Cˣ) (x : Fin G.n → ℂ) :
    star x ⬝ᵥ ((G.gram v * G.psi v (((y * β * shU G y)⁻¹ : G.Cˣ) : G.C)) *ᵥ x) =
      star (G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x) ⬝ᵥ
        ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ (G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x)) := by
  have e1 : (((y * β * shU G y)⁻¹ : G.Cˣ) : G.C) =
      sh G ((y⁻¹ : G.Cˣ) : G.C) * (((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C)) := by
    simp only [_root_.mul_inv_rev, Units.val_mul]; rfl
  have e2 : G.psi v (sh G ((y⁻¹ : G.Cˣ) : G.C)) =
      (G.gram v)⁻¹ * (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * G.gram v := G.psi_star v _
  have hg : G.gram v * (G.gram v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (Ne.isUnit (G.gram_det v))
  have e3 : G.gram v * G.psi v (((y * β * shU G y)⁻¹ : G.Cˣ) : G.C) =
      (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v ((y⁻¹ : G.Cˣ) : G.C) := by
    rw [e1, map_mul, map_mul, e2]
    calc G.gram v * ((G.gram v)⁻¹ * (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * G.gram v *
          (G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v ((y⁻¹ : G.Cˣ) : G.C)))
        = (G.gram v * (G.gram v)⁻¹) * (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * G.gram v *
          (G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v ((y⁻¹ : G.Cˣ) : G.C)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, Matrix.one_mul]; simp only [Matrix.mul_assoc]
  rw [e3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

def conjD (P : DPair G) (y : G.Cˣ) : DPair G where
  β := y * P.β * shU G y
  γ := y * P.γ * y⁻¹
  c := P.c
  sym := by
    simp only [Units.val_mul, shU_val, sh_mul, sh_sh, P.sym, mul_assoc]
  sim := by
    have hs := P.sim
    have h1 := unop_mul_inv G.star y
    simp only [Units.val_mul, shU_val, sh_mul]
    calc _ = (y : G.C) * (P.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * P.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G P.γ) *
            sh G y := by simp only [mul_assoc]
      _ = y * ((P.γ : G.C) * P.β * sh G P.γ) * sh G y := by
            rw [Units.inv_mul, show sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 from h1, mul_one, mul_one]
      _ = _ := by
            rw [hs, ← mul_assoc, ← mul_assoc, ← Algebra.commutes, mul_assoc _ (y : G.C), mul_assoc, mul_assoc]
  reg := by
    have e : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) = conjAlg G y P.γ := by simp [conjAlg]
    rw [e, minpoly.algHom_eq (conjAlg G y) (conjAlg_injective G y)]
    exact P.reg
  trivAf := by
    obtain ⟨x, t, hx⟩ := P.trivAf
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conj_val] at h
    exact ⟨_, t, h⟩
  posR := by
    intro v x hx
    have hM : G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x ≠ 0 := by
      intro h0; apply hx
      have e : G.psi v (y : G.C) *ᵥ (G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, ← map_mul, Units.mul_inv, map_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    rw [form_conj]
    exact P.posR v _ hM

theorem conjD_β (P : DPair G) (y : G.Cˣ) :
    (((conjD P y).β : G.Cˣ) : G.C) = (y : G.C) * P.β * sh G y := conj_val P.β y

theorem exists_conj (P : DPair G) (y : G.Cˣ) :
    ∃ P' : DPair G, P.Rel P' ∧ P'.γ = y * P.γ * y⁻¹ ∧ P'.c = P.c ∧
      ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
        ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (hx' : Triv G (AfP p) P'.β x' t),
          P'.toAf x' t hx' P'.self = P.toAf x t hx P.self := by
  refine ⟨conjD P y, ⟨y, 1, one_pos, ?_, rfl⟩, rfl, rfl, ?_⟩
  · rw [map_one, one_mul, conjD_β]
  · intro x t hx
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conjD_β] at h
    refine ⟨_, h, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹) *
          Units.map (inC G (AfP p)).toMonoidHom (y * P.γ * y⁻¹) *
          (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)⁻¹ =
        x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹
      simp only [map_mul, map_inv]
      group
    · rfl

theorem norm_sim (P : DPair G) :
    Algebra.norm ℚ (P.γ : G.C) * Algebra.norm ℚ (sh G P.γ) = (P.c : ℚ) ^ Module.finrank ℚ G.C := by
  have h := congrArg (Algebra.norm ℚ) P.sim
  rw [map_mul, map_mul, map_mul, Algebra.norm_algebraMap] at h
  have hb : Algebra.norm ℚ (P.β : G.C) ≠ 0 := (P.β.isUnit.map (Algebra.norm ℚ)).ne_zero
  apply mul_right_cancel₀ hb
  rw [← h]; ring

theorem c_eq_or_eq_neg (P P' : DPair G) (hγ : P'.γ = P.γ) : P'.c = P.c ∨ P'.c = -P.c := by
  have h1 := norm_sim P
  have h2 := norm_sim P'
  rw [hγ, h1] at h2
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  rcases (pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg]))

theorem exists_ne_zero_of_term_ne_zero (P : DPair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (h : P.term Kf f r K φ ≠ 0) :
    ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
      f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 := by
  unfold DPair.term at h
  split_ifs at h with hd
  · unfold DPair.termAt pointSum at h
    obtain ⟨q, hq⟩ := not_forall.1 (fun hc => h (finsum_eq_zero_of_forall_eq_zero hc))
    refine ⟨_, _, P.trivAf.choose_spec.choose_spec, (Quotient.out q).1, fun h0 => hq ?_⟩
    rw [h0, zero_mul, mul_zero]
  · exact absurd rfl h

end GlobalTheory.LKDefFin

noncomputable section

namespace GlobalTheory.LKDefFin

open GlobalTheory.LKDef

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem exists_triv_toAf_eq_conj (P : DPair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (g : G.GAf) : ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (t' : (AfP p)ˣ)
    (hx' : Triv G (AfP p) P.β x' t'), P.toAf x' t' hx' P.self = g⁻¹ * P.toAf x t hx P.self * g := by
  refine ⟨g.1.1⁻¹ * x, t * g.1.2⁻¹, ?_, ?_⟩
  · exact mul_triv_star (starT G.star (AfP p)) (inC G (AfP p) P.β) ((g.1.1⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
      (x : AfP p ⊗[ℚ] G.C) (t : AfP p) ((g.1.2⁻¹ : (AfP p)ˣ) : AfP p) hx (mem_uGroup.1 (g⁻¹).2)
  · apply Subtype.ext
    apply Prod.ext
    · change (g.1.1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ * (g.1.1⁻¹ * x)⁻¹ =
        g.1.1⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) * g.1.1
      group
    · change Units.map (algebraMap ℚ (AfP p)).toMonoidHom P.c =
        g.1.2⁻¹ * Units.map (algebraMap ℚ (AfP p)).toMonoidHom P.c * g.1.2
      rw [mul_comm g.1.2⁻¹, inv_mul_cancel_right]

theorem quot_commute_and_fixed (P Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) :
    ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.γ = Q.γ * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) ∧
    (Q.β : G.C) * sh G ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * ((Q.β⁻¹ : G.Cˣ) : G.C) = ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) := by
  have hmul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := fun x y => by
    simp only [sh, map_mul, MulOpposite.unop_mul]
  have hinv : ∀ y : G.Cˣ, sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := fun y => by
    rw [← hmul, Units.inv_mul, sh_one_eq]
  have hP := P.sim
  have hQ := Q.sim
  rw [hγ, hc] at hP
  refine ⟨?_, ?_⟩
  · have e1 : ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.γ * (Q.β * sh G Q.γ) = algebraMap ℚ G.C Q.c * P.β := by
      calc ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.γ * (Q.β * sh G Q.γ)
          = ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * (Q.γ * Q.β * sh G Q.γ) := by simp only [mul_assoc]
        _ = algebraMap ℚ G.C Q.c * (((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.β) := by
          rw [hQ]; simp only [← Algebra.smul_def, mul_smul_comm]
        _ = _ := by rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    have e2 : (Q.γ : G.C) * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * (Q.β * sh G Q.γ) = algebraMap ℚ G.C Q.c * P.β := by
      rw [← hP, Units.val_mul]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
    have e3 : (Q.β : G.C) * sh G Q.γ * (sh G ((Q.γ⁻¹ : G.Cˣ) : G.C) * ((Q.β⁻¹ : G.Cˣ) : G.C)) = 1 := by
      rw [mul_assoc, ← mul_assoc (sh G Q.γ), hinv, one_mul, Units.mul_inv]
    have e4 := congrArg (· * (sh G ((Q.γ⁻¹ : G.Cˣ) : G.C) * ((Q.β⁻¹ : G.Cˣ) : G.C))) (e1.trans e2.symm)
    rwa [mul_assoc _ (_ * sh G _), mul_assoc _ (_ * sh G _), e3, mul_one, mul_one] at e4
  · have h := hinv Q.β
    rw [Q.sym] at h
    rw [Units.val_mul, hmul, P.sym, ← mul_assoc, h, one_mul]

theorem rel_of_ratio (P Q P₁ : DPair G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hP : P.γ = P₁.γ) (hQ : Q.γ = P₁.γ) (hy : (y : G.C) * P₁.γ = P₁.γ * y)
    (ha : ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) * y = y * ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C))
    (hr : ((Q.β * P₁.β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C s * ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) *
      ((y : G.C) * ((P₁.β : G.C) * sh G y * ((P₁.β⁻¹ : G.Cˣ) : G.C)))) : DPair.Rel P Q := by
  refine ⟨y, s, hs, ?_, ?_⟩
  · have h1 : ((Q.β * P₁.β⁻¹ : G.Cˣ) : G.C) * (P₁.β : G.C) = Q.β := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    have h2 : ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) * (P₁.β : G.C) = P.β := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    rw [← h1, hr, ← h2]
    generalize ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) = a at ha ⊢
    calc algebraMap ℚ G.C s * a * ((y : G.C) * ((P₁.β : G.C) * sh G y * ((P₁.β⁻¹ : G.Cˣ) : G.C))) * P₁.β
        = algebraMap ℚ G.C s * ((a * y) * ((P₁.β : G.C) * sh G y) *
            (((P₁.β⁻¹ : G.Cˣ) : G.C) * P₁.β)) := by simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, mul_one, ha]; simp only [mul_assoc]
  · have hy' : y * P₁.γ = P₁.γ * y := Units.ext (by simpa using hy)
    rw [hQ, hP, hy', mul_inv_cancel_right]

theorem supp_compact (L : G.Level) (f : G.GAf → ℂ)
    (hT : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) :
    ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  obtain ⟨-, -, -, S, hS⟩ := hT
  refine ⟨⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)),
    S.isCompact_biUnion fun s _ => (L.compact.prod L.compact).image (by fun_prop), fun g hg => ?_⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
  exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

theorem finite_of_compact (Ω : Set G.GAf) (hΩ : IsCompact Ω) (γ₀ : G.Cˣ)
    (hirr : Irreducible (minpoly G.F (γ₀ : G.C))) (c₀ : ℚˣ) :
    {q : DCls G | ∃ P : DPair G, (Quot.mk DPair.Rel P : DCls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω}.Finite := by
  set Y : Set (DPair G) := {P | P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω} with hYdef
  have hset : {q : DCls G | ∃ P : DPair G, (Quot.mk DPair.Rel P : DCls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω} =
      Quot.mk DPair.Rel '' Y := by
    ext q; constructor
    · rintro ⟨P, rfl, h⟩; exact ⟨P, h, rfl⟩
    · rintro ⟨P, h, rfl⟩; exact ⟨P, rfl, h⟩
  rw [hset]
  rcases Y.eq_empty_or_nonempty with hY | ⟨P₁, hP₁⟩
  · rw [hY, Set.image_empty]; exact Set.finite_empty
  have hirr₁ : Irreducible (minpoly G.F (P₁.γ : G.C)) := by rw [hP₁.1]; exact hirr
  obtain ⟨L, _, _, ι, c, hinj, hcent, hc, hcc⟩ :=
    GlobalTheory.T.exists_numberField_involution_similitudeCentralizer p G P₁.β P₁.γ P₁.c P₁.sym P₁.sim hirr₁ P₁.reg.1
  obtain ⟨S, hloc⟩ := GlobalTheory.T.definitePairs_ratio_locally_rational_times_norm p G Ω hΩ P₁ L ι c hinj hcent hc
  have hγ : ∀ P ∈ Y, P.γ = P₁.γ := fun P hP => hP.1.trans hP₁.1.symm
  have hcc' : ∀ P ∈ Y, P.c = P₁.c := fun P hP => hP.2.1.trans hP₁.2.1.symm
  have ha : ∀ P ∈ Y, ∃ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) := fun P hP =>
    (hcent _).1 (quot_commute_and_fixed P P₁ (hγ P hP) (hcc' P hP)).1
  set X : Set L := {a | ∃ P ∈ Y, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C)} with hXdef
  obtain ⟨R, hR⟩ := GlobalTheory.FixedNormCls.finite_classes_mod_rat_norms L c hcc S X (by
    rintro a ⟨P, hP, hPa⟩
    refine ⟨fun h0 => ?_, hinj ?_, fun v hv => hloc P (hγ P hP) (hcc' P hP) hP.2.2 a hPa v hv⟩
    · rw [h0, map_zero] at hPa
      exact (P.β * P₁.β⁻¹).ne_zero hPa.symm
    · rw [hc, hPa]; exact (quot_commute_and_fixed P P₁ (hγ P hP) (hcc' P hP)).2)
  let good : L → Prop → DPair G → Prop := fun b s P => P ∈ Y ∧ ∃ (a : L) (q : ℚ) (z : L),
    ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) ∧ (0 < q ↔ s) ∧ q ≠ 0 ∧ z ≠ 0 ∧ a = algebraMap ℚ L q * b * (z * c z)
  let rep : L × Bool → DPair G := fun bs => if h : ∃ P, good bs.1 (bs.2 = true) P then h.choose else P₁
  refine ((R ×ˢ (Finset.univ : Finset Bool) : Finset (L × Bool)).finite_toSet.image
    (fun bs => Quot.mk DPair.Rel (rep bs))).subset ?_
  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨a, hPa⟩ := ha P hP
  obtain ⟨b, hb, q, z, hq, hz, hab⟩ := hR a ⟨P, hP, hPa⟩
  have hex : ∃ P', good b (decide (0 < q) = true) P' := ⟨P, hP, a, q, z, hPa, decide_eq_true_iff.symm, hq, hz, hab⟩
  refine ⟨(b, decide (0 < q)), Finset.mem_coe.2 (Finset.mem_product.2 ⟨hb, Finset.mem_univ _⟩), ?_⟩
  have hrep : rep (b, decide (0 < q)) = hex.choose := dif_pos hex
  obtain ⟨hP', a', q', z', hPa', hsgn, hq', hz', hab'⟩ := hex.choose_spec
  simp only [hrep]
  apply Quot.sound
  set P' := hex.choose
  have hpos : 0 < q / q' := by
    have hs : (0 < q' ↔ 0 < q) := by simpa using hsgn
    rcases lt_or_gt_of_ne hq with h | h
    · exact div_pos_of_neg_of_neg h (lt_of_le_of_ne (not_lt.1 (fun h' => absurd (hs.1 h') (not_lt.2 h.le))) hq')
    · exact div_pos h (hs.2 h)
  set w : L := z / z' with hw
  have hw0 : w ≠ 0 := div_ne_zero hz hz'
  let y : G.Cˣ := Units.map ι.toMonoidHom (Units.mk0 w hw0)
  have hy : (y : G.C) = ι w := rfl
  have hrat : a = algebraMap ℚ L (q / q') * a' * (w * c w) := by
    rw [hab, hab', hw, map_div₀, map_div₀]
    have hcz' : c z' ≠ 0 := by
      intro h; apply hz'; have := congrArg c h; rwa [hcc, map_zero] at this
    have hq'' : algebraMap ℚ L q' ≠ 0 := (map_ne_zero _).2 hq'
    field_simp
  apply rel_of_ratio P' P P₁ y (q / q') hpos (hγ P' hP') (hγ P hP)
  · rw [hy]; exact ((hcent _).2 ⟨w, rfl⟩)
  · rw [hy, ← hPa', ← map_mul, ← map_mul, mul_comm]
  · rw [← hPa, hrat, hy, ← hPa', ← hc, map_mul, map_mul, map_mul, AlgHom.commutes]

theorem finite_classes_fixed_gamma (L : G.Level) (f : G.GAf → ℂ)
    (hT : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (γ₀ : G.Cˣ)
    (hirr : Irreducible (minpoly G.F (γ₀ : G.C))) (c₀ : ℚˣ) :
    {q : DCls G | ∃ P : DPair G, (Quot.mk DPair.Rel P : DCls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
        f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0}.Finite := by
  obtain ⟨Ω, hΩ, hf⟩ := supp_compact L f hT
  refine (finite_of_compact Ω hΩ γ₀ hirr c₀).subset ?_
  rintro q ⟨P, rfl, hγ, hc, x, t, hx, g, hne⟩
  obtain ⟨x', t', hx', he⟩ := exists_triv_toAf_eq_conj P x t hx g
  exact ⟨P, rfl, hγ, hc, x', t', hx', he ▸ hf _ hne⟩

end GlobalTheory.LKDefFin

open GlobalTheory.LKDef GlobalTheory.LKDefFin in

theorem GlobalTheory.LKDefFin.finite_classes_of_pol : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      ∀ P0 : Polynomial G.F, {q : GlobalTheory.LKDef.DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
        (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf _ K' f' _ _ P0
  by_cases hne : {q : DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
      (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hne
    have hirr₀ : Irreducible (minpoly G.F ((Quot.out q₀).γ : G.C)) := hq₀.2.1
    refine ((finite_classes_fixed_gamma L f hf (Quot.out q₀).γ hirr₀ (Quot.out q₀).c).union
      (finite_classes_fixed_gamma L f hf (Quot.out q₀).γ hirr₀ (-(Quot.out q₀).c))).subset ?_
    intro q hq
    obtain ⟨x, t, hx, g, hg⟩ := exists_ne_zero_of_term_ne_zero _ _ _ _ _ _ hq.2.2
    have hpol : minpoly G.F ((Quot.out q₀).γ : G.C) = minpoly G.F ((Quot.out q).γ : G.C) :=
      hq₀.1.trans hq.1.symm
    have hirrq : Irreducible (minpoly G.F ((Quot.out q).γ : G.C)) := hq.2.1
    obtain ⟨y, hy⟩ := GlobalTheory.LKCx.units_conj_of_minpoly_eq_of_irreducible p G (Quot.out q₀).γ (Quot.out q).γ hpol hirrq
    obtain ⟨P', hrel, hγ, hc', htr⟩ := exists_conj (Quot.out q) y
    obtain ⟨x', hx', he⟩ := htr x t hx
    have hq' : (Quot.mk DPair.Rel P' : DCls G) = q := by
      rw [← Quot.sound hrel]; exact Quot.out_eq q
    have hγ' : P'.γ = (Quot.out q₀).γ := by
      rw [hγ]; apply Units.ext; rw [hy]; simp
    have hg' : f (g⁻¹ * P'.toAf x' t hx' P'.self * g) ≠ 0 := by rw [he]; exact hg
    rcases c_eq_or_eq_neg (Quot.out q₀) P' hγ' with hc | hc
    · exact Or.inl ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
    · exact Or.inr ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Set.finite_empty
