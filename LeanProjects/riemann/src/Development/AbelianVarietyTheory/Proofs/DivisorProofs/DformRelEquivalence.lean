import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsOrbitalTermEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitFibreSwap

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKDef.Regroup

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul' (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem dform_rel_equivalence : Equivalence (DForm.Rel (G := G)) := by
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_⟩
    simp [sh_one_eq]
  · obtain ⟨y, s, hs, hβ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_⟩
    have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
      rw [← sh_mul', Units.inv_mul, sh_one_eq]
    rw [hβ]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
      inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
  · obtain ⟨y, s, hs, hβ⟩ := h
    obtain ⟨y', s', hs', hβ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_⟩
    rw [hβ', hβ, Units.val_mul, sh_mul']
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]

theorem minpoly_conj (y : G.Cˣ) (x : G.C) : minpoly G.F ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) = minpoly G.F x :=
  minpoly.algEquiv_eq (Pair.innerAlgEquiv G.F y) x

def mkPair (B : DForm G) (y : GlobalTheory.LKCx.grp G B.β)
    (h : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable) :
    DPair G where
  β := B.β
  γ := y.1.1
  c := y.1.2
  sym := B.sym
  sim := y.2.1
  reg := h
  trivAf := B.trivAf
  posR := B.posR

theorem mkPair_rel_conj (B : DForm G) (w z w' : GlobalTheory.LKCx.grp G B.β) (hw : z * w * z⁻¹ = w') (h h') :
    (mkPair B w h).Rel (mkPair B w' h') := by
  subst hw
  have hz := z.2.1
  have hs : (0 : ℚ) < (z.1.2 : ℚ) := z.2.2
  refine ⟨z.1.1, ((z.1.2 : ℚ))⁻¹, inv_pos.mpr hs, ?_, ?_⟩
  · show (B.β : G.C) = algebraMap ℚ G.C ((z.1.2 : ℚ))⁻¹ * ((z.1.1 : G.C) * B.β * sh G (z.1.1 : G.C))
    rw [hz, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs.ne', map_one, one_mul]
  · rfl

theorem transport_sim (β : G.C) (y γ : G.Cˣ) (s c : ℚ) (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β) :
    ((y * γ * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * γ * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C c * (algebraMap ℚ G.C s * (y * β * sh G y)) := by
  have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← sh_mul', Units.inv_mul, sh_one_eq]
  have e' : ∀ X : G.C, sh G (y : G.C) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * X) = X := by
    intro X; rw [← mul_assoc, e, one_mul]
  have h' : ∀ X : G.C, (γ : G.C) * (β * (sh G (γ : G.C) * X)) = c • (β * X) := by
    intro X; rw [← mul_assoc β, ← mul_assoc, ← mul_assoc, h, Algebra.smul_def, mul_assoc]
  simp only [Units.val_mul, sh_mul', ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc, e',
    Units.inv_mul_cancel_left, h', smul_smul, mul_comm s c]

theorem finsum_eq_mem_of_supp {α : Type} (F : α → ℂ) (s : Set α) (h : Function.support F ⊆ s) :
    ∑ᶠ i ∈ s, F i = ∑ᶠ i, F i := by
  rw [← finsum_mem_inter_support, Set.inter_eq_right.2 h, finsum_mem_support]

section Sum

variable (G)

abbrev Idx : Type := Σ q : DFCls G, ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β)

def RegAt (x : Idx G) : Prop :=
  RegIrr G (((Quotient.out x.2 : GlobalTheory.LKCx.grp G (Quot.out x.1).β).1.1 : G.Cˣ) : G.C)

def toCls (x : {x : Idx G // RegAt G x}) : DCls G :=
  Quot.mk _ (mkPair (Quot.out x.1.1) (Quotient.out x.1.2) ⟨x.2.1, x.2.2.1⟩)

variable {G}

theorem toCls_injective : Function.Injective (toCls G) := by
  rintro ⟨⟨q, c⟩, h⟩ ⟨⟨q', c'⟩, h'⟩ e
  obtain ⟨y, s, hs, hβ, hγ⟩ := (DPair.mk_eq_iff _ _).1 e
  have hq : q = q' := by
    rw [← Quot.out_eq q, ← Quot.out_eq q']
    exact Quot.sound ⟨y, s, hs, hβ⟩
  subst hq
  have hc : (Quotient.out c).1.2 = (Quotient.out c').1.2 :=
    (DPair.rel_pol_c_term p G _ _ ⟨y, s, hs, hβ, hγ⟩).2.1
  change ((Quot.out q).β : G.C) = algebraMap ℚ G.C s * ((y : G.C) * (Quot.out q).β * sh G y) at hβ
  have hz : (y : G.C) * (Quot.out q).β * sh G y =
      algebraMap ℚ G.C ((Units.mk0 s⁻¹ (inv_ne_zero hs.ne') : ℚˣ) : ℚ) * (Quot.out q).β := by
    rw [Units.val_mk0]
    calc (y : G.C) * (Quot.out q).β * sh G y
        = algebraMap ℚ G.C s⁻¹ * (algebraMap ℚ G.C s * ((y : G.C) * (Quot.out q).β * sh G y)) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs.ne', map_one, one_mul]
      _ = _ := by rw [← hβ]
  let z : GlobalTheory.LKCx.grp G (Quot.out q).β := ⟨(y, Units.mk0 s⁻¹ (inv_ne_zero hs.ne')), hz, by
    show (0 : ℚ) < ((Units.mk0 s⁻¹ (inv_ne_zero hs.ne') : ℚˣ) : ℚ)
    rw [Units.val_mk0]; exact inv_pos.mpr hs⟩
  have hzc : z * Quotient.out c * z⁻¹ = Quotient.out c' := by
    apply Subtype.ext
    apply Prod.ext
    · exact hγ.symm
    · show Units.mk0 s⁻¹ (inv_ne_zero hs.ne') * (Quotient.out c).1.2 * (Units.mk0 s⁻¹ (inv_ne_zero hs.ne'))⁻¹ =
        (Quotient.out c').1.2
      rw [mul_comm, inv_mul_cancel_left, hc]
  have hcc : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound (isConj_iff.2 ⟨z, hzc⟩)
  subst hcc
  rfl

theorem mem_range_toCls
    (hpos : ∀ (B : DForm G) (y : G.Cˣ) (s : ℚ), (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s)
    (d : DCls G) (hd : Irreducible (Quot.out d).pol) : d ∈ Set.range (toCls G) := by
  obtain ⟨y, s, hs, hβ⟩ : DForm.Rel (DForm.ofDPair (Quot.out d)) (Quot.out (Quot.mk _ (DForm.ofDPair (Quot.out d))
      : DFCls G)) := by
    have h := Quot.eq.1 (Quot.out_eq (Quot.mk DForm.Rel (DForm.ofDPair (Quot.out d))))
    exact dform_rel_equivalence.symm (dform_rel_equivalence.eqvGen_iff.1 h)
  set P := Quot.out d with hP
  set q : DFCls G := Quot.mk _ (DForm.ofDPair P) with hq
  change ((Quot.out q).β : G.C) = algebraMap ℚ G.C s * ((y : G.C) * P.β * sh G y) at hβ
  have hsim : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) * (Quot.out q).β * sh G ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (P.c : ℚ) * (Quot.out q).β := by
    rw [hβ]; exact transport_sim _ _ _ _ _ P.sim
  let w : GlobalTheory.LKCx.grp G (Quot.out q).β := ⟨(y * P.γ * y⁻¹, P.c), hsim, hpos _ _ _ hsim⟩
  have hmw : minpoly G.F ((w.1.1 : G.Cˣ) : G.C) = P.pol := by
    show minpoly G.F (((y * P.γ * y⁻¹ : G.Cˣ)) : G.C) = minpoly G.F (P.γ : G.C)
    rw [Units.val_mul, Units.val_mul, minpoly_conj]
  obtain ⟨z, hz⟩ := isConj_iff.1 (Quotient.exact (Quotient.out_eq (ConjClasses.mk w)).symm)
  have hmin : minpoly G.F (((Quotient.out (ConjClasses.mk w)).1.1 : G.Cˣ) : G.C) = P.pol := by
    rw [← hz, ← hmw]
    show minpoly G.F ((((z.1.1 * w.1.1) * z.1.1⁻¹ : G.Cˣ)) : G.C) = _
    rw [Units.val_mul, Units.val_mul, minpoly_conj]
  have hreg : RegAt G ⟨q, ConjClasses.mk w⟩ := by
    unfold RegAt RegIrr; rw [hmin]; exact ⟨P.reg.1, P.reg.2, hd⟩
  refine ⟨⟨⟨q, ConjClasses.mk w⟩, hreg⟩, ?_⟩
  have hw : (minpoly G.F ((w.1.1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F ((w.1.1 : G.Cˣ) : G.C)).Separable := by
    rw [hmw]; exact P.reg
  have h1 : P.Rel (mkPair (Quot.out q) w hw) := ⟨y, s, hs, hβ, rfl⟩
  have h2 := mkPair_rel_conj (Quot.out q) w z _ hz hw ⟨hreg.1, hreg.2.1⟩
  have h3 := ((DPair.rel_equivalence G).trans h1 h2)
  exact ((DPair.mk_eq_iff _ _).2 ((DPair.rel_equivalence G).symm h3)).trans (Quot.out_eq d)

variable (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1))
  (f' : Gr G 1 → ℂ)

def summand (d : DCls G) : ℂ :=
  if Irreducible (Quot.out d).pol then wt (Quot.out d).pol * (Quot.out d).term Kf f 1 K' f' else 0

theorem summand_toCls
    (hterm : ∀ (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β),
      P.term Kf f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' ⟨(P.γ, P.c), hm⟩)
    (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g)
    (x : Idx G) (h : RegAt G x) :
    wt (minpoly G.F (((Quotient.out x.2 : GlobalTheory.LKCx.grp G (Quot.out x.1).β).1.1 : G.Cˣ) : G.C)) *
      centSum (GlobalTheory.LKCx.toAfF G (Quot.out x.1).β (Quot.out x.1).trivAf.choose
          (Quot.out x.1).trivAf.choose_spec.choose (Quot.out x.1).trivAf.choose_spec.choose_spec)
        (GlobalTheory.LKCx.toP1 G (Quot.out x.1).β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' (Quotient.out x.2) =
      summand wt Kf f K' f' (toCls G ⟨x, h⟩) := by
  set M := mkPair (Quot.out x.1) (Quotient.out x.2) ⟨h.1, h.2.1⟩ with hM
  obtain ⟨hpol, -, ht⟩ := DPair.rel_pol_c_term p G _ _ (DPair.rel_out M)
  have hirr : Irreducible (Quot.out (Quot.mk DPair.Rel M : DCls G)).pol := by
    rw [← hpol]; exact h.2.2
  show _ = summand wt Kf f K' f' (Quot.mk _ M)
  unfold summand
  rw [if_pos hirr, ← hpol, ← ht Kf f 1 K' f' one_pos hf hf', hterm M (Quotient.out x.2).2]
  rfl

theorem regroup_of
    (hpos : ∀ (B : DForm G) (y : G.Cˣ) (s : ℚ), (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s)
    (hfin : {q : DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term Kf f 1 K' f' ≠ 0}.Finite)
    (hterm : ∀ (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β),
      P.term Kf f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' ⟨(P.γ, P.c), hm⟩)
    (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) :
    GlobalTheory.LKDef.dSumIrr G wt Kf f 1 K' f' =
      ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
        if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
          wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
            centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                (Quot.out q).trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' (Quotient.out c)
        else 0 := by
  set F := summand wt Kf f K' f' with hF
  have hL : GlobalTheory.LKDef.dSumIrr G wt Kf f 1 K' f' = ∑ᶠ d, F d := rfl
  have hsuppF : Function.support F ⊆
      {q : DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term Kf f 1 K' f' ≠ 0} := by
    intro d hd
    rw [Function.mem_support, hF, summand] at hd
    split_ifs at hd with hi
    · exact ⟨hi, right_ne_zero_of_mul hd⟩
    · exact absurd rfl hd
  have hfinF := hfin.subset hsuppF
  have hrange : Function.support F ⊆ Set.range (toCls G) := fun d hd => mem_range_toCls hpos d (hsuppF hd).1
  let H : Idx G → ℂ := fun x => if h : RegAt G x then F (toCls G ⟨x, h⟩) else 0
  have hR : ∀ (q : DFCls G) (c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β)),
      (if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
          wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
            centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                (Quot.out q).trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' (Quotient.out c)
        else 0) = H ⟨q, c⟩ := by
    intro q c
    by_cases h : RegAt G ⟨q, c⟩
    · have h' : RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) := h
      simp only [H, dif_pos h]
      rw [if_pos h']
      exact summand_toCls wt Kf f K' f' hterm hf hf' ⟨q, c⟩ h
    · have h' : ¬ RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) := h
      simp only [H, dif_neg h]
      rw [if_neg h']
  have hsuppH : (Function.support H).Finite := by
    apply ((hfinF.preimage (toCls_injective).injOn).image Subtype.val).subset
    intro x hx
    rw [Function.mem_support] at hx
    by_cases h : RegAt G x
    · simp only [H, dif_pos h] at hx
      exact ⟨⟨x, h⟩, hx, rfl⟩
    · simp only [H, dif_neg h] at hx
      exact absurd rfl hx
  have hRHS : (∑ᶠ q : DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
      (if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
          wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
            centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                (Quot.out q).trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f' (Quotient.out c)
        else 0)) = ∑ᶠ q : DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β), H ⟨q, c⟩ :=
    finsum_congr fun q => finsum_congr fun c => hR q c
  rw [hRHS, ← GlobalTheory.OrbitFibre.finsum_sigma_iter H hsuppH, hL]
  have h1 : ∑ᶠ x, H x = ∑ᶠ x : {x // RegAt G x}, F (toCls G x) := by
    rw [← finsum_eq_mem_of_supp H (Set.range Subtype.val) ?_,
      finsum_mem_range Subtype.val_injective]
    · apply finsum_congr
      intro x
      simp only [H, dif_pos x.2]
    · intro x hx
      rw [Function.mem_support] at hx
      by_cases h : RegAt G x
      · exact ⟨⟨x, h⟩, rfl⟩
      · simp only [H, dif_neg h] at hx
        exact absurd rfl hx
  rw [h1, ← finsum_mem_range (toCls_injective (G := G)), finsum_eq_mem_of_supp F _ hrange]

end Sum

theorem regroup_main
    (hposT : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) (y : G.Cˣ) (s : ℚ),
  (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s)
    (hfinT : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {q : GlobalTheory.LKDef.DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite)
    (htermT : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : GlobalTheory.LKDef.DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      P.term L.K.toSubgroup f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' ⟨(P.γ, P.c), hm⟩) :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 := by
  intro p _ G ha wt L f hf hfb K' f' hf' hfb'
  exact regroup_of wt L.K.toSubgroup f K' f' (hposT p G) (hfinT p G ha L f hf hfb K' f' hf' hfb')
    (fun P hm => htermT p G P hm L f hf K' f' hf') (fun k hk g => hf.2.2.1 k hk g) hf'.2.2.1

end GlobalTheory.LKDef.Regroup
