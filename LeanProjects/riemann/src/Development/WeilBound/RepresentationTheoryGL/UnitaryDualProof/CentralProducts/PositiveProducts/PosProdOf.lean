import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.PositiveProducts.NontrivialOfNeBot
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Pos

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_untw (X : ℝ) (hX0 : 0 < X) (y : ℝ) (c : ℂ) : ‖c * ((X ^ (-y) : ℝ) : ℂ)‖ * X ^ y = ‖c‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX0 _), mul_assoc,
    ← Real.rpow_add hX0, neg_add_cancel, Real.rpow_zero, mul_one]

theorem norm_combo (X : ℝ) (hX0 : 0 < X) (p y u : ℝ) (c : ℂ) (hsum : p + -y + u = 0) :
    ‖((X ^ p : ℝ) : ℂ) * (c * ((X ^ (-y) : ℝ) : ℂ))‖ * X ^ u = ‖c‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hX0 _), abs_of_pos (Real.rpow_pos_of_pos hX0 _),
    show X ^ p * (‖c‖ * X ^ (-y)) * X ^ u = ‖c‖ * (X ^ p * X ^ (-y) * X ^ u) by ring,
    ← Real.rpow_add hX0, ← Real.rpow_add hX0, hsum, Real.rpow_zero, mul_one]

theorem fac_bound (hT : DerivTop k) (hP : DerivPos k) (hC : CentralSub k) (hLF : LFDeriv k)
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {r : ℕ} (π : GRep k r) (hs : IsSmooth π.ρ)
    (hirr : π.ρ.IsIrreducible) (hu : IsUnitarisable π.ρ) (ha : IsAdmissible π.ρ) (i : ℕ) (hi : i ≤ r) (s : ℝ)
    (x : kˣ) (hx : nabs k x < 1) (cA : ℂ)
    (a : ((derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)).tw s).V) (ha0 : a ≠ 0)
    (hea : ((derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)).tw s).ρ (sc (r - i) x) a = cA • a) :
    ‖cA‖ ≤ nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) ∧
    (‖cA‖ = nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) →
      ∀ (n' h' : ℕ) (e : r = n' + h'), i < h' → Subsingleton (derivB ψ h' (π.cast e)).V) := by
  have hX0 : 0 < nabs k x := nabs_pos' k x
  have hd := untw (derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)) s x cA a hea
  have hm0 : (0 : ℝ) ≤ ((r - i : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · have hu' : IsUnitarisable (derivB ψ 0 (π.cast (Nat.sub_add_cancel hi).symm)).ρ :=
      unit_cast (Nat.sub_add_cancel hi).symm hu
    have h1' := norm_eig_of_unit hu' ha0 hd
    have hcA : ‖cA‖ = nabs k x ^ (((r - 0 : ℕ) : ℝ) * s) := by
      rw [← norm_untw _ hX0 (((r - 0 : ℕ) : ℝ) * s) cA, h1', one_mul]
    have hle : ((r - 0 : ℕ) : ℝ) * (s + (((0 : ℕ) : ℝ) - 1) / 2) ≤ ((r - 0 : ℕ) : ℝ) * s := by
      simp only [Nat.cast_zero]; nlinarith
    refine ⟨hcA ▸ Real.rpow_le_rpow_of_exponent_ge hX0 hx.le hle, fun heq n' h' e hlt => ?_⟩
    exfalso
    have hr : r = 0 := by
      by_contra hr
      have hmpos : (0 : ℝ) < ((r - 0 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
      have hlt2 : ((r - 0 : ℕ) : ℝ) * (s + (((0 : ℕ) : ℝ) - 1) / 2) < ((r - 0 : ℕ) : ℝ) * s := by
        simp only [Nat.cast_zero]; nlinarith
      have := Real.rpow_lt_rpow_of_exponent_gt hX0 hx hlt2
      rw [← hcA, ← heq] at this
      exact lt_irrefl _ this
    omega
  · have hd' := retw (derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)) ((1 - (i : ℝ)) / 2) x _ a hd
    have key := norm_combo (nabs k x) hX0 (((r - i : ℕ) : ℝ) * ((1 - (i : ℝ)) / 2)) (((r - i : ℕ) : ℝ) * s)
      (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) cA (by ring)
    have hT0 : 0 < nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hX0 _
    by_cases htop : ∃ (n' h' : ℕ) (e : (r - i) + i = n' + h'), i < h' ∧
        Nontrivial (derivB ψ h' ((π.cast (Nat.sub_add_cancel hi).symm).cast e)).V
    · have hsD := isSmooth_tw (isSmooth_derivB ψ i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast
        (Nat.sub_add_cancel hi).symm hs)) ((1 - (i : ℝ)) / 2)
      have hlD := lfin_tw (hLF ψ hc (r - i) i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast (Nat.sub_add_cancel hi).symm hs)
        (isAdm_cast (Nat.sub_add_cancel hi).symm ha)) ((1 - (i : ℝ)) / 2)
      obtain ⟨W, ω, hW, hcc, hωx⟩ := hC (r - i) _ hsD hlD x _ a ha0 hd'
      have hlt := hP ψ hc h1 (r - i) i (π.cast (Nat.sub_add_cancel hi).symm) hi1
        (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ hs) (irr_cast _ hirr) (unit_cast _ hu) htop
        W.toSubmodule W.toRepresentation ω (nontrivial_of_ne_bot W hW) (subquot_sub W) hcc x hx
      rw [hωx] at hlt
      have hlt2 : ‖cA‖ < nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) := by
        rw [← key]
        nlinarith [norm_nonneg (((nabs k x ^ (((r - i : ℕ) : ℝ) * ((1 - (i : ℝ)) / 2)) : ℝ) : ℂ) *
          (cA * ((nabs k x ^ (-(((r - i : ℕ) : ℝ) * s)) : ℝ) : ℂ)))]
      exact ⟨hlt2.le, fun heq => absurd heq hlt2.ne⟩
    · have hnt : Nontrivial (derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)).V := ⟨⟨a, 0, ha0⟩⟩
      have htop' : ∀ (n' h' : ℕ) (e : (r - i) + i = n' + h'), i < h' →
          Subsingleton (derivB ψ h' ((π.cast (Nat.sub_add_cancel hi).symm).cast e)).V :=
        fun n' h' e hlt => not_nontrivial_iff_subsingleton.1 (fun hn => htop ⟨n', h', e, hlt, hn⟩)
      obtain ⟨-, hun⟩ := hT ψ hc h1 (r - i) i (π.cast (Nat.sub_add_cancel hi).symm) hi1
        (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ hs) (irr_cast _ hirr) (unit_cast _ hu) hnt htop'
      have h1' := norm_eig_of_unit hun ha0 hd'
      have heq : ‖cA‖ = nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) := by
        rw [← key, h1', one_mul]
      refine ⟨heq.le, fun _ n' h' e hlt => ?_⟩
      have := htop' n' h' ((Nat.sub_add_cancel hi).trans e) hlt
      rwa [cast_cast] at this

variable (k)

theorem posProd_of : DerivTop k → DerivPos k → GlobalTheory.RgGu.Leib.LeibnizOrd k → LFDeriv k → CentralSub k → EigProd k →
    EigFilt k → PosProdD k := by
  intro hT hP hL hLF hC hE hF ψ hc h1 r t π₁ π₂ hs₁ hi₁ hu₁ hs₂ hi₂ hu₂ n h e htop n' j e' hj x hx v c hv0 hv
  have ha₁ := adm π₁ hs₁ hi₁
  have ha₂ := adm π₂ hs₂ hi₂
  obtain ⟨i, hi, cA, cB, hil, rfl, ⟨a, ha0, hea⟩, b, hb0, heb⟩ :=
    pipe hL hLF hE hF ψ hc h1 π₁ π₂ hs₁ ha₁ hs₂ ha₂ j n' e' x c v hv0 hv
  obtain ⟨b1, t1⟩ := fac_bound hT hP hC hLF ψ hc h1 π₁ hs₁ hi₁ hu₁ ha₁ i hi.1 _ x hx cA a ha0 hea
  obtain ⟨b2, t2⟩ := fac_bound hT hP hC hLF ψ hc h1 π₂ hs₂ hi₂ hu₂ ha₂ (j - i) hi.2 _ x hx cB b hb0 heb
  have hX0 : 0 < nabs k x := nabs_pos' k x
  have hsz : (r - i) + (t - (j - i)) = n' := by omega
  have hexp : ((r - i : ℕ) : ℝ) * ((((j - i : ℕ) : ℝ) / 2) + ((i : ℝ) - 1) / 2) +
      ((t - (j - i) : ℕ) : ℝ) * (((i : ℝ) / 2) + (((j - i : ℕ) : ℝ) - 1) / 2) = (n' : ℝ) * ((j : ℝ) - 1) / 2 := by
    have h3 : ((r - i : ℕ) : ℝ) + ((t - (j - i) : ℕ) : ℝ) = (n' : ℝ) := by exact_mod_cast hsz
    have h4 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := Nat.cast_sub hil
    rw [h4, ← h3]; ring
  rw [← hexp, Real.rpow_add hX0, norm_mul]
  have hB1 := Real.rpow_pos_of_pos hX0 (((r - i : ℕ) : ℝ) * ((((j - i : ℕ) : ℝ) / 2) + ((i : ℝ) - 1) / 2))
  have hB2 := Real.rpow_pos_of_pos hX0 (((t - (j - i) : ℕ) : ℝ) * (((i : ℝ) / 2) + (((j - i : ℕ) : ℝ) - 1) / 2))
  by_contra hge
  have eqA : ‖cA‖ = nabs k x ^ (((r - i : ℕ) : ℝ) * ((((j - i : ℕ) : ℝ) / 2) + ((i : ℝ) - 1) / 2)) := by
    by_contra hne
    exact hge (lt_of_le_of_lt (mul_le_mul_of_nonneg_left b2 (norm_nonneg _))
      (mul_lt_mul_of_pos_right (lt_of_le_of_ne b1 hne) hB2))
  have eqB : ‖cB‖ = nabs k x ^ (((t - (j - i) : ℕ) : ℝ) * (((i : ℝ) / 2) + (((j - i : ℕ) : ℝ) - 1) / 2)) := by
    by_contra hne
    exact hge (lt_of_le_of_lt (mul_le_mul_of_nonneg_right b1 (norm_nonneg _))
      (mul_lt_mul_of_pos_left (lt_of_le_of_ne b2 hne) hB1))
  have top1 := t1 eqA
  have top2 := t2 eqB
  obtain ⟨hnt, -⟩ := htop
  obtain ⟨v', hv'⟩ := @exists_ne _ hnt 0
  have hsc : sc n (1 : kˣ) = 1 := map_one _
  have hv1 : (derivB ψ h ((π₁.prod π₂).cast e)).ρ (sc n 1) v' = (1 : ℂ) • v' := by simp [hsc]
  obtain ⟨i', hi', -, -, hil', -, ⟨a', ha', -⟩, b', hb', -⟩ :=
    pipe hL hLF hE hF ψ hc h1 π₁ π₂ hs₁ ha₁ hs₂ ha₂ h n e 1 1 v' hv' hv1
  by_cases hcase : i < i'
  · exact ha' (@Subsingleton.elim _ (top1 (r - i') i' (Nat.sub_add_cancel hi'.1).symm hcase) a' 0)
  · exact hb' (@Subsingleton.elim _ (top2 (t - (h - i')) (h - i') (Nat.sub_add_cancel hi'.2).symm (by omega)) b' 0)

end PositivityTheory.RgUd.Prod.Pos
