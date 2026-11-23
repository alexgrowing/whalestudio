import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCongrPowE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvLiftStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaDR

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem map_mk_eq_iff {R : Type} [CommRing R] {d : ℕ} (e : R) (P P' : Matrix (Fin d) (Fin d) R) :
    P.map (Ideal.Quotient.mk (Ideal.span {e})) = P'.map (Ideal.Quotient.mk (Ideal.span {e})) ↔
      ∀ a b, e ∣ P a b - P' a b := by
  constructor
  · intro h a b
    have h1 := congrFun (congrFun h a) b
    simp only [Matrix.map_apply] at h1
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  · intro h
    ext a b
    simp only [Matrix.map_apply]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h a b))

theorem map_smul_mat {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R') (c : R)
    (P : Matrix (Fin d) (Fin d) R) : (c • P).map f = f c • P.map f := by
  ext a b; simp

theorem map_sub_mat {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R')
    (P P' : Matrix (Fin d) (Fin d) R) : (P - P').map f = P.map f - P'.map f := by
  ext a b; simp

theorem map_mul_three {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R')
    (P₁ P₂ P₃ : Matrix (Fin d) (Fin d) R) : (P₁ * P₂ * P₃).map f = P₁.map f * P₂.map f * P₃.map f := by
  simp only [Matrix.map_mul]

theorem map_entry_sub_smul_one {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R') (c : R)
    (P : Matrix (Fin d) (Fin d) R) (a b : Fin d) :
    f ((P - c • (1 : Matrix (Fin d) (Fin d) R)) a b) = (P.map f) a b - (f c • (1 : Matrix (Fin d) (Fin d) R')) a b := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  · simp [Matrix.one_apply_ne hab]

theorem mat_approx (bk : BK K) (m : ℕ) {d : ℕ} (x : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) :
    ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ a b,
      toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ (l : bk.DS bk.ρ₀) ^ k * x a b - toDisc l (X : bk.S) bk.ρ₀ (s a b) := by
  choose k s hs using fun p : Fin d × Fin d => GlobalTheory.BKLim.WApprox.exists_congr_pow_E l K bk m (x p.1 p.2)
  refine ⟨∑ p, k p, fun a b => (l : bk.S) ^ (∑ p, k p - k (a, b)) * s (a, b), fun a b => ?_⟩
  have hle : k (a, b) ≤ ∑ p, k p := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (a, b))
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  have hc' : ∑ p, k p - k (a, b) = c := by omega
  show toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ (l : bk.DS bk.ρ₀) ^ (∑ p, k p) * x a b -
    toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (∑ p, k p - k (a, b)) * s (a, b))
  rw [hc', hc, pow_add, map_mul, map_pow, map_natCast]
  have h := dvd_mul_of_dvd_right (hs (a, b)) ((l : bk.DS bk.ρ₀) ^ c)
  convert h using 1
  ring

theorem mat_lift (bk : BK K) (m : ℕ) {d : ℕ} (x : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) :
    ∃ (k : ℕ) (γ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣
      toDisc l (X : bk.S) bk.ρ₀ (γ a b) - (l : bk.DS bk.ρ₀) ^ k * x a b) ∧
      ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev (γ a b)) - bk.ev (γ a b) := by
  obtain ⟨k₀, s, hs⟩ := mat_approx bk 1 x
  obtain ⟨k₁, hk₁⟩ := GlobalTheory.T.exists_invariant_lift_mod_E l K bk m
  choose γ hγ1 hγ2 using fun p : Fin d × Fin d => hk₁ (s p.1 p.2)
  refine ⟨k₁ + k₀, fun a b => γ (a, b), fun a b => ?_, fun g a b => hγ2 (a, b) g⟩
  have h1 := map_dvd (toDisc l (X : bk.S) bk.ρ₀) (hγ1 (a, b))
  have hs1 := hs a b
  rw [pow_one] at hs1
  have h2 := dvd_mul_of_dvd_right hs1 ((l : bk.DS bk.ρ₀) ^ k₁)
  have h3 := dvd_sub h1 h2
  convert h3 using 1
  simp only [map_sub, map_mul, map_pow, map_natCast]
  ring

theorem dvd_gal_E (bk : BK K) (g : GQ l) : bk.ev bk.E ∣ Per.σA g (bk.ev bk.E) := by
  rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
  have h : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  rw [h, map_zero]

theorem dvd_of_iS_dvd (bk : BK K) (s : bk.S) (h : bk.iS bk.E ∣ bk.iS s) : bk.E ∣ s := by
  have h2 : bk.ev bk.E ^ 1 ∣ bk.ev s :=
    (GlobalTheory.BSP.ainf_dvd_of_disc_dvd l K bk (bk.ev s)).1 1 (by rw [pow_one]; exact h)
  have h3 := (GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk 1).2.1 s h2
  rwa [pow_one] at h3

end GlobalTheory.BKLim.BetaDR

open GlobalTheory.BKLim.BetaDR in

theorem GlobalTheory.BKLim.exists_beta_of_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (φε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (H : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap bk.ev i → IsUnit H → (∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → ∀ a b, bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) a b) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) → ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b := by
  intro l _ K bk d N κ φε H i hi hH hΛ hmain m₀
  obtain ⟨hmap, hgal, -, hρ0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  set m := m₀ + 1 with hm

  obtain ⟨u, hu⟩ := isUnit_toDisc_frobS_E l K bk
  obtain ⟨U, hU⟩ := hH
  set v : bk.DS bk.ρ₀ := ((u⁻¹ : (bk.DS bk.ρ₀)ˣ) : bk.DS bk.ρ₀) with hv
  set H₁ : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := v ^ N • H with hH₁
  set H₁' : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := (u : bk.DS bk.ρ₀) ^ N • ((U⁻¹ : (Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀))ˣ) : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) with hH₁'
  have hvu : v * (u : bk.DS bk.ρ₀) = 1 := Units.inv_mul u
  have hH11 : H₁ * H₁' = 1 := by
    rw [hH₁, hH₁', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_pow, hvu, one_pow, one_smul, ← hU, Units.mul_inv]
  have hH12 : H₁' * H₁ = 1 := by
    rw [hH₁, hH₁', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_pow, mul_comm, hvu, one_pow, one_smul, ← hU,
      Units.inv_mul]

  have hmapt : ∀ P : Matrix (Fin d) (Fin d) bk.S, (P.map (toDisc l (X : bk.S) bk.ρ₀)).map i = P.map bk.iS := by
    intro P; ext a b; exact hi.ext _
  set A := H₁.map i with hA
  set A' := H₁'.map i with hA'
  have hAA' : A * A' = 1 := by rw [hA, hA', ← Matrix.map_mul, hH11, Matrix.map_one _ (map_zero i) (map_one i)]
  have hA'A : A' * A = 1 := by rw [hA, hA', ← Matrix.map_mul, hH12, Matrix.map_one _ (map_zero i) (map_one i)]
  have hiv : i v * bk.iS (frobS l bk.a bk.E) = 1 := by
    have e : bk.iS (frobS l bk.a bk.E) = i (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) := (hi.ext _).symm
    rw [e, ← hu, ← map_mul, hvu, map_one]
  have key : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G →
      A * (φε g).map bk.iA = κ g * A.map G := by
    intro g G hG
    have hGiv : G (i v) * G (bk.iS (frobS l bk.a bk.E)) = 1 := by rw [← map_mul, hiv, map_one]
    have e1 : A = i v ^ N • H.map i := by rw [hA, hH₁, map_smul_mat, map_pow]
    have e2 : A.map G = G (i v) ^ N • (H.map i).map G := by rw [e1, map_smul_mat, map_pow]
    calc A * (φε g).map bk.iA = i v ^ N • (H.map i * (φε g).map bk.iA) := by rw [e1, Matrix.smul_mul]
      _ = (i v ^ N * G (i v) ^ N) • (G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA)) := by
          rw [smul_smul, mul_assoc, ← mul_pow, hGiv, one_pow, mul_one]
      _ = (i v ^ N * G (i v) ^ N) • (bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) := by
          rw [hmain g G hG]
      _ = G (i v) ^ N • (κ g * (H.map i).map G) := by
          rw [smul_smul, mul_comm (i v ^ N), mul_assoc, ← mul_pow, hiv, one_pow, mul_one]
      _ = κ g * A.map G := by rw [e2, Matrix.mul_smul]
  obtain ⟨k₁, Λ, hΛE, hΛinv⟩ := hΛ m
  obtain ⟨k₂, Hs, hHsE, hHsinv⟩ := mat_lift bk m H₁
  obtain ⟨k₃, β, hβ⟩ := mat_approx bk m (H₁' * Λ.map (toDisc l (X : bk.S) bk.ρ₀) * Hs.map (toDisc l (X : bk.S) bk.ρ₀))
  have hM : (H₁' * Λ.map (toDisc l (X : bk.S) bk.ρ₀) * Hs.map (toDisc l (X : bk.S) bk.ρ₀)).map i =
      A' * Λ.map bk.iS * Hs.map bk.iS := by
    rw [Matrix.map_mul, Matrix.map_mul, hmapt, hmapt]
  set L := Λ.map bk.iS with hL
  set Hm := Hs.map bk.iS with hHm
  set B := β.map bk.iS with hB
  have hβD : ∀ a b, bk.iS bk.E ^ m ∣ ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)) a b - B a b := by
    intro a b
    have h := map_dvd i (hβ a b)
    rw [map_pow, hi.ext, map_sub, map_mul, map_pow, map_natCast, hi.ext] at h
    rw [← hM]
    exact h
  refine ⟨k₁ + k₂ + k₃, β, fun a b => ?_, fun g a b => ?_⟩
  · apply dvd_of_iS_dvd bk
    rw [map_entry_sub_smul_one]
    set q := Ideal.Quotient.mk (Ideal.span {bk.iS bk.E}) with hq
    have hE1 : bk.iS bk.E ∣ bk.iS bk.E ^ m := dvd_pow_self _ (by omega)
    have eL : L.map q = (q (l : bk.DA bk.ρ₀) ^ k₁) • 1 := by
      have h : L.map q = ((bk.iS ((l : bk.S) ^ k₁)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))).map q :=
        (map_mk_eq_iff _ _ _).2 fun a b => by rw [← map_entry_sub_smul_one]; exact map_dvd bk.iS (hΛE a b)
      rw [h, map_smul_mat, Matrix.map_one _ (map_zero q) (map_one q)]
      simp only [map_pow, map_natCast]
    have eH : Hm.map q = (q (l : bk.DA bk.ρ₀) ^ k₂) • A.map q := by
      have h : Hm.map q = ((l : bk.DA bk.ρ₀) ^ k₂ • A).map q :=
        (map_mk_eq_iff _ _ _).2 fun a b => by
          have h1 := map_dvd i (hHsE a b)
          rw [hi.ext, map_sub, map_mul, map_pow, map_natCast, hi.ext] at h1
          exact h1
      rw [h, map_smul_mat, map_pow]
    have eB : B.map q = ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map q :=
      ((map_mk_eq_iff _ _ _).2 fun a b => dvd_trans hE1 (hβD a b)).symm
    have hq0 : (bk.iS ((l : bk.S) ^ (k₁ + k₂ + k₃)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))).map q = B.map q := by
      rw [eB, map_smul_mat q, map_smul_mat q, map_mul_three, eL, eH, Matrix.map_one _ (map_zero q) (map_one q)]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
      rw [← Matrix.map_mul, hA'A, Matrix.map_one _ (map_zero q) (map_one q)]
      congr 1
      simp only [map_pow, map_natCast]
      ring
    exact (map_mk_eq_iff _ _ _).1 hq0.symm a b
  · obtain ⟨G, hG⟩ := hgal bk.ρ₀ hρ0 (g : GQ l)
    set q := Ideal.Quotient.mk (Ideal.span {bk.iS bk.E ^ m}) with hq
    have hGE : bk.iS bk.E ∣ G (bk.iS bk.E) := by
      obtain ⟨w, hw⟩ := dvd_gal_E bk (g : GQ l)
      show bk.iS bk.E ∣ G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev bk.E))
      rw [hG.ext, hw, map_mul]
      exact dvd_mul_right _ _
    have hGd : ∀ x, bk.iS bk.E ^ m ∣ x → bk.iS bk.E ^ m ∣ G x := by
      rintro x ⟨y, rfl⟩
      rw [map_mul, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hGE m) _
    have hGm : ∀ P P' : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), (∀ a b, bk.iS bk.E ^ m ∣ P a b - P' a b) →
        ∀ a b, bk.iS bk.E ^ m ∣ (P.map G) a b - (P'.map G) a b := by
      intro P P' h a b
      simp only [Matrix.map_apply]
      rw [← map_sub]
      exact hGd _ (h a b)
    have hφA : (φε g).map bk.iA * A'.map G = A' * κ g := by
      have hAG : A.map G * A'.map G = 1 := by
        rw [← Matrix.map_mul, hAA', Matrix.map_one _ (map_zero G) (map_one G)]
      calc (φε g).map bk.iA * A'.map G = A' * (A * (φε g).map bk.iA) * A'.map G := by
            rw [← Matrix.mul_assoc A', hA'A, Matrix.one_mul]
        _ = A' * κ g * (A.map G * A'.map G) := by rw [key g G hG]; simp only [Matrix.mul_assoc]
        _ = A' * κ g := by rw [hAG, Matrix.mul_one]
    have eΛ : (κ g * L.map G).map q = L.map q := (map_mk_eq_iff _ _ _).2 (hΛinv g G hG)
    have eH : (Hm.map G).map q = Hm.map q := (map_mk_eq_iff _ _ _).2 fun a b => by
      have h := map_dvd bk.iA (hHsinv g a b)
      rw [map_pow, map_sub] at h
      have e : G (bk.iS (Hs a b)) = bk.iA (Per.σA (g : GQ l) (bk.ev (Hs a b))) := hG.ext _
      show bk.iS bk.E ^ m ∣ G (bk.iS (Hs a b)) - bk.iS (Hs a b)
      rw [e]
      exact h
    have eB : B.map q = ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map q := ((map_mk_eq_iff _ _ _).2 hβD).symm
    have eBG : (B.map G).map q = (((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map G).map q :=
      ((map_mk_eq_iff _ _ _).2 (hGm _ _ hβD)).symm
    have hid : (φε g).map bk.iA * ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map G =
        (l : bk.DA bk.ρ₀) ^ k₃ • (A' * (κ g * L.map G) * Hm.map G) := by
      rw [map_smul_mat, map_pow, map_natCast, map_mul_three, Matrix.mul_smul]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hφA]
      simp only [Matrix.mul_assoc]
    have hfin : ((φε g).map bk.iA * B.map G).map q = B.map q := by
      rw [Matrix.map_mul, eBG, ← Matrix.map_mul, hid, eB, map_smul_mat q _ (A' * (κ g * L.map G) * Hm.map G),
        map_smul_mat q _ (A' * L * Hm), map_mul_three q A' (κ g * L.map G) (Hm.map G), eΛ, eH, map_mul_three q A' L Hm]
    have hdiv := (map_mk_eq_iff _ _ _).1 hfin a b
    have hσ : ((β.map bk.ev).map (Per.σA (g : GQ l))).map bk.iA = B.map G := by
      ext a b
      exact (hG.ext _).symm
    have hmat : (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev).map bk.iA =
        (φε g).map bk.iA * B.map G - B := by
      rw [map_sub_mat, Matrix.map_mul, hσ]
      rfl
    have h2 : bk.iS bk.E ^ m ∣ bk.iA ((φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b) := by
      have h := congrFun (congrFun hmat a) b
      rw [Matrix.map_apply] at h
      rw [h]
      exact hdiv
    have h3 := (GlobalTheory.BSP.ainf_dvd_of_disc_dvd l K bk _).1 m h2
    exact dvd_trans (pow_dvd_pow _ (by omega)) h3
