import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaBoundedDenominatorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinCompactnessStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameCocyclesLinkedStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.DRLim

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

private theorem hom_frobenius_pt {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
    (f : WittVector p R →+* WittVector p R) (x : WittVector p R) :
    f (WittVector.frobenius x) = WittVector.frobenius (f x) := by
  have h1 : ∀ z : WittVector p R, (p : WittVector p R) ∣ WittVector.frobenius z - z ^ p := by
    intro z
    rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have : WittVector.constantCoeff (WittVector.frobenius z - z ^ p) = 0 := by
      rw [map_sub, map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP, sub_self]
    exact this
  have h2 : ∀ y : R, WittVector.frobenius (WittVector.teichmuller p y) = WittVector.teichmuller p y ^ p := by
    intro y
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have h3 : ∀ n : ℕ, f (WittVector.frobenius x) - WittVector.frobenius (f x) ∈
      Ideal.span {(p : WittVector p R) ^ n} := by
    intro n
    have hnil : IsNilpotent ((p : ℕ) : WittVector p R ⧸ Ideal.span {(p : WittVector p R) ^ n}) := by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    have := WittVector.eq_of_apply_teichmuller_eq
      ((Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})).comp (f.comp WittVector.frobenius))
      ((Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})).comp (WittVector.frobenius.comp f)) hnil (by
        intro y
        obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv R p n).surjective y
        simp only [RingHom.comp_apply]
        rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton, h2, iterateFrobeniusEquiv_def]
        simp only [map_pow]
        rw [pow_right_comm]
        exact (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub (h1 _) n))
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun this x)
  rw [← sub_eq_zero]
  refine WittVector.ext fun n => ?_
  rw [WittVector.zero_coeff]
  exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).1 (h3 _) n (Nat.lt_succ_self n)

theorem σA_frob (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) :=
  hom_frobenius_pt (Per.σA g) x

theorem map_mk_eq_zero {R : Type} [CommRing R] {m n : Type} (I : Ideal R) (M : Matrix m n R) :
    M.map (Ideal.Quotient.mk I) = 0 ↔ ∀ i j, M i j ∈ I := by
  rw [← Matrix.ext_iff]
  simp only [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]

theorem msub {R B : Type} [CommRing R] [CommRing B] {m n : Type} (f : R →+* B) (M M' : Matrix m n R) :
    (M - M').map f = M.map f - M'.map f := Matrix.map_sub _ (map_sub f) _ _

theorem map_smul_one {R B : Type} [CommRing R] [CommRing B] {n : Type} [DecidableEq n] (f : R →+* B) (a : R) :
    (a • (1 : Matrix n n R)).map f = f a • (1 : Matrix n n B) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, h]

theorem exists_of_mem_sup {R : Type} [CommRing R] {a b x : R} (h : x ∈ Ideal.span {a} ⊔ Ideal.span {b}) :
    ∃ u v, x = b * u + a * v := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  exact ⟨z, y, by ring⟩

theorem σA_mem (bk : BK K) (g : GQ l) (n M : ℕ) (a : Ainf l)
    (ha : a ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M}) :
    Per.σA g a ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M} := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hE : bk.ev bk.E ∣ Per.σA g (bk.ev bk.E) := by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  obtain ⟨w, hw⟩ := hE
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, hw, mul_pow]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩)) (Ideal.mem_sup_right ?_)
  exact Ideal.mem_span_singleton.2 ⟨Per.σA g z * w ^ M, by ring⟩

theorem ev_mem (bk : BK K) (n M : ℕ) (s : bk.S) (hs : s ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ M}) :
    bk.ev s ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M} := by
  have := Ideal.mem_map_of_mem bk.ev hs
  rwa [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow, map_pow,
    map_natCast] at this

end GlobalTheory.BKLim.DRLim

open GlobalTheory.BKLim.DRLim in

theorem GlobalTheory.BKLim.isDR_of_links : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsDR) → F₀.IsDR := by
  intro l _ K bk d N ρ tw F F₀ r hlink hDR M
  obtain ⟨c, hc⟩ := GlobalTheory.T.breuilKisin_beta_bounded_denominators l K bk (M + 1)
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.exists_invariant_lift_mod_E l K bk (M + 1)
  choose γf hγ1 hγ2 using hk₀
  have htf1 := GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk 1
  have htfM := GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk (M + 1)
  let Xm : (Fin d × Fin d → bk.S) → Matrix (Fin d) (Fin d) bk.S := fun x => Matrix.of fun i j => x (i, j)
  let I₁ : ℕ → Ideal bk.S := fun n => Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ 1}
  let J : ℕ → Ideal (Ainf l) := fun n => Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ (M + 1)}
  let Φ : ↥(GK K) → Matrix (Fin d) (Fin d) bk.S → Matrix (Fin d) (Fin d) (Ainf l) := fun g β =>
    (F₀.ε g).map WittVector.frobenius * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev
  let Q : ℕ → (Fin d × Fin d → bk.S) → Prop := fun n x =>
    (∀ i j, (Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j ∈ I₁ n) ∧
      ∀ g i j, Φ g (Xm x) i j ∈ J n
  have hmono : ∀ n x, Q (n + 1) x → Q n x := by
    intro n x ⟨h1, h2⟩
    have hl : ∀ {R : Type} [CommRing R] (y : R), Ideal.span {(l : R) ^ (n + 1)} ≤ Ideal.span {(l : R) ^ n} :=
      fun _ => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n))
    exact ⟨fun i j => sup_le_sup_right (hl (0 : bk.S)) _ (h1 i j),
      fun g i j => sup_le_sup_right (hl (0 : Ainf l)) _ (h2 g i j)⟩
  have hpert : ∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)}) →
      Q n y := by
    intro n x y ⟨h1, h2⟩ hd
    have hle : Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)} ≤ I₁ n :=
      sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (by omega))) _
    have hD : ∀ i j, (Xm x - Xm y) i j ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)} :=
      fun i j => hd (i, j)
    refine ⟨fun i j => ?_, fun g i j => ?_⟩
    · have e : (Xm y - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j =
          (Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j - (Xm x - Xm y) i j := by
        simp only [Matrix.sub_apply]; ring
      rw [e]
      exact sub_mem (h1 i j) (hle (hD i j))
    · have e : Φ g (Xm y) = Φ g (Xm x) - ((F₀.ε g).map WittVector.frobenius *
          ((Xm x - Xm y).map bk.ev).map (Per.σA (g : GQ l)) - (Xm x - Xm y).map bk.ev) := by
        simp only [Φ, msub, Matrix.mul_sub]; abel
      rw [e, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply]
      refine sub_mem (h2 g i j) (sub_mem (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_) ?_)
      · exact σA_mem bk _ n (M + 1) _ (ev_mem bk n (M + 1) _ (hD k j))
      · exact ev_mem bk n (M + 1) _ (hD i j)
  have hex : ∀ n, ∃ x, Q n x := by
    intro n
    obtain ⟨m, hnm, R, G, hRT, hRG⟩ := hlink n
    obtain ⟨k', β'', hβ''⟩ := hDR m (M + 1)
    obtain ⟨β', hβ'⟩ := hc N (tw.d' m) _ (F m) k' β'' hβ''
    have hrel := GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked l K bk N N d (tw.d' m) n (fun g => (ρ g).val) (fun g => (tw.ρ' m g).val) F₀ (F m)
      (tw.Pi m) R (fun g i j => (pow_dvd_pow _ hnm).trans ((tw.onto m).equi g i j)) hRT
    let φS := frobS l bk.a
    let γ : Matrix (Fin (tw.d' m)) (Fin d) bk.S := Matrix.of fun i j => γf (φS (G i j))
    let Mx : Matrix (Fin d) (Fin d) bk.S := R.map φS * β' * γ
    refine ⟨fun ij => Mx ij.1 ij.2, ?_, ?_⟩
    ·
      let q := Ideal.Quotient.mk (I₁ n)
      have hE : ∀ s : bk.S, bk.E ∣ s → q s = 0 := fun s hs =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (by simpa using hs)))
      have hL : ∀ s : bk.S, (l : bk.S) ^ n ∣ s → q s = 0 := fun s hs =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 hs))
      have hq1 : β'.map q = q ((l : bk.S) ^ c) • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) _) := by
        have : (β' - (l : bk.S) ^ c • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) bk.S)).map q = 0 := by
          ext i j; exact hE _ (hβ'.1 i j)
        rwa [msub, map_smul_one, sub_eq_zero] at this
      have hq2 : γ.map q = q ((l : bk.S) ^ k₀) • (G.map φS).map q := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, γ, smul_eq_mul, ← map_mul]
        exact (Ideal.Quotient.eq.2 (Ideal.Quotient.eq_zero_iff_mem.1 (hE _ (hγ1 _))))
      have hq3 : (R.map φS).map q * (G.map φS).map q = q ((l : bk.S) ^ r) • (1 : Matrix (Fin d) (Fin d) _) := by
        have : (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)).map (q.comp φS) = 0 := by
          ext i j
          refine hL _ ?_
          have := map_dvd φS (hRG i j)
          simpa [φS, map_pow, map_natCast] using this
        rw [msub, Matrix.map_mul, map_smul_one, sub_eq_zero, RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_map,
          Function.comp_apply, map_pow, map_natCast] at this
        rw [this, map_pow, map_natCast]
      refine (map_mk_eq_zero (I₁ n) _).1 ?_
      show (Mx - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)).map q = 0
      rw [msub, map_smul_one, Matrix.map_mul, Matrix.map_mul, hq1, hq2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
      rw [hq3, smul_smul, sub_eq_zero]
      congr 1
      simp only [← map_mul, ← pow_add]
      ring_nf
    · intro g
      refine (map_mk_eq_zero (J n) _).1 ?_
      let p := Ideal.Quotient.mk (J n)
      show (Φ g Mx).map p = 0
      have hp1 : ((F₀.ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * (((R.map bk.ev).map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p =
          ((R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * (((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p := by
        have h : (((F₀.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * (F m).ε g)).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p = 0 := by
          ext i j
          simp only [Matrix.map_apply, Matrix.zero_apply]
          refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 ?_))
          simpa [map_pow, map_natCast] using map_dvd (WittVector.frobenius : Ainf l →+* Ainf l) (hrel g i j)
        simpa only [msub, Matrix.map_mul, sub_eq_zero] using h
      have hp2 : (((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * ((β'.map bk.ev).map (Per.σA (g : GQ l))).map p = (β'.map bk.ev).map p := by
        have h : ((((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l) * (β'.map bk.ev).map (Per.σA (g : GQ l)) - β'.map bk.ev)).map p = 0 := by
          ext i j
          simp only [Matrix.map_apply, Matrix.zero_apply]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (hβ'.2 g i j)))
        simpa only [msub, Matrix.map_mul, sub_eq_zero] using h
      have hp3 : ((γ.map bk.ev).map (Per.σA (g : GQ l))).map p = (γ.map bk.ev).map p := by
        ext i j
        simp only [Matrix.map_apply, Matrix.of_apply, γ]
        exact Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (hγ2 _ g)))
      have hRev : (R.map φS).map bk.ev = (R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l) := by
        exact Matrix.ext fun i j => bk.ev_frob _
      have hRσ : ((R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l)).map (Per.σA (g : GQ l)) = ((R.map bk.ev).map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l) := by
        exact Matrix.ext fun i j => σA_frob _ _
      simp only [Φ, Mx, msub, Matrix.map_mul]
      rw [hRev, hRσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hp1, Matrix.mul_assoc _ ((((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p), hp2, hp3, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.T.breuilKisin_quotient_eisenstein_compactness l K bk (Fin d × Fin d) (M + 1) Q hmono hpert hex
  refine ⟨c + k₀ + r, Xm x, fun i j => ?_, fun g i j => ?_⟩
  · have h4 := htf1.2.2.2 (bk.ev ((Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j))
      (fun n => exists_of_mem_sup (ev_mem bk n 1 _ ((hx n).1 i j)))
    simpa using htf1.2.1 _ h4
  · have h4 := htfM.2.2.2 (Φ g (Xm x) i j) (fun n => exists_of_mem_sup ((hx n).2 g i j))
    exact (pow_dvd_pow _ (Nat.le_succ M)).trans h4
