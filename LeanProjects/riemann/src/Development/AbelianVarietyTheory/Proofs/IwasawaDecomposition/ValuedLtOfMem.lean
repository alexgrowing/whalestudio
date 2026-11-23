import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDual
import Formalism.LocalToGlobal.Columns.AdelicLemmas

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.PtExist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "ι" => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)

theorem ad_ext {a b : AfE F E} (h : ∀ P, adAt F P a = adAt F P b) : a = b :=
  (afIso F E).injective (FiniteAdeleRing.ext _ h)

def idem (F : Type) [Field F] [NumberField F] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) : AfE F E :=
  (finAf F E (localIdele E P (atFin P (Units.mk0 2 two_ne_zero))) : AfE F E) - 1

open Classical in

theorem adAt_idem (P w : HeightOneSpectrum (𝓞 E)) : adAt F w (idem F P) = if w = P then 1 else 0 := by
  unfold idem
  rw [map_sub, adAt_finAf, map_one]
  split_ifs with h
  · subst h
    rw [compAt_localIdele_self]
    show algebraMap E (w.adicCompletion E) 2 - 1 = 1
    rw [map_ofNat]
    norm_num
  · rw [compAt_localIdele_ne h, sub_self]

theorem valued_lt_of_mem {P : HeightOneSpectrum (𝓞 E)} {w : Formalism.L2.Herm.intAf F E} (h : w ∈ idS F P.asIdeal) :
    Valued.v (adAt F P (w : AfE F E)) < 1 := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    show Valued.v (adAt F P (ι (algebraMap (𝓞 E) E b))) < 1
    rw [adAt_inclE, valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hb
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add]
    exact Valuation.map_add_lt _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 a.2 P)) hx

theorem hasRes_redA [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {a : AfE F E} (ha : a ∈ RInt F E) :
    HasRes P (adAt F P a) (redA P a) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (redA P a)
  refine ⟨r, hr, ?_⟩
  have h0 : resS F P (⟨a, ha⟩ - oToS F E r) = 0 := by
    rw [map_sub, resS_oToS, ← redA_int, hr, sub_self]
  have h1 := valued_lt_of_mem (Formalism.L2.Col.mem_idS_of_resS h0)
  rw [← adAt_inclE F, ← map_sub]
  exact h1

variable [StarRing E] (hc : CMData F E)

local notation "σ" => Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F)

theorem sig_sig (z : AfE F E) : σ (σ z) = z := DetClass.sigR_sigR (fun x => star_star x) z

open Classical in

theorem adAt_sig_idem (P w : HeightOneSpectrum (𝓞 E)) : adAt F w (σ (idem F P)) = if conjPrime₂ w = P then 1 else 0 := by
  split_ifs with h
  · have e := valued_sigR hc w (idem F P - 1)
    rw [map_sub (adAt F (conjPrime₂ w)), adAt_idem, if_pos h, map_one, sub_self, map_zero, Valuation.zero_iff, map_sub,
      map_sub, map_one, map_one, sub_eq_zero] at e
    exact e
  · have e := valued_sigR hc w (idem F P)
    rwa [adAt_idem, if_neg h, map_zero, Valuation.zero_iff] at e

variable (Q : Finset (HeightOneSpectrum (𝓞 E)))

def glue (z : AfE F E) (a b : HeightOneSpectrum (𝓞 E) → E) : AfE F E :=
  (1 - ∑ P ∈ Q, idem F P - σ (∑ P ∈ Q, idem F P)) * z + ∑ P ∈ Q, idem F P * ι (a P) + σ (∑ P ∈ Q, idem F P * ι (b P))

theorem sig_glue (z : AfE F E) (a b : HeightOneSpectrum (𝓞 E) → E) : σ (glue hc Q z a b) = glue hc Q (σ z) b a := by
  unfold glue
  rw [map_add, map_add, map_mul, map_sub, map_sub, sig_sig, sig_sig, map_one]
  ring

open Classical in

theorem adAt_glue (hQ : ∀ P ∈ Q, conjPrime₂ P ∉ Q) (z : AfE F E) (a b : HeightOneSpectrum (𝓞 E) → E)
    (w : HeightOneSpectrum (𝓞 E)) : adAt F w (glue hc Q z a b) =
      if w ∈ Q then algebraMap E _ (a w) else if conjPrime₂ w ∈ Q then algebraMap E _ (star (b (conjPrime₂ w))) else adAt F w z := by
  unfold glue
  simp only [map_add, map_mul, map_sub, map_sum, map_one, adAt_idem, adAt_sig_idem, sigR_inclE, adAt_inclE, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq]
  by_cases h : w ∈ Q
  · simp [h, hQ w h]
  · by_cases h' : conjPrime₂ w ∈ Q <;> simp [h, h']

theorem unimodGenus (n : ℕ) [NeZero n] : UnimodGenus hc n := by
  intro N hN hU
  have hs : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
  have hfix : ∀ e : E, hc.sig e = e → ∃ a : F, algebraMap F E a = e := fun e he => (hc.fixed e).1 he
  let h : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E := Formalism.UG.CS.formJ (hc.sig : E →+* E) hs 1 1
  obtain ⟨hsym, hap⟩ := Formalism.UG.P.hermitian_form_symmetry_holds E _ hs (Fin n) 1 1 (map_one _) (by
    ext i j
    simp [Formalism.UG.cT, Matrix.one_apply, eq_comm])
  replace hsym : h.IsSymm := hsym
  replace hap : ∀ x y, h x y = Formalism.UG.hform (starRingEnd E) 1 x y := fun x y => (hap x y).trans (one_mul _)
  have he : h = hStd E n := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [hap, Formalism.UG.hform]
    show _ = ∑ i, star (x i) * y i
    simp [Matrix.one_apply, starRingEnd_apply]
  have hr : ∀ y, (∀ x, h x y = 0) → y = 0 := fun y hy => funext fun i => by
    have := hy (Pi.single i 1)
    rwa [he, hStd_single_left] at this
  have hn : h.Nondegenerate := ⟨fun x hx => hr x fun y => by rw [← hsym.eq, hx, map_zero], hr⟩
  exact GlobalTheory.Mass.Genus.exists_globLat_eq (J := 1) hs hfix (Module.Finite.iff_fg.2 stdLat_lattice.fg)
    stdLat_lattice.span_eq_top N (GlobalTheory.SelfDualPoint.mem_genus h hc.cmUnram hsym hn stdLat_lattice hN
      (he ▸ stdLat_unimodular) (he ▸ hU))

variable {hc Q} {n : ℕ}

theorem mem_uad_iff (g : GL (Fin n) (AfE F E)) :
    g ∈ UAd hc n ↔ Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) (AfE F E)) * g = 1 := by
  show Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) (AfE F E)) * (1 : Matrix (Fin n) (Fin n) E).map ι * g =
    (1 : Matrix (Fin n) (Fin n) E).map ι ↔ _
  rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]

theorem inv_apply {g : GL (Fin n) (AfE F E)} (hg : g ∈ UAd hc n) (i j : Fin n) :
    ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j =
      σ ((g : Matrix (Fin n) (Fin n) (AfE F E)) j i) := by
  rw [Units.inv_eq_of_mul_eq_one_left ((mem_uad_iff g).1 hg)]
  rfl

theorem int_of_uni (hQ : ∀ P ∈ Q, conjPrime₂ P ∉ Q) {k : GL (Fin n) (AfE F E)} (hk : k ∈ UAd hc n)
    (h1 : ∀ w, conjPrime₂ w ∉ Q → ∀ i j, Valued.v (adAt F w ((k : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1)
    (h2 : ∀ w, conjPrime₂ w ∉ Q → ∀ i j,
      Valued.v (adAt F w (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1) (i j : Fin n) :
    (k : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := by
  refine (mem_rInt_iff F E _).2 fun w => ?_
  by_cases h : conjPrime₂ w ∈ Q
  · have e := inv_apply (inv_mem hk) i j
    rw [inv_inv] at e
    rw [← adAt_apply, e, valued_sigR]
    exact h2 _ (hQ _ h) j i
  · exact h1 w h i j

def mat (f : Sp E n ≃ₗ[E] Sp E n) : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => f (Pi.single j 1) i

omit [NumberField E] [StarRing E] in

theorem mat_mulVec (f : Sp E n ≃ₗ[E] Sp E n) (v : Sp E n) (i : Fin n) : ∑ j, mat f i j * v j = f v i := by
  conv_rhs => rw [← Finset.univ_sum_single v, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (v j) : Sp E n) = v j • (Pi.single j 1 : Sp E n) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [this, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

omit [NumberField E] [StarRing E] in

theorem mat_symm_mul (f : Sp E n ≃ₗ[E] Sp E n) : mat f.symm * mat f = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  refine (mat_mulVec f.symm (f (Pi.single j 1)) i).trans ?_
  rw [f.symm_apply_apply, Matrix.one_apply, Pi.single_apply]

theorem valued_pullV_le (x : GL (Fin n) (AfE F E)) {P : HeightOneSpectrum (𝓞 E)} {v : Sp E n}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) (i : Fin n) :
    Valued.v (adAt F P (Formalism.L2.Col.pullV x v i)) ≤ 1 := by
  obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hv
  have h1 := (mem_rInt_iff F E _).1 ((mem_globLat x _).1 h i) P
  rwa [← adAt_apply, pullV_osmul, map_mul, map_mul, adAt_inclE, valued_algebraMap, CharValCompare.val_of_notMem hs,
    one_mul] at h1

theorem valued_symm_le {N : Submodule (𝓞 E) (Sp E n)} {P : HeightOneSpectrum (𝓞 E)} {f : Sp E n ≃ₗ[E] Sp E n}
    (hf : CharValCompare.IsFr P N f) {u : Fin n → AfE F E} (hu : u ∈ Formalism.L2.Herm.hatL (F := F) N) (i : Fin n) :
    Valued.v (∑ j, algebraMap E (P.adicCompletion E) (mat f.symm i j) * adAt F P (u j)) ≤ 1 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    simp only [adAt_inclE, ← map_mul, ← map_sum]
    rw [mat_mulVec, valued_algebraMap]
    have h1 : f.symm v ∈ stdAt E n P := (hf _).1 (by rw [f.apply_symm_apply]; exact le_locP P _ hv)
    obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 h1
    obtain ⟨r, hr⟩ := (mem_stdLat _).1 h i
    have h2 : P.valuation E (algebraMap (𝓞 E) E r) ≤ 1 := HeightOneSpectrum.valuation_le_one (K := E) P r
    rwa [hr, Pi.smul_apply, Algebra.smul_def, map_mul, CharValCompare.val_of_notMem hs, one_mul] at h2
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    exact Valuation.map_add_le _ hx hy
  | smul a x _ hx =>
    have e : ∀ j, algebraMap E (P.adicCompletion E) (mat f.symm i j) * adAt F P ((a • x) j) =
        adAt F P a * (algebraMap E (P.adicCompletion E) (mat f.symm i j) * adAt F P (x j)) := fun j => by
      show _ * adAt F P ((a : AfE F E) * x j) = _
      rw [map_mul]
      ring
    simp only [e, ← Finset.mul_sum]
    rw [map_mul]
    exact mul_le_one' ((mem_rInt_iff F E _).1 a.2 P) hx

theorem carries_globLat (x : GL (Fin n) (AfE F E)) :
    Formalism.L2.Herm.Carries x (stdLat E n) (Formalism.UG.CS.globLat x (stdLat E n)) :=
  Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 stdLat_lattice.fg) stdLat_lattice.span_eq_top x

omit [StarRing E] in

theorem mulVec_int {k : Matrix (Fin n) (Fin n) (AfE F E)} (hk : ∀ i j, k i j ∈ RInt F E) {z : Fin n → AfE F E}
    (hz : ∀ i, z i ∈ RInt F E) (i : Fin n) : k.mulVec z i ∈ RInt F E := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hk i j) (hz j)

theorem exists_modify (hQ : ∀ P ∈ Q, conjPrime₂ P ∉ Q) {x : GL (Fin n) (AfE F E)} (hx : x ∈ UAd hc n)
    (fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n)
    (hfr : ∀ P ∈ Q, CharValCompare.IsFr P (Formalism.UG.CS.globLat x (stdLat E n)) (fr P)) :
    ∃ g ∈ UAd hc n, Formalism.L2.Herm.Carries g (stdLat E n) (Formalism.UG.CS.globLat x (stdLat E n)) ∧
      (∀ P ∈ Q, ∀ i j, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (mat (fr P) i j)) ∧
      ∀ w ∉ Q, conjPrime₂ w ∉ Q → ∀ v i, adAt F w (pullV g v i) = adAt F w (Formalism.L2.Col.pullV x v i) := by
  classical
  let G : Matrix (Fin n) (Fin n) (AfE F E) := Matrix.of fun i j =>
    glue hc Q ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j) (fun P => mat (fr P) i j) fun P => mat (fr P).symm j i
  let G' : Matrix (Fin n) (Fin n) (AfE F E) := Matrix.of fun i j =>
    glue hc Q (((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) (fun P => mat (fr P).symm i j)
      fun P => mat (fr P) j i
  have hG : ∀ w i j, adAt F w (G i j) = _ := fun w i j => adAt_glue hc Q hQ _ _ _ w
  have hG' : ∀ w i j, adAt F w (G' i j) = _ := fun w i j => adAt_glue hc Q hQ _ _ _ w
  have hone : ∀ w i j, adAt F w ((1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) i j) := fun w i j => by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : G' * G = 1 := by
    ext i j
    refine ad_ext fun w => ?_
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul, hG, hG']
    split_ifs with h h'
    · simp only [← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, mat_symm_mul, hone]
    · simp only [← map_mul, ← map_sum, ← star_mul, ← star_sum]
      rw [← Matrix.mul_apply, mat_symm_mul, hone, Matrix.one_apply, Matrix.one_apply]
      by_cases e : i = j <;> simp [e, eq_comm]
    · simp only [← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, Units.inv_mul]
  let g : GL (Fin n) (AfE F E) := ⟨G, G', mul_eq_one_comm.1 h1, h1⟩
  have hg : g ∈ UAd hc n := by
    rw [mem_uad_iff, ← h1]
    congr 1
    ext i j
    show σ (G j i) = G' i j
    exact (sig_glue hc Q _ _ _).trans (by rw [← inv_apply hx]; rfl)
  have hk : x⁻¹ * g ∈ UAd hc n := mul_mem (inv_mem hx) hg
  have k1 : ∀ w, conjPrime₂ w ∉ Q → ∀ i j,
      Valued.v (adAt F w (((x⁻¹ * g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
    intro w hw i j
    rw [Units.val_mul, Matrix.mul_apply, map_sum]
    simp only [g, map_mul, hG, if_neg hw]
    split_ifs with h
    · have := valued_pullV_le x ((hfr w h (Pi.single j 1)).2 (le_locP w _ (by simpa using single_mem_stdLat (E := E) j 1))) i
      simp only [Formalism.L2.Col.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE] at this
      exact this
    · simp only [← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, Units.inv_mul, Matrix.one_apply]
      split_ifs <;> simp
  have k2 : ∀ w, conjPrime₂ w ∉ Q → ∀ i j,
      Valued.v (adAt F w ((((x⁻¹ * g)⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
    intro w hw i j
    rw [mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_apply, map_sum]
    simp only [g, Units.inv_mk, map_mul, hG', if_neg hw]
    split_ifs with h
    · refine valued_symm_le (u := fun l => (x : Matrix (Fin n) (Fin n) (AfE F E)) l j) (hfr w h)
        ((carries_globLat x _).2 ((mem_latS_std _).2 fun l => ?_)) i
      simp only [Matrix.mulVec, dotProduct]
      rw [← Matrix.mul_apply, Units.inv_mul, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · simp only [← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, Units.inv_mul, Matrix.one_apply]
      split_ifs <;> simp
  have i1 := int_of_uni hQ hk k1 k2
  have i2 := int_of_uni hQ (inv_mem hk) k2 (by rw [inv_inv]; exact k1)
  refine ⟨g, hg, fun z => (carries_globLat x z).trans ?_, fun P hP i j => ?_, fun w h h' v i => ?_⟩
  · refine (mem_latS_std _).trans (Iff.trans ⟨fun h i => ?_, fun h i => ?_⟩ (mem_latS_std _).symm)
    · have := mulVec_int i2 h i
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_rev, inv_inv, mul_inv_cancel_right] at this
    · have := mulVec_int i1 h i
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right] at this
  · exact (hG P i j).trans (if_pos hP)
  · simp only [pullV, Formalism.L2.Col.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, g, Units.inv_mk, hG', if_neg h,
      if_neg h']

variable (hc) in

theorem exists_isPtOf_cm (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (p : DecoF E n ST SG Q)
    (h1 : Disjoint ST SG) (h2 : Disjoint ST Q) (h3 : Disjoint SG Q)
    (h4 : ∀ P ∈ uSG ST (uSG SG Q), conjPrime₂ P ∉ uSG ST (uSG SG Q)) : ∃ g : GL (Fin n) (AfE F E), IsPtOf hc g p := by
  classical
  simp only [Finset.mem_union, not_or] at h4
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_mem _, fun z => ?_, fun _ _ _ i => i.elim0, fun _ _ _ i => i.elim0, fun _ i => i.elim0⟩
    rw [Subsingleton.elim z 0, Matrix.mulVec_zero]
    exact iff_of_true (zero_mem _) (zero_mem _)
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨q, hq⟩ := decoPtSurj_of hc n ST SG (unimodGenus hc n) reduction_surjective_bis (fun P hP P' hP' hcj => by
    have e : P' = conjPrime₂ P := by
      ext b
      rw [mem_conjP]
      exact (hcj (cO E b) b (star_star _).symm).symm
    simp only [Finset.mem_union] at hP hP'
    have := h4 P (by tauto)
    rw [← e] at this
    tauto) h1 p.deco
  obtain ⟨x, hx, hd⟩ : ∃ x ∈ UAd hc n, decoRaw ST SG x = p.deco.1 := by
    refine ⟨_, (Quotient.out q).2, ?_⟩
    rw [← hq, decoPt, decoOf, dif_pos (decorated_lattice_exists hc n ST SG _ (Quotient.out q).2)]
  have hN : Formalism.UG.CS.globLat x (stdLat E n) = p.deco.1.N := congrArg Deco.N hd
  obtain ⟨g, hg, c1, c2, c3⟩ := exists_modify (fun P hP => (h4 P (Or.inr (Or.inr hP))).2.2) hx (ptFr p)
    fun P _ => hN ▸ isFr_ptFr p P
  refine ⟨g, hg, hN ▸ c1, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    rw [← hN] at hv
    rw [c3 _ (Finset.disjoint_left.1 h2 P.2) (h4 _ (Or.inl P.2)).2.2, ← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat x v).1 hv i)
  · rw [← hN] at hv
    rw [c3 _ (Finset.disjoint_left.1 h3 P.2) (h4 _ (Or.inr (Or.inl P.2))).2.2, ← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat x v).1 hv i)
  · rw [c2 _ P.2, ptFr_of_mem p (Finset.disjoint_right.1 h3 P.2) P.2]
    rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isPtOf : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q), Disjoint ST SG → Disjoint ST Q → Disjoint SG Q → (∀ P ∈ uSG ST (uSG SG Q), conjPrime₂ P ∉ uSG ST (uSG SG Q)) → ∃ g : GL (Fin n) (AfE H.F H.E), IsPtOf (host_cmData R H) g p :=
  fun R H n ST SG Q p => exists_isPtOf_cm (host_cmData R H) n ST SG Q p

end GlobalTheory.Mem.Col2.PtExist
