import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValOUnramifiedDegreeOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixBasisLatticeUpToDenominatorNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulMemSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnimodularLatticeLocalMatch
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnimodularLatticeLocalConjSymm

noncomputable section

namespace GlobalTheory.LvT.Pts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix GlobalTheory.Mem.Col2 GlobalTheory.LvT.Inh
open Formalism.HermitianLatticesTheory (localization₂ gmap IsUnimodular dual)

section Loc

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff (P : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt P a ↔ a ∈ valO P := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      refine le_antisymm (P.valuation_le_one s) (not_lt.1 fun hl => hs ((P.valuation_lt_one_iff_mem s).1 hl))
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [mem_valO, h2]
    exact P.valuation_le_one r
  · intro ha
    obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer a ha
    exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

def resP (P : HeightOneSpectrum (𝓞 E)) : valO P →+* Res P where
  toFun a := redP P a
  map_one' := by
    have := reduction_coe P 1
    rw [map_one, map_one] at this
    exact this
  map_mul' a b := reduction_mul ((intAt_iff P _).2 a.2) ((intAt_iff P _).2 b.2)
  map_zero' := by
    have := reduction_coe P 0
    rw [map_zero, map_zero] at this
    exact this
  map_add' a b := reduction_add ((intAt_iff P _).2 a.2) ((intAt_iff P _).2 b.2)

def toO (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) : valO P := ⟨algebraMap (𝓞 E) E r, (intAt_iff P _).1 (IntAt.coe P r)⟩

theorem resP_toO (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) : resP P (toO P r) = Ideal.Quotient.mk P.asIdeal r := reduction_coe P r

structure Unif (T : ℕ) (P : HeightOneSpectrum (𝓞 E)) : Prop where
  mem : (T : 𝓞 E) ∈ P.asIdeal
  nsq : (T : 𝓞 E) ∉ P.asIdeal ^ 2

theorem Unif.ne_zero {T : ℕ} {P : HeightOneSpectrum (𝓞 E)} (h : Unif T P) : (T : E) ≠ 0 := by
  intro h0
  have : T = 0 := by exact_mod_cast h0
  subst this
  exact h.nsq (by simp)

theorem Unif.sep {T : ℕ} {P : HeightOneSpectrum (𝓞 E)} (h : Unif T P) (x : E) (hx : x ≠ 0) :
    ∃ (n : ℤ) (y : E), y ∈ valO P ∧ y⁻¹ ∈ valO P ∧ x = (T : E) ^ n * y := by
  have hv : P.valuation E (T : E) = WithZero.exp (-1 : ℤ) := by
    have := LocUnr.valuation_eq_exp_neg_one P T h.mem h.nsq
    rwa [map_natCast] at this
  have hx' : P.valuation E x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy : P.valuation E ((T : E) ^ (WithZero.log (P.valuation E x)) * x) = 1 := by
    rw [map_mul, map_zpow₀, hv, ← WithZero.exp_zsmul]
    conv_lhs => rw [← WithZero.exp_log hx']
    rw [WithZero.log_exp, ← WithZero.exp_add]
    simp
  refine ⟨-WithZero.log (P.valuation E x), (T : E) ^ (WithZero.log (P.valuation E x)) * x, hy.le, ?_, ?_⟩
  · rw [mem_valO, map_inv₀, hy, inv_one]
  · rw [← mul_assoc, ← zpow_add₀ h.ne_zero, neg_add_cancel, zpow_zero, one_mul]

theorem Unif.res_ker {T : ℕ} {P : HeightOneSpectrum (𝓞 E)} (h : Unif T P) (x : valO P) :
    resP P x = 0 ↔ ∃ y : valO P, (x : E) = (T : E) * y := by
  constructor
  · intro h0
    obtain ⟨r, s, hs, e⟩ := (intAt_iff P _).2 x.2
    have h1 := reduction_spec P hs e
    rw [show redP P x = 0 from h0, mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at h1
    obtain ⟨s0, hs0, hh⟩ := LevLaws.exists_mul_mem_span P h.mem h.nsq
    obtain ⟨t, ht⟩ := hh r h1
    refine ⟨⟨x / T, (intAt_iff P _).1 ⟨t, s0 * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs0 hs, ?_⟩⟩,
      (mul_div_cancel₀ _ h.ne_zero).symm⟩
    have h2 := congrArg (algebraMap (𝓞 E) E) ht
    rw [map_mul, map_mul, map_natCast, ← e] at h2
    rw [map_mul, ← mul_div_assoc, mul_assoc, h2, mul_div_cancel_left₀ _ h.ne_zero]
  · rintro ⟨y, hy⟩
    have : x = toO P T * y := Subtype.ext (by rw [hy]; simp [toO])
    rw [this, map_mul, resP_toO, Ideal.Quotient.eq_zero_iff_mem.2 h.mem, zero_mul]

@[reducible] def locF {T : ℕ} {P : HeightOneSpectrum (𝓞 E)} (h : Unif T P) : LocF T (Res P) where
  K := E
  O := valO P
  frac x := (P.valuation E).valuationSubring.mem_or_inv_mem x
  q_ne := h.ne_zero
  sep := h.sep
  res := resP P
  res_surj c := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨toO P r, resP_toO P r⟩
  res_ker := h.res_ker

variable {n : ℕ}

theorem memLoc (P : HeightOneSpectrum (𝓞 E)) (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) :
    x ∈ localization₂ P.asIdeal L ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ L :=
  ⟨fun ⟨s, hs, hx⟩ => ⟨s, hs, hx⟩, fun ⟨s, hs, hx⟩ => ⟨s, hs, hx⟩⟩

theorem mul_notMem {P : HeightOneSpectrum (𝓞 E)} {s t : 𝓞 E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) :
    s * t ∉ P.asIdeal := fun hm => (P.isPrime.mem_or_mem hm).elim hs ht

theorem smul_eq_of {P : HeightOneSpectrum (𝓞 E)} (a : valO P) {r s : 𝓞 E}
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) (x : Fin n → E) : s • a • x = r • x := by
  rw [← algebraMap_smul E s, ← algebraMap_smul E r, ← h, mul_smul]
  rfl

def locO (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Fin n → E)) : Submodule (valO P) (Fin n → E) where
  carrier := localization₂ P.asIdeal M
  add_mem' := (localization₂ P.asIdeal M).add_mem
  zero_mem' := (localization₂ P.asIdeal M).zero_mem
  smul_mem' a x hx := by
    obtain ⟨r, s, hs, h⟩ := (intAt_iff P _).2 a.2
    obtain ⟨t, ht, hx⟩ := (memLoc P M x).1 hx
    refine (memLoc P M _).2 ⟨t * s, mul_notMem ht hs, ?_⟩
    rw [mul_smul, smul_eq_of a h, smul_comm]
    exact M.smul_mem r hx

theorem mem_std {T : ℕ} {P : HeightOneSpectrum (𝓞 E)} (h : Unif T P) (x : Fin n → E) :
    x ∈ (locF h).std n ↔ ∀ i, IntAt P (x i) :=
  (LevModel.mem_std (Lc := locF h) x).trans (forall_congr' fun i => (intAt_iff P (x i)).symm)

theorem exists_frame {T : ℕ} {P : HeightOneSpectrum (𝓞 E)} (h : Unif T P) {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : Submodule.IsLattice E M) : ∃ g, (locF h).IsFrame n g (locO P M) := by
  obtain ⟨g, hg, t, ht, h1, h2⟩ :=
    GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem E (Fin n) M P hM.fg hM.span_eq_top
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hg.ne_zero, fun x => ?_⟩
  rw [mem_std]
  show g *ᵥ x ∈ localization₂ P.asIdeal M ↔ _
  constructor
  · intro hx i
    obtain ⟨s, hs, hx⟩ := (memLoc P M _).1 hx
    obtain ⟨r, hr⟩ := h1 _ hx i
    refine ⟨r, t * s, mul_notMem ht hs, ?_⟩
    rw [hr, ← algebraMap_smul E s, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hg, Matrix.one_mulVec,
      map_mul, mul_assoc]
    rfl
  · intro hx
    have e : g *ᵥ x = ∑ j, x j • fun i => g i j := by
      funext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [e]
    refine (locO P M).sum_mem fun j _ => ?_
    exact (locO P M).smul_mem ⟨x j, (intAt_iff P _).1 (hx j)⟩
      ((memLoc P M _).2 ⟨t, ht, by rw [← algebraMap_smul E t]; exact h2 j⟩)

theorem exists_lattice [StarRing E] {T : ℕ} {P : HeightOneSpectrum (𝓞 E)} (h : Unif T P) (p : LocF.PP (locF h) n) :
    ∃ M : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E M ∧ ∀ x, x ∈ localization₂ P.asIdeal M ↔ x ∈ p.1.L := by
  obtain ⟨g, hg⟩ := p.2.lat
  let e : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E) (Matrix.GeneralLinearGroup.toLin g)
  have he : ∀ x, e x = (g : Matrix (Fin n) (Fin n) E) *ᵥ x := fun x => rfl
  refine ⟨gmap e (stdLat E n), gmap_lattice e _ stdLat_lattice, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [mem_localization_gmap, e.symm_apply_apply, mem_localization_standardLattice, he]
  exact ((hg y).trans (mem_std h y)).symm

theorem f_osmul {P : HeightOneSpectrum (𝓞 E)} {M : Submodule (𝓞 E) (Fin n → E)} {f : (Fin n → E) → Res P}
    (hs : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal M, f (a • x) = Ideal.Quotient.mk P.asIdeal a * f x)
    (a : valO P) {x : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) : f (a • x) = resP P a * f x := by
  obtain ⟨r, s, hs', h⟩ := (intAt_iff P _).2 a.2
  apply mul_left_cancel₀ (mk_ne_zero hs')
  rw [← hs s _ ((locO P M).smul_mem a hx), smul_eq_of a h, hs r x hx, ← mul_assoc]
  congr 1
  exact (reduction_spec P hs' h).symm

theorem toO_smul (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) (x : Fin n → E) : toO P r • x = r • x :=
  algebraMap_smul E r x

open Classical in

def redL (M : Submodule (𝓞 E) (Fin n → E)) (P : HeightOneSpectrum (𝓞 E)) (x : Fin n → E) : TDat.Red M P :=
  if h : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ M then
    (Ideal.Quotient.mk P.asIdeal h.choose : Res P)⁻¹ • Submodule.Quotient.mk (⟨_, h.choose_spec.2⟩ : M) else 0

variable {M : Submodule (𝓞 E) (Fin n → E)} {P : HeightOneSpectrum (𝓞 E)}

theorem mk_smul_mk (s : 𝓞 E) (z : M) :
    (Ideal.Quotient.mk P.asIdeal s : Res P) • (Submodule.Quotient.mk z : TDat.Red M P) = Submodule.Quotient.mk (s • z) := rfl

theorem redL_spec {x : Fin n → E} {s : 𝓞 E} (hs : s ∉ P.asIdeal) (hx : s • x ∈ M) :
    (Ideal.Quotient.mk P.asIdeal s : Res P) • redL M P x = Submodule.Quotient.mk (⟨_, hx⟩ : M) := by
  have h : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ M := ⟨s, hs, hx⟩
  unfold redL
  rw [dif_pos h]
  have ht : (Ideal.Quotient.mk P.asIdeal h.choose : Res P) ≠ 0 := mk_ne_zero h.choose_spec.1
  rw [smul_comm, inv_smul_eq_iff₀ ht, mk_smul_mk, mk_smul_mk]
  congr 1
  exact Subtype.ext (smul_comm _ _ _)

theorem redL_eq {x : Fin n → E} {s : 𝓞 E} (hs : s ∉ P.asIdeal) (hx : s • x ∈ M) {y : TDat.Red M P}
    (h : (Ideal.Quotient.mk P.asIdeal s : Res P) • y = Submodule.Quotient.mk (⟨_, hx⟩ : M)) : redL M P x = y :=
  smul_right_injective _ (show (Ideal.Quotient.mk P.asIdeal s : Res P) ≠ 0 from mk_ne_zero hs)
    ((redL_spec hs hx).trans h.symm)

theorem redL_coe (z : M) : redL M P z = Submodule.Quotient.mk z :=
  redL_eq (one_notMem P) (by rw [one_smul]; exact z.2) (by rw [mk_smul_mk]; rfl)

theorem redL_add {x y : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) (hy : y ∈ localization₂ P.asIdeal M) :
    redL M P (x + y) = redL M P x + redL M P y := by
  obtain ⟨s, hs, hx⟩ := (memLoc P M _).1 hx
  obtain ⟨t, ht, hy⟩ := (memLoc P M _).1 hy
  have h1 : (s * t) • x ∈ M := by rw [mul_comm, mul_smul]; exact M.smul_mem _ hx
  have h2 : (s * t) • y ∈ M := by rw [mul_smul]; exact M.smul_mem _ hy
  refine redL_eq (mul_notMem hs ht) (by rw [smul_add]; exact M.add_mem h1 h2) ?_
  rw [smul_add, redL_spec (mul_notMem hs ht) h1, redL_spec (mul_notMem hs ht) h2, ← Submodule.Quotient.mk_add]
  congr 1
  exact Subtype.ext (smul_add _ _ _).symm

theorem redL_smul (a : valO P) {x : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) :
    redL M P (a • x) = resP P a • redL M P x := by
  refine (show ∀ (r : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal M,
    redL M P (r • x) = (Ideal.Quotient.mk P.asIdeal r : Res P) • redL M P x from ?_) |> fun H => ?_
  · obtain ⟨r, s, hs', h⟩ := (intAt_iff P _).2 a.2
    apply smul_right_injective _ (show (Ideal.Quotient.mk P.asIdeal s : Res P) ≠ 0 from mk_ne_zero hs')
    show (Ideal.Quotient.mk P.asIdeal s : Res P) • _ = (Ideal.Quotient.mk P.asIdeal s : Res P) • _
    rw [← H s _ ((locO P M).smul_mem a hx), smul_eq_of a h, H r x hx, smul_smul]
    congr 1
    exact (reduction_spec P hs' h).symm
  · intro r x hx
    obtain ⟨s, hs, hx⟩ := (memLoc P M _).1 hx
    refine redL_eq hs (by rw [smul_comm]; exact M.smul_mem _ hx) ?_
    rw [smul_comm, redL_spec hs hx, mk_smul_mk]
    congr 1
    exact Subtype.ext (smul_comm _ _ _)

theorem redL_surj (y : TDat.Red M P) : ∃ x ∈ M, redL M P x = y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨z, z.2, redL_coe z⟩

theorem inv_smul_mem_of_redL {T : ℕ} (h : Unif T P) {x : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) (h0 : redL M P x = 0) :
    (T : E)⁻¹ • x ∈ localization₂ P.asIdeal M := by
  obtain ⟨s, hs, hx⟩ := (memLoc P M _).1 hx
  have h1 := redL_spec hs hx
  rw [h0, smul_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
  have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at h2
  obtain ⟨s0, hs0, hh⟩ := LevLaws.exists_mul_mem_span P h.mem h.nsq
  have key : ∀ y ∈ P.asIdeal • M, s0 • (T : E)⁻¹ • y ∈ M := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun r hr z hz => ?_) (fun y z hy hz => ?_)
    · obtain ⟨t, ht⟩ := hh r hr
      rw [smul_comm, smul_smul s0, ht, mul_smul, ← algebraMap_smul E (T : 𝓞 E), map_natCast, inv_smul_smul₀ h.ne_zero]
      exact M.smul_mem _ hz
    · rw [smul_add, smul_add]; exact M.add_mem hy hz
  refine (memLoc P M _).2 ⟨s0 * s, mul_notMem hs0 hs, ?_⟩
  rw [mul_smul, smul_comm s]
  exact key _ h2

theorem dual_redL {f : (Fin n → E) → Res P}
    (hs : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal M, f (a • x) = Ideal.Quotient.mk P.asIdeal a * f x)
    (φ : Module.Dual (Res P) (TDat.Red M P)) (hφ : ∀ z : M, φ (Submodule.Quotient.mk z) = f z)
    {x : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) : φ (redL M P x) = f x := by
  obtain ⟨s, hs', hx'⟩ := (memLoc P M _).1 hx
  apply mul_left_cancel₀ (mk_ne_zero hs')
  rw [← hs s x hx, ← hφ ⟨_, hx'⟩, ← redL_spec hs' hx', map_smul]
  rfl

theorem extF_of_mem (g : Module.Dual (Res P) (TDat.Red M P)) {x : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) :
    TDat.extF M P g x = g (redL M P x) := by
  obtain ⟨s, hs, hx'⟩ := (memLoc P M _).1 hx
  have h : ∃ a : Res P, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ z : M, (z : Fin n → E) = s • x ∧
      g (Submodule.Quotient.mk z) = Ideal.Quotient.mk P.asIdeal s * a :=
    ⟨g (redL M P x), s, hs, ⟨_, hx'⟩, rfl, by rw [← redL_spec hs hx', map_smul]; rfl⟩
  unfold TDat.extF
  rw [dif_pos h]
  obtain ⟨t, ht, ⟨z, hz⟩, e, h2⟩ := h.choose_spec
  obtain rfl : z = t • x := e
  apply mul_left_cancel₀ (mk_ne_zero ht)
  rw [← h2, ← redL_spec ht hz, map_smul]
  rfl

theorem extF_of_notMem (g : Module.Dual (Res P) (TDat.Red M P)) {x : Fin n → E} (hx : x ∉ localization₂ P.asIdeal M) :
    TDat.extF M P g x = 0 := by
  unfold TDat.extF
  rw [dif_neg]
  rintro ⟨_, s, hs, z, e, -⟩
  exact hx ((memLoc P M _).2 ⟨s, hs, e ▸ z.2⟩)

end Loc

section PP

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

theorem mem_of_f_ne (p : LocF.PP Lc n) {x : Fin n → Lc.K} (h : p.1.f x ≠ 0) : x ∈ p.1.L := by
  by_contra hx
  exact h (p.2.off x hx)

theorem pp_ext {p p' : LocF.PP Lc n} (hL : ∀ x, x ∈ p.1.L ↔ x ∈ p'.1.L) (hf : ∀ x ∈ p.1.L, p.1.f x = p'.1.f x) : p = p' := by
  refine Subtype.ext (LocF.Raw.ext (Submodule.ext hL) (funext fun x => ?_))
  by_cases hx : x ∈ p.1.L
  · exact hf x hx
  · rw [p.2.off x hx, p'.2.off x fun h => hx ((hL x).2 h)]

theorem le_of_ker {p p' : LocF.PP Lc n} (hk : p.ker = p'.ker) {e : Fin n → Lc.K} (h : p.1.f e = 1) (h' : p'.1.f e = 1)
    {x : Fin n → Lc.K} (hx : x ∈ p.1.L) : x ∈ p'.1.L ∧ p.1.f x = p'.1.f x := by
  have he := mem_of_f_ne p (h ▸ one_ne_zero)
  have he' := mem_of_f_ne p' (h' ▸ one_ne_zero)
  obtain ⟨a, ha⟩ := Lc.res_surj (p.1.f x)
  have h1 : x + (-a) • e ∈ p.ker := ⟨p.1.L.add_mem hx (p.1.L.smul_mem _ he), by
    rw [p.2.add _ hx _ (p.1.L.smul_mem _ he), p.2.smul _ _ he, h, map_neg, ha]; ring⟩
  rw [hk] at h1
  have e1 : x = (x + (-a) • e) + a • e := by rw [neg_smul]; abel
  refine ⟨e1 ▸ p'.1.L.add_mem h1.1 (p'.1.L.smul_mem _ he'), ?_⟩
  conv_rhs => rw [e1, p'.2.add _ h1.1 _ (p'.1.L.smul_mem _ he'), h1.2, p'.2.smul _ _ he', h', ha]
  ring

theorem eq_of_ker {p p' : LocF.PP Lc n} (hk : p.ker = p'.ker) {e : Fin n → Lc.K} (h : p.1.f e = 1) (h' : p'.1.f e = 1) :
    p = p' :=
  pp_ext (fun _ => ⟨fun hx => (le_of_ker hk h h' hx).1, fun hx => (le_of_ker hk.symm h' h hx).1⟩)
    fun _ hx => (le_of_ker hk h h' hx).2

end PP

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {T : ℕ}

structure TAt (T : ℕ) (ST : Finset (HeightOneSpectrum (𝓞 E))) : Prop where
  unif : ∀ P : ST, Unif T P.1
  st : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1

theorem TAt.ne (h : TAt T ST) (P : ST) : conjPrime₂ P.1 ≠ P.1 := (h.st P P).symm

theorem TAt.move (h : TAt T ST) (P : ST) : MoveHyp ST ∅ P :=
  ⟨h.ne P, h.st P, fun w => absurd w.2 (Finset.notMem_empty _)⟩

variable (ST) in

def OffT (w : HeightOneSpectrum (𝓞 E)) : Prop := ∀ P : ST, w ≠ P.1 ∧ w ≠ conjPrime₂ P.1

variable (ST) in

def AgreeOff (N N' : Submodule (𝓞 E) (Sp E n)) : Prop := ∀ w, OffT ST w → localization₂ w.asIdeal N = localization₂ w.asIdeal N'

def pair {P : ST} (h : Unif T P.1) (d : Deco E n ST SG) (hd : d.Ok) : LocF.PP (locF h) n :=
  ⟨⟨locO P.1 d.N, d.f P⟩, exists_frame h hd.lat, hd.f_add P, fun a _ hx => f_osmul (hd.f_smul P) a hx, hd.f_off P,
    (hd.f_ne P).imp fun _ hx => hx.2⟩

theorem mem_pair_L {P : ST} (h : Unif T P.1) (d : Deco E n ST SG) (hd : d.Ok) (x : Sp E n) :
    x ∈ (pair h d hd).1.L ↔ x ∈ localization₂ P.1.asIdeal d.N := Iff.rfl

theorem pair_f {P : ST} (h : Unif T P.1) (d : Deco E n ST SG) (hd : d.Ok) : (pair h d hd).1.f = d.f P := rfl

theorem mem_pair_ker {P : ST} (h : Unif T P.1) (hne : conjPrime₂ P.1 ≠ P.1) {d : Deco E n ST SG} (hd : d.Ok) (x : Sp E n) :
    x ∈ (pair h d hd).ker ↔ x ∈ localization₂ P.1.asIdeal (d.dnN P) := by
  rw [(hd.dnN_spec P hne).2.2.2]
  show x ∈ localization₂ P.1.asIdeal d.N ∧ d.f P x = 0 ↔ _
  constructor
  · rintro ⟨hx, h0⟩
    obtain ⟨s, hs, hx'⟩ := (memLoc _ _ _).1 hx
    exact (memLoc _ _ _).2 ⟨s, hs, (hd.mem_kerAt P _).2 ⟨hx', by rw [hd.f_smul P s x hx, h0, mul_zero]⟩⟩
  · intro hx
    obtain ⟨s, hs, hx'⟩ := (memLoc _ _ _).1 hx
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P _).1 hx'
    have hx : x ∈ localization₂ P.1.asIdeal d.N := (memLoc _ _ _).2 ⟨s, hs, h1⟩
    rw [hd.f_smul P s x hx] at h2
    exact ⟨hx, (mul_eq_zero.1 h2).resolve_left (mk_ne_zero hs)⟩

theorem pair_congr {SG' : Finset (HeightOneSpectrum (𝓞 E))} {P : ST} (h : Unif T P.1) {d : Deco E n ST SG} {d' : Deco E n ST SG'}
    (hd : d.Ok) (hd' : d'.Ok) (hN : localization₂ P.1.asIdeal d.N = localization₂ P.1.asIdeal d'.N) (hf : d.f P = d'.f P) :
    pair h d hd = pair h d' hd' :=
  pp_ext (fun x => by rw [mem_pair_L, mem_pair_L, hN]) fun x _ => congrFun hf x

theorem pair_up (h : TAt T ST) {d : Deco E n ST ∅} (hd : d.Ok) (P : ST) {x x' : Sp E n} (hx' : x' ∈ d.N)
    (hf : d.f P x' = 1) (hr : redL d.N P.1 x' = redL d.N P.1 x) {p₁ : LocF.PP (locF (h.unif P)) n}
    (hp : (pair (h.unif P) d hd).IsUp x p₁) (hu : (d.up P (T : 𝓞 E) x').Ok) : pair (h.unif P) _ hu = p₁ := by
  obtain ⟨hx, hk, h1⟩ := hp
  have hx'' : x' ∈ localization₂ P.1.asIdeal d.N := le_locP _ _ hx'
  refine eq_of_ker (e := (T : E)⁻¹ • x') ?_ ?_ ?_
  · rw [hk]
    ext y
    rw [mem_pair_ker _ (h.ne P), hd.dnN_up P (h.move P) (h.unif P).mem (h.unif P).nsq hx' hf]
    rfl
  · have := hd.up_f_inv P (h.move P) (h.unif P).mem (h.unif P).nsq hx' hf
    rw [map_natCast] at this
    exact this
  · have hneg : (-1 : valO P.1) • x ∈ localization₂ P.1.asIdeal d.N := (locO P.1 d.N).smul_mem _ hx
    have h0 : redL d.N P.1 (x' + (-1 : valO P.1) • x) = 0 := by
      rw [redL_add hx'' hneg, redL_smul _ hx, hr, map_neg, map_one, neg_one_smul, add_neg_cancel]
    have h2 : (T : E)⁻¹ • (x' + (-1 : valO P.1) • x) ∈ p₁.ker := by
      rw [hk]
      exact inv_smul_mem_of_redL (h.unif P) ((localization₂ _ _).add_mem hx'' hneg) h0
    have e : (T : E)⁻¹ • x' = (T : E)⁻¹ • (x' + (-1 : valO P.1) • x) + (T : E)⁻¹ • x := by
      rw [neg_one_smul, ← smul_add]; congr 1; abel
    rw [e, p₁.2.add _ h2.1 _ (mem_of_f_ne p₁ (h1 ▸ one_ne_zero)), h2.2, zero_add]
    exact h1

theorem pair_up_ne (h : TAt T ST) {d : Deco E n ST ∅} (hd : d.Ok) {P Q : ST} (hQ : Q ≠ P) {x' : Sp E n} (hx' : x' ∈ d.N)
    (hu : (d.up P (T : 𝓞 E) x').Ok) : pair (h.unif Q) _ hu = pair (h.unif Q) d hd :=
  pair_congr _ hu hd (((upN_spec hd.lat hd.uni P.1 (h.ne P) hx').2.2.1 Q.1 (fun e => hQ (Subtype.ext e)) (h.st P Q)).localization_eq)
    (d.up_f_ne P _ x' hQ)

theorem dn_ok (h : TAt T ST) {d : Deco E n ST ∅} (hd : d.Ok) (P : ST) (p₀ : LocF.PP (locF (h.unif P)) n)
    (hp : (p₀.1.L : Set (Sp E n)) = (pair (h.unif P) d hd).ker) : (d.dn P p₀.1.f).Ok := by
  have hL : ∀ x, x ∈ localization₂ P.1.asIdeal (d.dnN P) ↔ x ∈ p₀.1.L := fun x => by
    rw [← mem_pair_ker (h.unif P) (h.ne P) hd, ← hp]; rfl
  have hs : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.1.asIdeal (d.dnN P),
      p₀.1.f (a • x) = Ideal.Quotient.mk P.1.asIdeal a * p₀.1.f x := fun a x hx => by
    rw [← toO_smul P.1, ← resP_toO]
    exact p₀.2.smul _ _ ((hL x).1 hx)
  refine hd.dn P (h.move P) (fun x hx y hy => p₀.2.add x ((hL x).1 hx) y ((hL y).1 hy)) hs
    (fun x hx => p₀.2.off x fun h' => hx ((hL x).2 h')) ?_
  obtain ⟨x, hx⟩ := p₀.2.ne
  have hx' := (hL x).2 (mem_of_f_ne p₀ hx)
  obtain ⟨s, hs', hx''⟩ := (memLoc _ _ _).1 hx'
  exact ⟨_, hx'', by rw [hs s x hx']; exact mul_ne_zero (mk_ne_zero hs') hx⟩

theorem pair_dn (h : TAt T ST) {d : Deco E n ST ∅} (hd : d.Ok) (P : ST) (p₀ : LocF.PP (locF (h.unif P)) n)
    (hp : (p₀.1.L : Set (Sp E n)) = (pair (h.unif P) d hd).ker) (hu : (d.dn P p₀.1.f).Ok) :
    pair (h.unif P) _ hu = p₀ := by
  refine pp_ext (fun x => ?_) fun x _ => ?_
  · rw [mem_pair_L]
    show x ∈ localization₂ P.1.asIdeal (d.dnN P) ↔ _
    rw [← mem_pair_ker (h.unif P) (h.ne P) hd, ← hp]; rfl
  · rw [pair_f]; simp [Deco.dn]

theorem pair_dn_ne (h : TAt T ST) {d : Deco E n ST ∅} (hd : d.Ok) {P Q : ST} (hQ : Q ≠ P) {g : Sp E n → Res P.1}
    (hu : (d.dn P g).Ok) : pair (h.unif Q) _ hu = pair (h.unif Q) d hd :=
  pair_congr _ hu hd (((hd.dnN_spec P (h.ne P)).2.2.1 Q.1 (fun e => hQ (Subtype.ext e)) (h.st P Q)).localization_eq)
    (by classical exact Function.update_of_ne hQ _ _)

theorem deco_ext (h : TAt T ST) {d d' : Deco E n ST ∅} (hd : d.Ok) (hd' : d'.Ok) (ho : AgreeOff ST d.N d'.N)
    (hp : ∀ P, pair (h.unif P) d hd = pair (h.unif P) d' hd') : d = d' := by
  have hP : ∀ P : ST, localization₂ P.1.asIdeal d.N = localization₂ P.1.asIdeal d'.N := fun P => by
    ext x
    rw [← mem_pair_L (h.unif P) d hd, hp P, mem_pair_L]
  refine Deco.ext ?_ (funext fun P => congrArg (fun p => p.1.f) (hp P))
    (funext fun w => absurd w.2 (Finset.notMem_empty _))
  refine (GlobalTheory.GO.UniExt.unimodular_ext E n _ _ hd.lat hd.uni hd'.lat hd'.uni).2 fun w => ?_
  by_cases hw : OffT ST w
  · exact Or.inl (ho w hw)
  · obtain ⟨P, hP'⟩ := not_forall.1 hw
    by_cases h1 : w = P.1
    · subst h1; exact Or.inl (hP P)
    · have h2 : w = conjPrime₂ P.1 := by
        by_contra h2; exact hP' ⟨h1, h2⟩
      subst h2
      have h3 : ∀ Q : HeightOneSpectrum (𝓞 E), Q = P.1 → localization₂ Q.asIdeal d.N = localization₂ Q.asIdeal d'.N := by
        rintro _ rfl; exact hP P
      exact Or.inr (h3 _ (GlobalTheory.GO.UniExt.conjP_involutive P.1))

theorem exists_deco (h : TAt T ST) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hu : IsUnimodular (hStd E n) N) (p : ∀ P : ST, LocF.PP (locF (h.unif P)) n) :
    ∃ (e : Deco E n ST ∅) (he : e.Ok), AgreeOff ST N e.N ∧ ∀ P, pair (h.unif P) e he = p P := by
  classical
  have key : ∀ s : Finset ST, ∃ N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N' ∧ IsUnimodular (hStd E n) N' ∧
      AgreeOff ST N N' ∧ ∀ P ∈ s, ∀ x, x ∈ localization₂ P.1.asIdeal N' ↔ x ∈ (p P).1.L := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨N, hN, hu, fun _ _ => rfl, fun P hP => absurd hP (Finset.notMem_empty _)⟩
    | insert P s _ ih =>
      obtain ⟨N₁, a1, a2, a3, a4⟩ := ih
      obtain ⟨M, hM, hMp⟩ := exists_lattice (h.unif P) (p P)
      obtain ⟨N₂, b1, b2, b3, b4⟩ := GlobalTheory.GO.SplitGlue.exists_selfDual_prescribed E n N₁ M P.1 (h.ne P) a1 a2 hM
      refine ⟨N₂, b1, b2, fun w hw => (a3 w hw).trans (b4 w (hw P).1 (hw P).2).symm, fun Q hQ x => ?_⟩
      by_cases e : Q = P
      · subst e; rw [b3]; exact hMp x
      · rw [b4 Q.1 (fun e' => e (Subtype.ext e')) (h.st P Q)]
        exact a4 Q ((Finset.mem_insert.1 hQ).resolve_left e) x
  obtain ⟨N', a1, a2, a3, a4⟩ := key Finset.univ
  replace a4 := fun P => a4 P (Finset.mem_univ P)
  have hs : ∀ (P : ST) (a : 𝓞 E), ∀ x ∈ localization₂ P.1.asIdeal N',
      (p P).1.f (a • x) = Ideal.Quotient.mk P.1.asIdeal a * (p P).1.f x := fun P a x hx => by
    rw [← toO_smul P.1, ← resP_toO]
    exact (p P).2.smul _ _ ((a4 P x).1 hx)
  have he : (⟨N', fun P => (p P).1.f, fun w => absurd w.2 (Finset.notMem_empty _)⟩ : Deco E n ST ∅).Ok := by
    refine ⟨a1, a2, fun P x hx y hy => (p P).2.add x ((a4 P x).1 hx) y ((a4 P y).1 hy), hs,
      fun P x hx => (p P).2.off x fun h' => hx ((a4 P x).2 h'), fun P => ?_,
      fun w => absurd w.2 (Finset.notMem_empty _), fun w => absurd w.2 (Finset.notMem_empty _),
      fun w => absurd w.2 (Finset.notMem_empty _), fun w => absurd w.2 (Finset.notMem_empty _),
      fun w => absurd w.2 (Finset.notMem_empty _)⟩
    obtain ⟨x, hx⟩ := (p P).2.ne
    have hx' := (a4 P x).2 (mem_of_f_ne _ hx)
    obtain ⟨s, hs', hx''⟩ := (memLoc _ _ _).1 hx'
    exact ⟨_, hx'', by
      show (p P).1.f (s • x) ≠ 0
      rw [hs P s x hx']; exact mul_ne_zero (mk_ne_zero hs') hx⟩
  exact ⟨_, he, a3, fun P => pp_ext (a4 P) fun _ _ => rfl⟩

omit [StarRing E] in
theorem exists_smul_of_le {w : HeightOneSpectrum (𝓞 E)} {M N : Submodule (𝓞 E) (Sp E n)} (hM : M.FG)
    (h : M ≤ localization₂ w.asIdeal N) : ∃ a ∉ w.asIdeal, ∀ x ∈ M, a • x ∈ N := by
  classical
  obtain ⟨S, rfl⟩ := hM
  have h0 : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ s • y ∈ N := fun y hy =>
    (memLoc _ _ _).1 (h (Submodule.subset_span hy))
  choose! s hs hs' using h0
  refine ⟨∏ y ∈ S, s y, fun hm => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hm
    exact hs y hy h
  · induction hx using Submodule.span_induction with
    | mem y hy => rw [← Finset.prod_erase_mul S s hy, mul_smul]; exact N.smul_mem _ (hs' y hy)
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
    | smul c y _ hy => rw [smul_comm]; exact N.smul_mem _ hy

theorem ok_of_agree {d : Deco E n ST SG} (hd : d.Ok) {e : Deco E n ST ∅} (he : e.Ok)
    (h : ∀ w : SG, localization₂ w.1.asIdeal d.N = localization₂ w.1.asIdeal e.N) : (⟨e.N, e.f, d.be⟩ : Deco E n ST SG).Ok := by
  refine ⟨he.lat, he.uni, he.f_add, he.f_smul, he.f_off, he.f_ne,
    fun w x hx y hy => hd.be_add w x ((h w).ge hx) y ((h w).ge hy), fun w a x hx => hd.be_smul w a x ((h w).ge hx),
    fun w x hx => hd.be_off w x fun h' => hx ((h w).le h'), fun w c => ?_, fun w x hx h0 => ?_⟩
  · obtain ⟨x, hx, hc⟩ := hd.be_surj w c
    obtain ⟨s, hs, hx'⟩ := (memLoc _ _ _).1 ((h w).le (le_locP w.1 _ hx))
    haveI := w.1.isMaximal
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (mk_ne_zero hs)
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨t • s • x, e.N.smul_mem _ hx', ?_⟩
    show d.be w (t • s • x) = c
    rw [smul_smul, hd.be_smul w _ x (le_locP w.1 _ hx), map_mul, mul_comm, hb, one_smul, hc]
  · have hx1 : x ∈ localization₂ w.1.asIdeal d.N := (h w).ge (le_locP w.1 _ hx)
    obtain ⟨s, hs, hx'⟩ := (memLoc _ _ _).1 hx1
    have h1 := hd.be_ker w _ hx' (by rw [hd.be_smul w s x hx1, show d.be w x = 0 from h0, smul_zero])
    obtain ⟨a, ha, hle⟩ := exists_smul_of_le hd.lat.fg ((le_locP w.1 d.N).trans (h w).le)
    refine mem_smul_of_loc (M := e.N) hx (mul_notMem ha hs) ?_
    rw [mul_smul]
    refine Submodule.smul_induction_on h1 (fun r hr z hz => ?_) (fun y z hy hz => ?_)
    · rw [smul_comm]; exact Submodule.smul_mem_smul hr (hle z hz)
    · rw [smul_add]; exact Submodule.add_mem _ hy hz

end Deco

end GlobalTheory.LvT.Pts
