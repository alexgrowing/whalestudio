import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

noncomputable section

namespace GlobalTheory.LFun.ConjPlace

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

theorem esymm_inv_mul (B : Multiset ℂˣ) {j : ℕ} (hj : j ≤ B.card) :
    ((B.map (·⁻¹)).map fun b : ℂˣ => (b : ℂ)).esymm j * (B.map fun b : ℂˣ => (b : ℂ)).esymm B.card =
      (B.map fun b : ℂˣ => (b : ℂ)).esymm (B.card - j) := by
  obtain ⟨n, α, rfl⟩ : ∃ (n : ℕ) (α : Fin n → ℂˣ), B = Finset.univ.val.map α := by
    induction B using Quotient.inductionOn with
    | h l => exact ⟨l.length, l.get, by simp⟩
  have hn : (Finset.univ.val.map α).card = n := by simp
  rw [hn] at hj ⊢
  simp only [Multiset.map_map, Finset.esymm_map_val, Function.comp_def]
  have h1 : Finset.powersetCard n (Finset.univ : Finset (Fin n)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [h1, Finset.sum_singleton, Finset.sum_mul]
  refine Finset.sum_nbij' compl compl (fun t ht => ?_) (fun t ht => ?_) (by simp) (by simp) fun t _ => ?_
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    simp [Finset.card_compl, ht]
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    rw [Finset.card_compl, ht, Fintype.card_fin]; omega
  · rw [← Finset.prod_mul_prod_compl t, ← mul_assoc, ← Finset.prod_mul_distrib]
    simp

theorem satEig_inv_mul {q n j : ℕ} {B : Multiset ℂˣ} (hB : B.card = n) (hj : j ≤ n) :
    satEig q n (B.map (·⁻¹)) j * satEig q n B n = satEig q n B (n - j) := by
  subst hB
  rw [satEig, satEig, satEig, ← esymm_inv_mul B hj, Nat.cast_sub hj, sub_self, mul_zero, zero_div, Complex.cpow_zero,
    one_mul, mul_assoc, sub_sub_cancel, mul_comm (j : ℂ)]

theorem satEig_zero (q n : ℕ) (B : Multiset ℂˣ) : satEig q n B 0 = 1 := by simp [satEig, Multiset.esymm]

section Shift

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {h : G → ℂ} {x : V}

theorem apply_heckeVec_shift (hh : IsBiInv K h) (hx : x ∈ fixed ρ K) (z : G) :
    ρ z (heckeVec ρ K (fun g => h (z * g)) x) = heckeVec ρ K h x := by
  let e : V ≃+ V :=
    { (ρ z).toAddMonoidHom with
      invFun := ρ z⁻¹
      left_inv := fun y => by simp
      right_inv := fun y => by simp }
  rw [heckeVec_eq_of_section hh hx (fun c => z * (z⁻¹ • c).out) fun c => by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_coe, QuotientGroup.out_eq', smul_inv_smul],
    ← finsum_comp_equiv (MulAction.toPerm z)]
  refine (e.map_finsum _).trans (finsum_congr fun c => ?_)
  change ρ z _ = _
  simp

end Shift

section Doset

variable {K K' : Type} [Field K] [Field K'] {n : ℕ}

def dGL (n : ℕ) (ϖ : Kˣ) (j : ℕ) : GL (Fin n) K :=
  ⟨diagJ n ϖ j, diagJ n (ϖ⁻¹ : Kˣ) j,
    by rw [diagJ, diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp,
    by rw [diagJ, diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp⟩

open Classical in
theorem Tj_apply (O : Subring K) (ϖ : Kˣ) (j : ℕ) (g : GL (Fin n) K) : Tj ℂ n O ϖ j g =
    if ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O, g = a * dGL n ϖ j * b then 1 else 0 := by
  simp only [Tj, Set.indicator_apply, Set.mem_setOf_eq, Units.ext_iff, Units.val_mul, Pi.one_apply]
  rfl

theorem dGL_zero (ϖ : Kˣ) : dGL n ϖ 0 = 1 := Units.ext (by simp [dGL, diagJ])

theorem dGL_comm (ϖ : Kˣ) (g : GL (Fin n) K) : dGL n ϖ n * g = g * dGL n ϖ n := Units.ext (by
  have : (dGL n ϖ n).1 = Matrix.scalar _ (ϖ : K) := by simp [dGL, diagJ]
  rw [Units.val_mul, Units.val_mul, this]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq)

def revGL (K : Type) [Field K] (n : ℕ) : GL (Fin n) K :=
  ⟨(1 : Matrix (Fin n) (Fin n) K).submatrix id Fin.revPerm, (1 : Matrix (Fin n) (Fin n) K).submatrix Fin.revPerm id,
    by rw [Matrix.submatrix_mul_equiv]; simp,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]; simp⟩

theorem revGL_mem (O : Subring K) : revGL K n ∈ GLint (Fin n) O :=
  mem_GLint_iff.2 ⟨fun i j => by simp only [revGL, Matrix.submatrix_apply, Matrix.one_apply]; split_ifs <;> simp,
    fun i j => by
      change (1 : Matrix (Fin n) (Fin n) K) _ _ ∈ O
      simp only [Matrix.one_apply]; split_ifs <;> simp⟩

theorem dGL_mul_inv (ϖ : Kˣ) {j : ℕ} (hj : j ≤ n) :
    dGL n ϖ n * (dGL n ϖ j)⁻¹ = (revGL K n)⁻¹ * dGL n ϖ (n - j) * revGL K n := Units.ext (by
  change diagJ n (ϖ : K) n * diagJ n ((ϖ⁻¹ : Kˣ) : K) j = (1 : Matrix (Fin n) (Fin n) K).submatrix Fin.revPerm id *
    diagJ n (ϖ : K) (n - j) * (1 : Matrix (Fin n) (Fin n) K).submatrix id Fin.revPerm
  rw [show diagJ n (ϖ : K) (n - j) = (diagJ n (ϖ : K) (n - j)).submatrix id id from rfl,
    ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
    one_mul, mul_one, diagJ, diagJ, diagJ, Matrix.submatrix_diagonal_equiv, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have := i.2
  by_cases h : (i : ℕ) < j
  · simp [h, show ¬ (n - (i + 1) < n - j) by omega]
  · simp [h, show n - (i + 1) < n - j by omega])

def invT (c : K ≃+* K') (n : ℕ) : GL (Fin n) K ≃* GL (Fin n) K' where
  toFun g := dualConj 1 (bc (c : K →+* K') g)
  invFun g := dualConj 1 (bc (c.symm : K' →+* K) g)
  left_inv g := Units.ext (Matrix.ext fun i j => by
    rw [dualConj_one_val, ← map_inv, ← map_inv]
    exact (congrArg c.symm (congrFun₂ (dualConj_one_val _) j i)).trans (c.symm_apply_apply _))
  right_inv g := Units.ext (Matrix.ext fun i j => by
    rw [dualConj_one_val, ← map_inv, ← map_inv]
    exact (congrArg c (congrFun₂ (dualConj_one_val _) j i)).trans (c.apply_symm_apply _))
  map_mul' g h := by simp only [map_mul]

theorem invT_val (c : K ≃+* K') (g : GL (Fin n) K) (i j : Fin n) : (invT c n g).1 i j = c ((g⁻¹).1 j i) :=
  congrFun₂ (dualConj_one_val _) i j

variable (c : K ≃+* K') {O : Subring K} {O' : Subring K'} (hO : ∀ a, c a ∈ O' ↔ a ∈ O)

include hO in
theorem mem_iff_invT (g : GL (Fin n) K) : g ∈ GLint (Fin n) O ↔ invT c n g ∈ GLint (Fin n) O' := by
  simp only [mem_GLint_iff, ← map_inv, invT_val, hO, inv_inv]
  exact ⟨fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩, fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩⟩

theorem invT_dGL (ϖ : Kˣ) (j : ℕ) : invT c n (dGL n ϖ j)⁻¹ = dGL n (Units.map (c : K →* K') ϖ) j :=
  Units.ext (Matrix.ext fun a b => by
    rw [invT_val, inv_inv]
    simp only [dGL, diagJ, Matrix.diagonal_apply, eq_comm (a := b)]
    split_ifs with h h1 h2 h2 <;> first | simp; done | (subst h; contradiction))

theorem Tj_shift_self (O : Subring K) (ϖ : Kˣ) (g : GL (Fin n) K) :
    Tj ℂ n O ϖ n (dGL n ϖ n * g) = Tj ℂ n O ϖ 0 g := by
  have e : ∀ a b, a * dGL n ϖ n * b = dGL n ϖ n * (a * dGL n ϖ 0 * b) := fun a b => by
    rw [dGL_zero, mul_one, ← dGL_comm, mul_assoc]
  classical
  rw [Tj_apply, Tj_apply]
  refine if_congr ?_ rfl rfl
  simp only [e, mul_right_inj]

include hO in

theorem Tj_invT (ϖ : Kˣ) {j : ℕ} (hj : j ≤ n) (g : GL (Fin n) K) :
    Tj ℂ n O' (c ϖ) j (invT c n g) = Tj ℂ n O ϖ (n - j) (dGL n ϖ n * g) := by
  classical
  have e : dGL n ϖ (n - j) = revGL K n * (dGL n ϖ n * (dGL n ϖ j)⁻¹) * (revGL K n)⁻¹ := by
    rw [dGL_mul_inv ϖ hj]; group
  refine (Tj_apply O' (Units.map (c : K →* K') ϖ) j _).trans ?_
  rw [Tj_apply, ← invT_dGL]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, H⟩
    obtain ⟨a, rfl⟩ := (invT c n).surjective a
    obtain ⟨b, rfl⟩ := (invT c n).surjective b
    rw [← map_mul, ← map_mul, (invT c n).apply_eq_iff_eq] at H
    rw [← mem_iff_invT c hO] at ha hb
    refine ⟨_, mul_mem ha (inv_mem (revGL_mem O)), _, mul_mem (revGL_mem O) hb, ?_⟩
    rw [e, H, ← mul_assoc, ← mul_assoc, dGL_comm]; group
  · rintro ⟨a, ha, b, hb, H⟩
    refine ⟨_, (mem_iff_invT c hO _).1 (mul_mem ha (revGL_mem O)), _,
      (mem_iff_invT c hO _).1 (mul_mem (inv_mem (revGL_mem O)) hb), ?_⟩
    rw [← map_mul, ← map_mul, (invT c n).apply_eq_iff_eq, ← mul_right_inj (dGL n ϖ n), H, e,
      ← mul_assoc (dGL n ϖ n), ← mul_assoc (dGL n ϖ n), dGL_comm ϖ (a * _)]
    group

end Doset

section Satake

variable {E : Type} [Field E] [NumberField E] {w w' : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] (c : w.adicCompletion E ≃+* w'.adicCompletion E)
  (hc : ∀ a, Valued.v (c a) = Valued.v a)

include hc in
theorem map_mem_Ov_iff (a : w.adicCompletion E) : c a ∈ Ov E w' ↔ a ∈ Ov E w := by
  change Valued.v (c a) ≤ 1 ↔ Valued.v a ≤ 1
  rw [hc]

include hc in

theorem isSatVecGL_invT (hq : qV E w' = qV E w) {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V}
    {B : Multiset ℂˣ} (hx : IsSatVecGL w ρ x B) :
    IsSatVecGL w' (ρ.comp (invT c n).symm.toMonoidHom) x (B.map (·⁻¹)) := by
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨h0, hf, hB, hT⟩ := hx
  refine ⟨h0, (mem_fixed_comp_symm _ hK).2 hf, by simpa using hB, fun ϖ' hϖ' j hj => ?_⟩
  obtain ⟨p, rfl⟩ := c.surjective ϖ'
  have hp : IsUnifV E w p := (hc p).symm.trans hϖ'
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  have h1 := apply_heckeVec_shift (Tj_mem_hecke (n := n) hp n).1 hf (dGL n ϖ n)
  have h2 := apply_heckeVec_shift (Tj_mem_hecke (n := n) hp (n - j)).1 hf (dGL n ϖ n)
  rw [funext (Tj_shift_self _ ϖ), hT _ hp 0 n.zero_le, hT _ hp n le_rfl, satEig_zero, one_smul] at h1
  rw [← funext (Tj_invT c (map_mem_Ov_iff c hc) ϖ hj), hT _ hp _ (n.sub_le j), ← satEig_inv_mul hB hj, mul_smul, ← h1,
    ← map_smul] at h2
  rw [heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ' j).1 hf, hq]
  simpa [Function.comp_def] using congrArg (ρ (dGL n ϖ n)⁻¹) h2

end Satake

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {w w' : HeightOneSpectrum (𝓞 E)}

theorem toCompl_smul (h : w.under (𝓞 F) = v) (a : Fv F v) (y : Fv F v ⊗[F] E) :
    toCompl h (a • y) = complMap h a * toCompl h y := by
  rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, toCompl_tmul, map_one, mul_one]
  rfl

theorem toCompl_surjective (h : w.under (𝓞 F) = v) : Function.Surjective (toCompl h) := fun z => by
  obtain ⟨y, hy⟩ := (finAdEquiv F E).surjective (singleFin w z)
  exact ⟨_, (finAdEquiv_apply h y).symm.trans ((congrArg (· w) hy).trans (evalV_singleFin_self w z))⟩

theorem valued_complMap_le (h : w.under (𝓞 F) = v) (m : ℕ) {a : Fv F v} (ha : Valued.v a ≤ WithZero.exp (-(m : ℤ))) :
    Valued.v (complMap h a) ≤ WithZero.exp (-(m : ℤ)) := by
  subst h; exact GlobalTheory.AdeleBaseChange.locMap_valued w m a ha

theorem splitPrime_eq_of_toCompl (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v}
    (e : ∀ y, toCompl h y = complMap h (splitProj τ y)) : splitPrime τ = w := by
  refine HeightOneSpectrum.ext ((splitPrime τ).isMaximal.eq_of_le w.isPrime.ne_top fun x hx => ?_)
  have h1 := e (1 ⊗ₜ[F] (x : E))
  rw [toCompl_tmul, splitProj_tmul, map_one, one_mul, one_mul] at h1
  have h2 := valued_complMap_le h 1 (a := τ x) (by
    have := (mem_splitPrime τ x).1 hx
    rwa [← WithZero.exp_zero, show (0 : ℤ) = -((1 : ℕ) : ℤ) + 1 by norm_num, WithZero.exp_add,
      WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero] at this)
  rw [← h1, ReciprocityTheory.Aut.adic_valued_algebraMap] at h2
  refine (w.valuation_lt_one_iff_mem (K := E) x).1 (h2.trans_lt ?_)
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

theorem toCompl_eq (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w)
    (y : Fv F v ⊗[F] E) : toCompl h y = complMap h (splitProj τ y) := by
  have key : ∀ ρ : E →ₐ[F] Fv F v, toCompl h (splitIdem hE ρ) = 1 → ∀ y, toCompl h y = complMap h (splitProj ρ y) :=
    fun ρ e y => by simpa [e, toCompl_smul] using congrArg (toCompl h) (splitIdem_mul hE ρ y)
  have h1 : IsIdempotentElem (toCompl h (splitIdem hE τ)) := (map_mul _ _ _).symm.trans
    (congrArg _ (splitIdem_mul_self hE τ))
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 h1 with e | e
  · exact absurd ((splitPrime_eq_of_toCompl h (key (τ.comp σ) (by simp [splitIdem_comp, e]))).trans hτ.symm)
      (splitPrime_comp_ne hE τ)
  · exact key τ e y

theorem complMap_apply (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w)
    (x : E) : complMap h (τ x) = algebraMap E _ x := by
  simpa using (toCompl_eq hE h hτ (1 ⊗ₜ[F] x)).symm

def complEquiv (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) :
    Fv F v ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (complMap h) ⟨(complMap h).injective, fun z =>
    (toCompl_surjective h z).elim fun y hy => ⟨_, (toCompl_eq hE h hτ y).symm.trans hy⟩⟩

theorem valued_complMap (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w)
    (a : Fv F v) : Valued.v (complMap h a) = Valued.v a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  obtain ⟨x, hx⟩ := v.valuation_surjective F (Valued.v a)
  have h1 : Valued.v (algebraMap F (Fv F v) x) = Valued.v a := (ReciprocityTheory.Aut.adic_valued_algebraMap v x).trans hx
  have h2 : Valued.v (complMap h (algebraMap F (Fv F v) x)) = Valued.v a := by
    rw [complMap_algebraMap, ReciprocityTheory.Aut.adic_valued_algebraMap, ← hτ, ← valued_apply_eq_valuation, τ.commutes, h1]
  have h0 : Valued.v a ≠ 0 := (map_ne_zero _).2 ha
  have h3 : Valued.v (complMap h (a / algebraMap F (Fv F v) x)) ≤ 1 :=
    complMap_mem h (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, h1, div_self h0])
  have h4 : Valued.v (complMap h (algebraMap F (Fv F v) x / a)) ≤ 1 :=
    complMap_mem h (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, h1, div_self h0])
  rw [map_div₀, map_div₀, h2] at h3 h4
  exact le_antisymm ((div_le_one₀ (zero_lt_iff.2 h0)).1 h3)
    ((div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ((map_ne_zero _).2 ha)))).1 h4)

theorem qV_splitPrime (τ τ' : E →ₐ[F] Fv F v) : qV E (splitPrime τ) = qV E (splitPrime τ') := by
  rw [qV, qV, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr ((splitResidueEquiv τ).trans (splitResidueEquiv τ').symm).toEquiv

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}

section Chart

variable (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w)

theorem complEquiv_mem_iff (a : Fv F v) : complEquiv hE h hτ a ∈ Ov E w ↔ a ∈ v.adicCompletionIntegers F := by
  change Valued.v (complMap h a) ≤ 1 ↔ Valued.v a ≤ 1
  rw [valued_complMap hE h hτ]

theorem mem_latAt_iff (u : Fin n → Fv F v) : complEquiv hE h hτ ∘ u ∈ latAt w L ↔ u ∈ splitLat τ L := by
  constructor
  · intro hu
    have key : ∀ z ∈ latAt w L, (complEquiv hE h hτ).symm ∘ z ∈ splitLat τ L := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => (complEquiv hE h hτ).eq_symm_apply.2
          ((congrArg _ (one_mul _)).trans (complMap_apply hE h hτ _))⟩
      | zero => convert (splitLat τ L).zero_mem using 1; funext i; simp
      | add a b _ _ ha hb => convert add_mem ha hb using 1; funext i; simp
      | smul a b _ hb =>
        convert (splitLat τ L).smul_mem ⟨(complEquiv hE h hτ).symm a, (complEquiv_mem_iff hE h hτ _).1 (by simp)⟩ hb
          using 1
        funext i
        exact map_mul _ _ _
    convert key _ hu using 1
    funext i; simp
  · rintro ⟨y, hy, rfl⟩
    refine latLoc_induction (p := fun y => complEquiv hE h hτ ∘ splitVec τ y ∈ latAt w L) (fun a ha x hx => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hy
    · convert (latAt w L).smul_mem ⟨_, complMap_mem h ha⟩ (Submodule.subset_span ⟨x, hx, rfl⟩) using 1
      funext i
      exact (toCompl_eq hE h hτ _).symm
    · convert (latAt w L).zero_mem using 1; funext i; simp [splitVec]
    · convert add_mem hy hz using 1; funext i; simp [splitVec]
    · convert neg_mem hy using 1; funext i; simp [splitVec]

theorem isFrameAt_iff (β : GL (Fin n) (Fv F v)) :
    IsFrameAt w L (bc (complEquiv hE h hτ : Fv F v →+* w.adicCompletion E) β) ↔ IsSplitBasis τ L β := by
  have e : ∀ u, (bc (complEquiv hE h hτ : Fv F v →+* w.adicCompletion E) β).1 *ᵥ (complEquiv hE h hτ ∘ u) =
      complEquiv hE h hτ ∘ (β.1 *ᵥ u) := fun u => funext fun i =>
    (RingHom.map_mulVec (complEquiv hE h hτ : Fv F v →+* w.adicCompletion E) β.1 u i).symm
  rw [IsFrameAt, (complEquiv hE h hτ).surjective.comp_left.forall]
  simp only [e, mem_latAt_iff, Function.comp_apply, complEquiv_mem_iff]
  rfl

theorem locMat_eq (g : GLoc σ J v) :
    locMat σ J h g = bc (complEquiv hE h hτ : Fv F v →+* w.adicCompletion E) (splitHom σ J τ g) :=
  Units.ext (Matrix.ext fun _ _ => toCompl_eq hE h hτ _)

end Chart

theorem exists_conj_chart (hE : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v) (hne : w ≠ w')
    (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)}
    (he : IsSplitChart σ J L h e) :
    ∃ c : w.adicCompletion E ≃+* w'.adicCompletion E, (∀ a, Valued.v (c a) = Valued.v a) ∧ qV E w' = qV E w ∧
      (∀ y, c (toCompl h y) = toCompl h' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y)) ∧
      IsSplitChart σ J L h' (e.trans (invT c n)) := by
  obtain ⟨τ, hτ, -⟩ := existsUnique_splitPrime_eq hE hne h h'
  obtain ⟨τ', hτ', -⟩ := existsUnique_splitPrime_eq hE hne.symm h' h
  obtain rfl : τ' = τ.comp σ := (eq_or_eq_comp_conj hE τ τ').resolve_left fun e => hne (hτ.symm.trans (e ▸ hτ'))
  let φ := complEquiv hE h hτ
  let φ' := complEquiv hE h' hτ'
  have hc : ∀ a, Valued.v (φ.symm.trans φ' a) = Valued.v a := fun a => by
    obtain ⟨a, rfl⟩ := φ.surjective a
    rw [RingEquiv.trans_apply, φ.symm_apply_apply]
    exact (valued_complMap hE h' hτ' a).trans (valued_complMap hE h hτ a).symm
  obtain ⟨⟨a, ha, ea⟩, hK⟩ := he
  refine ⟨φ.symm.trans φ', hc, hτ ▸ hτ' ▸ qV_splitPrime _ _, fun y => ?_, ?_, fun g =>
    (hK g).trans (mem_iff_invT _ (map_mem_Ov_iff _ hc) _)⟩
  · rw [toCompl_eq hE h hτ, toCompl_eq hE h' hτ', splitProj_comp_sigR hE]
    exact congrArg φ' (φ.symm_apply_apply _)
  obtain ⟨β, rfl⟩ : ∃ β, bc (φ : Fv F v →+* w.adicCompletion E) β = a :=
    ⟨bc (φ.symm : w.adicCompletion E →+* Fv F v) a, Units.ext (Matrix.ext fun i j => φ.apply_symm_apply _)⟩
  refine ⟨_, (isFrameAt_iff hE h' hτ' _).2 (((isFrameAt_iff hE h hτ β).1 ha).dual hE hJ hL), fun g => ?_⟩
  rw [MulEquiv.trans_apply, ea, locMat_eq hE h hτ, locMat_eq hE h' hτ', ← map_inv, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul, ← splitEquivIn_apply hE hJ, ← splitEquivIn_apply hE hJ, splitEquivIn_comp]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invT_val, ← map_inv]
  exact congrArg φ' ((φ.symm_apply_apply _).trans
    (congrFun₂ (dualConj_one_val (splitEquivIn hE hJ τ β g)) i j).symm)

theorem isSplit_of_ne (hne : w ≠ w') (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) : IsSplit (E := E) v :=
  ⟨w, w', hne, congrArg HeightOneSpectrum.asIdeal h, congrArg HeightOneSpectrum.asIdeal h'⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {B B' : Multiset ℂˣ}

theorem isParamVec_conj (hE : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v) (hne : w ≠ w')
    (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hx : IsParamVec σ J L h ρ x B) :
    IsParamVec σ J L h' ρ x (B.map (·⁻¹)) := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, -⟩
  · obtain ⟨c, hc, hq, -, he'⟩ := exists_conj_chart hE hJ hL hne h h' he
    exact Or.inl ⟨hv, _, he', isSatVecGL_invT c hc hq hx⟩
  · exact absurd (isSplit_of_ne hne h h') (not_isSplit_of_isInertAt hw)

theorem hasParam_conj (hE : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v) (hne : w ≠ w')
    (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hρ : HasParam σ J L h ρ B) :
    HasParam σ J L h' ρ (B.map (·⁻¹)) := by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  rcases isParamVec_conj hE hJ hL hne h h' hx with ⟨hv, e, he, hx'⟩ | ⟨hw, -⟩
  · exact Or.inl ⟨hv, e, he, (Submodule.ne_bot_iff _).2 ⟨x, hx'.2.1, hx'.1⟩, fun y hy h0 =>
      (isParamVec_conj hE hJ hL hne h h' (hρ.isParamVec ((mem_fixed_comp_symm e he.2).1 hy) h0)).isSatVecGL hv he⟩
  · exact absurd (isSplit_of_ne hne h h') (not_isSplit_of_isInertAt hw)

theorem eq_map_inv_of_isParamVec (hE : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v) (hne : w ≠ w')
    {h : w.under (𝓞 F) = v} {h' : w'.under (𝓞 F) = v} (hx : IsParamVec σ J L h ρ x B)
    (hx' : IsParamVec σ J L h' ρ x B') : B' = B.map (·⁻¹) :=
  hx'.unique_of_isSplit (isSplit_of_ne hne h h') (isParamVec_conj hE hJ hL hne h h' hx)

theorem eq_map_inv_of_hasParam (hE : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v) (hne : w ≠ w')
    {h : w.under (𝓞 F) = v} {h' : w'.under (𝓞 F) = v} (hρ : HasParam σ J L h ρ B)
    (hρ' : HasParam σ J L h' ρ B') : B' = B.map (·⁻¹) := by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact eq_map_inv_of_isParamVec hE hJ hL hne hx (hρ'.isParamVec hx.mem_fixed hx.ne_zero)

theorem bcParam_map_inv (n : ℕ) (α : Fin (n / 2) → ℂˣ) : (bcParam n α).map (·⁻¹) = bcParam n α := by
  simp only [bcParam, Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv, Multiset.map_replicate, inv_one]
  rw [add_comm (Multiset.map _ _)]

theorem map_inv_of_isParamVec (hw : IsInertAt F E v w) {h : w.under (𝓞 F) = v} (hx : IsParamVec σ J L h ρ x B) :
    B.map (·⁻¹) = B := by
  rcases hx with ⟨hv, -⟩ | ⟨-, c, ϖ, e, α, -, -, -, rfl⟩
  · exact absurd hv (not_isSplit_of_isInertAt hw)
  · exact bcParam_map_inv n α

theorem map_inv_of_hasParam (hw : IsInertAt F E v w) {h : w.under (𝓞 F) = v} (hρ : HasParam σ J L h ρ B) :
    B.map (·⁻¹) = B := hρ.exists_vec.elim fun _ hx => map_inv_of_isParamVec hw hx

theorem param_conj_place (hE : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v)
    (h : w.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ J v) V) (B : Multiset ℂˣ) :
    (∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' →
      (∀ x, IsParamVec σ J L h ρ x B → IsParamVec σ J L h' ρ x (B.map (·⁻¹))) ∧
      (HasParam σ J L h ρ B → HasParam σ J L h' ρ (B.map (·⁻¹)))) ∧
    (IsInertAt F E v w → (∀ x, IsParamVec σ J L h ρ x B → B.map (·⁻¹) = B) ∧
      (HasParam σ J L h ρ B → B.map (·⁻¹) = B)) ∧
    ∀ α : Fin (n / 2) → ℂˣ, (bcParam n α).map (·⁻¹) = bcParam n α :=
  ⟨fun _ h' hne => ⟨fun _ => isParamVec_conj hE hJ hL hne h h', hasParam_conj hE hJ hL hne h h'⟩,
    fun hw => ⟨fun _ => map_inv_of_isParamVec hw, map_inv_of_hasParam hw⟩, bcParam_map_inv n⟩

theorem exists_isSplitChart_of_basis (hE : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v)
    (h : w.under (𝓞 F) = v) {τ : E →ₐ[F] Fv F v} (hτ : splitPrime τ = w) {β : GL (Fin n) (Fv F v)}
    (hβ : IsSplitBasis τ L β) : ∃ e, IsSplitChart σ J L h e := by
  let φ := complEquiv hE h hτ
  refine ⟨(splitEquivIn hE hJ τ β).toMulEquiv.trans (Units.mapEquiv φ.mapMatrix.toMulEquiv),
    ⟨_, (isFrameAt_iff hE h hτ β).2 hβ, fun g => ?_⟩, fun g => (mem_stabLoc_iff_GLint hE hJ hL hβ).trans ?_⟩
  · rw [locMat_eq hE h hτ, ← map_inv, ← map_mul, ← map_mul]; rfl
  · rw [mem_GLint_iff, mem_GLint_iff]
    exact (and_congr (forall₂_congr fun _ _ => complEquiv_mem_iff hE h hτ _)
      (forall₂_congr fun _ _ => complEquiv_mem_iff hE h hτ _)).symm

example (hE : IsCMExt F E σ) (α : Fin n → ℂˣ) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v)
      (h' : w'.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ (1 : Matrix (Fin n) (Fin n) E) v) (psSpaceGL w α)),
      w ≠ w' ∧ HasParam σ 1 (stdLattice E n) h ρ (Finset.univ.val.map α) ∧
        HasParam σ 1 (stdLattice E n) h' ρ ((Finset.univ.val.map α).map (·⁻¹)) := by
  obtain ⟨v, τ, hJ, hL, hβ⟩ := exists_split_data hE n
  have hne := (splitPrime_comp_ne hE τ).symm
  obtain ⟨e, he⟩ := exists_isSplitChart_of_basis hE hJ hL (splitPrime_under τ) rfl hβ
  have H := hasParam_psFunGL (isSplit_of_ne hne (splitPrime_under _) (splitPrime_under _)) he α
  exact ⟨v, _, _, splitPrime_under τ, splitPrime_under _, _, hne, H, hasParam_conj hE hJ hL hne _ _ H⟩

end GlobalTheory.LFun.ConjPlace

end
