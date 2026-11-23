import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
import GroundTheory.Brauer.TensorSimple
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CoordP

variable {p : ℕ} [Fact p.Prime]

theorem not_dvd_den_of_norm_le_one' (c : ℚ) (hc : ‖(c : ℚ_[p])‖ ≤ 1) : ¬ p ∣ c.den := by
  intro hd
  have hden : ‖((c.den : ℤ) : ℚ_[p])‖ < 1 :=
    Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)
  have hnum : ‖((c.num : ℤ) : ℚ_[p])‖ < 1 := by
    have h1 : ((c.num : ℤ) : ℚ_[p]) = (c : ℚ_[p]) * ((c.den : ℤ) : ℚ_[p]) := by
      have : (c.num : ℚ) = c * (c.den : ℤ) := by
        rw [Int.cast_natCast, Rat.mul_den_eq_num]
      exact_mod_cast congrArg (fun x : ℚ => (x : ℚ_[p])) this
    rw [h1, norm_mul]
    calc ‖(c : ℚ_[p])‖ * ‖((c.den : ℤ) : ℚ_[p])‖ ≤ 1 * ‖((c.den : ℤ) : ℚ_[p])‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hden
  have hpn : (p : ℤ) ∣ c.num := Padic.norm_intCast_lt_one_iff.1 hnum
  have h2 : p ∣ c.num.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs]; exact (dvd_abs _ _).2 hpn
  have h3 := Nat.dvd_gcd h2 hd
  rw [c.reduced.gcd_eq_one] at h3
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.1 h3)

def starL (G : HTGroup p) : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C where
  toFun x := (starT G.star ℚ_[p] x).unop
  map_add' x y := by simp
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      rw [TensorProduct.smul_tmul', starT_tmul, starT_tmul, TensorProduct.smul_tmul']; rfl
    | add x y hx hy =>
      simp only [smul_add, map_add, MulOpposite.unop_add, RingHom.id_apply] at hx hy ⊢
      rw [hx, hy]

def ent (G : HTGroup p) (w : Fin G.m) (r s : Fin G.n) : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] PadicAlgCl p :=
  (IntermediateField.val (G.Fw w)).toLinearMap ∘ₗ (Matrix.entryLinearMap ℚ_[p] (G.Fw w) r s) ∘ₗ
    (G.locW w).toLinearMap

theorem locW_one_tmul (G : HTGroup p) (w : Fin G.m) (c : G.C) :
    G.locW w ((1 : ℚ_[p]) ⊗ₜ c) = G.rho w c := by
  unfold HTGroup.locW
  erw [Algebra.TensorProduct.lift_tmul]
  simp

theorem linInd (G : HTGroup p) (w : Fin G.m) {ι : Type} (e : ι → G.C) (he : LinearIndependent G.F e) :
    LinearIndependent (G.Fw w) (fun l => G.rho w (e l)) := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  have hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a :=
    fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) := { G.rho w with commutes' := hg }
  let L : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : G.Fw w) ⊗ₜ x) = G.rho w x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : G.Fw w) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hT : LinearIndependent (G.Fw w) (fun l => (1 : G.Fw w) ⊗ₜ[G.F] (e l)) :=
    Module.Flat.linearIndependent_one_tmul he
  have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have e' : (fun l => G.rho w (e l)) = L.toLinearMap ∘ (fun l => (1 : G.Fw w) ⊗ₜ[G.F] (e l)) := by
    funext l
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [hL]
  rw [e']
  exact this

theorem embInd (G : HTGroup p) {ι : Type} [Fintype ι] (f : Module.Basis ι ℚ G.F) (a : ι → ℚ_[p])
    (h1 : ∀ w, ∑ k, a k • G.emb w (f k) = 0)
    (h2 : ∀ w, ∑ k, a k • G.emb w (IsCMField.complexConj G.F (f k)) = 0) : a = 0 := by
  have hall : ∀ τ : G.F →+* PadicAlgCl p, ∑ k, a k • τ (f k) = 0 := by
    intro τ
    rcases GlobalTheory.GlobEig.liesOver_or_conj G τ with h | h
    · obtain ⟨i, σ, hσ⟩ := G.emb_all τ h
      have e1 : ∀ k, τ (f k) = σ (G.emb i (f k)) := fun k => by rw [hσ]; rfl
      simp only [e1]
      rw [show ∑ x, a x • σ (G.emb i (f x)) = σ (∑ x, a x • G.emb i (f x)) by
        rw [map_sum]; exact Finset.sum_congr rfl fun x _ => by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes], h1 i, map_zero]
    · obtain ⟨i, σ, hσ⟩ := G.emb_all _ h
      have e1 : ∀ k, τ (f k) = σ (G.emb i (IsCMField.complexConj G.F (f k))) := fun k => by
        have := congrArg (fun φ : G.F →+* PadicAlgCl p => φ (IsCMField.complexConj G.F (f k))) hσ
        simp only [RingHom.comp_apply, RingHom.coe_coe, IsCMField.complexConj_apply_apply] at this
        exact this
      simp only [e1]
      rw [show ∑ x, a x • σ (G.emb i (IsCMField.complexConj G.F (f x))) =
          σ (∑ x, a x • G.emb i (IsCMField.complexConj G.F (f x))) by
        rw [map_sum]; exact Finset.sum_congr rfl fun x _ => by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes], h2 i, map_zero]
  have hcard : Fintype.card ι = Fintype.card (G.F →ₐ[ℚ] PadicAlgCl p) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis f]
  let eqv : ι ≃ (G.F →ₐ[ℚ] PadicAlgCl p) := Fintype.equivOfCardEq hcard
  have hdet : (Algebra.embeddingsMatrixReindex ℚ (PadicAlgCl p) f eqv).det ≠ 0 := by
    intro h0
    have h3 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ (PadicAlgCl p) f eqv
    rw [h0, zero_pow two_ne_zero] at h3
    exact Algebra.discr_not_zero_of_basis ℚ f ((map_eq_zero _).mp h3)
  set v : ι → PadicAlgCl p := fun k => algebraMap ℚ_[p] (PadicAlgCl p) (a k) with hv
  have hvM : Matrix.vecMul v (Algebra.embeddingsMatrixReindex ℚ (PadicAlgCl p) f eqv) = 0 := by
    funext j
    have := hall (eqv j).toRingHom
    simp only [Matrix.vecMul, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_apply, Equiv.symm_symm, Pi.zero_apply]
    simpa [hv, Algebra.smul_def] using this
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvM
  funext k
  have := congrFun hv0 k
  simpa [hv] using this

def shA (G : HTGroup p) : G.C →+ G.C :=
  (MulOpposite.opAddEquiv.symm.toAddMonoidHom).comp G.star.toAddMonoidHom

theorem shA_apply (G : HTGroup p) (x : G.C) : shA G x = sh G x := rfl

theorem sh_smul (G : HTGroup p) (z : G.F) (y : G.C) :
    sh G (z • y) = IsCMField.complexConj G.F z • sh G y := by
  rw [Algebra.smul_def, Algebra.smul_def]
  simp only [sh, map_mul, MulOpposite.unop_mul]
  rw [G.star_F]
  exact (Algebra.commutes _ _).symm

theorem sh_sh (G : HTGroup p) (y : G.C) : sh G (sh G y) = y := G.star_star y

theorem sh_linInd (G : HTGroup p) {ι : Type} (e : ι → G.C) (he : LinearIndependent G.F e) :
    LinearIndependent G.F (fun l => sh G (e l)) := by
  rw [linearIndependent_iff'] at he ⊢
  intro s g hg l hl
  have key : ∑ i ∈ s, IsCMField.complexConj G.F (g i) • e i = 0 := by
    have h := congrArg (shA G) hg
    rw [map_sum, map_zero] at h
    simpa only [shA_apply, sh_smul, sh_sh] using h
  have h := he s _ key l hl
  simpa using h

theorem inj (G : HTGroup p) (x : ℚ_[p] ⊗[ℚ] G.C) (h1 : ∀ w, G.locW w x = 0)
    (h2 : ∀ w, G.locW w (starT G.star ℚ_[p] x).unop = 0) : x = 0 := by
  set f := Module.finBasis ℚ G.F with hf
  set e := Module.finBasis G.F G.C with he
  set bb := f.smulTower e with hbb
  set bT := Algebra.TensorProduct.basis ℚ_[p] bb with hbT
  set a := bT.equivFun x with ha
  have hx : x = ∑ kl, a kl • ((1 : ℚ_[p]) ⊗ₜ (f kl.1 • e kl.2)) := by
    conv_lhs => rw [← bT.sum_equivFun x]
    refine Finset.sum_congr rfl fun kl _ => ?_
    rw [hbT, Algebra.TensorProduct.basis_apply, hbb, Module.Basis.smulTower_apply]
  have hxs : (starT G.star ℚ_[p] x).unop =
      ∑ kl, a kl • ((1 : ℚ_[p]) ⊗ₜ (IsCMField.complexConj G.F (f kl.1) • sh G (e kl.2))) := by
    have := map_sum (starL G) (fun kl => a kl • ((1 : ℚ_[p]) ⊗ₜ (f kl.1 • e kl.2))) Finset.univ
    rw [← hx] at this
    refine this.trans (Finset.sum_congr rfl fun kl _ => ?_)
    rw [map_smul]
    show a kl • (starT G.star ℚ_[p] ((1 : ℚ_[p]) ⊗ₜ (f kl.1 • e kl.2))).unop = _
    rw [starT_tmul]
    show a kl • (1 : ℚ_[p]) ⊗ₜ sh G (f kl.1 • e kl.2) = _
    rw [sh_smul]

  have himg : ∀ w (z : G.F) (y : G.C), G.rho w (z • y) = G.embW w z • G.rho w y := by
    intro w z y
    rw [Algebra.smul_def, map_mul, G.rho_F, Matrix.smul_eq_diagonal_mul]
    rfl
  have hcol : ∀ (w : Fin G.m) (g : G.F → G.F) (R : Fin (Module.finrank G.F G.C) → G.C),
      LinearIndependent G.F R →
      G.locW w (∑ kl, a kl • ((1 : ℚ_[p]) ⊗ₜ (g (f kl.1) • R kl.2))) = 0 →
      ∀ l, ∑ k, a (k, l) • G.emb w (g (f k)) = 0 := by
    intro w g R hR h0 l
    rw [map_sum] at h0
    simp only [map_smul, locW_one_tmul, himg] at h0
    rw [Fintype.sum_prod_type, Finset.sum_comm] at h0
    simp only [← smul_assoc, ← Finset.sum_smul] at h0
    have h3 := Fintype.linearIndependent_iff.1 (linInd G w R hR) _ h0 l
    have h4 := congrArg (G.Fw w).val h3
    rw [map_sum, map_zero] at h4
    simpa [HTGroup.embW, embOf_apply] using h4
  have hz : ∀ l, (fun k => a (k, l)) = 0 := by
    intro l
    refine embInd G f _ (fun w => ?_) (fun w => ?_)
    · exact hcol w id e e.linearIndependent (by have h := h1 w; rw [hx] at h; exact h) l
    · exact hcol w (IsCMField.complexConj G.F) (fun l => sh G (e l)) (sh_linInd G e e.linearIndependent)
        (by have h := h2 w; rw [hxs] at h; exact h) l
  rw [hx]
  refine Finset.sum_eq_zero fun kl _ => ?_
  rw [show a kl = 0 from congrFun (hz kl.2) kl.1, zero_smul]

theorem coord_bound : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : ℝ), ∃ e : ℕ, ∀ c : G.C,
    (∀ (w : Fin G.m) (a b : Fin G.n), ‖((G.rho w c a b : G.Fw w) : PadicAlgCl p)‖ ≤ B ∧
      ‖((G.rho w (sh G c) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B) →
    ∀ i, ∃ (k : ℤ) (m : ℕ), ¬ p ∣ m ∧ (Module.finBasis ℚ G.C).repr c i * (p : ℚ) ^ e = k / m := by
  intro p _ G B
  set b := Module.finBasis ℚ G.C with hb
  set bT := Algebra.TensorProduct.basis ℚ_[p] b with hbT
  let Φ : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]]
      (Fin G.m → Fin G.n → Fin G.n → PadicAlgCl p) × (Fin G.m → Fin G.n → Fin G.n → PadicAlgCl p) :=
    LinearMap.prod (LinearMap.pi fun w => LinearMap.pi fun r => LinearMap.pi fun s => ent G w r s)
      (LinearMap.pi fun w => LinearMap.pi fun r => LinearMap.pi fun s => ent G w r s ∘ₗ starL G)
  have hΦ : ∀ x, Φ x = 0 → x = 0 := by
    intro x hx
    have hx1 := congrArg Prod.fst hx
    have hx2 := congrArg Prod.snd hx
    refine inj G x (fun w => ?_) (fun w => ?_)
    · ext r s
      have h : ((G.locW w x r s : G.Fw w) : PadicAlgCl p) = 0 := congrFun (congrFun (congrFun hx1 w) r) s
      simpa using h
    · ext r s
      have h : ((G.locW w (starT G.star ℚ_[p] x).unop r s : G.Fw w) : PadicAlgCl p) = 0 :=
        congrFun (congrFun (congrFun hx2 w) r) s
      simpa using h
  let L := Φ ∘ₗ bT.equivFun.symm.toLinearMap
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    have h0 : bT.equivFun.symm a = 0 := hΦ _ ha
    rw [Module.Basis.equivFun_symm_apply] at h0
    funext j
    exact Fintype.linearIndependent_iff.1 bT.linearIndependent a h0 j
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  set R0 : ℝ := (K : ℝ) * max B 0 with hR0
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt R0 (by exact_mod_cast (Fact.out : p.Prime).one_lt : (1 : ℝ) < p)
  refine ⟨e, fun c hc i => ?_⟩
  set a : Fin (Module.finrank ℚ G.C) → ℚ_[p] := fun j => ((b.repr c j : ℚ) : ℚ_[p]) with ha
  have hsym : bT.equivFun.symm a = (1 : ℚ_[p]) ⊗ₜ c := by
    apply bT.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext j
    rw [Module.Basis.equivFun_apply, hbT, Algebra.TensorProduct.basis_repr_tmul]
    simp [ha, eq_ratCast]
  have hLa : L a = Φ ((1 : ℚ_[p]) ⊗ₜ c) := by
    show Φ (bT.equivFun.symm a) = _
    rw [hsym]
  have hnorm : ‖L a‖ ≤ max B 0 := by
    rw [hLa]
    refine norm_prod_le_iff.2 ⟨?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun w => ?_
      refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun r => ?_
      refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun s => ?_
      refine le_trans (le_of_eq ?_) ((hc w r s).1.trans (le_max_left _ _))
      show ‖((G.locW w ((1 : ℚ_[p]) ⊗ₜ c) r s : G.Fw w) : PadicAlgCl p)‖ = _
      rw [locW_one_tmul]
    · refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun w => ?_
      refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun r => ?_
      refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun s => ?_
      refine le_trans (le_of_eq ?_) ((hc w r s).2.trans (le_max_left _ _))
      show ‖((G.locW w (starT G.star ℚ_[p] ((1 : ℚ_[p]) ⊗ₜ c)).unop r s : G.Fw w) : PadicAlgCl p)‖ = _
      rw [starT_tmul, locW_one_tmul]; rfl
  have h1 : ‖a‖ ≤ R0 := by
    have h3 := hK.le_mul_dist a 0
    rw [dist_zero_right, map_zero, dist_zero_right] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have h2 : ‖((b.repr c i : ℚ) : ℚ_[p])‖ ≤ R0 := (norm_le_pi_norm a i).trans h1
  set q : ℚ := b.repr c i * (p : ℚ) ^ e with hq
  have hp0 : (0 : ℝ) < (p : ℝ) ^ e := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  have hqn : ‖(q : ℚ_[p])‖ ≤ 1 := by
    rw [hq]; push_cast
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    rw [mul_inv_le_iff₀ hp0, one_mul]
    exact h2.trans he.le
  exact ⟨q.num, q.den, not_dvd_den_of_norm_le_one' q hqn, (Rat.num_div_den q).symm⟩

end GlobalTheory.CoordP
