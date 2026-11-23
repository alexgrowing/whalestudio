import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypTwA
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypVin

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PValIntN
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {p : ℕ} {G : GAtP p}

theorem epsU_val (B B' γ : GL (Fin n) E) (k : ℕ) :
    ((epsU B B' γ k : Eˣ) : E) = (B'.1.det * (B.1.det)⁻¹) ^ k * (γ.1.det)⁻¹ := by
  simp [epsU]

theorem det_cT (τ : E →+* E) (M : Matrix (Fin n) (Fin n) E) : (cT τ M).det = τ M.det := by
  unfold cT
  rw [Matrix.det_transpose]
  exact (RingHom.map_det τ M).symm

theorem epsU_conj (hJ : IsUnit J.det) (B B' γ : GL (Fin n) E) (k : ℕ) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (hB : cT (σ : E →+* E) B.1 * J * B.1 = 1) :
    σ (epsU B B' γ k : Eˣ) * (epsU B B' γ k : Eˣ) = ((cT (σ : E →+* E) B'.1 * J * B'.1).det) ^ k := by
  have hJ0 : J.det ≠ 0 := hJ.ne_zero
  have h1 : σ γ.1.det * γ.1.det = 1 := by
    have h := congrArg Matrix.det (show cT (σ : E →+* E) γ.1 * J * γ.1 = J from hγ)
    rw [Matrix.det_mul, Matrix.det_mul, det_cT] at h
    have h' : (σ γ.1.det * γ.1.det) * J.det = 1 * J.det := by
      rw [one_mul]
      calc (σ γ.1.det * γ.1.det) * J.det = (σ : E →+* E) γ.1.det * J.det * γ.1.det := by
            show (σ γ.1.det * γ.1.det) * J.det = σ γ.1.det * J.det * γ.1.det
            ring
        _ = J.det := h
    exact mul_right_cancel₀ hJ0 h'
  have h2 : σ B.1.det * B.1.det = (J.det)⁻¹ := by
    have h := congrArg Matrix.det hB
    rw [Matrix.det_mul, Matrix.det_mul, det_cT, Matrix.det_one] at h
    refine eq_inv_of_mul_eq_one_left ?_
    calc σ B.1.det * B.1.det * J.det = (σ : E →+* E) B.1.det * J.det * B.1.det := by
          show σ B.1.det * B.1.det * J.det = σ B.1.det * J.det * B.1.det
          ring
      _ = 1 := h
  have h3 : (cT (σ : E →+* E) B'.1 * J * B'.1).det = σ B'.1.det * B'.1.det * J.det := by
    rw [Matrix.det_mul, Matrix.det_mul, det_cT]
    show σ B'.1.det * J.det * B'.1.det = _
    ring
  rw [epsU_val, h3]
  calc σ ((B'.1.det * (B.1.det)⁻¹) ^ k * (γ.1.det)⁻¹) * ((B'.1.det * (B.1.det)⁻¹) ^ k * (γ.1.det)⁻¹)
      = ((σ B'.1.det * B'.1.det) * (σ B.1.det * B.1.det)⁻¹) ^ k * (σ γ.1.det * γ.1.det)⁻¹ := by
        simp only [map_mul, map_pow, map_inv₀, mul_pow, mul_inv]
        ring
    _ = _ := by rw [h1, h2, inv_inv, inv_one, mul_one]

set_option maxHeartbeats 2000000 in

theorem epsU_iw (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (hW : LocInt A) (hp : p.Prime) (hT : ¬ p ∣ T)
    (halg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (hb : ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 S.Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, (((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)).mulVec t a ∈ (A.pl v).1.adicCompletionIntegers F)
    (hJ : IsUnit J.det) (hB : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1)
    (Lc : Submodule (𝓞 E) (Fin n → E)) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B')
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U) (b k : ℕ)
    (h : y.1 ^ (b + k) = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y.1 ^ b * κ.1) (v : Fin G.P.nV) :
    (A.iw v (epsU A.B B' γ k : Eˣ) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range ∧
      A.iw v (σ (epsU A.B B' γ k : Eˣ)) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range) ∧
    (A.iw v ((epsU A.B B' γ k : Eˣ) : E)⁻¹ ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range ∧
      A.iw v (σ ((epsU A.B B' γ k : Eˣ) : E)⁻¹) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range) := by
  have key : ∀ x : E, A.phE v x ∈ (A.pl v).1.adicCompletionIntegers F → A.iw v x ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    intro x hx
    refine (hW v _).2 ?_
    have e : A.eQ v (A.iw v x) = A.phE v x := (A.eQ v).apply_symm_apply _
    rw [e]
    exact hx
  obtain ⟨h1, h2⟩ := epsU_ph S A hp hT halg hb Lc y hy hle B' hB' γ κ b k h v
  have e1 : A.iw v (epsU A.B B' γ k : Eˣ) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := key _ h1
  have e2 : A.iw v ((epsU A.B B' γ k : Eˣ) : E)⁻¹ ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    refine key _ ?_
    rw [← map_inv, Units.coe_map] at h2
    rw [← Units.val_inv_eq_inv_val]
    exact h2
  have hg := gramW_gen S A hW hp hT halg hJ Lc y hy hle B' hB' v
  have g1 : A.iw v (cT (σ : E →+* E) B'.1 * J * B'.1).det ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    rw [RingHom.map_det]
    exact det_mem_sub _ _ fun a b => (hg a b).1
  have g2 : A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1).det)⁻¹ ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    have e : ((cT (σ : E →+* E) B'.1 * J * B'.1).det)⁻¹ = ((cT (σ : E →+* E) B'.1 * J * B'.1)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e, RingHom.map_det]
    exact det_mem_sub _ _ fun a b => (hg a b).2
  have hc := epsU_conj hJ A.B B' γ k hγ hB
  have h0 : ((epsU A.B B' γ k : Eˣ) : E) ≠ 0 := Units.ne_zero _
  have c1 : σ (epsU A.B B' γ k : Eˣ) = ((cT (σ : E →+* E) B'.1 * J * B'.1).det) ^ k * ((epsU A.B B' γ k : Eˣ) : E)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ h0).2 hc
  refine ⟨⟨e1, ?_⟩, e2, ?_⟩
  · rw [c1, map_mul, map_pow]
    exact Subring.mul_mem _ (Subring.pow_mem _ g1 k) e2
  · rw [map_inv₀, c1, mul_inv, inv_inv, ← inv_pow, map_mul, map_pow]
    exact Subring.mul_mem _ (Subring.pow_mem _ g2 k) e1

end Gen

theorem zpow_calc {K : Type} [Field K] (a b : K) (c : ℤ) (k : ℕ) :
    (a ^ (-c)) ^ k * ((b⁻¹) ^ (-c)) ^ k = ((b * a⁻¹) ^ k) ^ c := by
  rw [_root_.inv_zpow', neg_neg, _root_.zpow_neg, ← _root_.inv_zpow, ← mul_pow, ← mul_zpow, mul_comm a⁻¹ b, ← zpow_natCast, ← _root_.zpow_mul,
    mul_comm c, _root_.zpow_mul, zpow_natCast]

variable {D : D7}

theorem intW_of_pow (w : D.what₂.places.Pl) (r : D.what₂.LL) (k : ℕ) (hk : 0 < k) (h1 : r ^ k ∈ intW D.what₂.places w)
    (h2 : (r ^ k)⁻¹ ∈ intW D.what₂.places w) : r ∈ intW D.what₂.places w ∧ r⁻¹ ∈ intW D.what₂.places w := by
  by_cases hr0 : r = 0
  · subst hr0
    exact ⟨Subring.zero_mem _, by rw [_root_.inv_zero]; exact Subring.zero_mem _⟩
  have hd : r ∈ intW D.what₂.places w ∨ r⁻¹ ∈ intW D.what₂.places w := by
    by_contra hcon
    rw [not_or] at hcon
    have a1 : D.what₂.places.val w r < 0 := not_le.1 hcon.1
    have a2 : D.what₂.places.val w r⁻¹ < 0 := not_le.1 hcon.2
    have a3 : D.what₂.places.val w r + D.what₂.places.val w r⁻¹ < 0 := Left.add_neg_of_neg_of_nonpos a1 a2.le
    rw [← AddValuation.map_mul, mul_inv_cancel₀ hr0, AddValuation.map_one] at a3
    exact lt_irrefl _ a3
  have e1 : r⁻¹ = r ^ (k - 1) * (r ^ k)⁻¹ := by
    have : r ^ k = r ^ (k - 1) * r := pow_sub_one_mul hk.ne' r |>.symm
    rw [this, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr0), one_mul]
  have e2 : r = (r⁻¹) ^ (k - 1) * r ^ k := by
    have : r ^ k = r ^ (k - 1) * r := pow_sub_one_mul hk.ne' r |>.symm
    rw [this, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hr0), one_mul]
  rcases hd with h | h
  · exact ⟨h, by rw [e1]; exact Subring.mul_mem _ (Subring.pow_mem _ h _) h2⟩
  · exact ⟨by rw [e2]; exact Subring.mul_mem _ (Subring.pow_mem _ h _) h1, h⟩

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

set_option maxHeartbeats 4000000 in

theorem exists_pow (S : StepIn M i hi G) (β : S.Ch) (cl : {c // S.chOf c = β}) :
    ∃ (b k : ℕ), 0 < k ∧ ∃ (g κ : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ∧
      g.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ ∧ κ.1 ∈ (S.K β).lev.U ∧
      (S.K β).y cl ^ (b + k) = g * (S.K β).y cl ^ b * κ := by
  have hfin : Finite (Cls (S.K β).lev) := Finite.of_surjective _ (S.K β).y_bij.2
  obtain ⟨a, b, hab, he⟩ := @Finite.exists_ne_map_eq_of_infinite ℕ (Cls (S.K β).lev) _ hfin
    (fun n : ℕ => (Quotient.mk'' ((S.K β).y cl ^ n) : Cls (S.K β).lev))
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm he.symm (by omega)
  obtain ⟨g, hg, κ, hκ, e⟩ := (DoubleCoset.eq _ _ ((S.K β).y cl ^ a) ((S.K β).y cl ^ b)).1 he
  obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_subgroupOf.1 hg
  refine ⟨a, b - a, by omega, g, κ, γ, hγ, hγe.symm, Subgroup.mem_subgroupOf.1 hκ, ?_⟩
  rw [show a + (b - a) = b by omega]
  exact e

set_option maxHeartbeats 4000000 in

theorem twUnit_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) (β : S.Ch) (H : S.Core e β)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (L : LatIn S w β) : S.TwUnit w β := by
  intro cl B' hB'
  have hpw := L.resChar
  subst hpw
  obtain ⟨b, k, hk, g, κ, γ, hγ, hg, hκ, hpow⟩ := exists_pow S β cl
  have hσσ : ∀ x : D.host.E, sigD D (sigD D x) = x := fun x => by
    rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.host_conj_involutive]
  have hpow' : ((S.K β).y cl).1 ^ (b + k) =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y cl).1 ^ b * (⟨κ.1, hκ⟩ : (S.K β).lev.U).1 := by
    have := congrArg Subtype.val hpow
    rw [← hg]
    exact this
  have hiw := epsU_iw (S.K β).lev (S.loc β) H.int L.prime L.siteGood_prime_torsion L.alg L.base (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) H.std
    (S.lat cl.1) ((S.K β).y cl) ((S.K β).y_lat cl) (le_dual_chart (S.K β) cl) B' hB' γ hγ ⟨κ.1, hκ⟩ b k hpow'
  set ε : D.host.E := ((epsU (S.loc β).B B' γ k : D.host.Eˣ) : D.host.E) with hε

  have hint : ∀ x : D.host.E, (∀ v, (S.loc β).iw v x ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range ∧
      (S.loc β).iw v (sigD D x) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range) → ∀ τ, tEL D τ x ∈ intW D.what₂.places w := by
    intro x hx τ
    obtain ⟨⟨v, s⟩, rfl⟩ := S.pos.surjective τ
    rw [hR0]
    by_cases hs : Even s.val
    · have h1 := H.pos_emb v s x
      rw [if_pos hs] at h1
      rw [h1]
      exact rho_int v s.val _ (hx v).1
    · have h1 := H.pos_emb v s (sigD D x)
      rw [if_neg hs, hσσ] at h1
      rw [h1]
      exact rho_int v s.val _ (hx v).2
  have i1 : ∀ τ, tEL D τ ε ∈ intW D.what₂.places w := hint ε fun v => (hiw v).1
  have i2 : ∀ τ, (tEL D τ ε)⁻¹ ∈ intW D.what₂.places w := fun τ => by
    rw [← map_inv₀]
    exact hint ε⁻¹ (fun v => (hiw v).2) τ
  have i3 : ∀ τ, D.what₂.embLL (tEL D τ ε) ∈ unitsW D w := fun τ => ⟨_, i1 τ, i2 τ, rfl⟩

  obtain ⟨rc, hrc⟩ := H.chRat cl
  set r : D.what₂.LL := (∏ τ, (tEL D τ (S.loc β).B.1.det) ^ (-(cTw D i))) * rc *
    ∏ τ, (tEL D τ ((B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1.det)) ^ (-(cTw D i)) with hr
  have hrs : D.what₂.embLL r = S.sTw β cl B' := by
    rw [hr, map_mul, map_mul, map_prod, map_prod, hrc]
    unfold StepIn.sTw StepIn.kTw
    congr 1
    · congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, tEL_emb]
    · refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, tEL_emb]
      congr 1
      exact RingHom.map_det (embT D τ) _

  have hch : (((S.tw β).ch ((S.K β).y cl) : ℂˣ) : ℂ) ^ k * ∏ τ, (embT D τ γ.1.det) ^ (cTw D i) = 1 := by
    have h1 := congrArg (S.tw β).ch hpow
    rw [map_mul, map_mul, map_pow, map_pow, (S.tw β).ch_U κ hκ, mul_one, pow_add, mul_comm] at h1
    have h2 : (S.tw β).ch ((S.K β).y cl) ^ k = (S.tw β).ch g := mul_right_cancel h1
    have h3 := (S.tw β).ch_rat γ hγ g hg
    rw [← h2, Units.val_pow_eq_pow_val] at h3
    exact h3
  have hdet : ((B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1.det) = (B'.1.det)⁻¹ := by
    have := congrArg Units.val (map_inv Matrix.GeneralLinearGroup.det B')
    rw [Units.val_inv_eq_inv_val] at this
    exact this
  have hpw : D.what₂.embLL (r ^ k) = ∏ τ, (D.what₂.embLL (tEL D τ ε)) ^ (cTw D i) := by
    have hP0 : (∏ τ, (embT D τ γ.1.det) ^ (cTw D i)) ≠ 0 := right_ne_zero_of_mul_eq_one hch
    have hchk : (((S.tw β).ch ((S.K β).y cl) : ℂˣ) : ℂ) ^ k = (∏ τ, (embT D τ γ.1.det) ^ (cTw D i))⁻¹ :=
      eq_inv_of_mul_eq_one_left hch
    rw [map_pow, hr, map_mul, map_mul, map_prod, map_prod, hrc, mul_pow, mul_pow, hchk, ← Finset.prod_pow, ← Finset.prod_pow,
      mul_right_comm, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, map_zpow₀, tEL_emb, tEL_emb, tEL_emb, hdet, map_inv₀, zpow_calc, hε, epsU_val, map_mul, map_pow, map_mul, map_inv₀,
      map_inv₀, mul_zpow, _root_.inv_zpow]
  have hU : D.what₂.embLL (r ^ k) ∈ unitsW D w := by
    rw [hpw]
    refine Submonoid.prod_mem _ fun τ _ => ?_
    rcases Int.eq_nat_or_neg (cTw D i) with ⟨m, hm | hm⟩
    · rw [hm, zpow_natCast]
      exact Submonoid.pow_mem _ (i3 τ) m
    · rw [hm, _root_.zpow_neg, zpow_natCast]
      exact unitsW_inv (Submonoid.pow_mem _ (i3 τ) m)
  obtain ⟨r', hr1, hr2, hr3⟩ := hU
  have hrr : r' = r ^ k := D.what₂.embLL.injective hr3
  rw [hrr] at hr1 hr2
  obtain ⟨a1, a2⟩ := intW_of_pow w r k hk hr1 hr2
  exact ⟨r, a1, a2, hrs⟩

end Formalism.MainNotions.G.ChF

end
