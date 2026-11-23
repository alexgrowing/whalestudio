import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDual
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRational
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MonomialEqSumJet
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExistsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsLocallyConstantToZModPow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespondStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.PtMoments

section Gen

variable {p : ℕ} [Fact p.Prime]

theorem clo_push {H H' I : Type} {G : H → I → ℂ_[p]} {J J' : I → ℂ_[p]} (h : InIntClosure Set.univ G Set.univ J)
    (φ : H → H') {Sup : Set H'} {tab : H' → I → ℂ_[p]} {M : Set I} (hφ : ∀ a, φ a ∈ Sup)
    (ht : ∀ a, ∀ i ∈ M, G a i = tab (φ a) i) (hJ : ∀ i ∈ M, J' i = J i) : InIntClosure Sup tab M J' := by
  classical
  intro F hF ε hε
  obtain ⟨c, -, hc1, hcF⟩ := h F (Set.subset_univ _) ε hε
  refine ⟨c.mapDomain φ, ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finset.mem_coe.1 hx))
    exact hφ a
  · rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    exacts [hc1 a, by simp]
  · rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring), hJ m (hF hm)]
    simpa only [ht _ m (hF hm)] using hcF m hm

theorem continuous_toZMod_comp {Y : Type} [TopologicalSpace Y] (f : ZMod p → Y) :
    Continuous fun a : ℤ_[p] => f (PadicInt.toZMod a) := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun a => ?_)
  filter_upwards [Metric.ball_mem_nhds a one_pos] with x hx
  congr 1
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  simpa [dist_eq_norm] using hx

theorem exists_cont {r : ℕ} (f : (Fin r → ℕ) → ℂ_[p]) (hf : ∀ a c : Fin r → ℕ, f (fun i => a i + p * c i) = f a) :
    ∃ g : C(Fin r → ℤ_[p], ℂ_[p]), ∀ a : Fin r → ℕ, g (fun i => (a i : ℤ_[p])) = f a := by
  letI : TopologicalSpace ℕ := ⊥
  haveI : DiscreteTopology ℕ := ⟨rfl⟩
  refine ⟨⟨fun a => f fun i => (PadicInt.toZMod (a i)).val, ?_⟩, fun a => ?_⟩
  · exact (continuous_of_discreteTopology (f := f)).comp
      (continuous_pi fun i => (continuous_toZMod_comp (fun z : ZMod p => z.val)).comp (continuous_apply i))
  · simp only [ContinuousMap.coe_mk, map_natCast, ZMod.val_natCast]
    rw [← hf _ fun i => a i / p]
    simp only [Nat.mod_add_div]

variable (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

theorem lamC_coe (x : TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam (x : ℂ) = lam x := dif_pos x.2

theorem lamC_mul {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  have := lamC_coe lam (⟨x, hx⟩ * ⟨y, hy⟩)
  rw [map_mul, ← lamC_coe, ← lamC_coe] at this
  exact this

theorem emb_mem {E : Type} [Field E] [NumberField E] (σ : E →+* ℂ) (x : E) : σ x ∈ TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)

def lamHom {E : Type} [Field E] [NumberField E] (σ : E →+* ℂ) : E →+* ℂ_[p] :=
  lam.comp (σ.codRestrict TaylorLogMetric.Qbar (emb_mem σ))

theorem lamHom_apply {E : Type} [Field E] [NumberField E] (σ : E →+* ℂ) (x : E) :
    TaylorLogMetric.lamC lam (σ x) = lamHom lam σ x := dif_pos (emb_mem σ x)

theorem norm_int_le {E : Type} [Field E] [NumberField E] (ψ : E →+* ℂ_[p]) (a : 𝓞 E) : ‖ψ (a : E)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (ψ (a : E)) := by convert map_isIntegral_int ψ a.isIntegral_coe using 1; exact Subsingleton.elim _ _
  have h : ψ (a : E) ∈ (NormedField.valuation (K := ℂ_[p])).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_sq_le {E : Type} [Field E] [NumberField E] (ψ : E →+* ℂ_[p]) (x y : 𝓞 E) (h : x * y = (p : 𝓞 E))
    (hc : IsCoprime x y) (hx : ‖ψ (x : E)‖ < 1) : ‖ψ ((x : E) ^ 2)‖ ≤ (p : ℝ) ^ (-(2 * (1 : ℕ) : ℤ)) := by
  obtain ⟨u, v, huv⟩ := hc
  have h1 : ψ u * ψ x + ψ v * ψ y = 1 := by
    have := congrArg (fun z : 𝓞 E => ψ (z : E)) huv
    simpa using this
  have h2 : ψ x * ψ y = p := by
    have := congrArg (fun z : 𝓞 E => ψ (z : E)) h
    simpa using this
  have hy : 1 ≤ ‖ψ y‖ := by
    by_contra hn
    have h3 := IsUltrametricDist.norm_add_le_max (ψ u * ψ x) (ψ v * ψ y)
    rw [h1, norm_one, norm_mul, norm_mul] at h3
    refine absurd h3 (not_le.2 (max_lt ?_ ?_))
    · exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le ψ u) (norm_nonneg _) hx
    · exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le ψ v) (norm_nonneg _) (not_le.1 hn)
  have hp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  have h4 : ‖ψ x‖ ≤ (p : ℝ)⁻¹ := by
    rw [← hp, ← h2, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) hy
  rw [map_pow, norm_pow]
  calc _ ≤ ((p : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    _ = _ := by simp [zpow_ofNat]

theorem continuous_zc : Continuous (TaylorLogMetric.zc (p := p)) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem zc_nat (n : ℕ) : TaylorLogMetric.zc (p := p) (n : ℤ_[p]) = n := by simp [TaylorLogMetric.zc]

theorem wPh_eq {D : D7} (T : TaylorLogMetric.Tor D) {N N' : ℕ} (hp : p ≠ 2) (x : TaylorLogMetric.VC D N N') (n : ℤ) (hn : TaylorLogMetric.qH D T x = n) :
    TaylorLogMetric.wPh D T p x = Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  rw [TaylorLogMetric.wPh, if_neg hp]
  obtain ⟨k, m, h1, h2⟩ := Classical.epsilon_spec (p := fun s : ℂ =>
    ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * TaylorLogMetric.qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m) ⟨_, 0, n, by simp [hn], rfl⟩
  rw [h2]
  have h3 : m = ((p ^ k : ℕ) : ℤ) * n := by
    rw [hn] at h1
    exact_mod_cast h1.symm
  rw [h3, zpow_mul, zpow_natCast, hodd.pow.neg_one_pow, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast; ring

end Gen

section Rat

variable {X : Fields} (A : Amb X) {a b : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

theorem q_eq_coc (x : HomE X.E a b) : Real.sqrt A.d / 2 * (HV A.sc (emb A x) (emb A x)).re = coc A x x := by
  have h := (Heis.calculus X A a b).2.2.1 x x
  rw [coc, h]; ring

theorem alV_eq (x : HomE X.E a b) :
    alV A.d A.sc (emb A x) = Complex.exp ((Real.pi : ℂ) * Complex.I * (coc A x x : ℂ)) := by
  rw [← q_eq_coc]; rfl

theorem coc_nat (n : ℕ) (x y : HomE X.E a b) : coc A ((n : X.E) • x) ((n : X.E) • y) = (n : ℝ) ^ 2 * coc A x y := by
  have h : ∀ z : HomE X.E a b, emb A ((n : X.E) • z) = (n : ℂ) • emb A z := fun z => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact map_nsmul _ _ _
  have h2 : HV A.sc ((n : ℂ) • emb A x) ((n : ℂ) • emb A y) = (((n : ℝ) ^ 2 : ℝ) : ℂ) * HV A.sc (emb A x) (emb A y) := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, map_natCast]
    push_cast; ring
  simp only [coc, imH, altE, h, h2, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  ring

variable (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N')
include hX hδ hL

theorem coc_int {x y : HomE X.E a b} (hx : x ∈ per A N N') (hy : y ∈ per A N N') : ∃ n : ℤ, coc A x y = n :=
  (CocInt.cocycle_integral X A a b N N' hX hδ hL).2.2 x y fun Q =>
    ⟨1, one_ne_zero, by simpa using le_locP Q _ hx, by simpa using le_locP (conjPrime₂ Q) _ hy⟩

theorem al_unit {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) {t : HomE X.E a b} {n : ℕ} (hn : n ≠ 0)
    (ht : (n : X.E) • t ∈ per A N N') :
    alV A.d A.sc (emb A t) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (alV A.d A.sc (emb A t))‖ = 1 := by
  obtain ⟨m, hm⟩ := coc_int A hX hδ hL ht ht
  rw [coc_nat] at hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h : coc A t t = -2 * ((-(m : ℚ) / (2 * (n : ℚ) ^ 2) : ℚ) : ℝ) := by
    push_cast; rw [← hm]; field_simp
  have := (GlobalTheory.T.algebraicNumbers_padicPlaces_facts X.K p A.σ₀ ι).2.2 lam (-(m : ℚ) / (2 * (n : ℚ) ^ 2))
  rw [alV_eq, h]
  rwa [show (Real.pi : ℂ) * Complex.I * ((-2 * ((-(m : ℚ) / (2 * (n : ℚ) ^ 2) : ℚ) : ℝ) : ℝ) : ℂ) =
    -(2 * (Real.pi : ℂ)) * Complex.I * (((-(m : ℚ) / (2 * (n : ℚ) ^ 2) : ℚ) : ℝ) : ℂ) by push_cast; ring]

theorem brk_per {r : X.E} {k : ℕ} {y x w : HomE X.E a b} (hy : (k : X.E) • r • y ∈ per A N N') (hw : w ∈ per A N N') :
    brkE A (r • y) (x + (k : X.E) • w) = brkE A (r • y) x := by
  obtain ⟨c1, c2, -⟩ := CocInt.cocycle_integral X A a b N N' hX hδ hL
  obtain ⟨-, -, -, h4, h5, -⟩ := Heis.calculus X A a b
  obtain ⟨n, hn⟩ := (c2 w).1 hw _ hy
  rw [h5, h5, (h4 _ _ _).2.2.1, (c1 _ _ _).2, star_natCast, hn]
  push_cast
  rw [mul_add, Complex.exp_add]
  have : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (n : ℂ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I (-n)]; congr 1; push_cast; ring
  rw [this, mul_one]

end Rat

section Tr

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
  (cD : D.what₂.Tau → ℂ) {a b : ℕ}

def mat : HomE X.E a b →+ Matrix (Fin b) (Fin a) D.host.E where
  toFun x := fun i j => s.iE (x (Pi.single j 1) i)
  map_zero' := by funext i j; simp
  map_add' x y := by funext i j; exact map_add s.iE _ _

def pu (z : VCx X.Tau a b) : TaylorLogMetric.VC D a b := fun τ => z (s.iT.symm τ)

theorem pu_iT (z : VCx X.Tau a b) : (fun τ => pu s z (s.iT τ)) = z := by funext τ; simp [pu]

theorem mat_sum {r : ℕ} (c : Fin r → ℕ) (β : Fin r → HomE X.E a b) :
    mat s (∑ i, (c i : X.E) • β i) = ∑ i, (c i : D.host.E) • mat s (β i) := by
  simp only [map_sum, Nat.cast_smul_eq_nsmul, map_nsmul]

variable {s} (hs : s.Ok)
include hs

theorem pu_emb (x : HomE X.E a b) :
    pu s (emb (ambOf s B χ cD) x) = δ • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (mat s x) := by
  funext τ i j
  have := hs.1 (s.iT.symm τ) (x (Pi.single j 1) i)
  rw [Equiv.apply_symm_apply] at this
  exact congrArg (δ * ·) this

theorem Hf_pu (z w : VCx X.Tau a b) :
    TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) (pu s z) (pu s w) = HV (ambOf s B χ cD).sc z w := by
  rw [(GlobalTheory.T.fieldIso_lattices_form_taylor_correspond D X s cc δ B χ cD a b hs).2.2.1, pu_iT, pu_iT]

theorem pu_mem {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} {x : HomE X.E a b}
    (hx : x ∈ per (ambOf s B χ cD) N N') :
    pu s (emb (ambOf s B χ cD) x) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
  rw [(GlobalTheory.T.fieldIso_lattices_form_taylor_correspond D X s cc δ B χ cD a b hs).1, pu_iT]
  exact ⟨x, hx, rfl⟩

theorem exists_pt {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hδ : δ ≠ 0) (τ : X.Tau)
    {m : Matrix (Fin b) (Fin a) D.host.E}
    (hm : δ • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) m ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N')) :
    ∃ x ∈ per (ambOf s B χ cD) N N', mat s x = m := by
  rw [(GlobalTheory.T.fieldIso_lattices_form_taylor_correspond D X s cc δ B χ cD a b hs).1] at hm
  obtain ⟨x, hx, h⟩ := hm
  refine ⟨x, hx, ?_⟩
  funext i j
  have h1 : δ * s.σ₀ (X.emb τ (x (Pi.single j 1) i)) = δ * TaylorLogMetric.embT D (s.iT τ) (m i j) := congrFun (congrFun (congrFun h τ) i) j
  rw [hs.1] at h1
  exact (TaylorLogMetric.embT D (s.iT τ)).injective (mul_left_cancel₀ hδ h1)

theorem pu_emb_smul {r : X.E} {κ : D.host.K} (h : (κ : D.host.E) = s.iE r) (x : HomE X.E a b) :
    pu s (emb (ambOf s B χ cD) (r • x)) = D.host.φ₀ (κ : D.host.E) • pu s (emb (ambOf s B χ cD) x) := by
  rw [pu_emb B χ cD hs, pu_emb B χ cD hs]
  funext τ i j
  change δ * TaylorLogMetric.embT D τ (s.iE (r * x (Pi.single j 1) i)) = _ * (δ * TaylorLogMetric.embT D τ (s.iE (x (Pi.single j 1) i)))
  rw [map_mul, map_mul, ← h, GlobalTheory.InducedType.restrict_K D τ κ]
  ring

theorem Wx_Wx {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Y t : HomE X.E a b) (n : ℤ) (hn : coc (ambOf s B χ cD) Y Y = n) :
    Wx (ambOf s B χ cD) Y (Wx (ambOf s B χ cD) t ((ambOf s B χ cD).e a b N N')) = fun z =>
      alV (ambOf s B χ cD).d (ambOf s B χ cD).sc (emb (ambOf s B χ cD) t) *
        TaylorLogMetric.Wop D (TaylorLogMetric.tor0 D cc δ) p (pu s (emb (ambOf s B χ cD) Y))
          (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (pu s (emb (ambOf s B χ cD) t)) (B.eNat χ a b (s.lat N) (s.lat N'))) (pu s z) := by
  funext z
  have h1 : TaylorLogMetric.wPh D (TaylorLogMetric.tor0 D cc δ) p (pu s (emb (ambOf s B χ cD) Y)) =
      alV (ambOf s B χ cD).d (ambOf s B χ cD).sc (emb (ambOf s B χ cD) Y) := by
    rw [wPh_eq _ hp _ n, alV_eq, hn]
    rw [TaylorLogMetric.qH, Hf_pu B χ cD hs, ← hn, ← q_eq_coc]; rfl
  have h2 : ∀ z w : VCx X.Tau a b, pu s z + pu s w = pu s (z + w) := fun _ _ => rfl
  have h3 : ∀ z : VCx X.Tau a b, (ambOf s B χ cD).e a b N N' z = B.eNat χ a b (s.lat N) (s.lat N') (pu s z) := fun _ => rfl
  simp only [TaylorLogMetric.Wop, TaylorLogMetric.U, Wx, opU, h1, h2, h3, Hf_pu B χ cD hs]
  ring

theorem jetC_pu (c : ℂ) (hc : c ≠ 0) (G : TaylorLogMetric.VC D a b → ℂ) (F : VCx X.Tau a b → ℂ) (hF : ∀ k : ℕ, ContDiff ℂ k F)
    (h : F = fun z => c * G (pu s z)) (m : DVar X.Tau a b →₀ ℕ) :
    jetC (ambOf s B χ cD).cD F m = c * ((m.prod fun k n => cD (s.iT k.1) ^ n) *
      ((m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)))) := by
  have hG : G = fun w => c⁻¹ * F fun τ => w (s.iT τ) := by
    funext w
    have : pu s (fun τ => w (s.iT τ)) = w := by funext τ; simp [pu]
    rw [h]; simp only [this]; field_simp
  have hG' : ∀ k : ℕ, ContDiff ℂ k G := fun k => by
    rw [hG]
    exact contDiff_const.mul ((hF k).comp (contDiff_pi.2 fun τ => contDiff_apply ℂ _ (s.iT τ)))
  have hG2 : ∀ k : ℕ, ContDiff ℂ k fun z : VCx X.Tau a b => G (pu s z) := fun k =>
    (hG' k).comp (contDiff_pi.2 fun τ => contDiff_apply ℂ _ (s.iT.symm τ))
  have h1 := (Heis.calculus X (ambOf s B χ cD) a b).2.2.2.2.2.2.2 Unit {()} (fun _ => c) (fun _ z => G (pu s z))
    (fun _ _ => hG2) m
  simp only [Finset.sum_singleton] at h1
  rw [h, h1, jetC, ← (GlobalTheory.T.fieldIso_lattices_form_taylor_correspond D X s cc δ B χ cD a b hs).2.2.2 G hG' m]
  rfl

end Tr

section Main

variable {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

theorem pairN_nat {D : D7} {N N' r : ℕ} (Ω : ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (y : Matrix (Fin N') (Fin N) D.host.E) (c : Fin r → ℕ) :
    TaylorLogMetric.pairN D lam Ω b y (fun i => (c i : ℤ_[p])) =
      Ω⁻¹ * TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D y (∑ i, (c i : D.host.E) • b i) : D.host.K) : D.host.E)) := by
  let f : Matrix (Fin N') (Fin N) D.host.E →+ D.host.K := AddMonoidHom.mk' (TaylorLogMetric.hYY D y) fun u v => by
    simp only [TaylorLogMetric.hYY, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]
  have h : TaylorLogMetric.hYY D y (∑ i, (c i : D.host.E) • b i) = ∑ i, (c i : D.host.K) * TaylorLogMetric.hYY D y (b i) := by
    change f _ = ∑ i, (c i : D.host.K) * f (b i)
    simp only [map_sum, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
  rw [TaylorLogMetric.pairN, h]
  simp only [lamHom_apply, zc_nat]
  push_cast
  simp only [map_sum, map_mul, map_natCast]

theorem continuous_pairN {D : D7} {N N' r : ℕ} (Ω : ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (y : Matrix (Fin N') (Fin N) D.host.E) : Continuous (TaylorLogMetric.pairN D lam Ω b y) :=
  continuous_const.mul (continuous_finset_sum _ fun i _ => (continuous_zc.comp (continuous_apply i)).mul continuous_const)

theorem lamC_prod {κ : Type} (m : κ →₀ ℕ) (f : κ → ℂ) (hf : ∀ k, f k ∈ TaylorLogMetric.Qbar) :
    (m.prod fun k n => f k ^ n) ∈ TaylorLogMetric.Qbar ∧
      TaylorLogMetric.lamC lam (m.prod fun k n => f k ^ n) = m.prod fun k n => TaylorLogMetric.lamC lam (f k) ^ n := by
  have h : (m.prod fun k n => f k ^ n) = ((m.prod fun k n => (⟨f k, hf k⟩ : TaylorLogMetric.Qbar) ^ n : TaylorLogMetric.Qbar) : ℂ) := by
    simp [Finsupp.prod]
  refine ⟨h ▸ Subtype.property _, ?_⟩
  rw [h, lamC_coe, map_finsuppProd]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [map_pow, ← lamC_coe]

theorem lamC_fact {κ : Type} (m : κ →₀ ℕ) :
    (m.prod fun _ n => (n.factorial : ℂ)) ∈ TaylorLogMetric.Qbar ∧
      TaylorLogMetric.lamC lam (m.prod fun _ n => (n.factorial : ℂ)) = m.prod fun _ n => (n.factorial : ℂ_[p]) := by
  have h : (m.prod fun _ n => (n.factorial : ℂ)) = ((m.prod fun _ n => (n.factorial : TaylorLogMetric.Qbar) : TaylorLogMetric.Qbar) : ℂ) := by
    simp [Finsupp.prod]
  refine ⟨h ▸ Subtype.property _, ?_⟩
  rw [h, lamC_coe, map_finsuppProd]
  simp only [map_natCast]

variable {D : D7} {X : Fields} {s : Seam D X} {a b : ℕ}

theorem ren_inj : Function.Injective fun v : DVar X.Tau a b => (s.iT v.1, v.2) := fun v w h => by
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact Prod.ext (s.iT.injective h1) h2

theorem ptTab_eq (hs : s.Ok) {ι : X.K →+* ℂ_[p]} (hι : ∀ k, TaylorLogMetric.lamC lam (s.σ₀ k) = ι k) (c : X.Tau → ℂ_[p]) (Ω : ℂ_[p])
    (x : HomE X.E a b) (m : DVar X.Tau a b →₀ ℕ) :
    ptTab ι (fun τ => c τ / Ω) x m = (m.prod fun k n => c k.1 ^ n) *
      (Ω⁻¹ ^ (m.mapDomain fun v => (s.iT v.1, v.2)).degree *
        (m.mapDomain fun v => (s.iT v.1, v.2)).prod fun v n =>
          TaylorLogMetric.lamC lam (TaylorLogMetric.embT D v.1 (D.host.conj (mat s x v.2.1 v.2.2))) ^ n) := by
  have h : Ω⁻¹ ^ (m.mapDomain fun v => (s.iT v.1, v.2)).degree =
      (m.mapDomain fun v => (s.iT v.1, v.2)).prod fun _ n => Ω⁻¹ ^ n := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum]; rfl
  rw [h, Finsupp.prod_mapDomain_index_inj ren_inj, Finsupp.prod_mapDomain_index_inj ren_inj, ptTab, ← Finsupp.prod_mul,
    ← Finsupp.prod_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [adj_single, ← hι, hs.1, hs.2, ← mul_pow, div_eq_mul_inv, mul_assoc]
  rfl

theorem ptMom : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (Ω : ℂ_[p]) (ϖ : 𝓞 X.E) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → p ≠ 2 → Nat.Coprime (Ideal.absNorm cc) p → (∀ k, TaylorLogMetric.lamC lam (s.σ₀ k) = ι k) → (∀ τ, cD τ ∈ TaylorLogMetric.Qbar) → (ϖ : X.E) ∈ X.Kq → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → (∀ τ, ‖ι (X.emb τ (ϖ : X.E))‖ < 1) → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ → (ambOf s B χ cD).ESmooth a b → MomentsAt D cc δ (B.eNat χ) lam Ω → PtMom (ambOf s B χ cD) a b lam ι (fun τ => TaylorLogMetric.lamC lam (cD (s.iT τ)) / Ω) (star (ϖ : X.E) / (ϖ : X.E)) := by
  intro D X s cc δ B χ cD p _ lam ι Ω ϖ a b hX hs _ hp2 hcc hι hcD hϖ hN hco hsm ha hb hLa hE hM N N' hN1 hN2 t ⟨n, hn, ht⟩
  have hp : p.Prime := Fact.out
  obtain ⟨hδ, ⟨τ₀⟩, -, -, -, hLa⟩ := hLa
  have hL := (hLa N N' hN1 hN2).2
  have hadm := (GlobalTheory.T.fieldIso_lattices_form_taylor_correspond D X s cc δ B χ cD a b hs).2.1 N N' ha hb hN1 hN2
  have hn0 : n ≠ 0 := by rintro rfl; exact hp.ne_one (by simpa using hn)
  obtain ⟨N₀, hN₀, hM⟩ := hM a b _ _ hadm (pu s (emb (ambOf s B χ cD) t)) ⟨n, Nat.pos_of_ne_zero hn0, hn, by
    have := pu_mem B χ cD hs ht
    rwa [Nat.cast_smul_eq_nsmul, emb, map_nsmul] at this⟩
  obtain ⟨r, bb, hbb⟩ := GlobalTheory.T.admissible_lattice_basis_exists D cc δ p a b _ _ hp hcc hadm
  obtain ⟨μ, hμ, hM⟩ := hM r bb hbb
  choose β hβ hβm using fun i => exists_pt B χ cD hs hδ τ₀ (hbb.2 i)
  obtain ⟨hα, hα1⟩ := al_unit (ambOf s B χ cD) hX hδ hL lam ι hn0 ht
  set α := alV (ambOf s B χ cD).d (ambOf s B χ cD).sc (emb (ambOf s B χ cD) t) with hαd
  have hα0 : α ≠ 0 := Complex.exp_ne_zero _
  have hcj : ((X.conjO ϖ : 𝓞 X.E) : X.E) = star (ϖ : X.E) := rfl
  have hNE : (ϖ : X.E) * star (ϖ : X.E) = p := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) hN
    simpa [← hcj] using this
  have hpE : (p : X.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hϖ0 : (ϖ : X.E) ≠ 0 := left_ne_zero_of_mul (hNE ▸ hpE)
  have hϖ1 : star (ϖ : X.E) ≠ 0 := right_ne_zero_of_mul (hNE ▸ hpE)
  set v : X.E := (N₀ : X.E) * (star (ϖ : X.E) / (ϖ : X.E)) with hv
  have hpv : (p : X.E) * v = ((N₀ * X.conjO ϖ ^ 2 : 𝓞 X.E) : X.E) := by
    push_cast
    change _ = _ * star (ϖ : X.E) ^ 2
    rw [hv, ← hNE]; field_simp
  have hvv : star v * v = ((N₀ ^ 2 : 𝓞 X.E) : X.E) := by
    push_cast
    rw [hv, star_mul, star_div₀, star_star, star_natCast]; field_simp
  obtain ⟨κ, hκ⟩ := (SplitK.splitk D X s (X.conjO ϖ) p hs fun τ τ' => by rw [hcj, hX.emb_star, hX.emb_star, hϖ τ τ']).1
  obtain ⟨κ', hκ'⟩ := (SplitK.splitk D X s ϖ p hs hϖ).1
  have hgood : ∀ y ∈ per (ambOf s B χ cD) N N', pu s (emb (ambOf s B χ cD) (v • y)) ∈
      goodLifts D (TaylorLogMetric.tor0 D cc δ) lam N₀ 1 (s.lat N) (s.lat N') := fun y hy => by
    refine AddSubgroup.subset_closure ⟨κ ^ 2, ?_, _, pu_mem B χ cD hs hy, ?_⟩
    · have h1 : D.host.conj (((κ ^ 2 : 𝓞 D.host.K) : D.host.K) : D.host.E) = ((((κ' : D.host.K)) ^ 2 : D.host.K) : D.host.E) := by
        push_cast
        rw [map_pow, hκ, hκ', ← hs.2, hcj, star_star]
      rw [h1, ← GlobalTheory.InducedType.restrict_K D (s.iT τ₀)]
      push_cast
      rw [hκ', ← map_pow, ← hs.1, hι]
      exact norm_sq_le (ι.comp (X.emb τ₀)) ϖ _ hN hco (hsm τ₀)
    · rw [pu_emb_smul B χ cD hs (κ := (κ : D.host.K) ^ 2 * N₀ / p)]
      · push_cast
        simp
      · push_cast
        rw [hκ, hcj, ← map_natCast s.iE N₀, ← map_natCast s.iE p, ← map_pow, ← map_mul, ← map_div₀, hv, ← hNE]
        congr 1; field_simp
  have key : ∀ k : HomE X.E a b × (DVar X.Tau a b →₀ ℕ), ∃ g : C(Fin r → ℤ_[p], ℂ_[p]), k.1 ∈ per (ambOf s B χ cD) N N' →
      jetC (ambOf s B χ cD).cD (Wx (ambOf s B χ cD) (v • k.1) (Wx (ambOf s B χ cD) t ((ambOf s B χ cD).e a b N N'))) k.2
        ∈ TaylorLogMetric.Qbar ∧
      TaylorLogMetric.lamC lam (jetC (ambOf s B χ cD).cD
        (Wx (ambOf s B χ cD) (v • k.1) (Wx (ambOf s B χ cD) t ((ambOf s B χ cD).e a b N N'))) k.2) = TaylorLogMetric.lamC lam α * μ g ∧
      ∀ c : Fin r → ℕ, g (fun i => (c i : ℤ_[p])) =
        TaylorLogMetric.lamC lam (brkE (ambOf s B χ cD) (v • k.1) (∑ i, (c i : X.E) • β i)) *
          ptTab ι (fun τ => TaylorLogMetric.lamC lam (cD (s.iT τ)) / Ω) (∑ i, (c i : X.E) • β i) k.2 := by
    rintro ⟨y, m⟩
    by_cases hy : y ∈ per (ambOf s B χ cD) N N'
    swap
    · exact ⟨0, fun h => absurd h hy⟩
    obtain ⟨hC, hJ⟩ := hM 1 _ (hgood y hy)
    obtain ⟨q, hq⟩ : ∃ q : ℤ, coc (ambOf s B χ cD) (v • y) (v • y) = q := by
      rw [((CocInt.cocycle_integral X _ a b N N' hX hδ hL).1 _ _ _).1, smul_smul, hvv]
      exact coc_int _ hX hδ hL hy (Submodule.smul_mem _ _ hy)
    have h7 := (Heis.calculus X (ambOf s B χ cD) a b).2.2.2.2.2.2.1
    have hjet := jetC_pu B χ cD hs α hα0 _ _ (h7 _ _ (h7 _ _ (hE N N' hN1 hN2))) (Wx_Wx B χ cD hs hp2 N N' (v • y) t q hq) m
    obtain ⟨g₀, hg₀⟩ := exists_cont (p := p)
      (fun c : Fin r → ℕ => TaylorLogMetric.lamC lam (brkE (ambOf s B χ cD) (v • y) (∑ i, (c i : X.E) • β i))) fun c c' => by
        have h1 : ∑ i, ((c i + p * c' i : ℕ) : X.E) • β i = ∑ i, (c i : X.E) • β i + (p : X.E) • ∑ i, (c' i : X.E) • β i := by
          simp only [Nat.cast_add, Nat.cast_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
        rw [h1, brk_per _ hX hδ hL]
        · rw [smul_smul, hpv]; exact Submodule.smul_mem _ _ hy
        · exact Submodule.sum_mem _ fun i _ => by
            rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hβ i) _
    obtain ⟨l, γ, yy, hγ1, hγ2⟩ := GlobalTheory.MonoJet.monomial_eq_sum_jet D p a b lam (m.mapDomain fun v => (s.iT v.1, v.2))
    let G : Fin l → C(Fin r → ℤ_[p], ℂ_[p]) := fun i =>
      g₀ * ⟨fun c => ∏ j, TaylorLogMetric.pairN D lam Ω bb (yy i j) c, continuous_finset_prod _ fun j _ => continuous_pairN lam Ω bb _⟩
    have hG := fun i => hJ _ (yy i) (G i) fun c => by
      change g₀ _ * _ = _
      rw [hg₀]
      congr 2
      rw [← funext hβm, ← mat_sum, ← pu_emb B χ cD hs, TaylorLogMetric.kap, Hf_pu B χ cD hs, brkE, brk, altE, neg_mul]
    obtain ⟨c1, c2⟩ := lamC_prod lam m (fun k => cD (s.iT k.1)) fun k => hcD _
    obtain ⟨f1, f2⟩ := lamC_fact lam m
    refine ⟨(m.prod fun k n => TaylorLogMetric.lamC lam (cD (s.iT k.1)) ^ n) • ∑ i, γ i • G i, fun _ => ⟨?_, ?_, fun c => ?_⟩⟩
    · rw [hjet]; exact mul_mem hα (mul_mem c1 (mul_mem f1 (hC _)))
    · rw [hjet, lamC_mul lam hα (mul_mem c1 (mul_mem f1 (hC _))), lamC_mul lam c1 (mul_mem f1 (hC _)), lamC_mul lam f1 (hC _),
        c2, f2]
      simp only [map_smul, map_sum, smul_eq_mul, ← hG, ← hγ1, Finsupp.prod_mapDomain_index_inj ren_inj]
      rfl
    · rw [ptTab_eq lam hs hι, hγ2, mat_sum]
      simp only [G, hβm, ContinuousMap.smul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.coe_mk, hg₀,
        pairN_nat, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  choose g hg using key
  refine ⟨N₀, hN₀, fun y hy m => (hg (y, m) hy).1, ?_⟩
  refine clo_congr (clo_mul (J := fun k => μ (g k)) ?_ (TaylorLogMetric.lamC lam α) hα1.le) subset_rfl subset_rfl fun k hk => (hg k hk).2.1
  refine clo_push (Riemann.riemann_sums p r μ _ g hμ) (fun c => ∑ i, (c i : X.E) • β i) (fun c => ?_)
    (fun c k hk => (hg k hk).2.2 c) fun _ _ => rfl
  exact Submodule.sum_mem _ fun i _ => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hβ i) _

end Main

end GlobalTheory.MomT.PtMoments
