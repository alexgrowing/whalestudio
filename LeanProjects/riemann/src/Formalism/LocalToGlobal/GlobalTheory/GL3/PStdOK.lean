import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO

open Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta)

theorem selfDual_img {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W)
    (g : V ≃ₗ[ℂ] W) (hg : IsIsom H H' (g : V →ₗ[ℂ] W)) (Λ : AddSubgroup V) (h : IsSelfDual H Λ) :
    IsSelfDual H' (imgLat (g : V →ₗ[ℂ] W) Λ) := by
  apply le_antisymm
  · intro x hx
    refine ⟨g.symm x, ?_, g.apply_symm_apply x⟩
    rw [← h]
    intro y hy
    obtain ⟨m, hm⟩ := hx (g y) ⟨y, hy, rfl⟩
    refine ⟨m, ?_⟩
    rw [← hm]
    have := hg (g.symm x) y
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    simp only [altE, this]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← h] at hx
    obtain ⟨m, hm⟩ := hx y hy
    refine ⟨m, ?_⟩
    rw [← hm]
    have := hg x y
    simp only [altE]
    exact congrArg Complex.im this

theorem exists_nat_mul (F : Type*) [Field F] [NumberField F] (T : Finset F) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ T, IsIntegral ℤ ((m : F) * x) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) T
  have hn : Ideal.absNorm (Ideal.span {(b : 𝓞 F)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact nonZeroDivisors.ne_zero b.2
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {(b : 𝓞 F)}))
  refine ⟨_, Nat.pos_of_ne_zero hn, fun x hx => ?_⟩
  obtain ⟨r, hr⟩ := hb x hx
  have : ((Ideal.absNorm (Ideal.span {(b : 𝓞 F)}) : ℕ) : F) * x = ((t * r : 𝓞 F) : F) := by
    rw [Algebra.smul_def] at hr
    have h1 : ((Ideal.absNorm (Ideal.span {(b : 𝓞 F)}) : ℕ) : F) = (t : F) * ((b : 𝓞 F) : F) := by
      have := congrArg (fun y : 𝓞 F => (y : F)) ht
      simpa using this.symm
    rw [h1, mul_assoc]
    push_cast
    exact congrArg ((t : F) * ·) hr.symm
  rw [this]; exact RingOfIntegers.isIntegral_coe _

theorem denom (E K : Type*) [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type*} [Fintype ι] (f : ι → E →+ K) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, ∀ x : 𝓞 E, IsIntegral ℤ ((m : K) * f i (x : E)) := by
  let bs := RingOfIntegers.basis E
  obtain ⟨m, hm, h⟩ := exists_nat_mul K
    (Finset.univ.image fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => f p.1 ((bs p.2 : 𝓞 E) : E))
  refine ⟨m, hm, fun i x => ?_⟩
  have hx : (x : E) = ∑ j, (bs.repr x j) • ((bs j : 𝓞 E) : E) := by
    conv_lhs => rw [← bs.sum_repr x]
    simp
  rw [hx, map_sum, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [map_zsmul, mul_smul_comm]
  exact (h _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)).zsmul _

theorem fg_of_nsmul_le {ι : Type} (M M' : AddSubgroup (ι → ℂ)) [AddGroup.FG M'] (N : ℕ) (hN : 0 < N)
    (h : ∀ x ∈ M, N • x ∈ M') : AddGroup.FG M := by
  rw [← Module.Finite.iff_addGroup_fg]
  have : Module.Finite ℤ M' := Module.Finite.iff_addGroup_fg.2 inferInstance
  let f : M →+ M' :=
    { toFun := fun x => ⟨N • x.1, h x.1 x.2⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  refine Module.Finite.of_injective f.toIntLinearMap ?_
  intro x y hxy
  have h1 : N • x.1 = N • y.1 := congrArg (fun z : M' => z.1) hxy
  ext i
  have h2 := congrFun h1 i
  simp only [Pi.smul_apply, nsmul_eq_mul] at h2
  exact mul_left_cancel₀ (by exact_mod_cast hN.ne') h2

def e4 : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

def reix (n : Type) : (n → Fin 2 → Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun u := fun w => u w.2 (e4.symm w.1).1 (e4.symm w.1).2
  invFun z := fun τ i j => z (e4 (i, j), τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv u := by funext τ i j; simp
  right_inv z := by funext ⟨a, τ⟩; simp

theorem reix_pow {n : Type} [Fintype n] (Λ : AddSubgroup (n → ℂ)) :
    imgLat (reix n : (n → Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (powLat Λ 2 2) = pow4 Λ := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩ a
    exact hu (e4.symm a).1 (e4.symm a).2
  · intro hz
    exact ⟨(reix n).symm z, fun i j => hz (e4 (i, j)), (reix n).apply_symm_apply z⟩

theorem reix_isom (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] :
    IsIsom (formV (Formalism.L2.Th1.F.area L) n 2 2) (matH (blk4 (hOne L n)))
      (reix n : (n → Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
  intro x y
  rw [blockFourfold_hOne_eq_hOne, matH_hOne, formV_apply]
  congr 1
  show ∑ w : Fin 4 × n, x w.2 (e4.symm w.1).1 (e4.symm w.1).2 * conj (y w.2 (e4.symm w.1).1 (e4.symm w.1).2)
    = ∑ τ, ∑ i, ∑ j, x τ i j * conj (y τ i j)
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have := Equiv.sum_comp e4.symm (fun p : Fin 2 × Fin 2 => x τ p.1 p.2 * conj (y τ p.1 p.2))
  rw [Fintype.sum_prod_type] at this
  exact this

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem lam_mul (o : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ TaylorLogMetric.lamOf D cc δ) :
    D.host.φ₀ (((o : D.host.K) : D.host.E)) * w ∈ TaylorLogMetric.lamOf D cc δ := by
  obtain ⟨c, hc, rfl⟩ := FL.lam_mem D cc δ w hw
  refine AddSubgroup.subset_closure ⟨o * c, cc.mul_mem_left _ hc, ?_⟩
  have : (((o * c : 𝓞 D.host.K) : D.host.K) : D.host.E)
      = ((o : D.host.K) : D.host.E) * ((c : D.host.K) : D.host.E) := by push_cast; rfl
  rw [this, map_mul]; ring

theorem theta_eq (D : D7) : cmTheta 1 D.host.d = D.host.φ₀ (((AR.om D : D.host.K) : D.host.E)) := by
  have := AR.ph_om D
  rw [show D.host.φ₀ (((AR.om D : D.host.K) : D.host.E)) = _ from this]
  simp [cmTheta]

theorem lam_theta {w : ℂ} (hw : w ∈ TaylorLogMetric.lamOf D cc δ) : cmTheta 1 D.host.d * w ∈ TaylorLogMetric.lamOf D cc δ := by
  rw [theta_eq]; exact lam_mul _ hw

theorem lamMM_smul (o : 𝓞 D.host.K) {v : D.what₂.Tau → ℂ} (hv : v ∈ lamMM D (TaylorLogMetric.lamOf D cc δ)) :
    D.host.φ₀ (((o : D.host.K) : D.host.E)) • v ∈ lamMM D (TaylorLogMetric.lamOf D cc δ) := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, a, ha, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨_, lam_mul o hw, a, ha, by funext τ; simp [mul_assoc]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem gen_mem {Λ : AddSubgroup ℂ} {w : ℂ} (hw : w ∈ Λ) {y : Fin 4 → D.host.E} (hy : ∀ a, y a ∈ D.host.AA0) :
    w • emb4 D y ∈ pow4 (lamMM D Λ) :=
  fun a => AddSubgroup.subset_closure ⟨w, hw, y a, hy a, rfl⟩

def put4 (n : Type) (a : Fin 4) : (n → ℂ) →+ (Fin 4 × n → ℂ) where
  toFun v := fun w => if w.1 = a then v w.2 else 0
  map_zero' := by funext w; simp
  map_add' := by intro x y; funext w; by_cases h : w.1 = a <;> simp [h]

theorem fourth_power_le_closure_embeddings (Λ : AddSubgroup ℂ) : pow4 (lamMM D Λ) ≤
    AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ y : Fin 4 → D.host.E, (∀ a, y a ∈ D.host.AA0) ∧ z = w • emb4 D y} := by
  intro z hz
  have key : ∀ a : Fin 4, lamMM D Λ ≤ (AddSubgroup.closure
      {z | ∃ w ∈ Λ, ∃ y : Fin 4 → D.host.E, (∀ a, y a ∈ D.host.AA0) ∧ z = w • emb4 D y}).comap
        (put4 D.what₂.Tau a) := by
    intro a
    unfold lamMM
    rw [AddSubgroup.closure_le]
    rintro v ⟨w, hw, a0, ha0, rfl⟩
    refine AddSubgroup.subset_closure ⟨w, hw, Pi.single a a0, ?_, ?_⟩
    · intro a'
      by_cases h : a' = a
      · subst h; rwa [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne h]; exact FractionalIdeal.zero_mem _
    · funext ⟨a', τ⟩
      show (if a' = a then w * TaylorLogMetric.embT D τ a0 else 0) = w * TaylorLogMetric.embT D τ ((Pi.single a a0 : Fin 4 → D.host.E) a')
      by_cases h : a' = a
      · subst h; simp
      · rw [Pi.single_eq_of_ne h]; simp [h]
  have hsum : z = ∑ a, put4 D.what₂.Tau a (slice a z) := by
    funext ⟨a', τ⟩
    simp only [Finset.sum_apply, put4, AddMonoidHom.coe_mk, ZeroHom.coe_mk, slice]
    rw [Finset.sum_eq_single a']
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [hsum]
  exact AddSubgroup.sum_mem _ fun a _ => key a (hz a)

theorem int_mem_inverse_half_different {x : D.host.E} (hx : IsIntegral ℤ x) : x ∈ D.host.AA0 := by
  have h1 := FL.one_mem_inverse_halfDifferent D
  have h2 : ((⟨x, hx⟩ : 𝓞 D.host.E) • (1 : D.host.E)) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
    Submodule.smul_mem _ _ h1
  have e : ((⟨x, hx⟩ : 𝓞 D.host.E) • (1 : D.host.E)) = x := by rw [Algebra.smul_def, mul_one]; rfl
  rw [e] at h2
  exact h2

theorem exists_nat_clearing_order_denominators (D : D7) : ∃ k : ℕ, 0 < k ∧ ∀ a ∈ D.host.AA0, IsIntegral ℤ ((k : D.host.E) * a) := by
  obtain ⟨k, hk, h⟩ := FL.exists_int_clearing_order_denominators D
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, fun a ha => ?_⟩
  have h1 := h a ha
  rw [Nat.cast_natAbs]
  rcases abs_choice k with e | e <;> rw [e]
  · exact h1
  · push_cast; rw [neg_mul]; exact h1.neg

section B

variable (B : Base D cc δ)

theorem mem_iff (x : ℂ) : x ∈ B.L.lattice ↔ x ∈ TaylorLogMetric.lamOf D cc δ := by
  rw [← B.lat]; rfl

theorem hst : ∀ x ∈ B.L.lattice, cmTheta 1 D.host.d * x ∈ B.L.lattice :=
  fun x hx => (mem_iff B _).2 (lam_theta ((mem_iff B x).1 hx))

theorem theta_val (D : D7) : cmTheta 1 D.host.d = (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := by
  simp [cmTheta]

theorem hθ : cmTheta 1 D.host.d * (B.ω₀ / 2) ∉ B.L.lattice := by
  rw [mem_iff, theta_val]; exact B.t0.2.1

theorem hθ' : (1 - cmTheta 1 D.host.d) * (B.ω₀ / 2) ∉ B.L.lattice := by
  have e : 1 - cmTheta 1 D.host.d = (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := by rw [theta_val]; ring
  rw [mem_iff, e]; exact B.t0.2.2

theorem half : B.ω₀ / 2 ∉ B.L.lattice := SC.half_notMem (hst B) B.omega_mem (hθ B) (hθ' B)

theorem betaStd : ∀ x ∈ stdLat B.L (Fin 4 × D.what₂.Tau),
    alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau)) x = stdChar B.L B.ω₀ x :=
  fun x hx => SC.stdChar_eq (hst B) B.omega_mem (hθ B) (hθ' B) (by have := D.host.hyp.2.2.2.1; omega) _ x hx

theorem selfDual (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := selfDual_img _ _ (reix D.what₂.Tau) (reix_isom B.L D.what₂.Tau) _ h
  rw [reix_pow] at h2
  exact selfDual_img _ _ B.gC B.isomOK _ h2

theorem betaSemi (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSemiChar (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) := by
  refine (quadMultiplierSemicharacter _ _ (standardFormBasic _ _).2.1 1 D.host.d odd_one _
    (le_of_eq (selfDual B hcc hδ).symm) ?_).2.2
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨cmTheta 1 D.host.d • z, fun a => ?_, map_smul B.gC _ z⟩
  have := lamMM_smul (AR.om D) (hz a)
  rw [← theta_eq] at this
  exact this

theorem up : ∃ N : ℕ, 0 < N ∧
    ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM),
      N • x ∈ stdLat B.L (Fin 4 × D.what₂.Tau) := by
  obtain ⟨k, hk, hA⟩ := exists_nat_clearing_order_denominators D
  let f : Fin 4 × (Fin 4 × D.what₂.Tau) → D.host.E →+ D.host.K := fun p =>
    { toFun := fun x => B.γ₀.g (Pi.single p.1 x) p.2
      map_zero' := by simp
      map_add' := fun x y => by rw [Pi.single_add, map_add]; rfl }
  obtain ⟨m, hm, hf⟩ := denom D.host.E D.host.K f
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  have hle : pow4 B.lamM ≤ ((stdLat B.L (Fin 4 × D.what₂.Tau)).comap
      (nsmulAddMonoidHom (α := Fin 4 × D.what₂.Tau → ℂ) (m * k))).comap
        (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)).toAddMonoidHom := by
    refine (fourth_power_le_closure_embeddings _).trans ?_
    rw [AddSubgroup.closure_le]
    rintro _ ⟨w, hw, y, hy, rfl⟩
    show (m * k) • B.gC (w • emb4 D y) ∈ stdLat B.L (Fin 4 × D.what₂.Tau)
    rw [mem_stdLat]
    intro v
    rw [map_smul, show B.gC (emb4 D y) = _ from B.gC_spec y, mem_iff]

    have hint : IsIntegral ℤ (((m * k : ℕ) : D.host.K) * B.γ₀.g y v) := by
      have hy' : y = ∑ a, Pi.single a (y a) := by
        funext a'; simp [Finset.sum_apply, Pi.single_apply]
      have e : ((m * k : ℕ) : D.host.K) * B.γ₀.g y v
          = ∑ a, (m : D.host.K) * f (a, v) ((k : D.host.E) * y a) := by
        conv_lhs => rw [hy']
        rw [map_sum, Finset.sum_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        show ((m * k : ℕ) : D.host.K) * B.γ₀.g (Pi.single a (y a)) v
          = (m : D.host.K) * B.γ₀.g (Pi.single a ((k : D.host.E) * y a)) v
        have : (Pi.single a ((k : D.host.E) * y a) : Fin 4 → D.host.E) = k • Pi.single a (y a) := by
          funext a'
          by_cases h : a' = a
          · subst h; simp
          · simp [Pi.single_eq_of_ne h]
        rw [this, map_nsmul]
        simp only [Pi.smul_apply, nsmul_eq_mul]
        push_cast; ring
      rw [e]
      exact IsIntegral.sum _ fun a _ => hf (a, v) ⟨_, hA _ (hy a)⟩
    have := lam_mul (cc := cc) (δ := δ) (⟨_, hint⟩ : 𝓞 D.host.K) hw
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    show ((m * k : ℕ) : ℂ) * (w * D.host.φ₀ ((B.γ₀.g y v : D.host.K) : D.host.E))
      = D.host.φ₀ (((((m * k : ℕ) : D.host.K) * B.γ₀.g y v : D.host.K)) : D.host.E) * w
    push_cast
    rw [map_mul, map_mul, map_natCast, map_natCast]
    ring
  rintro _ ⟨z, hz, rfl⟩
  exact hle hz

theorem down : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ stdLat B.L (Fin 4 × D.what₂.Tau),
    N • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) := by
  obtain ⟨m, hm, hT⟩ := exists_nat_mul D.host.E
    (Finset.univ.image fun p : (Fin 4 × D.what₂.Tau) × Fin 4 =>
      B.γ₀.g.symm (Pi.single p.1 (1 : D.host.K)) p.2)
  refine ⟨m, hm, fun x hx => ?_⟩
  rw [mem_stdLat] at hx
  have hsum : m • x = ∑ v, m • (Pi.single v (x v) : Fin 4 × D.what₂.Tau → ℂ) := by
    rw [← Finset.smul_sum]
    congr 1
    funext v'; simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun v _ => ?_
  refine ⟨x v • emb4 D (m • B.γ₀.g.symm (Pi.single v (1 : D.host.K))),
    gen_mem ((mem_iff B _).1 (hx v)) (fun a => int_mem_inverse_half_different ?_), ?_⟩
  · have := hT _ (Finset.mem_image.2 ⟨(v, a), Finset.mem_univ _, rfl⟩)
    simpa using this
  · show B.gC (x v • emb4 D (m • B.γ₀.g.symm (Pi.single v (1 : D.host.K)))) = _
    rw [map_smul, show B.gC (emb4 D _) = _ from B.gC_spec _, map_nsmul, LinearEquiv.apply_symm_apply]
    funext v'
    by_cases h : v' = v
    · subst h; simp; ring
    · simp [Pi.single_eq_of_ne h]

theorem idx₂ : relIdx (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
    (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 := by
  obtain ⟨N, hN, h⟩ := down B
  exact Formalism.L2.Th1.H.Inh.relIdx_ne_zero_of_fg _ _ N hN h

theorem idx₁ : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
    (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0 := by
  obtain ⟨N, hN, h⟩ := up B
  have := fg_of_nsmul_le _ (stdLat B.L (Fin 4 × D.what₂.Tau)) N hN h
  exact Formalism.L2.Th1.H.Inh.relIdx_ne_zero_of_fg _ _ N hN h

theorem stdOK (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.StdOK :=
  B.stdOK_of' (half B) (betaStd B) (betaSemi B hcc hδ) (selfDual B hcc hδ) (idx₁ B) (idx₂ B)

end B

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO

end
