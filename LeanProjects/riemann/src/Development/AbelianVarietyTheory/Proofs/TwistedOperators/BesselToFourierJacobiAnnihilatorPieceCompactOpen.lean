import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulSelfDualHomLatticeMemDepthLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHomLatticeOwnAnnihilatorStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSympl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AnnPiece

variable {D : D7}

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, RingHom.map_add, mul_add, add_mul, Finset.sum_add_distrib, LinearMap.map_add]

theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, LinearMap.map_add]

def symplR (S T : HSp D) (x : WO S T) : WO S T →+ AF D.host.F :=
  AddMonoidHom.mk' (symplO S T x) (symplO_add_right S T x)

def symplL (S T : HSp D) (y : WO S T) : WO S T →+ AF D.host.F :=
  AddMonoidHom.mk' (fun x => symplO S T x y) fun x x' => symplO_add_left S T x x' y

theorem mem_idAt_true (x : AE D) : x ∈ idAt D (fun _ => True) ↔ infPart D x = 0 := by
  simp only [GlobalTheory.FinPl.idAt, Ideal.mem_inf, RingHom.mem_ker, Ideal.mem_iInf]
  exact ⟨fun h => h.1, fun h => ⟨h, fun w => absurd trivial w.2⟩⟩

theorem isClosed_mxAt (m n : ℕ) : IsClosed {a : Mx D m n | MxAt (fun _ => True) a} := by
  have e : {a : Mx D m n | MxAt (fun _ => True) a} =
      ⋂ i, ⋂ j, {a : Mx D m n | infPart D (a i j) = 0} := by
    ext a
    simp only [Set.mem_setOf_eq, MxAt, mem_idAt_true, Set.mem_iInter]
  rw [e]
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field D.host.F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Ainf D.host.F)
  haveI : T2Space (Ainf D.host.F ⊗[D.host.F] D.host.E) := eh.isEmbedding.t2Space
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq ((GlobalTheory.Member.continuous_infPart D).comp ((continuous_apply j).comp (continuous_apply i))) continuous_const

theorem mxAt_mul_rat {m n k : ℕ} {a : Mx D m n} (ha : MxAt (fun _ => True) a) (b : Mx D n k) :
    MxAt (fun _ => True) (a ⬝ b) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem eq_one_of_pow_near (z : ℂ) (hz : ‖z‖ = 1) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1) : z = 1 := by
  have key : ∀ w : ℂ, ‖w‖ = 1 → ‖w - 1‖ < 1 → 3 / 2 ≤ ‖w + 1‖ := by
    intro w hw h1
    have hp : ‖w + 1‖ ^ 2 + ‖w - 1‖ ^ 2 = 2 * ‖w‖ ^ 2 + 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im]
      ring
    rw [hw] at hp
    nlinarith [norm_nonneg (w + 1), norm_nonneg (w - 1)]
  have ind : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * (z ^ (2 ^ k) + 1) := by
        rw [pow_succ, pow_mul]; ring
      have hn : ‖z ^ (2 ^ k)‖ = 1 := by rw [norm_pow, hz, one_pow]
      have h2 := key _ hn (h _)
      rw [e, norm_mul, pow_succ]
      have h0 : 0 ≤ (3 / 2 : ℝ) ^ k * ‖z - 1‖ := by positivity
      nlinarith
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h3 := ind k
  have h4 := h (2 ^ k)
  have : 1 < (3 / 2 : ℝ) ^ k * ‖z - 1‖ := by
    rw [div_lt_iff₀ hpos] at hk; linarith
  linarith

section Ann

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (Γ : AddSubgroup (WO V W))

def ann : AddSubgroup (Mx D W.rank ρ) where
  carrier := {a' | MxAt (fun _ => True) a' ∧ ∀ a, dV.extX W a ∈ Γ → ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1}
  zero_mem' := ⟨fun i j => zero_mem _, fun a _ => by
    rw [map_zero, show symplO V W (dV.extX W a) 0 = 0 from map_zero (symplR V W (dV.extX W a)), AddChar.map_zero_eq_one]⟩
  add_mem' := fun {x y} hx hy => ⟨fun i j => add_mem (hx.1 i j) (hy.1 i j), fun a ha => by
    rw [map_add, symplO_add_right, AddChar.map_add_eq_mul, hx.2 a ha, hy.2 a ha, one_mul]⟩
  neg_mem' := fun {x} hx => ⟨fun i j => neg_mem (hx.1 i j), fun a ha => by
    have e : symplO V W (dV.extX W a) (dV.extY W (-x)) = -symplO V W (dV.extX W a) (dV.extY W x) := by
      rw [map_neg]; exact map_neg (symplR V W (dV.extX W a)) _
    have h1 := AddChar.map_add_eq_mul ψ (-symplO V W (dV.extX W a) (dV.extY W x)) (symplO V W (dV.extX W a) (dV.extY W x))
    rw [neg_add_cancel, AddChar.map_zero_eq_one, hx.2 a ha, mul_one] at h1
    rw [e, ← h1]⟩

theorem A₂_eq (dW : HypDec W W₀ σ) (Γ' : AddSubgroup (WO V W)) :
    (piecesOf dV dW ψ Γ Γ' : Pieces V₀ W W₀ ρ σ).A₂ = ann dV ψ Γ :=
  AddSubgroup.closure_eq (ann dV ψ Γ)

end Ann

end GlobalTheory.AnnPiece

namespace GlobalTheory.AnnPiece

variable {D : D7}

section Ann2

variable {V V₀ W : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (Γ : AddSubgroup (WO V W))

theorem continuous_extX : Continuous fun x : Mx D W.rank ρ => dV.extX W x := by
  simp only [HypDec.extX_apply]; exact continuous_id.matrix_mul continuous_const

theorem continuous_extY : Continuous fun x : Mx D W.rank ρ => dV.extY W x := by
  simp only [HypDec.extY_apply]; exact continuous_id.matrix_mul continuous_const

theorem continuous_symplO : Continuous fun p : WO V W × WO V W => symplO V W p.1 p.2 :=
  Formalism.IndefR.Eqv.continuous_trace.comp (continuous_const.mul Formalism.IndefR.Eqv.continuous_hO)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ann_open (hψ : Continuous ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1) (C : Set (Mx D W.rank ρ)) (hC : IsCompact C)
    (hΓC : ∀ a, dV.extX W a ∈ Γ → a ∈ C) :
    ∃ U : Set (Mx D W.rank ρ), IsOpen U ∧ (0 : Mx D W.rank ρ) ∈ U ∧ ∀ a' ∈ U, MxAt (fun _ => True) a' → a' ∈ ann dV ψ Γ := by
  have h1 : Continuous fun p : Mx D W.rank ρ × Mx D W.rank ρ => (dV.extX W p.1, dV.extY W p.2) :=
    ((continuous_extX dV).comp continuous_fst).prodMk ((continuous_extY dV).comp continuous_snd)
  have h2 : Continuous fun p : Mx D W.rank ρ × Mx D W.rank ρ => symplO V W (dV.extX W p.1) (dV.extY W p.2) :=
    Continuous.comp (g := fun p : WO V W × WO V W => symplO V W p.1 p.2)
      (f := fun p : Mx D W.rank ρ × Mx D W.rank ρ => (dV.extX W p.1, dV.extY W p.2)) (continuous_symplO (V := V) (W := W)) h1
  set Φ : Mx D W.rank ρ × Mx D W.rank ρ → ℂ := fun p => ψ (symplO V W (dV.extX W p.1) (dV.extY W p.2)) with hΦdef
  have hΦ : Continuous Φ := Continuous.comp (g := ψ)
    (f := fun p : Mx D W.rank ρ × Mx D W.rank ρ => symplO V W (dV.extX W p.1) (dV.extY W p.2)) hψ h2
  have hO : IsOpen {p | ‖Φ p - 1‖ < 1} := isOpen_lt (hΦ.sub continuous_const).norm continuous_const
  have hsub : C ×ˢ ({0} : Set (Mx D W.rank ρ)) ⊆ {p | ‖Φ p - 1‖ < 1} := by
    rintro ⟨a, b⟩ ⟨-, hb⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    simp only [Set.mem_setOf_eq, hΦdef, map_zero]
    rw [show symplO V W (dV.extX W a) 0 = 0 from map_zero (symplR V W (dV.extX W a)), AddChar.map_zero_eq_one, sub_self,
      norm_zero]
    exact one_pos
  obtain ⟨u, v, -, hv, hCu, h0v, huv⟩ := generalized_tube_lemma hC isCompact_singleton hO hsub
  refine ⟨v, hv, h0v rfl, fun a' ha' hfin => ⟨hfin, fun a ha => ?_⟩⟩
  have hpow : ∀ n : ℕ, Φ (n • a, a') = Φ (a, a') ^ n := by
    intro n
    simp only [hΦdef, map_nsmul]
    rw [show symplO V W (n • dV.extX W a) (dV.extY W a') = n • symplO V W (dV.extX W a) (dV.extY W a') from
      map_nsmul (symplL V W (dV.extY W a')) n _, AddChar.map_nsmul_eq_pow]
  refine eq_one_of_pow_near _ (hψ1 _) fun n => ?_
  have hn : (n • a, a') ∈ u ×ˢ v := ⟨hCu (hΓC _ (by rw [map_nsmul]; exact nsmul_mem ha n)), ha'⟩
  have := huv hn
  simp only [Set.mem_setOf_eq, hpow] at this
  exact this

set_option synthInstance.maxHeartbeats 400000 in

theorem ann_isCompact (K : Set (Mx D W.rank ρ)) (hK : IsCompact K) (hSK : ∀ a' ∈ ann dV ψ Γ, a' ∈ K)
    (U : Set (Mx D W.rank ρ)) (hU : IsOpen U) (h0 : (0 : Mx D W.rank ρ) ∈ U)
    (hUS : ∀ a' ∈ U, MxAt (fun _ => True) a' → a' ∈ ann dV ψ Γ) : IsCompact (ann dV ψ Γ : Set (Mx D W.rank ρ)) := by
  have hcl : IsClosed (ann dV ψ Γ : Set (Mx D W.rank ρ)) := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro b hb
    by_cases hbF : MxAt (fun _ => True) b
    · refine ⟨(fun x => x - b) ⁻¹' U, ?_, hU.preimage (continuous_id.sub continuous_const), by simpa using h0⟩
      intro x hx hxS
      apply hb
      have h1 : x - b ∈ ann dV ψ Γ := hUS _ hx fun i j => sub_mem (hxS.1 i j) (hbF i j)
      have h2 := sub_mem hxS h1
      rwa [sub_sub_cancel] at h2
    · refine ⟨{a | MxAt (fun _ => True) a}ᶜ, ?_, (isClosed_mxAt _ _).isOpen_compl, hbF⟩
      intro x hx hxS
      exact hx hxS.1
  exact hK.of_isClosed_subset hcl hSK

theorem symplO_extY (u : WO V W) (b : Mx D W.rank ρ) :
    symplO V W u (dV.extY W b) = symplO V W (dV.extX W (u ⬝ dV.jX)) (dV.extY W b) := by
  simp only [symplO]
  rw [dV.hO_coordS, dV.hO_coordS]
  simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY,
    HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY, Matrix.mul_one, Matrix.mul_zero]
  simp [hO, pairS]

end Ann2

end GlobalTheory.AnnPiece

namespace GlobalTheory.AnnPiece

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem pcBF_A₂_compact_open : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    IsCompact ((pcBF W F ρ h).A₂ : Set (Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ)) ∧
    ∃ U : Set (Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ), IsOpen U ∧ (0 : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ) ∈ U ∧
      ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ (pcBF W F ρ h).A₂ := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  have hi : 2 * ρ + 1 < D.R.m := by omega
  obtain ⟨hR, -, hB, -⟩ := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) hi
  obtain ⟨Na, hNa, hNa'⟩ : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G (2 * ρ + 1), N • u ∈ latRow G (2 * ρ + 1) := GlobalTheory.T.exists_nsmul_selfDual_hom_lattice_mem_depth_lattice D hq T L μ0 hL sc G W M hM F hF (2 * ρ + 1) hi
  obtain ⟨Nb, hNb, hNb'⟩ : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G (2 * ρ + 1),
      N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) ∈ latBig G (2 * ρ + 1) := GlobalTheory.T.nsmul_projection_xColumns_mem_selfDual_lattice D hq T L μ0 hL sc G W M hM F hF ρ h
  have hC : ∀ u' : WO (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.V (.grid (2 * ρ + 1) 0)), MxAt (fun _ => True) u' →
      (∀ u ∈ latBig G (2 * ρ + 1), W.ψ (symplO _ _ u u') = 1) → u' ∈ latBig G (2 * ρ + 1) := GlobalTheory.T.selfDual_modulus_shift_hom_lattice_own_annihilator D hq T L μ0 hL sc G W M hM F hF (2 * ρ + 1) hi
  rw [A₂_eq]
  have hψ := W.ψ_std.1
  obtain ⟨U, hU, h0, hUS⟩ := ann_open (F.dB ρ h) W.ψ (latRow G (2 * ρ + 1)) hψ.1 hψ.2.1
    ((fun w : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) => w ⬝ (F.dB ρ h).jX) ''
      (latRow G (2 * ρ + 1) : Set (WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)))))
    (hR.cpt.image (f := fun w : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) => w ⬝ (F.dB ρ h).jX)
      (continuous_id.matrix_mul continuous_const))
    (fun a ha => ⟨(F.dB ρ h).extX _ a, ha, by
      show a ⬝ (F.dB ρ h).pX ⬝ (F.dB ρ h).jX = a
      rw [Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]⟩)
  refine ⟨ann_isCompact (F.dB ρ h) W.ψ _
    ((fun w : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) =>
        algebraMap D.host.F (AE D) ((Na * Nb : ℕ) : D.host.F)⁻¹ • (w ⬝ (F.dB ρ h).jY)) ''
      (latBig G (2 * ρ + 1) : Set (WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)))))
    ?_ ?_ U hU h0 hUS, U, hU, h0, hUS⟩
  · exact hB.cpt.image (f := fun w : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) =>
        algebraMap D.host.F (AE D) ((Na * Nb : ℕ) : D.host.F)⁻¹ • (w ⬝ (F.dB ρ h).jY))
      (Continuous.comp (g := fun m : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ => algebraMap D.host.F (AE D) ((Na * Nb : ℕ) : D.host.F)⁻¹ • m)
        (f := fun w : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) => w ⬝ (F.dB ρ h).jY) (continuous_const_smul _)
        (continuous_id.matrix_mul continuous_const))
  · intro a' ha'
    obtain ⟨hfin, hann⟩ := ha'
    set N := Na * Nb with hN
    have key : ∀ u ∈ latBig G (2 * ρ + 1), W.ψ (symplO _ _ u ((F.dB ρ h).extY _ (N • a'))) = 1 := by
      intro u hu
      have h1 : (F.dB ρ h).extX _ (N • (u ⬝ (F.dB ρ h).jX)) ∈ latRow G (2 * ρ + 1) := by
        rw [HypDec.extX_apply, Matrix.smul_mul, hN, mul_smul]
        exact hNa' _ (hNb' u hu)
      have h2 := hann _ h1
      have e1 : symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) u ((F.dB ρ h).extY _ (N • a')) =
          symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX _ (N • (u ⬝ (F.dB ρ h).jX))) ((F.dB ρ h).extY _ a') := by
        rw [map_nsmul, map_nsmul]
        rw [show symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) u (N • (F.dB ρ h).extY _ a') = N • symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) u ((F.dB ρ h).extY _ a')
          from map_nsmul (symplR (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) u) N _]
        rw [show symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) (N • (F.dB ρ h).extX _ (u ⬝ (F.dB ρ h).jX)) ((F.dB ρ h).extY _ a') =
            N • symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX _ (u ⬝ (F.dB ρ h).jX)) ((F.dB ρ h).extY _ a')
          from map_nsmul (symplL (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extY _ a')) N _]
        rw [symplO_extY]
      rw [e1]
      exact h2
    have hmem := hC _ (mxAt_mul_rat (fun i j => nsmul_mem (hfin i j) N) _) key
    refine ⟨_, hmem, ?_⟩
    show algebraMap D.host.F (AE D) ((Na * Nb : ℕ) : D.host.F)⁻¹ • ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (N • a') ⬝ (F.dB ρ h).jY) = a'
    rw [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, Matrix.mul_one]
    rw [← Nat.cast_smul_eq_nsmul (AE D) N a', smul_smul, ← map_natCast (algebraMap D.host.F (AE D)), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hNa.ne' hNb.ne')), map_one, one_smul]

end GlobalTheory.AnnPiece

end
