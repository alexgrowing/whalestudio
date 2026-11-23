import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionBoundOfWeightHypStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesLatticeTrivialQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfSubmodule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Cocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCocTmulOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContractEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExpStarZeroNear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryBcrisOfDualExponentialZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemHfDOfRestriction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLayerIff
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

noncomputable section

namespace GlobalTheory.Cyc.ClassBound

open TensorProduct
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem padicInt_hom_witt_ext_pt {R : Type} [CommRing R] [CharP R l]
    (f g : ℤ_[l] →+* WittVector l R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  ext n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (n + 1) z)
  have hz : z = c * (l : ℤ_[l]) ^ (n + 1) + ((PadicInt.appr z (n + 1) : ℕ) : ℤ_[l]) := by
    rw [hc]; ring
  have h : f z - g z = (f c - g c) * (l : WittVector l R) ^ (n + 1) := by
    generalize PadicInt.appr z (n + 1) = m at hz
    rw [hz]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self n), WittVector.zero_coeff]

theorem exists_coords {G : Type} [Group G] [TopologicalSpace G] {LL O : Type} [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL] [Algebra ℤ_[l] O]
    (hc : ∀ a : ℤ_[l], algebraMap O LL (algebraMap ℤ_[l] O a) = algebraMap ℚ_[l] LL a)
    (Y V : LocLat G ℚ_[l] LL O) (φ : ↥Y.L.T →ₗ[O] (V.V ⧸ V.L.T)) {n : ℕ}
    (w : Module.Basis (Fin n) ℚ_[l] V.V) {m : ℕ} (u : Module.Basis (Fin m) ℚ_[l] Y.V)
    (hu : ∀ x : Y.V, x ∈ Y.L.T ↔ ∀ i, ‖u.repr x i‖ ≤ 1) :
    letI : Module ℤ_[l] ↥Y.L.T := Module.compHom ↥Y.L.T (algebraMap ℤ_[l] O)
    ∃ (Φ : ↥Y.L.T →+ V.V) (ψ : Fin n → (↥Y.L.T →ₗ[ℤ_[l]] ℚ_[l])) (r : ℕ),
      (∀ y, (Submodule.Quotient.mk (Φ y) : V.V ⧸ V.L.T) = φ y) ∧
      (∀ i y, ψ i y = w.repr (Φ y) i) ∧ ∀ i y, ‖ψ i y‖ ≤ (l : ℝ) ^ r := by
  letI : Module ℤ_[l] ↥Y.L.T := Module.compHom ↥Y.L.T (algebraMap ℤ_[l] O)
  haveI := Y.L.free
  obtain ⟨Φ, hΦ⟩ := Module.projective_lifting_property V.L.T.mkQ φ (Submodule.mkQ_surjective _)
  have hs : ∀ (a : ℤ_[l]) (y : ↥Y.L.T), Φ (a • y) = (a : ℚ_[l]) • Φ y := fun a y => by
    change Φ (algebraMap ℤ_[l] O a • y) = _
    rw [map_smul, ← algebraMap_smul LL, hc, algebraMap_smul]
  let ψ : Fin n → (↥Y.L.T →ₗ[ℤ_[l]] ℚ_[l]) := fun i =>
    { toFun := fun y => w.repr (Φ y) i
      map_add' := fun a b => by simp
      map_smul' := fun a y => by rw [hs, map_smul]; rfl }
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hu1 : ∀ j, u j ∈ Y.L.T := fun j => (hu _).2 fun i => by
    rw [u.repr_self, Finsupp.single_apply]; split_ifs <;> simp
  obtain ⟨r, hr⟩ : ∃ r : ℕ, ∀ i j, ‖ψ i ⟨u j, hu1 j⟩‖ ≤ (l : ℝ) ^ r := by
    obtain ⟨C, hC⟩ := (Set.finite_range fun p : Fin n × Fin m => ‖ψ p.1 ⟨u p.2, hu1 p.2⟩‖).bddAbove
    obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt C hl1
    exact ⟨r, fun i j => (hC ⟨(i, j), rfl⟩).trans hr.le⟩
  refine ⟨Φ.toAddMonoidHom, ψ, r, fun y => congrArg (fun F : _ →ₗ[_] _ => F y) hΦ, fun _ _ => rfl,
    fun i y => ?_⟩
  let a : Fin m → ℤ_[l] := fun j => ⟨u.repr (y : Y.V) j, (hu _).1 y.2 j⟩
  have hy : y = ∑ j, a j • (⟨u j, hu1 j⟩ : ↥Y.L.T) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    conv_lhs => rw [← u.sum_repr (y : Y.V)]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = algebraMap ℤ_[l] O (a j) • u j
    rw [← algebraMap_smul LL (algebraMap ℤ_[l] O (a j)), hc, algebraMap_smul]
  rw [hy, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  rw [map_smul]
  change ‖u.repr (y : Y.V) j * _‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((hu _).1 y.2 j)).trans (hr i j)

theorem actVB_sum_tmul {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (w : Module.Basis (Fin n) Qp V) (x : Fin n → B) (g : G)
    (c : Qp) (hc : ∀ v, ρ g v = c • v) (z : Fin n → Qp)
    (hz : ∀ i, algebraMap Qp B (z i) = c • PD.actB g (x i) - x i) :
    w.equivFun.symm z ⊗ₜ[Qp] (1 : B) =
      actVB PD ρ g (∑ i, w i ⊗ₜ[Qp] x i) - ∑ i, w i ⊗ₜ[Qp] x i := by
  rw [map_sum, ← Finset.sum_sub_distrib, Module.Basis.equivFun_symm_apply, sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = ρ g (w i) ⊗ₜ[Qp] PD.actB g (x i) - _
  rw [hc, smul_tmul, smul_tmul, ← tmul_sub, ← hz i, Algebra.algebraMap_eq_smul_one]

set_option maxHeartbeats 1600000 in

theorem mem_HfD_of_coords (P : LocPrime l) (K LL : FinExt l) (s : ℕ) (hK : K.1 ≤ Ks K s)
    (V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (c : GQ l → ℚ_[l])
    (hV : ∀ (g : ↥(GK K)) (x : V.V), V.ρ g x = c g • x) {n : ℕ}
    (w : Module.Basis (Fin n) ℚ_[l] V.V) (hw : ∀ x : V.V, x ∈ V.L.T ↔ ∀ i, ‖w.repr x i‖ ≤ 1)
    (hwc : Continuous w.equivFun.symm) (f₀ : ↥(GK K) → V.V)
    (hf₀ : ∀ g h, f₀ (g * h) - (f₀ g + V.ρ g (f₀ h)) ∈ V.L.T) (z : Fin n → GQ l → ℚ_[l])
    (hz : ∀ i, CocOn (Gj K s) (fun σ y => c σ * y) Set.univ (z i)) (x : Fin n → P.R.B)
    (hx : ∀ i, ∀ σ ∈ Gj K s, algebraMap ℚ_[l] P.R.B (z i σ) = c σ • P.actQ σ (x i) - x i)
    (hzf : ∀ i (g : ↥(GK K)), (g : GQ l) ∈ Gj K s → ‖z i g - w.repr (f₀ g) i‖ ≤ 1) :
    (fun g => (l ^ (padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) -
      padicValNat l (Module.finrank ℚ_[l] ↥K.1)) : ℕ) •
        (Submodule.Quotient.mk (f₀ g) : V.V ⧸ V.L.T)) ∈ HfD (P.PD K) V.L := by
  obtain ⟨hN, hF, hO, hI⟩ := GlobalTheory.Cyc.LayerGroup.layer_group l K s hK
  refine GlobalTheory.pow_smul_mem_HfD_of_restriction l P K LL V ((Gj K s).subgroupOf (GK K)) hO
    (fun g => w.equivFun.symm fun i => z i g) f₀ ?_ ?_ ⟨∑ i, w i ⊗ₜ[ℚ_[l]] x i, ?_⟩ hf₀ ?_ _ hI.le
  · refine hwc.comp_continuousOn (continuousOn_pi.2 fun i => ?_)
    exact (hz i).1.comp continuous_subtype_val.continuousOn fun g hg => hg
  · intro g hg h hh
    rw [hV, ← map_smul, ← map_add]
    congr 1
    funext i
    exact (hz i).2.2 g hg h hh
  · intro h hh
    exact actVB_sum_tmul (P.PD K) V.ρ w x h (c h) (hV h) _ fun i => by
      rw [P.PD_actB]; exact hx i h hh
  · intro h hh
    refine (hw _).2 fun i => ?_
    have h1 : ∀ (a : Fin n → ℚ_[l]) (v : V.V),
        w.repr (w.equivFun.symm a - v) i = a i - w.repr v i := fun a v => by
      rw [map_sub w.repr, Finsupp.sub_apply, ← w.equivFun_apply, LinearEquiv.apply_symm_apply]
    exact (congrArg norm (h1 _ _)).le.trans (hzf i h hh)

theorem scalar_step (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h4 : ArchimedeanSignatureMatching D) (K : FinExt l) (s : ℕ)
    (hs : Lev l s) (e r N : ℕ) (c : GQ l → ℚ_[l]) (hb : ∀ σ ∈ Gj K s, ‖c σ‖ ≤ (l : ℝ) ^ r)
    (hc : ∀ σ ∈ Gj K s, ∀ τ ∈ Gj K s, ‖c (σ * τ) - c σ -
      (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * c τ‖ ≤ 1)
    (hl : ∀ σ ∈ Gj K s, ∀ᶠ τ in nhdsWithin σ (Gj K s), ‖c τ - c σ‖ ≤ 1)
    (hr : ∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l,
      algebraMap ℚ_[l] (D.loc l).R.BdR ((l : ℚ_[l]) ^ N * c σ) -
        (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) *
          (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈
        ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1)) :
    ∃ (z : GQ l → ℚ_[l]) (x : (D.loc l).R.B),
      CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z ∧
      (∀ σ ∈ Gj K s, algebraMap ℚ_[l] (D.loc l).R.B (z σ) =
        (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • (D.loc l).actQ σ x - x) ∧
      ∀ σ ∈ Gj K s, ‖z σ - (l : ℚ_[l]) ^ (N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
        (s + padicValNat l (e + 1))) * c σ‖ ≤ 1 := by
  obtain ⟨z, hz, hzc⟩ := GlobalTheory.Cyc.TwistLift.lift_cocycle D h2 h4 l K s hs e r c hb hc hl
  obtain ⟨b, hb0, hbσ⟩ := hr
  have hl1 : ∀ k : ℕ, ‖(l : ℚ_[l]) ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (Padic.norm_p_lt_one).le
  have hsm : ∀ (k : ℕ) (j : ℤ) (y : (D.loc l).R.BdR), y ∈ ((D.loc l).PD (botExt l)).Fil j →
      (l : (D.loc l).R.BdR) ^ k * y ∈ ((D.loc l).PD (botExt l)).Fil j := fun k j y hy => by
    have := nsmul_mem hy (l ^ k)
    rwa [nsmul_eq_mul, Nat.cast_pow] at this
  have hz1 : CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y)
      Set.univ (fun σ => (l : ℚ_[l]) ^ N * z σ) :=
    ⟨continuousOn_const.mul hz.1, fun _ _ => trivial, fun g hg h hh => by
      simp only [hz.2.2 g hg h hh]; ring⟩
  obtain ⟨z', hz', hz'c⟩ := GlobalTheory.Cyc.ExpScalar.exists_expStar_zero_near D h2 h4 l K s hs e _ hz1
    ⟨(l : (D.loc l).R.BdR) ^ (s + padicValNat l (e + 1)) * b, hsm _ _ _ hb0, fun σ hσ => by
      obtain ⟨a, ha⟩ := hbσ σ hσ
      let u : ℤ_[l] := ⟨_, hzc σ hσ⟩
      have hu : z σ = (u : ℚ_[l]) + (l : ℚ_[l]) ^ (s + padicValNat l (e + 1)) * c σ := by
        simp [u]
      have hι : (D.loc l).ιB ((D.locA l).ιA (algebraMap ℤ_[l] (Ainf l) u)) =
          algebraMap ℚ_[l] _ (u : ℚ_[l]) := by
        have : (D.locA l).ιA (algebraMap ℤ_[l] (Ainf l) u) = algebraMap ℚ_[l] _ (u : ℚ_[l]) := by
          apply (D.locT l).eB.injective
          rw [(D.locT l).ιA, (D.locT l).zB, GlobalTheory.RingIface.zB_eq_aB_zA]
          exact congrArg (Formalism.Per.aB l)
            (padicInt_hom_witt_ext_pt (algebraMap ℤ_[l] (Ainf l)) (Formalism.Per.zA l) u)
        rw [this, AlgHom.commutes]
      refine ⟨(l : Ainf l) ^ (s + padicValNat l (e + 1)) * a +
        (l : Ainf l) ^ N * algebraMap ℤ_[l] (Ainf l) u, ?_⟩
      have := hsm (s + padicValNat l (e + 1)) _ _ ha
      convert this using 1
      simp only [hu, map_add, map_mul, map_pow, map_natCast, hι]
      ring⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.coboundary_bcris_of_dualExponential_zero D h2 h4 l K s hs e z' hz'
  refine ⟨z', x, hz'.1, hx, fun σ hσ => ?_⟩
  have h1 : z' σ - (l : ℚ_[l]) ^ (N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
        (s + padicValNat l (e + 1))) * c σ =
      (z' σ - (l : ℚ_[l]) ^ ((e + 2) * s + padicValNat l e + e / (l - 1) + 1) *
        ((l : ℚ_[l]) ^ N * z σ)) +
      (l : ℚ_[l]) ^ ((e + 2) * s + padicValNat l e + e / (l - 1) + 1 + N) *
        (z σ - (l : ℚ_[l]) ^ (s + padicValNat l (e + 1)) * c σ) := by ring
  rw [h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz'c σ hσ) ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hl1 _) (norm_nonneg _) (hzc σ hσ)

theorem scalar_of_isCob (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h4 : ArchimedeanSignatureMatching D) (K : FinExt l) (s : ℕ)
    (hs : Lev l s) (hle : Gj K s ≤ GK K) (e N r : ℕ) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y]
    (ρ : ↥(GK K) →* (Y →ₗ[ℤ_[l]] Y)) (f : ↥(GK K) → Y) (hf : ∀ g h, f (g * h) = f g + ρ g (f h))
    (hfl : ∀ (n : ℕ) (g : ↥(GK K)), ∀ᶠ h in nhds g, ∃ y : Y, f h - f g = (l ^ n : ℕ) • y)
    (one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0)) (hone : (one : WCb l) = 1)
    (hcob : IsCob (repQ (D.locA l) (Gj K s) (ρ.comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1))
      (fun g => (l : ℤ_[l]) ^ N • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]]
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))))
    (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (hψr : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r)
    (hψe : ∀ (g : ↥(GK K)) (y : Y), ‖ψ (ρ g y) -
      (((D.loc l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * ψ y‖ ≤ 1) :
    ∃ (z : GQ l → ℚ_[l]) (x : (D.loc l).R.B),
      CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z ∧
      (∀ σ ∈ Gj K s, algebraMap ℚ_[l] (D.loc l).R.B (z σ) =
        (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • (D.loc l).actQ σ x - x) ∧
      ∀ g : ↥(GK K), (g : GQ l) ∈ Gj K s →
        ‖z g - (l : ℚ_[l]) ^ (N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
          (s + padicValNat l (e + 1))) * ψ (f g)‖ ≤ 1 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : GQ l → ℚ_[l], ∀ (σ : GQ l) (h : σ ∈ GK K), c σ = ψ (f ⟨σ, h⟩) :=
    ⟨fun σ => if h : σ ∈ GK K then ψ (f ⟨σ, h⟩) else 0, fun σ h => dif_pos h⟩
  have H1 : ∀ σ ∈ Gj K s, ‖c σ‖ ≤ (l : ℝ) ^ r := fun σ hσ => by
    rw [hc σ (hle hσ)]; exact hψr _
  have H2 : ∀ σ ∈ Gj K s, ∀ τ ∈ Gj K s, ‖c (σ * τ) - c σ -
      (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * c τ‖ ≤ 1 := fun σ hσ τ hτ => by
    have h1 : f ⟨σ * τ, hle (mul_mem hσ hτ)⟩ = _ := hf ⟨σ, hle hσ⟩ ⟨τ, hle hτ⟩
    rw [hc σ (hle hσ), hc τ (hle hτ), hc _ (hle (mul_mem hσ hτ)), h1, ψ.map_add,
      add_sub_cancel_left]
    exact hψe ⟨σ, hle hσ⟩ _
  have H3 : ∀ σ ∈ Gj K s, ∀ᶠ τ in nhdsWithin σ (Gj K s), ‖c τ - c σ‖ ≤ 1 := fun σ hσ => by
    refine Filter.Eventually.filter_mono (nhdsWithin_mono σ (hle : (Gj K s : Set (GQ l)) ⊆ GK K)) ?_
    have h1 := hfl r ⟨σ, hle hσ⟩
    have h3 : nhdsWithin σ (GK K : Set (GQ l)) =
        Filter.map Subtype.val (nhds (⟨σ, hle hσ⟩ : ↥(GK K))) :=
      nhdsWithin_eq_map_subtype_coe (hle hσ)
    rw [h3, Filter.eventually_map]
    filter_upwards [h1] with τ ⟨y, hy⟩
    rw [hc σ (hle hσ), hc τ τ.2, ← ψ.map_sub]
    have h5 : ψ (f ⟨τ, τ.2⟩ - f ⟨σ, hle hσ⟩) = (l ^ r : ℕ) • ψ y := by
      rw [← map_nsmul, ← hy]
    rw [h5, nsmul_eq_mul, norm_mul, Nat.cast_pow, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hl0 : (0 : ℝ) < (l : ℝ) ^ r := by
      have := (Fact.out : l.Prime).pos
      positivity
    rw [inv_mul_le_iff₀ hl0, mul_one]
    exact hψr _
  have H4 := GlobalTheory.PushCob.push_coboundary D l K s e r N Y (ρ.comp (Subgroup.inclusion hle)) ψ hψr
    (fun σ hσ y => hψe ⟨σ, hle hσ⟩ y) (fun g => f (Subgroup.inclusion hle g)) c
    (fun σ hσ => hc σ (hle hσ)) one hone hcob
  obtain ⟨z, x, hz, hx, hzc⟩ := scalar_step D h2 h4 K s hs e r N c H1 H2 H3 H4
  refine ⟨z, x, hz, hx, fun g hg => ?_⟩
  have := hzc g hg
  rwa [hc g g.2] at this

set_option maxHeartbeats 800000 in

theorem mem_HfD_of_isCob (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h4 : ArchimedeanSignatureMatching D) (K LL : FinExt l) (s : ℕ)
    (hs : Lev l s) (hK : K.1 ≤ Ks K s) (hle : Gj K s ≤ GK K) (e N r : ℕ)
    (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y]
    (ρ : ↥(GK K) →* (Y →ₗ[ℤ_[l]] Y)) (f : ↥(GK K) → Y) (hf : ∀ g h, f (g * h) = f g + ρ g (f h))
    (hfl : ∀ (n : ℕ) (g : ↥(GK K)), ∀ᶠ h in nhds g, ∃ y : Y, f h - f g = (l ^ n : ℕ) • y)
    (one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0)) (hone : (one : WCb l) = 1)
    (hcob : IsCob (repQ (D.locA l) (Gj K s) (ρ.comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1))
      (fun g => (l : ℤ_[l]) ^ N • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]]
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))))
    (V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hV : ∀ (g : ↥(GK K)) (x : V.V),
      V.ρ g x = (((D.loc l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • x) {n : ℕ}
    (w : Module.Basis (Fin n) ℚ_[l] V.V) (hw : ∀ x : V.V, x ∈ V.L.T ↔ ∀ i, ‖w.repr x i‖ ≤ 1)
    (hwc : Continuous w.equivFun.symm) (Φ : Y →+ V.V)
    (hΦ : ∀ g y, Φ (ρ g y) - V.ρ g (Φ y) ∈ V.L.T)
    (ψ : Fin n → (Y →ₗ[ℤ_[l]] ℚ_[l])) (hψ : ∀ i y, ψ i y = w.repr (Φ y) i)
    (hψr : ∀ i y, ‖ψ i y‖ ≤ (l : ℝ) ^ r) :
    (fun g => (l ^ (padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) -
      padicValNat l (Module.finrank ℚ_[l] ↥K.1)) : ℕ) •
        (Submodule.Quotient.mk ((l ^ (N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
          (s + padicValNat l (e + 1))) : ℕ) • Φ (f g)) : V.V ⧸ V.L.T)) ∈
      HfD ((D.loc l).PD K) V.L := by
  have hψe : ∀ i (g : ↥(GK K)) (y : Y), ‖ψ i (ρ g y) -
      (((D.loc l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * ψ i y‖ ≤ 1 := fun i g y => by
    have := (hw _).1 (hΦ g y) i
    rwa [map_sub w.repr, Finsupp.sub_apply, hV, map_smul w.repr, Finsupp.smul_apply, smul_eq_mul,
      ← hψ, ← hψ] at this
  choose z x hz hx hzc using fun i => scalar_of_isCob D h2 h4 K s hs hle e N r Y ρ f hf hfl one hone
    hcob (ψ i) (hψr i) (hψe i)
  generalize N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
    (s + padicValNat l (e + 1)) = k at hzc ⊢
  have A1 : ∀ g h, (l ^ k : ℕ) • Φ (f (g * h)) -
      ((l ^ k : ℕ) • Φ (f g) + V.ρ g ((l ^ k : ℕ) • Φ (f h))) ∈ V.L.T := fun g h => by
    rw [hf g h, Φ.map_add, map_nsmul (V.ρ g), ← smul_add, ← smul_sub, add_sub_add_left_eq_sub]
    exact nsmul_mem (hΦ _ _) _
  have A2 : ∀ i (g : ↥(GK K)), (g : GQ l) ∈ Gj K s →
      ‖z i g - w.repr ((l ^ k : ℕ) • Φ (f g)) i‖ ≤ 1 := fun i g hg => by
    have := hzc i g hg
    rw [hψ] at this
    rw [map_nsmul w.repr, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_pow]
    exact this
  exact mem_HfD_of_coords (D.loc l) K LL s hK V
    (fun σ => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])) hV w hw hwc
    (fun g => (l ^ k : ℕ) • Φ (f g)) A1 z hz x hx A2

@[reducible] def modQuot {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) : Module O (T.V ⧸ T.L.T) :=
  Submodule.Quotient.module _

attribute [local instance high] modQuot

theorem pow_smul_eq_mk {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (T : Submodule O V)
    (l a b : ℕ) (x : V) (y : V ⧸ T) (h : Submodule.Quotient.mk x = y) :
    (l ^ (a + b) : ℕ) • y = (l ^ b : ℕ) • (Submodule.Quotient.mk ((l ^ a : ℕ) • x) : V ⧸ T) := by
  rw [← T.mkQ_apply, map_nsmul, T.mkQ_apply, h, ← mul_nsmul, ← pow_add]

theorem lift_equivariant {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (Y V : LocLat G Qp LL O) (φ : ↥Y.L.T →ₗ[O] (V.V ⧸ V.L.T))
    (hφ : ∀ g y, φ (actT Y.L g y) = actD V.L g (φ y)) (Φ : ↥Y.L.T →+ V.V)
    (hΦ : ∀ y, (Submodule.Quotient.mk (Φ y) : V.V ⧸ V.L.T) = φ y) (g : G) (y : ↥Y.L.T) :
    Φ (actT Y.L g y) - V.ρ g (Φ y) ∈ V.L.T := by
  refine (Submodule.Quotient.eq _).1 ?_
  have h1 := hφ g y
  rw [← hΦ, ← hΦ] at h1
  exact h1

set_option maxHeartbeats 800000 in

theorem mem_HfD_of_lattice (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h4 : ArchimedeanSignatureMatching D) (K LL : FinExt l) (s : ℕ)
    (hs : Lev l s) (hK : K.1 ≤ Ks K s) (hle : Gj K s ≤ GK K) (e N : ℕ)
    (Y V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hV : ∀ g x, V.ρ g x =
      ((algebraMap ℚ_[l] ↥LL.1 (((D.loc l).PD K).χ g : ℚ_[l]))⁻¹) ^ e • x)
    (φ : ↥Y.L.T →ₗ[↥(OL LL)] (V.V ⧸ V.L.T)) (hφ : ∀ g y, φ (actT Y.L g y) = actD V.L g (φ y))
    (f : ↥(GK K) → ↥Y.L.T) (hf : ∀ g h, f (g * h) = f g + actT Y.L g (f h))
    (hfl : ∀ (n : ℕ) (g : ↥(GK K)), ∀ᶠ h in nhds g, ∃ y : ↥Y.L.T, f h - f g = (l ^ n : ℕ) • y)
    (one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0)) (hone : (one : WCb l) = 1)
    (hcob : letI := zlMod LL Y
      IsCob (repQ (D.locA l) (Gj K s) ((actTZ LL Y).comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1))
        (fun g => (l : ℤ_[l]) ^ N • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]]
          (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1))))) :
    (fun g => (l ^ cTB l s e (padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) -
      padicValNat l (Module.finrank ℚ_[l] ↥K.1)) N : ℕ) • φ (f g)) ∈ HfD ((D.loc l).PD K) V.L := by
  letI := zlMod LL Y
  choose n w hw hw' hwc using GlobalTheory.Cyc.LatBasis.exists_basis l ↥(GK K) LL V
  choose m u hu hu' huc using GlobalTheory.Cyc.LatBasis.exists_basis l ↥(GK K) LL Y
  choose Φ ψ r hΦ hψ hψr using exists_coords (l := l) (LL := ↥LL.1) (O := ↥(OL LL)) (fun _ => rfl) Y V φ w u hu
  have hV' : ∀ (g : ↥(GK K)) (x : V.V),
      V.ρ g x = (((D.loc l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • x := fun g x => by
    rw [hV, (D.loc l).PD_χ, ← map_inv₀, ← map_pow, algebraMap_smul, zpow_neg, zpow_natCast,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow]
  have hΦ' := lift_equivariant Y V φ hφ Φ hΦ
  have key := mem_HfD_of_isCob D h2 h4 K LL s hs hK hle e N r ↥Y.L.T (actTZ LL Y) f hf hfl one hone
    hcob V hV' w hw hwc Φ hΦ' ψ hψ hψr
  have h3 := fun a b g => pow_smul_eq_mk V.L.T l a b _ _ (hΦ (f g))
  rw [cTB, funext (h3 _ _)]
  exact key

set_option maxHeartbeats 800000 in

theorem class_bound : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBat S E := by
  intro D HW F hA l _ K s LL h S E e M0 h0 Yt Y Z Ve ι π hses _ hZ _ hVe hcr hW yt hyt _ φ hφ f hf
  obtain ⟨-, h2, -, h4, h5, -, h7, -, -⟩ := hA
  have hK : K.1 ≤ Ks K s := h.2.2.1
  have hle : Gj K s ≤ GK K := fun _ hg x => hg ⟨x.1, hK x.2⟩
  let one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0) := ⟨1, 1, (AinfSub l).one_mem, by simp⟩
  have hone : (one : WCb l) = 1 := rfl
  obtain ⟨hc1, hc2⟩ := GlobalTheory.ConnCoc.conn l ↥(GK K) LL Y Yt ι hses.1 yt f hf
  letI := zlMod LL Y
  have hcoc := GlobalTheory.TensorOneCoc.isCoc_tmul_one l (D.loc l) (D.locA l) (Gj K s) ↥Y.L.T
    ((actTZ LL Y).comp (Subgroup.inclusion hle)) ((e : ℤ) + 1)
    (fun g => f (Subgroup.inclusion hle g))
    (fun g g' => hc1 (Subgroup.inclusion hle g) (Subgroup.inclusion hle g'))
    (fun n g => (continuous_inclusion hle).continuousAt.eventually
      (hc2 n (Subgroup.inclusion hle g))) one hone
  have htor := GlobalTheory.T.ses_lattice_trivial_quotient D HW F h5 h7 l K s LL h e Yt Y Z ι π hle hses hZ hcr yt hyt f hf
    one hone
  have hcob := GlobalTheory.T.torsion_bound_of_weight_hyp D HW F h5 h7 l K s LL h Y M0 h0 0 ((e : ℤ) + 1) hle (by omega) hW _
    hcoc htor
  have key := mem_HfD_of_lattice D h2 h4 K LL s ⟨h.1, h.2.1⟩ hK hle e _ Y Ve hVe φ hφ f hc1 hc2
    one hone hcob
  have hl : ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  have hg : gK S = padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) -
      padicValNat l (Module.finrank ℚ_[l] ↥K.1) := by
    rw [gK, hl, hs]; rfl
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [cTBY, hg, hl, hs]
  exact key

end GlobalTheory.Cyc.ClassBound
