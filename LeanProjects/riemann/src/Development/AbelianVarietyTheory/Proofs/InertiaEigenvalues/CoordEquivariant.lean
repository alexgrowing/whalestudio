import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAdicModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateBasisOfIsDecompletionAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleTwistCoboundaryOnBallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompletionFrameOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiGradedPieceIsoTwistedOCStatement

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Topology Filter TensorProduct Matrix

namespace GlobalTheory.Cyc.GradedTorsion

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_eq (q : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) q = ((algebraMap ℚ_[l] (Om l) q : Om l) : PadicComplex l) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) q

theorem act_zC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (z : ℤ_[l]) : act g (zC z) = zC z := by
  rw [zC, algebraMap_eq, ha.1, AlgEquiv.commutes]

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  have h : (l : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h, algebraMap_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem zC_add (x y : ℤ_[l]) : zC (x + y) = zC x + zC y := by simp [zC]

theorem zC_mul (x y : ℤ_[l]) : zC (x * y) = zC x * zC y := by simp [zC]

theorem zC_sum {ι : Type} (s : Finset ι) (f : ι → ℤ_[l]) : zC (∑ j ∈ s, f j) = ∑ j ∈ s, zC (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, zC_add, ih]

theorem zC_pow_l (k : ℕ) : zC ((l : ℤ_[l]) ^ k) = (l : PadicComplex l) ^ k := by simp [zC]

theorem mulVec_mem_ball {d : ℕ} {A : Matrix (Fin d) (Fin d) (PadicComplex l)}
    (hA : ∀ a b, ‖A a b‖ ≤ 1) {y : Fin d → PadicComplex l} (hy : y ∈ ball l d) :
    A *ᵥ y ∈ ball l d := by
  intro a
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun b _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA a b) (norm_nonneg _) (hy b)

theorem twAct_smul_nat (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (i : ℤ) {d : ℕ} (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (σ : GQ l) (n : ℕ)
    (y : Fin d → PadicComplex l) :
    twAct act χ i U σ ((n : PadicComplex l) • y) = (n : PadicComplex l) • twAct act χ i U σ y := by
  have : (fun a => act σ (((n : PadicComplex l) • y) a)) =
      (n : PadicComplex l) • fun a => act σ (y a) := by
    funext a; simp
  simp only [twAct]
  rw [this, Matrix.mulVec_smul, smul_comm]

theorem twAct_mulVec (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (i : ℤ) {d : ℕ} (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (σ : GQ l) (h : D * U σ = M σ * D.map (act σ))
    (y : Fin d → PadicComplex l) :
    twAct act χ i M σ (D *ᵥ y) = D *ᵥ twAct act χ i U σ y := by
  have : (fun a => act σ ((D *ᵥ y) a)) = D.map (act σ) *ᵥ fun a => act σ (y a) := by
    funext a; simp [Matrix.mulVec, dotProduct]
  simp only [twAct]
  rw [this, Matrix.mulVec_mulVec, ← h, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

theorem sandwich {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    {K : FinExt l} {m d : ℕ} {M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)}
    {D : Matrix (Fin d) (Fin d) (PadicComplex l)} {g : GQ l} (hD : IsDec act χ K m M D U g)
    (i : ℤ) (n : ℕ)
    (hU : ∀ (c : GQ l → Fin d → PadicComplex l) (k : ℕ),
      CocOn (Gj K m) (twAct act χ i U) (ball l d) c →
      CobOn (Gj K m) (twAct act χ i U) (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ) →
      CobOn (Gj K m) (twAct act χ i U) (ball l d) (fun σ => (l : PadicComplex l) ^ n • c σ))
    (c : GQ l → Fin d → PadicComplex l) (k : ℕ)
    (hc : CocOn (Gj K m) (twAct act χ i M) (ball l d) c)
    (hk : CobOn (Gj K m) (twAct act χ i M) (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ)) :
    CobOn (Gj K m) (twAct act χ i M) (ball l d) (fun σ => (l : PadicComplex l) ^ (n + 1) • c σ) := by
  obtain ⟨hdet, hint, hinv, -, hcomm⟩ := hD
  set E : Matrix (Fin d) (Fin d) (PadicComplex l) := (l : PadicComplex l) • D⁻¹ with hE
  have hEint : ∀ a b, ‖E a b‖ ≤ 1 := fun a b => by simpa [hE] using hinv a b
  have hDE : ∀ y, D *ᵥ (E *ᵥ y) = (l : PadicComplex l) • y := fun y => by
    rw [Matrix.mulVec_mulVec, hE, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hinj : Function.Injective D.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det D).2 hdet)
  have hEt : ∀ σ ∈ Gj K m, ∀ y, twAct act χ i U σ (E *ᵥ y) = E *ᵥ twAct act χ i M σ y := by
    intro σ hσ y
    apply hinj
    show D *ᵥ _ = D *ᵥ _
    rw [← twAct_mulVec act χ i M U D σ (hcomm σ hσ), hDE, hDE, twAct_smul_nat]
  obtain ⟨x, hx, hxe⟩ := hU (fun σ => E *ᵥ c σ) k
    ⟨(continuous_const.matrix_mulVec continuous_id).comp_continuousOn hc.1,
      fun σ hσ => mulVec_mem_ball hEint (hc.2.1 σ hσ), fun σ hσ τ hτ => by
        simp only [hc.2.2 σ hσ τ hτ, Matrix.mulVec_add, hEt σ hσ]⟩
    (by
      obtain ⟨x, hx, hxe⟩ := hk
      refine ⟨E *ᵥ x, mulVec_mem_ball hEint hx, fun σ hσ => ?_⟩
      have := hxe σ hσ
      simp only at this ⊢
      rw [hEt σ hσ, ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul])
  refine ⟨D *ᵥ x, mulVec_mem_ball hint hx, fun σ hσ => ?_⟩
  have := hxe σ hσ
  simp only at this ⊢
  rw [twAct_mulVec act χ i M U D σ (hcomm σ hσ), ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul,
    hDE, smul_smul, pow_succ]

theorem transfer {G : Subgroup (GQ l)} {X : Type} [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] ↥G X) {d : ℕ}
    (A : GQ l → (Fin d → PadicComplex l) → (Fin d → PadicComplex l))
    (Ψ : X →+ (Fin d → PadicComplex l)) (hinj : Function.Injective Ψ)
    (hr : Set.range Ψ = ball l d)
    (hl : ∀ (k : ℕ) x, Ψ ((l : ℤ_[l]) ^ k • x) = (l : PadicComplex l) ^ k • Ψ x)
    (hA : ∀ (g : ↥G) x, Ψ (ρ g x) = A g (Ψ x)) (n : ℕ)
    (H : ∀ (c : GQ l → Fin d → PadicComplex l) (k : ℕ), CocOn G A (ball l d) c →
      CobOn G A (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ) →
      CobOn G A (ball l d) (fun σ => (l : PadicComplex l) ^ n • c σ)) :
    @TorsKilledBy ℤ_[l] ↥G X _ _ _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology X) ρ
      (l : ℤ_[l]) ((l : ℤ_[l]) ^ n) := by
  classical
  rintro f ⟨hfc, hfm⟩ ⟨k, x, hx⟩
  rw [continuous_adicModule_iff] at hfc
  have hb : ∀ y, Ψ y ∈ ball l d := fun y => hr ▸ ⟨y, rfl⟩
  let c : GQ l → Fin d → PadicComplex l := fun σ => if h : σ ∈ G then Ψ (f ⟨σ, h⟩) else 0
  have hc : ∀ σ (h : σ ∈ G), c σ = Ψ (f ⟨σ, h⟩) := fun σ h => dif_pos h
  have hcont : Continuous fun g : ↥G => Ψ (f g) := by
    rw [continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt (l := l))
    filter_upwards [hfc g N] with h hh
    obtain ⟨y, e⟩ := hh
    rw [dist_eq_norm, ← map_sub, e, hl, norm_smul, norm_pow]
    refine lt_of_le_of_lt ?_ hN
    exact mul_le_of_le_one_right (by positivity) ((pi_norm_le_iff_of_nonneg zero_le_one).2 (hb y))
  obtain ⟨y, hy, hye⟩ := H c k
    ⟨by
      rw [continuousOn_iff_continuous_domRestrict]
      convert hcont using 1
      funext g
      exact hc g g.2,
    fun σ hσ => by rw [hc σ hσ]; exact hb _,
    fun σ hσ τ hτ => by
      rw [hc σ hσ, hc τ hτ, hc _ (G.mul_mem hσ hτ)]
      have := hfm ⟨σ, hσ⟩ ⟨τ, hτ⟩
      rw [← hA ⟨σ, hσ⟩, ← map_add, ← this]
      rfl⟩
    ⟨Ψ x, hb x, fun σ hσ => by
      have := hx ⟨σ, hσ⟩
      simp only [Pi.smul_apply] at this
      simp only
      rw [hc σ hσ, ← hl, this, map_sub, hA]⟩
  rw [← hr] at hy
  obtain ⟨z, rfl⟩ := hy
  refine ⟨z, fun g => hinj ?_⟩
  have := hye g g.2
  simp only at this
  rw [Pi.smul_apply, hl, map_sub, hA, ← this, hc g g.2]

theorem exists_coord {T Q : Type} [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup Q]
    [Module ℤ_[l] Q] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] T) (Φ : Q →+ PadicComplex l)
    (hinj : Function.Injective Φ) (hr : Set.range Φ = {y | ‖y‖ ≤ 1})
    (hz : ∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) :
    ∃ Ψ : T ⊗[ℤ_[l]] Q →+ (Fin d → PadicComplex l), Function.Injective Ψ ∧
      Set.range Ψ = ball l d ∧ (∀ (z : ℤ_[l]) x, Ψ (z • x) = zC z • Ψ x) ∧
      ∀ t q a, Ψ (t ⊗ₜ q) a = zC (b.repr t a) * Φ q := by
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := Q) b
  refine ⟨⟨⟨fun x a => Φ (e x a), ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · funext a; simp
  · intro x y; funext a; simp
  · intro x y hxy
    apply e.injective
    ext a
    exact hinj (congrFun hxy a)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩ a
      exact (hr ▸ ⟨_, rfl⟩ : Φ (e x a) ∈ {y : PadicComplex l | ‖y‖ ≤ 1})
    · intro hy
      have : ∀ a, ∃ q, Φ q = y a := fun a =>
        (hr.symm ▸ hy a : y a ∈ Set.range Φ)
      choose q hq using this
      refine ⟨e.symm (Finsupp.equivFunOnFinite.symm q), ?_⟩
      funext a
      simp [hq]
  · intro z x
    funext a
    simp [hz]
  · intro t q a
    simp [e, hz]

theorem coord_equivariant {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {T Q : Type} [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup Q]
    [Module ℤ_[l] Q] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] T) (Φ : Q →+ PadicComplex l)
    (Ψ : T ⊗[ℤ_[l]] Q →+ (Fin d → PadicComplex l))
    (hΨ : ∀ t q a, Ψ (t ⊗ₜ q) a = zC (b.repr t a) * Φ q)
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (r : T →ₗ[ℤ_[l]] T)
    (s : Q →ₗ[ℤ_[l]] Q) (hM : ∀ a j, M g a j = zC (b.repr (r (b j)) a))
    (hs : ∀ x, Φ (s x) = chiC χ i g * act g (Φ x)) (x : T ⊗[ℤ_[l]] Q) :
    Ψ (TensorProduct.map r s x) = twAct act χ i M g (Ψ x) := by
  induction x using TensorProduct.induction_on with
  | zero => funext a; simp [twAct, Matrix.mulVec, dotProduct]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    funext a
    simp [twAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  | tmul t q =>
    funext a
    have h1 : b.repr (r t) a = ∑ j, b.repr (r (b j)) a * b.repr t j := by
      conv_lhs => rw [← b.sum_repr t, map_sum, map_sum, Finsupp.finsetSum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    simp only [TensorProduct.map_tmul, hΨ, twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, map_mul, act_zC ha, hM, hs, h1, zC_sum, zC_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

theorem rI_eq (l m : ℕ) (J : Finset ℤ) (i : ℤ) :
    rI l m (J : Set ℤ) i = ∑ u ∈ J.erase i, (m + padicValInt l (u - i)) := by
  rw [rI, ← finsum_mem_finset_eq_sum]
  refine finsum_congr fun u => ?_
  by_cases h1 : u ∈ J <;> by_cases h2 : u = i <;> simp [h1, h2, vZ]

theorem of_basis (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l)
    {T : Type} [AddCommGroup T] [Module ℤ_[l] T] (m : ℕ) (hlev : Lev l m)
    (ρ : ↥(Gj K m) →* (T →ₗ[ℤ_[l]] T)) (i : ℤ)
    (J : Set ℤ) (hfin : J.Finite) {d : ℕ} {M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)}
    (b : Module.Basis (Fin d) ℤ_[l] T)
    (hb : ∀ (σ : ↥(Gj K m)) a j, M σ a j = zC (b.repr (ρ σ (b j)) a))
    {Dm : Matrix (Fin d) (Fin d) (PadicComplex l)} {g : GQ l}
    (hD : IsDec AI.actC P.χQ K m M Dm U g) (hHT : HTBasis AI.actC P.χQ (Gj K m) M J) :
    @TorsKilledBy ℤ_[l] _ _ _ _ _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology _)
      (repQ AI (Gj K m) ρ i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (2 + max 1 (rI l m J i))) := by
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hHT' := GlobalTheory.T.hodgeTateBasis_of_isDecompletionAtLevel l _ _ ha hχ K _ d M U Dm g _ hD hHT
  have hJ : J = (hfin.toFinset : Set ℤ) := hfin.coe_toFinset.symm
  have hc6 := GlobalTheory.T.cocycle_twist_coboundary_on_ball l _ _ ha hχ K _ d hlev U g hD.2.2.2.1 hfin.toFinset (hJ ▸ hHT') i
  rw [← rI_eq, ← hJ] at hc6
  have hs := sandwich hD i _ hc6
  obtain ⟨Φ, hinj, hr, hz, hact⟩ := GlobalTheory.T.xiGradedPiece_iso_twistedOC l P AI i
  obtain ⟨Ψ, hΨi, hΨr, hΨz, hΨ⟩ := exists_coord b Φ hinj hr hz
  have hn : 2 + max 1 (rI l m J i) = 1 + max 1 (rI l m J i) + 1 := by omega
  rw [hn]
  refine transfer _ (twAct AI.actC P.χQ i M) Ψ hΨi hΨr
    (fun k x => by rw [hΨz, zC_pow_l]) (fun σ x => ?_) _ hs
  have hζ : (σ : GQ l) (P.ζQ 1) = P.ζQ 1 := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ ?_
    refine (le_sup_right : _ ≤ Ks K _) (IntermediateField.subset_adjoin _ _ ?_)
    show P.ζQ 1 ^ (l ^ m) = 1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlev.1
    have h1 : P.ζQ 1 ^ l = 1 := (P.ζQ_succ 0).trans P.ζQ_zero
    rw [pow_add, pow_one, pow_mul, h1, one_pow]
  exact coord_equivariant ha _ i b Φ Ψ hΨ M σ (ρ σ)
    (actQab (xiOK AI) i (i + 1) σ) (hb σ) (hact σ hζ) x

theorem torsion_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (i : ℤ) (hle : Gj K (mN l s (M0 + h0)) ≤ GK K), HypW S E T M0 h0 → letI := zlMod LL T; letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) i (i + 1))) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; TorsKilledBy (repQ (D.locA l) (Gj K (mN l s (M0 + h0))) ((actTZ LL T).comp (Subgroup.inclusion hle)) i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (2 + max 1 (rI l (mN l s (M0 + h0)) (Jset S T) i))) := by
  intro D HW F h7 l _ K s LL h S E T M0 h0 i hle hW
  have hsm : s ≤ mN l s (M0 + h0) := by unfold mN; omega
  have hlev : Lev l (mN l s (M0 + h0)) :=
    ⟨le_trans h.1 hsm, fun h2 => le_trans (h.2.1 h2) hsm⟩
  have h1 := (GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).1
  refine h1.elim fun d h1 => h1.elim fun M h1 => h1.elim fun A hM => ?_
  have h2 := GlobalTheory.T.exists_decompletion_frame_of_lattice D HW F l K s LL h T M0 h0 hW d M A hM
  refine h2.elim fun Dm h2 => h2.elim fun U h2 => h2.elim fun g hD => ?_
  have h3 := GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks D HW F h7 l K s LL h T hW.1 d M A hM _ hsm
  refine Exists.elim hM fun b hb => ?_
  exact @of_basis l _ (D.loc l) (D.locA l) K _ _ (zlMod LL T) _ hlev
    ((actTZ LL T).comp (Subgroup.inclusion hle)) i _ h3.1 d M U b
    (fun σ => hb.1 (Subgroup.inclusion hle σ)) Dm g hD.1 h3.2

end GlobalTheory.Cyc.GradedTorsion
