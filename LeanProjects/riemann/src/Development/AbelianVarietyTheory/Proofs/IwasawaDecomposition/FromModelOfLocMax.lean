import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGeneratingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.LineNorm.Glue

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def IsChart (N : TrueGeo.Model Y) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) (D : ℕ) (W : N.X.Opens)
    (r : Y.Fnˣ) : Prop :=
  (∀ y, N.j y ∈ W → (D • Δ).IsEqn y r) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X),
      spMap e.O.subtype ≫ yt = y.1 ≫ N.j → ⊤ ≤ yt ⁻¹ᵁ W →
      (D : ℝ) * φ v e y = Real.log (e.w (valAt y.1 (((t (below y.1))⁻¹ ^ D * r : Y.Fnˣ) : Y.Fn)))

variable {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y}

theorem below_mem (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W) :
    N.j (below y.1) ∈ W := by
  change (y.1 ≫ N.j) _ ∈ W
  rw [← h]
  exact hW (x := spMap e.O.subtype _) trivial

theorem unitAt_of_isEqn (ht : ∀ y, Δ.IsEqn y (t y)) {D : ℕ} {y : Y.X} {r : Y.Fnˣ} :
    (D • Δ).IsEqn y r ↔ UnitAt y (((t y)⁻¹ ^ D * r : Y.Fnˣ) : Y.Fn) := by
  rw [((ht y).nsmul D).iff_unitAt, inv_pow, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_inv_mul]

theorem IsChart.pull {N N' : TrueGeo.Model Y} {D : ℕ} {W : N.X.Opens} {r : Y.Fnˣ} (h : IsChart N Δ t φ D W r)
    (π : N'.X ⟶ N.X) (hπ : N'.j ≫ π = N.j) : IsChart N' Δ t φ D (π ⁻¹ᵁ W) r := by
  refine ⟨fun y hy => h.1 y ?_, fun v e y yt hc hW => h.2 v e y (yt ≫ π) ?_ hW⟩
  · rw [← hπ]; exact hy
  · rw [← Category.assoc, hc, Category.assoc, hπ]

theorem IsChart.pow (ht : ∀ y, Δ.IsEqn y (t y)) {N : TrueGeo.Model Y} {D : ℕ} {W : N.X.Opens} {r : Y.Fnˣ}
    (h : IsChart N Δ t φ D W r) (k : ℕ) : IsChart N Δ t φ (D * k) W (r ^ k) := by
  refine ⟨fun y hy => ?_, fun v e y yt hc hW => ?_⟩
  · rw [mul_nsmul]; exact (h.1 y hy).nsmul k
  · have hu := (unitAt_of_isEqn ht).1 (h.1 _ (below_mem N hc hW))
    rw [pow_mul, ← mul_pow, Units.val_pow_eq_pow_val, valAt_pow hu.regAt, map_pow, Real.log_pow,
      ← h.2 v e y yt hc hW]
    push_cast
    ring

theorem hom_unique {N M : TrueGeo.Model Y} {f g : N.X ⟶ M.X} (hf : N.j ≫ f = M.j) (hg : N.j ≫ g = M.j) : f = g := by
  have := N.ar.isIntegral
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsDominant N.j := ⟨(dense_iff_closure_eq.2 (genericPoint_spec N.X)).mono
    (Set.singleton_subset_iff.2 ⟨_, ((j_gen_specializes N).antisymm (genericPoint_specializes _)).eq⟩)⟩
  refine ext_of_isDominant_of_isSeparated M.p (ext_of_isDominant N.j ?_) N.j (hf.trans hg.symm)
  rw [← Category.assoc, ← Category.assoc, hf, hg]

theorem exists_normal_dominating_finset {ι : Type} (M : TrueGeo.Model Y) (N : ι → TrueGeo.Model Y) (S : Finset ι) :
    ∃ (P : TrueGeo.Model Y) (π : P.X ⟶ M.X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme P.X ∧ P.j ≫ π = M.j ∧
      ∀ a ∈ S, ∃ ρ : P.X ⟶ (N a).X, P.j ≫ ρ = (N a).j := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨P, π, -, hP, -, -, h, -⟩ := ModelDom.exists_normal_dominating F Y M M
    exact ⟨P, π, hP, h, by simp⟩
  | insert a S _ ih =>
    obtain ⟨P, π, -, h, hS⟩ := ih
    obtain ⟨Q, σ, τ, hQ, -, -, h₁, h₂, -⟩ := ModelDom.exists_normal_dominating F Y P (N a)
    refine ⟨Q, σ ≫ π, hQ, by rw [← Category.assoc, h₁, h], fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact ⟨τ, h₂⟩
    · obtain ⟨ρ, hρ⟩ := hS b hb
      exact ⟨σ ≫ ρ, by rw [← Category.assoc, h₁, hρ]⟩

theorem w_le_one (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W)
    (g : Γ(N.X, W)) (hg : genericPoint Y.X ∈ N.j ⁻¹ᵁ W) :
    e.w (valAt y.1 (fnOf (N.j ⁻¹ᵁ W) hg (N.j.app W g))) ≤ 1 := by
  have hb : below y.1 ∈ N.j ⁻¹ᵁ W := below_mem N h hW
  have ht : ⊤ ≤ y.1 ⁻¹ᵁ (N.j ⁻¹ᵁ W) := fun p _ => by
    change (y.1 ≫ N.j) p ∈ W
    rw [← h]
    exact hW (x := spMap e.O.subtype p) trivial
  have hev := OfModel.eval_pull e.O.subtype N.j y.1 yt h (U := W) (W := N.j ⁻¹ᵁ W) le_rfl ht hW g
  rw [OfModel.valAt_fnOf _ hb ht, Scheme.Hom.app_eq_appLE, hev, ← e.mem_O]
  exact Subtype.prop _

theorem isChart_of_dvd (ht : ∀ y, Δ.IsEqn y (t y)) {M N : TrueGeo.Model Y} (π : N.X ⟶ M.X) (hπ : N.j ≫ π = M.j)
    {V : M.X.Opens} {d n : ℕ} {s : Fin n → Y.Fn} (hs : Generates M t V d s)
    (hφ : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ V →
      (d : ℝ) * φ v e y = Real.log (⨆ i, e.w (valAt y.1 (s i * (((t (below y.1))⁻¹ ^ d : Y.Fnˣ) : Y.Fn)))))
    {i : Fin n} {W : N.X.Opens} (hi : s i ≠ 0)
    (hg : ∀ k, ∃ g : Γ(N.X, W), ∀ h : genericPoint Y.X ∈ N.j ⁻¹ᵁ W,
      fnOf (N.j ⁻¹ᵁ W) h (N.j.app W g) * s i = s k) :
    IsChart N Δ t φ d (W ⊓ π ⁻¹ᵁ V) (Units.mk0 (s i) hi) := by
  have hV (y : Y.X) (hy : N.j y ∈ W ⊓ π ⁻¹ᵁ V) : M.j y ∈ V := by rw [← hπ]; exact hy.2
  have e₀ (y : Y.X) : (((t y)⁻¹ ^ d * Units.mk0 (s i) hi : Y.Fnˣ) : Y.Fn) =
      s i * (((t y)⁻¹ ^ d : Y.Fnˣ) : Y.Fn) := by rw [Units.val_mul, mul_comm]; rfl
  refine ⟨fun y hy => (unitAt_of_isEqn ht).2 ?_, fun v e y yt hc hW => ?_⟩
  · obtain ⟨h₁, k, hk⟩ := hs y (hV y hy)
    obtain ⟨g, hg⟩ := hg k
    have hy' : y ∈ N.j ⁻¹ᵁ W := hy.1
    obtain ⟨a, ha⟩ := regAt_fnOf hy' (gen_mem hy') (N.j.app W g)
    obtain ⟨b, hb⟩ := h₁ i
    obtain ⟨c, hu, hc⟩ := hk
    rw [← hg (gen_mem hy'), mul_assoc, ← ha, ← hb, ← map_mul] at hc
    obtain rfl := IsFractionRing.injective (Y.X.presheaf.stalk y) Y.X.functionField hc
    rw [e₀]
    exact ⟨b, isUnit_of_mul_isUnit_right hu, hb⟩
  · have hb := below_mem N hc hW
    have hb' : below y.1 ∈ N.j ⁻¹ᵁ W := hb.1
    rw [hφ v e y (yt ≫ π) (by rw [← Category.assoc, hc, Category.assoc, hπ]) (fun p hp => (hW hp).2), e₀]
    congr 1
    have : Nonempty (Fin n) := ⟨i⟩
    refine le_antisymm (ciSup_le fun k => ?_) (le_ciSup (f := fun k =>
      e.w (valAt y.1 (s k * (((t (below y.1))⁻¹ ^ d : Y.Fnˣ) : Y.Fn)))) (Finite.bddAbove_range _) i)
    obtain ⟨g, hg⟩ := hg k
    rw [← hg (gen_mem hb'), mul_assoc, valAt_mul (regAt_fnOf hb' _ _) ((hs _ (hV _ hb)).1 i), map_mul]
    exact mul_le_of_le_one_left (e.w.nonneg _) (w_le_one N hc (fun p hp => (hW hp).1) g _)

theorem IsChart.w_div_le (ht : ∀ y, Δ.IsEqn y (t y)) {N : TrueGeo.Model Y} {D : ℕ} {W W' : N.X.Opens}
    {r r' : Y.Fnˣ} (h : IsChart N Δ t φ D W r) (h' : IsChart N Δ t φ D W' r')
    {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y} {yt : Sp e.O ⟶ N.X}
    (hc : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) (hW : ⊤ ≤ yt ⁻¹ᵁ (W ⊓ W')) :
    e.w (valAt y.1 ((r : Y.Fn) / (r' : Y.Fn))) ≤ 1 := by
  have hb := below_mem N hc hW
  have e₁ := h.1 _ hb.1
  have e₂ := h'.1 _ hb.2
  have u₁ := (unitAt_of_isEqn ht).1 e₁
  have u₂ := (unitAt_of_isEqn ht).1 e₂
  have u₃ := e₂.iff_unitAt.1 e₁
  have p₁ := e.w.pos (valAt_ne_zero u₁)
  have p₂ := e.w.pos (valAt_ne_zero u₂)
  have q := Real.log_injOn_pos p₁ p₂ ((h.2 v e y yt hc fun p hp => (hW hp).1).symm.trans
    (h'.2 v e y yt hc fun p hp => (hW hp).2))
  have e₃ : (((t (below y.1))⁻¹ ^ D * r : Y.Fnˣ) : Y.Fn) =
      (r : Y.Fn) / (r' : Y.Fn) * (((t (below y.1))⁻¹ ^ D * r' : Y.Fnˣ) : Y.Fn) := by
    rw [Units.val_mul, Units.val_mul, mul_left_comm, div_mul_cancel₀ _ r'.ne_zero]
  rw [e₃, valAt_mul u₃.regAt u₂.regAt, map_mul] at q
  exact ((mul_eq_right₀ p₂.ne').1 q).le

theorem fromModel_of_charts (ht : ∀ y, Δ.IsEqn y (t y)) (N : TrueGeo.Model Y)
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X) (D : ℕ+)
    (h : ∀ x : N.X, ∃ (W : N.X.Opens) (r : Y.Fnˣ), x ∈ W ∧ IsChart N Δ t φ D W r) : FromModel Y Δ t φ := by
  have := N.ar.isIntegral
  choose W r hx hch using h
  obtain ⟨ρ, hρ₁, hρ₂, -, hρ₄, -⟩ := ModelFn.main F Y N
  have hreg (a b : N.X) : ∀ x ∈ W a ⊓ W b, RegAt x (ρ.symm ((r a : Y.Fn) / (r b : Y.Fn))) :=
    GlobalTheory.T.regular_of_valuation_bounded_at_points F Y N hN _ _ fun v e y yt hc hW => by
      rw [hρ₄, RingEquiv.apply_symm_apply]
      exact (hch a).w_div_le ht (hch b) hc hW
  have hne (a b : N.X) : ρ.symm ((r a : Y.Fn) / (r b : Y.Fn)) ≠ 0 :=
    (map_ne_zero _).2 (div_ne_zero (r a).ne_zero (r b).ne_zero)
  have hunit (a b : N.X) : ∀ x ∈ W a ⊓ W b, UnitAt x (ρ.symm ((r a : Y.Fn) / (r b : Y.Fn))) := fun x hx =>
    (unitAt_iff (hne a b)).2 ⟨hreg a b x hx, by
      rw [← map_inv₀, inv_div]
      exact hreg b a x ⟨hx.2, hx.1⟩⟩
  choose g hg using fun a b => exists_unit_fnOf_eq (hunit a b)
  let L : LB N.X := { ι := N.X, U := W, g := g }
  have hL : L.IsLB := by
    refine ⟨eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩, fun i => Units.ext (Cartier.fn_ext fun h => ?_),
      fun i j k => Units.ext (Cartier.fn_ext fun h => ?_)⟩
    · rw [LB.val_res, fnOf_resG, Units.val_one, map_one]
      refine (hg i i _).trans ?_
      rw [div_self (Units.ne_zero _), map_one]
    · simp only [Units.val_mul, map_mul, LB.val_res, fnOf_resG]
      refine (congrArg₂ (· * ·) (hg i j _) (hg j k _)).trans (Eq.trans ?_ (hg i k _).symm)
      rw [← map_mul, div_mul_div_cancel₀ (Units.ne_zero _)]
  refine ⟨N, L, D, fun i => r (i PUnit.unit), hL, ⟨LB.isLB_pull hL N.j, fun i i' hii => ?_,
    fun i y hy => (hch _).1 y (Set.mem_iInter.1 hy PUnit.unit)⟩, fun v e y yt i hc hW => (hch _).2 v e y yt hc hW⟩
  have l : (L.pull N.j).U i ⊓ (L.pull N.j).U i' ≤ N.j ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (i' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hp : ((L.pull N.j).g i i').val =
      resG Y.X l (N.j.app _ (L.g (i PUnit.unit) (i' PUnit.unit)).val) := by
    have : (L.pull N.j).g i i' = res l (pullU N.j _ (L.g (i PUnit.unit) (i' PUnit.unit))) := by
      change ∏ _k : PUnit, _ = _
      exact (Fintype.prod_unique _).trans (zpow_one _)
    rw [this]
    rfl
  have hU : genericPoint N.X ∈ L.U (i PUnit.unit) ⊓ L.U (i' PUnit.unit) := hρ₂ ▸ l hii
  rw [hp, fnOf_resG, ← hρ₁ _ hU]
  have := congrArg ρ (hg (i PUnit.unit) (i' PUnit.unit) hU)
  rw [RingEquiv.apply_symm_apply] at this
  exact ((congrArg (· * _) this).trans (div_mul_cancel₀ _ (Units.ne_zero _))).symm

theorem fromModel_of_locMax : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : GlobalTheory.TrueGeo.Model Y) (Δ : Y.Dv)
    (t : Y.X → Y.Fnˣ) (φ : PtFn Y), (∀ y, Δ.IsEqn y (t y)) → (∀ z, LocMax M t φ z) → FromModel Y Δ t φ := by
  intro F _ _ Y M Δ t φ ht h
  classical
  choose V d n s hz hs hφ using h
  choose N π V' hπ _ hz' hle hN using fun z => GlobalTheory.T.exists_model_refinement_generating F Y M Δ t (V z) (d z) (n z) (s z) z ht (hz z) (hs z)
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : CompactSpace M.X := QuasiCompact.compactSpace_of_compactSpace M.p
  obtain ⟨S, hS⟩ := CompactSpace.elim_nhds_subcover (fun z => (V' z : Set M.X))
    fun z => (V' z).isOpen.mem_nhds (hz' z)
  obtain ⟨P, σ, hP, hσ, hdom⟩ := exists_normal_dominating_finset M N S
  refine fromModel_of_charts ht P hP (∏ a ∈ S, d a) fun x => ?_
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hS.ge (Set.mem_univ (σ x)))
  obtain ⟨τ, hτ⟩ := hdom a ha
  obtain rfl : σ = τ ≫ π a := hom_unique hσ (by rw [← Category.assoc, hτ, hπ])
  obtain ⟨i, W, hxW, hi, hg⟩ := hN a (τ x) hxa
  have hc := ((isChart_of_dvd ht (π a) (hπ a) (hs a) (hφ a) hi hg).pow ht
    ((∏ b ∈ S.erase a, d b : ℕ+) : ℕ)).pull τ hτ
  rw [← PNat.mul_coe, Finset.mul_prod_erase S d ha] at hc
  exact ⟨_, _, show τ x ∈ W ⊓ π a ⁻¹ᵁ V a from ⟨hxW, hle a hxa⟩, hc⟩

end GlobalTheory.LineNorm.Glue
