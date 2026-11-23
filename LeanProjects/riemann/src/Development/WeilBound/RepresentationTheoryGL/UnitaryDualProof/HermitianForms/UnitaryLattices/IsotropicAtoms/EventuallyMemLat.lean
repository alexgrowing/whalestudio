import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.InvSmulEqOfSmulEq

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir Filter Topology

namespace PositivityTheory.RgUd.Form.U.Atom

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lat

instance instNonemptyLat (m : ℕ) : Nonempty {A : AddSubgroup (Fin (m + 1) → k) // IsLat A} := by
  obtain ⟨A, h1, h2, -⟩ := exists_lat_mem (k := k) (m + 1) 0
  exact ⟨⟨A, h1, h2⟩⟩

instance instDirectedLat (m : ℕ) : IsDirected {A : AddSubgroup (Fin (m + 1) → k) // IsLat A} (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, isCompact_sup _ _ a.2.1 b.2.1, AddSubgroup.isOpen_mono le_sup_left a.2.2⟩,
    le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

theorem eventually_mem_lat (m : ℕ) (x : Fin (m + 1) → k) :
    ∀ᶠ A : {A : AddSubgroup (Fin (m + 1) → k) // IsLat A} in atTop, x ∈ A.1 := by
  obtain ⟨A, h1, h2, hx⟩ := exists_lat_mem (k := k) (m + 1) x
  exact eventually_atTop.2 ⟨⟨A, h1, h2⟩, fun B hB => hB hx⟩

theorem eventually_ge_lat (m : ℕ) (A₁ : AddSubgroup (Fin (m + 1) → k)) (h1 : IsLat A₁) :
    ∀ᶠ A : {A : AddSubgroup (Fin (m + 1) → k) // IsLat A} in atTop, A₁ ≤ A.1 :=
  eventually_atTop.2 ⟨⟨A₁, h1⟩, fun _ hB => hB⟩

end Lat

theorem nabs_pos (z : kˣ) : 0 < nabs k z := by
  unfold GlobalTheory.SplitWeil.nabs
  have e : MeasureTheory.distribHaarChar k z * MeasureTheory.distribHaarChar k z⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one e))

theorem nabs_one' : nabs k (1 : kˣ) = 1 := by
  simp [GlobalTheory.SplitWeil.nabs]

theorem bessel {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : IsPsd B) (x e : V)
    (h1 : B e e = B e x) (h2 : B x e = B e x) : (B e x).re ≤ (B x x).re := by
  have key : B x x = B e e + B (x - e) (x - e) := by
    have hx : x = e + (x - e) := by abel
    conv_lhs => rw [hx]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [h1, h2]
    ring
  rw [key, ← h1, Complex.add_re]
  linarith [hB.2 (x - e)]

section Common

variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem colInv (hB : MirEq π (m + 1) h s B) (x : Fin (m + 1) → k) (v w : V) :
    B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w := by
  have := hB (unip k (m + 1) (Multiplicative.ofAdd x)) (unip_mem_Mir m x) v w
  rw [det_unip, nabs_one', Real.one_rpow, Complex.ofReal_one, one_mul] at this
  exact this

theorem glInv (hB : MirEq π (m + 1) h s B) (g : GL (Fin (m + 1)) k) (v w : V) :
    B (π (blkAt k (m + 1) N (by omega) g) v) (π (blkAt k (m + 1) N (by omega) g) w) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * B v w := by
  have := hB (glEmb k (m + 1) g) (glEmb_mem_Mir' m g) v w
  rw [det_glEmb, blkAt_glEmb] at this
  exact this

local notation "P" => avg (1 : AddChar k Circle) h π 0

theorem one_zero_dot (a : Fin (m + 1) → k) : (1 : AddChar k Circle) ((0 : Fin (m + 1) → k) ⬝ᵥ a) = 1 := by
  simp

variable (hπ : IsSmooth π)
include hπ

theorem P_add {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v w : V) : P A (v + w) = P A v + P A w :=
  avg_add h π 1 continuous_one_char hπ 0 hA v w

theorem P_smul {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (c : ℂ) (v : V) : P A (c • v) = c • P A v :=
  avg_smul h π 1 continuous_one_char hπ 0 hA c v

theorem wirtinger_sub {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v w : V) : P A (v - w) = P A v - P A w := by
  rw [sub_eq_add_neg, P_add hπ hA, ← neg_one_smul ℂ w, P_smul hπ hA, neg_one_smul, ← sub_eq_add_neg]

theorem P_mono {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hA' : IsLat A') (hAA' : A ≤ A') (v : V) :
    P A' (P A v) = P A' v := by
  have := avg_avg h π 1 continuous_one_char hπ 0 0 hA hA' hAA' v
  rw [this, if_pos (fun _ _ => rfl)]

theorem P_idem {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) : P A (P A v) = P A v :=
  P_mono hπ hA hA le_rfl v

theorem P_fix {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hA' : IsLat A') (hAA' : A ≤ A') (v : V) :
    P A (P A' v) = P A' v := by
  have := avg_eigen h π 1 continuous_one_char hπ 0 0 hA (P A' v) (fun a ha => by
    rw [colEl_avg h π 1 continuous_one_char hπ 0 hA' (hAA' ha)])
  rw [this, if_pos (fun _ _ => rfl)]

theorem P_colEl {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) {a : Fin (m + 1) → k} (ha : a ∈ A) (v : V) :
    P A (π (colEl k m N h a) v) = P A v := by
  rw [avg_colEl h π 1 continuous_one_char hπ 0 hA ha v, one_zero_dot, Circle.coe_one, one_smul]

theorem P_form (hB : MirEq π (m + 1) h s B) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v w : V) :
    B (P A v) w = B v (P A w) :=
  form_avg h π 1 continuous_one_char hπ B (colInv hB) 0 hA v w

theorem P_sq (hB : MirEq π (m + 1) h s B) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) :
    B (P A v) (P A v) = B (P A v) v := by
  rw [← P_form hπ hB hA, P_idem hπ hA]

end Common

section AtomCons

variable {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

local notation "P" => avg (1 : AddChar k Circle) h π 0
local notation "LT" => {A : AddSubgroup (Fin (m + 1) → k) // IsLat A}

variable (hπ : IsSmooth π) (hpsd : IsPsd B) (hB : MirEq π (m + 1) h s B)
include hπ hpsd hB

theorem q_im (A : LT) (v : V) : (B (P A.1 v) v).im = 0 := by
  have e := hpsd.1 (P A.1 v) (P A.1 v)
  rw [P_sq hπ hB A.2] at e
  have := congrArg Complex.im e
  rw [Complex.conj_im] at this
  linarith

theorem q_re_nonneg (A : LT) (v : V) : 0 ≤ (B (P A.1 v) v).re := by
  rw [← P_sq hπ hB A.2]
  exact hpsd.2 _

theorem q_anti (A A' : LT) (hle : A ≤ A') (v : V) : (B (P A'.1 v) v).re ≤ (B (P A.1 v) v).re := by
  have e1 : P A'.1 v = P A'.1 (P A.1 v) := (P_mono hπ A.2 A'.2 hle v).symm
  rw [← P_sq hπ hB A'.2 v, e1, P_sq hπ hB A'.2, ← P_sq hπ hB A.2 v]
  exact bessel B hpsd _ _ (P_sq hπ hB A'.2 _) (P_form hπ hB A'.2 _ _).symm

theorem q_le (A : LT) (v : V) : (B (P A.1 v) v).re ≤ (B v v).re :=
  bessel B hpsd _ _ (P_sq hπ hB A.2 _) (P_form hπ hB A.2 _ _).symm

omit hpsd hB in
theorem P_pol (A : LT) (v w : V) : B (P A.1 v) w =
    (B (P A.1 (v + w)) (v + w) - B (P A.1 (v - w)) (v - w) + Complex.I * B (P A.1 (v + Complex.I • w)) (v + Complex.I • w)
      - Complex.I * B (P A.1 (v - Complex.I • w)) (v - Complex.I • w)) / 4 := by
  rw [P_add hπ A.2, wirtinger_sub hπ A.2, P_add hπ A.2, wirtinger_sub hπ A.2, P_smul hπ A.2]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ,
    smul_eq_mul, Complex.conj_I]
  linear_combination (B (P A.1 v) w - B (P A.1 w) v) / 2 * Complex.I_sq

def ell (v : V) : ℝ := ⨅ A : LT, (B (P A.1 v) v).re

theorem tendsto_q (v : V) : Tendsto (fun A : LT => B (P A.1 v) v) atTop (𝓝 ((ell (h := h) (π := π) (B := B) v : ℝ) : ℂ)) := by
  have hT : Tendsto (fun A : LT => (B (P A.1 v) v).re) atTop (𝓝 (ell (h := h) (π := π) (B := B) v)) :=
    tendsto_atTop_ciInf (fun A A' hle => q_anti hπ hpsd hB A A' hle v)
      ⟨0, by rintro _ ⟨A, rfl⟩; exact q_re_nonneg hπ hpsd hB A v⟩
  have e : (fun A : LT => B (P A.1 v) v) = fun A => (((B (P A.1 v) v).re : ℝ) : ℂ) :=
    funext fun A => Complex.ext (by simp) (by simp [q_im hπ hpsd hB A v])
  rw [e]
  exact (Complex.continuous_ofReal.tendsto _).comp hT

def lim₀ (v w : V) : ℂ :=
  (((ell (h := h) (π := π) (B := B) (v + w) : ℝ) : ℂ) - (ell (h := h) (π := π) (B := B) (v - w) : ℝ)
    + Complex.I * (ell (h := h) (π := π) (B := B) (v + Complex.I • w) : ℝ)
    - Complex.I * (ell (h := h) (π := π) (B := B) (v - Complex.I • w) : ℝ)) / 4

theorem tendsto_lim₀ (v w : V) :
    Tendsto (fun A : LT => B (P A.1 v) w) atTop (𝓝 (lim₀ (h := h) (π := π) (B := B) v w)) := by
  have := ((((tendsto_q hπ hpsd hB (v + w)).sub (tendsto_q hπ hpsd hB (v - w))).add
    ((tendsto_q hπ hpsd hB (v + Complex.I • w)).const_mul Complex.I)).sub
    ((tendsto_q hπ hpsd hB (v - Complex.I • w)).const_mul Complex.I)).div_const 4
  exact this.congr fun A => (P_pol hπ A v w).symm

def atomForm : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (lim₀ (h := h) (π := π) (B := B))
    (fun v₁ v₂ w => tendsto_nhds_unique (tendsto_lim₀ hπ hpsd hB (v₁ + v₂) w)
      (((tendsto_lim₀ hπ hpsd hB v₁ w).add (tendsto_lim₀ hπ hpsd hB v₂ w)).congr fun A => by
        rw [P_add hπ A.2, map_add, LinearMap.add_apply]))
    (fun c v w => tendsto_nhds_unique (tendsto_lim₀ hπ hpsd hB (c • v) w)
      (((tendsto_lim₀ hπ hpsd hB v w).const_mul c).congr fun A => by
        rw [P_smul hπ A.2, map_smul, LinearMap.smul_apply, smul_eq_mul]))
    (fun v w₁ w₂ => tendsto_nhds_unique (tendsto_lim₀ hπ hpsd hB v (w₁ + w₂))
      (((tendsto_lim₀ hπ hpsd hB v w₁).add (tendsto_lim₀ hπ hpsd hB v w₂)).congr fun A => by
        rw [map_add]))
    (fun c v w => tendsto_nhds_unique (tendsto_lim₀ hπ hpsd hB v (c • w))
      (((tendsto_lim₀ hπ hpsd hB v w).const_mul (starRingEnd ℂ c)).congr fun A => by
        rw [map_smulₛₗ, smul_eq_mul]))

theorem atomForm_apply (v w : V) : atomForm hπ hpsd hB v w = lim₀ (h := h) (π := π) (B := B) v w := rfl

theorem isAtom_atomForm : IsAtom h π B (atomForm hπ hpsd hB) := fun v w => by
  rw [atomForm_apply]
  exact tendsto_lim₀ hπ hpsd hB v w

end AtomCons

theorem comap_comap_inv {m : ℕ} (g : GL (Fin (m + 1)) k) (A : AddSubgroup (Fin (m + 1) → k)) :
    (A.comap (Matrix.mulVecLin (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom).comap
      (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom = A := by
  ext x
  simp only [AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

section AtomProps

variable {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

local notation "P" => avg (1 : AddChar k Circle) h π 0
local notation "LT" => {A : AddSubgroup (Fin (m + 1) → k) // IsLat A}

variable (hπ : IsSmooth π) (hpsd : IsPsd B) (hB : MirEq π (m + 1) h s B)
include hπ hpsd hB

theorem atom_tendsto (v w : V) : Tendsto (fun A : LT => B (P A.1 v) w) atTop (𝓝 (atomForm hπ hpsd hB v w)) :=
  tendsto_lim₀ hπ hpsd hB v w

theorem atom_herm (v w : V) : atomForm hπ hpsd hB w v = starRingEnd ℂ (atomForm hπ hpsd hB v w) := by
  refine tendsto_nhds_unique (atom_tendsto hπ hpsd hB w v)
    (((Complex.continuous_conj.tendsto _).comp (atom_tendsto hπ hpsd hB v w)).congr fun A => ?_)
  simp only [Function.comp_apply]
  rw [P_form hπ hB A.2, hpsd.1 v (P A.1 w)]

theorem atom_nonneg (v : V) : 0 ≤ (atomForm hπ hpsd hB v v).re :=
  ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp (atom_tendsto hπ hpsd hB v v))
    fun A => q_re_nonneg hπ hpsd hB A v

theorem atom_le (v : V) : (atomForm hπ hpsd hB v v).re ≤ (B v v).re :=
  le_of_tendsto' ((Complex.continuous_re.tendsto _).comp (atom_tendsto hπ hpsd hB v v))
    fun A => q_le hπ hpsd hB A v

theorem atom_isPsd : IsPsd (atomForm hπ hpsd hB) :=
  ⟨atom_herm hπ hpsd hB, atom_nonneg hπ hpsd hB⟩

theorem atom_colEl (x : Fin (m + 1) → k) (v w : V) :
    atomForm hπ hpsd hB (π (colEl k m N h x) v) w = atomForm hπ hpsd hB v w := by
  refine tendsto_nhds_unique (atom_tendsto hπ hpsd hB _ w) ((atom_tendsto hπ hpsd hB v w).congr' ?_)
  filter_upwards [eventually_mem_lat m x] with A hA
  rw [P_colEl hπ A.2 hA]

theorem atom_colEl_right (x : Fin (m + 1) → k) (v w : V) :
    atomForm hπ hpsd hB v (π (colEl k m N h x) w) = atomForm hπ hpsd hB v w := by
  rw [← starRingEnd_self_apply (atomForm hπ hpsd hB v _), ← atom_herm, atom_colEl, atom_herm, starRingEnd_self_apply]

theorem atom_kills_of (v : V) (hv : ∀ w, B v w = 0) (w : V) : atomForm hπ hpsd hB v w = 0 := by
  have h0 : atomForm hπ hpsd hB w v = 0 := by
    refine tendsto_nhds_unique (atom_tendsto hπ hpsd hB w v) (tendsto_const_nhds.congr fun A => ?_)
    rw [hpsd.1 v (P A.1 w), hv, map_zero]
  rw [← starRingEnd_self_apply (atomForm hπ hpsd hB v w), ← atom_herm, h0, map_zero]

theorem atom_kills_derKer (ψ : AddChar k Circle) (hkill : Kills ψ π (m + 2) B) :
    ∀ v ∈ DerKer k ψ π m, ∀ w, atomForm hπ hpsd hB v w = 0 := by
  have hle : DerKer k ψ π m ≤ LinearMap.ker (atomForm hπ hpsd hB) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, hu⟩, y, rfl⟩
    obtain ⟨x, u', hu', e, hχ⟩ := derUnip_decomp ψ m N h u hu
    have hz : π u' y - ((lvlChar k ψ N (m + 2) ⟨u', hu'⟩ : ℂˣ) : ℂ) • y ∈
        twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) :=
      Submodule.subset_span ⟨⟨u', hu'⟩, y, rfl⟩
    have hsplit : π u y - ((derChar k ψ N (m + 1) ⟨u, hu⟩ : ℂˣ) : ℂ) • y =
        π (colEl k m N h x) (π u' y - ((lvlChar k ψ N (m + 2) ⟨u', hu'⟩ : ℂˣ) : ℂ) • y) +
          ((lvlChar k ψ N (m + 2) ⟨u', hu'⟩ : ℂˣ) : ℂ) • (π (colEl k m N h x) y - y) := by
      rw [hχ]
      show π u y - _ = _
      rw [e, map_mul, Module.End.mul_apply, map_sub, map_smul, smul_sub]
      abel
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [hsplit]
    ext w
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, atom_colEl hπ hpsd hB x,
      atom_kills_of hπ hpsd hB _ (fun w => hkill _ hz w) w, map_sub, LinearMap.sub_apply, atom_colEl hπ hpsd hB x,
      sub_self, smul_zero, add_zero, LinearMap.zero_apply]
  intro v hv w
  have := hle hv
  rw [LinearMap.mem_ker] at this
  rw [this, LinearMap.zero_apply]

theorem atom_gl (g : GL (Fin (m + 1)) k) (v w : V) :
    atomForm hπ hpsd hB (π (blkAt k (m + 1) N (by omega) g) v) (π (blkAt k (m + 1) N (by omega) g) w) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * atomForm hπ hpsd hB v w := by
  let φ : LT → LT := fun A => ⟨A.1.comap (Matrix.mulVecLin (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom,
    isLat_comap g A.2⟩
  have hφ : Tendsto φ atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨⟨b.1.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom, isLat_comap g⁻¹ b.2⟩, fun a ha x hx => ?_⟩
    have : (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom
        ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec x) ∈ b.1 := by
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact hx
    exact ha this
  refine tendsto_nhds_unique (atom_tendsto hπ hpsd hB _ _)
    ((((atom_tendsto hπ hpsd hB v w).comp hφ).const_mul _).congr fun A => ?_)
  simp only [Function.comp_apply, φ]
  have e := avg_conj h π 1 continuous_one_char hπ g 0 (isLat_comap g A.2) v
  rw [comap_comap_inv, Matrix.zero_vecMul] at e
  rw [e, glInv hB]

theorem atom_mir : MirEq π (m + 1) h s (atomForm hπ hpsd hB) := by
  intro p hp v w
  obtain ⟨x, g, e, hdet⟩ := mir_decomp m N h p hp
  show atomForm hπ hpsd hB (π (blkAt k (m + 2) N h p) v) (π (blkAt k (m + 2) N h p) w) = _
  rw [hdet, e, map_mul, Module.End.mul_apply, Module.End.mul_apply, atom_colEl, atom_colEl_right, atom_gl]

end AtomProps

theorem uAtom : UAtom k := by
  intro ψ hψ hψ1 m N h V _ _ π hπ s B hL
  obtain ⟨hpsd, hkill, hmir⟩ := hL
  exact ⟨atomForm hπ hpsd hmir, isAtom_atomForm hπ hpsd hmir, atom_isPsd hπ hpsd hmir, atom_le hπ hpsd hmir,
    atom_kills_derKer hπ hpsd hmir ψ hkill, atom_gl hπ hpsd hmir, atom_mir hπ hpsd hmir⟩

theorem exists_ne_one {ψ : AddChar k Circle} (hψ1 : ψ ≠ 1) : ∃ x, ψ x ≠ 1 := by
  by_contra hc
  push Not at hc
  exact hψ1 (AddChar.ext _ _ fun x => by rw [hc x, AddChar.one_apply])

section Split

variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

local notation "LT" => {A : AddSubgroup (Fin (m + 1) → k) // IsLat A}

variable (hψ : Continuous ψ) (hπ : IsSmooth π) (hpsd : IsPsd B) (hB : MirEq π (m + 1) h s B)
include hψ hπ hpsd hB

theorem avg_sq {ξ : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) :
    B (avg ψ h π ξ A v) (avg ψ h π ξ A v) = B (avg ψ h π ξ A v) v := by
  rw [← form_avg h π ψ hψ hπ B (colInv hB) ξ hA, avg_avg h π ψ hψ hπ ξ ξ hA hA le_rfl v, if_pos (fun _ _ => rfl)]

theorem split_c (hψ1 : ψ ≠ 1) {B₀ B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)}
    (hat : IsAtom h π B B₀) (hd : IsDens ψ h π A₀ B B') (c : ℂ) (hc : ∀ v w, B₀ v w = c * B v w) (v : V)
    (hv : B' v v ≠ 0) : c = 0 := by
  obtain ⟨x₁, hx₁⟩ := exists_ne_one hψ1
  obtain ⟨A₁, hA₁, -, hd1⟩ := hd v v
  obtain ⟨A₂, hc2, -, hx2⟩ := exists_lat_mem (k := k) (m + 1) (Pi.single (Fin.last m) x₁)
  have hA : IsLat (A₁ ⊔ A₂) := ⟨isCompact_sup _ _ hA₁.1 hc2, AddSubgroup.isOpen_mono le_sup_left hA₁.2⟩
  have e1 := hd1 (A₁ ⊔ A₂) hA le_sup_left
  have hww : B (avg ψ h π (xi0 k m) (A₁ ⊔ A₂) v) (avg ψ h π (xi0 k m) (A₁ ⊔ A₂) v) ≠ 0 := by
    rw [avg_sq hψ hπ hpsd hB hA]
    intro h0
    apply hv
    rw [e1, h0, mul_zero]
  have h0 : B₀ (avg ψ h π (xi0 k m) (A₁ ⊔ A₂) v) (avg ψ h π (xi0 k m) (A₁ ⊔ A₂) v) = 0 := by
    refine tendsto_nhds_unique (hat _ _) (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_lat m (A₁ ⊔ A₂) hA] with A' hA'
    rw [← avg_zero_char h π ψ 0 rfl A'.1, avg_avg h π ψ hψ hπ (xi0 k m) 0 hA A'.2 hA' v, if_neg, map_zero,
      LinearMap.zero_apply]
    intro hall
    have := hall _ (le_sup_right (a := A₁) hx2)
    rw [zero_dotProduct, AddChar.map_zero_eq_one] at this
    apply hx₁
    rw [this]
    simp [xi0, dotProduct_single]
  rw [hc] at h0
  exact (mul_eq_zero.1 h0).resolve_right hww

theorem mem_ker_of_re (x : V) (hx : (B x x).re = 0) : x ∈ LinearMap.ker B := by
  rw [LinearMap.mem_ker]
  ext w
  exact apply_eq_zero_of_isotropic B hpsd.1 hpsd.2 x hx w

theorem avg_ker (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) {x : V}
    (hx : x ∈ LinearMap.ker B) : avg ψ h π ξ A x ∈ LinearMap.ker B := by
  rw [LinearMap.mem_ker] at hx ⊢
  ext w
  rw [form_avg h π ψ hψ hπ B (colInv hB) ξ hA, hx, LinearMap.zero_apply, LinearMap.zero_apply]

theorem gl_ker (g : GL (Fin (m + 1)) k) {y : V} (hy : y ∈ LinearMap.ker B) :
    π (blkAt k (m + 1) N (by omega) g) y ∈ LinearMap.ker B := by
  rw [LinearMap.mem_ker] at hy ⊢
  ext w
  have e : w = π (blkAt k (m + 1) N (by omega) g) (π (blkAt k (m + 1) N (by omega) g⁻¹) w) := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
  conv_lhs => rw [e]
  rw [glInv hB, hy, LinearMap.zero_apply, mul_zero, LinearMap.zero_apply]

theorem null_nbhd {A₀ : AddSubgroup (Fin (m + 1) → k)} {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hA₀ : IsLat A₀)
    (hd : IsDens ψ h π A₀ B B') (hB'0 : ∀ v, B' v v = 0) (u : V) (ξ : Fin (m + 1) → k) (hξ : ξ ≠ 0) :
    ∃ As : AddSubgroup (Fin (m + 1) → k), IsLat As ∧
      ∀ A, IsLat A → As ≤ A → avg ψ h π ξ A u ∈ LinearMap.ker B := by
  obtain ⟨g, hg⟩ := exists_GL_vecMul m ξ hξ
  have hg' : Matrix.vecMul ξ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = xi0 k m := hg
  obtain ⟨A₁, hA₁, hA₀₁, hd1⟩ := hd (π (blkAt k (m + 1) N (by omega) g⁻¹) u) (π (blkAt k (m + 1) N (by omega) g⁻¹) u)
  refine ⟨A₁.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom,
    isLat_comap g⁻¹ hA₁, fun A hA hle => ?_⟩
  have hA' := isLat_comap g hA
  have hle' : A₁ ≤ A.comap (Matrix.mulVecLin (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom := by
    intro x hx
    apply hle
    simp only [AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hx
  have e := avg_conj h π ψ hψ hπ g ξ hA' (π (blkAt k (m + 1) N (by omega) g⁻¹) u)
  rw [comap_comap_inv, hg'] at e
  have hu : π (blkAt k (m + 1) N (by omega) g) (π (blkAt k (m + 1) N (by omega) g⁻¹) u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
  rw [hu] at e
  rw [e]
  apply gl_ker hψ hπ hpsd hB
  apply mem_ker_of_re hψ hπ hpsd hB
  have e2 := hd1 _ hA' hle'
  rw [hB'0] at e2
  have hn : ((A₀.relIndex (A.comap (Matrix.mulVecLin (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (relIndex_ne_zero' _ _ hA'.1 hA₀.2 (hA₀₁.trans hle'))
  rw [avg_sq hψ hπ hpsd hB hA', (mul_eq_zero.1 e2.symm).resolve_left hn, Complex.zero_re]

theorem decomp (Ξ : AddSubgroup (Fin (m + 1) → k)) (hΞ : IsLat Ξ) (y : V)
    (hy : ∀ t, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → π (colEl k m N h t) y = y) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) :
    ∃ (R : Finset (Fin (m + 1) → k)) (c : ℂ), (∀ ξ ∈ R, ξ ∈ Ξ) ∧
      (∀ ξ ∈ Ξ, ∃! ξ', ξ' ∈ R ∧ ξ - ξ' ∈ Ξ ⊓ annSub k ψ A) ∧ y = c • ∑ ξ ∈ R, avg ψ h π ξ A y := by
  classical
  let L : AddSubgroup (Fin (m + 1) → k) :=
    { carrier := {t | ∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1}
      add_mem' := fun {a b} ha hb ξ hξ => by rw [dotProduct_add, AddChar.map_add_eq_mul, ha ξ hξ, hb ξ hξ, one_mul]
      zero_mem' := fun ξ _ => by simp
      neg_mem' := fun {a} ha ξ hξ => by rw [dotProduct_neg, AddChar.map_neg_eq_inv, ha ξ hξ, inv_one] }
  have hLo : IsOpen (L : Set (Fin (m + 1) → k)) := by
    have := isOpen_ann ψ hψ (m + 1) Ξ hΞ.1
    convert this using 1
    exact Set.ext fun t => forall₂_congr fun ξ _ => by rw [dotProduct_comm]
  have hUo : IsOpen ((L ⊓ A : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) := by
    rw [AddSubgroup.coe_inf]
    exact hLo.inter hA.2
  obtain ⟨T, hT, hTr⟩ := exists_transversal A (L ⊓ A) hA.1 hUo inf_le_right
  have hΞ'o : IsOpen ((Ξ ⊓ annSub k ψ A : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) := by
    rw [AddSubgroup.coe_inf]
    exact hΞ.2.inter (isOpen_ann ψ hψ (m + 1) A hA.1)
  obtain ⟨R, hR, hRtr⟩ := exists_transversal Ξ (Ξ ⊓ annSub k ψ A) hΞ.1 hΞ'o inf_le_left
  have hdata : ∀ ξ ∈ R, AvgData ψ h π ξ A y (L ⊓ A, T) := fun ξ hξ =>
    ⟨inf_le_right, hUo, fun a ha => hy a (AddSubgroup.mem_inf.1 ha).1,
      fun a ha => (AddSubgroup.mem_inf.1 ha).1 ξ (hR ξ hξ), hT, hTr⟩
  have hcard : (T.filter (fun t => t ∈ L)).card = 1 := by
    obtain ⟨t₀, ⟨ht₀T, ht₀U⟩, huniq⟩ := hTr 0 A.zero_mem
    refine Finset.card_eq_one.2 ⟨t₀, Finset.ext fun t => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨htT, htL⟩
      refine huniq t ⟨htT, ?_⟩
      rw [zero_sub]
      exact AddSubgroup.mem_inf.2 ⟨L.neg_mem htL, A.neg_mem (hT t htT)⟩
    · rintro rfl
      refine ⟨ht₀T, ?_⟩
      have := (AddSubgroup.mem_inf.1 ht₀U).1
      rw [zero_sub] at this
      simpa using L.neg_mem this
  have inner : ∀ t ∈ T, ∑ ξ ∈ R, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) y =
      if t ∈ L then (R.card : ℂ) • y else 0 := by
    intro t htT
    rw [← Finset.sum_smul]
    by_cases ht : t ∈ L
    · rw [if_pos ht, hy t ht]
      have : ∀ ξ ∈ R, starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) = 1 := fun ξ hξ => by
        rw [show ψ (ξ ⬝ᵥ t) = 1 from ht ξ (hR ξ hξ)]
        simp
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    · rw [if_neg ht]
      obtain ⟨ξ₁, hξ₁, hne⟩ : ∃ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) ≠ 1 := by
        by_contra hc
        push Not at hc
        exact ht hc
      have hs := sum_transversal_char (A := Ξ) (H := Ξ ⊓ annSub k ψ A) inf_le_left hR hRtr
        (fun ξ => starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ))
        (fun a b => by rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, map_mul])
        (fun ξ hξ => by
          rw [show ψ (ξ ⬝ᵥ t) = 1 from (AddSubgroup.mem_inf.1 hξ).2 t (hT t htT)]
          simp)
        hξ₁ (fun hc => hne (Circle.ext (by simpa using congrArg (starRingEnd ℂ) hc)))
      rw [hs, zero_smul]
  have hsum : ∑ ξ ∈ R, avg ψ h π ξ A y = ((T.card : ℂ)⁻¹ * R.card) • y := by
    rw [Finset.sum_congr rfl fun ξ hξ => avg_eq h π ψ (hdata ξ hξ), ← Finset.smul_sum, Finset.sum_comm,
      Finset.sum_congr rfl inner, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hcard, one_smul,
      mul_smul]
  have hT0 : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_pos.2 (transversal_nonempty hTr)).ne'
  have hR0 : (R.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_pos.2 (transversal_nonempty hRtr)).ne'
  refine ⟨R, (T.card : ℂ) / R.card, hR, hRtr, ?_⟩
  rw [hsum, smul_smul, show (T.card : ℂ) / R.card * ((T.card : ℂ)⁻¹ * R.card) = 1 by field_simp, one_smul]

theorem annulus_null {A₀ : AddSubgroup (Fin (m + 1) → k)} {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hA₀ : IsLat A₀)
    (hd : IsDens ψ h π A₀ B B') (hB'0 : ∀ v, B' v v = 0) (Ξ : AddSubgroup (Fin (m + 1) → k)) (hΞ : IsLat Ξ) (v : V)
    (hv : ∀ t, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → π (colEl k m N h t) v = v) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (ξ : Fin (m + 1) → k) (hξΞ : ξ ∈ Ξ) (hξA : ξ ∉ annSub k ψ A) :
    avg ψ h π ξ A v ∈ LinearMap.ker B := by
  classical
  have hN : ∀ η : Fin (m + 1) → k, ∃ As : AddSubgroup (Fin (m + 1) → k), IsLat As ∧
      (η ≠ 0 → ∀ A', IsLat A' → As ≤ A' → avg ψ h π η A' v ∈ LinearMap.ker B) := by
    intro η
    by_cases hη : η = 0
    · exact ⟨A, hA, fun h' => absurd hη h'⟩
    · obtain ⟨As, h1, h2⟩ := null_nbhd hψ hπ hpsd hB hA₀ hd hB'0 v η hη
      exact ⟨As, h1, fun _ => h2⟩
  choose As hAsL hAsN using hN
  have hannO : IsOpen (annSub k ψ A : Set (Fin (m + 1) → k)) := isOpen_ann ψ hψ (m + 1) A hA.1
  obtain ⟨K, hKdef⟩ : ∃ K : Set (Fin (m + 1) → k), K = (Ξ : Set (Fin (m + 1) → k)) \ (annSub k ψ A : Set (Fin (m + 1) → k)) :=
    ⟨_, rfl⟩
  have hK : IsCompact K := hKdef ▸ hΞ.1.diff hannO
  let U : (Fin (m + 1) → k) → Set (Fin (m + 1) → k) := fun η => {ζ | ζ - η ∈ annSub k ψ (As η)}
  have hUo : ∀ η, IsOpen (U η) := fun η =>
    (isOpen_ann ψ hψ (m + 1) (As η) (hAsL η).1).preimage (continuous_id.sub continuous_const)
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover
    (fun η : K => U η.1) (fun η => hUo η.1)
    (fun ζ hζ => Set.mem_iUnion.2 ⟨⟨ζ, hζ⟩, show ζ - ζ ∈ annSub k ψ (As ζ) by rw [sub_self]; exact zero_mem _⟩)
  have hsupc : IsCompact ((F.sup (fun η => As η.1) : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) := by
    refine Finset.sup_induction (p := fun S : AddSubgroup (Fin (m + 1) → k) => IsCompact (S : Set (Fin (m + 1) → k)))
      ?_ ?_ ?_
    · rw [AddSubgroup.coe_bot]
      exact isCompact_singleton
    · intro a ha b hb
      exact isCompact_sup a b ha hb
    · intro η _
      exact (hAsL η.1).1
  have hA'' : IsLat (A ⊔ F.sup (fun η => As η.1)) :=
    ⟨isCompact_sup _ _ hA.1 hsupc, AddSubgroup.isOpen_mono le_sup_left hA.2⟩
  have hx : ∀ t, (∀ ξ' ∈ Ξ, ψ (ξ' ⬝ᵥ t) = 1) → π (colEl k m N h t) (avg ψ h π ξ A v) = avg ψ h π ξ A v :=
    fun t ht => by rw [colEl_comm_avg h π ψ hψ hπ ξ hA t v, hv t ht]
  obtain ⟨R, c, hR, -, hdec⟩ := decomp hψ hπ hpsd hB Ξ hΞ _ hx hA''
  rw [hdec]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun η hη => ?_)
  rw [avg_avg h π ψ hψ hπ ξ η hA hA'' le_sup_left v]
  split_ifs with hc
  swap
  · exact Submodule.zero_mem _
  have hηK : η ∈ K := by
    rw [hKdef]
    exact ⟨hR η hη, fun hηA => hξA (fun a ha => by rw [← hc a ha]; exact hηA a ha)⟩
  have hmem := hF hηK
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨i, hiF, hi⟩ := hmem
  have hi0 : i.1 ≠ 0 := by
    intro h0
    have hiK : i.1 ∈ (Ξ : Set (Fin (m + 1) → k)) \ (annSub k ψ A : Set (Fin (m + 1) → k)) := hKdef ▸ i.2
    exact hiK.2 (by rw [h0]; exact zero_mem _)
  have hle : As i.1 ≤ A ⊔ F.sup (fun η => As η.1) :=
    le_sup_of_le_right (Finset.le_sup (f := fun η => As η.1) hiF)
  have e := avg_avg h π ψ hψ hπ i.1 η (hAsL i.1) hA'' hle v
  rw [if_pos (fun a ha => ?_)] at e
  · rw [← e]
    exact avg_ker hψ hπ hpsd hB η hA'' (hAsN i.1 hi0 (As i.1) (hAsL i.1) le_rfl)
  · have := hi a ha
    rw [sub_dotProduct, AddChar.map_sub_eq_div, div_eq_one] at this
    exact this

theorem diag_eq {A₀ : AddSubgroup (Fin (m + 1) → k)} {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hψ1 : ψ ≠ 1) (hA₀ : IsLat A₀)
    (hd : IsDens ψ h π A₀ B B') (hB'0 : ∀ v, B' v v = 0) (v : V) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) :
    B (avg (1 : AddChar k Circle) h π 0 A v) v = B v v := by
  classical
  have hS : (stabSub h π v : Set (Fin (m + 1) → k)) ∈ 𝓝 (0 : Fin (m + 1) → k) :=
    (isOpen_stabSub h π hπ v).mem_nhds (zero_mem _)
  obtain ⟨Ξ₀, hΞ₀c, hΞ₀⟩ := exists_small_ann ψ hψ hψ1 (m + 1) _ hS
  have hΞ : IsLat (Ξ₀ ⊔ A) := ⟨isCompact_sup _ _ hΞ₀c hA.1, AddSubgroup.isOpen_mono le_sup_right hA.2⟩
  have hv : ∀ t, (∀ ξ ∈ Ξ₀ ⊔ A, ψ (ξ ⬝ᵥ t) = 1) → π (colEl k m N h t) v = v :=
    fun t ht => hΞ₀ t fun ξ hξ => ht ξ (le_sup_left (b := A) hξ)
  obtain ⟨R, c, hR, hRtr, hdec⟩ := decomp hψ hπ hpsd hB _ hΞ v hv hA
  obtain ⟨ξ₀, ⟨hξ₀R, hξ₀H⟩, huniq⟩ := hRtr 0 (zero_mem _)
  have hξ₀A : ξ₀ ∈ annSub k ψ A := by
    have := (AddSubgroup.mem_inf.1 hξ₀H).2
    rw [zero_sub] at this
    simpa using (annSub k ψ A).neg_mem this
  have hn : ∑ ξ ∈ R.erase ξ₀, avg ψ h π ξ A v ∈ LinearMap.ker B := by
    refine Submodule.sum_mem _ fun ξ hξ => ?_
    obtain ⟨hξne, hξR⟩ := Finset.mem_erase.1 hξ
    refine annulus_null hψ hπ hpsd hB hA₀ hd hB'0 _ hΞ v hv hA ξ (hR ξ hξR) fun hξA => hξne ?_
    refine huniq ξ ⟨hξR, ?_⟩
    rw [zero_sub]
    exact AddSubgroup.mem_inf.2 ⟨neg_mem (hR ξ hξR), neg_mem hξA⟩
  have hP : avg ψ h π ξ₀ A v = avg (1 : AddChar k Circle) h π 0 A v := by
    rw [avg_congr_char h π ψ hψ hπ hA (ξ' := 0) (fun a ha => by rw [hξ₀A a ha, zero_dotProduct, AddChar.map_zero_eq_one]) v,
      avg_zero_char h π ψ 0 rfl]
  obtain ⟨n, hnB, hv'⟩ : ∃ n ∈ LinearMap.ker B, v = c • (avg (1 : AddChar k Circle) h π 0 A v + n) := by
    refine ⟨_, hn, ?_⟩
    conv_lhs => rw [hdec]
    rw [← Finset.add_sum_erase R _ hξ₀R, hP]
  have h1 : avg (1 : AddChar k Circle) h π 0 A v =
      c • (avg (1 : AddChar k Circle) h π 0 A v + avg (1 : AddChar k Circle) h π 0 A n) := by
    have := congrArg (avg (1 : AddChar k Circle) h π 0 A) hv'
    rwa [P_smul hπ hA, P_add hπ hA, P_idem hπ hA] at this
  have h2 : v - avg (1 : AddChar k Circle) h π 0 A v = c • (n - avg (1 : AddChar k Circle) h π 0 A n) := by
    calc v - avg (1 : AddChar k Circle) h π 0 A v
        = c • (avg (1 : AddChar k Circle) h π 0 A v + n) -
            c • (avg (1 : AddChar k Circle) h π 0 A v + avg (1 : AddChar k Circle) h π 0 A n) := by
          rw [← hv', ← h1]
      _ = c • (n - avg (1 : AddChar k Circle) h π 0 A n) := by
          rw [← smul_sub]
          congr 1
          abel
  have hPn : avg (1 : AddChar k Circle) h π 0 A n ∈ LinearMap.ker B := by
    rw [← avg_zero_char h π ψ 0 rfl]
    exact avg_ker hψ hπ hpsd hB 0 hA hnB
  have hmem : v - avg (1 : AddChar k Circle) h π 0 A v ∈ LinearMap.ker B := by
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hnB hPn)
  rw [LinearMap.mem_ker] at hmem
  have := congrArg (fun f => f v) hmem
  simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply] at this
  exact (sub_eq_zero.1 this).symm

theorem split_eq {B₀ B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hψ1 : ψ ≠ 1) (hA₀ : IsLat A₀)
    (hat : IsAtom h π B B₀) (hd : IsDens ψ h π A₀ B B') (hB'0 : ∀ v, B' v v = 0) : B₀ = B := by
  have hdiag : ∀ v, B₀ v v = B v v := fun v =>
    tendsto_nhds_unique (hat v v)
      (tendsto_const_nhds.congr fun A => (diag_eq hψ hπ hpsd hB hψ1 hA₀ hd hB'0 v A.2).symm)
  have := eq_zero_of_diag (B₀ - B) (fun v => by rw [LinearMap.sub_apply, LinearMap.sub_apply, hdiag, sub_self])
  exact sub_eq_zero.1 this

end Split

theorem uSplit : USplit k := by
  intro ψ hψ hψ1 m N h V _ _ π hπ s B B₀ B' A₀ hL hA₀ hat hd
  obtain ⟨hpsd, -, hmir⟩ := hL
  exact ⟨fun h0 => split_eq hψ hπ hpsd hmir hψ1 hA₀ hat hd h0,
    fun c hc ⟨v, hv⟩ => split_c hψ hπ hpsd hmir hψ1 hat hd c hc v hv⟩

end PositivityTheory.RgUd.Form.U.Atom
