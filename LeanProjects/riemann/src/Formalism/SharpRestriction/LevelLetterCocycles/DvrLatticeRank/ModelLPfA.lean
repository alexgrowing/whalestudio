import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfLoc
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLA

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem expwd_core {O A E L X Y : Type*} [CommRing O] [AddCommGroup A] [Module O A]
    [AddCommGroup E] [Module O E] [AddCommGroup L] [Module O L] [AddCommGroup X] [Module O X]
    [AddCommGroup Y] [Module O Y] [Module.Flat O X]
    (j : A →ₗ[O] E) (hj : Function.Injective j) (g : L →ₗ[O] X) (μ : A ⊗[O] X →ₗ[O] Y)
    {m m' : ℕ} (a : Fin m → A) (s : Fin m → L) (b : Fin m' → A) (t : Fin m' → L)
    (h : ∑ i, j (a i) ⊗ₜ[O] s i = ∑ k, j (b k) ⊗ₜ[O] t k) :
    ∑ i, μ (a i ⊗ₜ g (s i)) = ∑ k, μ (b k ⊗ₜ g (t k)) := by
  have hinjX : Function.Injective (LinearMap.rTensor X j) :=
    Module.Flat.rTensor_preserves_injective_linearMap j hj
  have h2 := congrArg (LinearMap.lTensor E g) h
  simp only [map_sum, LinearMap.lTensor_tmul] at h2
  have h3 : LinearMap.rTensor X j (∑ i, a i ⊗ₜ[O] g (s i)) =
      LinearMap.rTensor X j (∑ k, b k ⊗ₜ[O] g (t k)) := by
    simp only [map_sum, LinearMap.rTensor_tmul]
    exact h2
  have h5 := congrArg μ (hinjX h3)
  simpa only [map_sum] using h5

theorem flat_compHom {O LL X : Type*} [CommRing O] [IsDomain O] [IsDedekindDomain O] [Field LL]
    [Algebra O LL] (hinj : Function.Injective (algebraMap O LL)) [AddCommGroup X] [Module LL X] :
    letI : Module O X := Module.compHom X (algebraMap O LL)
    Module.Flat O X := by
  letI : Module O X := Module.compHom X (algebraMap O LL)
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := hx
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have h1 : algebraMap O LL r • x = 0 := hrx
  rw [smul_eq_zero] at h1
  rw [Submodule.mem_bot]
  rcases h1 with h1 | h1
  · exact absurd ((map_eq_zero_iff _ hinj).mp h1) hr0
  · exact h1

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

theorem lev_letE_mul (c : ZMod n) (ζ : LL) (a : LetA O n) :
    W.lev c ζ ((letE c : LetA O n) * a) = W.lev c ζ a := by
  have h0 : ((letE c : LetA O n) * a - a) c = 0 := by
    first
    | (simp [letE]; done)
    | (simp [letE, Pi.single_apply]; done)
  have h1 := W.79 c ζ _ h0
  rw [map_sub, sub_eq_zero] at h1
  exact h1

theorem levN_smul_alg (i : ZMod n) (ζ : LL) (o : O) (x : ↥(W.N T)) (k : ℤ) :
    W.levN T i ζ ((algebraMap O (LetA O n) o) • x) k = algebraMap O LL o • W.levN T i ζ x k := by
  rw [W.levN_smul, finsum_eq_single _ 0]
  · rw [AlgHom.commutes]
    first
    | (simp; done)
    | (simp [PowerSeries.algebraMap_apply, PowerSeries.coeff_C]; done)
    | (simp [PowerSeries.algebraMap_apply', PowerSeries.coeff_C]; done)
    | (simp [PowerSeries.coeff_zero_eq_constantCoeff, Algebra.smul_def]; done)
  · intro j hj
    rw [AlgHom.commutes]
    first
    | (simp [hj]; done)
    | (simp [PowerSeries.algebraMap_apply, PowerSeries.coeff_C, hj]; done)
    | (simp [PowerSeries.algebraMap_apply', PowerSeries.coeff_C, hj]; done)

theorem levB_smul_alg (i : ZMod n) (ζ : LL) (o : O) (x : ↥(W.N T)) (k : ℤ) :
    Ct.levB T i ζ ((algebraMap O (LetA O n) o) • x) k = algebraMap O LL o • Ct.levB T i ζ x k := by
  apply framepf_ιV_inj (PD := PD) T
  rw [← Ct.levN_eq, levN_smul_alg, Ct.levN_eq, map_smul]

def val1 (c : ZMod n) (x : ↥(W.N T)) : T.V ⊗[Qp] BdR :=
  ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (c - 1) 1 x 0))

theorem level_value_add (c : ZMod n) (x y : ↥(W.N T)) : val1 Ct T c (x + y) = val1 Ct T c x + val1 Ct T c y := by
  first
  | (simp only [val1, map_add, Pi.add_apply]; done)
  | (simp [val1]; done)
  | (simp [val1, CmpTie.levB]; done)

theorem level_value_smul (c : ZMod n) (o : O) (x : ↥(W.N T)) :
    val1 Ct T c ((algebraMap O (LetA O n) o) • x) = algebraMap O LL o • val1 Ct T c x := by
  first
  | (simp only [val1, levB_smul_alg, map_smul]; done)
  | (simp [val1, levB_smul_alg]; done)
  | (simp [val1, levB_smul_alg, map_smul]; done)

def PtHyp (c : ZMod n) (ζ : LL) : Prop :=
  IsCrys PD T.ρ ∧ (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) ∧ ζ ^ PD.p = 1 ∧
    PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0 ∧
    (∀ (x : ↥(W.N T)) (k : ℤ), k < 0 → W.levN T (c - 1) 1 x k = 0) ∧
    ∀ x ∈ W.N T, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ W.N T

theorem valAt_eq {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) (x : ↥(W.N T)) :
    valAt W T c ζ (x : W.DD T) = val1 Ct T c x := by
  obtain ⟨hc, hζ, hζ1, hQ0, hQ1, hneg, hex⟩ := hP
  refine framepf_valAt Ct T hc c ζ hζ hζ1 hQ0 hQ1 x (fun r hr => ?_) (hex _ x.2)
  apply framepf_ιV_inj (PD := PD) T
  rw [← Ct.levN_eq, hneg x r hr, map_zero]

def XO (BdR : Type) [CommRing BdR] [Algebra Qp BdR] (T : LocLat G Qp LL O) : Type := T.V ⊗[Qp] BdR

instance (BdR : Type) [CommRing BdR] [Algebra Qp BdR] (T : LocLat G Qp LL O) :
    AddCommGroup (XO BdR T) := inferInstanceAs (AddCommGroup (T.V ⊗[Qp] BdR))

instance (BdR : Type) [CommRing BdR] [Algebra Qp BdR] (T : LocLat G Qp LL O) :
    Module LL (XO BdR T) := inferInstanceAs (Module LL (T.V ⊗[Qp] BdR))

instance (BdR : Type) [CommRing BdR] [Algebra Qp BdR] (T : LocLat G Qp LL O) :
    Module O (XO BdR T) := Module.compHom _ (algebraMap O LL)

theorem smul_XO (o : O) (x : XO BdR T) : o • x = algebraMap O LL o • x := rfl

def valL {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) :
    ↥(NcS W T (c - 1)) →ₗ[O] XO BdR T where
  toFun x := (valAt W T c ζ (x : W.DD T) : T.V ⊗[Qp] BdR)
  map_add' x y := by
    have hx : (x : W.DD T) ∈ W.N T := x.2.1.1
    have hy : (y : W.DD T) ∈ W.N T := y.2.1.1
    have e := valAt_eq Ct T hP (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [level_value_add, ← valAt_eq Ct T hP ⟨x, hx⟩, ← valAt_eq Ct T hP ⟨y, hy⟩] at e
    exact e
  map_smul' o x := by
    have hx : (x : W.DD T) ∈ W.N T := x.2.1.1
    have e := valAt_eq Ct T hP ((algebraMap O (LetA O n) o) • ⟨x, hx⟩)
    rw [level_value_smul, ← valAt_eq Ct T hP ⟨x, hx⟩] at e
    have e2 : valAt W T c ζ ((algebraMap O (LetA O n) o) • (x : W.DD T)) =
        algebraMap O LL o • valAt W T c ζ (x : W.DD T) := e
    rw [algebraMap_smul] at e2
    change valAt W T c ζ (o • (x : W.DD T)) = algebraMap O LL o • valAt W T c ζ (x : W.DD T)
    exact e2

theorem valL_ker {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) (π' : LetA O n)
    (hπ : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0) :
    (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype ≤ LinearMap.ker (valL Ct T hP) := by
  intro x hx
  rw [Submodule.mem_comap] at hx
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 hx.1
  have hxN : (x : W.DD T) ∈ W.N T := x.2.1.1
  rw [LinearMap.mem_ker]
  change valAt W T c ζ (x : W.DD T) = 0
  rw [valAt_eq Ct T hP ⟨x, hxN⟩]
  have hzx' : (π' ^ 1) • z = (x : W.DD T) := hzx
  have hxe : (⟨x, hxN⟩ : ↥(W.N T)) = (π' ^ 1) • ⟨z, hz⟩ := by
    apply Subtype.ext
    exact hzx'.symm
  have hneg := hP.2.2.2.2.2.1
  have h0 : Ct.levB T (c - 1) 1 ⟨x, hxN⟩ 0 = 0 := by
    apply framepf_ιV_inj (PD := PD) T
    rw [← Ct.levN_eq, hxe, W.levN_smul, map_zero, pow_one]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hπ, zero_smul]
    · rw [hneg ⟨z, hz⟩ _ (by omega), smul_zero]
  simp only [val1, h0, map_zero]

def valQ {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) (π' : LetA O n)
    (hπ : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0) : LcQ W T π' c →ₗ[O] XO BdR T :=
  Submodule.liftQ _ (valL Ct T hP) (valL_ker Ct T hP π' hπ)

def muL (c : ZMod n) (ζ : LL) : LetA O n ⊗[O] XO BdR T →ₗ[O] (ℤ → XO BdR T) :=
  TensorProduct.lift (LinearMap.mk₂ O (fun a d => serC (W.lev c ζ a) d)
    (fun a a' d => by
      funext i
      simp only [serC, map_add, Pi.add_apply]
      split_ifs <;> simp [add_smul])
    (fun o a d => by
      funext i
      simp only [serC, map_smul, Pi.smul_apply]
      split_ifs
      · rw [smul_XO, PowerSeries.coeff_smul, Algebra.smul_def, mul_smul]
      · rw [smul_zero])
    (fun a d d' => by
      funext i
      simp only [serC, Pi.add_apply]
      split_ifs <;> simp [smul_add])
    (fun o a d => by
      funext i
      simp only [serC, Pi.smul_apply]
      split_ifs
      · rw [smul_XO, smul_XO, smul_comm]
      · rw [smul_zero]))

include Ct in

theorem expS_wd [IsDomain O] [IsDedekindDomain O] (hinj : Function.Injective (algebraMap O LL))
    {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) (π' : LetA O n)
    (hπ : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0)
    {m m' : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) (hy : ∀ j, y j ∈ NcS W T (c - 1))
    (b : Fin m' → LetA O n) (z : Fin m' → W.DD T) (hz : ∀ k, z k ∈ NcS W T (c - 1))
    (h : ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ[O] mkL W T π' c (y j) (hy j) =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b k) ⊗ₜ[O] mkL W T π' c (z k) (hz k)) :
    expS W T c ζ a y = expS W T c ζ b z := by
  haveI : Module.Flat O (XO BdR T) := flat_compHom (X := XO BdR T) hinj
  have key := expwd_core (IsScalarTower.toAlgHom O (LetA O n) W.EE).toLinearMap
    (fun x y hxy => W.EE_inj hxy) (valQ Ct T hP π' hπ) (muL (W := W) T c ζ)
    (fun j => (letE c : LetA O n) * a j) (fun j => mkL W T π' c (y j) (hy j))
    (fun k => (letE c : LetA O n) * b k) (fun k => mkL W T π' c (z k) (hz k)) h
  have e1 : ∀ j, muL (W := W) T c ζ (((letE c : LetA O n) * a j) ⊗ₜ[O]
      valQ Ct T hP π' hπ (mkL W T π' c (y j) (hy j))) = serC (W.lev c ζ (a j)) (valAt W T c ζ (y j)) :=
    fun j => by
      show serC (W.lev c ζ ((letE c : LetA O n) * a j)) (valAt W T c ζ (y j)) = _
      rw [lev_letE_mul]
  have e2 : ∀ k, muL (W := W) T c ζ (((letE c : LetA O n) * b k) ⊗ₜ[O]
      valQ Ct T hP π' hπ (mkL W T π' c (z k) (hz k))) = serC (W.lev c ζ (b k)) (valAt W T c ζ (z k)) :=
    fun k => by
      show serC (W.lev c ζ ((letE c : LetA O n) * b k)) (valAt W T c ζ (z k)) = _
      rw [lev_letE_mul]
  have key2 : ∑ j, serC (W.lev c ζ (a j)) (valAt W T c ζ (y j)) =
      ∑ k, serC (W.lev c ζ (b k)) (valAt W T c ζ (z k)) := by
    refine (Finset.sum_congr rfl (fun j _ => (e1 j).symm)).trans ?_
    refine Eq.trans ?_ (Finset.sum_congr rfl (fun k _ => e2 k))
    exact key
  funext i
  have := congrFun key2 i
  simpa [expS, Finset.sum_apply] using this

end Generic

end Formalism.MainNotions.N.Ln34.MLA

end
