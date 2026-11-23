import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl Matrix
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 160000
namespace GlobalTheory.FinPl.LatMem
variable {D : D7}

open Classical in

def indP (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop) : Af F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if P v then (1 : Fv F v) else 0) ∈ (v.adicCompletionIntegers F : Set (Fv F v))
    split_ifs
    · exact (v.adicCompletionIntegers F).one_mem
    · exact (v.adicCompletionIntegers F).zero_mem⟩

open Classical in
theorem evalV_indP (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop)
    (v : HeightOneSpectrum (𝓞 F)) : evalV F v (indP F P) = if P v then 1 else 0 := rfl

theorem indicatorAdele_mem_integralAdeles' (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop) :
    indP F P ∈ intAf F := fun v => by
  classical
  rw [evalV_indP]
  split_ifs
  · exact (v.adicCompletionIntegers F).one_mem
  · exact (v.adicCompletionIntegers F).zero_mem

theorem indicatorAdele_supported (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop) :
    ∀ v, ¬ P v → evalV F v (indP F P) = 0 := fun v hv => by
  classical
  rw [evalV_indP, if_neg hv]

theorem compFin_eq_compAt (a : AE D) (v : Pl D) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E v a = compAt D v a := by
  change Algebra.TensorProduct.map ((evalV D.host.F v).comp (sndA D.host.F)) (AlgHom.id _ _) a =
    Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) a)
  rw [GlobalTheory.AdelicU.Supp.tens_map_map]

theorem compInf_eq_zero {a : AE D} (h : infPart D a = 0) (w : NumberField.InfinitePlace D.host.F) :
    GlobalTheory.AdelicU.compInf D.host.F D.host.E w a = 0 := by
  change Algebra.TensorProduct.map ((GlobalTheory.AutFunCompare.evW w).comp (fstA D.host.F)) (AlgHom.id _ _) a = 0
  rw [← GlobalTheory.AdelicU.Supp.tens_map_map]
  change Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id _ _) (infPart D a) = 0
  rw [h, map_zero]

theorem mem_idAt_iff {P : Pl D → Prop} {a : AE D} :
    a ∈ idAt D P ↔ infPart D a = 0 ∧ ∀ w, ¬ P w → compAt D w a = 0 := by
  unfold idAt
  rw [Submodule.mem_inf, RingHom.mem_ker, Submodule.mem_iInf]
  exact and_congr_right fun _ => ⟨fun h w hw => RingHom.mem_ker.1 (h ⟨w, hw⟩), fun h w => RingHom.mem_ker.2 (h w.1 w.2)⟩

theorem mul_indP {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) :
    a * (pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E)) = a := by
  classical
  obtain ⟨h0, hw⟩ := mem_idAt_iff.1 ha
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
  · rw [map_mul, compInf_eq_zero h0, zero_mul]
  · rw [map_mul]
    have he : GlobalTheory.AdelicU.compFin D.host.F D.host.E v (pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F v (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    by_cases hv : P v
    · rw [he, evalV_indP, if_pos hv]
      exact mul_one _
    · rw [compFin_eq_compAt, hw v hv, zero_mul]

theorem tmul_mem_idAt {P : Pl D → Prop} {α : Af D.host.F} (hα : ∀ v, ¬ P v → evalV D.host.F v α = 0) (e : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] e ∈ idAt D P := by
  refine mem_idAt_iff.2 ⟨?_, fun w hw => ?_⟩
  · change fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] e = 0
    exact TensorProduct.zero_tmul _ _
  · change evalV D.host.F w α ⊗ₜ[D.host.F] e = 0
    rw [hα w hw, TensorProduct.zero_tmul]

theorem star_int (c : 𝓞 D.host.E) : ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = star (c : D.host.E) :=
  ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) c, rfl⟩

private theorem dual_row {K : Type} [CommRing K] [StarRing K] {r : ℕ} (G G' : Matrix (Fin r) (Fin r) K) (w : Fin r → K)
    (hGe : ∀ l b, ∑ k, G' l k * G k b = if l = b then 1 else 0) (b : Fin r) :
    ∑ k, star (star (∑ l, w l * G' l k)) * G k b = w b := by
  simp only [star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, hGe]
  simp

private theorem dual_key {K : Type} [CommRing K] [StarRing K] {r : ℕ} (G G' : Matrix (Fin r) (Fin r) K) (w x : Fin r → K)
    (hGe : ∀ l b, ∑ k, G' l k * G k b = if l = b then 1 else 0) (hst : ∀ a b, star (G a b) = G b a) :
    star (∑ a, ∑ b, star (x a) * G a b * star (∑ l, w l * G' l b)) = ∑ j, x j * w j := by
  simp only [star_sum, star_mul', star_star, hst]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∑ l, w l * (∑ b, G' l b * G b a) = w a := by simp [hGe]
  rw [← h2, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem exists_dualBasis (S : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ) :
    ∃ (m : ℕ) (s s' : Fin m → Fin S.rank → D.host.E), (∀ i, s i ∈ Λ) ∧ (∀ i, s' i ∈ Λ) ∧
      ∀ a b : Fin S.rank, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k b = if a = b then 1 else 0 := by
  classical
  set E := D.host.E
  set O := 𝓞 E
  set V := Fin S.rank → E
  have hlat := hΛ.1
  have hfg : Λ.FG := hlat.fg
  have hsp : Submodule.span E (Λ : Set V) = ⊤ := hlat.span_eq_top
  haveI hfin : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  have hcancel : ∀ (d : O) (x : V), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul E d x] at h
    exact (smul_eq_zero.1 h).resolve_left (by simpa using hd)
  haveI hflat : Module.Flat O Λ := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : O) • (x : V) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  haveI hfp : Module.FinitePresentation O Λ := Module.finitePresentation_of_finite _ _
  haveI hproj : Module.Projective O Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' O Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ

  let g : Fin m → V := fun i => (π (Pi.single i 1) : V)
  have hg : ∀ i, g i ∈ Λ := fun i => (π (Pi.single i 1)).2
  have hexp : ∀ x : Λ, (x : V) = ∑ i, ((σ x i : O) : E) • g i := by
    intro x
    have h1 : π (σ x) = x := LinearMap.congr_fun hσ x
    conv_lhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ π (σ x)]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← IsScalarTower.algebraMap_smul E (σ x i)]
    congr 2
    congr 1
    funext j
    simp [Pi.single_apply, eq_comm]

  have hden : ∀ v : V, ∃ d : O, d ≠ 0 ∧ d • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E (Λ : Set V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  have hunitV : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) x) :=
    (isLocalizedModule_id (nonZeroDivisors O) V E).map_units
  have hunitE : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O E) x) :=
    (isLocalizedModule_id (nonZeroDivisors O) E E).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype := by
    refine ⟨hunitV, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let φ : Fin m → Λ →ₗ[O] E := fun i => (Algebra.linearMap O E) ∘ₗ (LinearMap.proj i) ∘ₗ σ
  let Φ0 : Fin m → V →ₗ[O] E := fun i => IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (φ i) hunitE
  have hΦ0 : ∀ i (x : Λ), Φ0 i (x : V) = ((σ x i : O) : E) := fun i x =>
    IsLocalizedModule.lift_apply _ Λ.subtype (φ i) hunitE x
  let Φ : Fin m → V →ₗ[E] E := fun i => (Φ0 i).extendScalarsOfIsLocalization (nonZeroDivisors O) E
  have hΦ : ∀ i (x : Λ), Φ i (x : V) = ((σ x i : O) : E) := fun i x => hΦ0 i x
  let w : Fin m → Fin S.rank → E := fun i j => Φ i (Pi.single j 1)
  have hw : ∀ i (x : V), Φ i x = ∑ j, x j * w i j := by
    intro i x
    rw [LinearMap.pi_apply_eq_sum_univ (Φ i) x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul]
    congr 2
    funext l
    simp [Pi.single_apply, eq_comm]

  have hid : ∀ x : V, x = ∑ i, Φ i x • g i := by
    intro x
    have hL : (LinearMap.id : V →ₗ[E] V) = ∑ i, (LinearMap.smulRight (Φ i) (g i)) := by
      refine LinearMap.ext_on hsp fun y hy => ?_
      rw [LinearMap.id_apply, LinearMap.sum_apply]
      simp only [LinearMap.smulRight_apply]
      refine (hexp ⟨y, hy⟩).trans (Finset.sum_congr rfl fun i _ => ?_)
      exact congrArg (· • g i) (hΦ i ⟨y, hy⟩).symm
    have := LinearMap.congr_fun hL x
    simpa using this
  have hG : S.gram⁻¹ * S.gram = 1 := Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)
  have hGe : ∀ l b, ∑ k, S.gram⁻¹ l k * S.gram k b = if l = b then 1 else 0 := fun l b => by
    have := congrFun (congrFun hG l) b
    rwa [Matrix.mul_apply, Matrix.one_apply] at this
  let s' : Fin m → Fin S.rank → E := fun i k => star (∑ l, w i l * S.gram⁻¹ l k)
  have hs'row : ∀ i b, ∑ k, star (s' i k) * S.gram k b = w i b := by
    intro i b
    exact dual_row (K := D.host.E) S.gram _ (w i) hGe b
  refine ⟨m, g, s', hg, fun i => ?_, fun a b => ?_⟩
  · rw [hΛ.2]
    intro x hx
    obtain ⟨c', hc'⟩ := star_int (σ ⟨x, hx⟩ i)
    refine ⟨c', ?_⟩
    have key : star (∑ a, ∑ b, star (x a) * S.gram a b * s' i b) = ∑ j, x j * w i j := by
      exact dual_key (K := D.host.E) S.gram _ (w i) x hGe (GlobalTheory.LatVac.gram_star S)
    have h3 : ((σ ⟨x, hx⟩ i : O) : E) = ∑ j, x j * w i j := (hΦ i ⟨x, hx⟩).symm.trans (hw i x)
    rw [hc', h3, ← key, star_star]
  · have := congrFun (hid (Pi.single b 1)) a
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, hw, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    simp only [hs'row]
    rw [this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem intAf_mul' {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by
  rw [map_mul]
  exact mul_mem (hα v) (hβ v)

theorem latO_mxAt {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : MxAt P u := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hw
    intro i j
    exact tmul_mem_idAt hα _
  | zero => intro i j; exact zero_mem _
  | add x y _ _ hx hy => intro i j; exact add_mem (hx i j) (hy i j)
  | neg x _ hx => intro i j; exact neg_mem (hx i j)

theorem gen_mulVec (S T : HSp D) (α β : Af D.host.F) (a : D.host.E) (s x : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) *ᵥ
      (fun j => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x j)) =
    fun i => pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] ((a * ∑ k, ∑ j, star (s k) * S.gram k j * x j) * t i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.tmul_sum]
  have hp : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl
  rw [hp]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem latO_maps {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) {P : Pl D → Prop} {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) {y : Fin S.rank → AE D} (hy : y ∈ latV S LS P) :
    u *ᵥ y ∈ latA T LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
      rw [Set.mem_singleton_iff] at hc
      subst hc
      rw [gen_mulVec]
      obtain ⟨b, hb⟩ := (hS.2 x).1 hx s hs
      refine AddSubgroup.subset_closure ⟨α * β, intAf_mul' hαi hβi,
        fun v hv => by rw [map_mul, hα v hv, zero_mul], b • a, ?_, t, ht, ?_⟩
      · exact Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) b ha
      · funext i
        congr 1
        rw [Algebra.smul_def]
        show _ = (b : D.host.E) * a * t i
        rw [hb]
        ring
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
    | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz
  | zero => rw [Matrix.zero_mulVec]; exact zero_mem _
  | add w w' _ _ hw hw' => rw [Matrix.add_mulVec]; exact add_mem hw hw'
  | neg w _ hw => rw [Matrix.neg_mulVec]; exact neg_mem hw

def rowMul (S T : HSp D) (s' : Fin S.rank → D.host.E) (z : Fin T.rank → AE D) : WO S T :=
  Matrix.of fun k j => z k * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (∑ l, star (s' l) * S.gram l j))

theorem rowMul_mem {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {s' : Fin S.rank → D.host.E}
    (hs' : s' ∈ LS) {z : Fin T.rank → AE D} (hz : z ∈ latA T LT P) :
    rowMul S T s' z ∈ latO S T (LS : Set _) (LT : Set _) P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, s', hs', x, hx, ?_⟩
    ext k j
    simp only [rowMul, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero =>
    have : rowMul S T s' 0 = 0 := by ext k j; simp [rowMul]
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : rowMul S T s' (z + z') = rowMul S T s' z + rowMul S T s' z' := by ext k j; simp [rowMul, add_mul]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : rowMul S T s' (-z) = -rowMul S T s' z := by ext k j; exact neg_mul (z k) _
    rw [this]; exact neg_mem hz

theorem mem_latO_iff : ∀ (D : D7) (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (P : Pl D → Prop) (u : WO S T), u ∈ latO S T (LS : Set _) (LT : Set _) P ↔
      MxAt P u ∧ ∀ y ∈ latV S LS P, Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) y ∈ latA T LT P := by
  intro D S T LS LT hS _ P u
  refine ⟨fun hu => ⟨latO_mxAt hu, fun y hy => latO_maps hS hu hy⟩, fun ⟨hP, hmap⟩ => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := exists_dualBasis S hS
  let yv : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i l)
  have hyv : ∀ i, yv i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨indP D.host.F P, indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s i, hs i, rfl⟩
  have hu : u = ∑ i, rowMul S T (s' i) (u *ᵥ yv i) := by
    ext k j
    simp only [Matrix.sum_apply, rowMul, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, yv]
    simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← TensorProduct.tmul_sum, hdual]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; exact (mul_indP (hP k j)).symm
    · intro l _ hl; rw [if_neg hl, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hu]
  exact sum_mem fun i _ => rowMul_mem (hs' i) (hmap _ (hyv i))

end GlobalTheory.FinPl.LatMem
