import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchwartzBruhatHalfIffPullbackMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceIsometry

open GlobalTheory.SplitScalar

theorem eq_zero_of_eq_mul {c z : ℂ} (hc : c ≠ 1) (h : z = c * z) : z = 0 := by
  have : (c - 1) * z = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem isHalf_add {m n : ℕ} {a : AE D} {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x + y) :=
  fun i j => by rw [Matrix.add_apply, mul_add, hx, hy]

theorem isHalf_sub {m n : ℕ} {a : AE D} {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x - y) :=
  fun i j => by rw [Matrix.sub_apply, mul_sub, hx, hy]

theorem char_mul_conj (hψ : IsStdChar D ψ (-1)) (s t : AF D.host.F) :
    ψ s * (starRingEnd ℂ) (ψ t) = ψ (s - t) := by
  have h : ψ t * (starRingEnd ℂ) (ψ t) = 1 := by rw [Complex.mul_conj', hψ.1.2.1]; simp
  have h2 : ψ s = ψ (s - t) * ψ t := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  rw [h2, mul_assoc, h, mul_one]

theorem symplO_sub_right (x y y' : WO S T) : symplO S T x (y - y') = symplO S T x y - symplO S T x y' := by
  rw [symplO_skew, symplO_sub_left, symplO_skew S T x y, symplO_skew S T x y']
  abel

theorem exists_section {v : FinPl D} {m n : ℕ} {a : AE D} {Λ : AddSubgroup (WO S T)}
    {κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)} (h : IsCoord a Λ κ) :
    ∃ σ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → WO S T, (∀ z, IsHalf a (σ z)) ∧ (∀ z, κ (σ z) = z) ∧
      ∀ z t, IsHalf a t → σ (z + κ t) = σ z + t := by
  choose σ h1 h2 using fun z => h.2.1.surjOn (Set.mem_univ z)
  exact ⟨σ, h1, h2, fun z t ht => h.2.1.injOn (h1 _) (isHalf_add (h1 z) ht) (by rw [h2, h.1, h2])⟩

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_pair_ne_one (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : AE D}
    (ha : IsSplitIdem D a) {d : WO S T} (hd : IsHalf a d) (hn : d ∉ latO S T ΛS ΛT fun _ => True) :
    ∃ l ∈ latO S T ΛS ΛT fun _ => True, IsHalf (cA D a) l ∧ ψ (symplO S T l d) ≠ 1 := by
  by_contra hc
  push_neg at hc
  refine hn (GlobalTheory.LatVac.mem_of_char hψ hS hT (half_fin ha hd) fun u hu => ?_)
  have hb := (isSplitIdem_conj ha).1
  have h1 := hc (cA D a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu)
    ((isHalf_iff _ _).2 (by rw [smul_smul, hb]))
  rw [← (isHalf_iff _ _).1 hd, symplO_smul, symplO_skew, AddChar.map_neg_eq_inv, h1, inv_one]

theorem heisO_eigen {l : WO S T} {f : WO S T → ℂ} (h : heisO ψ S T l f = f) (x y : WO S T) :
    heisO ψ S T l (heisO ψ S T y (heisO ψ S T x f)) =
      ψ (symplO S T l y + symplO S T l x) • heisO ψ S T y (heisO ψ S T x f) := by
  rw [heisO_comm ψ S T l y, heisO_comm ψ S T l x, h, heisO_smul, smul_smul, AddChar.map_add_eq_mul]

open Classical in

theorem ipO_translates (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : AE D}
    (ha : IsSplitIdem D a) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hl : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f)
    (hn : nrm2 μ 𝓕 f = 1) {x x' y y' : WO S T} (hx : IsHalf a x) (hx' : IsHalf a x') (hy : IsHalf (cA D a) y)
    (hy' : IsHalf (cA D a) y') :
    ipO μ 𝓕 (heisO ψ S T y (heisO ψ S T x f)) (heisO ψ S T y' (heisO ψ S T x' f)) =
      if x - x' ∈ (latO S T ΛS ΛT fun _ => True) ∧ y - y' ∈ latO S T ΛS ΛT fun _ => True then
        ψ (symplO S T (y - y') x') else 0 := by
  have hb := isSplitIdem_conj ha
  have h0 : cA D a * a = 0 := by rw [mul_comm]; exact ha.2.1
  have h0' : cA D (cA D a) * cA D a = 0 := by rw [mul_comm]; exact hb.2.1
  have th : ∀ w g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (heisO ψ S T w g) := fun w g hg =>
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg w
  have I := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  have t1 := th y _ (th x _ hf)
  have t2 := th y' _ (th x' _ hf)
  have key : ∀ l, heisO ψ S T l f = f → ψ (symplO S T l (y - y') + symplO S T l (x - x')) ≠ 1 →
      ipO μ 𝓕 (heisO ψ S T y (heisO ψ S T x f)) (heisO ψ S T y' (heisO ψ S T x' f)) = 0 := fun l h hne => by
    refine eq_zero_of_eq_mul hne ?_
    have e := ((I _ _ t1 t2).2.2.2.2.2.2.1 l).1
    rw [heisO_eigen h, heisO_eigen h, ((I _ _ t1 (GlobalTheory.WeilVacMove.isTheta_smul _ t2)).2.2.1 _).1,
      ((I _ _ t1 t2).2.2.1 _).2, ← mul_assoc, char_mul_conj hψ] at e
    rw [symplO_sub_right, symplO_sub_right, sub_add_sub_comm, e]
  split_ifs with h
  · have e1 : heisO ψ S T x f = heisO ψ S T x' f := by
      rw [← add_sub_cancel x' x, heisO_add_of_orth ψ S T (symplO_eq_zero S T h0 hx' (isHalf_sub hx hx')),
        hl.2 a ha _ h.1 (isHalf_sub hx hx')]
    have e2 : heisO ψ S T y (heisO ψ S T x' f) =
        ψ (symplO S T (y - y') x') • heisO ψ S T y' (heisO ψ S T x' f) := by
      have := heisO_eigen (hl.2 _ hb _ h.2 (isHalf_sub hy hy')) x' y'
      rw [symplO_eq_zero S T h0' (isHalf_sub hy hy') hy', zero_add] at this
      rw [← this, ← heisO_add_of_orth ψ S T (symplO_eq_zero S T h0' (isHalf_sub hy hy') hy'), sub_add_cancel]
    rw [e1, e2, ((I _ _ t2 t2).2.2.1 _).1, ((I _ _ (th x' _ hf) (th x' _ hf)).2.2.2.2.2.2.1 y').1,
      ((I _ _ hf hf).2.2.2.2.2.2.1 x').1, (I _ _ hf hf).2.2.2.2.1, hn, Complex.ofReal_one, mul_one]
  · rcases not_and_or.1 h with h | h
    · obtain ⟨l, hl1, hl2, hl3⟩ := exists_pair_ne_one hψ hS hT ha (isHalf_sub hx hx') h
      refine key l (hl.2 _ hb l hl1 hl2) ?_
      rwa [symplO_eq_zero S T h0' hl2 (isHalf_sub hy hy'), zero_add]
    · obtain ⟨l, hl1, hl2, hl3⟩ := exists_pair_ne_one hψ hS hT hb (isHalf_sub hy hy') h
      rw [GlobalTheory.DualPairCheck.cA_cA] at hl2
      refine key l (hl.2 _ ha l hl1 hl2) ?_
      rwa [symplO_eq_zero S T h0 hl2 (isHalf_sub hx hx'), add_zero]

theorem halfInd_add {a : AE D} {Λ : AddSubgroup (WO S T)} {l : WO S T} (hl : l ∈ Λ) (hl' : IsHalf a l) (t : WO S T) :
    halfInd a Λ (t + l) = halfInd a Λ t := by
  classical
  unfold halfInd
  refine if_congr (and_congr (Λ.add_mem_cancel_right hl) ⟨fun h => ?_, fun h => isHalf_add h hl'⟩) rfl rfl
  simpa using isHalf_sub h hl'

open Classical in

theorem integral_waves (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : AE D}
    (ha : IsSplitIdem D a) {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (ν : Measure G)
    [ν.IsAddRightInvariant] {κ : WO S T → G} {σ : G → WO S T} (h1 : ∀ z, IsHalf a (σ z)) (h2 : ∀ z, κ (σ z) = z)
    (h3 : ∀ z t, IsHalf a t → σ (z + κ t) = σ z + t) (h4 : ∀ t, IsHalf a t → σ (κ t) = t)
    (hm : MeasurableSet (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t}))
    {x x' y y' : WO S T} (hx : IsHalf a x) (hx' : IsHalf a x') (hy : IsHalf (cA D a) y) (hy' : IsHalf (cA D a) y') :
    ∫ z, (ψ (symplO S T (σ z) y) * halfInd a (latO S T ΛS ΛT fun _ => True) (σ z + x)) *
        (starRingEnd ℂ) (ψ (symplO S T (σ z) y') * halfInd a (latO S T ΛS ΛT fun _ => True) (σ z + x')) ∂ν =
      ((ν (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t})).toReal : ℂ) *
        if x - x' ∈ (latO S T ΛS ΛT fun _ => True) ∧ y - y' ∈ latO S T ΛS ΛT fun _ => True then
          ψ (symplO S T (y - y') x') else 0 := by
  set Λ := latO S T ΛS ΛT fun _ => True with hΛ
  let F : WO S T → ℂ := fun t => ψ (symplO S T t (y - y')) * (halfInd a Λ (t + x) * (starRingEnd ℂ) (halfInd a Λ (t + x')))
  have eF : ∀ t, (ψ (symplO S T t y) * halfInd a Λ (t + x)) *
      (starRingEnd ℂ) (ψ (symplO S T t y') * halfInd a Λ (t + x')) = F t := fun t => by
    rw [map_mul, mul_mul_mul_comm, char_mul_conj hψ, ← symplO_sub_right]
  have tr : ∀ t, IsHalf a t → ∫ z, F (σ z) ∂ν = ∫ z, F (σ z + t) ∂ν := fun t ht => by
    rw [← integral_add_right_eq_self (fun z => F (σ z)) (κ t)]
    simp only [h3 _ t ht]
  simp only [eF]
  split_ifs with h
  · have hx0 : IsHalf a (-x') := fun i j => by rw [Matrix.neg_apply, mul_neg, hx']
    rw [tr _ hx0]
    have e : ∀ z, F (σ z + -x') = Set.indicator (κ '' {t | t ∈ Λ ∧ IsHalf a t})
        (fun _ => ψ (symplO S T (y - y') x')) z := fun z => by
      have e1 : σ z + -x' + x = σ z + (x - x') := by abel
      simp only [F]
      rw [e1, neg_add_cancel_right, halfInd_add h.1 (isHalf_sub hx hx')]
      by_cases hz : σ z ∈ Λ
      · rw [Set.indicator_of_mem (show z ∈ κ '' {t | t ∈ Λ ∧ IsHalf a t} from ⟨σ z, ⟨hz, h1 z⟩, h2 z⟩), halfInd, if_pos ⟨hz, h1 z⟩, map_one, mul_one, mul_one,
          ← sub_eq_add_neg, symplO_sub_left, sub_eq_add_neg (symplO S T (σ z) _), AddChar.map_add_eq_mul,
          GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hz h.2, one_mul, ← symplO_skew]
      · rw [Set.indicator_of_notMem, halfInd, if_neg fun h => hz h.1, zero_mul, mul_zero]
        rintro ⟨t, ht, rfl⟩
        exact hz (by rw [h4 t ht.2]; exact ht.1)
    simp only [e]
    rw [integral_indicator_const _ hm, Complex.real_smul]
    rfl
  · rw [mul_zero]
    rcases not_and_or.1 h with h | h
    · refine (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)).trans (integral_zero _ _)
      simp only [F, halfInd]
      split_ifs with p q
      · exact absurd (by simpa using sub_mem p.1 q.1) h
      all_goals simp
    · obtain ⟨l, hl1, hl2, hl3⟩ := exists_pair_ne_one hψ hS hT (isSplitIdem_conj ha) (isHalf_sub hy hy') h
      rw [GlobalTheory.DualPairCheck.cA_cA] at hl2
      refine eq_zero_of_eq_mul hl3 ?_
      conv_lhs => rw [tr l hl2]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [F]
      rw [add_right_comm _ l x, add_right_comm _ l x', halfInd_add hl1 hl2, halfInd_add hl1 hl2,
        GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul]
      ring

theorem placeModel_isometry : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (a : AE D), IsSplitIdem D a → ∀ (m n : ℕ) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a (latO S T ΛS ΛT fun _ => True) κ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n) (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t}) ≠ 0 ∧ GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n) (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t}) ≠ ⊤ ∧ ∀ Φ₁ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), ∀ Φ₂ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), ((GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n) (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t})).toReal : ℂ) * ipO μ 𝓕 (Tm (pull a κ Φ₁)) (Tm (pull a κ Φ₂)) = GlobalTheory.SplitWeil.ip ν Φ₁ Φ₂ := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v a ha m n κ hκ Tm hTm ν hν
  have hψ := base_std hB
  have hS := hB.2.2.1
  have hT := hB.2.2.2.1
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv D.host.F v)
  haveI : BorelSpace (Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
    inferInstanceAs (BorelSpace (Fin m → Fin n → Fv D.host.F v))
  haveI : (GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : SecondCountableTopology (Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → Fv D.host.F v))
  obtain ⟨σ, h1, h2, h3⟩ := exists_section hκ
  have h4 : ∀ t, IsHalf a t → σ (κ t) = t := fun t ht => hκ.2.1.injOn (h1 _) ht (h2 _)
  have hp : ∀ Φ, pull a κ Φ ∘ σ = Φ := fun Φ => funext fun z => by
    simp only [Function.comp, pull, if_pos (h1 z), h2]
  refine ⟨(hκ.2.2.1.measure_pos _ ⟨κ 0, 0, ⟨zero_mem _, fun _ _ => mul_zero _⟩, rfl⟩).ne',
    hκ.2.2.2.measure_lt_top.ne, ?_⟩
  obtain ⟨w1, w2⟩ := GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates D ψ S T ΛS ΛT hψ hS hT a ha.1 ha.2.1 (infPart_splitIdem ha)
  obtain ⟨c1, c2⟩ := GlobalTheory.T.isSchwartzBruhatHalf_iff_pullback_matrix D S T v m n a _ κ hκ
  have I := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  set W := {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧
    Ψ = fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)} with hW
  have good : ∀ Ψ ∈ Submodule.span ℂ W, IsThetaFunO ψ S T (Tm Ψ) ∧
      Ψ ∘ σ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)) := fun Ψ h => by
    induction h using Submodule.span_induction with
    | mem Ψ h =>
      obtain ⟨x, y, hx, hy, rfl⟩ := h
      obtain ⟨Φ, hΦ, e⟩ := c2 _ (w1 x y hx hy).1
      refine ⟨?_, by rw [e, hp]; exact hΦ⟩
      rw [(w1 x y hx hy).2 f₀ Tm hTm]
      exact GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (base_theta hB) x) y
    | zero => exact ⟨by rw [map_zero]; exact GlobalTheory.WeilVacMove.isTheta_zero, zero_mem _⟩
    | add _ _ _ _ p q => exact ⟨by rw [map_add]; exact GlobalTheory.WeilVacMove.isTheta_add p.1 q.1, add_mem p.2 q.2⟩
    | smul c _ _ p =>
      exact ⟨by rw [map_smul]; exact GlobalTheory.WeilVacMove.isTheta_smul c p.1, Submodule.smul_mem _ c p.2⟩
  have int : ∀ Ψ ∈ Submodule.span ℂ W, ∀ Ψ' ∈ Submodule.span ℂ W,
      Integrable (fun z => Ψ (σ z) * (starRingEnd ℂ) (Ψ' (σ z))) (GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n)) :=
    fun Ψ h Ψ' h' => Continuous.integrable_of_hasCompactSupport
      ((good Ψ h).2.1.continuous.mul (Complex.continuous_conj.comp (good Ψ' h').2.1.continuous))
      (HasCompactSupport.mul_right (good Ψ h).2.2)
  have main : ∀ Ψ ∈ Submodule.span ℂ W, ∀ Ψ' ∈ Submodule.span ℂ W,
      ((GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n)
        (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t})).toReal : ℂ) * ipO μ 𝓕 (Tm Ψ) (Tm Ψ') =
      ∫ z, Ψ (σ z) * (starRingEnd ℂ) (Ψ' (σ z)) ∂(GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n)) := fun Ψ h Ψ' h' => by
    induction h, h' using Submodule.span_induction₂ with
    | mem_mem Ψ Ψ' h h' =>
      obtain ⟨x, y, hx, hy, rfl⟩ := h
      obtain ⟨x', y', hx', hy', rfl⟩ := h'
      rw [(w1 x y hx hy).2 f₀ Tm hTm, (w1 x' y' hx' hy').2 f₀ Tm hTm,
        ipO_translates hψ hS hT ha hμ (base_theta hB) hB.2.2.2.2.2.lat (restrictedTensorBasePoint_norm_sq hB hμ) hx hx' hy hy']
      exact (integral_waves hψ hS hT ha _ h1 h2 h3 h4 hκ.2.2.1.measurableSet hx hx' hy hy').symm
    | zero_left => simp [ipO]
    | zero_right => simp [ipO]
    | add_left x y z hx hy hz p q =>
      rw [map_add, ((I _ _ (good x hx).1 (good z hz).1).2.2.2.1 _ (good y hy).1).1, mul_add, p, q,
        ← integral_add (int x hx z hz) (int y hy z hz)]
      simp only [Pi.add_apply, add_mul]
    | add_right x y z hx hy hz p q =>
      rw [map_add, ((I _ _ (good y hy).1 (good x hx).1).2.2.2.1 _ (good z hz).1).2, mul_add, p, q,
        ← integral_add (int x hx y hy) (int x hx z hz)]
      simp only [Pi.add_apply, map_add, mul_add]
    | smul_left c x y hx hy p =>
      rw [map_smul, ((I _ _ (good x hx).1 (good y hy).1).2.2.1 c).1, mul_left_comm, p, ← integral_const_mul]
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    | smul_right c x y hx hy p =>
      rw [map_smul, ((I _ _ (good x hx).1 (good y hy).1).2.2.1 c).2, mul_left_comm, p, ← integral_const_mul]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm]
  intro Φ₁ p Φ₂ q
  rw [main _ (w2 _ (c1 _ p)) _ (w2 _ (c1 _ q))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact congrArg₂ (fun s t => s * (starRingEnd ℂ) t) (congrFun (hp Φ₁) z) (congrFun (hp Φ₂) z)

end GlobalTheory.PlaceIsometry

end
