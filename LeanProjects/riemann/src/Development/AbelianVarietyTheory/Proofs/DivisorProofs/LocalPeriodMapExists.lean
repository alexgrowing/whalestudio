import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCInfOfIsDualRiemann
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAbelianLogarithm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorsionForm
open Filter Topology GlobalTheory.HermFrame GlobalTheory.ShFam.Hor.LogCh
open scoped ComplexOrder

namespace GlobalTheory.NormPeriods

section Linear

variable {g : ℕ}

def colR (p : Fin g ⊕ Fin g → Fin g → ℂ) : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => p (.inr j) i

def colL (p : Fin g ⊕ Fin g → Fin g → ℂ) : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => p (.inl j) i

theorem normalise {G : Matrix (Fin g) (Fin g) ℂ} (hG : G.PosDef) {p : Fin g ⊕ Fin g → Fin g → ℂ}
    (h : ∀ i j, (form G (p i) (p j)).im = -Matrix.J (Fin g) ℝ i j) :
    IsUnit (colR p).det ∧ IsSiegel ((colR p)⁻¹ * colL p) ∧
      (∀ z w, form G (colR p *ᵥ z) (colR p *ᵥ w) = GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.herm ((colR p)⁻¹ * colL p) z w) ∧
      ∀ x, colR p *ᵥ per ((colR p)⁻¹ * colL p) x = ∑ i, x i • p i := by
  set A := colR p with hA
  set B := colL p with hB
  have cA (k) : A *ᵥ Pi.single k 1 = p (.inr k) := RiemannRel.of_cols_mulVec (fun k => p (.inr k)) k
  have cB (k) : B *ᵥ Pi.single k 1 = p (.inl k) := RiemannRel.of_cols_mulVec (fun k => p (.inl k)) k
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm G z z).re := fun z hz =>
    (Complex.pos_iff.1 ((posDef_iff.1 hG).2 z hz)).1
  have hM : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0 := fun j k => by
    rw [← RiemannRel.hermForm_col, cA, cA]
    exact (h _ _).trans (by simp [Matrix.J])
  have hN : ∀ j k, ((Aᵀ * G * B.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k := fun j k => by
    rw [← RiemannRel.hermForm_col, cA, cB]
    exact (h _ _).trans (by simp [Matrix.J])
  have hK : ∀ j k, ((Bᵀ * G * B.map (starRingEnd ℂ)) j k).im = 0 := fun j k => by
    rw [← RiemannRel.hermForm_col, cB, cB]
    exact (h _ _).trans (by simp [Matrix.J])
  have hdet := RiemannRel.det_ne_zero G A B hpos hM hN
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  set τ := A⁻¹ * B with hτ
  have hAB : A * τ = B := by rw [hτ, ← Matrix.mul_assoc, mul_nonsing_inv A hu, Matrix.one_mul]
  have hs := RiemannRel.symm_posDef G A τ hG.1 hdet hpos hM (by rw [hAB]; exact hN) (by rw [hAB]; exact hK)
  refine ⟨hu, hs, fun z w => ?_, fun x => ?_⟩
  · set M := Aᵀ * G * A.map (starRingEnd ℂ) with hMd
    have hRY : M.map Complex.re * τ.map Complex.im = 1 := by
      have hN' : Aᵀ * G * B.map (starRingEnd ℂ) = M * τ.map (starRingEnd ℂ) := by
        rw [← hAB, Matrix.map_mul, hMd]; simp only [Matrix.mul_assoc]
      rw [hN'] at hN
      ext j k
      have := hN j k
      simp only [mul_apply, Complex.im_sum, map_apply, Complex.mul_im, hM, Complex.conj_im, zero_mul, add_zero,
        mul_neg, Finset.sum_neg_distrib, neg_inj] at this
      rw [← this]
      simp [mul_apply]
    have e : ((τ.map Complex.im)⁻¹).map (fun t : ℝ => (t : ℂ)) = M := by
      rw [inv_eq_left_inv hRY]
      ext j k
      exact Complex.ext (by simp) (by simp [hM])
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.herm, e, ← dotProduct_mulVec]
    exact RiemannRel.hermForm_mulVec G A A z w
  · rw [per, ← hs.1.eq, vecMul_transpose, mulVec_add, mulVec_mulVec, hAB, Fintype.sum_sum_type]
    funext i
    simp [mulVec, dotProduct, hA, hB, colR, colL, mul_comm]

theorem mem_stdLat {l : Fl g} : l ∈ stdLat g ↔ ∃ m : Fin g ⊕ Fin g → ℤ, l = fun i => (m i : ℝ) := by
  rw [stdLat, Module.Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr, Set.mem_range, eq_intCast]
  exact ⟨fun h => by choose m hm using h; exact ⟨m, funext fun i => (hm i).symm⟩, fun ⟨m, hm⟩ i => ⟨m i, by rw [hm]⟩⟩

theorem exists_sympl (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (Ef : LinearMap.BilinForm ℤ Λ) (hE : ∀ a b : Λ, (Ef a b : ℝ) = (form H a b).im) (hb : Function.Bijective Ef) :
    ∃ p : Fin g ⊕ Fin g → Fin g → ℂ, LinearIndependent ℝ p ∧
      (∀ w, w ∈ Λ ↔ ∃ m : Fin g ⊕ Fin g → ℤ, w = ∑ j, m j • p j) ∧
      ∀ i j, (form H (p i) (p j)).im = -Matrix.J (Fin g) ℝ i j := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  have hr : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have halt : Ef.IsAlt := fun a => by
    have h := (hE a a).trans (Complex.conj_eq_iff_im.1 (conj_form hH _ _))
    exact_mod_cast h
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank halt hb hr
  refine ⟨fun j => (b j : Fin g → ℂ), ?_, fun w => ⟨fun hw => ?_, ?_⟩, fun i j => ?_⟩
  · have he : (fun j => (b j : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ Λ) :=
      funext fun j => (Module.Basis.ofZLatticeBasis_apply ℝ Λ b j).symm
    rw [he]
    exact (b.ofZLatticeBasis ℝ Λ).linearIndependent
  · refine ⟨b.repr ⟨w, hw⟩, ?_⟩
    have h := congrArg (fun x : Λ => (x : Fin g → ℂ)) (b.sum_repr ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · rintro ⟨m, rfl⟩
    exact Λ.sum_mem fun j _ => Λ.smul_mem _ (b j).2
  · rw [← hE]
    rcases i with i | i <;> rcases j with j | j
    · simp [hb.left_left, Matrix.J]
    · simp [hb.left_right, Matrix.J, one_apply]
    · rw [hb.right_left halt]
      by_cases e : i = j <;> simp [Matrix.J, one_apply, e]
    · simp [hb.right_right, Matrix.J]

theorem exists_extend {n : ℕ} {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)} {b₀ : Fin n → ℂ}
    (hK : IsLatFam B K) (hb₀ : b₀ ∈ B) {β : Fin g ⊕ Fin g → Fin g → ℂ} (hβ₁ : LinearIndependent ℝ β)
    (hβ₂ : ∀ w, w ∈ K b₀ ↔ ∃ m : Fin g ⊕ Fin g → ℤ, w = ∑ j, m j • β j) :
    ∃ p : (Fin n → ℂ) → Fin g ⊕ Fin g → Fin g → ℂ, p b₀ = β ∧ (∀ j, AnalyticAt ℂ (fun b => p b j) b₀) ∧
      ∀ᶠ b in 𝓝 b₀, ∀ w, w ∈ K b ↔ ∃ m : Fin g ⊕ Fin g → ℤ, w = ∑ j, m j • p b j := by
  let ε : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm
  have tr (c : Fin g ⊕ Fin g → Fin g → ℂ) (w : Fin g → ℂ) :
      (∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • c (ε j)) ↔ ∃ m : Fin g ⊕ Fin g → ℤ, w = ∑ j, m j • c j :=
    ⟨fun ⟨m, hm⟩ => ⟨fun j => m (ε.symm j), by rw [hm, ← ε.sum_comp]; simp⟩,
      fun ⟨m, hm⟩ => ⟨fun j => m (ε j), by rw [hm, ← ε.sum_comp]⟩⟩
  have hβK : ∀ j, β j ∈ K b₀ := fun j =>
    (hβ₂ (β j)).2 ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  choose ζ hζ0 hζa hζ using fun j => hK.2.2.2 b₀ hb₀ (β j) (hβK j)
  have hla : AnalyticAt ℂ (fun b j => ζ (ε j) b) b₀ := AnalyticAt.pi fun j => hζa (ε j)
  have hlc := hla.continuousAt
  have hlK : ∀ᶠ b in 𝓝 b₀, ∀ j, ζ (ε j) b ∈ K b :=
    Filter.eventually_all.2 fun j => IsLatFam.eventually_mem_of_graph (hζ0 _) (hζa _).continuousAt (hζ _)
  have hβ' : IsLatBasis (K b₀) ((fun b j => ζ (ε j) b) b₀) := by
    simp only [hζ0]
    exact ⟨hβ₁.comp ε ε.injective, fun w => (hβ₂ w).trans (tr β w).symm⟩
  set R : ℝ := ∑ j, (‖β (ε j)‖ + 1) with hR
  have hball := (isCompact_closedBall (0 : Fin g → ℂ) R).eventually_forall_of_forall_eventually (x₀ := b₀)
    (P := fun b w => w ∈ K b → ∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • ζ (ε j) b)
    fun y _ => IsLatFam.eventually_intComb hK hb₀ hlc hlK hβ' y
  have hli : ∀ᶠ b in 𝓝 b₀, LinearIndependent ℝ (fun j => ζ (ε j) b) := hlc.tendsto.eventually hβ'.1.eventually
  have hnorm : ∀ᶠ b in 𝓝 b₀, ∀ j, ‖ζ (ε j) b‖ ≤ ‖β (ε j)‖ + 1 := by
    refine Filter.eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun b => ‖ζ (ε j) b‖) b₀ := (hζa _).continuousAt.norm
    have hlt : (fun b => ‖ζ (ε j) b‖) b₀ < (fun _ => ‖β (ε j)‖ + 1) b₀ := by simp [hζ0]
    filter_upwards [hc.eventually_lt continuousAt_const hlt] with b hb
    exact hb.le
  refine ⟨fun b j => ζ j b, funext hζ0, hζa, ?_⟩
  filter_upwards [hball, hli, hnorm, hlK, hK.1.mem_nhds hb₀] with b h1 h2 h3 h4 h5 w
  obtain ⟨H, hH⟩ := hK.2.1 b h5
  rw [← hH, ← tr (fun j => ζ j b)]
  refine (isLatBasis_of_ball H _ R h2 (fun j => ?_) (Finset.sum_le_sum fun j _ => h3 j) fun w hw hwH => ?_).2 w
  · show ζ (ε j) b ∈ (H : Set (Fin g → ℂ)); rw [hH]; exact h4 j
  · exact h1 w hw (by rw [← hH]; exact hwH)

end Linear

section Fibre

open MonoidalCategory CartesianMonoidalCategory Limits

variable {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S}

variable (P y) in

theorem exists_unimodular : ∃ (d : P.RiemannData y) (Ef : LinearMap.BilinForm ℤ d.u.Λ),
    (∀ a b : d.u.Λ, (Ef a b : ℝ) = (form d.H a b).im) ∧ Function.Bijective Ef := by
  have h := isGrpPullback_pullback P.A y
  obtain ⟨L, hL, ha, hk, hc⟩ := P.isPol.2.2 ℂ y
  have hB : IsAbelianScheme ((Over.pullback y).obj P.A) := PolPull.isAbelianScheme_of_isGrpPullback P.isAb h
  obtain ⟨L', hL', hr, hs, ha', hk', hl⟩ := RiemannExists.exists_sym_translate ℂ _ hB L hL ha hk
  let Q' : Out.PolAV (Sp ℂ) := ⟨(Over.pullback y).obj P.A, hB, P.g,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim, L', hL', hr, hs, ha', hk'⟩
  obtain ⟨rig, hrg⟩ := Q'.rigid
  obtain ⟨u, H, χ, Ef, hH, -, -, -, -, -, h₁, h₂, -⟩ := thetaUnifAV_all Q' rig hrg
  exact ⟨⟨(Over.pullback y).obj P.A, _, h, L', hL', hc.trans hl.symm, u, H, χ, hH⟩, Ef, h₁, h₂⟩

theorem im_form_eq (d d' : P.RiemannData y) (T T' : (Fin P.g → ℂ) ≃L[ℂ] (Fin P.g → ℂ))
    {e : (Fin P.g → ℂ) → (Sp ℂ ⟶ P.A.left)} (he : IsHolTo univ e)
    (hT : ∀ z, e z = (d.u.ex (T z)).left ≫ d.φ) (hT' : ∀ z, e z = (d'.u.ex (T' z)).left ≫ d'.φ)
    {l l' : Fin P.g → ℂ} (hl : T l ∈ d.u.Λ) (hl' : T l' ∈ d.u.Λ) :
    (form d'.H (T' l) (T' l')).im = (form d.H (T l) (T l')).im := by
  classical
  have hm {l} (hl : T l ∈ d.u.Λ) : T' l ∈ d'.u.Λ := by
    rwa [HodgeSmooth.mem_iff, ← hT', hT, ← HodgeSmooth.mem_iff]
  let D : (Fin 1 → ℂ) → (P.RiemannData y × ((Fin P.g → ℂ) ≃L[ℂ] (Fin P.g → ℂ))) := fun b =>
    if b = 0 then (d, T) else (d', T')
  have hD (b) : D b = (d, T) ∨ D b = (d', T') := by
    by_cases h : b = 0 <;> simp [D, h]
  have key := RiemannConst.eventually_im_form_eq S P 1 univ (fun _ => y) 0 (fun b => (D b).1) (fun q => e q.2)
    (fun b => (D b).2) (fun _ => l) (fun _ => l') isOpen_univ trivial
    (by simpa using RiemannConst.isHolTo_comp_clm he (ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) _))
    (fun b _ z => by
      rcases hD b with h | h <;> rw [h]
      exacts [hT z, hT' z]) continuousOn_const continuousOn_const
    (fun b _ => by
      rcases hD b with h | h <;> rw [h]
      exacts [⟨hl, hl'⟩, ⟨hm hl, hm hl'⟩])
  obtain ⟨b, hb, hb0⟩ := ((key.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and self_mem_nhdsWithin).exists
  have e₀ : D 0 = (d, T) := if_pos rfl
  have e₁ : D b = (d', T') := if_neg hb0
  rw [e₀, e₁] at hb
  exact hb

end Fibre

theorem isLatFam_ker {S : Scheme.{0}} (P : PPAS S) {m g : ℕ} {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ S)}
    (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ P.A)) (hB : IsOpen B) (hy : IsHolTo B y)
    (hex : IsHolTo (B ×ˢ univ) fun q : (Fin m → ℂ) × (Fin g → ℂ) => (e q.1 q.2).left)
    (hadd : ∀ b ∈ B, ∀ z w, e b (z + w) = e b z * e b w)
    (hd : ∀ b ∈ B, ∀ v : epsPt (y b) ⟶ P.A,
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e b 0).left →
        ∃! w, IsDerivAt0 (fun z => (e b z).left) w v.left) :
    IsLatFam B fun b => {w | e b w = 1} := by
  have := P.isAb.comm
  have := P.isAb.proper
  have hD := hB.prod (isOpen_univ (X := Fin g → ℂ))
  have hzero : ∀ b ∈ B, e b 0 = 1 := fun b hb => UnifPoint.map_zero_of_add (hadd b hb)
  refine ⟨hB, fun b hb => ?_, ?_, fun b₀ hb₀ w₀ hw₀ => ?_⟩
  · refine ⟨{ carrier := {w | e b w = 1}, add_mem' := fun {u v} hu hv => ?_, zero_mem' := hzero b hb,
              neg_mem' := fun {u} hu => ?_ }, rfl⟩
    · show e b (u + v) = 1
      rw [hadd b hb, show e b u = 1 from hu, show e b v = 1 from hv, _root_.one_mul]
    · show e b (-u) = 1
      have h := hadd b hb (-u) u
      rw [neg_add_cancel, hzero b hb, show e b u = 1 from hu, _root_.mul_one] at h
      exact h.symm
  · have h := KerFam.isOpen_ne_one hD (y := fun q : (Fin m → ℂ) × (Fin g → ℂ) => y q.1) (fun q => e q.1 q.2)
      (fun q hq => by
        have := RelExp.HolAt.comp (a := y) (φ := Prod.fst) (v₀ := q) ⟨B, hB, hq.1, hy⟩ analyticAt_fst
        exact this) fun q hq => ⟨_, hD, hq, hex⟩
    refine (congrArg IsOpen (Set.ext fun q => ?_)).mpr h
    exact ⟨fun hq => ⟨⟨hq.1, trivial⟩, hq.2⟩, fun hq => ⟨hq.1.1, hq.2⟩⟩
  · exact KerFam.exists_graph P.isAb.smooth P.isAb.geomConnected e hB hy hex hb₀ hw₀ (hadd b₀ hb₀)
      fun v hv hv' => hd b₀ hb₀ (Over.homMk v hv) (by rw [hzero b₀ hb₀]; exact hv')

theorem exists_family {S : Scheme.{0}} (P : PPAS S) {m : ℕ} {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ S)}
    {b₀ : Fin m → ℂ} (hB : IsOpen B) (hb₀ : b₀ ∈ B) (hy : IsHolTo B y) :
    ∃ C : Set (Fin m → ℂ), IsOpen C ∧ b₀ ∈ C ∧ ∃ (τ : (Fin m → ℂ) → Matrix (Fin P.g) (Fin P.g) ℂ)
      (ex : (Fin m → ℂ) × (Fin P.g → ℂ) → (Sp ℂ ⟶ P.A.left)),
      IsPeriodMap C τ ∧ IsHolTo (C ×ˢ univ) ex ∧ ∀ b ∈ C,
        (∀ z, ex (b, z) ≫ P.A.hom = y b) ∧
        (∀ z w, ∀ x x' : Over.mk (y b) ⟶ P.A, x.left = ex (b, z) → x'.left = ex (b, w) →
          (x * x').left = ex (b, z + w)) ∧
        (∀ x : Over.mk (y b) ⟶ P.A, ∃ z, x.left = ex (b, z)) ∧
        (∀ z, ex (b, z) = y b ≫ unitSec P.A ↔ ∃ l ∈ stdLat P.g, z = per (τ b) l) ∧
        ∀ d : P.RiemannData (y b), ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ),
          (∀ z, (d.u.ex (F z)).left ≫ d.φ = ex (b, z)) ∧
          ∀ z w, HermFrame.form d.H (F z) (F w) = GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.herm (τ b) z w := by
  classical
  have := P.isAb.comm
  obtain ⟨g, B₁, e, hB₁, hb₁, he, -⟩ := RelExp.exists_relative_exp_of_smooth S P.A m B y b₀ P.isAb.smooth
    P.isAb.geomConnected hB hb₀ hy
  have hcmp := fun b hb (d : P.RiemannData (y b)) => ExpCompare.exists_equiv_of_exp S P (y b) d g (e b) (he b hb).2.1
    (he b hb).2.2.1 (he b hb).2.2.2.1 (he b hb).2.2.2.2.2 (he b hb).2.2.2.2.1
  choose d Ef hEf hbij using fun b => exists_unimodular P (y b)
  obtain rfl : g = P.g := by
    obtain ⟨T, -⟩ := hcmp b₀ hb₁ (d b₀)
    simpa using T.toLinearEquiv.finrank_eq
  have : Nonempty ((Fin P.g → ℂ) ≃L[ℂ] (Fin P.g → ℂ)) := ⟨.refl _ _⟩
  choose! T hT using fun b hb => hcmp b hb (d b)
  let ε : (Fin m → ℂ) × (Fin P.g → ℂ) → (Sp ℂ ⟶ P.A.left) := fun q => (e q.1 q.2).left
  have hol {C : Set (Fin m → ℂ)} (hC : IsOpen C) (h : C ⊆ B₁) : IsHolTo (C ×ˢ univ) ε :=
    RelExp.isHolTo_of_holAt (hC.prod isOpen_univ) fun q hq => (he q.1 (h hq.1)).1 q.2
  have hker : ∀ b ∈ B₁, ∀ z, e b z = 1 ↔ T b z ∈ (d b).u.Λ := fun b hb z => by
    rw [HodgeSmooth.mem_iff, ← hT b hb, ← HodgeSmooth.one_left]
    exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩
  have hK := isLatFam_ker P e (hB₁.inter hB)
    (RelExp.isHolTo_of_holAt (hB₁.inter hB) fun b hb => ⟨B, hB, hb.2, hy⟩)
    (hol (hB₁.inter hB) inter_subset_left) (fun b hb => (he b hb.1).2.1) fun b hb => (he b hb.1).2.2.2.2.2
  have := (d b₀).u.discrete
  obtain ⟨β, hβ₁, hβ₂, hβ₃⟩ := exists_sympl (d b₀).u.Λ (d b₀).u.full (d b₀).isAH.1 (Ef b₀) (hEf b₀) (hbij b₀)
  obtain ⟨p, hp₀, hpa, hp⟩ := exists_extend hK ⟨hb₁, hb₀⟩ (β := fun j => (T b₀).symm (β j))
    (hβ₁.map' (((T b₀).symm : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)).restrictScalars ℝ)
      (LinearMap.ker_eq_bot.2 (T b₀).symm.injective)) fun w => by
      rw [mem_setOf_eq, hker b₀ hb₁, hβ₂]
      refine exists_congr fun n => ?_
      rw [← (T b₀).symm.injective.eq_iff, (T b₀).symm_apply_apply, map_sum]
      simp only [map_zsmul]
  obtain ⟨C₁, hC₁, hC₁o, hC₁b⟩ := eventually_nhds_iff.1 ((eventually_all.2 fun j => (hpa j).eventually_analyticAt).and
    (hp.and (hB₁.mem_nhds hb₁)))
  have hpΛ : ∀ b ∈ C₁, ∀ j, T b (p b j) ∈ (d b).u.Λ := fun b hb j =>
    (hker b (hC₁ b hb).2.2 _).1 (((hC₁ b hb).2.1 _).2 ⟨Pi.single j 1, by simp [Pi.single_apply]⟩)
  have hconst : ∀ᶠ b in 𝓝 b₀, ∀ i j, (form (d b).H (T b (p b i)) (T b (p b j))).im = -Matrix.J (Fin P.g) ℝ i j :=
    eventually_all.2 fun i => eventually_all.2 fun j => by
      have := RiemannConst.eventually_im_form_eq S P m C₁ y b₀ d ε T (fun b => p b i) (fun b => p b j) hC₁o hC₁b
        (hol hC₁o fun b hb => (hC₁ b hb).2.2) (fun b hb => hT b (hC₁ b hb).2.2)
        (fun b hb => ((hC₁ b hb).1 i).continuousAt.continuousWithinAt)
        (fun b hb => ((hC₁ b hb).1 j).continuousAt.continuousWithinAt) fun b hb => ⟨hpΛ b hb i, hpΛ b hb j⟩
      simpa only [hp₀, ContinuousLinearEquiv.apply_symm_apply, hβ₃] using this
  obtain ⟨C, hC, hCo, hCb⟩ := eventually_nhds_iff.1 (hconst.and (hC₁o.mem_nhds hC₁b))
  have hCB : C ⊆ B₁ := fun b hb => (hC₁ b (hC b hb).2).2.2
  have hnorm : ∀ b ∈ C, ∀ (d' : P.RiemannData (y b)) (T' : (Fin P.g → ℂ) ≃L[ℂ] (Fin P.g → ℂ)),
      (∀ z, (e b z).left = (d'.u.ex (T' z)).left ≫ d'.φ) →
      IsUnit (colR (p b)).det ∧ IsSiegel ((colR (p b))⁻¹ * colL (p b)) ∧
      (∀ z w, form d'.H (T' (colR (p b) *ᵥ z)) (T' (colR (p b) *ᵥ w)) =
        GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.herm ((colR (p b))⁻¹ * colL (p b)) z w) ∧
      ∀ x, colR (p b) *ᵥ per ((colR (p b))⁻¹ * colL (p b)) x = ∑ i, x i • p b i := fun b hb d' T' hT' => by
    have hH (v w) : form (chg (LinearMap.toMatrix' (T' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))) d'.H) v w =
        form d'.H (T' v) (T' w) := by
      rw [form_chg, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
      rfl
    simp only [← hH]
    refine normalise (posDef_chg ?_ d'.posDef) fun i j => ?_
    · exact (LinearMap.isUnit_toMatrix'_iff).2 ((Module.End.isUnit_iff _).2 T'.bijective)
    · rw [hH, im_form_eq (d b) d' (T b) T' (he b (hCB hb)).2.2.2.1 (hT b (hCB hb)) hT' (hpΛ b (hC b hb).2 i)
        (hpΛ b (hC b hb).2 j), (hC b hb).1]
  have hn := fun b hb => hnorm b hb (d b) (T b) (hT b (hCB hb))
  have hpc : ∀ b ∈ C, ∀ j i, AnalyticAt ℂ (fun b => p b j i) b := fun b hb j =>
    analyticAt_pi_iff.1 ((hC₁ b (hC b hb).2).1 j)
  have hpd (j i) : DifferentiableOn ℂ (fun b => p b j i) C := fun b hb =>
    (hpc b hb j i).differentiableAt.differentiableWithinAt
  refine ⟨C, hCo, hCb, fun b => (colR (p b))⁻¹ * colL (p b), fun q => ε (q.1, colR (p q.1) *ᵥ q.2),
    ⟨hCo, fun i j => ?_, fun b hb => (hn b hb).2.1⟩,
    RelExp.isHolTo_of_holAt (hCo.prod isOpen_univ) fun q hq => ?_, fun b hb => ⟨fun z => Over.w _, ?_, ?_, ?_, ?_⟩⟩
  · have hh := RiemannRel.differentiableOn_left_inverse (B := C) (fun b => colR (p b)) (fun b => (colR (p b))⁻¹)
      (fun i j => hpd _ _) fun b hb => nonsing_inv_mul _ (hn b hb).1
    simp only [mul_apply]
    exact DifferentiableOn.fun_sum fun l _ => (hh i l).mul (hpd _ _)
  · refine RelExp.HolAt.comp (a := ε) (φ := fun q : (Fin m → ℂ) × (Fin P.g → ℂ) => (q.1, colR (p q.1) *ᵥ q.2))
      (v₀ := q) ((he q.1 (hCB hq.1)).1 _) (analyticAt_fst.prod (AnalyticAt.pi fun i => ?_))
    simp only [mulVec, dotProduct]
    exact Finset.analyticAt_fun_sum _ fun j _ => ((hpc q.1 hq.1 (.inr j) i).comp analyticAt_fst).mul
      (analyticAt_pi_iff.1 analyticAt_snd j)
  · intro z w x x' hx hx'
    obtain rfl : x = e b (colR (p b) *ᵥ z) := Over.OverMorphism.ext hx
    obtain rfl : x' = e b (colR (p b) *ᵥ w) := Over.OverMorphism.ext hx'
    simp only [ε, mulVec_add, (he b (hCB hb)).2.1]
  · intro x
    obtain ⟨z, rfl⟩ := (he b (hCB hb)).2.2.1 x
    exact ⟨(colR (p b))⁻¹ *ᵥ z, by simp only [ε, mulVec_mulVec, mul_nonsing_inv _ (hn b hb).1, one_mulVec]⟩
  · intro z
    have inj : Function.Injective (colR (p b)).mulVec :=
      mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (hn b hb).1)
    have k : ε (b, colR (p b) *ᵥ z) = y b ≫ unitSec P.A ↔ e b (colR (p b) *ᵥ z) = 1 := by
      rw [← HodgeSmooth.one_left]
      exact ⟨Over.OverMorphism.ext, fun h => congrArg Over.Hom.left h⟩
    refine k.trans (((hC₁ b (hC b hb).2).2.1 _).trans ?_)
    simp only [mem_stdLat, ← inj.eq_iff (a := z), (hn b hb).2.2.2]
    refine ⟨fun ⟨n, h⟩ => ⟨_, ⟨n, rfl⟩, ?_⟩, ?_⟩
    · simpa only [Int.cast_smul_eq_zsmul] using h
    · rintro ⟨_, ⟨n, rfl⟩, h⟩
      exact ⟨n, by simpa only [Int.cast_smul_eq_zsmul] using h⟩
  · intro d'
    obtain ⟨T', hT'⟩ := hcmp b (hCB hb) d'
    exact ⟨(T' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)) ∘ₗ (colR (p b)).mulVecLin, fun z => (hT' _).symm,
      (hnorm b hb d' T' hT').2.2.1⟩

theorem exists_normalised_periods : ∀ (S : Scheme.{0}) (P : PPAS S) (B : Set (V 1)) (y : V 1 → (Sp ℂ ⟶ S)) (v₀ : V 1),
    IsOpen B → v₀ ∈ B → IsHolTo B y → (∀ v ∈ B, Nonempty (P.RiemannData (y v))) →
    ∃ r : ℝ, 0 < r ∧ Metric.ball v₀ r ⊆ B ∧ ∃ (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
      (ex : Pt (V 1) P.g → (Sp ℂ ⟶ P.A.left)),
      IsPeriodMap (Metric.ball v₀ r) τ ∧ IsHolTo (cov (Metric.ball v₀ r) P.g) ex ∧
      ∀ v ∈ Metric.ball v₀ r,
        (∀ z, ex (v, z) ≫ P.A.hom = y v) ∧
        (∀ z w, ∀ x x' : Over.mk (y v) ⟶ P.A, x.left = ex (v, z) → x'.left = ex (v, w) →
          (x * x').left = ex (v, z + w)) ∧
        (∀ x : Over.mk (y v) ⟶ P.A, ∃ z, x.left = ex (v, z)) ∧
        (∀ z, ex (v, z) = y v ≫ unitSec P.A ↔ ∃ l ∈ stdLat P.g, z = per (τ v) l) ∧
        ∀ d : P.RiemannData (y v), ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ),
          (∀ z, (d.u.ex (F z)).left ≫ d.φ = ex (v, z)) ∧
          ∀ z w, HermFrame.form d.H (F z) (F w) = GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.herm (τ v) z w := by
  intro S P B y v₀ hB hv₀ hy _
  let φ : V 1 ≃L[ℂ] (Fin 1 → ℂ) := EuclideanSpace.equiv (Fin 1) ℂ
  obtain ⟨C, hC, hC₀, τ, ex, hτ, hex, H⟩ := exists_family P (y := fun b => y (φ.symm b)) (b₀ := φ v₀)
    (hB.preimage φ.symm.continuous) hv₀ (RiemannConst.isHolTo_comp_clm hy (φ.symm : (Fin 1 → ℂ) →L[ℂ] V 1))
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 (hB.inter (hC.preimage φ.continuous)) v₀ ⟨hv₀, hC₀⟩
  refine ⟨r, hr, fun v hv => (hrB hv).1, fun v => τ (φ v), fun q => ex (φ q.1, q.2),
    ⟨Metric.isOpen_ball, fun i j => (hτ.2.1 i j).comp φ.differentiable.differentiableOn fun v hv => (hrB hv).2,
      fun v hv => hτ.2.2 _ (hrB hv).2⟩, ?_, fun v hv => H (φ v) (hrB hv).2⟩
  refine RelExp.isHolTo_of_holAt (Metric.isOpen_ball.prod isOpen_univ) fun q hq => ?_
  exact RelExp.HolAt.comp (a := ex) (φ := fun q : Pt (V 1) P.g => (φ q.1, q.2)) (v₀ := q)
    ⟨_, hC.prod isOpen_univ, ⟨(hrB hq.1).2, trivial⟩, hex⟩
    ((((φ : V 1 →L[ℂ] (Fin 1 → ℂ)).analyticAt _).comp analyticAt_fst).prod analyticAt_snd)

end GlobalTheory.NormPeriods
