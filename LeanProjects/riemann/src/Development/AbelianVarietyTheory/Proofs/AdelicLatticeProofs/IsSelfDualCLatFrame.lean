import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemHermitianStandardLatticeIffPairingIntegral
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceModel

open GlobalTheory.DualPairCheck (cA_incA gram_star trace_cA star_purely_imaginary_eq_neg)
open GlobalTheory.WeilUnramifiedCompare (mem_hermitianStandardLattice_iff_pairing_integral hT_coord intAf_mul)

variable {D : D7} (S T : HSp D)

theorem hO_smul_left (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hO_smul_right (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_inv_star (a b : Fin S.rank) : star (S.gram⁻¹ a b) = S.gram⁻¹ b a := by
  have h : S.gram.IsHermitian := Matrix.ext fun i j => gram_star S j i
  exact congrFun (congrFun h.inv b) a

theorem hO_herm (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  unfold hO
  simp only [map_sum, map_mul, cA_cA, cA_incA, gram_star, gram_inv_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem symplO_skew (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [← trace_cA, map_mul, cA_incA, star_purely_imaginary_eq_neg, hO_herm, map_neg, neg_mul, map_neg]

theorem symplO_add_left (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem symplO_add_right (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

theorem symplO_smul (a : AE D) (x y : WO S T) : symplO S T (a • x) y = symplO S T x (cA D a • y) := by
  unfold symplO
  rw [hO_smul_left, hO_smul_right, cA_cA]

theorem symplO_zero_right (x : WO S T) : symplO S T x 0 = 0 := by
  simpa using symplO_add_right S T x 0 0

theorem symplO_zero_left (x : WO S T) : symplO S T 0 x = 0 := by
  simpa using symplO_add_left S T 0 0 x

theorem isBichar_symplO (ψ : AddChar (AF D.host.F) ℂ) : IsBichar fun x y : WO S T => ψ (symplO S T x y) where
  left a b y := by rw [symplO_add_left, AddChar.map_add_eq_mul]
  right a b y := by rw [symplO_add_right, AddChar.map_add_eq_mul]
  zero_left y := by rw [symplO_zero_left, AddChar.map_zero_eq_one]
  zero_right y := by rw [symplO_zero_right, AddChar.map_zero_eq_one]

def heisL (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by funext t; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by funext t; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; exact mul_left_comm _ _ _

theorem heisL_heisL (ψ : AddChar (AF D.host.F) ℂ) (w w' : WO S T) (f : WO S T → ℂ) :
    heisL S T ψ w (heisL S T ψ w' f) = ψ (symplOH S T w w') • heisL S T ψ (w + w') f := by
  funext t
  change ψ (symplOH S T t w) * (ψ (symplOH S T (t + w) w') * f (t + w + w')) =
    ψ (symplOH S T w w') * (ψ (symplOH S T t (w + w')) * f (t + (w + w')))
  simp only [symplOH, symplO_add_left, symplO_add_right, mul_add, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heisL_comm (ψ : AddChar (AF D.host.F) ℂ) (w w' : WO S T) (f : WO S T → ℂ) :
    heisL S T ψ w (heisL S T ψ w' f) = ψ (symplO S T w w') • heisL S T ψ w' (heisL S T ψ w f) := by
  rw [heisL_heisL, heisL_heisL, smul_smul, ← AddChar.map_add_eq_mul, add_comm w' w]
  congr 2
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [symplOH, symplOH, symplO_skew S T w w']
  linear_combination (symplO S T w w') * h2

def half (e : AE D) : AddSubgroup (WO S T) where
  carrier := {u | e • u = u}
  zero_mem' := smul_zero e
  add_mem' {a b} ha hb := by
    change e • (a + b) = a + b
    rw [smul_add, show e • a = a from ha, show e • b = b from hb]
  neg_mem' {a} ha := by
    change e • (-a) = -a
    rw [smul_neg, show e • a = a from ha]

theorem mem_half {e : AE D} {u : WO S T} : u ∈ half S T e ↔ e • u = u := Iff.rfl

theorem isHalf_iff {e : AE D} {u : WO S T} : IsHalf e u ↔ u ∈ half S T e :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem heisL_half (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (he : cA D e * e = 0) (x : WO S T) (hx : x ∈ half S T e)
    (x' : WO S T) (hx' : x' ∈ half S T e) (f : WO S T → ℂ) :
    heisL S T ψ x (heisL S T ψ x' f) = heisL S T ψ (x + x') f := by
  have : symplO S T x x' = 0 := by
    rw [← (mem_half S T).1 hx, ← (mem_half S T).1 hx', symplO_smul, smul_smul, he, zero_smul, symplO_zero_right]
  rw [heisL_heisL, symplOH, this, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem inv_smul_nsmul {k : ℕ} (hk : 0 < k) (t : WO S T) : incA D (k : D.host.E)⁻¹ • (k • t) = t := by
  have : (k : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, ← map_natCast (incA D), ← map_mul, inv_mul_cancel₀ this, map_one,
    one_smul]

theorem half_div (e : AE D) (k : ℕ) (hk : 0 < k) (x : WO S T) (hx : x ∈ half S T e) :
    ∃ x' ∈ half S T e, k • x' = x :=
  ⟨incA D (k : D.host.E)⁻¹ • x, by rw [mem_half, smul_comm, (mem_half S T).1 hx], by
    rw [smul_comm, inv_smul_nsmul S T hk]⟩

def latFrame : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
  S.L0.map (S.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_latFrame (y : Fin S.rank → D.host.E) : y ∈ latFrame S ↔ ∑ i, y i • S.frame i ∈ S.L0 := by
  rw [← S.frame.equivFun_symm_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change S.frame.equivFun.symm (S.frame.equivFun x) ∈ S.L0
    rwa [LinearEquiv.symm_apply_apply]
  · exact fun h => ⟨_, h, S.frame.equivFun.apply_symm_apply y⟩

theorem coe_latFrame : (latFrame S : Set (Fin S.rank → D.host.E)) = L0c D S :=
  Set.ext fun y => mem_latFrame S y

theorem isSelfDualC_latFrame : IsSelfDualC S (latFrame S) := by
  refine ⟨⟨S.standardTuple_isLattice.fg.map _, ?_⟩, fun y => ?_⟩
  · change Submodule.span _ (S.frame.equivFun.toLinearMap '' (S.L0 : Set S.V)) = ⊤
    rw [← Submodule.map_span, S.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  · rw [mem_latFrame, mem_hermitianStandardLattice_iff_pairing_integral]
    constructor
    · intro h x hx
      rw [← hT_coord]
      exact h _ ((mem_latFrame S x).1 hx)
    · intro h x hx
      have := h (S.frame.equivFun x) ⟨x, hx, rfl⟩
      rwa [← hT_coord, S.frame.sum_equivFun] at this

variable {S T} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem latO_le_top (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, _, h⟩ => ⟨α, hα, fun _ hv => absurd trivial hv, h⟩

theorem placeIdem_smul_mem (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    algebraMap (AF D.host.F) (AE D) ε • u ∈ latO S T LS LT fun w => w = v := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  have hβ : β ∈ intAf D.host.F := fun w => by
    by_cases hw : w = v
    · subst hw; rw [h1]; exact one_mem _
    · rw [h0 w hw]; exact zero_mem _
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β * α, intAf_mul hβ hα, fun w hw => ?_, a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul, h0 w hw, zero_mul]
    · ext i j
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem idem_smul_mem (hε : IsPlaceIdem D v ε) {e : AE D} (he : e * e = e)
    (heε : algebraMap (AF D.host.F) (AE D) ε * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ (latO S T LS LT fun w => w = v) ⊓ half S T e := by
  refine AddSubgroup.mem_inf.2 ⟨?_, by rw [mem_half, smul_smul, he]⟩
  rw [← heε, mul_smul]
  exact placeIdem_smul_mem hε
    (GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])) u hu)

theorem infPart_half (hε : IsPlaceIdem D v ε) {e : AE D} (heε : algebraMap (AF D.host.F) (AE D) ε * e = e)
    {u : WO S T} (hu : u ∈ half S T e) : u.map (infPart D) = 0 := by
  obtain ⟨β, rfl, -⟩ := hε
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  ext i j
  rw [Matrix.map_apply, ← (isHalf_iff S T).2 hu i j, ← heε, map_mul, map_mul, h0, zero_mul, zero_mul]
  rfl

theorem halfInd_eq_ind (e : AE D) (Λ : AddSubgroup (WO S T)) : halfInd e Λ = ind (Λ ⊓ half S T e) := by
  funext t
  unfold halfInd ind
  by_cases h : t ∈ Λ ⊓ half S T e
  · rw [if_pos h, if_pos ⟨h.1, (isHalf_iff S T).2 h.2⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1, (isHalf_iff S T).1 h'.2⟩]

theorem exists_placeModel (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (hec : e * cA D e = 0) (Λ : AddSubgroup (WO S T))
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hX : ∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e)
    (hY : ∀ y ∈ half S T (cA D e), (∀ u ∈ Λ ⊓ half S T e, ψ (symplO S T u y) = 1) → y ∈ Λ ⊓ half S T (cA D e))
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u)
    {c : ℂ} (hc : c ≠ 0) (f₀ : WO S T → ℂ) (hf : ∀ u ∈ Λ ⊓ half S T e, heisO ψ S T u f₀ = f₀)
    (hf' : ∀ u ∈ Λ ⊓ half S T (cA D e), heisO ψ S T u f₀ = f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm := by
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have c1 : cA D e * e = 0 := by rw [mul_comm, hec]
  have c2 : cA D (cA D e) * cA D e = 0 := by rw [cA_cA, hec]
  obtain ⟨Tm, h0, h1⟩ := exists_intertwiner (X := half S T e) (Y := half S T (cA D e)) (L := Λ ⊓ half S T e)
    (L' := Λ ⊓ half S T (cA D e)) (isBichar_symplO S T ψ) inf_le_right inf_le_right hLL' hX hY
    (half_div S T e) (half_div S T _) tf hfin (heisL S T ψ) (heisL_half S T ψ c1) (heisL_half S T ψ c2)
    (fun x _ y _ => heisL_comm S T ψ x y) f₀ hf hf'
  have h2 := fun Φ (hΦ : IsSBHalf e Λ Φ) =>
    h1 Φ (fun t ht => (isHalf_iff S T).1 (hΦ.1 t ht)) _ hΦ.2.choose_spec.1
      (fun u hu => hΦ.2.choose_spec.2.1 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨hΦ.2.choose_spec.2.2 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (hΦ.1 t ht)) _⟩
  refine ⟨c⁻¹ • Tm, fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, (h2 Φ hΦ).1 x ((isHalf_iff S T).1 hx)]
    exact ((heisL S T ψ x).map_smul _ _).symm
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, (h2 Φ hΦ).2 y ((isHalf_iff S T).1 hy)]
    exact ((heisL S T ψ y).map_smul _ _).symm
  · rw [LinearMap.smul_apply, LinearMap.map_smul, halfInd_eq_ind, h0, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem mem_of_dual {ψ : AddChar (AF D.host.F) ℂ} (hε : IsPlaceIdem D v ε)
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ (latO S T LS LT fun _ => True) ↔
      ∀ u' ∈ (latO S T LS LT fun _ => True), ψ (symplO S T u u') = 1))
    {a : AE D} (ha : a * a = a) (h1 : algebraMap (AF D.host.F) (AE D) ε * a = a)
    (h2 : algebraMap (AF D.host.F) (AE D) ε * cA D a = cA D a) (x : WO S T) (hx : x ∈ half S T a)
    (h : ∀ y ∈ (latO S T LS LT fun w => w = v) ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) :
    x ∈ (latO S T LS LT fun w => w = v) ⊓ half S T a := by
  have := idem_smul_mem hε ha h1 ((hdual x (infPart_half hε h1 hx)).2 fun u hu => by
    have := h _ (idem_smul_mem hε (by rw [← map_mul, ha]) h2 hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this)
  rwa [(mem_half S T).1 hx] at this

theorem placeModelExistsO : ∀ D : D7, PlaceModelExistsO D := by
  intro D ψ hψ S T e v ε hs hε heq c f₀ hc _ hvac
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * e = e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have hs' : IsSplitIdem D (cA D e) :=
    ⟨he', by rw [cA_cA, mul_comm, hec], v, ε, hε, by rw [cA_cA, add_comm, heq]⟩
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (isSelfDualC_latFrame S) (isSelfDualC_latFrame T)).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ (isSelfDualC_latFrame S).1.fg (isSelfDualC_latFrame T).1.fg fun w => w = v
  rw [coe_latFrame, coe_latFrame] at hdual hfin
  refine exists_placeModel ψ hec _
    (fun u hu y hy => (hdual u (infPart_half hε heε hu.2)).1 (latO_le_top _ hu.1) y (latO_le_top _ hy.1))
    (mem_of_dual hε hdual he heε heε') (fun y hy h => ?_) (fun k hk => ?_) hc f₀
    (fun u hu => hvac.2 e hs u hu.1 ((isHalf_iff S T).2 hu.2))
    (fun u hu => hvac.2 _ hs' u hu.1 ((isHalf_iff S T).2 hu.2))
  · refine mem_of_dual hε hdual he' heε' (by rwa [cA_cA]) y hy fun u hu => ?_
    rw [cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, idem_smul_mem hε he heε (latO_le_top _ hu), ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

end GlobalTheory.PlaceModel

end
