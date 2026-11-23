import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyCoefficientFieldPrime
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyBoundaryLocalIff

noncomputable section

namespace Formalism.L2.Geo

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts NumberField Formalism.MainNotions.DIV.Inh Formalism.MainNotions.DIV.Inh.LocalProvisionModel

def cfJunk (p : ℕ) : CF p := (nonempty_coefficient_field p).some

section Tools

def ballC (C : Type) [NormedField C] [IsUltrametricDist C] : AddSubgroup C where
  carrier := {x | ‖x‖ ≤ 1}
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_ballC {C : Type} [NormedField C] [IsUltrametricDist C] (x : C) : x ∈ ballC C ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem intCast_mem_ballC {C : Type} [NormedField C] [IsUltrametricDist C] (t : ℤ) : (t : C) ∈ ballC C := by
  have h1 : (1 : C) ∈ ballC C := by
    rw [mem_ballC]
    simp
  simpa using (ballC C).zsmul_mem h1 t

theorem smul_mem_ballC {C : Type} [NormedField C] [IsUltrametricDist C] (a v : C) (ha : ‖a‖ ≤ 1) (hv : v ∈ ballC C) :
    a • v ∈ ballC C := by
  rw [mem_ballC, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hv

theorem span_intCast (C : Type) [Field C] : Submodule.span C (Set.range (Int.castAddHom C)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : (1 : C) ∈ Submodule.span C (Set.range (Int.castAddHom C)) := Submodule.subset_span ⟨1, by simp⟩
  simpa using Submodule.smul_mem _ x h1

theorem ballC_eq_inf {C : Type} [NormedField C] [IsUltrametricDist C] (a : C) :
    ballC C = ballC C ⊓ (Ospan (C := C) (Set.range (Int.castAddHom C)) ⊔
      (ballC C).map (DistribSMul.toAddMonoidHom C a)) := by
  refine le_antisymm (le_inf le_rfl (le_sup_of_le_left fun x hx => ?_)) inf_le_left
  exact AddSubgroup.subset_closure ⟨x, hx, 1, ⟨1, by simp⟩, by simp⟩

def actT (C A : Type) [Field C] [Group A] : Cˣ × A →* Module.End C C :=
  (algebraMap C (Module.End C C)).toMonoidHom.comp ((Units.coeHom C).comp (MonoidHom.fst Cˣ A))

theorem actT_apply (C A : Type) [Field C] [Group A] (g : Cˣ × A) (s : C) : actT C A g s = (g.1 : C) • s := rfl

def rkB (ρ : ℕ) : Bool → ℕ
  | false => 0
  | true => min ρ 1

theorem rkB_le_one (ρ : ℕ) (y : Bool) : rkB ρ y ≤ 1 := by
  cases y <;> simp [rkB]

theorem rkB_le (ρ : ℕ) (y : Bool) : rkB ρ y ≤ ρ := by
  cases y <;> simp [rkB]

theorem rkB_true_pos {ρ : ℕ} (h : 0 < ρ) : 0 < rkB ρ true := by
  show 0 < min ρ 1
  omega

theorem le_choose_two (r : ℕ) : r - 1 ≤ r * (r - 1) / 2 := by
  rcases r with _ | _ | k
  · simp
  · simp
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    simp only [Nat.add_sub_cancel]
    nlinarith

theorem flDim_eq (f r : ℕ) : f * (r * (r - 1) / 2) - f * (r - 1) + f * (r - 1) = f * (r * (r - 1) / 2) :=
  Nat.sub_add_cancel (Nat.mul_le_mul_left _ (le_choose_two r))

open Matrix in

theorem pd_of_int {Y : Type} [AddCommGroup Y] (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)
    (hsymm : ∀ a b, β a b = β b a) (hint : ∀ a b, ∃ z : ℤ, β a b = z) (hpos : ∀ a, a ≠ 0 → 0 < β a a)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ Y) (x : Fin n → ℝ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ k, x i * x k * β (b i) (b k) := by
  classical
  choose g hg using fun i k => hint (b i) (b k)
  let G : Matrix (Fin n) (Fin n) ℤ := Matrix.of g
  let GR : Matrix (Fin n) (Fin n) ℝ := G.map (Int.castRingHom ℝ)
  have hGR : ∀ i k, GR i k = β (b i) (b k) := fun i k => by simp [GR, G, hg]
  have hq : ∀ x : Fin n → ℝ, ∑ i, ∑ k, x i * x k * β (b i) (b k) = x ⬝ᵥ (GR *ᵥ x) := by
    intro x
    simp only [dotProduct, Matrix.mulVec, hGR, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hz : ∀ z : Fin n → ℤ, (fun i => (z i : ℝ)) ⬝ᵥ (GR *ᵥ fun i => (z i : ℝ)) =
      β (∑ i, z i • b i) (∑ i, z i • b i) := by
    intro z
    rw [← hq]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by
      rw [hsymm (b k) (b i)]
      ring
  have hhom : ∀ (t : ℝ) (x : Fin n → ℝ), (t • x) ⬝ᵥ (GR *ᵥ (t • x)) = t ^ 2 * (x ⬝ᵥ (GR *ᵥ x)) := by
    intro t x
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hnnZ : ∀ z : Fin n → ℤ, 0 ≤ (fun i => (z i : ℝ)) ⬝ᵥ (GR *ᵥ fun i => (z i : ℝ)) := by
    intro z
    rw [hz]
    by_cases h : (∑ i, z i • b i) = 0
    · rw [h]
      simp
    · exact (hpos _ h).le
  have hnnQ : ∀ w : Fin n → ℚ, 0 ≤ (fun i => (w i : ℝ)) ⬝ᵥ (GR *ᵥ fun i => (w i : ℝ)) := by
    intro w
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ w
    choose z hz' using fun i => hd i (Finset.mem_univ i)
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    have h1 : (fun i => (z i : ℝ)) = ((d : ℤ) : ℝ) • fun i => (w i : ℝ) := by
      funext i
      have h2 := congrArg (fun q : ℚ => (q : ℝ)) (hz' i)
      simpa using h2
    have h2 := hnnZ z
    rw [h1, hhom] at h2
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h2
  have hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (GR *ᵥ x) := by
    intro x
    have hdense : DenseRange (Pi.map fun (_ : Fin n) (q : ℚ) => (q : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hdense.induction_on x ?_ hnnQ
    refine isClosed_le continuous_const ?_
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 := hz z
    have h2 : GR *ᵥ (fun i => (z i : ℝ)) = 0 := by
      funext i
      show (G.map (Int.castRingHom ℝ) *ᵥ ((Int.castRingHom ℝ) ∘ z)) i = 0
      rw [← RingHom.map_mulVec, hGz]
      simp
    rw [h2, dotProduct_zero] at h1
    have h3 : ∑ i, z i • b i ≠ 0 := fun h =>
      hz0 (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent z h i)
    exact (hpos _ h3).ne h1
  have hherm : GR.IsHermitian := by
    ext i k
    simp [Matrix.conjTranspose_apply, hGR, hsymm (b k) (b i)]
  have hPS : GR.PosSemidef := .of_dotProduct_mulVec_nonneg hherm fun x => by simpa using hpsd x
  have hU : IsUnit GR := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    have h1 : GR.det = ((G.det : ℤ) : ℝ) := ((Int.castRingHom ℝ).map_det G).symm
    rw [h1]
    exact_mod_cast hdet
  have hPD := hPS.posDef_iff_isUnit.2 hU
  rw [hq]
  simpa using hPD.dotProduct_mulVec_pos hx

variable (D : D7)

theorem subsingleton_pow (k : ℕ) : Subsingleton (Fin k → 𝓞 D.host.E) ↔ k = 0 := by
  constructor
  · intro hs
    by_contra hk
    have := hs.elim (fun _ => (0 : 𝓞 D.host.E)) (fun _ => 1)
    exact zero_ne_one (congrFun this ⟨0, Nat.pos_of_ne_zero hk⟩)
  · rintro rfl
    infer_instance

theorem finrank_OE : Module.finrank ℤ (𝓞 D.host.E) = 2 * D.R.f := by
  rw [RingOfIntegers.rank, D.host.finrank_cmField]
  simp only [Ranks.f, Ranks.n]
  ring

theorem finrank_pow (k : ℕ) : Module.finrank ℤ (Fin k → 𝓞 D.host.E) = k * (2 * D.R.f) := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, finrank_OE]
  simp

def trZ (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : ℤ := ∑ i, Algebra.trace ℤ (𝓞 D.host.E) (a i * cjO D (b i))

theorem trZ_cast (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : ((trZ D k a b : ℤ) : ℝ) = beK D k a b := by
  rw [beK_apply, trZ, Int.cast_sum]
  rfl

theorem beK_symm (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : beK D k a b = beK D k b a := by
  rw [beK_apply, beK_apply]
  exact Finset.sum_congr rfl fun i _ => beO_symm D _ _

theorem beK_bal (k : ℕ) (c c' : 𝓞 D.host.E) (h : (c' : D.host.E) = D.host.conj (c : D.host.E))
    (a b : Fin k → 𝓞 D.host.E) : beK D k (c • a) b = beK D k a (c' • b) := by
  rw [beK_apply, beK_apply]
  exact Finset.sum_congr rfl fun i _ => beO_bal D c c' h _ _

theorem trZ_add_left (k : ℕ) (a a' b : Fin k → 𝓞 D.host.E) : trZ D k (a + a') b = trZ D k a b + trZ D k a' b := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add, trZ_cast, trZ_cast, trZ_cast, map_add, LinearMap.add_apply]

theorem trZ_add_right (k : ℕ) (a b b' : Fin k → 𝓞 D.host.E) : trZ D k a (b + b') = trZ D k a b + trZ D k a b' := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add, trZ_cast, trZ_cast, trZ_cast, map_add]

theorem trZ_symm (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : trZ D k a b = trZ D k b a := by
  apply Int.cast_injective (α := ℝ)
  rw [trZ_cast, trZ_cast, beK_symm]

theorem trZ_bal (k : ℕ) (c : 𝓞 D.host.E) (a b : Fin k → 𝓞 D.host.E) :
    trZ D k (c • a) b = trZ D k a (integersConjugation D c • b) := by
  apply Int.cast_injective (α := ℝ)
  rw [trZ_cast, trZ_cast, beK_bal D k c (integersConjugation D c) (integers_conjugation_coe D c)]

theorem trZ_self_nonneg (k : ℕ) (a : Fin k → 𝓞 D.host.E) : 0 ≤ trZ D k a a := by
  have h : (0 : ℝ) ≤ ((trZ D k a a : ℤ) : ℝ) := by
    rw [trZ_cast, beK_apply]
    exact Finset.sum_nonneg fun i _ => beO_nonneg D _
  exact_mod_cast h

theorem trZ_zero_rank (a b : Fin 0 → 𝓞 D.host.E) : trZ D 0 a b = 0 := by
  simp [trZ]

open Classical in

def pU (p : ℕ) (c : CF p) : (c.C)ˣ := if h : (p : c.C) = 0 then 1 else Units.mk0 (p : c.C) h

theorem vU_pU_zpow (p : ℕ) (c : CF p) (z : ℤ) (h : 2 ≤ p ∨ z = 0) : BoundaryLocalData.vU p (pU p c ^ z) = z := by
  rcases h with h | rfl
  · have hp0 : (p : c.C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h1 : ((pU p c ^ z : (c.C)ˣ) : c.C) = (p : c.C) ^ z := by simp [pU, hp0]
    have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast h)).ne'
    unfold BoundaryLocalData.vU Real.logb
    rw [h1, norm_zpow, c.norm_p, Real.log_zpow, Real.log_inv]
    field_simp
  · simp [BoundaryLocalData.vU]

def u2 : (FractionRing ℤ_[2])ˣ :=
  Units.mk0 (algebraMap ℤ_[2] (FractionRing ℤ_[2]) 2)
    ((map_ne_zero_iff _ (IsFractionRing.injective ℤ_[2] (FractionRing ℤ_[2]))).2 two_ne_zero)

theorem two_adic_unit_zpow_mem (z : ℤ) (hz : 0 ≤ z) :
    ((u2 ^ z : (FractionRing ℤ_[2])ˣ) : FractionRing ℤ_[2]) ∈ (algebraMap ℤ_[2] (FractionRing ℤ_[2])).range := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  exact ⟨2 ^ n, by simp [u2]⟩

end Tools

section Model

variable (D : D7) (r j p : ℕ) (c : CF p) (ρ : ℕ)

@[reducible] def locT : Loc D r j p where
  Mdl := Unit
  Xm := ()
  YY := ()
  Xn := fun _ => ()
  Pt := fun _ => Bool
  fld := fun _ => c
  Ylat := fun y => Fin (rkB ρ y) → 𝓞 D.host.E
  ylAdd := fun _ => inferInstance
  ylMod := fun _ => inferInstance
  ylFree := fun _ => inferInstance
  ylFin := fun _ => inferInstance
  be := fun y => beK D (rkB ρ y)
  be_symm := fun y a b => beK_symm D _ a b
  be_bal := fun y e e' h a b => beK_bal D _ e e' h a b
  be_posDef := fun y => ⟨Fin _, inferInstance, Module.finBasis ℤ _, fun x hx => pd_of_int (beK D (rkB ρ y))
    (fun a b => beK_symm D _ a b) (fun a a' => beK_int D (rkB ρ y) a a') (fun a h => beK_pos D _ a h) _ x hx⟩
  yl_rank := fun y => ⟨rkB ρ y, by rw [finrank_pow]; ring, fun h1 h2 => by
    have := rkB_le_one ρ y; omega⟩
  Gen := fun _ => Bool
  abAt := fun η => rkB ρ η = 0
  Sh := fun _ => Unit
  IsInv := fun _ => True
  IsLocFree := fun _ => True
  Sec := fun _ => c.C
  secAdd := fun _ => inferInstance
  H0 := fun _ => ballC c.C
  nrm := fun _ f _ => ‖f‖
  nrm_nonneg := fun _ f _ => norm_nonneg f
  norm_le_one_of_mem_sections := fun _ _ h _ => h
  GIso := fun _ _ => Unit
  vrat := fun _ _ => 0
  Lb := fun _ => ()
  Lb_inv := fun _ => trivial
  nrmRef := fun _ f _ => ‖f‖
  DVP := Bool
  dvRho := fun y => rkB ρ y
  Ext := fun _ => Unit
  Chart := fun _ _ _ => Unit
  chAt := fun _ => True
  chOpen := fun _ => True
  chAbExact := fun {_ y _} _ => 0 < rkB ρ y
  chModU := fun _ => True
  chConst := fun _ => True
  PL := Unit
  phiAt := fun _ _ _ => 0
  phiAt_zero := fun _ _ _ _ => rfl
  divGe := fun _ _ _ _ => True
  FJd := Unit
  Chr := fun _ => Unit
  fjN := fun _ f _ _ => ‖f‖
  Unim := ℕ
  LBG := fun _ => Unit
  LBGq := fun _ => Unit
  resQ := fun _ => ()
  PPq := fun _ => ()
  symmG := fun _ => True
  rigG := fun _ => True
  LBGt := fun _ _ => Unit
  LBB := fun _ _ => Unit
  resGt := fun _ _ => ()
  prPull := fun _ => ()
  principal := fun _ => True
  psiV := fun y a => beK D (rkB ρ y) a (BoundaryLocalData.w0 D • a)
  piPP := ()
  keySh := fun _ => ()
  latStd := fun n => n
  At := fun _ La n => AtM (2 * (D.R.f * r * La)) n
  atAdd := fun _ _ _ => inferInstance
  atFin := fun _ _ _ => inferInstance
  at_tors := fun _ _ _ x => atM_tors _ _ x
  at_card := fun _ _ _ h => atM_card _ _ h
  Th := fun _ La n => (c.C)ˣ × Multiplicative (AtM (2 * (D.R.f * r * La)) n)
  thGrp := fun _ _ _ => inferInstance
  ovr := fun _ _ _ => MonoidHom.snd _ _
  ovr_surj := fun _ _ _ x => ⟨(1, x), rfl⟩
  scal := fun _ _ _ => MonoidHom.inl _ _
  scal_inj := fun _ _ _ a b h => congrArg Prod.fst h
  scal_central := fun _ _ _ a g => by
    ext <;> simp [mul_comm]
  ker_ovr := fun _ _ _ g => ⟨fun h => ⟨g.1, Prod.ext rfl h.symm⟩, fun ⟨a, h⟩ => by rw [← h]; rfl⟩
  dl := fun _ _ _ => MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.inv _)
  dl_ovr := fun _ _ _ _ => rfl
  dl_scal := fun _ La n a => Prod.ext rfl (inv_one : (1 : Multiplicative (AtM (2 * (D.R.f * r * La)) n))⁻¹ = 1)
  dl_dl := fun _ _ _ g => by
    show (g.1, (g.2⁻¹)⁻¹) = g
    rw [inv_inv]
  Sn := fun _ _ _ => c.C
  snAdd := fun _ _ _ => inferInstance
  snMod := fun _ _ _ => inferInstance
  act := fun _ La n => actT c.C (Multiplicative (AtM (2 * (D.R.f * r * La)) n))
  act_scal := fun _ _ _ _ _ => rfl
  vth := fun _ _ _ => 1
  Jet := fun _ _ _ _ => c.C
  jAdd := fun _ _ _ _ => inferInstance
  jMod := fun _ _ _ _ => inferInstance
  intJet := fun _ _ _ _ => ballC c.C
  jet := fun _ _ _ _ => LinearMap.id
  LieGt := fun _ _ => PUnit
  LieB := fun _ _ => PUnit
  LieT := fun _ _ => PUnit
  lgAdd := fun _ _ => inferInstance
  lbAdd := fun _ _ => inferInstance
  ltAdd := fun _ _ => inferInstance
  resB := fun _ _ => 0
  incT := fun _ _ => 0
  kapGt := fun _ _ _ _ => 0
  kapB := fun _ _ _ _ => 0
  Harm := fun _ => Unit
  SecP := fun _ => Unit
  evA := fun _ _ _ => 0
  evGt := fun _ _ _ => 0
  Tp := fun _ => ℤ
  tpAdd := fun _ => inferInstance
  OmV := fun _ => c.C
  omAdd := fun _ => inferInstance
  omMod := fun _ => inferInstance
  om := fun _ => ballC c.C
  ht := fun _ => Int.castAddHom c.C
  IsHTBlowup := fun _ _ => True
  eOmP := fun _ _ _ => ()
  SES := fun _ => Unit
  ExactMod := fun _ _ => True
  htSES := fun _ _ => ()
  nefHT := fun _ _ => True
  nefQ := fun _ => True
  descK := fun _ _ => True
  bdryLoci := fun _ => True
  BT := fun _ => Unit
  extA := fun _ => True
  compat := fun _ _ => True
  Crv := PsiT D → ℕ → ℤ
  eDeg := fun d => -∑ᶠ τ, ((∑ i ∈ Finset.Icc 1 j, d τ i) + -∑ i ∈ Finset.Icc (j + 1) r, d τ i)
  Pm := fun d => pmM D d (r + j)
  Pm_nonneg := fun d => pmM_nonneg D _ _
  degLie := fun d τ b => if b then -∑ i ∈ Finset.Icc (j + 1) r, d τ i else ∑ i ∈ Finset.Icc 1 j, d τ i
  degLdR := fun d μ => -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 r, μ τ i * (d τ i : ℝ)

@[reducible] def extT : ExtA D (locT D r j p c ρ) where
  FlagData := fun _ => Unit
  flagCl := fun _ _ => ()
  allFlags := ()
  YY_eq := rfl
  Idl := fun _ => Unit
  blowUp := fun _ _ => ()
  powP := fun _ => True
  pbPrinc := fun _ _ => True
  Corr := fun _ _ => Unit
  diagCl := fun _ _ _ => ()
  IvD := fun _ => Unit
  jIdl := fun _ _ => ()
  ZP := fun _ => Bool × Bool
  spz := fun x x' => (x'.1 = true → x.1 = true) ∧ (x'.2 = true → x.2 = true)
  abP := fun x => x.2 = true
  inQ := fun x => x.1 = true
  isGenP := fun x => x = (true, true)
  isGenP_ab := fun x h => by rw [h]
  gpt := fun η => (false, decide (rkB ρ η = 0))
  abAt_iff := fun η => by
    show rkB ρ η = 0 ↔ decide (rkB ρ η = 0) = true
    rw [decide_eq_true_eq]
  gpt_notQ := fun _ h => Bool.false_ne_true h
  genFin := fun _ => inferInstanceAs (Finite Bool)
  genNe := fun _ => ⟨false⟩
  redK := fun _ y => (false, decide (rkB ρ y = 0))
  dvRho_pos_iff := fun _ y => by
    show 0 < rkB ρ y ↔ ¬ decide (rkB ρ y = 0) = true
    rw [decide_eq_true_eq]
    omega
  genK := fun η => η
  redK_genK := fun _ => rfl
  imgM := fun {_ y _} _ => (false, decide (rkB ρ y = 0))
  imgU := fun {_ y _} _ => (true, decide (rkB ρ y = 0))
  img_spz := fun _ => ⟨fun h => absurd h Bool.false_ne_true, fun h => h⟩
  imgU_inQ := fun _ => rfl
  chAt_imgM := fun _ _ => rfl
  chAbExact_imgU := fun {_ y _} _ h => by
    show ¬ decide (rkB ρ y = 0) = true
    rw [decide_eq_true_eq]
    exact Nat.pos_iff_ne_zero.1 h
  RFam := fun _ _ => Unit
  chFam := fun _ => ()
  ptK := fun _ y => y
  ptK_good := fun _ y => subsingleton_pow D (rkB ρ y)
  vpi := fun _ => 1
  vpi_pos := fun _ => one_pos
  ordGe := fun _ _ _ _ => True
  yEta := fun η => η
  yEta_good := fun η => subsingleton_pow D (rkB ρ η)
  homSh := fun _ _ => ()
  homSh_inv := fun _ _ _ _ => trivial
  isoSec := fun _ => (1 : c.C)
  nrm_isoSec := fun _ _ => by
    show ‖(1 : c.C)‖ = (p : ℝ) ^ (-(0 : ℝ))
    simp
  isoSymm := fun _ => ()
  vrat_symm := fun _ _ => by
    show (0 : ℝ) = -0
    simp
  LieV := fun _ => c.C
  lvAdd := fun _ => inferInstance
  lvMod := fun _ => inferInstance
  lieL := fun _ => ballC c.C
  eig := fun _ _ => ⊤
  Wst := fun _ _ _ => ⊤
  Wst_le := fun _ _ _ => le_rfl
  taut := fun _ _ _ => ballC c.C
  taut_eq := fun _ _ _ => by simp
  nrmIn := fun _ f _ _ => ‖f‖
  nrmRef_def := fun _ _ _ => rfl
  nrm_Lb_def := fun _ _ _ => rfl
  om_smul := fun _ a ha v hv => smul_mem_ballC a v ha hv
  TC := fun _ => c.C
  tcAdd := fun _ => inferInstance
  tcMod := fun _ => inferInstance
  iT := fun _ => Int.castAddHom c.C
  iT_span := fun _ => span_intCast c.C
  htC := fun _ => LinearMap.id
  htC_iT := fun _ _ => rfl
  psiC := fun _ => 0
  lieGt1 := fun _ => ⊥
  eT := fun _ _ => LinearMap.id
  HTn := fun _ => Unit
  htEval := fun _ _ => Int.castAddHom c.C
  htIdl := fun _ => ()
  IsHTBlowup_def := fun _ _ _ =>
    ⟨fun _ => ⟨(), fun _ t => ⟨intCast_mem_ballC t, 0, zero_mem _, by simp⟩, rfl⟩, fun _ => trivial⟩
  wFib := fun _ _ _ => ballC c.C
  htFlags := fun _ => ()
  omSh := fun _ => ()
  omPat := fun _ => ballC c.C
  omPat_def := fun _ _ _ _ _ => ballC_eq_inf _
  BPt := fun _ => Unit
  bfld := fun _ => c
  OmB := fun _ => c.C
  obAdd := fun _ => inferInstance
  obMod := fun _ => inferInstance
  omB := fun _ => ballC c.C
  omPB := fun _ => ballC c.C
  eOmB := fun _ _ => ballC c.C
  eB := fun _ _ => LinearMap.id
  YsP := fun _ => Bool
  ysBd := fun x => x = true
  FlP := Unit
  hFl := fun _ => ()
  FlCl := Unit
  flMem := fun _ _ => True
  flDim := fun _ => D.R.f * (r * (r - 1) / 2) - D.R.f * (r - 1)
  Sum1 := Unit
  locus := fun _ => ()
  bdryLoci_def := fun _ =>
    ⟨fun _ => ⟨Set.univ, Set.finite_univ, fun _ _ => ⟨(), trivial, trivial⟩, fun _ _ => flDim_eq D.R.f r⟩,
      fun _ => trivial⟩
  CrvS := fun _ => Unit
  degGr := fun _ _ _ => 0
  nefHT_def := fun _ _ => ⟨fun _ _ => by simp, fun _ => trivial⟩
  CrvQ := Unit
  degGrQ := fun _ _ _ => 0
  nefQ_def := fun _ => ⟨fun _ _ => by simp, fun _ => trivial⟩
  degGrD := fun d => d
  degLdR_def := fun _ _ => rfl
  degLie_f := fun _ _ => rfl
  degLie_alt := fun _ _ => rfl
  eDeg_def := fun _ _ => rfl
  Pm_head := fun d τ i _ h2 => le_trans (le_abs_self _)
    (abs_le_pmM D d (r + j) τ _ (Finset.Icc_subset_Icc le_rfl (by omega)))
  Pm_tail := fun d τ i _ _ => le_trans (neg_le_abs _)
    (abs_le_pmM D d (r + j) τ _ (Finset.Icc_subset_Icc (by omega) (by omega)))

open Classical in

@[reducible] def locBT (hp : 2 ≤ p ∨ ρ = 0) (hd : ρ * (2 * D.R.f) ≤ D.R.f * r) :
    BoundaryLocalData.LocB D (locT D r j p c ρ) where
  chX := fun {_} y => XT D (Fin (rkB ρ y) → 𝓞 D.host.E)
  xAdd := fun {_} _ => inferInstance
  xMod := fun {_} _ => inferInstance
  phi := fun {_} y => XT.mk D (Fin (rkB ρ y) → 𝓞 D.host.E)
  phi_conj := fun {_} y e e' h a => by
    have : e' = integersConjugation D e := RingOfIntegers.ext (by rw [h, integers_conjugation_coe])
    rw [this, XT.smul_mk]
  tau := fun {_} y a χ => pU p c ^ trZ D (rkB ρ y) a ((XT.mk D (Fin (rkB ρ y) → 𝓞 D.host.E)).symm χ)
  tau_add_left := fun {_} y a a' χ => by rw [trZ_add_left, zpow_add]
  tau_add_right := fun {_} y a χ χ' => by rw [map_add, trZ_add_right, zpow_add]
  tau_symm := fun {_} y a b => congrArg (fun z : ℤ => pU p c ^ z) (trZ_symm D (rkB ρ y) a b)
  tau_smul := fun {_} y e a χ => by rw [XT.symm_smul, trZ_bal]
  be_tau := fun {_} y a b => by
    show beK D (rkB ρ y) a b = BoundaryLocalData.vU p (pU p c ^ trZ D (rkB ρ y) a b)
    rw [vU_pU_zpow, trZ_cast]
    rcases hp with hp | rfl
    · exact Or.inl hp
    · cases y <;> exact Or.inr (trZ_zero_rank D _ _)
  multiplicationLatticeFirst := fun {_} y _ b => XT.mk D (Fin (rkB ρ y) → 𝓞 D.host.E) b
  multiplicationLatticeSecond := fun {_} y a _ => XT.mk D (Fin (rkB ρ y) → 𝓞 D.host.E) a
  mulC := fun {_} y a b => pU p c ^ trZ D (rkB ρ y) a b
  psiV_def := fun {_} y a => by
    show beK D (rkB ρ y) a (BoundaryLocalData.w0 D • a) = BoundaryLocalData.vU p (pU p c ^ trZ D (rkB ρ y) a (BoundaryLocalData.w0 D • a))
    rw [vU_pU_zpow, trZ_cast]
    rcases hp with hp | rfl
    · exact Or.inl hp
    · cases y <;> exact Or.inr (trZ_zero_rank D _ _)
  StrictHenselianAcyclic := fun _ => Unit
  squareRootLineBundle := fun _ => Unit
  res2 := fun {_} _ => ()
  PoiQ := fun _ => ()
  biext := fun {_} _ => True
  dg := fun {_} _ => ()
  dgq := fun {_} _ => ()
  dg_res := fun {_} _ => rfl
  PPq_def := fun _ => rfl
  BPt := Unit
  Rl := fun _ => ℤ_[2]
  iRr := fun _ => inferInstance
  iRd := fun _ => inferInstance
  iRl := fun _ => inferInstance
  iRn := fun _ => inferInstance
  iRi := fun _ => inferInstance
  iRc := fun _ => inferInstance
  Yb := fun _ => Fin 1 → 𝓞 D.host.E
  iYa := fun _ => inferInstance
  iYm := fun _ => inferInstance
  Xb := fun _ => XT D (Fin 1 → 𝓞 D.host.E)
  iXa := fun _ => inferInstance
  iXm := fun _ => inferInstance
  phib := fun _ => XT.mk D (Fin 1 → 𝓞 D.host.E)
  phib_conj := fun _ e e' h a => by
    have : e' = integersConjugation D e := RingOfIntegers.ext (by rw [h, integers_conjugation_coe])
    rw [this, XT.smul_mk]
  taub := fun _ a χ => u2 ^ trZ D 1 a ((XT.mk D (Fin 1 → 𝓞 D.host.E)).symm χ)
  taub_add_left := fun _ a a' χ => by rw [trZ_add_left, zpow_add]
  taub_add_right := fun _ a χ χ' => by rw [map_add, trZ_add_right, zpow_add]
  taub_symm := fun _ a b => congrArg (fun z : ℤ => u2 ^ z) (trZ_symm D 1 a b)
  taub_smul := fun _ e a χ => by rw [XT.symm_smul, trZ_bal]
  taub_pos := fun _ a => two_adic_unit_zpow_mem _ (trZ_self_nonneg D 1 a)
  Sg := fun _ => FractionRing ℤ_[2]
  iSg := fun _ => inferInstance
  iSk := fun _ => inferInstance
  iSm := fun _ => inferInstance
  iSt := fun _ => inferInstance
  Sreg := fun _ => LinearMap.range (Algebra.linearMap ℤ_[2] (FractionRing ℤ_[2]))
  fc := fun _ => LinearMap.pi fun _ => LinearMap.id
  trU := fun _ _ _ => 1
  oX := ()
  oX_inv := trivial
  secOf := fun {_} _ => (1 : c.C)
  nrm_secOf := fun {_} _ _ => by
    show ‖(1 : c.C)‖ = (p : ℝ) ^ (-(0 : ℝ))
    simp
  keySh_inv := fun _ _ => trivial
  dimB := fun y => D.R.f * r - rkB ρ y * (2 * D.R.f)
  dimB_add := fun y => by
    show D.R.f * r - rkB ρ y * (2 * D.R.f) + Module.finrank ℤ (Fin (rkB ρ y) → 𝓞 D.host.E) = D.R.f * r
    rw [finrank_pow]
    refine Nat.sub_add_cancel ?_
    cases y
    · simp [rkB]
    · exact (Nat.mul_le_mul_right _ (rkB_le ρ true)).trans hd
  FB := fun _ _ _ _ => c.C
  fbAdd := fun _ _ _ _ => inferInstance
  fbMod := fun _ _ _ _ => inferInstance
  nB := fun {_ _ _ _} σ => ‖σ‖
  sgc := fun _ _ _ χ => if χ = 0 then LinearMap.id else 0
  trB := fun _ _ _ _ _ => LinearEquiv.refl c.C c.C
  trB_norm := fun _ _ _ _ _ _ => rfl
  alp := fun n => if h : ModuliIntegralCharts.NHyp D p n then (exists_alp D p n h).choose else 0
  alp_spec := fun n h => by
    rw [dif_pos h]
    exact (exists_alp D p n h).choose_spec
  th1 := fun _ _ => (1 : c.C)
  pbAl := fun _ _ _ => LinearMap.id
  vth_def := fun _ _ _ _ => rfl
  jX := fun _ _ _ _ _ => LinearMap.id
  intJet_free := fun _ _ _ _ =>
    ⟨1, Module.Basis.singleton (Fin 1) c.C, fun v =>
      ⟨fun h i => by simpa using (mem_ballC v).1 h, fun h => (mem_ballC v).2 (by simpa using h 0)⟩⟩
  jX_int := fun _ _ _ _ _ _ h => h
  jet_fourier := fun y nW n DF s t _ => by
    refine ⟨{0}, fun F hF => ⟨0, zero_mem _, ?_⟩⟩
    have h0 : (0 : Fin nW → XT D (Fin (rkB ρ y) → 𝓞 D.host.E)) ∈ F := hF (Finset.mem_singleton_self 0)
    rw [Finset.sum_eq_single_of_mem 0 h0 (fun χ _ hχ => by simp [hχ])]
    simp

end Model

def rhoJ (r p : ℕ) : ℕ := if 2 ≤ r ∧ 2 ≤ p then 1 else 0

theorem rhoJ_p (r p : ℕ) : 2 ≤ p ∨ rhoJ r p = 0 := by
  unfold rhoJ
  split_ifs with h
  · exact Or.inl h.2
  · exact Or.inr rfl

theorem rhoJ_dim (f r p : ℕ) : rhoJ r p * (2 * f) ≤ f * r := by
  unfold rhoJ
  split_ifs with h
  · nlinarith [h.1]
  · simp

def junkLocalData (D : D7) (r j p : ℕ) : ModuliIntegralCharts.Loc D r j p := locT D r j p (cfJunk p) (rhoJ r p)

def exJunk (D : D7) (r j p : ℕ) : ModuliIntegralCharts.ExtA D (junkLocalData D r j p) := extT D r j p (cfJunk p) (rhoJ r p)

def junkLocBAll (D : D7) (r j p : ℕ) : BoundaryLocalData.LocB D (junkLocalData D r j p) :=
  locBT D r j p (cfJunk p) (rhoJ r p) (rhoJ_p r p) (rhoJ_dim D.R.f r p)

def junkLocB (D : D7) (r j p : ℕ) (_hp : p.Prime) : BoundaryLocalData.LocB D (junkLocalData D r j p) := junkLocBAll D r j p

section Facts

variable (D : D7) (r j p : ℕ) (c : CF p) (ρ : ℕ)

theorem locT_not_good (h : 0 < ρ) : ¬ (locT D r j p c ρ).good (Z := ()) true :=
  fun hs => (Nat.pos_iff_ne_zero.1 (rkB_true_pos h)) ((subsingleton_pow D (rkB ρ true)).1 hs)

theorem locT_isChart (h : 0 < ρ) : IsChart (locT D r j p c ρ) (Z := ()) (y := true) (e := ()) () :=
  ⟨trivial, trivial, rkB_true_pos h, trivial, trivial⟩

theorem rhoJ_pos {r p : ℕ} (hr : 2 ≤ r) (hp : 2 ≤ p) : 0 < rhoJ r p := by
  simp [rhoJ, hr, hp]

theorem junkLocalData_bad {r p : ℕ} (hr : 2 ≤ r) (hp : 2 ≤ p) :
    ∃ y : (junkLocalData D r j p).Pt (junkLocalData D r j p).Xm, ¬ (junkLocalData D r j p).good y :=
  ⟨true, locT_not_good D r j p (cfJunk p) (rhoJ r p) (rhoJ_pos hr hp)⟩

theorem junkLocalData_chart {r p : ℕ} (hr : 2 ≤ r) (hp : 2 ≤ p) :
    ∃ (y : (junkLocalData D r j p).DVP) (e : (junkLocalData D r j p).Ext y)
      (χ : (junkLocalData D r j p).Chart (junkLocalData D r j p).Xm y e),
      0 < (junkLocalData D r j p).dvRho y ∧ IsChart (junkLocalData D r j p) χ :=
  ⟨true, (), (), rkB_true_pos (rhoJ_pos hr hp), locT_isChart D r j p (cfJunk p) (rhoJ r p) (rhoJ_pos hr hp)⟩

theorem junkLocalData_be_pd {Z : (junkLocalData D r j p).Mdl} (y : (junkLocalData D r j p).Pt Z) (n : ℕ)
    (b : Module.Basis (Fin n) ℤ ((junkLocalData D r j p).Ylat y)) (x : Fin n → ℝ) :
    x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * (junkLocalData D r j p).be y (b i) (b k) :=
  fun hx => pd_of_int ((junkLocalData D r j p).be y) ((junkLocalData D r j p).be_symm y)
    (fun a a' => beK_int D (rkB (rhoJ r p) y) a a') ((junkLocalData D r j p).be_pos y) b x hx

variable {D r j p}

theorem good_of_le_one {L : Loc D r j p} (B : BoundaryLocalData.LocB D L) (hp : p ≤ 1) {Z : L.Mdl} (y : L.Pt Z) : L.good y := by
  have key : ∀ a : L.Ylat y, a = 0 := fun a => by
    by_contra h
    have h1 := L.be_pos y a h
    rw [B.be_tau] at h1
    have h2 : Real.log (p : ℝ) = 0 := by
      interval_cases p <;> simp
    simp [BoundaryLocalData.vU, Real.logb, h2] at h1
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem good_of_rank_le_one {L : Loc D r j p} (B : BoundaryLocalData.LocB D L) (hr : r ≤ 1) (y : L.Pt L.Xm) : L.good y := by
  by_contra hns
  rw [Loc.good, not_subsingleton_iff_nontrivial] at hns
  obtain ⟨a, ha⟩ := exists_ne (0 : L.Ylat y)
  have htf : ∀ n : ℤ, n • a = 0 → n = 0 := by
    intro n hn
    by_contra h0
    have h1 := L.be_pos y a ha
    have h2 : L.be y (n • a) a = 0 := by
      rw [hn]
      simp
    rw [map_smul, LinearMap.smul_apply, zsmul_eq_mul] at h2
    have h3 : (n : ℝ) ≠ 0 := by exact_mod_cast h0
    rcases mul_eq_zero.1 h2 with h | h
    · exact h3 h
    · exact h1.ne' h
  let φ : 𝓞 D.host.E →ₗ[ℤ] L.Ylat y :=
    (LinearMap.toSpanSingleton (𝓞 D.host.E) (L.Ylat y) a).restrictScalars ℤ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro e he
    by_contra h0
    obtain ⟨d, hd⟩ := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 D.host.E) e
    have h3 : Algebra.intNorm ℤ (𝓞 D.host.E) e • a = 0 := by
      have h4 : e • a = 0 := he
      rw [← algebraMap_smul (𝓞 D.host.E), hd, mul_comm, mul_smul, h4, smul_zero]
    exact (Algebra.intNorm_ne_zero.2 h0) (htf _ h3)
  have h4 := LinearMap.finrank_le_finrank_of_injective hinj
  have h5 := B.dimB_add y
  have h6 : L.dP y = Module.finrank ℤ (L.Ylat y) := rfl
  have h7 : 0 < D.R.f := by
    have := D.R.ord_pos
    simp only [Ranks.f, Ranks.n]
    omega
  rw [finrank_OE] at h4
  have h8 : D.R.f * r ≤ D.R.f := by
    interval_cases r <;> simp
  omega

end Facts

end Formalism.L2.Geo

end
