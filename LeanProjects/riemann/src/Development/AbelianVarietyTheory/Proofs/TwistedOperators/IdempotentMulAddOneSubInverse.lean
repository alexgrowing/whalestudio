import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulActO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinear

open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.VecInv
open GlobalTheory.AdelicLatMove (mt_mul mt_one)

variable {D : D7} {S T : HSp D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem absV_inv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v)ˣ) :
    absV F v x⁻¹ = (absV F v x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← absV_mul, inv_mul_cancel]
  simp [absV]

theorem sqrt_div_mul_eq_sqrt_mul {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (a b : ℕ) :
    (Real.sqrt ((p ^ b * q⁻¹ ^ a)⁻¹))⁻¹ = p ^ ((b : ℝ) / 2) * q ^ (-(a : ℝ) / 2) := by
  rw [Real.sqrt_inv, inv_inv, Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity), inv_pow,
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hq.le, ← Real.rpow_mul hp.le, ← Real.rpow_mul hq.le]
  congr 2 <;> ring

section Chart

variable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem chart_inj (hπ : Chart e v π) {u u' : WO S T} (hu : IsHalf e u) (hu' : IsHalf e u') (h : u.map π = u'.map π) :
    u = u' := by
  ext i j
  have h1 : π (u i j - u' i j) = 0 := by rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h i) j
  rw [hπ.2.1, mul_sub, hu i j, hu' i j, sub_eq_zero] at h1
  exact h1

theorem exists_section (he : e * e = e) (hπ : Chart e v π) :
    ∃ σ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) →+ WO S T, (∀ w, (σ w).map π = w) ∧ ∀ w, IsHalf e (σ w) := by
  choose s hs using hπ.1
  have p1 : ∀ w : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v), Matrix.map (e • w.map s) π = w := fun w => by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, chart_e he hπ, one_mul, Matrix.map_apply, hs]
  exact ⟨AddMonoidHom.mk' (fun w => e • w.map s) fun w w' => chart_inj hπ (isHalf_smul' he _)
    (GlobalTheory.SplitScalar.isHalf_add (isHalf_smul' he _) (isHalf_smul' he _)) (by
      rw [Matrix.map_add _ π.map_add, p1, p1, p1]), p1, fun w => isHalf_smul' he _⟩

theorem chart_det (he : e * e = e) (hπ : Chart e v π) {V : HSp D} {k : GA D V} {z : (AE D)ˣ} (hz : IsDetAt e V k z) :
    ((mt V k).map π).det = π z := by
  rw [hz, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, chart_e he hπ, one_mul, sub_self, add_zero,
    RingHom.map_det]
  rfl

theorem chart_det_inv (he : e * e = e) (hπ : Chart e v π) {V : HSp D} {k : GA D V} {z : (AE D)ˣ} (hz : IsDetAt e V k z) :
    ((mt V k⁻¹).map π).det = ((Units.map π.toMonoidHom z)⁻¹ : (Fv D.host.F v)ˣ) := by
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  change _ * π z = 1
  rw [← chart_det he hπ hz, ← Matrix.det_mul, ← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one,
    Matrix.map_one _ π.map_zero π.map_one, Matrix.det_one]

theorem off_det (he : e * e = e) {V : HSp D} {k : GA D V} {z : (AE D)ˣ} (hz : IsDetAt e V k z) :
    (1 - e) * (z : AE D) = 1 - e := by
  rw [hz]; linear_combination (1 - (mt V k).det) * he

variable {σ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) →+ WO S T}

theorem section_smul (he : e * e = e) (hπ : Chart e v π) (q1 : ∀ w, (σ w).map π = w) (q2 : ∀ w, IsHalf e (σ w))
    (o : Fv D.host.F v) (ho : o ∈ v.adicCompletionIntegers D.host.F) (m : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))
    (hm : σ m ∈ latO S T ΛS ΛT fun _ => True) : σ (o • m) ∈ latO S T ΛS ΛT fun _ => True := by
  obtain ⟨s, hs⟩ := hπ.1 o
  have : σ (o • m) = (e * s) • σ m := chart_inj hπ (q2 _) (by rw [mul_smul]; exact isHalf_smul' he _) (by
    rw [q1]
    ext i j
    have := congrFun (congrFun (q1 m) i) j
    rw [Matrix.map_apply] at this
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.map_mul,
      RingHom.map_mul, chart_e he hπ, hs, one_mul, this])
  rw [this]
  exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ((hπ.2.2.2 _).2 (isInt_Ov.2 (by rwa [hs]))) _ hm

theorem section_den (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) (hπ : Chart e v π)
    (q1 : ∀ w, (σ w).map π = w) (q2 : ∀ w, IsHalf e (σ w)) :
    ∃ N : ℕ, 0 < N ∧ ∀ m, σ m ∈ (latO S T ΛS ΛT fun _ => True) → ∀ i j,
      (N : Fv D.host.F v) * m i j ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨N, hN, h1⟩ := exists_den_latO (S := S) (T := T) hS.fg hT.fg
  refine ⟨N, hN, fun m hm i j => ?_⟩
  have h2 := finPart_mem_of_toEAf (w := (N : AE D) * σ m i j) (by
    rw [RingHom.map_mul, map_natCast]; exact h1 _ hm i j)
  rw [← q2 m i j, mul_left_comm, hπ.2.2.2, isInt_Ov, RingHom.map_mul, map_natCast] at h2
  rw [← congrFun (congrFun (q1 m) i) j]
  exact h2

theorem section_range (hπ : Chart e v π) (q1 : ∀ w, (σ w).map π = w) (q2 : ∀ w, IsHalf e (σ w)) :
    σ.range = half S T e := by
  ext u
  refine ⟨?_, fun hu => ⟨u.map π, chart_inj hπ (q2 _) ((isHalf_iff S T).2 hu) (q1 _)⟩⟩
  rintro ⟨w, rfl⟩
  exact (isHalf_iff S T).1 (q2 w)

theorem section_act (hπ : Chart e v π) (q1 : ∀ w, (σ w).map π = w) (q2 : ∀ w, IsHalf e (σ w)) (g : GA D S) (h : GA D T)
    (w : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) :
    actO S T g⁻¹ h⁻¹ (σ w) = σ ((mt T h⁻¹).map π * w * (mt S g).map π) :=
  chart_inj hπ (isHalf_actO _ _ (q2 w)) (q2 _) (by rw [q1, actO, inv_inv, Matrix.map_mul, Matrix.map_mul, q1])

end Chart

theorem relIndex_comap_range {G G' : Type} [AddCommGroup G] [AddCommGroup G'] (σ : G →+ G') (h : Function.Injective σ)
    (A B : AddSubgroup G') : (A ⊓ σ.range).relIndex (B ⊓ σ.range) = (A.comap σ).relIndex (B.comap σ) := by
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ h, AddSubgroup.map_comap_eq, AddSubgroup.map_comap_eq,
    inf_comm A, inf_comm B]

theorem sqrt_index (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} {x y : (AE D)ˣ} (hx : IsDetAt e S g x) (hy : IsDetAt e T h y)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    (Real.sqrt ((((latO S T ΛS ΛT fun _ => True) ⊓ half S T e).relIndex
      ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e) : ℕ) : ℝ))⁻¹ = modFac S T x y := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  obtain ⟨σ, q1, q2⟩ := exists_section (S := S) (T := T) he.1 hπ
  have inj : Function.Injective σ := fun w w' h => by rw [← q1 w, h, q1]
  have hinf : infPart D e = 0 := GlobalTheory.PlaceModelSum.IsOrthSum.infPart_eq
    ⟨Unit, {()}, fun _ => e, fun _ _ => he, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => e) ()).symm⟩
  have hA := relIndex_matrix_lattice D.host.F v S.rank T.rank ((latO S T ΛS ΛT fun _ => True).comap σ)
    (((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹)).comap σ) (section_smul he.1 hπ q1 q2)
    (section_den hS hT hπ q1 q2) (fun w => ?_)
    ((mt T h⁻¹).map π) ((mt S g).map π) (Units.map π.toMonoidHom x) (Units.map π.toMonoidHom y)⁻¹ (chart_det he.1 hπ hx)
    (chart_det_inv he.1 hπ hy) (fun m hm => ?_) (fun w => ?_)
  · rw [← section_range hπ q1 q2, relIndex_comap_range σ inj, hA, absV_inv, ← absFin_split D e v π he hπ x (off_det he.1 hx),
      ← absFin_split D e v π he hπ y (off_det he.1 hy)]
    exact sqrt_div_mul_eq_sqrt_mul (absFin_pos D x) (absFin_pos D y) _ _
  · obtain ⟨k, hk, h1⟩ := exists_nsmul_mem_latO' hS hT (σ w) (infPart_of_half hinf (q2 w))
    exact ⟨k, hk, by rwa [AddSubgroup.mem_comap, map_nsmul]⟩
  · rw [AddSubgroup.mem_comap, ← section_act hπ q1 q2]
    exact hle _ hm (q2 m)
  · rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, AddSubgroup.mem_comap, ← section_act hπ q1 q2]
    rfl

theorem actO_mul (g g' : GA D S) (h h' : GA D T) (u : WO S T) :
    actO S T (g * g') (h * h') u = actO S T g h (actO S T g' h' u) := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]

def Law (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (a : AE D) (Λ : AddSubgroup (WO S T))
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (g : GA D S) (h : GA D T) (C : ℂ) : Prop :=
  ∀ Φ, IsSBHalf a Λ Φ → om (g, h) (Tm Φ) = C • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t)

variable {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {a : AE D} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}

theorem Law.mul (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) {g g' : GA D S}
    {h h' : GA D T} {C C' : ℂ} (H : Law om a (latO S T ΛS ΛT fun _ => True) Tm g h C)
    (H' : Law om a (latO S T ΛS ΛT fun _ => True) Tm g' h' C') :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm (g * g') (h * h') (C * C') := fun Φ hΦ => by
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, H' Φ hΦ, map_smul, H _ (isSBHalf_actO hS hT _ _ hΦ), smul_smul,
    mul_comm C']
  simp only [_root_.mul_inv_rev, actO_mul]

theorem Law.inv (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) {g : GA D S}
    {h : GA D T} {C : ℂ} (hC : C ≠ 0) (H : Law om a (latO S T ΛS ΛT fun _ => True) Tm g h C) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g⁻¹ h⁻¹ C⁻¹ := fun Φ hΦ => by
  have h1 := H _ (isSBHalf_actO hS hT g h hΦ)
  simp only [act_act_inv] at h1
  have h2 := congrArg (om (g⁻¹, h⁻¹)) h1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
    Module.End.one_apply, map_smul] at h2
  rw [inv_inv, inv_inv, h2, smul_smul, inv_mul_cancel₀ hC, one_smul]

theorem Law.congr {Λ : AddSubgroup (WO S T)} {g g' : GA D S} {h h' : GA D T} {C C' : ℂ} (H : Law om a Λ Tm g h C)
    (e1 : g = g') (e2 : h = h') (e3 : C = C') : Law om a Λ Tm g' h' C' := e1 ▸ e2 ▸ e3 ▸ H

def fac (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) : ℂ :=
  (splitFacO χS χT x y : ℂ) * (modFac S T x y : ℂ)

variable {χS χT : (AE D)ˣ →* Circle}

theorem fac_mul (x x' y y' : (AE D)ˣ) :
    fac S T χS χT (x * x') (y * y') = fac S T χS χT x y * fac S T χS χT x' y' := by
  unfold fac
  rw [GlobalTheory.WeilSplit.splitFacO_mul, modFac_mul, Circle.coe_mul, Complex.ofReal_mul]
  ring

theorem fac_ne_zero (x y : (AE D)ˣ) : fac S T χS χT x y ≠ 0 :=
  mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (modFac_pos S T x y).ne')

theorem fac_one : fac S T χS χT 1 1 = 1 := by
  simp [fac, modFac_one, splitFacO]

theorem suppAt_mul {e : AE D} {V : HSp D} {g g' : GA D V} (h : SuppAt e V g) (h' : SuppAt e V g') :
    SuppAt e V (g * g') :=
  suppAt_of (by
    rw [mt_mul, ← Matrix.smul_mul, GlobalTheory.SplitScalar.off_smul_mt h, Matrix.smul_mul, Matrix.one_mul,
      GlobalTheory.SplitScalar.off_smul_mt h'])

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := suppAt_of (by rw [mt_one])

theorem actO_scalar {e : AE D} {z : GA D T} {N : ℕ}
    (z2 : e • mt T z = e • ((N : AE D) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)))) {w : WO S T} (hw : IsHalf e w) :
    actO S T 1 z w = N • w := by
  have hw' := (mem_half S T).1 ((isHalf_iff S T).1 hw)
  rw [actO, inv_one, mt_one, Matrix.mul_one, ← hw', Matrix.mul_smul, ← Matrix.smul_mul, z2, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.one_mul, smul_comm, Nat.cast_smul_eq_nsmul]

theorem actO_scalar' {e : AE D} {z : GA D T} {N : ℕ}
    (z2 : e • mt T z = e • ((N : AE D) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)))) (g : GA D S) (h : GA D T)
    {w : WO S T} (hw : IsHalf e w) : actO S T g⁻¹ (h * z⁻¹)⁻¹ w = N • actO S T g⁻¹ h⁻¹ w := by
  rw [← actO_scalar z2 (isHalf_actO _ _ hw), ← actO_mul, one_mul, _root_.mul_inv_rev, inv_inv]

theorem exists_scalar {e : AE D} (he : IsSplitIdem D e) (V : HSp D) {N : ℕ} (hN : 0 < N) :
    ∃ z : GA D V, SuppAt e V z ∧ e • mt V z = e • ((N : AE D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) := by
  have hN' : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.SplitOnto.exists_unitary (c := cA D) GlobalTheory.SplitOnto.cA_cA (GlobalTheory.SplitOnto.gram_mul_inv V)
    (GlobalTheory.SplitOnto.gram_conj V) he.1 he.2.1 ((N : AE D) • 1) (incA D (N : D.host.E)⁻¹ • 1) (by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul (incA D _), ← map_natCast (incA D), ← map_mul, inv_mul_cancel₀ hN',
        map_one, one_smul])
  let g' : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨g, h1⟩
  exact ⟨g', fun i j => congrFun (congrFun h2 i) j, h3⟩

variable {ψ : AddChar (AF D.host.F) ℂ} {f₀ : WO S T → ℂ}

section Model

variable (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (ha : a * a = a)
  (hinf : infPart D a = 0) (hc : a * cA D a = 0) (hf : IsThetaFunO ψ S T f₀)
  (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀)
  (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)

include hW hS hT ha hinf hc hf hv hTm

theorem law_enlarge {e : AE D} (he : IsSplitIdem D e) (hae : a * e = e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g)
    (hh : SuppAt e T h)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  have h1 := om_base_enlarge D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hf hTm hc hv e he hae g h hg hh _ _
    (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle
  rw [← Complex.ofReal_inv, sqrt_index hS.1 hT.1 he (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle] at h1
  exact om_model_of_base D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hf hTm g h _ h1

theorem law_place {e : AE D} (he : IsSplitIdem D e) (hae : a * e = e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g)
    (hh : SuppAt e T h) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  obtain ⟨N, hN, h1⟩ := exists_nsmul_actO hS.1 hT.1 g⁻¹ h⁻¹
  obtain ⟨z, z1, z2⟩ := exists_scalar he T hN
  have z4 : SuppAt e T z⁻¹ := suppAt_of (GlobalTheory.SplitScalar.off_smul_mt_inv z1)
  have l1 := law_enlarge hW hS hT ha hinf hc hf hv hTm he hae hg (suppAt_mul hh z4) fun w hw hwe => by
    rw [actO_scalar' z2 g h hwe]
    exact h1 w hw
  have l2 := law_enlarge hW hS hT ha hinf hc hf hv hTm he hae (suppAt_one e S) z4 fun w hw hwe => by
    rw [inv_one, inv_inv, actO_scalar z2 hwe]
    exact nsmul_mem hw N
  have l3 := l1.mul hS.1 hT.1 (l2.inv hS.1 hT.1 (fac_ne_zero _ _))
  have e1 : fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T (h * z⁻¹)) =
      fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h) * fac S T χS χT (detAt e he.1 S 1) (detAt e he.1 T z⁻¹) := by
    rw [← fac_mul, ← MonoidHom.map_mul, ← MonoidHom.map_mul, mul_one]
  exact l3.congr (by rw [inv_one, mul_one]) (mul_inv_cancel_right _ _)
    (by rw [e1, mul_inv_cancel_right₀ (fac_ne_zero _ _)])

theorem law_sum {ι : Type} (es : ι → AE D) (P : Finset ι) :
    (∀ i ∈ P, IsSplitIdem D (es i)) → (∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) →
      (∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0) → (∀ i ∈ P, a * es i = es i) → ∀ (g : GA D S) (h : GA D T),
      SuppAt (∑ i ∈ P, es i) S g → SuppAt (∑ i ∈ P, es i) T h →
      ∀ x y, IsDetAt (∑ i ∈ P, es i) S g x → IsDetAt (∑ i ∈ P, es i) T h y →
        Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT x y) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro _ _ _ _ g h hg hh x y hx hy
    rw [Finset.sum_empty] at hg hh hx hy
    have k : ∀ (V : HSp D) (g : GA D V), SuppAt 0 V g → g = 1 := fun V g hg => GlobalTheory.WeilSplit.ext_mt (by
      rw [mt_one, ← sub_eq_zero]
      ext i j
      rw [← hg i j, RingHom.map_zero, add_zero, zero_mul, Matrix.zero_apply])
    have k' : ∀ (V : HSp D) (g : GA D V) (x : (AE D)ˣ), IsDetAt 0 V g x → x = 1 := fun V g x hx =>
      Units.ext (hx.trans (by rw [zero_mul, zero_add, sub_zero, Units.val_one]))
    intro Φ _
    rw [k S g hg, k T h hh, k' S g x hx, k' T h y hy, Prod.mk_one_one, map_one, fac_one, one_smul,
      Module.End.one_apply]
    simp only [actO, inv_one, mt_one, Matrix.mul_one, Matrix.one_mul]
  | insert i P hi ih =>
    intro h1 h2 h3 h4 g h hg hh x y hx hy
    have m0 := Finset.mem_insert_self i P
    have h1' : ∀ j ∈ P, IsSplitIdem D (es j) := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have h2' : ∀ j ∈ P, ∀ k ∈ P, k ≠ j → es j * es k = 0 := fun j hj k hk =>
      h2 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have ih' := ih h1' h2' (fun j hj k hk => h3 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      fun j hj => h4 j (Finset.mem_insert_of_mem hj)
    have a0 : (∑ j ∈ P, es j) * ∑ j ∈ P, es j = ∑ j ∈ P, es j :=
      GlobalTheory.PlaceModelSum.IsOrthSum.idem ⟨ι, P, es, h1', h2', rfl⟩
    have a1 : es i * ∑ j ∈ P, es j = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => h2 i m0 j (Finset.mem_insert_of_mem hj) fun h => hi (h ▸ hj)
    have a2 : (∑ j ∈ P, es j) * cA D (es i) = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun j hj => h3 j (Finset.mem_insert_of_mem hj) i m0
    have a3 : (∑ j ∈ P, es j) * cA D (∑ j ∈ P, es j) = 0 := by
      rw [map_sum, Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k hk =>
        h3 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    rw [Finset.sum_insert hi] at hg hh hx hy
    have he := h1 i m0
    generalize ∑ j ∈ P, es j = e' at *
    obtain ⟨hb, hc₁, hb', hc', d2, d3, d4⟩ :=
      GlobalTheory.WeilSplit.idem_laws (cA D) GlobalTheory.DualPairCheck.cA_cA he.1 he.2.1 a0 a1 a2 a3
    have s1 : ∀ (V : HSp D) (g : GA D V), SuppAt (es i) V (GlobalTheory.WeilSplit.cut _ hb hc₁ V g) := fun V g i j => by
      rw [GlobalTheory.WeilSplit.mt_cut_sub, ← mul_assoc, hb]
    have s2 : ∀ (V : HSp D) (g : GA D V), SuppAt (es i + e') V g → SuppAt e' V (GlobalTheory.WeilSplit.cut _ hb' hc' V g) :=
      fun V g hg i j => by
        rw [GlobalTheory.WeilSplit.mt_cut_sub]
        exact d4 _ (hg i j)
    have r1 := law_place hW hS hT ha hinf hc hf hv hTm he (h4 i m0) (s1 S g) (s1 T h)
    have r2 := ih' _ _ (s2 S g hg) (s2 T h hh) _ _ (isDetAt_detAt e' a0 S _) (isDetAt_detAt e' a0 T _)
    have r3 := r1.mul hS.1 hT.1 r2
    exact r3.congr (GlobalTheory.WeilSplit.cut_mul_cut hb hc₁ hb' hc' S g) (GlobalTheory.WeilSplit.cut_mul_cut hb hc₁ hb' hc' T h)
      ((fac_mul _ _ _ _).symm.trans (congrArg₂ (fac S T χS χT)
        (GlobalTheory.WeilSplit.split_det hb hc₁ he.1 a0 a1 d2 d3 hb' hc' hx).symm
        (GlobalTheory.WeilSplit.split_det hb hc₁ he.1 a0 a1 d2 d3 hb' hc' hy).symm))

end Model

theorem law_orth (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (ho : GlobalTheory.PlaceModelSum.IsOrthSum a) (hc : a * cA D a = 0) (hf : IsThetaFunO ψ S T f₀)
    (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀) {c : ℂ} (hc0 : c ≠ 0)
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) c f₀ Tm) {g : GA D S} {h : GA D T}
    (hg : SuppAt a S g) (hh : SuppAt a T h) {x y : (AE D)ˣ} (hx : IsDetAt a S g x) (hy : IsDetAt a T h y) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT x y) := by
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ (c • Tm) :=
    ⟨fun Φ hΦ x hx => by rw [LinearMap.smul_apply, LinearMap.smul_apply, hTm.trans Φ hΦ x hx, heisO_smul'],
      fun Φ hΦ x hx => by rw [LinearMap.smul_apply, LinearMap.smul_apply, hTm.modul Φ hΦ x hx, heisO_smul'],
      by rw [one_smul, LinearMap.smul_apply, ← map_smul, hTm.vac]⟩
  have ha := ho.idem
  have hinf := ho.infPart_eq
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := ho
  have h3 : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 := fun i hi j hj => by
    rw [← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hi, ← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hj, RingHom.map_mul,
      mul_mul_mul_comm, hc, mul_zero]
  intro Φ hΦ
  have := law_sum hW hS hT ha hinf hc hf hv hTm' es P h1 h2 h3
    (fun i hi => (mul_comm _ _).trans (GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hi)) g h hg hh x y hx hy Φ hΦ
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, smul_comm] at this
  exact smul_right_injective _ hc0 this

theorem subst_eq (g : GA D S) (h : GA D T) (t : WO S T) : subst S T g h t = actO S T g⁻¹ h⁻¹ t := by
  simp [subst, actO]

theorem splitLinearModel : ∀ D : D7, SplitLinearModel D := by
  intro D ψ S T χS χT om hW ΛS ΛT hS hT P e he f₀ hf hv c hc Tm hTm g h hg hh x y hx hy Φ hΦ
  rw [law_orth hW hS hT (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he) he.2 hf hv hc hTm hg hh hx hy Φ hΦ, ← map_smul]
  simp only [subst_eq]
  rfl

theorem idempotent_mul_add_one_sub_inverse {R : Type} [CommRing R] {c d d' : R} (hc : c * c = c) (h : d * d' = 1) :
    (c * d + (1 - c)) * (c * d' + (1 - c)) = 1 := by
  linear_combination c * c * h + (2 - d - d') * hc

theorem det_conj {e : AE D} (he : cA D e * cA D e = cA D e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) : (detAt (cA D e) he V g : AE D) * cA D x = 1 := by
  rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
  exact idempotent_mul_add_one_sub_inverse he (GlobalTheory.SplitDetCharacter.det_mul_conj V g)

theorem norm_aux {R : Type} [CommRing R] {x y x' y' : R} (h : y * x' = 1) (h' : y' * x = 1) : y * x * (y' * x') = 1 := by
  linear_combination (y' * x) * h + h'

theorem absFin_of_mul_conj {x y : (AE D)ˣ} (h : (y : AE D) * cA D x = 1) : absFin D y = (absFin D x)⁻¹ := by
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have h' := congrArg (cA D) h
  rw [RingHom.map_mul, GlobalTheory.SplitOnto.cA_cA, RingHom.map_one] at h'
  have h1 : Algebra.norm (AF D.host.F) ((y * x : (AE D)ˣ) : AE D) = 1 := hinj (by
    rw [GlobalTheory.SplitDetCharacter.algebraMap_norm, RingHom.map_one, Units.val_mul, RingHom.map_mul]
    exact norm_aux h h')
  have h2 : ∀ v, normV D v (y * x) = 1 := fun v => Units.ext (by
    change evalV D.host.F v (sndA D.host.F (Algebra.norm (AF D.host.F) ((y * x : (AE D)ˣ) : AE D))) = 1
    rw [h1, map_one, map_one])
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← absFin_mul, absFin]
  simp [h2, absV]

theorem splitLinearModelConj : ∀ D : D7, SplitLinearModelConj D := by
  intro D ψ S T χS χT om hW ΛS ΛT hS hT P e he f₀ hf hv c hc Tm hTm g h hg hh x y hx hy Φ hΦ
  have ho := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).conj
  have sc : ∀ (V : HSp D) (k : GA D V), SuppAt e V k → SuppAt (cA D e) V k := fun V k hk i j => by
    rw [GlobalTheory.SplitOnto.cA_cA, add_comm]; exact hk i j
  have dx := det_conj ho.idem hx
  have dy := det_conj ho.idem hy
  rw [law_orth hW hS hT ho (by rw [GlobalTheory.SplitOnto.cA_cA, mul_comm, he.2]) hf hv hc hTm (sc S g hg) (sc T h hh)
    (isDetAt_detAt _ ho.idem S g) (isDetAt_detAt _ ho.idem T h) Φ hΦ, ← map_smul]
  have e1 : fac S T χS χT (detAt _ ho.idem S g) (detAt _ ho.idem T h) =
      (splitFacO χS χT x y : ℂ) * ((modFac S T x y)⁻¹ : ℝ) := by
    rw [fac, splitFacO, splitFacO, GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resT _ _ dx,
      GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resS _ _ dy, modFac, modFac, absFin_of_mul_conj dx,
      absFin_of_mul_conj dy, Real.inv_rpow (absFin_pos D x).le, Real.inv_rpow (absFin_pos D y).le, mul_inv]
  rw [e1]
  simp only [subst_eq]
  rfl

end GlobalTheory.SplitLinear

end
