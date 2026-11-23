import Mathlib
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PointGlobalSectionsNeBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFramesNormAtEqNorm

open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory.ProvisionalDivX

section Form

variable {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
  (c : Module.Basis (Fin n) ℂ W)

def formMap : (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

theorem formMap_apply (x : Fin n → K) : formMap e c x = ∑ i, e (x i) • c i := rfl

theorem repr_formMap (x : Fin n → K) (i : Fin n) : c.repr (formMap e c x) i = e (x i) := by
  rw [formMap_apply, c.repr_sum_self]

theorem formMap_injective : Function.Injective (formMap e c) := by
  intro x y h
  funext i
  apply e.injective
  rw [← repr_formMap e c, ← repr_formMap e c, h]

theorem formMap_basisFun (i : Fin n) : formMap e c (Pi.basisFun K (Fin n) i) = c i := by
  apply c.repr.injective
  ext k
  rw [repr_formMap, Pi.basisFun_apply, c.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : k = i
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h h'.symm), map_zero]

theorem mem_range_formMap {v : W} (hv : ∀ i, c.repr v i ∈ Set.range e) :
    v ∈ Set.range (formMap e c) := by
  choose x hx using hv
  refine ⟨x, c.repr.injective ?_⟩
  ext i
  rw [repr_formMap, hx]

theorem span_eq_top_of_formMap (S : Set (Fin n → K))
    (h : Submodule.span ℂ (formMap e c '' S) = ⊤) : Submodule.span K S = ⊤ := by
  by_contra hne
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let ψ : W →ₗ[ℂ] ℂ := c.constr ℂ (fun i => e (f (Pi.basisFun K (Fin n) i)))
  have hψ : ∀ x, ψ (formMap e c x) = e (f x) := by
    intro x
    rw [formMap_apply, map_sum]
    conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ψ]
  have h0 : ψ = 0 := by
    apply LinearMap.ext_on h
    rintro _ ⟨x, hx, rfl⟩
    have : f x = 0 := hle (Submodule.subset_span hx)
    rw [hψ, this, map_zero, LinearMap.zero_apply]
  apply hf
  ext x
  have := hψ (Pi.single x 1)
  rw [h0, LinearMap.zero_apply] at this
  simpa using this.symm

end Form

theorem exists_hLat_form (K : Type) [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (c : Module.Basis (Fin n) ℂ W)
    (gen : Finset W) (hspan : Submodule.span ℂ (gen : Set W) = ⊤)
    (hrat : ∀ v ∈ gen, ∀ i, c.repr v i ∈ Set.range e) :
    ∃ (H : HLat K) (j : H.V →ₛₗ[e] W), H.Good ∧
      (LinearIndependent ℂ (fun i => j (H.b i)) ∧
        Submodule.span ℂ (Set.range (fun i => j (H.b i))) = ⊤) ∧
      (∀ x, x ∈ H.L ↔ ∃ a : W → 𝓞 K, j x = ∑ v ∈ gen, e ((a v : 𝓞 K) : K) • v) ∧
      (∀ x ∈ gen, x ∈ Set.range j) ∧
      (∀ x, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord H.b H.X (InfinitePlace.mk e) x) = ‖j x‖) := by
  classical
  obtain ⟨X, hX, hn⟩ := GlobalTheory.exists_frames_normAt_eq_norm K e W n c ⊥
  have hpre : ∀ v : W, ∃ x : Fin n → K, v ∈ gen → formMap e c x = v := by
    intro v
    by_cases hv : v ∈ gen
    · obtain ⟨x, hx⟩ := mem_range_formMap e c (hrat v hv)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose pre hpre using hpre
  have hb : (fun i => formMap e c (Pi.basisFun K (Fin n) i)) = c :=
    funext (formMap_basisFun e c)
  have hsum : ∀ a : W → 𝓞 K, formMap e c (∑ v ∈ gen, a v • pre v) =
      ∑ v ∈ gen, e ((a v : 𝓞 K) : K) • v := by
    intro a
    rw [map_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [show a v • pre v = ((a v : 𝓞 K) : K) • pre v from rfl, LinearMap.map_smulₛₗ, hpre v hv]
  refine ⟨HLat.mk (Fin n → K) (Fin n) (Pi.basisFun K (Fin n)) X
    (Submodule.span (𝓞 K) (pre '' (gen : Set W))), formMap e c, ⟨hX, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, hn⟩
  · exact Submodule.fg_span (gen.finite_toSet.image pre)
  · apply span_eq_top_of_formMap e c
    rw [eq_top_iff, ← hspan]
    apply Submodule.span_mono
    intro v hv
    exact ⟨pre v, Submodule.subset_span ⟨v, hv, rfl⟩, hpre v hv⟩
  · show LinearIndependent ℂ (fun i => formMap e c (Pi.basisFun K (Fin n) i))
    rw [hb]; exact c.linearIndependent
  · show Submodule.span ℂ (Set.range (fun i => formMap e c (Pi.basisFun K (Fin n) i))) = ⊤
    rw [hb]; exact c.span_eq
  · intro (x : Fin n → K)
    show x ∈ Submodule.span (𝓞 K) (pre '' (gen : Set W)) ↔ ∃ a : W → 𝓞 K,
      formMap e c x = ∑ v ∈ gen, e ((a v : 𝓞 K) : K) • v
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        refine ⟨fun w => if w = v then 1 else 0, ?_⟩
        rw [hpre v hv, Finset.sum_eq_single_of_mem v hv (fun w _ hw => by simp [hw])]
        simp
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by simp [ha, hb, add_smul, Finset.sum_add_distrib]⟩
      | smul r x _ hx =>
        obtain ⟨a, ha⟩ := hx
        refine ⟨fun w => r * a w, ?_⟩
        rw [show r • x = (r : K) • x from rfl, LinearMap.map_smulₛₗ, ha, Finset.smul_sum]
        simp [mul_smul]
    · rintro ⟨a, ha⟩
      rw [← hsum a, (formMap_injective e c).eq_iff] at ha
      rw [ha]
      exact Submodule.sum_mem _ fun v hv =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, hv, rfl⟩)
  · intro v hv
    exact ⟨pre v, hpre v hv⟩

structure MjForm (D : D7) (j : ℕ) where

  H : HLat D.what₂.LL

  jm : H.V →ₛₗ[D.what₂.embLL] D.what₂.Mj j
  good : H.Good
  basis : LinearIndependent ℂ (fun i => jm (H.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jm (H.b i))) = ⊤
  lat : 1 ≤ j → j ≤ D.R.m → ∀ x, x ∈ H.L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
    jm x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v
  sub : 1 ≤ j → j ≤ D.R.m → ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range jm
  metric : ∀ x, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord H.b H.X
    (InfinitePlace.mk D.what₂.embLL) x) = ‖jm x‖

theorem nonempty_mjForm (D : D7) (j : ℕ)
    (h : 1 ≤ j → j ≤ D.R.m → ∃ (n : ℕ) (c : Module.Basis (Fin n) ℂ (D.what₂.Mj j)),
      ∀ v ∈ (D.what₂.MjLat j).gen, ∀ i, c.repr v i ∈ Set.range D.what₂.embLL) :
    Nonempty (MjForm D j) := by
  classical
  by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
  · obtain ⟨n, c, hc⟩ := h hj.1 hj.2
    obtain ⟨H, jm, h1, h2, h3, h4, h5⟩ := exists_hLat_form D.what₂.LL D.what₂.embLL (D.what₂.Mj j) n c
      _ (D.what₂.MjLat j).span_top hc
    exact ⟨⟨H, jm, h1, h2, fun _ _ => h3, fun _ _ => h4, h5⟩⟩
  · let c := Module.finBasis ℂ (D.what₂.Mj j)
    obtain ⟨H, jm, h1, h2, -, -, h5⟩ := exists_hLat_form D.what₂.LL D.what₂.embLL (D.what₂.Mj j) _ c
      (Finset.univ.image c) (by simp) (by
        intro v hv i
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hv
        rw [c.repr_self, Finsupp.single_apply]
        split_ifs
        · exact ⟨1, map_one _⟩
        · exact ⟨0, map_zero _⟩)
    exact ⟨⟨H, jm, h1, h2, fun a b => absurd ⟨a, b⟩ hj, fun a b => absurd ⟨a, b⟩ hj, h5⟩⟩

theorem resChar_eq_iff (D : D7) {p : ℕ} (hp : p.Prime) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = p ↔ (p : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  constructor
  · intro h; rw [← h]; exact resChar_mem D w
  · intro hmem
    by_contra hne
    have hcop : Nat.Coprime (D.what₂.places.resChar w) p :=
      (Nat.coprime_primes (D.what₂.places.resChar_prime w) hp).mpr hne
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (p : 𝓞 D.what₂.LL) :=
      hcop.cast
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem D w)) (Ideal.mul_mem_left _ _ hmem)

def placeEquiv (D : D7) (p : ℕ) [hp : Fact p.Prime] :
    Formalism.L2.Geo.PlL D p ≃ {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} :=
  (D.plEq.subtypeEquiv (resChar_eq_iff D hp.out)).symm

theorem wtL_eq_ramIdx_mul (D : D7) (p : ℕ) [hp : Fact p.Prime] (la : Formalism.L2.Geo.PlL D p) :
    Formalism.L2.Geo.wtL D p la = (D.what₂.places.ramIdx (placeEquiv D p la).1 : ℝ) *
      (padicValNat p (Ideal.absNorm (D.plEq (placeEquiv D p la).1).asIdeal) : ℝ) /
        (Module.finrank ℚ D.what₂.LL : ℝ) := by
  have he : D.plEq (placeEquiv D p la).1 = la.1 := D.plEq.apply_symm_apply _
  have := liesOver_of_mem p hp.out la.1 la.2
  have hN := Ideal.pow_inertiaDeg p la.1.asIdeal
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  rw [D.ram_eq, he, Formalism.L2.Geo.wtL, ← hN, padicValNat.prime_pow]
  push_cast
  rw [Real.log_pow]
  field_simp

def smallShim (D : D7) (r : ℕ) : DV.ShimX D.what₂.Tau :=
  provisionalShimX D.what₂.Tau (max r 2) 1 ∅ le_rfl (by omega) (by simp)

end GlobalTheory.ProvisionalDivX

namespace GlobalTheory

open ProvisionalDivX

def provisionalDivX (D : D7) (G : DV.Geo D.what₂.LL) (Y : G.Var)
    (jc : ∀ (p : ℕ) [Fact p.Prime], DV.KW p →+* ℂ)
    (M : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ),
      DV.Mdl D p (max r 2) (DV.rkOf (DV.PsiOf D (jc p)) (max r 2) 1))
    (F : ∀ j, MjForm D j) : DivX D :=
  letI := D.host.cmStar
  { geo := G
    Lev := Unit
    levPr := fun _ => ∅
    shv := fun S _ => smallShim D S.rank
    shv_N := fun _ _ h => max_eq_left h
    shv_lev := fun _ _ => rfl
    PlP := fun p _ => Formalism.L2.Geo.PlL D p
    plpFin := fun p _ => Formalism.L2.Geo.finPl D p
    plpNe := fun p _ => Formalism.L2.Geo.plL_ne D p
    wtP := fun p _ => Formalism.L2.Geo.wtL D p
    divisorWeight_nonneg := fun p _ => Formalism.L2.Geo.wtL_nonneg D p
    divisorWeight_sum := fun p _ => Formalism.L2.Geo.wtL_sum D p
    plP := fun p _ => placeEquiv D p
    divisorWeight_def := fun p _ => wtL_eq_ramIdx_mul D p
    jC := fun p _ _ => jc p
    Mp := fun _ _ _ _ _ => Unit
    md := fun S _ p _ _ _ => M p S.rank
    vdd := fun _ _ => 0
    vdd_unram := fun _ _ _ => rfl
    phiFr_unram := fun _ _ _ _ _ _ => rfl
    vdd_nonneg := fun _ _ => le_rfl
    CurveM := fun _ _ _ _ _ _ => Empty
    degM := fun _ _ _ _ _ _ _ _ => 0
    htMdl := fun _ _ _ _ _ => ()
    htCurve := fun _ _ p _ =>
      { toFun := fun c => Empty.elim c
        invFun := fun c => c.2
        left_inv := fun c => Empty.elim c
        right_inv := fun c => Empty.elim c.2 }
    htCurve_deg := fun _ _ _ _ c => Empty.elim c
    MjH := fun j => (F j).H
    MjH_good := fun j => (F j).good
    jM := fun j => (F j).jm
    jM_basis := fun j => (F j).basis
    jM_lat := fun j => (F j).lat
    MjLat_sub := fun j => (F j).sub
    jM_metric := fun j _ _ => (F j).metric
    Qp := fun _ => ∅
    degreeZero_partial_set_empty := rfl
    Qp_muAt := fun _ => Finset.notMem_empty _
    Qp_g := fun _ _ _ => Finset.notMem_empty _
    QPl := fun _ => Empty
    qv := fun _ v => v.elim
    qv_gt := fun _ v => v.elim
    qv_char := fun _ _ v => v.elim
    nu := fun _ v => v.elim
    nu_ne := fun _ v => v.elim
    nu_abs := fun _ v => v.elim
    ZQ := fun _ v => v.elim
    quotientLocalValueFirst := fun _ v => v.elim
    typeDim := fun _ v => v.elim
    Comp := fun _ => Unit
    degHH := fun _ _ _ => 0
    Yv := fun _ _ => Y
    Ybd := fun _ _ => G.supp Y 0
    Lw := fun _ _ => 0
    iMj := fun _ _ => 0
    iMj_mem := fun _ _ _ => Submodule.zero_mem _
    logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
    logLam_base := fun _ _ => rfl
    kapR := fun _ => kapSharp D
    kapR_pos := fun _ => RowSide.kapOf_pos _ _
    kapR_conj := fun _ => rfl
    Surf := Empty
    surfCh2 := fun s => s.elim
    surfDegOm := fun s => s.elim
    SurfFp := Empty
    surfFpCh2 := fun s => s.elim }

theorem exists_provisionalDivX : ∀ D : D7, (∀ j, 1 ≤ j → j ≤ D.R.m →
    ∃ (n : ℕ) (c : Module.Basis (Fin n) ℂ (D.what₂.Mj j)),
      ∀ v ∈ (D.what₂.MjLat j).gen, ∀ i, c.repr v i ∈ Set.range D.what₂.embLL) →
    ∃ X : DivX D, DV.KapRBase X := by
  intro D h
  obtain ⟨G, Y, -⟩ := GlobalTheory.PointGeometry.exists_geo D.what₂.LL
  exact ⟨provisionalDivX D G Y (fun p _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some)
    (fun p _ r => (GlobalTheory.nonempty_admissibleModel D p _ (max r 2) 1 (by omega)).some)
    (fun j => (nonempty_mjForm D j (h j)).some), rfl⟩

end GlobalTheory

end
