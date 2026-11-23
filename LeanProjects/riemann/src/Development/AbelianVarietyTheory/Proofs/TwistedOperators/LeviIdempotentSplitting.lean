import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff

noncomputable section

namespace GlobalTheory.SignProj

open Formalism.BasicNotions GlobalTheory.Cusp GlobalTheory.TruncKer GlobalTheory.Chamber
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp IsIsotropic)

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : HSpace E}

def proj (Φ : WittFrame V) (u : SV (wittIndex V)) : V.V →ₗ[E] V.V :=
  ∑ i, if u i = 1 then (V.hT (Φ.f i)).smulRight (Φ.e i)
    else if u i = -1 then (V.hT (Φ.e i)).smulRight (Φ.f i) else 0

def eps (Φ : WittFrame V) (u : SV (wittIndex V)) : Matrix (Fin V.rank) (Fin V.rank) E :=
  LinearMap.toMatrix V.frame V.frame (proj Φ u)

theorem proj_apply (Φ : WittFrame V) (u : SV (wittIndex V)) (y : V.V) :
    proj Φ u y = ∑ i, if u i = 1 then V.hD y (Φ.f i) • Φ.e i
      else if u i = -1 then V.hD y (Φ.e i) • Φ.f i else 0 := by
  simp only [proj, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [HSpace.hD]

variable (Φ : WittFrame V) (u : SV (wittIndex V))

theorem hD_f_e (i j : Fin (wittIndex V)) : V.hD (Φ.f i) (Φ.e j) = if i = j then 1 else 0 := by
  have h := V.herm.eq (Φ.f i) (Φ.e j)
  simp only [HSpace.hD] at *
  have e2 := Φ.ef j i
  simp only [HSpace.hD] at e2
  rw [← h, e2]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

theorem hD_sum_left {ι : Type} (s : Finset ι) (c : ι → V.V) (w : V.V) :
    V.hD (∑ i ∈ s, c i) w = ∑ i ∈ s, V.hD (c i) w := by
  simp only [HSpace.hD, map_sum]

theorem hD_smul_left (a : E) (x w : V.V) : V.hD (a • x) w = a * V.hD x w := by
  simp only [HSpace.hD, map_smul, smul_eq_mul]

theorem hD_sub_left (x y w : V.V) : V.hD (x - y) w = V.hD x w - V.hD y w := by
  simp only [HSpace.hD, map_sub]

theorem proj_e {i : Fin (wittIndex V)} (hi : u i = 1) : proj Φ u (Φ.e i) = Φ.e i := by
  rw [proj_apply, Finset.sum_eq_single i]
  · rw [if_pos hi, Φ.ef, if_pos rfl, one_smul]
  · intro j _ hj
    split_ifs
    · rw [Φ.ef, if_neg (Ne.symm hj), zero_smul]
    · rw [Φ.ee, zero_smul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ i) h

theorem proj_f {i : Fin (wittIndex V)} (hi : u i = -1) : proj Φ u (Φ.f i) = Φ.f i := by
  rw [proj_apply, Finset.sum_eq_single i]
  · rw [if_neg (by rw [hi]; decide), if_pos hi, hD_f_e, if_pos rfl, one_smul]
  · intro j _ hj
    split_ifs
    · rw [Φ.ff, zero_smul]
    · rw [hD_f_e, if_neg (Ne.symm hj), zero_smul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ i) h

theorem proj_f_eq_zero {i : Fin (wittIndex V)} (hi : u i = 1) : proj Φ u (Φ.f i) = 0 := by
  rw [proj_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h1 h2
  · rw [Φ.ff, zero_smul]
  · have : i ≠ j := fun e => by subst e; rw [hi] at h2; exact absurd h2 (by decide)
    rw [hD_f_e, if_neg this, zero_smul]
  · rfl

theorem proj_e_eq_zero {i : Fin (wittIndex V)} (hi : u i = -1) : proj Φ u (Φ.e i) = 0 := by
  rw [proj_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h1 h2
  · have : i ≠ j := fun e => by subst e; rw [hi] at h1; exact absurd h1 (by decide)
    rw [Φ.ef, if_neg this, zero_smul]
  · rw [Φ.ee, zero_smul]
  · rfl

theorem e_ne_zero (i : Fin (wittIndex V)) : Φ.e i ≠ 0 := fun h => by
  have := Φ.ef i i
  rw [h, if_pos rfl] at this
  simp [HSpace.hD] at this

theorem f_ne_zero (i : Fin (wittIndex V)) : Φ.f i ≠ 0 := fun h => by
  have := Φ.ef i i
  rw [h, if_pos rfl] at this
  simp [HSpace.hD] at this

theorem e_mem_sub {i : Fin (wittIndex V)} (hi : u i = 1) : Φ.e i ∈ Φ.sub u :=
  Submodule.subset_span (Or.inl ⟨i, hi, rfl⟩)

theorem f_mem_sub {i : Fin (wittIndex V)} (hi : u i = -1) : Φ.f i ∈ Φ.sub u :=
  Submodule.subset_span (Or.inr ⟨i, hi, rfl⟩)

theorem proj_mem (y : V.V) : proj Φ u y ∈ Φ.sub u := by
  rw [proj_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · exact Submodule.smul_mem _ _ (e_mem_sub Φ u h1)
  · exact Submodule.smul_mem _ _ (f_mem_sub Φ u h2)
  · exact zero_mem _

theorem proj_self {x : V.V} (hx : x ∈ Φ.sub u) : proj Φ u x = x := by
  have : Φ.sub u ≤ LinearMap.eqLocus (proj Φ u) LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact proj_e Φ u hi
    · exact proj_f Φ u hi
  exact this hx

theorem proj_proj (y : V.V) : proj Φ u (proj Φ u y) = proj Φ u y := proj_self Φ u (proj_mem Φ u y)

theorem hD_proj_f {j : Fin (wittIndex V)} (hj : u j = 1) (y : V.V) :
    V.hD (proj Φ u y) (Φ.f j) = V.hD y (Φ.f j) := by
  rw [proj_apply, hD_sum_left, Finset.sum_eq_single j]
  · rw [if_pos hj, hD_smul_left, Φ.ef, if_pos rfl, mul_one]
  · intro i _ hij
    split_ifs
    · rw [hD_smul_left, Φ.ef, if_neg hij, mul_zero]
    · rw [hD_smul_left, Φ.ff, mul_zero]
    · simp [HSpace.hD]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem hD_proj_e {j : Fin (wittIndex V)} (hj : u j = -1) (y : V.V) :
    V.hD (proj Φ u y) (Φ.e j) = V.hD y (Φ.e j) := by
  rw [proj_apply, hD_sum_left, Finset.sum_eq_single j]
  · rw [if_neg (by rw [hj]; decide), if_pos hj, hD_smul_left, hD_f_e, if_pos rfl, mul_one]
  · intro i _ hij
    split_ifs
    · rw [hD_smul_left, Φ.ee, mul_zero]
    · rw [hD_smul_left, hD_f_e, if_neg hij, mul_zero]
    · simp [HSpace.hD]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem neg_eq_one_iff (s : SignType) : -s = 1 ↔ s = -1 := by decide +revert
theorem neg_eq_neg_one_iff (s : SignType) : -s = -1 ↔ s = 1 := by decide +revert

theorem sub_proj_mem_perp (y : V.V) : y - proj Φ u y ∈ perp V (Φ.sub (-u)) := by
  have : Φ.sub (-u) ≤ LinearMap.ker (V.hT.flip (y - proj Φ u y)) := by
    refine Submodule.span_le.2 ?_
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · have hi' : u i = -1 := (neg_eq_one_iff _).1 hi
      show V.hD (y - proj Φ u y) (Φ.e i) = 0
      rw [hD_sub_left, hD_proj_e Φ u hi', sub_self]
    · have hi' : u i = 1 := (neg_eq_neg_one_iff _).1 hi
      show V.hD (y - proj Φ u y) (Φ.f i) = 0
      rw [hD_sub_left, hD_proj_f Φ u hi', sub_self]
  exact GlobalTheory.Cusp.mem_perp.2 fun x hx => this hx

theorem eq_zero_of_mem {x : V.V} (h1 : x ∈ Φ.sub u) (h2 : x ∈ perp V (Φ.sub (-u))) : x = 0 := by
  rw [← proj_self Φ u h1, proj_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with a b
  · rw [GlobalTheory.Cusp.mem_perp.1 h2 _ (f_mem_sub Φ (-u) (by simp [a])), zero_smul]
  · rw [GlobalTheory.Cusp.mem_perp.1 h2 _ (e_mem_sub Φ (-u) (by simp [b])), zero_smul]
  · rfl

theorem exists_ne (hu : u ≠ 0) : ∃ i, u i = 1 ∨ u i = -1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
  have key : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  exact ⟨i, key _ hi⟩

theorem sub_ne_bot (hu : u ≠ 0) : Φ.sub u ≠ ⊥ := by
  obtain ⟨i, hi | hi⟩ := exists_ne u hu
  · exact fun h => e_ne_zero Φ i (by simpa [h] using e_mem_sub Φ u hi)
  · exact fun h => f_ne_zero Φ i (by simpa [h] using f_mem_sub Φ u hi)

theorem sub_le_perp : Φ.sub u ≤ perp V (Φ.sub u) := by
  have gen : ∀ a ∈ Φ.e '' {i | u i = 1} ∪ Φ.f '' {i | u i = -1},
      ∀ b ∈ Φ.e '' {i | u i = 1} ∪ Φ.f '' {i | u i = -1}, V.hD a b = 0 := by
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) _ (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Φ.ee i j
    · have : i ≠ j := fun e => by
        subst e; exact absurd ((show u i = 1 from hi).symm.trans (show u i = -1 from hj)) (by decide)
      rw [Φ.ef, if_neg this]
    · have : i ≠ j := fun e => by
        subst e; exact absurd ((show u i = -1 from hi).symm.trans (show u i = 1 from hj)) (by decide)
      rw [hD_f_e, if_neg this]
    · exact Φ.ff i j
  refine Submodule.span_le.2 fun a ha => ?_
  have : Φ.sub u ≤ LinearMap.ker (V.hT.flip a) :=
    Submodule.span_le.2 fun b hb => (gen a ha b hb : _)
  exact GlobalTheory.Cusp.mem_perp.2 fun x hx => this hx

theorem isIsotropic_sub (hu : u ≠ 0) : IsIsotropic V (Φ.sub u) := ⟨sub_ne_bot Φ u hu, sub_le_perp Φ u⟩

theorem eps_mul_self : eps Φ u * eps Φ u = eps Φ u := by
  rw [eps, ← LinearMap.toMatrix_comp]
  congr 1
  exact LinearMap.ext fun y => proj_proj Φ u y

theorem rank_eps : (eps Φ u).rank = Module.finrank E (LinearMap.range (proj Φ u)) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ V.frame V.frame, eps, Matrix.toLin_toMatrix]

theorem rank_eps_pos (hu : u ≠ 0) : 0 < (eps Φ u).rank := by
  rw [rank_eps]
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [Submodule.finrank_eq_zero] at h
  obtain ⟨i, hi | hi⟩ := exists_ne u hu
  · exact e_ne_zero Φ i (by simpa [proj_e Φ u hi, h] using LinearMap.mem_range_self (proj Φ u) (Φ.e i))
  · exact f_ne_zero Φ i (by simpa [proj_f Φ u hi, h] using LinearMap.mem_range_self (proj Φ u) (Φ.f i))

theorem rank_eps_lt (hu : u ≠ 0) : (eps Φ u).rank < V.rank := by
  rw [rank_eps, ← V.rank_eq]
  refine Submodule.finrank_lt fun h => ?_
  have hinj : Function.Injective (proj Φ u) :=
    LinearMap.injective_iff_surjective.2 (LinearMap.range_eq_top.1 h)
  obtain ⟨i, hi | hi⟩ := exists_ne u hu
  · exact f_ne_zero Φ i (hinj (by rw [proj_f_eq_zero Φ u hi, map_zero]))
  · exact e_ne_zero Φ i (hinj (by rw [proj_e_eq_zero Φ u hi, map_zero]))

end GlobalTheory.SignProj

section Places

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp IsIsotropic extSub coordR act parab unipRad)
open GlobalTheory.SplitFlag
open scoped Matrix TensorProduct

namespace GlobalTheory.SignProj

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : HSpace E}

theorem comp_proj (Φ : WittFrame V) (u : SV (wittIndex V)) (T : V.V →ₗ[E] V.V)
    (h1 : ∀ x ∈ Φ.sub u, T x ∈ Φ.sub u) (h2 : ∀ x ∈ perp V (Φ.sub (-u)), T x ∈ perp V (Φ.sub (-u))) :
    T ∘ₗ proj Φ u = proj Φ u ∘ₗ T := by
  refine LinearMap.ext fun y => ?_
  have hz : proj Φ u (T y) - T (proj Φ u y) = 0 := by
    refine eq_zero_of_mem Φ u (sub_mem (proj_mem Φ u _) (h1 _ (proj_mem Φ u y))) ?_
    have e : proj Φ u (T y) - T (proj Φ u y) = T (y - proj Φ u y) - (T y - proj Φ u (T y)) := by
      rw [map_sub]; abel
    rw [e]
    exact sub_mem (h2 _ (sub_proj_mem_perp Φ u y)) (sub_proj_mem_perp Φ u (T y))
  exact (sub_eq_zero.1 hz).symm

end GlobalTheory.SignProj

namespace GlobalTheory.SignProj

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (u : SV (wittIndex V))

theorem comm_of_mem_levi (γ : GF V) (hγ : rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u}) :
    γ.1.1 * eps Φ u = eps Φ u * γ.1.1 := by
  simp only [WittFrame.levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hγ
  obtain ⟨hA, hB⟩ := hγ u (Finset.mem_singleton_self u)
  haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
  have h1 : ∀ x ∈ Φ.sub u, ratAct D.sp.cm V γ x ∈ Φ.sub u := (diagH_mem_parab (AF D.host.F)).1 hA
  have h2' : ∀ x ∈ Φ.sub (-u), ratAct D.sp.cm V γ x ∈ Φ.sub (-u) := (diagH_mem_parab (AF D.host.F)).1 hB
  have h2 : ∀ x ∈ perp V (Φ.sub (-u)), ratAct D.sp.cm V γ x ∈ perp V (Φ.sub (-u)) :=
    (diagH_mem_parab D.host.F).1 (parab_le_perp ((diagH_mem_parab D.host.F).2 h2'))
  have hc := comp_proj Φ u _ h1 h2
  have hγm : γ.1.1 = LinearMap.toMatrix V.frame V.frame (ratAct D.sp.cm V γ) :=
    (LinearMap.toMatrix_toLin V.frame V.frame γ.1.1).symm
  rw [hγm, eps, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, hc]

theorem splitVec_sub' {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y z : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E) :
    splitVec τ (y - z) = splitVec τ y - splitVec τ z := funext fun _ => map_sub _ _ _

theorem epsR_mulVec_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} {y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E}
    (hy : y ∈ extSub (F := D.host.F) V (Fv D.host.F v) (Φ.sub u)) :
    (eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v)) *ᵥ y = y := by
  have : extSub (F := D.host.F) V (Fv D.host.F v) (Φ.sub u) ≤
      LinearMap.eqLocus ((eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v))).mulVecLin LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    change ((eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v))) *ᵥ coordR (F := D.host.F) V (Fv D.host.F v) x =
      coordR (F := D.host.F) V (Fv D.host.F v) x
    rw [map_mulVec_coordR]
    have e : (eps Φ u *ᵥ fun j => V.frame.repr x j) = fun j => V.frame.repr x j := by
      have := LinearMap.toMatrix_mulVec_repr V.frame V.frame (proj Φ u) x
      rw [proj_self Φ u hx] at this
      exact this
    rw [e]
    rfl
  exact this hy

theorem epsR_mulVec_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (a : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E) :
    (eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v)) *ᵥ a ∈ extSub (F := D.host.F) V (Fv D.host.F v) (Φ.sub u) := by
  refine mulVec_mem_extSub V _ _ (fun k => ?_) a
  have : GlobalTheory.AutFunCompare.vecOf V ((eps Φ u)ᵀ k) = proj Φ u (V.frame k) := by
    simp only [GlobalTheory.AutFunCompare.vecOf, eps]
    refine V.frame.repr.injective ?_
    ext i
    simp [LinearMap.toMatrix_apply]
  rw [this]
  exact proj_mem Φ u _

theorem map_epsR {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    ((eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v))).map (splitProj τ) = (eps Φ u).map τ := by
  refine Matrix.ext fun i j => ?_
  exact splitProj_inclR τ (eps Φ u i j)

theorem eps_mulVec_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    {w : Fin V.rank → Fv D.host.F v} (hw : w ∈ wPart τ (Φ.sub u)) : (eps Φ u).map τ *ᵥ w = w := by
  obtain ⟨y, hy, rfl⟩ := hw
  rw [← map_epsR, ← splitVec_mulVec, epsR_mulVec_of_mem Φ u hy]

theorem eps_mulVec_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (w : Fin V.rank → Fv D.host.F v) : (eps Φ u).map τ *ᵥ w ∈ wPart τ (Φ.sub u) := by
  have h := isCMExt_host D
  rw [← splitVec_splitIncl h τ w, ← map_epsR, ← splitVec_mulVec]
  exact splitVec_mem_wPart τ (epsR_mulVec_mem Φ u _)

theorem mem_unipRad (hu : u ≠ 0) (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig V.gram v)
    (H : (eps Φ u).map τ * ((splitHom D.sp.cm.sig V.gram τ g).1 - 1) * (1 - (eps Φ u).map τ) =
      (splitHom D.sp.cm.sig V.gram τ g).1 - 1) :
    g ∈ unipRad D.sp.cm V (Fv D.host.F v) (Φ.sub u) := by
  have h := isCMExt_host D
  have hJ := isHermND_gram V
  set A := (splitHom D.sp.cm.sig V.gram τ g).1 with hA
  set B := (splitHom D.sp.cm.sig V.gram (τ.comp D.sp.cm.sig) g).1 with hB
  set εt := (eps Φ u).map τ
  have T0 : ∀ w, A *ᵥ w - w = εt *ᵥ ((A - 1) *ᵥ ((1 - εt) *ᵥ w)) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, H, Matrix.sub_mulVec, Matrix.one_mulVec]
  have T1 : ∀ w ∈ wPart τ (Φ.sub u), A *ᵥ w = w := fun w hw => by
    have h0 : (1 - εt) *ᵥ w = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, show εt *ᵥ w = w from eps_mulVec_of_mem Φ u τ hw, sub_self]
    have := T0 w
    rw [h0, Matrix.mulVec_zero, Matrix.mulVec_zero] at this
    exact sub_eq_zero.1 this
  have T2 : ∀ w, A *ᵥ w - w ∈ wPart τ (Φ.sub u) := fun w => by
    rw [T0 w]; exact eps_mulVec_mem Φ u τ _
  have T3 : ∀ w' ∈ wPart (τ.comp D.sp.cm.sig) (perp V (Φ.sub u)), B *ᵥ w' = w' := fun w' hw' => by
    have hw'' := (mem_wPart_comp_iff D.sp.cm h hJ τ).1 hw'
    rw [perp_perp] at hw''
    set d := B *ᵥ w' - w'
    have hd : ∀ z, d ⬝ᵥ V.gram.map τ *ᵥ z = 0 := fun z => by
      obtain ⟨z₀, rfl⟩ : ∃ z₀, A *ᵥ z₀ = z := ⟨((splitHom D.sp.cm.sig V.gram τ g)⁻¹).1 *ᵥ z, by
        rw [hA, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
      have e1 : (B *ᵥ w') ⬝ᵥ V.gram.map τ *ᵥ (A *ᵥ z₀) = w' ⬝ᵥ V.gram.map τ *ᵥ z₀ :=
        pairing_splitHom τ g w' z₀
      have e2 : w' ⬝ᵥ V.gram.map τ *ᵥ (A *ᵥ z₀ - z₀) = 0 := hw'' _ (T2 z₀)
      rw [Matrix.mulVec_sub, dotProduct_sub] at e2
      show (B *ᵥ w' - w') ⬝ᵥ V.gram.map τ *ᵥ (A *ᵥ z₀) = 0
      rw [sub_dotProduct, e1]
      linear_combination -e2
    have hv : Matrix.vecMul d (V.gram.map τ) = 0 := funext fun k => by
      have := hd (Pi.single k 1)
      rw [Matrix.dotProduct_mulVec] at this
      simpa using this
    have : d = 0 := by
      have e := congrArg (fun x => Matrix.vecMul x ((splitGram hJ τ)⁻¹).1) hv
      simp only [Matrix.zero_vecMul, Matrix.vecMul_vecMul] at e
      rwa [← splitGram_val hJ τ, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at e
    exact sub_eq_zero.1 this
  have T4 : ∀ w' ∈ wPart (τ.comp D.sp.cm.sig) (Φ.sub u), B *ᵥ w' = w' := fun w' hw' =>
    T3 w' (wPart_mono _ (sub_le_perp Φ u) hw')
  have key : ∀ (τ' : D.host.E →ₐ[D.host.F] Fv D.host.F v) y, splitVec τ' (act D.sp.cm V g y) =
      (splitHom D.sp.cm.sig V.gram τ' g).1 *ᵥ splitVec τ' y := fun τ' y => splitVec_matHom_mulVec τ' g y
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := (mem_extSub_iff_split D.sp.cm h τ).1 hy
    exact splitVec_ext h τ (by rw [key]; exact T1 _ h1) (by rw [key]; exact T4 _ h2)
  · obtain ⟨-, h2⟩ := (mem_extSub_iff_split D.sp.cm h τ).1 hy
    refine (mem_extSub_iff_split D.sp.cm h τ).2 ⟨?_, ?_⟩
    · rw [splitVec_sub', key]; exact T2 _
    · rw [splitVec_sub', key, T3 _ h2, sub_self]; exact zero_mem _

end GlobalTheory.SignProj

theorem GlobalTheory.SignProj.exists_proj_unip : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)), u ≠ 0 →
    ∃ (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u)), ε * ε = ε ∧
      0 < ε.rank ∧ ε.rank < V.rank ∧
      (∀ γ : GF V, rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → γ.1.1 * ε = ε * γ.1.1) ∧
      ∀ v (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GLoc D.sp.cm.sig V.gram v),
        ε.map τ * ((splitHom D.sp.cm.sig V.gram τ g).1 - 1) * (1 - ε.map τ) = (splitHom D.sp.cm.sig V.gram τ g).1 - 1 →
        emb D.sp.cm.sig V.gram v g ∈ NA (IsoFlag.single hW) := by
  intro D V Φ u hu
  refine ⟨GlobalTheory.SignProj.eps Φ u, GlobalTheory.SignProj.isIsotropic_sub Φ u hu, GlobalTheory.SignProj.eps_mul_self Φ u,
    GlobalTheory.SignProj.rank_eps_pos Φ u hu, GlobalTheory.SignProj.rank_eps_lt Φ u hu,
    fun γ hγ => GlobalTheory.SignProj.comm_of_mem_levi Φ u γ hγ, fun v τ g H => ?_⟩
  refine IsoFlag.emb_mem_unip.2 ?_
  rw [IsoFlag.unip_single]
  exact GlobalTheory.SignProj.mem_unipRad Φ u hu v τ g H

end Places
