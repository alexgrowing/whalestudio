import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section

namespace GlobalTheory.CompPhase

section Abstract

variable {R S : Type} [CommRing R] [Ring S] [Algebra R S] {st : S →+ S} {e : S} {h : R}

def skw (st : S →+ S) (e : S) (h : R) (z : S) : S :=
  e * z * (1 - e - h • st e) - st (e * z * (1 - e - h • st e))

def ex (h : R) (x : S) : S := 1 + x + h • (x * x)

theorem st_one' (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) : st 1 = 1 := by
  have := hm (st 1) 1
  rw [mul_one, hi, mul_one] at this
  exact this.symm

theorem half_add (hh : h + h = 1) (x : S) : h • x + h • x = x := by rw [← add_smul, hh, one_smul]

theorem st_smul (hh : h + h = 1) (x : S) : st (h • x) = h • st x := by
  conv_rhs => rw [← half_add hh x, map_add, smul_add, half_add hh]

theorem cube_zero {f x y w : S} (hx : x * e = 0) (hy : (1 - e) * y * (1 - f) = 0) (hw : f * w = 0) : x * y * w = 0 := by
  have : x * y * w = x * ((1 - e) * y * (1 - f)) * w + x * e * (y * w) + x * y * (f * w) - x * e * (y * (f * w)) := by
    noncomm_ring
  rw [this, hx, hy, hw]; simp

theorem ex_unitary (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) (hh : h + h = 1) {x : S}
    (hs : st x = -x) (h3 : x * x * x = 0) : st (ex h x) * ex h x = 1 := by
  have h4 : x * x * (x * x) = 0 := by rw [← mul_assoc, h3, zero_mul]
  have h3' : x * (x * x) = 0 := by rw [← mul_assoc, h3]
  simp only [ex, map_add, st_one' hm hi, st_smul hh, hm, hs, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg,
    neg_neg, h3, h3', h4, one_mul, mul_one, smul_zero, add_zero, neg_zero]
  have := half_add hh (x * x)
  generalize h • (x * x) = y at this ⊢
  rw [← this]; abel

theorem skw_spec (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) (hh : h + h = 1) (he : e * e = e)
    (h0 : st e * e = 0) (z : S) : st (ex h (skw st e h z)) * ex h (skw st e h z) = 1 := by
  have he' : st e * st e = st e := by rw [← hm, he]
  have e1 : st (e * z * (1 - e - h • st e)) = (1 - st e - h • e) * st z * st e := by
    rw [hm, hm, map_sub, map_sub, st_one' hm hi, st_smul hh, hi, mul_assoc]
  refine ex_unitary hm hi hh (by rw [skw, map_sub, hi, neg_sub]) (cube_zero (e := e) (f := st e) ?_ ?_ ?_)
  · rw [skw, e1, sub_mul, mul_assoc, mul_assoc _ (st e), h0, sub_mul, sub_mul, smul_mul_assoc, h0, he]; simp
  · rw [skw, e1, mul_sub (1 - e), sub_mul, ← mul_assoc, ← mul_assoc, sub_mul 1 e e, he, mul_assoc (1 - e), mul_assoc _ (st e),
      mul_sub (st e), he']
    simp
  · rw [skw, e1, mul_sub, ← mul_assoc, ← mul_assoc, h0, ← mul_assoc, ← mul_assoc, mul_sub (st e), mul_sub (st e), he', mul_smul_comm, h0]; simp

theorem exists_log (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) (hh : h + h = 1) {g : S}
    (hu : st g * g = 1) (h1 : (g - 1) * e = 0) (h2 : (1 - e) * (g - 1) * (1 - st e) = 0) : ∃ z, ex h (skw st e h z) = g := by
  have s1 := st_one' hm hi
  have k1 : g * e = e := by rwa [sub_mul, one_mul, sub_eq_zero] at h1
  have k2 : st g * e = e := by conv_lhs => rw [← k1, ← mul_assoc, hu, one_mul]
  have k3 : st e * (g - 1) = 0 := by
    have := congrArg st k2
    rw [hm, hi] at this
    rw [mul_sub, this, mul_one, sub_self]
  obtain ⟨m, rfl⟩ : ∃ m, g = 1 + m := ⟨g - 1, by abel⟩
  rw [add_sub_cancel_left] at h1 h2 k3
  have m3 : m * m * m = 0 := cube_zero h1 h2 k3
  have m3' : m * (m * m) = 0 := by rw [← mul_assoc, m3]
  have m4 : m * m * (m * m) = 0 := by rw [← mul_assoc, m3, zero_mul]
  have sm : st m = m * m - m := by
    have a : (1 + m) * (1 - m + m * m) = 1 := by
      rw [show (1 + m) * (1 - m + m * m) = 1 + m * m * m by noncomm_ring, m3, add_zero]
    have := left_inv_eq_right_inv hu a
    rw [map_add, s1] at this
    rw [← add_right_inj 1, this]; abel
  have sx : st (m - h • (m * m)) = -(m - h • (m * m)) := by
    simp only [map_sub, st_smul hh, hm, sm, mul_sub, sub_mul, m3, m3', m4, sub_zero, zero_sub, neg_neg, sub_self]
    have := half_add hh (m * m)
    generalize h • (m * m) = y at this ⊢
    rw [← this]; abel
  have x2 : (1 - e) * (m - h • (m * m)) * (1 - st e) = 0 := by
    have : (1 - e) * (m * m) * (1 - st e) = 0 := by
      have a : (1 - e) * m = (1 - e) * m * st e := by rwa [mul_sub, mul_one, sub_eq_zero] at h2
      rw [← mul_assoc, a, mul_assoc _ (st e), k3, mul_zero, zero_mul]
    rw [mul_sub (1 - e), sub_mul, h2, mul_smul_comm, smul_mul_assoc, this]; simp
  have x1 : (m - h • (m * m)) * e = 0 := by rw [sub_mul, smul_mul_assoc, mul_assoc, h1]; simp
  have x3 : st e * (m - h • (m * m)) = 0 := by rw [mul_sub, mul_smul_comm, ← mul_assoc, k3]; simp
  refine ⟨m - h • (m * m), ?_⟩
  have q : skw st e h (m - h • (m * m)) = m - h • (m * m) := by
    generalize m - h • (m * m) = x at sx x1 x2 x3
    rw [skw, hm, hm, map_sub, map_sub, s1, st_smul hh, hi, sx]
    have x1' : e * x * e = 0 := by rw [mul_assoc, x1, mul_zero]
    have x3' : st e * (x * st e) = 0 := by rw [← mul_assoc, x3, zero_mul]
    simp only [mul_sub, sub_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, mul_neg, neg_mul, x1', x3', smul_neg,
      ← mul_assoc e] at x2 ⊢
    have := half_add hh (e * x * st e)
    generalize h • (e * x * st e) = y at this ⊢
    rw [← this] at x2
    exact sub_eq_zero.1 (neg_eq_zero.1 (Eq.trans (by abel) x2))
  rw [q, ex]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, m3, m3', m4, smul_zero, sub_zero]
  abel

theorem map_ex_skw {T : Type} [Ring T] (π : S →+* T) {a y : S} (h1 : π (y - a) = 0) (h2 : π (st (y - a)) = 0)
    (hm : ∀ x y, st (x * y) = st y * st x) : π (ex h (skw st e h y)) = π (ex h (skw st e h a)) := by
  rw [map_sub, sub_eq_zero] at h1
  rw [map_sub, map_sub, sub_eq_zero] at h2
  have q : π (skw st e h y) = π (skw st e h a) := by
    simp only [skw, map_sub π, hm, map_mul, h1, h2]
  simp only [ex, Algebra.smul_def, map_add, map_mul, q]

theorem ex_skw_mem (S₀ : Subring S) (h0 : ∀ x ∈ S₀, st x ∈ S₀) (he : e ∈ S₀) (hh : algebraMap R S h ∈ S₀) {a : S} (ha : a ∈ S₀) :
    ex h (skw st e h a) ∈ S₀ := by
  have q : e * a * (1 - e - h • st e) ∈ S₀ := by
    rw [Algebra.smul_def]
    exact mul_mem (mul_mem he ha) (sub_mem (sub_mem (one_mem _) he) (mul_mem hh (h0 _ he)))
  have q' : skw st e h a ∈ S₀ := sub_mem q (h0 _ q)
  rw [ex, Algebra.smul_def]
  exact add_mem (add_mem (one_mem _) q') (mul_mem hh (mul_mem q' q'))

theorem continuous_ex_skw [TopologicalSpace S] [IsTopologicalRing S] (hc : Continuous st) :
    Continuous fun z => ex h (skw st e h z) := by
  simp only [ex, skw, Algebra.smul_def]
  fun_prop

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev sndT (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : AF F ⊗[F] E →+* Af F ⊗[F] E :=
  (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

omit [NumberField E] in

theorem dense_ratFin : Dense {x : AF F ⊗[F] E | ∃ a : E, sndT F E (x - inclR (F := F) (AF F) a) = 0} := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  let B : AddSubgroup (AF F ⊗[F] E) := (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.range ⊔ (sndT F E).toAddMonoidHom.ker
  have hB : ∀ x, x ∈ B.topologicalClosure := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul a x =>
      have hc : Continuous fun a : AF F => a ⊗ₜ[F] x := by
        have : (fun a : AF F => a ⊗ₜ[F] x) = fun a : AF F => a • ((1 : AF F) ⊗ₜ[F] x) := by
          funext a; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]; fun_prop
      have hd : Dense ((Set.univ : Set (Ainf F)) ×ˢ Set.range (algebraMap F (Af F))) :=
        dense_univ.prod GlobalTheory.AdeleCharTwist.denseRange_fin
      refine map_mem_closure (s := (Set.univ : Set (Ainf F)) ×ˢ Set.range (algebraMap F (Af F))) hc (hd a) ?_
      rintro (b : AF F) ⟨-, c, hc⟩
      refine AddSubgroup.mem_sup.2 ⟨_, ⟨c • x, rfl⟩, (b - algebraMap F (AF F) c) ⊗ₜ[F] x, ?_, ?_⟩
      · show sndA F (b - algebraMap F (AF F) c) ⊗ₜ[F] x = 0
        rw [map_sub, AlgHom.commutes, hc]
        exact (congrArg (· ⊗ₜ[F] x) (sub_self b.2)).trans (TensorProduct.zero_tmul _ _)
      · show (1 : AF F) ⊗ₜ[F] (c • x) + _ = _
        rw [TensorProduct.sub_tmul, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, add_sub_cancel]
  refine Dense.mono (s₁ := (B : Set (AF F ⊗[F] E))) (fun x hx => ?_) hB
  obtain ⟨_, ⟨a, rfl⟩, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hx
  exact ⟨a, (congrArg (sndT F E) (add_sub_cancel_left _ _)).trans hz⟩

omit [NumberField E] in
theorem sndT_sigR (σ : E →ₐ[F] E) (x : AF F ⊗[F] E) :
    sndT F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ (sndT F E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Dense

variable {D : D7} {V : HSp D}

theorem finHom_val (g : GA D V) : (finHom V g).1 = (sndT D.host.F D.host.E).mapMatrix (Formalism.L2.Theta.mt V g) := rfl

theorem sndT_adj {b : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)}
    (hb : (sndT D.host.F D.host.E).mapMatrix b = 0) :
    (sndT D.host.F D.host.E).mapMatrix (GlobalTheory.AutFunCompare.adj D.sp.cm V b) = 0 := by
  rw [GlobalTheory.AutFunCompare.adj_apply, map_mul, map_mul]
  refine mul_eq_zero_of_left (mul_eq_zero_of_right _ ?_) _
  ext i j
  exact (sndT_sigR _ (b j i)).trans ((congrArg _ (congrFun (congrFun hb j) i)).trans (map_zero _))

theorem half_adele : incA D (1 / 2) + incA D (1 / 2) = 1 := by rw [← map_add, add_halves, map_one]

def exA (V : HSp D) (e : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (z : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) :=
  ex (incA D (1 / 2)) (skw (GlobalTheory.AutFunCompare.adj D.sp.cm V) (e.map (incA D)) (incA D (1 / 2)) z)

theorem continuous_exA (e : Matrix (Fin V.rank) (Fin V.rank) D.host.E) : Continuous (exA V e) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact continuous_ex_skw ((continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF D.host.F) D.sp.cm.sig)).matrix_transpose).matrix_mul continuous_const)

theorem exA_rat (e a : Matrix (Fin V.rank) (Fin V.rank) D.host.E) :
    exA V e (a.map (incA D)) ∈ ((incA D).mapMatrix (m := Fin V.rank)).range :=
  ex_skw_mem ((incA D).mapMatrix (m := Fin V.rank)).range
    (by rintro _ ⟨X, rfl⟩; exact ⟨_, (GlobalTheory.AutFunCompare.adj_map D.sp.cm V X).symm⟩) ⟨_, rfl⟩
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply]⟩ ⟨_, rfl⟩

theorem sndT_exA (e : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    {y a : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)}
    (hb : (sndT D.host.F D.host.E).mapMatrix (y - a) = 0) :
    (sndT D.host.F D.host.E).mapMatrix (exA V e y) = (sndT D.host.F D.host.E).mapMatrix (exA V e a) := by
  have h2 := sndT_adj hb
  have hm := GlobalTheory.AutFunCompare.adj_mul D.sp.cm V
  unfold exA
  generalize GlobalTheory.AutFunCompare.adj D.sp.cm V = st at h2 hm ⊢
  generalize (sndT D.host.F D.host.E).mapMatrix (m := Fin V.rank) = π at hb h2 ⊢
  exact map_ex_skw π hb h2 hm

theorem exA_unitary {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C)
    {L : Matrix (Fin r) (Fin V.rank) D.host.E} (hL : L * C = 1) (z) :
    GlobalTheory.AutFunCompare.adj D.sp.cm V (exA V (C * L) z) * exA V (C * L) z = 1 := by
  refine skw_spec (GlobalTheory.AutFunCompare.adj_mul D.sp.cm V) (GlobalTheory.AutFunCompare.adj_adj D.sp.cm V) half_adele ?_ ?_ z
  · rw [← Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul]
  · have := hC.2.2
    rw [GlobalTheory.AutFunCompare.adj_map, ← Matrix.map_mul, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc] at this ⊢
    rw [← Matrix.mul_assoc V.gram C, ← Matrix.mul_assoc (Formalism.UG.cT _ C), this]
    simp

theorem mem_of_param (K : Subgroup (GA D V)) (hK : IsClosed (K : Set (GA D V))) (hQ : GQ V ≤ K) (hR : GinfC V ≤ K)
    (e : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (c : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) → GA D V)
    (hc : ∀ z, Formalism.L2.Theta.mt V (c z) = exA V e z) (z) : c z ∈ K := by
  have cc : Continuous c := GlobalTheory.MixModel.continuous_of_mt V (by simp only [hc]; exact continuous_exA e)
  have hd : Dense (Set.pi Set.univ fun _ : Fin V.rank => Set.pi Set.univ fun _ : Fin V.rank =>
      {x : AF D.host.F ⊗[D.host.F] D.host.E | ∃ a : D.host.E, sndT _ _ (x - incA D a) = 0}) :=
    dense_pi _ fun _ _ => dense_pi _ fun _ _ => dense_ratFin
  refine hK.closure_subset (map_mem_closure cc (hd z) fun y hy => ?_)
  choose a ha using fun i j => hy i trivial j trivial
  have h1 : c ((Matrix.of a).map (incA D)) ∈ GQ V := by
    refine (GlobalTheory.MixModel.mem_GQ_iff V _).2 ?_
    rw [hc]
    exact exA_rat e _
  have h2 : finHom V (c y) = finHom V (c ((Matrix.of a).map (incA D))) := by
    refine Units.ext ?_
    rw [finHom_val, finHom_val, hc, hc]
    exact sndT_exA e (by ext i j; exact ha i j)
  generalize c ((Matrix.of a).map (incA D)) = γ at h1 h2
  have h3 : γ⁻¹ * c y ∈ GinfC V := by
    show finHom V _ = 1
    rw [map_mul, map_inv, h2, inv_mul_cancel]
  have := K.mul_mem (hQ h1) (hR h3)
  rwa [mul_inv_cancel_left] at this

theorem exists_param {e : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (hu : ∀ z, GlobalTheory.AutFunCompare.adj D.sp.cm V (exA V e z) * exA V e z = 1) :
    ∃ c : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) → GA D V, ∀ z,
      Formalism.L2.Theta.mt V (c z) = exA V e z := by
  generalize exA V e = f at hu
  exact ⟨fun z => ⟨⟨_, _, mul_eq_one_comm.1 (hu z), hu z⟩, (GlobalTheory.AutFunCompare.adj_mul_self_iff D.sp.cm V _).1 (hu z)⟩,
    fun _ => rfl⟩

theorem exists_logA {e : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    {g : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)} (hu : GlobalTheory.AutFunCompare.adj D.sp.cm V g * g = 1)
    (h1 : (g - 1) * e.map (incA D) = 0)
    (h2 : (1 - e.map (incA D)) * (g - 1) * (1 - GlobalTheory.AutFunCompare.adj D.sp.cm V (e.map (incA D))) = 0) :
    ∃ z, exA V e z = g := by
  unfold exA
  exact exists_log (GlobalTheory.AutFunCompare.adj_mul D.sp.cm V) (GlobalTheory.AutFunCompare.adj_adj D.sp.cm V) half_adele hu h1 h2

theorem NI_le (K : Subgroup (GA D V)) (hK : IsClosed (K : Set (GA D V))) (hQ : GQ V ≤ K) (hR : GinfC V ≤ K) {r : ℕ}
    {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) : NI V C ≤ K := by
  intro n hn
  obtain ⟨L, hL, -⟩ := GlobalTheory.AutFunCompare.exists_dual D.sp.cm V C hC.2.1 hC.2.2
  rw [GlobalTheory.AutFunCompare.NI_eq] at hn
  have hn' := (GlobalTheory.AutFunCompare.mem_unipRad_idem D.sp.cm V C L hL n).1 hn
  have h' := exists_param (exA_unitary hC hL)
  obtain ⟨c, hc⟩ := h'
  have h := exists_logA ((GlobalTheory.AutFunCompare.adj_mul_self_iff D.sp.cm V _).2 n.2) hn'.1 hn'.2
  obtain ⟨z, hz⟩ := h
  have hzn : c z = n := GlobalTheory.MixModel.mt_injective V ((hc z).trans hz)
  rw [← hzn]
  exact mem_of_param K hK hQ hR _ c hc z

section Phase

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {u : GA D V → ℂ}

structure CompFun (V : HSp D) (u : GA D V → ℂ) : Prop where
  left : ∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h
  real : ∀ g ∈ GinfC V, ∀ h, u (h * g) = u h
  lev : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, ∀ g, u (g * k) = u g

theorem CompFun.cont (hu : CompFun V u) : Continuous u := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨U, hU, e⟩ := hu.lev
  refine continuous_iff_continuousAt.2 fun g => (continuousAt_const (y := u g)).congr ?_
  have : ∀ᶠ x in nhds g, g⁻¹ * x ∈ (U : Set (GA D V)) :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp))
  filter_upwards [this] with x hx
  rw [← e _ hx g, mul_inv_cancel_left]

theorem CompFun.unip (hu : CompFun V u) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C)
    {n : GA D V} (hn : n ∈ NI V C) (g : GA D V) : u (n * g) = u g := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  let K : Subgroup (GA D V) :=
    { carrier := {n | ∀ g, u (n * g) = u g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun ha hb g => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha g => by rw [← ha, mul_inv_cancel_left] }
  refine NI_le K ?_ hu.left (fun k hk g => ?_) hC hn g
  · have : (K : Set (GA D V)) = ⋂ g, {n | u (n * g) = u g} := Set.ext fun n => ⟨fun h => Set.mem_iInter.2 h, fun h => Set.mem_iInter.1 h⟩
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (hu.cont.comp (continuous_mul_const g)) continuous_const
  · rw [← hu.real _ ((MonoidHom.normal_ker (finHom V)).conj_mem' k hk g) g]
    congr 1; group

theorem atTau_mem_real (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  exacts [h.choose_spec.1, one_mem _]

theorem CompFun.rder (hu : CompFun V u) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (u * φ) = u * Rder θ V τ X φ := by
  funext g
  simp only [Rder, Pi.mul_apply, oneP, hu.real _ (atTau_mem_real τ _), deriv_const_mul_field]

theorem foldr_mul {α : Type} (F : α → (GA D V → ℂ) → (GA D V → ℂ)) (hF : ∀ a φ, F a (u * φ) = u * F a φ) (l : List α)
    (φ : GA D V → ℂ) : l.foldr F (u * φ) = u * l.foldr F φ := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, List.foldr_cons, ih, hF]

theorem CompFun.gelf (hu : CompFun V u) (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ k (u * φ) = u * gelf θ V τ k φ := by
  have h : ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)),
      (l.map (RderC θ V τ)).foldr (fun f acc => f acc) (u * φ) = u * (l.map (RderC θ V τ)).foldr (fun f acc => f acc) φ := by
    intro l
    rw [List.foldr_map, List.foldr_map]
    refine foldr_mul (fun Z acc => RderC θ V τ Z acc) (fun Z ψ => ?_) l φ
    simp only [RderC, hu.rder, mul_add, mul_smul_comm]
  simp only [Formalism.L2.Theta.gelf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have := h (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) 1)
  rw [List.map_ofFn] at this
  exact this

theorem CompFun.aut (hu : CompFun V u) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) : IsAutFunSm θ V (u * φ) := by
  refine ⟨⟨fun γ hγ g => ?_, ?_, hu.cont.mul h.cont⟩, fun k τs Xs hX g => ?_, ?_, ?_⟩
  · simp only [Pi.mul_apply, h.left γ hγ, hu.left γ hγ]
  · obtain ⟨U, hU, e⟩ := h.level
    obtain ⟨U', hU', e'⟩ := hu.lev
    refine ⟨U ⊓ U', hU.inter hU', fun k hk hf g => ?_⟩
    simp only [Pi.mul_apply, e k hk.1 hf, e' k hk.2]
  · have hc : ∀ t : Fin k → ℝ, u (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) = u g := fun t =>
      hu.real _ (Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact atTau_mem_real _ _) g
    simp only [Pi.mul_apply, hc]
    exact contDiff_const.mul (h.smooth k τs Xs hX g)
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨W.map (LinearMap.mulLeft ℂ u), inferInstance, ⟨φ, m, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨_, s τ k f hf, (hu.gelf τ k f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖u x‖ * C, fun g hg => ?_⟩
    have e := foldr_mul (u := u) (fun (p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) f => Rder θ V p.1 p.2 f)
      (fun p f => hu.rder p.1 p.2 f) l φ
    rw [e, Pi.mul_apply, hu.real g hg, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)

theorem CompFun.cusp (hu : CompFun V u) {φ : GA D V → ℂ} (h : IsCuspFun V φ) : IsCuspFun V (u * φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  have : (fun n : NI V C => (u * φ) ((n : GA D V) * g)) = fun n : NI V C => u g * φ ((n : GA D V) * g) :=
    funext fun n => congrArg (· * φ ((n : GA D V) * g)) (hu.unip hC n.2 g)
  rw [this, integral_const_mul, h r C hC μ 𝓕 hμ h𝓕 g, mul_zero]

variable {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}

theorem CompFun.multMap (hu : CompFun V u) (hJ : ∀ k ∈ J, ∀ g, u (g * k) = u g) {T : MMap M} (h : IsMultMap θ M J χ T) :
    IsMultMap θ M J χ (postOn M (LinearMap.mulLeft ℂ u) T) := by
  refine ⟨fun v => hu.aut (h.aut v), fun v => hu.cusp (h.cusp v), fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · show u (g * k) * T v (g * k) = χ k * (u g * T v g)
    rw [hJ k hk, h.lev v k hk, mul_left_comm]
  · funext x
    show u x * T _ x = u (x * atTau θ V τ g) * T v (x * atTau θ V τ g)
    rw [h.equiv τ g hg v w hw, hu.real _ (atTau_mem_real τ g)]
    rfl
  · obtain ⟨ℓ, s, e⟩ := h.cont τ v x
    exact ⟨u x • ℓ, GlobalTheory.MultMem.sobCont_smul _ s, fun w => by rw [LinearMap.smul_apply, e]; rfl⟩

theorem ipM_phase (hn : ∀ h, ‖u h‖ = 1) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) :
    ipM M μ 𝓕 (postOn M (LinearMap.mulLeft ℂ u) T) (postOn M (LinearMap.mulLeft ℂ u) T') = ipM M μ 𝓕 T T' := by
  have e : ∀ v v' g, star (postOn M (LinearMap.mulLeft ℂ u) T v g) * postOn M (LinearMap.mulLeft ℂ u) T' v' g =
      star (T v g) * T' v' g := fun v v' g => by
    show star (u g * T v g) * (u g * T' v' g) = _
    have : star (u g) * u g = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hn]; simp
    rw [star_mul']
    linear_combination (star (T v g) * T' v' g) * this
  have : IsMultIP M μ 𝓕 (postOn M (LinearMap.mulLeft ℂ u) T) (postOn M (LinearMap.mulLeft ℂ u) T') = IsMultIP M μ 𝓕 T T' := by
    funext c
    simp only [IsMultIP, e]
  unfold ipM
  rw [this]

end Phase

theorem exists_unitary {X : Type} [AddCommGroup X] [Module ℂ X] (H : HMod X) {U : Submodule ℂ X} {ip : X → X → ℂ}
    (hH : H.Is U ip) (L : X →ₗ[ℂ] X) (hL : ∀ x ∈ U, L x ∈ U) (hip : ∀ x y, ip (L x) (L y) = ip x y) :
    ∃ W : H.H ≃ₗᵢ[ℂ] H.H, ∀ y, H.e (W y) = L (H.e y) := by
  obtain ⟨h1, rfl, h3⟩ := hH
  let f : H.H →ₗ[ℂ] H.H := (LinearEquiv.ofInjective H.e h1).symm.toLinearMap ∘ₗ
    (L ∘ₗ H.e).codRestrict (LinearMap.range H.e) fun y => hL _ ⟨y, rfl⟩
  have hf : ∀ y, H.e (f y) = L (H.e y) := fun y =>
    congrArg Subtype.val ((LinearEquiv.ofInjective H.e h1).apply_symm_apply ⟨L (H.e y), hL _ ⟨y, rfl⟩⟩)
  exact ⟨(f.isometryOfInner fun x y => by rw [h3, h3, hf, hf, hip]).toLinearIsometryEquiv rfl, hf⟩

theorem compFun_of_level (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {u : GA D V → ℂ}
    (h1 : ∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) (h2 : ∀ g ∈ GinfC V, ∀ h, u (h * g) = u h)
    (h3 : ∀ k ∈ Lev.levG V β L, ∀ h, u (h * k) = u h) : CompFun V u := by
  refine ⟨h1, h2, _, GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L, fun k hk g => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have e : Lev.finE V (a * b) = Lev.finE V b := by
    have : finHom V a = 1 := ha
    rw [map_mul, Lev.finE, MonoidHom.comp_apply, this, map_one, one_mul]
  rw [← mul_assoc, h3 b ⟨hb, (e ▸ hk : Lev.finE V b ∈ lev D.sp.cm V.gram β L)⟩, h2 a ha]

end GlobalTheory.CompPhase

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
