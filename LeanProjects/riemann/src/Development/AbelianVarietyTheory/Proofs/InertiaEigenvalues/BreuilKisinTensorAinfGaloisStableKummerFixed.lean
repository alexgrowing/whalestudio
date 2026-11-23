import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.StableFix

theorem SemiBC.span_eq {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) :
    Submodule.span B (Set.range u) = ⊤ := by
  have h1 : (Submodule.span B (Set.range u)).mkQ = 0 := h.hom_ext fun x => by
    rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨x, rfl⟩
  exact Submodule.eq_top_iff'.2 fun y => by
    have := LinearMap.congr_fun h1 y
    rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem kappa_act {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (s : GQ l) (g : G) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, TWact (galOW O s) T g (kappa T y) =
      kappa T (TensorProduct.map (galW l s).toLinearMap (actZ T g) y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem kappa_smul' {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w' x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (P : PhiMod O K l e a ι)

theorem inclO_smul_mem_MA (r : OA l O) {v : ι → OW l O} (hv : v ∈ MA P) : inclO l O r • v ∈ MA P := by
  obtain ⟨c, rfl⟩ := hv
  exact ⟨r • c, funext fun i => (map_mul (inclO l O) r (c i))⟩

theorem inclO_smul_mem_LA (r : OA l O) {v : ι → OW l O} (hv : v ∈ LA t ϖ P) : inclO l O r • v ∈ LA t ϖ P := by
  obtain ⟨c, rfl⟩ := hv
  refine ⟨r • c, ?_⟩
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul (inclO l O) r (c i))

abbrev eb (i : ι) : ι → OW l O := fun j => if i = j then 1 else 0

theorem phiW_eb (i : ι) : phiW t ϖ P (eb i) = frobMat t ϖ P *ᵥ eb i := by
  rw [phiW_apply]
  congr 1
  funext j
  show frobOW l O (if i = j then 1 else 0) = if i = j then 1 else 0
  split_ifs <;> simp

theorem phiW_inclV (c : ι → OA l O) : phiW t ϖ P (inclV l O ι c) = inclL t ϖ P (fun i => frobOA l O (c i)) := by
  rw [phiW_apply, inclL_apply]
  congr 1
  funext j
  exact frobOW_inclO (c j)

def mb (i : ι) : Vec K a ι := fun _ j => if i = j then 1 else 0

theorem mb_mem (i : ι) : (mb i : Vec K a ι) ∈ P.M :=
  mem_tot.2 fun τ j => by
    change (if i = j then (1 : K⟦X⟧) else 0) ∈ A O K
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem toW_mb (i : ι) : toW t ϖ P ⟨mb i, mem_ME_of_mem_M (mb_mem P i)⟩ = eb i := by
  funext j
  rw [toW_apply]
  show _ = (if i = j then (1 : OW l O) else 0)
  split_ifs with h
  · convert map_one (ϖ.iW t K) using 2
    funext τ
    apply Subtype.ext
    simp [mb, h]
  · convert map_zero (ϖ.iW t K) using 2
    funext τ
    apply Subtype.ext
    simp [mb, h]

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem add_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T))
      (z z' : E.M (ainfObj (ϖ.field a))) (v v' : ι → OW l O), I.j v = kappa T (j z) → I.j v' = kappa T (j z') →
      I.j (v + v') = kappa T (j (z + z')) := by
  letI := zlLat T
  intro j z z' v v' hv hw
  rw [I.j.map_add, hv, hw, j.map_add, (kappa T).map_add]

theorem smul_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T))
      (c : (ainfObj (ϖ.field a)).A) (z : E.M (ainfObj (ϖ.field a))) (v : ι → OW l O), I.j v = kappa T (j z) →
      I.j (inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfId (ϖ.field a) c) • v) = kappa T (j (c • z)) := by
  letI := zlLat T
  intro j c z v hv
  have e1 : j (c • z) = inclW l (ainfId (ϖ.field a) c) • j z := j.map_smulₛₗ c z
  rw [e1, kappa_smul', LinearEquiv.map_smul, hv, inclO_tmul]

theorem span_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
      (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (j (E.tr (ϖ.toAinf a) x))) ↔
        ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) →
      ∀ z : E.M (ainfObj (ϖ.field a)), ∃ v ∈ MA P, I.j v = kappa T (j z) := by
  letI := zlLat T
  intro j hE z
  have hz : z ∈ Submodule.span (ainfObj (ϖ.field a)).A (Set.range (E.tr (ϖ.toAinf a))) := by
    rw [SemiBC.span_eq (E.tr_bc (ϖ.toAinf a))]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, rfl⟩ := hz
    obtain ⟨m', hm', h'⟩ := (hE (kappa T (j (E.tr (ϖ.toAinf a) y)))).1 ⟨y, rfl⟩
    exact ⟨_, toW_mem_MA t ϖ P hm', h'.symm⟩
  | zero => exact ⟨0, zero_mem _, by rw [I.j.map_zero, j.map_zero, (kappa T).map_zero]⟩
  | add z z' _ _ h h' =>
    obtain ⟨v, hv, hv'⟩ := h
    obtain ⟨v', hw, hw'⟩ := h'
    exact ⟨v + v', add_mem hv hw, add_step I E j z z' v v' hv' hw'⟩
  | smul c z _ h =>
    obtain ⟨v, hv, hv'⟩ := h
    exact ⟨_, inclO_smul_mem_MA P _ hv, smul_step I E j c z v hv'⟩

theorem core {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (hI : IsBK I)
    (g : ↥(GK (ϖ.field a))) (m : Vec K a ι) (hm : m ∈ P.M) :
    I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) ∈ MA P ∧
      ((g : GQ l) ∈ ϖ.GfieldInf a →
        I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) = toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := by
  letI := zlLat T
  obtain ⟨E, j, H, hE⟩ := hI
  obtain ⟨x, hx⟩ := (hE (I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩))).2 ⟨m, hm, rfl⟩
  have hact : I.j (I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) =
      kappa T (j (E.tr (ainfHom (ϖ.field a) g) (E.tr (ϖ.toAinf a) x))) := by
    rw [Ident.j_act, hx, kappa_act]
    exact congrArg (kappa T) (H.j_act g _).symm
  refine ⟨?_, fun hg => I.j.injective ?_⟩
  · obtain ⟨v, hv, hv'⟩ := span_step I E j hE (E.tr (ainfHom (ϖ.field a) g) (E.tr (ϖ.toAinf a) x))
    rw [← hact, I.j.injective.eq_iff] at hv'
    exact hv' ▸ hv
  · have h1 : (ainfHom (ϖ.field a) g).comp (ϖ.toAinf a) = ϖ.toAinf a :=
      Hom.ext' (RingHom.ext fun y => PiSys.gal_ev l a ϖ hg y)
    rw [hact, ← E.tr_comp, h1, ← hx]

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PhiMod O K l e a ι} {T : Lat a O K ϖ}

theorem act_eb_mem (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) (i : ι) :
    I.act (g : GQ l) g (eb i) ∈ MA P := by
  rw [← toW_mb P i]
  exact (core I hI g _ (mb_mem P i)).1

theorem act_MA (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) :
    ∀ v ∈ MA P, I.act (g : GQ l) g v ∈ MA P := by
  rintro _ ⟨c, rfl⟩
  rw [pi_eq_sum_univ (inclV l O ι c), map_sum]
  refine sum_mem fun i _ => ?_
  rw [Ident.act_smul]
  change galOW O (g : GQ l) (inclO l O (c i)) • _ ∈ _
  rw [galOW_inclO]
  exact inclO_smul_mem_MA P _ (act_eb_mem I hI g i)

theorem act_LA (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) :
    ∀ v ∈ LA t ϖ P, I.act (g : GQ l) g v ∈ LA t ϖ P := by
  rintro _ ⟨c, rfl⟩
  have h1 : inclL t ϖ P c = ∑ i, inclO l O (c i) • phiW t ϖ P (eb i) := by
    rw [inclL_apply]
    conv_lhs => rw [pi_eq_sum_univ (fun i => inclO l O (c i)), Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, phiW_eb]
  rw [h1, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Ident.act_smul, galOW_inclO, Ident.act_phiW]
  refine inclO_smul_mem_LA P _ ?_
  obtain ⟨d, hd⟩ := act_eb_mem I hI g i
  rw [← hd, phiW_inclV]
  exact ⟨_, rfl⟩

theorem act_fix (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) (hg : (g : GQ l) ∈ ϖ.GfieldInf a)
    (v : ME P) : I.act (g : GQ l) g (toW t ϖ P v) = toW t ϖ P v := by
  conv_lhs => rw [pi_eq_sum_univ (toW t ϖ P v), map_sum]
  conv_rhs => rw [pi_eq_sum_univ (toW t ϖ P v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ident.act_smul, toW_apply, ϖ.galOW_iW t K hg]
  congr 1
  have h := (core I hI g _ (mb_mem P i)).2 hg
  rw [toW_mb P i] at h
  exact h

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) ∧ ∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I hBK
  refine ⟨fun g => ⟨act_LA _ hBK g, act_MA _ hBK g⟩, fun g hg v => ?_⟩
  exact act_fix (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) hBK
    ⟨sQ l g, PiSys.fixing_fieldInf_le a ϖ hg⟩ hg v

end GlobalTheory.BKGal.StableFix
