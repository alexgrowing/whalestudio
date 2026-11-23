import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

namespace E2

section Plain

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (s t : R)

open LinearMap (lsmul)

def Z1 : Submodule R (M × M) := LinearMap.ker ((lsmul R M s).coprod (lsmul R M t))

theorem mem_Z1_iff_cocycle {z : M × M} : z ∈ Z1 s t ↔ s • z.1 + t • z.2 = 0 := by
  simp [Z1]

def bd : M →ₗ[R] Z1 (M := M) s t :=
  ((lsmul R M t).prod (-(lsmul R M s))).codRestrict _ (fun x => by
    rw [mem_Z1_iff_cocycle]; simp [smul_smul, mul_comm s t])

theorem bd_coe (x : M) : ((bd s t x : Z1 (M := M) s t) : M × M) = (t • x, -(s • x)) := rfl

def B1 : Submodule R (Z1 (M := M) s t) := LinearMap.range (bd s t)

def iK : LinearMap.ker (lsmul R M s) →ₗ[R] Z1 (M := M) s t :=
  ((LinearMap.inl R M M).comp (Submodule.subtype _)).codRestrict _ (fun a => by
    rw [mem_Z1_iff_cocycle]
    have ha : s • (a : M) = 0 := LinearMap.mem_ker.1 a.2
    simpa using ha)

theorem iK_coe (a : LinearMap.ker (lsmul R M s)) :
    ((iK s t a : Z1 (M := M) s t) : M × M) = ((a : M), 0) := rfl

def fK : (LinearMap.ker (lsmul R M s) ⧸ LinearMap.range (lsmul R (LinearMap.ker (lsmul R M s)) t))
    →ₗ[R] (Z1 (M := M) s t ⧸ B1 (M := M) s t) :=
  Submodule.mapQ _ _ (iK s t) (by
    rintro _ ⟨a, rfl⟩
    have ha : s • (a : M) = 0 := LinearMap.mem_ker.1 a.2
    refine ⟨(a : M), Subtype.ext ?_⟩
    rw [bd_coe, iK_coe, ha, neg_zero]
    rfl)

def cK : Z1 (M := M) s t →ₗ[R]
    LinearMap.ker (lsmul R (M ⧸ LinearMap.range (lsmul R M s)) t) :=
  ((Submodule.mkQ _).comp ((LinearMap.snd R M M).comp (Submodule.subtype _))).codRestrict _
    (fun z => by
      rw [LinearMap.mem_ker]
      show t • (Submodule.Quotient.mk z.1.2 : M ⧸ LinearMap.range (lsmul R M s)) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨-z.1.1, ?_⟩
      have := (mem_Z1_iff_cocycle s t).1 z.2
      rw [LinearMap.lsmul_apply, smul_neg]
      exact neg_eq_iff_add_eq_zero.2 this)

theorem cK_coe (z : Z1 (M := M) s t) :
    ((cK s t z : LinearMap.ker (lsmul R (M ⧸ LinearMap.range (lsmul R M s)) t)) :
      M ⧸ LinearMap.range (lsmul R M s)) = Submodule.Quotient.mk z.1.2 := rfl

def gK : (Z1 (M := M) s t ⧸ B1 (M := M) s t) →ₗ[R]
    LinearMap.ker (lsmul R (M ⧸ LinearMap.range (lsmul R M s)) t) :=
  Submodule.liftQ _ (cK s t) (by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    refine Subtype.ext ?_
    rw [cK_coe, bd_coe]
    show Submodule.Quotient.mk (-(s • x)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨-x, by simp⟩)

theorem fK_mk (a : LinearMap.ker (lsmul R M s)) :
    fK s t (Submodule.Quotient.mk a) = Submodule.Quotient.mk (iK s t a) := rfl

theorem gK_mk (z : Z1 (M := M) s t) :
    gK s t (Submodule.Quotient.mk z) = cK s t z := rfl

theorem fK_inj : Function.Injective (fK (M := M) s t) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [fK_mk, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, hy⟩ := hx
  have h0 : ((bd s t y : Z1 (M := M) s t) : M × M) = ((a : M), 0) := by rw [hy, iK_coe]
  rw [bd_coe] at h0
  have h1 : t • y = (a : M) := congrArg Prod.fst h0
  have h2 : -(s • y) = 0 := congrArg Prod.snd h0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨⟨y, by simpa using h2⟩, Subtype.ext h1⟩

theorem gK_surj : Function.Surjective (gK (M := M) s t) := by
  rintro ⟨y, hy⟩
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have h1 : t • (Submodule.Quotient.mk b : M ⧸ LinearMap.range (lsmul R M s)) = 0 := hy
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨a, ha⟩ := h1
  have ha' : s • a = t • b := ha
  refine ⟨Submodule.Quotient.mk ⟨(-a, b), ?_⟩, ?_⟩
  · rw [mem_Z1_iff_cocycle]; simp [ha']
  · rw [gK_mk]; exact Subtype.ext rfl

theorem fgK_exact : Function.Exact (fK (M := M) s t) (gK (M := M) s t) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  constructor
  · intro h
    rw [gK_mk] at h
    have h1 : (Submodule.Quotient.mk z.1.2 : M ⧸ LinearMap.range (lsmul R M s)) = 0 := by
      rw [← cK_coe, h]; rfl
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨y0, hy0⟩ := h1
    have hy0' : s • y0 = z.1.2 := hy0
    have hz := (mem_Z1_iff_cocycle s t).1 z.2
    have ha : s • (z.1.1 + t • y0) = 0 := by
      rw [smul_add, smul_comm s t y0, hy0', hz]
    refine ⟨Submodule.Quotient.mk ⟨z.1.1 + t • y0, by simpa using ha⟩, ?_⟩
    rw [fK_mk, Submodule.Quotient.eq]
    refine ⟨y0, Subtype.ext ?_⟩
    rw [bd_coe, Submodule.coe_sub, iK_coe, hy0']
    refine Prod.ext ?_ ?_ <;> simp
  · rintro ⟨x, hx⟩
    rw [← hx]
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [fK_mk, gK_mk]
    refine Subtype.ext ?_
    rw [cK_coe, iK_coe]
    rfl

def swZ : Z1 (M := M) s t ≃ₗ[R] Z1 (M := M) t s :=
  (LinearEquiv.prodComm R M M).ofSubmodules _ _ (by
    ext z
    simp only [Submodule.mem_map, mem_Z1_iff_cocycle]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [add_comm] using hw
    · intro hz
      exact ⟨(z.2, z.1), by simpa [add_comm] using hz, rfl⟩)

theorem swZ_coe (z : Z1 (M := M) s t) :
    ((swZ s t z : Z1 (M := M) t s) : M × M) = (z.1.2, z.1.1) := rfl

def swH : (Z1 (M := M) s t ⧸ B1 (M := M) s t) ≃ₗ[R] (Z1 (M := M) t s ⧸ B1 (M := M) t s) :=
  Submodule.Quotient.equiv _ _ (swZ s t) (by
    ext z
    simp only [Submodule.mem_map, B1, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨-x, Subtype.ext ?_⟩
      show _ = ((swZ s t (bd s t x) : Z1 (M := M) t s) : M × M)
      rw [swZ_coe, bd_coe, bd_coe]
      simp
    · rintro ⟨x, rfl⟩
      refine ⟨_, ⟨-x, rfl⟩, Subtype.ext ?_⟩
      show ((swZ s t (bd s t (-x)) : Z1 (M := M) t s) : M × M) = _
      rw [swZ_coe, bd_coe, bd_coe]
      simp)

theorem swH_mk (z : Z1 (M := M) s t) :
    swH s t (Submodule.Quotient.mk z) = Submodule.Quotient.mk (swZ s t z) := rfl

def qqHom : ((M ⧸ LinearMap.range (lsmul R M s)) ⧸
      LinearMap.range (lsmul R (M ⧸ LinearMap.range (lsmul R M s)) t)) →ₗ[R]
    ((M ⧸ LinearMap.range (lsmul R M t)) ⧸
      LinearMap.range (lsmul R (M ⧸ LinearMap.range (lsmul R M t)) s)) :=
  Submodule.liftQ _ (Submodule.liftQ _ ((Submodule.mkQ _).comp (Submodule.mkQ _)) (by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      show Submodule.Quotient.mk (Submodule.Quotient.mk (s • x)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨Submodule.Quotient.mk x, rfl⟩)) (by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (Submodule.Quotient.mk (t • x)) = 0
    have : (Submodule.Quotient.mk (t • x) : M ⧸ LinearMap.range (lsmul R M t)) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]; exact ⟨x, rfl⟩
    rw [this]; rfl)

theorem qqHom_mk (x : M) :
    qqHom s t (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (Submodule.Quotient.mk x) := rfl

def qqEquiv : ((M ⧸ LinearMap.range (lsmul R M s)) ⧸
      LinearMap.range (lsmul R (M ⧸ LinearMap.range (lsmul R M s)) t)) ≃ₗ[R]
    ((M ⧸ LinearMap.range (lsmul R M t)) ⧸
      LinearMap.range (lsmul R (M ⧸ LinearMap.range (lsmul R M t)) s)) :=
  LinearEquiv.ofLinearMap (qqHom s t) (qqHom t s)
    (by ext x; rfl)
    (by ext x; rfl)

def aaHom : LinearMap.ker (lsmul R (LinearMap.ker (lsmul R M s)) t) →ₗ[R]
    LinearMap.ker (lsmul R (LinearMap.ker (lsmul R M t)) s) :=
  LinearMap.codRestrict _
    (LinearMap.codRestrict _ ((Submodule.subtype _).comp (Submodule.subtype _)) (fun x => by
      rw [LinearMap.mem_ker]
      exact congrArg Subtype.val (LinearMap.mem_ker.1 x.2))) (fun x => by
    rw [LinearMap.mem_ker]
    exact Subtype.ext (LinearMap.mem_ker.1 x.1.2))

theorem aaHom_coe (x : LinearMap.ker (lsmul R (LinearMap.ker (lsmul R M s)) t)) :
    ((aaHom s t x).1.1 : M) = x.1.1 := rfl

def aaEquiv : LinearMap.ker (lsmul R (LinearMap.ker (lsmul R M s)) t) ≃ₗ[R]
    LinearMap.ker (lsmul R (LinearMap.ker (lsmul R M t)) s) :=
  LinearEquiv.ofLinearMap (aaHom s t) (aaHom t s) (by ext x; rfl) (by ext x; rfl)

end Plain

section AlgebraTools

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def IsGrMap {F G : GMod B R k} (φ : F.M →ₗ[R] G.M) : Prop := ∀ m x, x ∈ F.gr m → φ x ∈ G.gr m

def cmp {F : GMod B R k} (h : DirectSum.IsInternal F.gr) (m : Deg k) (x : F.M) : F.M :=
  letI := h.chooseDecomposition
  ((DirectSum.decompose F.gr x) m : F.M)

section
variable {F G : GMod B R k} (h : DirectSum.IsInternal F.gr)
include h

theorem cmp_mem (m : Deg k) (x : F.M) : cmp h m x ∈ F.gr m := SetLike.coe_mem _

theorem cmp_same {m : Deg k} {x : F.M} (hx : x ∈ F.gr m) : cmp h m x = x := by
  let _ := h.chooseDecomposition
  exact DirectSum.decompose_of_mem_same _ hx

theorem cmp_ne {m m' : Deg k} {x : F.M} (hx : x ∈ F.gr m') (hne : m' ≠ m) : cmp h m x = 0 := by
  let _ := h.chooseDecomposition
  exact DirectSum.decompose_of_mem_ne _ hx hne

theorem cmp_zero (m : Deg k) : cmp h m 0 = 0 := cmp_same h (F.gr m).zero_mem

theorem cmp_add (m : Deg k) (x y : F.M) : cmp h m (x + y) = cmp h m x + cmp h m y := by
  let _ := h.chooseDecomposition
  simp [cmp, DirectSum.decompose_add]

theorem mem_of_cmp (S : AddSubmonoid F.M) {x : F.M} (hx : ∀ m, cmp h m x ∈ S) : x ∈ S := by
  classical
  let _ := h.chooseDecomposition
  rw [← DirectSum.sum_support_decompose F.gr x]
  exact sum_mem (fun m _ => hx m)

theorem cmp_map (hG : DirectSum.IsInternal G.gr) (φ : F.M →ₗ[R] G.M) (hφ : IsGrMap φ)
    (m : Deg k) (x : F.M) : cmp hG m (φ x) = φ (cmp h m x) := by
  have hx : x ∈ ⨆ i, F.gr i := h.submodule_iSup_eq_top ▸ Submodule.mem_top
  refine Submodule.iSup_induction F.gr (motive := fun x => cmp hG m (φ x) = φ (cmp h m x)) hx
    ?_ ?_ ?_
  · intro i x hx
    by_cases hi : i = m
    · subst hi
      rw [cmp_same h hx, cmp_same hG (hφ _ _ hx)]
    · rw [cmp_ne h hx hi, cmp_ne hG (hφ _ _ hx) hi, map_zero]
  · rw [map_zero, cmp_zero, cmp_zero, map_zero]
  · intro x y hx hy
    rw [map_add, cmp_add, cmp_add, map_add, hx, hy]

theorem comap_of_inj (hG : DirectSum.IsInternal G.gr) (φ : F.M →ₗ[R] G.M) (hφ : IsGrMap φ)
    (inj : Function.Injective φ) (m : Deg k) :
    F.gr m = (G.gr m).comap (φ.restrictScalars B) := by
  ext x
  constructor
  · exact hφ m x
  · intro hx
    have hx' : φ x ∈ G.gr m := hx
    have : cmp h m x = x := inj (by rw [← cmp_map h hG φ hφ, cmp_same hG hx'])
    rw [← this]
    exact cmp_mem h m x

theorem map_of_surj (hG : DirectSum.IsInternal G.gr) (φ : F.M →ₗ[R] G.M) (hφ : IsGrMap φ)
    (surj : Function.Surjective φ) (m : Deg k) :
    G.gr m = (F.gr m).map (φ.restrictScalars B) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := surj y
    refine ⟨cmp h m x, cmp_mem h m x, ?_⟩
    show φ (cmp h m x) = φ x
    rw [← cmp_map h hG φ hφ, cmp_same hG hy]
  · rintro ⟨x, hx, rfl⟩
    exact hφ m x hx

theorem isHomSub_ker (hG : DirectSum.IsInternal G.gr) (φ : F.M →ₗ[R] G.M) (hφ : IsGrMap φ) :
    F.IsHomSub (LinearMap.ker φ) := by
  refine le_antisymm ?_ (Submodule.span_le.2 fun x hx => hx.1)
  intro x hx
  refine mem_of_cmp h (Submodule.span R _).toAddSubmonoid (fun m => Submodule.subset_span ?_)
  refine ⟨?_, m, cmp_mem h m x⟩
  rw [LinearMap.mem_ker, ← cmp_map h hG φ hφ, LinearMap.mem_ker.1 hx, cmp_zero]

theorem isHomSub_range (φ : F.M →ₗ[R] G.M) (hφ : IsGrMap φ) :
    G.IsHomSub (LinearMap.range φ) := by
  refine le_antisymm ?_ (Submodule.span_le.2 fun x hx => hx.1)
  rintro _ ⟨x, rfl⟩
  refine mem_of_cmp h ((Submodule.span R _).comap φ).toAddSubmonoid
    (fun m => Submodule.subset_span ?_)
  exact ⟨⟨_, rfl⟩, m, hφ _ _ (cmp_mem h m x)⟩

end

def sesOfGr {F' F F'' : GMod B R k} (h' : DirectSum.IsInternal F'.gr)
    (h : DirectSum.IsInternal F.gr) (h'' : DirectSum.IsInternal F''.gr)
    (f : F'.M →ₗ[R] F.M) (g : F.M →ₗ[R] F''.M) (inj : Function.Injective f)
    (surj : Function.Surjective g) (exact : Function.Exact f g)
    (hf : IsGrMap f) (hg : IsGrMap g) : SES F' F F'' where
  f := f
  g := g
  inj := inj
  surj := surj
  exact := exact
  f_gr := comap_of_inj h' h f hf inj
  g_gr := map_of_surj h h'' g hg surj

def isoOfGr {F G : GMod B R k} (h : DirectSum.IsInternal F.gr) (hG : DirectSum.IsInternal G.gr)
    (e : F.M ≃ₗ[R] G.M) (he : IsGrMap e.toLinearMap) : GIso F G where
  e := e
  map_gr m := (map_of_surj h hG e.toLinearMap he e.surjective m).symm

def gprod (F G : GMod B R k) : GMod B R k where
  M := F.M × G.M
  gr m := (F.gr m).prod (G.gr m)

theorem internal_prod' {ι A M M' : Type} [DecidableEq ι] [CommRing A] [AddCommGroup M]
    [AddCommGroup M'] [Module A M] [Module A M'] (P : ι → Submodule A M) (P' : ι → Submodule A M')
    (hP : DirectSum.IsInternal P) (hP' : DirectSum.IsInternal P') :
    DirectSum.IsInternal (fun i => (P i).prod (P' i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv h0 i hi
    have h1 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hP.submodule_iSupIndep s
      (fun i => (v i).1) (fun i hi => (hv i hi).1)
      (by rw [← Prod.fst_sum, h0]; rfl) i hi
    have h2 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hP'.submodule_iSupIndep s
      (fun i => (v i).2) (fun i hi => (hv i hi).2)
      (by rw [← Prod.snd_sum, h0]; rfl) i hi
    exact Prod.ext h1 h2
  · rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have ha : ((a, 0) : M × M') ∈ ⨆ i, (P i).prod (P' i) := by
      have h : a ∈ ⨆ i, P i := hP.submodule_iSup_eq_top ▸ Submodule.mem_top
      refine Submodule.iSup_induction P
        (motive := fun a => ((a, 0) : M × M') ∈ ⨆ i, (P i).prod (P' i)) h ?_ ?_ ?_
      · intro i x hx
        exact Submodule.mem_iSup_of_mem i ⟨hx, zero_mem _⟩
      · exact zero_mem _
      · intro x y hx hy
        have := add_mem hx hy
        simpa using this
    have hb : ((0, b) : M × M') ∈ ⨆ i, (P i).prod (P' i) := by
      have h : b ∈ ⨆ i, P' i := hP'.submodule_iSup_eq_top ▸ Submodule.mem_top
      refine Submodule.iSup_induction P'
        (motive := fun b => ((0, b) : M × M') ∈ ⨆ i, (P i).prod (P' i)) h ?_ ?_ ?_
      · intro i x hx
        exact Submodule.mem_iSup_of_mem i ⟨zero_mem _, hx⟩
      · exact zero_mem _
      · intro x y hx hy
        have := add_mem hx hy
        simpa using this
    have := add_mem ha hb
    simpa using this

theorem internal_prod {F G : GMod B R k} (hF : DirectSum.IsInternal F.gr)
    (hG : DirectSum.IsInternal G.gr) : DirectSum.IsInternal (gprod F G).gr :=
  internal_prod' F.gr G.gr hF hG

theorem isGr_prod (𝒜 : Deg k → Submodule B R) {F G : GMod B R k} (hF : F.IsGr 𝒜) (hG : G.IsGr 𝒜) :
    (gprod F G).IsGr 𝒜 where
  smul_mem := fun ha hx => ⟨hF.smul_mem ha hx.1, hG.smul_mem ha hx.2⟩
  internal := internal_prod hF.internal hG.internal
  fin := by
    have := hF.fin
    have := hG.fin
    exact Module.Finite.prod

theorem secs_perm {ts ts' : List (Deg k × R)} (hp : ts.Perm ts') : secs ts = secs ts' := by
  unfold secs
  congr 1
  ext s
  show (∃ d, (d, s) ∈ ts) ↔ (∃ d, (d, s) ∈ ts')
  simp only [hp.mem_iff]

theorem admissible_tail_of_cons_mem [IsLocalRing B] (𝒜 : Deg k → Submodule B R) {d : Deg k} {s : R}
    {l : List (Deg k × R)} {J J' : Ideal R} (h : admitted 𝒜 ((d, s) :: l) J) (hJ : J ≤ J')
    (hs : s ∈ J') : admitted 𝒜 l J' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le (hJ.trans le_sup_left) ?_)⟩
  rw [secs, Ideal.span_le]
  rintro x ⟨d0, hx⟩
  rcases List.mem_cons.1 hx with h | h
  · have hxs : x = s := (Prod.mk.inj h).2
    rw [hxs]
    exact Ideal.mem_sup_left hs
  · exact Ideal.mem_sup_right (Ideal.subset_span ⟨d0, h⟩)

theorem ann_le_quot (F : GMod B R k) (s : R) : F.Ann ≤ (F.quot s).Ann := by
  intro r hr
  refine Module.mem_annihilator.2 (fun y => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show Submodule.Quotient.mk (r • x) = 0
  rw [Module.mem_annihilator.1 hr x]
  rfl

theorem self_mem_quot (F : GMod B R k) (s : R) : s ∈ (F.quot s).Ann := by
  refine Module.mem_annihilator.2 (fun y => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

theorem ann_le_ann (F : GMod B R k) (s : R) (d : Deg k) : F.Ann ≤ (F.ann s d).Ann := by
  intro r hr
  refine Module.mem_annihilator.2 (fun y => ?_)
  exact Subtype.ext (Module.mem_annihilator.1 hr y.1)

theorem self_mem_ann (F : GMod B R k) (s : R) (d : Deg k) : s ∈ (F.ann s d).Ann := by
  refine Module.mem_annihilator.2 (fun y => ?_)
  exact Subtype.ext (LinearMap.mem_ker.1 y.2)

end AlgebraTools

section Koszul

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def H1 (F : GMod B R k) (s t : R) (d d' : Deg k) : GMod B R k where
  M := Z1 (M := F.M) s t ⧸ B1 (M := F.M) s t
  gr m := (((F.gr (m - d)).prod (F.gr (m - d'))).comap
    ((Z1 (M := F.M) s t).subtype.restrictScalars B)).map
      ((B1 (M := F.M) s t).mkQ.restrictScalars B)

theorem koszul_homology_eq (F : GMod B R k) (s t : R) (d d' : Deg k) :
    H1 F s t d d' = ((gprod (F.shift d) (F.shift d')).sub (Z1 (M := F.M) s t)).quo
      (B1 (M := F.M) s t) := rfl

theorem ann_le_koszul_ann (F : GMod B R k) (s t : R) (d d' : Deg k) : F.Ann ≤ (H1 F s t d d').Ann := by
  intro r hr
  refine Module.mem_annihilator.2 (fun y => ?_)
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hz : r • z = 0 := Subtype.ext (Prod.ext (Module.mem_annihilator.1 hr z.1.1)
    (Module.mem_annihilator.1 hr z.1.2))
  show Submodule.Quotient.mk (r • z) = 0
  rw [hz]
  rfl

theorem fst_mem_koszul_ann (F : GMod B R k) (s t : R) (d d' : Deg k) : s ∈ (H1 F s t d d').Ann := by
  refine Module.mem_annihilator.2 (fun y => ?_)
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨-z.1.2, Subtype.ext ?_⟩
  have hz := (mem_Z1_iff_cocycle s t).1 z.2
  rw [bd_coe]
  refine Prod.ext ?_ ?_
  · show t • (-z.1.2) = s • z.1.1
    rw [smul_neg, neg_eq_iff_add_eq_zero, add_comm]; exact hz
  · show -(s • (-z.1.2)) = s • z.1.2
    rw [smul_neg, neg_neg]

theorem snd_mem_annihilator_H1 (F : GMod B R k) (s t : R) (d d' : Deg k) : t ∈ (H1 F s t d d').Ann := by
  refine Module.mem_annihilator.2 (fun y => ?_)
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨z.1.1, Subtype.ext ?_⟩
  have hz := (mem_Z1_iff_cocycle s t).1 z.2
  rw [bd_coe]
  refine Prod.ext rfl ?_
  show -(s • z.1.1) = t • z.1.2
  rw [neg_eq_iff_add_eq_zero]; exact hz

end Koszul

section Main

variable {k : ℕ}

theorem koszul_homology_isGraded (hGr : RuleGr) (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) {s t : X.R}
    {d d' : Deg k} (hs : s ∈ X.𝒜 d) (ht : t ∈ X.𝒜 d') : (H1 F s t d d').IsGr X.𝒜 := by
  have hsh := (hGr k X F hF).2.1
  have hK : (gprod (F.shift d) (F.shift d')).IsGr X.𝒜 := isGr_prod X.𝒜 (hsh d) (hsh d')
  have hZ : (gprod (F.shift d) (F.shift d')).IsHomSub (Z1 (M := F.M) s t) :=
    isHomSub_ker (F := gprod (F.shift d) (F.shift d')) (G := F) hK.internal hF.internal
      ((LinearMap.lsmul X.R F.M s).coprod (LinearMap.lsmul X.R F.M t)) (by
        rintro m ⟨a, b⟩ ⟨ha, hb⟩
        have h1 : s • a ∈ F.gr (d + (m - d)) := hF.smul_mem hs ha
        have h2 : t • b ∈ F.gr (d' + (m - d')) := hF.smul_mem ht hb
        rw [add_sub_cancel] at h1 h2
        exact add_mem h1 h2)
  have hKZ := ((hGr k X _ hK).1 _ hZ).1
  have hB : ((gprod (F.shift d) (F.shift d')).sub (Z1 (M := F.M) s t)).IsHomSub
      (B1 (M := F.M) s t) :=
    isHomSub_range (F := F.shift (d + d'))
      (G := (gprod (F.shift d) (F.shift d')).sub (Z1 (M := F.M) s t)) (hsh (d + d')).internal
      (bd (M := F.M) s t) (by
        intro m x hx
        have hx' : x ∈ F.gr (m - (d + d')) := hx
        have h1 : t • x ∈ F.gr (d' + (m - (d + d'))) := hF.smul_mem ht hx'
        have h2 : s • x ∈ F.gr (d + (m - (d + d'))) := hF.smul_mem hs hx'
        have e1 : d' + (m - (d + d')) = m - d := by abel
        have e2 : d + (m - (d + d')) = m - d' := by abel
        rw [e1] at h1
        rw [e2] at h2
        exact ⟨h1, neg_mem h2⟩)
  exact ((hGr k X _ hKZ).1 _ hB).2

def sesK (hGr : RuleGr) (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) {s t : X.R}
    {d d' : Deg k} (hs : s ∈ X.𝒜 d) (ht : t ∈ X.𝒜 d') :
    SES ((F.ann s d).quot t) (H1 F s t d d') ((F.quot s).ann t d') :=
  sesOfGr
    ((hGr k X _ ((hGr k X F hF).2.2 d s hs).2).2.2 d' t ht).1.internal
    (koszul_homology_isGraded hGr X F hF hs ht).internal
    ((hGr k X _ ((hGr k X F hF).2.2 d s hs).1).2.2 d' t ht).2.internal
    (fK (M := F.M) s t) (gK (M := F.M) s t) (fK_inj s t) (gK_surj s t) (fgK_exact s t)
    (by
      rintro m _ ⟨a, ha, rfl⟩
      exact ⟨iK s t a, ⟨ha, zero_mem _⟩, rfl⟩)
    (by
      rintro m _ ⟨z, hz, rfl⟩
      exact ⟨z.1.2, hz.2, rfl⟩)

def isoH (hGr : RuleGr) (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) {s t : X.R}
    {d d' : Deg k} (hs : s ∈ X.𝒜 d) (ht : t ∈ X.𝒜 d') :
    GIso (H1 F s t d d') (H1 F t s d' d) :=
  isoOfGr (koszul_homology_isGraded hGr X F hF hs ht).internal (koszul_homology_isGraded hGr X F hF ht hs).internal
    (swH (M := F.M) s t) (by
      rintro m _ ⟨z, hz, rfl⟩
      exact ⟨swZ s t z, ⟨hz.2, hz.1⟩, rfl⟩)

def isoQQ (hGr : RuleGr) (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) {s t : X.R}
    {d d' : Deg k} (hs : s ∈ X.𝒜 d) (ht : t ∈ X.𝒜 d') :
    GIso ((F.quot s).quot t) ((F.quot t).quot s) :=
  isoOfGr
    ((hGr k X _ ((hGr k X F hF).2.2 d s hs).1).2.2 d' t ht).1.internal
    ((hGr k X _ ((hGr k X F hF).2.2 d' t ht).1).2.2 d s hs).1.internal
    (qqEquiv (M := F.M) s t) (by
      rintro m _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩)

def isoAA (hGr : RuleGr) (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) {s t : X.R}
    {d d' : Deg k} (hs : s ∈ X.𝒜 d) (ht : t ∈ X.𝒜 d') :
    GIso ((F.ann s d).ann t d') ((F.ann t d').ann s d) :=
  isoOfGr
    ((hGr k X _ ((hGr k X F hF).2.2 d s hs).2).2.2 d' t ht).2.internal
    ((hGr k X _ ((hGr k X F hF).2.2 d' t ht).2).2.2 d s hs).2.internal
    (aaEquiv (M := F.M) s t) (by
      intro m x hx
      have hx' : x.1.1 ∈ F.gr (m - d' - d) := hx
      rw [sub_right_comm] at hx'
      exact hx')

theorem swap_eq (hGr : RuleGr) (hIso : RuleIso) (hE1 : EulerAdditivityExactSequence) (X : HidaSetting k)
    (l : List (Deg k × X.R)) (F : X.Mod) (hF : F.IsGr X.𝒜) {s t : X.R} {d d' : Deg k}
    (hs : s ∈ X.𝒜 d) (ht : t ∈ X.𝒜 d') (hl : Valid X.𝒜 l)
    (hA : admitted X.𝒜 ((d, s) :: (d', t) :: l) F.Ann) :
    ∀ᶠ m in atTop, chi ((d, s) :: (d', t) :: l) F m = chi ((d', t) :: (d, s) :: l) F m := by
  have hA1 : admitted X.𝒜 l (H1 F s t d d').Ann :=
    admissible_tail_of_cons_mem X.𝒜 (admissible_tail_of_cons_mem X.𝒜 hA (ann_le_koszul_ann F s t d d') (fst_mem_koszul_ann F s t d d')) le_rfl
      (snd_mem_annihilator_H1 F s t d d')
  have hA2 : admitted X.𝒜 l (H1 F t s d' d).Ann :=
    admissible_tail_of_cons_mem X.𝒜 (admissible_tail_of_cons_mem X.𝒜 hA (ann_le_koszul_ann F t s d' d) (snd_mem_annihilator_H1 F t s d' d)) le_rfl
      (fst_mem_koszul_ann F t s d' d)
  have e1 := hE1 k X l _ _ _ hl
    ((hGr k X _ ((hGr k X F hF).2.2 d s hs).2).2.2 d' t ht).1
    (koszul_homology_isGraded hGr X F hF hs ht)
    ((hGr k X _ ((hGr k X F hF).2.2 d s hs).1).2.2 d' t ht).2
    (sesK hGr X F hF hs ht) hA1
  have e2 := hE1 k X l _ _ _ hl
    ((hGr k X _ ((hGr k X F hF).2.2 d' t ht).2).2.2 d s hs).1
    (koszul_homology_isGraded hGr X F hF ht hs)
    ((hGr k X _ ((hGr k X F hF).2.2 d' t ht).1).2.2 d s hs).2
    (sesK hGr X F hF ht hs) hA2
  filter_upwards [e1, e2] with m h1 h2
  have i1 := hIso k X l _ _ (isoH hGr X F hF hs ht) m
  have i2 := hIso k X l _ _ (isoQQ hGr X F hF hs ht) m
  have i3 := hIso k X l _ _ (isoAA hGr X F hF hs ht) m
  simp only [chi]
  linarith

end Main

end E2

section Main

open E2

theorem euler_rule_two_of_graded_finite_iso : RuleGr → RuleFin → RuleIso → EulerAdditivityExactSequence → EulerIndependenceOfOrder := by
  intro hGr _ hIso hE1 k X ts ts' F hV hp
  induction hp generalizing F with
  | nil => intro _ _; exact Eventually.of_forall (fun _ => rfl)
  | cons x hp ih =>
    obtain ⟨d, s⟩ := x
    intro hF hA
    have hs : s ∈ X.𝒜 d := (hV (d, s) (List.mem_cons_self ..)).2
    have hl : Valid X.𝒜 _ := fun p hp' => hV p (List.mem_cons_of_mem _ hp')
    have hq := (hGr k X F hF).2.2 d s hs
    have e1 := ih (F.quot s) hl hq.1 (admissible_tail_of_cons_mem X.𝒜 hA (ann_le_quot F s) (self_mem_quot F s))
    have e2 := ih (F.ann s d) hl hq.2 (admissible_tail_of_cons_mem X.𝒜 hA (ann_le_ann F s d) (self_mem_ann F s d))
    filter_upwards [e1, e2] with m h1 h2
    simp only [chi, h1, h2]
  | swap x y l =>
    obtain ⟨d', t⟩ := x
    obtain ⟨d, s⟩ := y
    intro hF hA
    have hs : s ∈ X.𝒜 d := (hV (d, s) (List.mem_cons_self ..)).2
    have ht : t ∈ X.𝒜 d' := (hV (d', t) (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2
    have hl : Valid X.𝒜 l :=
      fun p hp' => hV p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp'))
    exact swap_eq hGr hIso hE1 X l F hF hs ht hl hA
  | @trans l₁ l₂ l₃ hp1 hp2 ih1 ih2 =>
    intro hF hA
    have hV2 : Valid X.𝒜 l₂ := fun p hp' => hV p (hp1.mem_iff.2 hp')
    have hA2 : admitted X.𝒜 l₂ F.Ann := by
      obtain ⟨N, hN⟩ := hA
      exact ⟨N, by rw [← secs_perm hp1]; exact hN⟩
    filter_upwards [ih1 F hV hF hA, ih2 F hV2 hF hA2] with m h1 h2
    rw [h1, h2]

end Main

end Formalism.MainNotions.V.Pf.V2.Calc
