import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic

open Module
noncomputable section
namespace Formalism.HermitianLatticesTheory

section
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

omit [IsFractionRing R K] in
theorem finitely_generated_projective_coords (L : Submodule R V) (hL : L.FG) (hK : Function.Injective (algebraMap R K)) :
    ∃ (n : ℕ) (g : Fin n → L) (f : Fin n → (L →ₗ[R] R)), ∀ y : L, y = ∑ i, f i y • g i := by
  classical
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  haveI : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  have htor : Submodule.torsion R L = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have ha' : (algebraMap R K (a : R)) • (x : V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val ha
    have hne : algebraMap R K (a : R) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap R K)]
      exact fun h0 => nonZeroDivisors.ne_zero a.2 (hK h0)
    exact Subtype.ext ((smul_eq_zero.mp ha').resolve_left hne)
  haveI : Module.Flat R L := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htor
  haveI : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R L
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨n, fun i => π (Pi.single i 1), fun i => (LinearMap.proj i) ∘ₗ σ, fun y => ?_⟩
  have e1 : π (σ y) = y := LinearMap.congr_fun hσ y
  have e2 : σ y = ∑ i, σ y i • (Pi.single i (1 : R) : Fin n → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← e1, e2]
  simp [map_sum, map_smul]

theorem dualLattice_basis [FiniteDimensional K V] (L : Submodule R V)
    (hsp : Submodule.span K (L : Set V) = ⊤) :
    ∃ (s : Set V) (_ : Fintype s) (b : Basis s K V), (∀ i, b i = (i : V)) ∧ s ⊆ L := by
  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent K (L : Set V)
  have hfin : s.Finite := hli.setFinite
  refine ⟨s, hfin.fintype, Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp]), fun i => ?_, hsL⟩
  simp

theorem dualLattice_denom {ι : Type*} [Fintype ι] (b : Basis ι K V) (L : Submodule R V)
    (hL : L.FG) : ∃ d : R, d ≠ 0 ∧ ∀ y ∈ L, d • y ∈ Submodule.span R (Set.range b) := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (Finset.image (fun p : V × ι => b.repr p.1 p.2) (S ×ˢ Finset.univ))
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  have key : ∀ v ∈ S, d • v ∈ Submodule.span R (Set.range b) := by
    intro v hv
    rw [← b.sum_repr v, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, hr⟩ := hint (b.repr v i) (Finset.mem_image.mpr ⟨(v, i), by simp [hv], rfl⟩)
    have hr' : algebraMap R K r = d • b.repr v i := hr
    rw [← smul_assoc, ← hr', algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)
  have hle : Submodule.span R (S : Set V) ≤
      (Submodule.span R (Set.range b)).comap (d • LinearMap.id : V →ₗ[R] V) := by
    rw [Submodule.span_le]
    intro v hv
    simpa using key v hv
  intro y hy
  rw [← hS] at hy
  simpa using hle hy

variable [StarRing K]

theorem dualLattice_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hnd : h.Nondegenerate) (b : Basis ι K V) :
    ∃ bs : ι → V, ∀ i j, h (b i) (bs j) = if i = j then 1 else 0 := by
  classical
  haveI := Module.Finite.of_basis b
  let T : V →ₗ[K] (ι → K) := LinearMap.pi fun i => h (b i)
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∀ i, h (b i) x = 0 := fun i => congrFun hx i
    have hflip : h.flip x = 0 := b.ext fun i => by simp [h0 i]
    exact hnd.2 x fun y => by simpa using LinearMap.congr_fun hflip y
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Module.finrank_eq_card_basis b])).mp hinj
  choose bs hbs using fun j => hsurj (Pi.single j 1)
  refine ⟨bs, fun i j => ?_⟩
  have := congrFun (hbs j) i
  simpa [T, Pi.single_apply] using this

theorem dualLattice_expand {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hnd : h.Nondegenerate) (b : Basis ι K V) (bs : ι → V)
    (hbs : ∀ i j, h (b i) (bs j) = if i = j then 1 else 0) (x : V) :
    x = ∑ j, h (b j) x • bs j := by
  classical
  set z := x - ∑ j, h (b j) x • bs j with hzdef
  have hz : ∀ i, h (b i) z = 0 := by
    intro i
    simp [z, map_sub, map_sum, map_smul, hbs, smul_eq_mul]
  have hflip : h.flip z = 0 := b.ext fun i => by simp [hz i]
  have hz0 : z = 0 := hnd.2 z fun y => by simpa using LinearMap.congr_fun hflip y
  exact sub_eq_zero.mp hz0

theorem dualLattice_repr {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (b : Basis ι K V) (bs : ι → V)
    (hbs : ∀ i j, h (b i) (bs j) = if i = j then 1 else 0) (L : Submodule R V)
    (hb : ∀ i, b i ∈ L) (d : R) (hd : d ≠ 0)
    (hdL : ∀ y ∈ L, d • y ∈ Submodule.span R (Set.range b)) (f : L →ₗ[R] R) :
    ∃ w : V, ∀ y (hy : y ∈ L), h w y = algebraMap R K (f ⟨y, hy⟩) := by
  classical
  let w : V := ∑ j, star (algebraMap R K (f ⟨b j, hb j⟩)) • bs j
  have hsym : ∀ i j, h (bs j) (b i) = if i = j then 1 else 0 := by
    intro i j
    rw [← hs.eq (b i) (bs j), hbs]
    split_ifs <;> simp
  have hwb : ∀ i, h w (b i) = algebraMap R K (f ⟨b i, hb i⟩) := by
    intro i
    simp [w, map_sum, LinearMap.map_smulₛₗ₂, hsym, starRingEnd_apply, star_star, Algebra.smul_def]
  have hspL : Submodule.span R (Set.range b) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hspan : ∀ z ∈ Submodule.span R (Set.range b), ∀ hz : z ∈ L,
      h w z = algebraMap R K (f ⟨z, hz⟩) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro _
      exact hwb i
    | zero =>
      intro hz
      have e : (⟨0, hz⟩ : L) = 0 := rfl
      rw [e, map_zero, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro hxy
      have e : (⟨x + y, hxy⟩ : L) = ⟨x, hspL hx⟩ + ⟨y, hspL hy⟩ := rfl
      rw [e, map_add, map_add, map_add, ihx (hspL hx), ihy (hspL hy)]
    | smul r x hx ih =>
      intro hrx
      have e1 : h w (r • x) = algebraMap R K r * h w x := by
        rw [← algebraMap_smul K r x, LinearMap.map_smul, smul_eq_mul]
      have e2 : (⟨r • x, hrx⟩ : L) = r • ⟨x, hspL hx⟩ := rfl
      rw [e1, e2, map_smul, smul_eq_mul, map_mul, ih (hspL hx)]
  refine ⟨w, fun y hy => ?_⟩
  have h1 := hspan _ (hdL y hy) (L.smul_mem d hy)
  have e1 : h w (d • y) = algebraMap R K d * h w y := by
    rw [← algebraMap_smul K d y, LinearMap.map_smul, smul_eq_mul]
  have e2 : (⟨d • y, L.smul_mem d hy⟩ : L) = d • ⟨y, hy⟩ := rfl
  rw [e1, e2, map_smul, smul_eq_mul, map_mul] at h1
  have hne : algebraMap R K d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K)]
    exact fun h0 => hd (IsFractionRing.injective R K h0)
  exact mul_left_cancel₀ hne h1

end

theorem dualLattice : DualLattice := by
  intro R K V _ _ _ _ _ _ _ _ _ _ _ h hs hnd hst L hL
  classical
  have mem_dual : ∀ (M : Submodule R V) (x : V),
      x ∈ dual h M ↔ ∀ y ∈ M, ∃ r : R, algebraMap R K r = h y x := by
    intro M x
    simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]
  have hLfg := hL.fg
  have hLsp := hL.span_eq_top
  obtain ⟨s, hfs, b, hbi, hsL⟩ := dualLattice_basis (R := R) L hLsp
  have hbL : ∀ i, b i ∈ L := fun i => hsL (by rw [hbi]; exact i.2)
  obtain ⟨bs, hbs⟩ := dualLattice_dualBasis h hnd b
  obtain ⟨d, hd0, hdL⟩ := dualLattice_denom b L hLfg
  have hexp := dualLattice_expand h hnd b bs hbs
  have hdK : algebraMap R K d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K)]
    exact fun h0 => hd0 (IsFractionRing.injective R K h0)

  have hA : ∀ z ∈ Submodule.span R (Set.range b), ∀ j, ∃ r : R, algebraMap R K r = h z (bs j) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro j
      refine ⟨if i = j then 1 else 0, ?_⟩
      rw [hbs]
      split_ifs <;> simp
    | zero => intro j; exact ⟨0, by simp⟩
    | add x y _ _ ihx ihy =>
      intro j
      obtain ⟨r1, hr1⟩ := ihx j
      obtain ⟨r2, hr2⟩ := ihy j
      exact ⟨r1 + r2, by rw [map_add, hr1, hr2, map_add, LinearMap.add_apply]⟩
    | smul r x _ ih =>
      intro j
      obtain ⟨r1, hr1⟩ := ih j
      obtain ⟨r', hr'⟩ := hst r
      refine ⟨r' * r1, ?_⟩
      rw [map_mul, hr', hr1, ← algebraMap_smul K r x, LinearMap.map_smulₛₗ₂]
      simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]

  have hle : dual h L ≤ Submodule.span R (Set.range bs) := by
    intro x hx
    rw [hexp x]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := (mem_dual L x).mp hx (b j) (hbL j)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl⟩)
  have hfg : (dual h L).FG :=
    Submodule.FG.of_le (Submodule.fg_span (Set.finite_range bs)) hle

  have hbsK : ∀ j, bs j ∈ Submodule.span K (dual h L : Set V) := by
    intro j
    obtain ⟨d', hd'⟩ := hst d
    have hd'0 : algebraMap R K d' ≠ 0 := by rw [hd']; exact star_ne_zero.mpr hdK
    have hmem : d' • bs j ∈ dual h L := by
      rw [mem_dual]
      intro y hy
      obtain ⟨r, hr⟩ := hA _ (hdL y hy) j
      refine ⟨r, ?_⟩
      have e1 : h y (d' • bs j) = algebraMap R K d' * h y (bs j) := by
        rw [← algebraMap_smul K d' (bs j), LinearMap.map_smul, smul_eq_mul]
      have e2 : h (d • y) (bs j) = star (algebraMap R K d) * h y (bs j) := by
        rw [← algebraMap_smul K d y, LinearMap.map_smulₛₗ₂]
        simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
      rw [hr, e1, e2, hd']
    have e : bs j = (algebraMap R K d')⁻¹ • (d' • bs j) := by
      rw [← algebraMap_smul K d' (bs j), smul_smul, inv_mul_cancel₀ hd'0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hspd : Submodule.span K (dual h L : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [hexp x]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbsK j)
  refine ⟨⟨hfg, hspd⟩, ?_, ?_⟩
  ·
    refine le_antisymm ?_ ((dualBasic R K V h hs hst).2.1 L)
    obtain ⟨n, g, f, hgf⟩ := finitely_generated_projective_coords L hLfg (IsFractionRing.injective R K)
    choose w hw using fun k => dualLattice_repr h hs b bs hbs L hbL d hd0 hdL (f k)
    have hwd : ∀ k, w k ∈ dual h L := by
      intro k
      rw [mem_dual]
      intro y hy
      obtain ⟨r', hr'⟩ := hst (f k ⟨y, hy⟩)
      refine ⟨r', ?_⟩
      rw [hr', ← hs.eq (w k) y, hw k y hy, starRingEnd_apply]
    let Pm : V →ₗ[K] V := ∑ k, (h (w k)).smulRight (g k : V)
    have hP : Pm = LinearMap.id := by
      refine LinearMap.ext_on hLsp ?_
      intro y hy
      have e := congrArg Subtype.val (hgf ⟨y, hy⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      simp only [Pm, LinearMap.sum_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply, hw _ y hy, algebraMap_smul]
      exact e.symm
    intro x hx
    have ex : x = ∑ k, h (w k) x • (g k : V) := by
      have := LinearMap.congr_fun hP x
      simpa [Pm] using this.symm
    rw [ex]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨r, hr⟩ := (mem_dual _ x).mp hx (w k) (hwd k)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (g k).2
  ·
    intro a ha
    have hsa : star a ≠ 0 := star_ne_zero.mpr ha
    ext x
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    constructor
    · intro hx
      refine ⟨star a • x, ?_, by rw [smul_smul, inv_mul_cancel₀ hsa, one_smul]⟩
      rw [mem_dual] at hx ⊢
      intro z hz
      obtain ⟨r, hr⟩ := hx (a • z) ⟨z, hz, rfl⟩
      refine ⟨r, ?_⟩
      rw [hr, LinearMap.map_smulₛₗ₂, LinearMap.map_smul]
      simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
    · rintro ⟨y, hy, rfl⟩
      rw [mem_dual] at hy ⊢
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨r, hr⟩ := hy z hz
      refine ⟨r, ?_⟩
      simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
      rw [hr, LinearMap.map_smulₛₗ₂, LinearMap.map_smul]
      simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hsa, one_mul]

end Formalism.HermitianLatticesTheory
