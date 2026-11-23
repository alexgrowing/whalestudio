import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w w'

section Grading

theorem isInternal_of_proj {R : Type*} {A : Type*} {ι : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [DecidableEq ι]     (p : ι → Submodule R A) (π : ι → A →ₗ[R] A) (h1 : ∀ i a, a ∈ p i → π i a = a)
    (h2 : ∀ i j a, i ≠ j → a ∈ p j → π i a = 0) (h3 : ⨆ i, p i = ⊤) : DirectSum.IsInternal p := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, h3⟩
  rw [Submodule.disjoint_def]
  intro a ha ha'
  have hle : (⨆ (j) (_ : j ≠ i), p j) ≤ LinearMap.ker (π i) :=
    iSup_le fun j => iSup_le fun hj b hb => h2 i j b (Ne.symm hj) hb
  rw [← h1 i a ha]
  exact hle ha'

variable {S : Type u} [CommRing S] {N : ℕ}

theorem eq_zero_or_isHomogeneous_of_mem_piece {p : Poly S N} {e : ℤ}
    (hp : p ∈ (polyGraded S N).piece e) : p = 0 ∨ ∃ n : ℕ, (n : ℤ) = e ∧ p.IsHomogeneous n := by
  classical
  change p ∈ weightedHomogeneousSubmodule S _ e at hp
  rw [mem_weightedHomogeneousSubmodule] at hp
  by_cases h0 : p = 0
  · exact Or.inl h0
  right
  have key : ∀ s : Fin (N + 1) →₀ ℕ, Finsupp.weight (fun _ => (1 : ℤ)) s =
      ((Finsupp.weight (1 : Fin (N + 1) → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]
    push_cast
    exact Finset.sum_congr rfl fun _ _ => nsmul_one _
  obtain ⟨s0, hs0⟩ := ne_zero_iff.mp h0
  refine ⟨Finsupp.weight (1 : Fin (N + 1) → ℕ) s0, by rw [← key, hp hs0], fun s hs => ?_⟩
  have := (hp hs).trans (hp hs0).symm
  rw [key, key] at this
  exact_mod_cast this

variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

omit [IsScalarTower S (Poly S N) M] in

theorem GradedPMod.smul_mem_int (𝓜 : GradedPMod S N M) {p : Poly S N} {e a : ℤ} {m : M}
    (hp : p ∈ (polyGraded S N).piece e) (hm : m ∈ 𝓜.piece a) : p • m ∈ 𝓜.piece (a + e) := by
  rcases eq_zero_or_isHomogeneous_of_mem_piece hp with rfl | ⟨n, rfl, hn⟩
  · rw [zero_smul]; exact zero_mem _
  · exact 𝓜.smul_mem n a p m hn hm

def GradedPMod.transport (𝓜 : GradedPMod S N M) (e : M ≃ₗ[Poly S N] M') : GradedPMod S N M' where
  piece c := (𝓜.piece c).map ((e.restrictScalars S : M ≃ₗ[S] M') : M →ₗ[S] M')
  isInternal := by
    have hi := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp 𝓜.isInternal
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨hi.1.map_orderIso (Submodule.orderIsoMapComap (e.restrictScalars S)), ?_⟩
    rw [← Submodule.map_iSup, hi.2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (e.restrictScalars S).surjective
  smul_mem d c p m hp hm := by
    obtain ⟨m0, hm0, rfl⟩ := hm
    exact ⟨p • m0, 𝓜.smul_mem d c p m0 hp hm0, by simp⟩

def GradedPMod.toTransport (𝓜 : GradedPMod S N M) (e : M ≃ₗ[Poly S N] M') :
    GradedHom 𝓜 (𝓜.transport e) where
  toLin := e.toLinearMap
  map_piece _ m hm := ⟨m, hm, rfl⟩

def GradedPMod.ofTransport (𝓜 : GradedPMod S N M) (e : M ≃ₗ[Poly S N] M') :
    GradedHom (𝓜.transport e) 𝓜 where
  toLin := e.symm.toLinearMap
  map_piece _ m hm := by
    obtain ⟨m0, hm0, rfl⟩ := hm
    simpa using hm0

end Grading

section Free

variable {S : Type u} [CommRing S] {N : ℕ}

variable (S N) in

def freeGraded {r : ℕ} (deg : Fin r → ℤ) : GradedPMod S N (Fin r → Poly S N) where
  piece c := Submodule.pi Set.univ fun j => (polyGraded S N).piece (c - deg j)
  isInternal := by
    classical
    refine isInternal_of_proj _ (fun c => LinearMap.pi fun j =>
      (weightedHomogeneousComponent (fun _ : Fin (N + 1) => (1 : ℤ)) (c - deg j)).comp
        (LinearMap.proj j)) ?_ ?_ ?_
    · intro c f hf
      funext j
      have hj : f j ∈ (polyGraded S N).piece (c - deg j) := (Submodule.mem_pi.mp hf) j (Set.mem_univ _)
      change weightedHomogeneousComponent _ (c - deg j) (f j) = f j
      rw [weightedHomogeneousComponent_of_mem hj, if_pos rfl]
    · intro c c' f hcc' hf
      funext j
      have hj : f j ∈ (polyGraded S N).piece (c' - deg j) := (Submodule.mem_pi.mp hf) j (Set.mem_univ _)
      change weightedHomogeneousComponent _ (c - deg j) (f j) = 0
      rw [weightedHomogeneousComponent_of_mem hj, if_neg (by omega)]
    · rw [eq_top_iff]
      rintro f -
      rw [← Finset.univ_sum_single f]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hall : f j ∈ ⨆ e, (polyGraded S N).piece e := by
        rw [((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
          (polyGraded S N).isInternal).2]
        trivial
      have hmap : Pi.single j (f j) ∈
          (⨆ e, (polyGraded S N).piece e).map (LinearMap.single S (fun _ => Poly S N) j) :=
        ⟨f j, hall, rfl⟩
      rw [Submodule.map_iSup] at hmap
      have hsub : ∀ e, ((polyGraded S N).piece e).map (LinearMap.single S (fun _ => Poly S N) j) ≤
          Submodule.pi Set.univ fun j' => (polyGraded S N).piece (e + deg j - deg j') := by
        intro e
        rintro _ ⟨p, hp, rfl⟩
        rw [Submodule.mem_pi]
        intro j' _
        by_cases h : j' = j
        · subst h
          rw [LinearMap.single_apply, Pi.single_eq_same, add_sub_cancel_right]
          exact hp
        · rw [LinearMap.single_apply, Pi.single_eq_of_ne h]
          exact zero_mem _
      have hle : (⨆ e, ((polyGraded S N).piece e).map (LinearMap.single S (fun _ => Poly S N) j)) ≤
          ⨆ c, Submodule.pi Set.univ fun j' => (polyGraded S N).piece (c - deg j') :=
        iSup_mono' fun e => ⟨e + deg j, hsub e⟩
      exact hle hmap
  smul_mem e c p f hp hf := by
    rw [Submodule.mem_pi] at hf ⊢
    intro j _
    have := (polyGraded S N).smul_mem e (c - deg j) p (f j) hp (hf j (Set.mem_univ _))
    rw [show c + (e : ℤ) - deg j = c - deg j + e by ring]
    exact this

theorem single_one_mem_freeGraded {r : ℕ} (deg : Fin r → ℤ) (j : Fin r) :
    (Pi.single j 1 : Fin r → Poly S N) ∈ (freeGraded S N deg).piece (deg j) := by
  classical
  change _ ∈ Submodule.pi _ _
  rw [Submodule.mem_pi]
  intro j' _
  by_cases h : j' = j
  · subst h
    rw [Pi.single_eq_same, sub_self]
    change (1 : Poly S N) ∈ weightedHomogeneousSubmodule S _ _
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one _ _
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

variable (S N) in

def freeMap {r : ℕ} (g : Fin r → M) : (Fin r → Poly S N) →ₗ[Poly S N] M :=
  ∑ j, (LinearMap.proj j).smulRight (g j)

omit [Module S M] [IsScalarTower S (Poly S N) M] in
theorem freeMap_apply {r : ℕ} (g : Fin r → M) (f : Fin r → Poly S N) :
    freeMap S N g f = ∑ j, f j • g j := by
  simp [freeMap]

omit [IsScalarTower S (Poly S N) M] in

theorem GradedPMod.exists_gens (𝓜 : GradedPMod S N M) (hM : Module.Finite (Poly S N) M) :
    ∃ (r : ℕ) (g : Fin r → M) (deg : Fin r → ℤ), (∀ j, g j ∈ 𝓜.piece (deg j)) ∧
      Submodule.span (Poly S N) (Set.range g) = ⊤ := by
  classical
  let _ := 𝓜.isInternal.chooseDecomposition
  obtain ⟨s, hs⟩ := hM.fg_top
  let J := Σ m : s, ((DirectSum.decompose 𝓜.piece (m : M)).support : Finset ℤ)
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j => (DirectSum.decompose 𝓜.piece ((e.symm j).1 : M) (e.symm j).2 : M),
    fun j => ((e.symm j).2 : ℤ), fun j => (DirectSum.decompose 𝓜.piece _ _).2, ?_⟩
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro m hm
  rw [← DirectSum.sum_support_decompose 𝓜.piece m]
  refine Submodule.sum_mem _ fun c hc => Submodule.subset_span ⟨e ⟨⟨m, hm⟩, ⟨c, hc⟩⟩, ?_⟩
  dsimp only
  rw [Equiv.symm_apply_apply]

omit [IsScalarTower S (Poly S N) M] in
theorem freeMap_mem {r : ℕ} (𝓜 : GradedPMod S N M) {g : Fin r → M} {deg : Fin r → ℤ}
    (hg : ∀ j, g j ∈ 𝓜.piece (deg j)) (c : ℤ) {f : Fin r → Poly S N}
    (hf : f ∈ (freeGraded S N deg).piece c) : freeMap S N g f ∈ 𝓜.piece c := by
  rw [freeMap_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : f j ∈ (polyGraded S N).piece (c - deg j) := (Submodule.mem_pi.mp hf) j (Set.mem_univ _)
  have := 𝓜.smul_mem_int hj (hg j)
  rwa [add_sub_cancel] at this

omit [Module S M] [IsScalarTower S (Poly S N) M] in
theorem freeMap_surjective {r : ℕ} {g : Fin r → M} (hg : Submodule.span (Poly S N) (Set.range g) = ⊤) :
    Function.Surjective (freeMap S N g) := by
  classical
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine ⟨Pi.single j 1, ?_⟩
  rw [freeMap_apply, Finset.sum_eq_single j (fun j' _ h => by rw [Pi.single_eq_of_ne h, zero_smul])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]

end Free

section Kernel

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable {𝓕 : GradedPMod S N M} {𝓜 : GradedPMod S N M'}

omit [IsScalarTower S (Poly S N) M] [IsScalarTower S (Poly S N) M'] in

theorem GradedHom.map_decompose (φ : GradedHom 𝓕 𝓜) [DirectSum.Decomposition 𝓕.piece]
    [DirectSum.Decomposition 𝓜.piece] (c : ℤ) (m : M) :
    φ.toLin (DirectSum.decompose 𝓕.piece m c : M) = (DirectSum.decompose 𝓜.piece (φ.toLin m) c : M') := by
  classical
  induction m using DirectSum.Decomposition.inductionOn 𝓕.piece with
  | zero => simp
  | @homogeneous i m =>
    by_cases h : i = c
    · subst h
      rw [DirectSum.decompose_of_mem_same _ m.2, DirectSum.decompose_of_mem_same _ (φ.map_piece _ _ m.2)]
    · rw [DirectSum.decompose_of_mem_ne _ m.2 h, DirectSum.decompose_of_mem_ne _ (φ.map_piece _ _ m.2) h,
        map_zero]
  | add m m' hm hm' =>
    simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, hm, hm']

def GradedHom.kerGraded (φ : GradedHom 𝓕 𝓜) : GradedPMod S N (LinearMap.ker φ.toLin) where
  piece c := (𝓕.piece c).comap ((LinearMap.ker φ.toLin).subtype.restrictScalars S)
  isInternal := by
    classical
    let _ := 𝓕.isInternal.chooseDecomposition
    let _ := 𝓜.isInternal.chooseDecomposition
    have hker : ∀ (c : ℤ) (k : LinearMap.ker φ.toLin),
        (DirectSum.decompose 𝓕.piece (k : M) c : M) ∈ LinearMap.ker φ.toLin := by
      intro c k
      rw [LinearMap.mem_ker, φ.map_decompose, LinearMap.mem_ker.mp k.2, DirectSum.decompose_zero]
      rfl
    let π : ℤ → LinearMap.ker φ.toLin →ₗ[S] LinearMap.ker φ.toLin := fun c =>
      { toFun := fun k => ⟨_, hker c k⟩
        map_add' := fun a b => by
          apply Subtype.ext
          simp [DirectSum.decompose_add]
        map_smul' := fun s a => by
          apply Subtype.ext
          simp [DirectSum.decompose_smul, DirectSum.smul_apply] }
    refine isInternal_of_proj _ π ?_ ?_ ?_
    · intro c k hk
      exact Subtype.ext (DirectSum.decompose_of_mem_same _ hk)
    · intro c c' k hcc' hk
      exact Subtype.ext (DirectSum.decompose_of_mem_ne _ hk (Ne.symm hcc'))
    · rw [eq_top_iff]
      rintro k -
      have hk : k = ∑ c ∈ (DirectSum.decompose 𝓕.piece (k : M)).support, π c k := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact (DirectSum.sum_support_decompose 𝓕.piece (k : M)).symm
      rw [hk]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (DirectSum.decompose 𝓕.piece (k : M) c).2
  smul_mem d c p k hp hk := 𝓕.smul_mem d c p k hp hk

def GradedHom.kerIncl (φ : GradedHom 𝓕 𝓜) : GradedHom φ.kerGraded 𝓕 where
  toLin := (LinearMap.ker φ.toLin).subtype
  map_piece _ _ hk := hk

end Kernel

section Cohom

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem cohomMap_toH0 {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜') (c : ℤ)
    (m : 𝓜.piece c) : cohomMap f 0 c (toH0 𝓜 c m) = toH0 𝓜' c ⟨f.toLin m, f.map_piece c m m.2⟩ := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  funext I
  change locMap f.toLin I.1.1 (LocalizedModule.mk (m : M) 1) = LocalizedModule.mk (f.toLin m) 1
  exact locMap_mk _ _ _ _

theorem cohomMap_leftInverse {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜')
    (g : GradedHom 𝓜' 𝓜) (hfg : ∀ m, g.toLin (f.toLin m) = m) (i : ℕ) (c : ℤ) (y : cohom 𝓜 i c) :
    cohomMap g i c (cohomMap f i c y) = y := by
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ y
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  funext I
  change locMap g.toLin I.1.1 (locMap f.toLin I.1.1 ((s : Cech.Cochain (locSys S N M) i) I)) =
    (s : Cech.Cochain (locSys S N M) i) I
  generalize ((s : Cech.Cochain (locSys S N M) i) I) = z
  induction z using LocalizedModule.induction_on with
  | h m t => rw [locMap_mk, locMap_mk, hfg]

end Cohom

section Main

theorem toH0_surjective_of_exact (hC : CechExact.Statement.{u, w}) {S : Type u} [CommRing S]
    [IsNoetherianRing S] {N : ℕ} {K F M : Type w}
    [AddCommGroup K] [Module (Poly S N) K] [Module S K] [IsScalarTower S (Poly S N) K]
    [AddCommGroup F] [Module (Poly S N) F] [Module S F] [IsScalarTower S (Poly S N) F]
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    {𝓚 : GradedPMod S N K} {𝓕 : GradedPMod S N F} {𝓜 : GradedPMod S N M}
    (ι : GradedHom 𝓚 𝓕) (φ : GradedHom 𝓕 𝓜) (hι : Function.Injective ι.toLin)
    (hφ : Function.Surjective φ.toLin) (hex : Function.Exact ι.toLin φ.toLin) (c : ℤ)
    (hF : Function.Surjective (toH0 𝓕 c)) (hK : Subsingleton (cohom 𝓚 1 c)) :
    Function.Surjective (toH0 𝓜 c) := by
  obtain ⟨-, h⟩ := hC S N K F M 𝓚 𝓕 𝓜 ι φ hι hφ hex c
  obtain ⟨-, δ, hδ, -⟩ := h 0
  intro y
  obtain ⟨z, hz⟩ := (hδ y).mp (Subsingleton.elim _ _)
  obtain ⟨f, rfl⟩ := hF z
  exact ⟨⟨φ.toLin f, φ.map_piece c f f.2⟩, by rw [← cohomMap_toH0, hz]⟩

theorem SerreOnto.proof (hC : CechExact.Statement.{u, max u v})
    (hF : SerreFree.Statement.{u, max u v}) (hV : SerreVanish.Statement.{u, max u v}) :
    SerreOnto.Statement.{u, v} := by
  intro S _ _ N M _ _ _ _ 𝓜 hM
  obtain ⟨r, g, deg, hg, hspan⟩ := 𝓜.exists_gens hM

  let eM : M ≃ₗ[Poly S N] ULift.{u} M := ULift.moduleEquiv.symm
  let eF : (Fin r → Poly S N) ≃ₗ[Poly S N] ULift.{v} (Fin r → Poly S N) := ULift.moduleEquiv.symm
  let 𝓜L := 𝓜.transport eM
  let 𝓕 := (freeGraded S N deg).transport eF
  let φ : GradedHom 𝓕 𝓜L :=
    { toLin := eM.toLinearMap ∘ₗ freeMap S N g ∘ₗ eF.symm.toLinearMap
      map_piece := by
        rintro c _ ⟨f, hf, rfl⟩
        exact ⟨freeMap S N g f, freeMap_mem 𝓜 hg c hf, by simp [eF]⟩ }
  have hφ : Function.Surjective φ.toLin := by
    change Function.Surjective (⇑eM.toLinearMap ∘ ⇑(freeMap S N g) ∘ ⇑eF.symm.toLinearMap)
    exact eM.surjective.comp ((freeMap_surjective hspan).comp eF.symm.surjective)

  have hKfin : Module.Finite (Poly S N) (LinearMap.ker φ.toLin) := by
    have : Module.Finite (Poly S N) (ULift.{v} (Fin r → Poly S N)) := Module.Finite.equiv eF
    have : IsNoetherian (Poly S N) (ULift.{v} (Fin r → Poly S N)) :=
      isNoetherian_of_isNoetherianRing_of_finite _ _
    infer_instance
  obtain ⟨c₁, hc₁⟩ := hV S N _ φ.kerGraded hKfin

  let b : Module.Basis (Fin r) (Poly S N) (ULift.{v} (Fin r → Poly S N)) :=
    (Pi.basisFun (Poly S N) (Fin r)).map eF
  have hb : ∀ j, b j ∈ 𝓕.piece (deg j) := fun j =>
    ⟨Pi.single j 1, single_one_mem_freeGraded deg j, by simp [b, eF]⟩
  have hFc := (hF S N _ 𝓕 r b deg hb).2
  refine ⟨max c₁ (∑ j, |deg j|), fun c hc => ?_⟩
  have hcd : ∀ j, deg j ≤ c := fun j => (le_abs_self _).trans
    ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans
      ((le_max_right _ _).trans hc))
  have hsurjL : Function.Surjective (toH0 𝓜L c) :=
    toH0_surjective_of_exact hC φ.kerIncl φ (LinearMap.ker φ.toLin).injective_subtype hφ
      (LinearMap.exact_subtype_ker_map _) c (hFc c hcd).2.surjective
      (hc₁ 1 le_rfl c ((le_max_left _ _).trans hc))

  intro y
  obtain ⟨z, hz⟩ := hsurjL (cohomMap (𝓜.toTransport eM) 0 c y)
  refine ⟨⟨(𝓜.ofTransport eM).toLin z, (𝓜.ofTransport eM).map_piece c z z.2⟩, ?_⟩
  rw [← cohomMap_toH0 (𝓜.ofTransport eM), hz, cohomMap_leftInverse]
  intro m
  simp [GradedPMod.toTransport, GradedPMod.ofTransport]

end Main

end

end GroundTheory.Heights₂.Heights.Kleiman
