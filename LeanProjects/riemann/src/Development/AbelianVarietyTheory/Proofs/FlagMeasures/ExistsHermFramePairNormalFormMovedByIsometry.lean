import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.DegMove

section Gen

variable {G R M : Type*} [Group G] [Ring R] [AddCommGroup M] [Module R M] [DistribMulAction G M]
  [SMulCommClass G R M]

theorem mem_iff (s : G) (A : Submodule R M) (x : M) : s • x ∈ s • A ↔ x ∈ A := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, hb, h⟩
    rwa [← MulAction.injective s h]
  · intro h; exact ⟨x, h, rfl⟩

theorem ext_smul (s : G) {A B : Submodule R M} (h : ∀ x, s • x ∈ A ↔ x ∈ B) : A = s • B := by
  ext y
  obtain ⟨x, rfl⟩ := MulAction.surjective s y
  rw [mem_iff, h]

theorem smul_inf (s : G) (A B : Submodule R M) : s • A ⊓ s • B = s • (A ⊓ B) :=
  ext_smul s fun x => by simp only [Submodule.mem_inf, mem_iff]

theorem smul_sup (s : G) (A B : Submodule R M) : s • A ⊔ s • B = s • (A ⊔ B) :=
  (Submodule.smul_sup' s A B).symm

theorem smul_iSup {ι : Sort*} (s : G) (A : ι → Submodule R M) : ⨆ i, s • A i = s • ⨆ i, A i := by
  simp only [Submodule.pointwise_smul_def, Submodule.map_iSup]

theorem smul_prod (s : G) (A B : Submodule R M) : (s • A).prod (s • B) = s • A.prod B :=
  ext_smul s fun x => by simp only [Submodule.mem_prod, Prod.smul_fst, Prod.smul_snd, mem_iff]

theorem relIndex_smul (s : G) (A B : Submodule R M) :
    (s • A).toAddSubgroup.relIndex (s • B).toAddSubgroup = A.toAddSubgroup.relIndex B.toAddSubgroup := by
  simp only [Submodule.pointwise_smul_def, Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (MulAction.injective s)

end Gen

section Lat

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}

omit [StarRing K] in
theorem memR (s : V ≃ₗ[K] V) (A : Submodule R V) (x : V) : s x ∈ s • A ↔ x ∈ A := mem_iff s A x

omit [StarRing K] in
theorem memK (s : V ≃ₗ[K] V) (A : Submodule K V) (x : V) : s x ∈ s • A ↔ x ∈ A := mem_iff s A x

omit [StarRing K] in
theorem rs_smul (s : V ≃ₗ[K] V) (S : Submodule K V) : rs R (s • S) = s • rs R S :=
  ext_smul s fun x => memK s S x

theorem perp_smul (hs : s ∈ isomGrp H) (S : Submodule K V) : perp H (s • S) = s • perp H S := by
  refine ext_smul s fun x => ?_
  rw [mem_perp_iff, mem_perp_iff, s.surjective.forall]
  refine forall_congr' fun y => ?_
  rw [memK, LinearEquiv.smul_def, (mem_isomGrp H s).1 hs]

omit [StarRing K] in
theorem smulLat_smul (s : V ≃ₗ[K] V) (g : R) (A : Submodule R V) : smulLat g (s • A) = s • smulLat g A := by
  unfold smulLat
  simp only [Submodule.pointwise_smul_def, ← Submodule.map_comp]
  congr 1
  ext x
  simp [LinearEquiv.smul_def]

omit [StarRing K] in
theorem span_smul (s : V ≃ₗ[K] V) (A : Submodule R V) :
    Submodule.span K ((s • A : Submodule R V) : Set V) = s • Submodule.span K (A : Set V) := by
  rw [Submodule.smul_span]
  rfl

theorem dual_smul (hs : s ∈ isomGrp H) (A : Submodule R V) : dual H (s • A) = s • dual H A := by
  refine ext_smul s fun x => ?_
  rw [mem_dual_iff, mem_dual_iff, span_smul, mem_iff, s.surjective.forall]
  refine and_congr_right fun _ => forall_congr' fun y => ?_
  rw [memR, LinearEquiv.smul_def, (mem_isomGrp H s).1 hs]

theorem isUnimod_smul (hs : s ∈ isomGrp H) (A : Submodule R V) : IsUnimod H (s • A) ↔ IsUnimod H A := by
  have key : ∀ (t : V ≃ₗ[K] V) (B : Submodule R V), t ∈ isomGrp H → IsUnimod H B → IsUnimod H (t • B) := by
    rintro t B ht ⟨⟨⟨N, hN, hB⟩, hsp⟩, hd⟩
    refine ⟨⟨⟨t • N, hN.map _, ?_⟩, ?_⟩, by rw [dual_smul ht, hd]⟩
    · rw [hB]; simp
    · rw [span_smul, hsp]
      exact (ext_smul t fun x => by simp).symm
  refine ⟨fun h => ?_, key s A hs⟩
  simpa using key s⁻¹ _ ((isomGrp H).inv_mem hs) h

def mv (hs : s ∈ isomGrp H) (F : FlagD H r) : FlagD H r where
  e a := s (F.e a)
  T := F.T
  indep := F.indep.map' (s : V →ₗ[K] V) s.ker
  iso a b := by rw [(mem_isomGrp H s).1 hs, F.iso]
  zperp a := by rw [(mem_isomGrp H s).1 hs, F.zperp]
  zz := by rw [(mem_isomGrp H s).1 hs, F.zz]
  hT := F.hT

variable (hs : s ∈ isomGrp H) (F F' : FlagD H r)

theorem mv_e (a : Fin (r + 1)) : (mv hs F).e a = s (F.e a) := rfl

theorem move_z : (mv hs F).z = s F.z := rfl

theorem mv_Xa (a : ℕ) : (mv hs F).Xa a = s • F.Xa a := by
  unfold FlagD.Xa
  rw [Submodule.smul_span, ← Set.image_smul, Set.image_image]
  rfl

theorem mv_X : (mv hs F).X = s • F.X := mv_Xa hs F r

theorem isotropicFrameMapIsometry_pairComplement : V0 (mv hs F) (mv hs F') = s • V0 F F' := by
  unfold V0
  rw [mv_X, mv_X, ← smul_sup, ← smul_sup, Submodule.smul_span, ← Set.image_smul, Set.image_pair]
  rfl

theorem mv_latL (Λ : Submodule R V) : latL (mv hs F) (mv hs F') (s • Λ) = s • latL F F' Λ := by
  simp only [latL, uPerp, mv_X, smul_sup, perp_smul hs, rs_smul, smul_inf]

theorem flagPairDefinitePartLattice_isometry (Λ : Submodule R V) : flagPairDefinitePartLattice (mv hs F) (mv hs F') (s • Λ) = s • flagPairDefinitePartLattice F F' Λ := by
  simp only [flagPairDefinitePartLattice, wSp, mv_latL, isotropicFrameMapIsometry_pairComplement, perp_smul hs, rs_smul, smul_inf]

theorem mv_iotaGraph (Λ : Submodule R V) (g : R) :
    iotaGraph (mv hs F) (mv hs F') (s • Λ) g = s • iotaGraph F F' Λ g := by
  have hc : ∀ A : Submodule R V, (s • A).comap (LinearMap.snd R V V - LinearMap.fst R V V) =
      s • A.comap (LinearMap.snd R V V - LinearMap.fst R V V) := fun A =>
    ext_smul s fun x => by
      simp only [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.snd_apply, LinearMap.fst_apply,
        Prod.smul_fst, Prod.smul_snd, ← smul_sub, mem_iff]
  simp only [iotaGraph, flagPairDefinitePartLattice_isometry, mv_X, rs_smul, smulLat_smul, smul_prod, smul_inf, smul_sup, hc]

theorem mv_latLa (Λ : Submodule R V) (g : R) : latLa (mv hs F) (mv hs F') (s • Λ) g = s • latLa F F' Λ g := by
  unfold latLa fixLat
  rw [mv_iotaGraph]
  exact ext_smul s fun x => mem_iff s (iotaGraph F F' Λ g) (x, x)

theorem mv_lead (Λ : Submodule R V) (a : Fin (r + 1)) : lead (mv hs F) (s • Λ) a = lead F Λ a := by
  unfold lead
  rw [mv_Xa, rs_smul, smul_sup]
  ext t
  simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply, mv_e,
    ← map_smul, memR]

theorem mv_isAdm (Λ : Submodule R V) (g : R) : IsAdm (mv hs F) (mv hs F') (s • Λ) g ↔ IsAdm F F' Λ g := by
  unfold IsAdm
  refine forall_congr' fun a => forall_congr' fun t => ?_
  rw [s.surjective.forall]
  refine forall_congr' fun x' => ?_
  rw [s.surjective.exists]
  simp only [mv_e, mv_Xa, smulLat_smul, ← map_smul, ← map_sub, memR, memK]

theorem mv_Dl (l : ℕ) (h : l ≤ r + 1) : Dl (mv hs F) (mv hs F') l h = Dl F F' l h := by
  unfold Dl Zhat
  simp only [mv_e, (mem_isomGrp H s).1 hs]

theorem mv_posDef (σ : K →+* ℂ) (h : F.PosDefAt σ) : (mv hs F).PosDefAt σ := by
  intro w
  obtain ⟨w, rfl⟩ := s.surjective w
  simp only [mv_e, mv_X, memK, (mem_isomGrp H s).1 hs]
  exact h w

theorem mv_inN (n : V ≃ₗ[K] V) :
    (mv hs F).InN ((MulAut.conj s n : V ≃ₗ[K] V) : V →ₗ[K] V) ↔ F.InN (n : V →ₗ[K] V) := by
  have e : ∀ x, ((MulAut.conj s n : V ≃ₗ[K] V) : V →ₗ[K] V) (s x) = s ((n : V →ₗ[K] V) x) := fun x => by
    simp
  unfold FlagD.InN
  refine and_congr ?_ (and_congr (iff_of_true (LinearEquiv.bijective _) (LinearEquiv.bijective _))
    (and_congr ?_ ?_))
  · rw [s.surjective.forall₂]
    simp only [e, (mem_isomGrp H s).1 hs]
  · simp only [mv_e, e, mv_Xa, ← map_sub, memK]
  · rw [s.surjective.forall]
    simp only [mv_e, e, mv_X, ← map_sub, memK, (mem_isomGrp H s).1 hs]

end Lat

section Form

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}

omit [NumberField K] [StarRing K] in
theorem line_smul (s : V ≃ₗ[K] V) (A : Submodule (𝓞 K) K) (v : V) : line A (s v) = s • line A v := by
  unfold line
  simp only [Submodule.pointwise_smul_def, ← Submodule.map_comp]
  congr 1
  ext x
  simp [LinearEquiv.smul_def]

def mvN (hs : s ∈ isomGrp H) (N : NF H r) : NF H r where
  F := mv hs N.F
  F' := mv hs N.F'
  j := N.j
  j_le := N.j_le
  c := N.c
  c_norm := N.c_norm
  T := N.T
  hT := N.hT
  hT' := N.hT'
  same a ha := by rw [mv_e, mv_e, N.same a ha, map_smul]
  w := N.w
  sgn := N.sgn
  pair a b := by rw [mv_e, mv_e, (mem_isomGrp H s).1 hs, N.pair]
  ist b := s (N.ist b)
  ist_e a b hb := by rw [mv_e, (mem_isomGrp H s).1 hs, N.ist_e a b hb]
  ist_e' a b ha hb := by rw [mv_e, (mem_isomGrp H s).1 hs, N.ist_e' a b ha hb]
  normalForm_dual_orthogonal_last b hb := by rw [move_z, (mem_isomGrp H s).1 hs, N.normalForm_dual_orthogonal_last b hb]
  ist_iso a b ha hb := by rw [(mem_isomGrp H s).1 hs, N.ist_iso a b ha hb]
  posdef σ := mv_posDef hs N.F σ (N.posdef σ)
  𝔡 := N.𝔡
  𝔡_ne := N.𝔡_ne
  𝔡_star := N.𝔡_star

variable (hs : s ∈ isomGrp H) (N : NF H r)

theorem mvN_Ist : (mvN hs N).Ist = s • N.Ist := by
  unfold NF.Ist
  rw [Submodule.smul_span, ← Set.image_smul, Set.image_image]
  rfl

theorem mvN_Wn : (mvN hs N).Wn = s • N.Wn := by
  unfold NF.Wn
  rw [mvN_Ist, ← perp_smul hs, ← smul_sup, ← smul_sup, ← mv_X hs, ← mv_X hs]
  rfl

theorem isotropicNormalFormMapIsometry_baseLattice : (mvN hs N).P0 = s • N.P0 := by
  unfold NF.P0
  simp only [← smul_sup, ← smul_iSup, ← line_smul]
  rfl

theorem mvN_Ref (L : Submodule (𝓞 K) V) : (mvN hs N).Ref (s • L) = s • N.Ref L := by
  unfold NF.Ref
  rw [isotropicNormalFormMapIsometry_baseLattice, mvN_Wn, rs_smul, smul_inf, smul_sup]

theorem mvN_R : (mvN hs N).R = N.R.map (MulAut.conj s).toMonoidHom := by
  unfold NF.R
  rw [MonoidHom.map_closure]
  congr 1
  ext n
  obtain ⟨n, rfl⟩ := (MulAut.conj s).surjective n
  refine Iff.trans ?_ (Function.Injective.mem_set_image (MulAut.conj s).injective).symm
  exact and_congr (mv_inN hs N.F n) (mv_inN hs N.F' n)

theorem mvN_Gam (L : Submodule (𝓞 K) V) :
    (mvN hs N).Gam (s • L) = (N.Gam L).map (MulAut.conj s).toMonoidHom := by
  unfold NF.Gam
  rw [mvN_R, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj s).injective]

theorem mvN_om (Λ : Submodule (𝓞 K) V) : (mvN hs N).om (s • Λ) = N.om Λ := by
  unfold NF.om GlobalTheory.HL.invVol
  have e : latL (mvN hs N).F (mvN hs N).F' (s • Λ) = s • latL N.F N.F' Λ := mv_latL hs _ _ Λ
  rw [e, mvN_Ref, mvN_Gam, mvN_Gam, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj s).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj s).injective]

theorem mvN_isTerm (g : ℕ) (Λ : Submodule (𝓞 K) V) : (mvN hs N).IsTerm g (s • Λ) ↔ N.IsTerm g Λ := by
  refine and_congr (and_congr (isUnimod_smul hs Λ) ?_) (mv_isAdm hs N.F N.F' Λ _)
  change IsFrame (mv hs N.F) _ N.aa ∧ IsFrame (mv hs N.F') _ N.aa ↔ _
  simp only [IsFrame, mv_lead]

theorem mvN_gI (g : ℕ) (Λ : Submodule (𝓞 K) V) : (mvN hs N).gI g (s • Λ) = N.gI g Λ := by
  change idx (flagPairDefinitePartLattice (mv hs N.F) (mv hs N.F') _) (latLa (mv hs N.F) (mv hs N.F') _ _) = _
  rw [flagPairDefinitePartLattice_isometry, mv_latLa]
  exact relIndex_smul s _ _

theorem mvN_nD (l : ℕ) : (mvN hs N).nD l = N.nD l := by
  unfold NF.nD
  change (if h : l ≤ r + 1 then |((Algebra.norm ℚ (Dl (mv hs N.F) (mv hs N.F') l h) : ℚ) : ℝ)| * _ else 0) = _
  simp only [mv_Dl]
  rfl

end Form

theorem exists_moved : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (s : V ≃ₗ[K] V), s ∈ isomGrp H → ∃ N' : NF H r, (∀ a, N'.F.e a = s (N.F.e a) ∧ N'.F'.e a = s (N.F'.e a)) ∧ N'.j = N.j ∧ N'.c = N.c ∧ N'.T = N.T ∧ N'.𝔡 = N.𝔡 ∧ (∀ l, N'.nD l = N.nD l) ∧ ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), N'.om (s • Λ) = N.om Λ ∧ (N'.IsTerm g (s • Λ) ↔ N.IsTerm g Λ) ∧ N'.gI g (s • Λ) = N.gI g Λ := by
  intro K V _ _ _ _ _ _ _ _ H _ r N s hs
  exact ⟨mvN hs N, fun _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, mvN_nD hs N,
    fun g Λ => ⟨mvN_om hs N Λ, mvN_isTerm hs N g Λ, mvN_gI hs N g Λ⟩⟩

end GlobalTheory.DegMove
