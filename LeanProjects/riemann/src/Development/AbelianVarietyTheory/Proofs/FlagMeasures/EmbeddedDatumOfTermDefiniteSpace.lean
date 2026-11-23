import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLiftEmbeddedDatumOfTermStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.DatEmb

open GlobalTheory.Mass

section Lin
variable {K V W C : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup C] [Module K C]

theorem exists_equiv (X : Submodule K V) (e : W →ₗ[K] V) (c : C →ₗ[K] V) (he : ∀ w, e w ∈ X → w = 0)
    (hc : ∀ y, c y ∈ X → y = 0) (h1 : ∀ w, ∃ y, e w - c y ∈ X) (h2 : ∀ y, ∃ w, e w - c y ∈ X) :
    ∃ φ : W ≃ₗ[K] C, ∀ w, e w - c (φ w) ∈ X := by
  let q := X.mkQ
  have ie : Function.Injective (q ∘ₗ e) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact he w ((Submodule.Quotient.mk_eq_zero X).1 hw)
  have ic : Function.Injective (q ∘ₗ c) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hc y ((Submodule.Quotient.mk_eq_zero X).1 hy)
  have hr : LinearMap.range (q ∘ₗ e) = LinearMap.range (q ∘ₗ c) := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      obtain ⟨y, hy⟩ := h1 w
      exact ⟨y, ((Submodule.Quotient.eq X).2 hy).symm⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨w, hw⟩ := h2 y
      exact ⟨w, (Submodule.Quotient.eq X).2 hw⟩
  refine ⟨(LinearEquiv.ofInjective _ ie).trans
    ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective _ ic).symm), fun w => ?_⟩
  have key := congrArg Subtype.val ((LinearEquiv.ofInjective _ ic).apply_symm_apply
    (LinearEquiv.ofEq _ _ hr (LinearEquiv.ofInjective _ ie w)))
  simp only [LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply] at key
  exact (Submodule.Quotient.eq X).1 key.symm

end Lin

variable {K W C : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W]
  [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] [AddCommGroup C] [Module K C]
  [Module (𝓞 K) C] [IsScalarTower (𝓞 K) K C]

abbrev pre (φ : W ≃ₗ[K] C) (M : Submodule (𝓞 K) C) : Submodule (𝓞 K) W :=
  M.comap ((φ : W →ₗ[K] C).restrictScalars (𝓞 K))

omit [NumberField K] [StarRing K] in
theorem pre_eq_map (φ : W ≃ₗ[K] C) (M : Submodule (𝓞 K) C) :
    pre φ M = M.map ((φ.symm : C →ₗ[K] W).restrictScalars (𝓞 K)) := by
  ext y
  simp only [pre, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe]
  constructor
  · intro h
    exact ⟨φ y, h, φ.symm_apply_apply y⟩
  · rintro ⟨m, hm, rfl⟩
    simpa using hm

omit [NumberField K] [StarRing K] in
theorem idxN_pre (φ : W ≃ₗ[K] C) (A B : Submodule (𝓞 K) C) : idxN (pre φ A) (pre φ B) = idxN A B := by
  rw [pre_eq_map, pre_eq_map]
  unfold idxN
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (fun a b h => φ.symm.injective h)

omit [NumberField K] [StarRing K] in
theorem isLattice_pre (φ : W ≃ₗ[K] C) {M : Submodule (𝓞 K) C} (h : Submodule.IsLattice K M) :
    Submodule.IsLattice K (pre φ M) := by
  rw [pre_eq_map]
  refine ⟨h.fg.map _, ?_⟩
  have hs : ((M.map ((φ.symm : C →ₗ[K] W).restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) =
      (φ.symm : C →ₗ[K] W) '' (M : Set C) := by
    simp [Submodule.map_coe]
  rw [hs, Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearEquiv.range]

omit [NumberField K] in
theorem dual_pre (φ : W ≃ₗ[K] C) {HW : HermSpace K W} {H' : HermSpace K C}
    (hφ : ∀ x y, H'.B (φ x) (φ y) = HW.B x y) (M : Submodule (𝓞 K) C) :
    Formalism.HermitianLatticesTheory.dual HW.B.flip (pre φ M) = pre φ (Formalism.HermitianLatticesTheory.dual H'.B.flip M) := by
  ext x
  simp only [pre, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_comap, Submodule.mem_iInf,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearMap.flip_apply]
  constructor
  · intro hx m hm
    have hm' := hx (φ.symm m) (by simpa using hm)
    rwa [← hφ, φ.apply_symm_apply] at hm'
  · intro hx y hy
    rw [← hφ]
    exact hx _ hy

omit [NumberField K] [StarRing K] in
theorem mem_smulLat_pre (φ : W ≃ₗ[K] C) (g : 𝓞 K) (M : Submodule (𝓞 K) C) (y : W) :
    y ∈ smulLat g (pre φ M) ↔ φ y ∈ smulLat g M := by
  have hs : ∀ z : W, φ (g • z) = g • φ z := fun z => (φ : W →ₗ[K] C).map_smul_of_tower g z
  simp only [smulLat, Submodule.mem_map, pre, Submodule.mem_comap, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨φ z, hz, (hs z).symm⟩
  · rintro ⟨m, hm, hmy⟩
    refine ⟨φ.symm m, by simpa using hm, φ.injective ?_⟩
    rw [hs, φ.apply_symm_apply, hmy]

private theorem discN_pre_of_isometry (φ : W ≃ₗ[K] C) {HW : HermSpace K W} {H' : HermSpace K C}
    (hφ : ∀ x y, H'.B (φ x) (φ y) = HW.B x y) (M : Submodule (𝓞 K) C) :
    GlobalTheory.Mass.discN HW.B.flip (pre φ M) = GlobalTheory.Mass.discN H'.B.flip M := by
  unfold GlobalTheory.Mass.discN
  rw [dual_pre φ hφ, idxN_pre]

theorem isDat_pre (φ : W ≃ₗ[K] C) {HW : HermSpace K W} {H' : HermSpace K C}
    (hφ : ∀ x y, H'.B (φ x) (φ y) = HW.B x y) {g j r x : ℕ} (hj : j ≤ r) {L L' : Submodule (𝓞 K) C}
    {Γ : Submodule (𝓞 K) (C × C)} (h : IsDat H' g L j x (L', Γ)) :
    IsDat HW g (pre φ L) r x (pre φ L',
      Γ.comap (((φ : W →ₗ[K] C).prodMap (φ : W →ₗ[K] C)).restrictScalars (𝓞 K))) := by
  obtain ⟨⟨hlat, hint⟩, hdisc, ⟨m1, m2, m3, m4, m5, m6, m7⟩, hidx, t, ht, hgen⟩ := h
  have hfix : fixLat (Γ.comap (((φ : W →ₗ[K] C).prodMap (φ : W →ₗ[K] C)).restrictScalars (𝓞 K))) =
      pre φ (fixLat Γ) := by
    ext y
    simp [fixLat, pre, Submodule.mem_comap]
  refine ⟨⟨isLattice_pre φ hlat, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    have hab := hint _ ha _ hb
    simp only [LinearMap.flip_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe] at hab ⊢
    rwa [← hφ]
  · rw [discN_pre_of_isometry φ hφ, discN_pre_of_isometry φ hφ]
    exact hdisc
  · intro p hp
    exact m1 hp
  · intro p hp
    obtain ⟨h1, h2⟩ := Submodule.mem_prod.1 hp
    exact m2 (Submodule.mem_prod.2 ⟨(mem_smulLat_pre φ _ _ _).1 h1, (mem_smulLat_pre φ _ _ _).1 h2⟩)
  · intro y' hy'
    obtain ⟨z, hz⟩ := m3 _ hy'
    refine ⟨φ.symm z, ?_⟩
    show (φ y', φ (φ.symm z)) ∈ Γ
    rwa [φ.apply_symm_apply]
  · intro y hy
    obtain ⟨z, hz⟩ := m4 _ hy
    refine ⟨φ.symm z, ?_⟩
    show (φ (φ.symm z), φ y) ∈ Γ
    rwa [φ.apply_symm_apply]
  · intro y hy
    have hy' : ((0 : C), φ y) ∈ Γ := by simpa using hy
    exact (mem_smulLat_pre φ _ _ _).2 (m5 _ hy')
  · intro y hy
    have hy' : (φ y, (0 : C)) ∈ Γ := by simpa using hy
    exact (mem_smulLat_pre φ _ _ _).2 (m6 _ hy')
  · intro p hp q hq
    obtain ⟨s, hs⟩ := m7 (φ p.1, φ p.2) hp (φ q.1, φ q.2) hq
    refine ⟨s, ?_⟩
    rw [← hφ, ← hφ]
    exact hs
  · rw [hfix]
    exact (idxN_pre φ L (fixLat Γ)).trans hidx
  · refine ⟨t.image φ.symm, Finset.card_image_le.trans (ht.trans hj), ?_⟩
    rw [hfix, pre_eq_map, pre_eq_map, hgen, Submodule.map_sup, Submodule.map_span]
    congr 2
    simp [Finset.coe_image]

omit [NumberField K] [StarRing K] in
theorem mem_sup_iff {A : Type} [AddCommGroup A] [Module (𝓞 K) A] {M X S : Submodule (𝓞 K) A}
    (h1 : M ≤ S) (h2 : X ⊓ S ≤ M) {u v : A} (hv : v ∈ S) (huv : u - v ∈ X) : u ∈ M ⊔ X ↔ v ∈ M := by
  constructor
  · intro hu
    obtain ⟨m, hm, x, hx, rfl⟩ := Submodule.mem_sup.1 hu
    have hvm : v - m ∈ X ⊓ S := by
      refine Submodule.mem_inf.2 ⟨?_, S.sub_mem hv (h1 hm)⟩
      have hvx : v - m = x - (m + x - v) := by abel
      rw [hvx]
      exact X.sub_mem hx huv
    simpa using M.add_mem (h2 hvm) hm
  · intro hv'
    have hu : u = v + (u - v) := by abel
    rw [hu]
    exact Submodule.add_mem_sup hv' huv

end GlobalTheory.DegAsm.DatEmb

namespace GlobalTheory.DegAsm
open DatEmb GlobalTheory.Mass Formalism.HermitianLatticeCounting.P

private theorem span_gs_Iio_le_orthogonal {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {H : HermSpace K V} {r : ℕ} (F : FlagD H r) (n : ℕ) {v : V}
    (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) {x : V} (hx : x ∈ F.Xa n) : H.B x v = 0 := by
  unfold FlagD.Xa at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, -, rfl⟩ := hy
    exact hv _
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

private theorem flag_e_mem_V0 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {H : HermSpace K V} {r : ℕ} (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  | cast b => exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))

theorem isDat_datOf : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → IsEmb F HW e → Adapt F G 𝔡 N → N.IsTerm g Λ → IsDat HW g (lat0 F e Λ) r (N.gI g Λ) (datOf F G e g Λ) ∧ 1 ≤ N.gI g Λ ∧ (N.gI g Λ : ℝ) ≤ N.Del ∧ GlobalTheory.Mass.PD HW.B.flip ∧ Module.finrank K W + 2 * r + 1 = Module.finrank K V := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F G 𝔡 N g Λ hg hE hA hT
  obtain ⟨-, hX, -, -, -, -, -, -, hlat⟩ := adapt_invariants K V H hK r F G 𝔡 N hA
  obtain ⟨-, -, -, -, hL0', hio⟩ := hlat g Λ
  have hSG : SameGr F N.F := hA.2.1
  have hSG' : SameGr N.F F := AdaptInv.sameGr_symm hSG
  obtain ⟨hfull, ⟨hW1, hW2, hW3⟩, -, hrank, hWn, huP, hwSp, hwSp', -, -, -, -⟩ :=
    NF.geometry K V H hK r N
  obtain ⟨-, -, -, -, -, hFX, -, hlF, -⟩ := hfull
  obtain ⟨H', hH', hH'PD, -, -, -, hDat⟩ := GlobalTheory.T.definiteLift_embedded_datum_of_term K V H hK r N g Λ hg hT
  obtain ⟨-, hgI, hiI, -, hle, -⟩ := GlobalTheory.DegCnt.FixIdx.main K V H hK r N g Λ hg hT
  have frame : ∀ v : V, (∀ a, H.B (F.e a) v = 0) ↔ (∀ a, H.B (N.F.e a) v = 0) := by
    intro v
    constructor
    · intro hv a
      have hd := span_gs_Iio_le_orthogonal F a.val hv (hSG a)
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hd
      rw [hd]
      exact hv a
    · intro hv a
      have hd := span_gs_Iio_le_orthogonal N.F a.val hv (hSG' a)
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hd
      rw [hd]
      exact hv a
  have hEm : ∀ v : V, (∀ a, H.B (N.F.e a) v = 0) ↔ v ∈ LinearMap.range e ⊔ N.F.X := by
    intro v
    rw [← frame, hX]
    exact hE.2 v
  have hiso : ∀ x y, H.B (e x) (e y) = HW.B x y := hE.1
  have hfr : ∀ y, ∀ a, H.B (N.F.e a) (e y) = 0 := fun y =>
    (hEm _).2 (Submodule.mem_sup_left (LinearMap.mem_range_self e y))
  have hXV : N.F.X ≤ V0 N.F N.F' := le_sup_left.trans le_sup_left
  have hXII : ∀ x, x ∈ N.F.X → x ∈ wSp N.F N.F' → x ∈ II N.F N.F' := fun x hx hw =>
    (hFX x hx).1 ((NFGeom.mem_perp' _ x).1 hw)
  have hWw : ∀ y : N.Wt, (y : V) ∈ wSp N.F N.F' := fun y => by
    rw [hwSp]
    exact Submodule.mem_sup_left y.2
  have hWu : ∀ y : N.Wt, (y : V) ∈ uPerp N.F N.F' := fun y => by
    rw [huP, hWn]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left y.2)
  have huS : uPerp N.F' N.F = uPerp N.F N.F' := by
    unfold uPerp
    rw [sup_comm]
  have hIIL : ∀ x, x ∈ II N.F N.F' → x ∈ flagPairDefinitePartLattice N.F N.F' Λ ∧ x ∈ flagPairDefinitePartLattice N.F' N.F Λ := by
    intro x hx
    refine ⟨⟨⟨NFGeom.II_le_uPerp N hx, Submodule.mem_sup_right hx.1⟩, NFGeom.II_le_wSp N hx⟩,
      ⟨⟨?_, Submodule.mem_sup_right hx.2⟩, ?_⟩⟩
    · show x ∈ uPerp N.F' N.F
      rw [huS]
      exact NFGeom.II_le_uPerp N hx
    · show x ∈ wSp N.F' N.F
      rw [hwSp']
      exact NFGeom.II_le_wSp N hx
  have he : ∀ w, e w ∈ N.F.X → w = 0 := by
    intro w hw
    apply HW.nondeg
    intro y
    rw [← hiso]
    exact span_gs_Iio_le_orthogonal N.F r (hfr y) hw
  have hc : ∀ y : N.Wt, (y : V) ∈ N.F.X → y = 0 := by
    intro y hy
    have h0 : (y : V) ∈ N.Wt ⊓ II N.F N.F' :=
      Submodule.mem_inf.2 ⟨y.2, (hFX _ hy).1 (fun w hw => hW1 _ y.2 _ hw)⟩
    rw [hW2] at h0
    exact Subtype.ext ((Submodule.mem_bot K).1 h0)
  have h1 : ∀ w, ∃ y : N.Wt, e w - N.Wt.subtype y ∈ N.F.X := by
    intro w
    obtain ⟨x, hx, hxo⟩ := hlF (e w) (hfr w)
    obtain ⟨y, hy, i, hi, hyi⟩ := Submodule.mem_sup.1 (hW3 _ hxo)
    refine ⟨⟨y, hy⟩, ?_⟩
    have hd : e w - y = x + i := by
      calc e w - y = (e w - x) - y + x := by abel
        _ = (y + i) - y + x := by rw [hyi]
        _ = x + i := by abel
    simp only [Submodule.subtype_apply]
    rw [hd]
    exact add_mem hx (Submodule.mem_inf.1 hi).1
  have h2 : ∀ y : N.Wt, ∃ w, e w - N.Wt.subtype y ∈ N.F.X := by
    intro y
    have hf : ∀ a, H.B (N.F.e a) y = 0 := fun a => hW1 _ y.2 _ (flag_e_mem_V0 N.F N.F' a)
    obtain ⟨v, hv, x, hx, hvx⟩ := Submodule.mem_sup.1 ((hEm y).1 hf)
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hv
    refine ⟨w, ?_⟩
    simp only [Submodule.subtype_apply]
    rw [← hvx]
    simpa using N.F.X.neg_mem hx
  obtain ⟨φ, hφX⟩ := DatEmb.exists_equiv N.F.X e N.Wt.subtype he hc h1 h2
  simp only [Submodule.subtype_apply] at hφX
  have hφ : ∀ x y, H'.B (φ x) (φ y) = HW.B x y := by
    intro x y
    rw [hH', ← hiso]
    have e1 : H.B (e x - φ x) (e y) = 0 := span_gs_Iio_le_orthogonal N.F r (hfr y) (hφX x)
    have e2 : H.B (φ x : V) (e y - φ y) = 0 := by
      rw [← H.herm, hW1 _ (φ x).2 _ (hXV (hφX y)), star_zero]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1
    rw [map_sub, sub_eq_zero] at e2
    rw [e1, e2]
  have hP := DatEmb.isDat_pre φ hφ N.j_le hDat
  have hlat0 : lat0 F e Λ = lat0 N.F e Λ := by
    unfold lat0
    rw [hX]
  have hdat : datOf F G e g Λ = datOf N.F N.F' e g Λ := by
    unfold datOf
    rw [hX, hL0', hio]
  have q1 : lat0 N.F e Λ = DatEmb.pre φ (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) := by
    ext w
    simp only [lat0, DatEmb.pre, GlobalTheory.Mass.latIn, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, Submodule.subtype_apply]
    have hsub : e w - (φ w : V) ∈ Λ ⊔ rs (𝓞 K) N.F.X := Submodule.mem_sup_right (hφX w)
    show _ ↔ (φ w : V) ∈ (rs (𝓞 K) (uPerp N.F N.F') ⊓ (Λ ⊔ rs (𝓞 K) N.F.X)) ⊓ rs (𝓞 K) (wSp N.F N.F')
    simp only [Submodule.mem_inf]
    constructor
    · intro h
      refine ⟨⟨hWu (φ w), ?_⟩, hWw (φ w)⟩
      simpa using Submodule.sub_mem _ h hsub
    · intro h
      simpa using Submodule.add_mem _ h.1.2 hsub
  have hS1 : flagPairDefinitePartLattice N.F' N.F Λ ≤ rs (𝓞 K) (wSp N.F N.F') := by
    rw [← hwSp']
    exact inf_le_right
  have hS2 : flagPairDefinitePartLattice N.F N.F' Λ ≤ rs (𝓞 K) (wSp N.F N.F') := inf_le_right
  have q2 : datOf N.F N.F' e g Λ = (DatEmb.pre φ (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F' N.F Λ)),
      ((iotaGraph N.F N.F' Λ (g : 𝓞 K)).comap ((N.Wt.subtype.prodMap N.Wt.subtype).restrictScalars (𝓞 K))).comap
        (((φ : W →ₗ[K] N.Wt).prodMap (φ : W →ₗ[K] N.Wt)).restrictScalars (𝓞 K))) := by
    refine Prod.ext ?_ ?_
    · ext w
      simp only [datOf, DatEmb.pre, GlobalTheory.Mass.latIn, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe, Submodule.subtype_apply]
      refine DatEmb.mem_sup_iff hS1 ?_ (hWw (φ w)) (hφX w)
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      exact (hIIL x (hXII x hx1 hx2)).2
    · ext p
      simp only [datOf, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.prodMap_apply,
        LinearEquiv.coe_coe, Submodule.subtype_apply]
      refine DatEmb.mem_sup_iff (S := (rs (𝓞 K) (wSp N.F N.F')).prod (rs (𝓞 K) (wSp N.F N.F')))
        (inf_le_left.trans (Submodule.prod_mono hS1 hS2)) ?_
        (Submodule.mem_prod.2 ⟨hWw (φ p.1), hWw (φ p.2)⟩)
        (Submodule.mem_prod.2 ⟨by simpa using hφX p.1, by simpa using hφX p.2⟩)
      intro q hq
      obtain ⟨hq1, hq2⟩ := Submodule.mem_inf.1 hq
      obtain ⟨ha1, ha2⟩ := Submodule.mem_prod.1 hq1
      obtain ⟨hb1, hb2⟩ := Submodule.mem_prod.1 hq2
      have i1 := hXII _ ha1 hb1
      have i2 := hXII _ ha2 hb2
      refine Submodule.mem_inf.2 ⟨Submodule.mem_prod.2 ⟨(hIIL _ i1).2, (hIIL _ i2).1⟩, ?_⟩
      exact Submodule.mem_sup_right (Submodule.mem_prod.2 ⟨i1.2, i2.1⟩)
  rw [hlat0, hdat, q1, q2]
  refine ⟨hP, hgI, ?_, ?_, ?_⟩
  · have h1' : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast hiI
    have h0 : (0 : ℝ) ≤ N.gI g Λ := Nat.cast_nonneg _
    nlinarith
  · intro τ x hx
    have hpos := hH'PD τ (φ x) ((LinearEquiv.map_ne_zero_iff φ).2 hx)
    simpa [LinearMap.flip_apply, hφ] using hpos
  · rw [φ.finrank_eq]
    exact hrank

end GlobalTheory.DegAsm
