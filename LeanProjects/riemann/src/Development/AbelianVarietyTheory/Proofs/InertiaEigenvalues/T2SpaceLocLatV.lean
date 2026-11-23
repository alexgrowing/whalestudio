import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.DictKs

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

abbrev onT {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) : ↥T.L.T →ₗ[O] ↥T'.L.T :=
  (f.f.restrictScalars O).restrict f.T_le

theorem onT_inj {T Y Z : LocLat G Qp LL O} {ι : LatHom T.L Y.L} {π : LatHom Y.L Z.L}
    (h : IsSESLat (Qp := Qp) ι π) : Function.Injective (onT ι) := fun a b hab =>
  Subtype.ext (h.1 (congrArg Subtype.val hab))

theorem onT_surj {T Y Z : LocLat G Qp LL O} {ι : LatHom T.L Y.L} {π : LatHom Y.L Z.L}
    (h : IsSESLat (Qp := Qp) ι π) : Function.Surjective (onT π) := fun z => by
  obtain ⟨y, hy, hyz⟩ := h.2.2.1 z z.2
  exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩

theorem onT_exact {T Y Z : LocLat G Qp LL O} {ι : LatHom T.L Y.L} {π : LatHom Y.L Z.L}
    (h : IsSESLat (Qp := Qp) ι π) : Function.Exact (onT ι) (onT π) := fun y => by
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (h.2.2.2.1 y).1 (congrArg Subtype.val hy)
    exact ⟨⟨x, h.2.2.2.2 x (hx ▸ y.2)⟩, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((h.2.2.2.1 _).2 ⟨x, rfl⟩)

theorem lTensor_inj {T Y Z : LocLat G Qp LL O} {ι : LatHom T.L Y.L} {π : LatHom Y.L Z.L}
    (h : IsSESLat (Qp := Qp) ι π) (R : Type) [AddCommGroup R] [Module O R] :
    Function.Injective ((onT ι).lTensor R) := by
  haveI := Z.L.free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (onT π) LinearMap.id (onT_surj h)
  have h3 := ((onT_exact h).split_tfae (onT_inj h) (onT_surj h)).out 0 1
  obtain ⟨r, hr⟩ := h3.1 ⟨s, hs⟩
  apply Function.LeftInverse.injective (g := r.lTensor R)
  intro x
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id]
  rfl

theorem t2Space_locLat_V [T2Space LL] [IsTopologicalRing LL] (T : LocLat G Qp LL O) : T2Space T.V := by
  let b := Module.finBasis LL T.V
  exact T2Space.of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem lTensor_TWmap {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L) (f : RW →ₐ[O] RW)
    (b : TW RW T) : (onT ι).lTensor RW (TWmap f T b) = TWmap f Y ((onT ι).lTensor RW b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem lTensor_TWact {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L) (f : RW →ₐ[O] RW) (g : G)
    (b : TW RW T) : (onT ι).lTensor RW (TWact f T g b) = TWact f Y g ((onT ι).lTensor RW b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    simp only [TWact, TensorProduct.map_tmul, LinearMap.lTensor_tmul]
    congr 1
    exact Subtype.ext (ι.equiv g t)
  | add a b ha hb => simp only [map_add, ha, hb]

theorem generic [T2Space LL] [IsTopologicalRing LL] (E : EtTie W RA RW inclR φR gR πA)
    (hinj : Function.Injective (algebraMap O RW))
    (hdense : ∀ M : Submonoid ↥W.GKs, IsClosed (M : Set ↥W.GKs) →
      (∀ g : ↥W.GKs, W.resΓ (g : G) = 1 → g ∈ M) → (∀ g : ↥W.GKs, W.resΓ (g : G) = W.gam → g ∈ M) →
      ∀ g, g ∈ M)
    (T Yt Z : LocLat G Qp LL O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L)
    (hS : IsSESLat (Qp := Qp) ι π) (yt : ↥Yt.L.T) (z : ↥Z.L.T) (e : W.DD Yt)
    (hz : (z : Z.V) = π.f yt) (he : E.jD Z (W.map π e) = (1 : RW) ⊗ₜ[O] z)
    (pr : ↥(W.divisibleCocycles T)) (h1 : W.map ι (pr : W.DD T × W.DD T).1 = W.φD Yt e - e)
    (h2 : W.map ι (pr : W.DD T × W.DD T).2 = W.γ Yt e - e)
    (c : ↥(latticeCocycles (resLat T W.GKs)))
    (hc : ∀ g : ↥W.GKs, ι.f ((c : ↥W.GKs → T.V) g) = Yt.ρ (g : G) yt - yt) :
    W.cl T pr = Submodule.Quotient.mk c := by
  have hjι : ∀ x, E.jD Yt (W.map ι x) = (onT ι).lTensor RW (E.jD T x) := fun x => E.jD_map ι x
  have hjπ : ∀ x, E.jD Z (W.map π x) = (onT π).lTensor RW (E.jD Yt x) := fun x => E.jD_map π x
  have hex := lTensor_exact RW (onT_exact hS) (onT_surj hS)
  have hzz : onT π yt = z := Subtype.ext hz.symm
  obtain ⟨b, hb⟩ := (hex (E.jD Yt e - (1 : RW) ⊗ₜ[O] yt)).1 (by
    rw [map_sub, ← hjπ, he, LinearMap.lTensor_tmul, hzz, sub_self])
  have hI := lTensor_inj hS RW
  have hφ : TWmap φR T b - b = E.jD T (pr : W.DD T × W.DD T).1 := by
    apply hI
    rw [map_sub, lTensor_TWmap, hb, ← hjι, h1, map_sub, map_sub, E.jD_φ]
    simp [TWmap]
  obtain ⟨c', hc', hval⟩ := E.cl_def T pr b hφ
  rw [← hc']
  congr 1
  haveI := Yt.L.free
  haveI := t2Space_locLat_V T
  have hone : Function.Injective fun y : ↥Yt.L.T => (1 : RW) ⊗ₜ[O] y := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥Yt.L.T)
      (Algebra.linearMap O RW) hinj
    intro a a' haa
    have h' : (1 : O) ⊗ₜ[O] a = (1 : O) ⊗ₜ[O] a' := this (by simpa using haa)
    simpa using congrArg (TensorProduct.lid O _) h'
  have hact : ∀ g : G, (onT ι).lTensor RW (TWact (gR g) T g b - b) =
      E.jD Yt (W.γD Yt (W.resΓ g) e - e) - (1 : RW) ⊗ₜ[O] (Yt.actT g yt - yt) := by
    intro g
    rw [map_sub, lTensor_TWact, hb, map_sub, map_sub, E.jD_act, tmul_sub]
    simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
    abel
  have key : ∀ (g : ↥W.GKs) (t : ↥T.L.T), (t : T.V) = (c' : ↥W.GKs → T.V) g →
      (onT ι).lTensor RW ((1 : RW) ⊗ₜ[O] t) = (1 : RW) ⊗ₜ[O] (Yt.actT g yt - yt) →
      (c' : ↥W.GKs → T.V) g = (c : ↥W.GKs → T.V) g := by
    intro g t ht h
    rw [LinearMap.lTensor_tmul] at h
    have h' := congrArg Subtype.val (hone h)
    apply hS.1
    rw [hc, ← ht]
    exact h'
  let M : Submonoid ↥W.GKs :=
    { carrier := {g | (c' : ↥W.GKs → T.V) g = (c : ↥W.GKs → T.V) g}
      mul_mem' := fun {a a'} ha ha' => by
        simp only [Set.mem_setOf_eq] at ha ha' ⊢
        rw [c'.2.1.2, c.2.1.2, ha, ha']
      one_mem' := by
        have e1 := c'.2.1.2 1 1
        have e2 := c.2.1.2 1 1
        simp only [mul_one, map_one, Module.End.one_apply, left_eq_add] at e1 e2
        simp only [Set.mem_setOf_eq]
        rw [e1, e2] }
  have hM := hdense M (isClosed_eq c'.2.1.1 c.2.1.1)
    (fun g hg => by
      let t : ↥T.L.T := ⟨(c' : ↥W.GKs → T.V) g, c'.2.2 g (Set.mem_univ _)⟩
      refine key g t rfl ?_
      rw [(hval g t rfl).1 hg, map_neg, hact, hg, W.γD_one]
      simp)
    (fun g hg => by
      let t : ↥T.L.T := ⟨(c' : ↥W.GKs → T.V) g, c'.2.2 g (Set.mem_univ _)⟩
      refine key g t rfl ?_
      rw [(hval g t rfl).2 hg, map_sub, hact, hg, ← hjι, h2]
      simp [LocWach.γ])
  exact Subtype.ext (funext fun g => hM g)

end Generic

variable {l : ℕ} [Fact l.Prime]

theorem zlW_inj (R : Type) [CommRing R] [Nontrivial R] [CharP R l] : Function.Injective (zlW l R) := by
  unfold zlW
  rw [RingHom.coe_comp]
  exact (WittVector.map_injective _ (ZMod.castHom (dvd_refl l) R).injective).comp
    (WittVector.equiv l).symm.injective

theorem algebraMap_RW_inj (LL : FinExt l) : Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  haveI : Module.IsTorsionFree ℤ_[l] ↥(OL LL) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    have h := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) hab
    have h' : algebraMap ℚ_[l] ↥LL.1 a = algebraMap ℚ_[l] ↥LL.1 b := h
    exact Subtype.ext ((algebraMap ℚ_[l] ↥LL.1).injective h')
  have := Module.Flat.lTensor_preserves_injective_linearMap (M := ↥(OL LL))
      (Algebra.linearMap ℤ_[l] (WCb l)) (zlW_inj (Cb l))
  intro a a' haa
  have h' : a ⊗ₜ[ℤ_[l]] (1 : ℤ_[l]) = a' ⊗ₜ[ℤ_[l]] (1 : ℤ_[l]) := this (by simpa using haa)
  simpa using congrArg (TensorProduct.rid ℤ_[l] _) h'

theorem mem_OL_iff (LL : FinExt l) (x : ℚ_[l]) : algebraMap ℚ_[l] ↥LL.1 x ∈ OL LL ↔ ‖x‖ ≤ 1 := by
  have h1 : algebraMap ℚ_[l] ↥LL.1 x ∈ OL LL ↔ IsIntegral ℤ_[l] x :=
    isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective
  rw [h1, IsIntegrallyClosed.isIntegral_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem le_v_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (k : ℕ) :
    (k : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ↔ ‖x‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hlR : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _
  obtain ⟨y, rfl⟩ : ∃ y, x = (l : ℚ_[l]) ^ k * y := ⟨x / l ^ k, by field_simp⟩
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, P.v_l, nsmul_one,
    norm_mul, Padic.norm_p_pow, mul_le_iff_le_one_right hlR, ← mem_OL_iff LL, ← P.v_O]
  have : (k : WithTop ℚ) ≠ ⊤ := by exact_mod_cast WithTop.coe_ne_top (a := (k : ℚ))
  conv_lhs => lhs; rw [← add_zero (k : WithTop ℚ)]
  exact WithTop.add_le_add_iff_left this

theorem norm_eq_of_v (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (k : ℕ)
    (h : P.v LL (algebraMap ℚ_[l] ↥LL.1 x) = k) : ‖x‖ = (l : ℝ) ^ (-(k : ℤ)) := by
  apply le_antisymm ((le_v_iff P LL x k).1 h.ge)
  by_contra hlt
  push Not at hlt
  have h2 : ‖x‖ ≤ (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    have e : -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) := by
      push_cast
      ring
    rw [e]
    exact hlt
  rw [← le_v_iff P LL, h] at h2
  have h3 : (((k + 1 : ℕ) : ℚ) : WithTop ℚ) ≤ ((k : ℚ) : WithTop ℚ) := by exact_mod_cast h2
  rw [WithTop.coe_le_coe] at h3
  push_cast at h3
  linarith

theorem dense_gen (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (hs : W.s = s)
    (M : Submonoid ↥W.GKs) (hM : IsClosed (M : Set ↥W.GKs))
    (h1 : ∀ g : ↥W.GKs, W.resΓ (g : ↥(GK K)) = 1 → g ∈ M)
    (h2 : ∀ g : ↥W.GKs, W.resΓ (g : ↥(GK K)) = W.gam → g ∈ M) (g : ↥W.GKs) : g ∈ M := by
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hcb := (cyc_basic l P.χQ hχ).2.2 K
  have hK0 : ∀ x : ↥(GK K), (x : GQ l) ∈ (K0 K).fixingSubgroup := fun x =>
    IntermediateField.fixingSubgroup_antitone (inf_le_left : K0 K ≤ K.1) x.2
  have hmem : ∀ x : ↥(GK K), x ∈ W.GKs ↔ (x : GQ l) ∈ Gj K s := by
    intro x
    rw [W.GKs_def, (hcb x (hK0 x)).1 s, hs, P.PD_χ, ← le_v_iff P LL,
      (algebraMap ℚ_[l] ↥LL.1).map_sub, (algebraMap ℚ_[l] ↥LL.1).map_one]
  have hGj : Gj K s ≤ GK K := IntermediateField.fixingSubgroup_antitone h.2.2.1
  obtain ⟨γ, hγ⟩ := W.resΓ_onto W.gam
  have hγv : ‖(P.χQ (γ : GQ l) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    apply norm_eq_of_v P LL
    have := W.gam_gen
    rw [← hγ, W.χΓ_res, hs, P.PD_χ] at this
    rw [map_sub, map_one]
    exact this
  have hγj : (γ : GQ l) ∈ Gj K s := ((hcb γ (hK0 γ)).1 s).2 hγv.le
  have hd := ((gen_dense l AI.actC P.χQ hact hχ K s ⟨h.1, h.2.1⟩).2 γ ⟨hγj, hγv⟩).2.2
    ((hmem g).1 g.2)
  let j : ↥W.GKs → GQ l := fun x => ((x : ↥(GK K)) : GQ l)
  have hj : Topology.IsInducing j := Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hsub : {x | ∃ h ∈ Hinf K, ∃ a : ℕ, x = h * (γ : GQ l) ^ a} ⊆ j '' (M : Set ↥W.GKs) := by
    rintro _ ⟨η, hη, a, rfl⟩
    have hη0 : η ∈ (K0 K).fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Kinf K) hη
    have hη1 : P.χQ η = 1 := (hcb η hη0).2.1 hη
    have hηj : η ∈ Gj K s := ((hcb η hη0).1 s).2 (by
      rw [hη1, Units.val_one, sub_self, norm_zero]
      positivity)
    let η' : ↥W.GKs := ⟨⟨η, hGj hηj⟩, (hmem _).2 hηj⟩
    let γ' : ↥W.GKs := ⟨γ, (hmem _).2 hγj⟩
    refine ⟨η' * γ' ^ a, M.mul_mem (h1 η' ?_) (M.pow_mem (h2 γ' hγ) a), rfl⟩
    apply W.χΓ_inj
    rw [map_one]
    apply Units.ext
    apply Subtype.ext
    have := W.χΓ_res η'
    rw [P.PD_χ] at this
    change _ = algebraMap ℚ_[l] ↥LL.1 (P.χQ η : ℚ_[l]) at this
    rw [hη1, Units.val_one, map_one] at this
    exact this
  have := closure_mono hsub hd
  have h3 : g ∈ closure (M : Set ↥W.GKs) := by
    rw [hj.closure_eq_preimage_closure_image]
    exact this
  rwa [hM.closure_eq] at h3

end GlobalTheory.Cyc.DictKs

theorem GlobalTheory.Cyc.dict_ext_Ks : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm9 D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T Yt Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L), IsSESLat (Qp := S.Qp) ι π → (∀ g x, Z.ρ g x = x) → ∀ (yt : ↥Yt.L.T) (z : ↥Z.L.T) (e : S.W.DD Yt), (z : Z.V) = π.f yt → E.jD Z (S.W.map π e) = (1 : S.RW) ⊗ₜ[S.O] z → ∀ pr : ↥(S.W.divisibleCocycles T), S.W.map ι (pr : S.W.DD T × S.W.DD T).1 = S.W.φD Yt e - e → S.W.map ι (pr : S.W.DD T × S.W.DD T).2 = S.W.γ Yt e - e → ∀ c : ↥(latticeCocycles (resLat T S.W.GKs)), (∀ g : ↥S.W.GKs, ι.f ((c : ↥S.W.GKs → T.V) g) = Yt.ρ (g : S.G) yt - yt) → S.W.cl T pr = Submodule.Quotient.mk c := by
  intro D HW F _ l _ K s LL h S E T Yt Z ι π hS _ yt z e hz he pr h1 h2 c hc
  haveI : T2Space S.LL := inferInstanceAs (T2Space ↥LL.1)
  haveI : IsTopologicalRing S.LL := inferInstanceAs (IsTopologicalRing ↥LL.1)
  exact GlobalTheory.Cyc.DictKs.generic E (GlobalTheory.Cyc.DictKs.algebraMap_RW_inj LL)
    (GlobalTheory.Cyc.DictKs.dense_gen (D.loc l) (D.locA l) K s LL h _ ((HW l).W_s K s LL h))
    T Yt Z ι π hS yt z e hz he pr h1 h2 c hc
