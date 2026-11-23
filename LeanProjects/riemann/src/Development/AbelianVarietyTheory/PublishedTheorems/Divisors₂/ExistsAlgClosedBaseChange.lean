import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.Published

def NefProductNonneg : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (d : ℕ),
    IsProjOver (strHom k X) → topologicalKrullDim X = d →
    ∀ N : Fin d → LB X, (∀ i, IsNef k (N i)) → 0 ≤ interNum k (structureModule X) N

def NefBigIff : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)]
    (D : ℕ), IsProjOver (strHom k X) → topologicalKrullDim X = D →
    ∀ N : LB X, IsNef k N → (IsBig k N ↔ 0 < topSelfIntersection k N D)

def NefRiemannRoch : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (D : ℕ),
    IsProjOver (strHom k X) → topologicalKrullDim X = D →
    ∀ L : LB X, IsNef k L →
      (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L D : ℝ) * (m : ℝ) ^ D / D.factorial)
        =O[atTop] fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1)

def NefNumerics : Prop := NefProductNonneg ∧ NefBigIff ∧ NefRiemannRoch

theorem dim_affineOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) :=
  (topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
    hU.range_fromSpec).trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U)))

theorem dim_le_of_isIntegralHom {X Y : Scheme.{0}} (π : Y ⟶ X) [IsIntegralHom π] :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  refine ⟨(π ⁻¹ᵁ U : Y.Opens), (π ⁻¹ᵁ U).isOpen, hy, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le X (U : Set X))
  rw [dim_affineOpen (hU.preimage π), dim_affineOpen hU]
  letI := (π.app U).hom.toAlgebra
  have : Algebra.IsIntegral Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := ⟨IsIntegralHom.isIntegral_app π U hU⟩
  exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, π ⁻¹ᵁ U)))
    fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h

theorem exists_algClosed_baseChange {k : Type} [Field k] {X : Scheme.{0}} [a : Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k X)) :
    ∃ (X' : Scheme.{0}) (_ : Algebra (AlgebraicClosure k) Γ(X', ⊤)) (π : X' ⟶ X),
      IsProjOver (strHom (AlgebraicClosure k) X') ∧
      topologicalKrullDim X' = topologicalKrullDim X ∧
      (∀ L : LB X, IsNef k L → IsNef (AlgebraicClosure k) (L.pull π)) ∧
      (∀ L : LB X, L.IsLB → lbH0 (AlgebraicClosure k) (L.pull π) = lbH0 k L) ∧
      ∀ (d : ℕ) (L : Fin d → LB X), (∀ i, (L i).IsLB) →
        interNum (AlgebraicClosure k) (structureModule X') (fun i => (L i).pull π) =
          interNum k (structureModule X) L := by
  obtain ⟨f, rfl⟩ : ∃ f : X ⟶ Sp k, a = algebraΓOfHom f :=
    ⟨strHom k X, Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)⟩
  letI := algebraΓOfHom f
  rw [strHom_eq (f := f) fun _ => rfl] at hp
  have H := IsPullback.of_hasPullback f (spMap (algebraMap k (AlgebraicClosure k)))
  set π := pullback.fst f (spMap (algebraMap k (AlgebraicClosure k)))
  set f' := pullback.snd f (spMap (algebraMap k (AlgebraicClosure k)))
  letI := algebraΓOfHom f'
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hp
  have : IsIntegralHom (spMap (algebraMap k (AlgebraicClosure k))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  have : IsIntegralHom π := MorphismProperty.of_isPullback (P := @IsIntegralHom) H.flip this
  have : IsProper (strHom k X) := by rwa [strHom_eq (f := f) fun _ => rfl]
  refine ⟨_, algebraΓOfHom f', π, ?_, ?_, fun L h => ?_, fun L hL => ?_, fun d L hL => ?_⟩
  · rw [strHom_eq (f := f') fun _ => rfl]
    exact PosBaseChange.isProjOver_of_isPullback H hp
  · exact (dim_le_of_isIntegralHom π).antisymm
      (PosBaseChange.dim_le_of_isClosedMap π.isClosedMap (PosBaseChange.surjective_proj H))
  · exact PosBaseChange.isNef_pull h hA (hA.pull_of_isAffineHom π) π π.isClosedMap
  · exact FieldChangeInter.hdim_pull H hL 0
  · exact FieldChangeInter.interNum_pull H hL

section AnyField

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {D : ℕ}

theorem NefProductNonneg.interNum_nonneg (h : NefProductNonneg) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {N : Fin D → LB X} (hN : ∀ i, IsNef k (N i)) :
    0 ≤ interNum k (structureModule X) N := by
  obtain ⟨X', _, π, hp', hd, hn, -, hi⟩ := exists_algClosed_baseChange hp
  rw [← hi D N fun i => (hN i).isLB]
  exact h _ X' D hp' (hd.trans hD) _ fun i => hn _ (hN i)

theorem NefProductNonneg.interNumOn_nonneg (h : NefProductNonneg) (hp : IsProjOver (strHom k X))
    {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (hD : topologicalKrullDim Z = D)
    {N : Fin D → LB X} (hN : ∀ j, IsNef k (N j)) : 0 ≤ interNumOn k i N := by
  letI := algebraΓAlong k i
  have hi := appTop_algebraMap_along k i
  rw [interNumOn_eq_interNum_pull hi fun j => (hN j).isLB]
  refine h.interNum_nonneg ?_ hD fun j => (hN j).pull_of_isClosedImmersion i hi
  obtain ⟨n, e, he, hs⟩ := hp
  exact ⟨n, i ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩

theorem NefProductNonneg.interNumRed_nonneg (h : NefProductNonneg) (hp : IsProjOver (strHom k X))
    {Z : Closeds X} (hD : topologicalKrullDim (Z : Set X) = D)
    {N : Fin D → LB X} (hN : ∀ j, IsNef k (N j)) : 0 ≤ interNumRed k Z N :=
  h.interNumOn_nonneg hp (redι Z) ((topologicalKrullDim_red Z).trans hD) hN

theorem NefRiemannRoch.isBigO (h : NefRiemannRoch) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L D : ℝ) * (m : ℝ) ^ D / D.factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1) := by
  obtain ⟨X', _, π, hp', hd, hn, h0, hi⟩ := exists_algClosed_baseChange hp
  have hL' := LB.isLB_pull hL.isLB π
  refine (h _ X' D hp' (hd.trans hD) _ (hn _ hL)).congr_left fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL.1 m) π)
    (by rw [cls_lbPow hL', cls_pull hL.1, cls_pull (isLB_lbPow hL.1 m), cls_lbPow hL.1, map_nsmul]),
    h0 _ (isLB_lbPow hL.1 m), topSelf_def, hi D (fun _ => L) fun _ => hL.1, topSelf_def]

theorem NefRiemannRoch.tendsto (h : NefRiemannRoch) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    Tendsto (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) / (m : ℝ) ^ D) atTop
      (nhds ((topSelfIntersection k L D : ℝ) / D.factorial)) := by
  have ho : (fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1)) =o[atTop] fun m : ℕ => (m : ℝ) ^ D := by
    refine (isLittleO_iff_tendsto' ?_).2 ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).congr' ?_)
    · filter_upwards [eventually_gt_atTop 0] with m hm h0
      exact absurd h0 (by positivity)
    · filter_upwards [eventually_gt_atTop 0] with m hm
      have : (m : ℝ) ≠ 0 := by positivity
      rw [zpow_sub_one₀ this, zpow_natCast]
      field_simp
  have ht := ((h.isBigO hp hD hL).trans_isLittleO ho).tendsto_div_nhds_zero.add_const
    ((topSelfIntersection k L D : ℝ) / D.factorial)
  rw [zero_add] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem NefRiemannRoch.topSelf_nonneg (h : NefRiemannRoch) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) : 0 ≤ topSelfIntersection k L D := by
  have h0 := ge_of_tendsto' (h.tendsto hp hD hL) fun m => (by positivity : (0 : ℝ) ≤ _)
  have hf : (0 : ℝ) < D.factorial := by positivity
  exact_mod_cast (div_nonneg_iff.1 h0).elim And.left fun h' => absurd h'.2 hf.not_ge

theorem NefRiemannRoch.isBig_iff (h : NefRiemannRoch) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    IsBig k L ↔ 0 < topSelfIntersection k L D := by
  have ht := h.tendsto hp hD hL
  have hf : (0 : ℝ) < D.factorial := by positivity
  rw [GlobalTheory.isBig_iff (algebraMap_eq_strHom k X) hp hD, ← Int.cast_pos (R := ℝ),
    ← div_pos_iff_of_pos_right hf]
  refine ⟨fun ⟨_, c, hc, hm⟩ => hc.trans_le (ge_of_tendsto_of_frequently ht
    ((hm.and_eventually (eventually_gt_atTop 0)).mono fun m hm => ?_)),
    fun ha => ⟨hL.isLB, _, half_pos ha, Eventually.frequently ?_⟩⟩
  · have := hm.2
    exact (le_div_iff₀ (by positivity)).2 hm.1
  · filter_upwards [ht.eventually_const_le (half_lt_self ha), eventually_gt_atTop 0] with m h₁ h₂
    exact (le_div_iff₀ (by positivity)).1 h₁

end AnyField

theorem NefRiemannRoch.nefBigIff (h : NefRiemannRoch) : NefBigIff :=
  fun _ _ _ _ _ _ _ hp hD _ hL => h.isBig_iff hp hD hL

open GlobalTheory.ProjSpace in

example (k : Type) [Field k] (d : ℕ) :
    IsIntegral (PSpace k (d + 1)) ∧ IsProjOver (strHom k (PSpace k (d + 1))) ∧
    topologicalKrullDim (PSpace k (d + 1)) = (d + 1 : ℕ) ∧
    IsNef k (O1 k (d + 1)) ∧ IsBig k (O1 k (d + 1)) ∧
    IsNef k (LB.triv (PSpace k (d + 1))) ∧ ¬ IsBig k (LB.triv (PSpace k (d + 1))) := by
  rw [strHom_eq (algebraMap_top_eq k (d + 1))]
  exact ⟨inferInstance, isProjOver_str k _, topologicalKrullDim_eq k _, isNef_twistingSheaf k _, isBig_twistingSheaf k _,
    (triv_nef_not_big k d).1, (triv_nef_not_big k d).2.2⟩

end GlobalTheory.Published
