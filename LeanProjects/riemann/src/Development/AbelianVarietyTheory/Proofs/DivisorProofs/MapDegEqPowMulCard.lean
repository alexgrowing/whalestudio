import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.ZV GlobalTheory.DegKer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbelianTower

theorem isFinite_pow {K : Type} [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G]
    (D : TorusExtension G) (N : ℕ) (hN : 1 ≤ N) : IsFinite ((𝟙 G) ^ N : G ⟶ G).left := by
  letI := D.addCommGroup
  letI := D.grpB
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_quasiCompact
  have := D.free
  have := D.finite
  have h1 : IsFinite ((𝟙 D.B) ^ N : D.B ⟶ D.B).left := GlobalTheory.MulFiniteAny.isFinite_mulA K D.B D.isAbelian N hN
  have hf : IsFinite (mulN (splitTorus (Sp K) D.X) N).left := Diag.isFinite_mulN _ D.X (by omega)
  rw [GrpTangent.mulN_eq_pow] at hf
  have := isAffineHom_descendsAlong_fpqc.{0}
  have hP := IsPullback.of_hasPullback D.q ((𝟙 D.B) ^ N)
  have w : ((𝟙 G) ^ N) ≫ D.q = D.q ≫ ((𝟙 D.B) ^ N) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have ha := hP.lift_fst _ _ w
  have hb := hP.lift_snd _ _ w
  have a2 : IsAffineHom (hP.lift _ _ w).left :=
    ExtensionMul.of_pow_kernel @IsAffineHom D.i D.q D.isKernel N hP ha hb inferInstance
  have a3 : UniversallyClosed (hP.lift _ _ w).left :=
    ExtensionMul.of_pow_kernel @UniversallyClosed D.i D.q D.isKernel N hP ha hb inferInstance
  have a4 : LocallyOfFiniteType (hP.lift _ _ w).left :=
    ExtensionMul.of_pow_kernel @LocallyOfFiniteType D.i D.q D.isKernel N hP ha hb inferInstance
  have a5 : IsFinite (hP.lift _ _ w).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  have hP' := (hP.map (Over.forget _)).flip
  have b1 : IsFinite (pullback.fst D.q ((𝟙 D.B) ^ N)).left := MorphismProperty.of_isPullback (P := @IsFinite) hP' h1
  rw [← ha, Over.comp_left]
  infer_instance

theorem mapDeg_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [IsFinite φ] [IsFinite ψ] [Surjective φ] [Surjective ψ] {D E : ℕ} (hD : MapDeg φ D) (hE : MapDeg ψ E) :
    MapDeg (φ ≫ ψ) (E * D) := by
  refine MapDeg.of_isFinite fun U hU hne => ?_
  obtain ⟨z, hz⟩ := hne
  obtain ⟨y, rfl⟩ := ψ.surjective z
  obtain ⟨x, rfl⟩ := φ.surjective y
  haveI : Nonempty U := ⟨⟨_, hz⟩⟩
  haveI : Nonempty (ψ ⁻¹ᵁ U) := ⟨⟨φ x, hz⟩⟩
  haveI : Nonempty (φ ⁻¹ᵁ ψ ⁻¹ᵁ U) := ⟨⟨x, hz⟩⟩
  letI := (ψ.app U).hom.toAlgebra
  letI := (φ.app (ψ ⁻¹ᵁ U)).hom.toAlgebra
  letI : Algebra Γ(Z, U) Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U) := ((φ ≫ ψ).app U).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Y, ψ ⁻¹ᵁ U) Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Γ(Z, U) Γ(Y, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
  haveI := IsSchemeTheoreticallyDominant.of_isDominant φ
  haveI := IsSchemeTheoreticallyDominant.of_isDominant ψ
  haveI : FaithfulSMul Γ(Z, U) Γ(Y, ψ ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (ψ.app_injective U)
  haveI : FaithfulSMul Γ(Y, ψ ⁻¹ᵁ U) Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (φ.app_injective _)
  rw [← hE.finrank_eq U hU ⟨_, hz⟩, ← hD.finrank_eq _ (hU.preimage ψ) ⟨φ x, hz⟩]
  exact (Module.finrank_mul_finrank' Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U)).symm

theorem finrank_eq_of_mapDeg {X Y : Scheme.{0}} [IsIntegral Y] (φ : X ⟶ Y) [IsFinite φ] [Flat φ] {D : ℕ}
    (hD : MapDeg φ D) (y : Y) : φ.finrank y = D := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  letI := (φ.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := φ.finite_app U hU
  haveI : Module.Flat Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
    have := φ.flat_appLE hU (hU.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hp : IsPullback (hU.preimage φ).fromSpec (Spec.map (φ.app U)) φ hU.fromSpec :=
    (IsOpenImmersion.isPullback _ _ _ _ (by
      rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hU (hU.preimage φ)])
      (by simp)).flip
  obtain ⟨q, rfl⟩ : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hy
  rw [← hD.finrank_eq U hU ⟨_, hy⟩, ← FiniteCover.rankAtStalk_bot,
    Module.rankAtStalk_eq_of_le_of_finite_of_flat _ (p := ⊥) (q := q) bot_le,
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp q]
  exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) _

theorem mapDeg_eq_pow_mul_card (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G]
    [IsIntegral G.left] [LocallyOfFiniteType G.hom] (α : G ⟶ G) [IsMonHom α] [IsFinite α.left] :
    Finite {x : Out.baseOver (Sp K) ⟶ G // x ≫ α = 1} ∧
      ∃ e : ℕ, MapDeg α.left (ringExpChar K ^ e * Nat.card {x : Out.baseOver (Sp K) ⟶ G // x ≫ α = 1}) := by
  have hs := (flat_and_surjective_of_isFinite_grpEnd K G α).2
  obtain ⟨D, -, hD⟩ := exists_mapDeg_of_isFinite _ _ α.left inferInstance hs
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint G.left)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : Nonempty (α.left ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := α.left.surjective (genericPoint G.left)
    exact ⟨⟨x, show α.left x ∈ U from hx ▸ hξ⟩⟩
  letI := (α.left.app U).hom.toAlgebra
  have : Module.Finite Γ(G.left, U) Γ(G.left, α.left ⁻¹ᵁ U) := α.left.finite_app U hU
  have : IsSchemeTheoreticallyDominant α.left := .of_isDominant _
  have : FaithfulSMul Γ(G.left, U) Γ(G.left, α.left ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (α.left.app_injective U)
  let c : K →+* Γ(G.left, U) :=
    (G.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : ExpChar Γ(G.left, U) (ringExpChar K) := expChar_of_injective_ringHom c.injective _
  let Ω := AlgebraicClosure (FractionRing Γ(G.left, U))
  have : FaithfulSMul Γ(G.left, U) Ω := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq Γ(G.left, U) (FractionRing Γ(G.left, U)) Ω, RingHom.coe_comp]
    exact (RingHom.injective _).comp (IsFractionRing.injective _ _)
  obtain ⟨h0, e, he⟩ := finrank_eq_pow_mul_card Γ(G.left, U) Γ(G.left, α.left ⁻¹ᵁ U) Ω (ringExpChar K)
  rw [card_fibre_eq α.left hU Ω] at h0 he
  set z := Spec.map (CommRingCat.ofHom (algebraMap Γ(G.left, U) Ω)) ≫ hU.fromSpec with hz
  let z' : Over.mk (z ≫ G.hom) ⟶ G := Over.homMk z rfl
  have h1 : Nat.card {y : Over.mk (z ≫ G.hom) ⟶ G // y ≫ α = z'} =
      Nat.card {y : Spec (CommRingCat.of Ω) ⟶ G.left // y ≫ α.left = z} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun y => ⟨y.1.left, congrArg CommaMorphism.left y.2⟩) ⟨?_, ?_⟩)
    · intro y y' h
      exact Subtype.ext (Over.OverMorphism.ext (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      refine ⟨⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩, rfl⟩
      change y ≫ G.hom = z ≫ G.hom
      rw [← hy, Category.assoc, Over.w α]
  rw [← h1] at h0 he
  have hne := (Nat.card_ne_zero.mp h0).1
  rw [← card_coset_eq G _ α z' hne, ← card_ker_eq G α Ω (z ≫ G.hom)] at h0 he
  refine ⟨(Nat.card_ne_zero.mp h0).2, e, ?_⟩
  rw [← he, hD.finrank_eq U hU ⟨_, hξ⟩]
  exact hD

theorem exists_finrank_torsion (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K] (h0 : (p : K) = 0)
    (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom]
    (D : TorusExtension G) : ∃ h : ℕ, ∀ (n : ℕ) (S : Type) [CommRing S] [Algebra K S] [Module.Finite K S]
      (y : SpAlg K S ⟶ G), IsPullback y.left (spMap (algebraMap K S)) (mulN G (p ^ n)).left η[G].left →
        Module.finrank K S = p ^ (n * h) := by
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ G.hom ‹_› ‹_›
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have hm : ∀ N, IsMonHom ((𝟙 G) ^ N : G ⟶ G) := fun N => GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have hf : ∀ n, IsFinite ((𝟙 G) ^ p ^ n : G ⟶ G).left := fun n => isFinite_pow G D _ (Nat.one_le_pow _ _ hp.out.pos)
  have hl := fun n => (flat_and_surjective_of_isFinite_grpEnd K G ((𝟙 G) ^ p ^ n)).1
  have hs := fun n => (flat_and_surjective_of_isFinite_grpEnd K G ((𝟙 G) ^ p ^ n)).2
  obtain ⟨hfin, e, he⟩ := mapDeg_eq_pow_mul_card K G ((𝟙 G) ^ p ^ 1)
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 h0
  rw [ringExpChar.eq K p] at he
  let M : Subgroup (Out.baseOver (Sp K) ⟶ G) := (IsMonHom.monoidHom ((𝟙 G) ^ p ^ 1 : G ⟶ G) _).ker
  haveI : Finite M := hfin
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := M)).1 fun g => ⟨1, Subtype.ext (by
    have h : g.1 ≫ (𝟙 G) ^ p ^ 1 = 1 := g.2
    rw [MonObj.comp_pow, Category.comp_id] at h
    exact h)⟩
  have hd : ∀ n, MapDeg ((𝟙 G) ^ p ^ n : G ⟶ G).left (p ^ (n * (e + k))) := fun n => by
    induction n with
    | zero =>
      simp only [pow_zero, pow_one, zero_mul]
      exact MapDeg.id_one _
    | succ n ih =>
      have h := mapDeg_comp _ _ he ih
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ← pow_mul, ← pow_add,
        show Nat.card {x : Out.baseOver (Sp K) ⟶ G // x ≫ (𝟙 G) ^ p ^ 1 = 1} = p ^ k from hk, ← pow_add,
        ← pow_add, add_comm 1 n] at h
      rwa [add_mul, _root_.one_mul]
  refine ⟨e + k, fun n S _ _ _ y H => ?_⟩
  rw [GrpTangent.mulN_eq_pow] at H
  have h := Scheme.Hom.finrank_of_isPullback _ _ _ _ H (⊥ : PrimeSpectrum K)
  rw [finrank_eq_of_mapDeg _ (hd n)] at h
  rw [← h, ← FiniteCover.rankAtStalk_bot]
  exact (Scheme.Hom.finrank_SpecMap_algebraMap K S _).symm

theorem exists_tower : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A], IsSemiAbelian A → (∀ N, 1 ≤ N → IsFinite (torsion A N).hom ∧ Flat (torsion A N).hom) → ∃ G : PDivGroup p O, Nonempty (G.TorsionTower A) := by
  intro p hp O _ _ A _ hA hf
  by_cases h0 : (p : O) = 0
  swap
  · exact RaynaudPDiv.exists_tower p O h0 A hA hf
  have := hA.comm
  have := hA.smooth
  have := hA.geomConnected
  let K := AlgebraicClosure (FractionRing O)
  have hi : Function.Injective (algebraMap O K) :=
    (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O _)
  let B := (Over.pullback (spMap (algebraMap O K))).obj A
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom _))
  have : GeometricallyConnected B.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom _))
  choose R _ _ y h1 h2 H using fun n : ℕ => RaynaudPDiv.exists_isPullback_torsion O A (p ^ n)
    (hf _ (Nat.one_le_pow _ _ hp.out.pos)).1 (hf _ (Nat.one_le_pow _ _ hp.out.pos)).2
  have h := fun n => AbelianPDiv.isUnivTorsion_of_isPullback (y n) (H n)
  obtain ⟨D⟩ := hA.fibres K (spMap (algebraMap O K))
  obtain ⟨d, hd⟩ := exists_finrank_torsion p K (by rw [← map_natCast (algebraMap O K), h0, map_zero]) B D
  have hk : ∀ n, Module.finrank K (K ⊗[O] R n) = p ^ (n * d) := fun n => by
    obtain ⟨y', h'⟩ := AbelianPDiv.exists_isPullback_baseChange (y n) (H n) K
    exact hd n _ y' h'
  have hr : ∀ n (q : PrimeSpectrum O), Module.rankAtStalk (R n) q = p ^ (n * d) := fun n q => by
    rw [← Module.rankAtStalk_eq_of_le_of_finite_of_flat (R n)
        (p := PrimeSpectrum.comap (algebraMap O K) ⊥) (q := q) ?_, ← Module.rankAtStalk_baseChange,
      Module.rankAtStalk_eq_finrank_of_free, hk n]
    · rfl
    · intro a ha
      have ha' : algebraMap O K a = 0 := ha
      rw [(map_eq_zero_iff _ hi).1 ha']
      exact zero_mem _
  choose r r1 r2 r3 using fun n : ℕ =>
    (h n).exists_res (h (n + 1)) (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := d
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := hr
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

end GlobalTheory.SemiAbelianTower
