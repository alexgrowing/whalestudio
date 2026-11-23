import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionMapExistsUniqueHomotopyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSuppSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedSectionsTateTwistResolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionMultiplicationChainMapStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CupGen
open ClsSpec

theorem sub_zero_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i; simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem aw_zero_left {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {m : ℤ} (hm : 0 + m = m)
    (hI : ∀ (s : ℤ) (U : Scheme.{0}), s < 0 → Subsingleton (Sec (I.X s) U))
    (α : Cochain ((chains R).obj E) I 0) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K m)
    (h : μ.IsAW hm α β γ) (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + m = w) (U : Scheme.{0}) (x : Sx E N U) :
    ev γ N w hw U x = μ.mul U 0 w w (zero_add w) (ev α 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β N w hw U x) := by
  rw [h N w hw U x, Finset.sum_eq_single 0]
  · subst hw
    have e1 : ((m * (((0 : Fin (N + 1)) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul]
    have e2 : x.sub ((0 : Fin (N + 1)) : ℕ) (N - ((0 : Fin (N + 1)) : ℕ)) (by simp) = x := sub_zero_full x (by omega)
    rw [e2]
    rfl
  · intro p _ hp
    have hp' : 0 < (p : ℕ) := Fin.pos_iff_ne_zero.2 hp
    haveI := hI (-((p : ℕ) : ℤ) + 0) U (by omega)
    rw [Subsingleton.elim (ev α p _ rfl U _) 0, map_zero, LinearMap.zero_apply, smul_zero]
  · intro h0; exact absurd (Finset.mem_univ _) h0

theorem factor_cochain {R : Type} [CommRing R] {E : Spc} {D C : Cx R} (ι : D ⟶ C)
    (hinj : ∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) {n : ℤ} (β : Cochain ((chains R).obj E) C n)
    (hβ : ∀ p s h U x, ∃ b, Sec.map (ι.f s) b = ev β p s h U x) :
    ∃ β' : Cochain ((chains R).obj E) D n, β'.comp (Cochain.ofHom ι) (add_zero n) = β := by
  choose b hb using hβ
  obtain ⟨β', hβ'⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (E := E) (I := D) (n := n) b (fun p s h V U g x => by
    apply hinj
    rw [← res_map, hb, hb, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.1])
  refine ⟨β', (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h U x => ?_⟩
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.2.2, hβ', hb]

theorem supp_twres (q : ℕ) [NeZero q] (i : ℤ) (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i))
    (hinj : ∀ n U, Function.Injective (Sec.map (ι.f n) (U := U)))
    (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) :
    ∃ e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (D.X 0) U, IsTwRes q i D e ∧
      ∀ U ζ, Sec.map (ι.f 0) (e U ζ) = resGen i ζ := GlobalTheory.T.supportedSections_tateTwist_resolution q i D ι hinj hD

theorem exists_unit_map (q : ℕ) [NeZero q] (i k : ℤ) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
    (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i))
    (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) :
    ∃ u : D ⟶ res _ (tw q k), ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (s : ℤ) (b : Sec (D.X s) U),
      Sec.map (u.f s) b = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b) := GlobalTheory.T.unitSection_multiplication_chainMap q i k μ D ι hD

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem root_mul (q : ℕ) [NeZero q] (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ) :
    cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧
      rootClass 0 ζ = one q (sch.obj X) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨α, hα, hαv⟩ := rootClass_spec i ζ
    obtain ⟨β, hβ, hβv⟩ := rootClass_spec j ζ
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) (twPair q i j) (E := sch.obj X) (rfl : (0 : ℤ) + 0 = 0 + 0)).1 α β
    have hc := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) (twPair q i j) (E := sch.obj X) (rfl : (0 : ℤ) + 0 = 0 + 0)).2 α β γ hγ
    change (twPair q i j).cup (sch.obj X) rfl (rootClass i ζ) (rootClass j ζ) = rootClass (i + j) ζ
    rw [← hα, ← hβ, hc, (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.2]
    refine ((GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q (i + j)) X).1 _ γ).1 ?_
    have e := hγ 0 0 (by simp) X (𝟙 X)
    rw [Finset.sum_eq_single 0 (fun p _ hp => absurd (Subsingleton.elim (α := Fin 1) p 0) hp) (fun h0 => absurd (Finset.mem_univ _) h0)] at e
    have e1 : (((0 : ℤ) * (((0 : Fin 1) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul] at e
    refine e.trans ?_
    have a1 := hαv X (𝟙 X)
    have b1 := hβv X (𝟙 X)
    rw [res_id] at a1 b1
    change (twPair q i j).mul X 0 0 0 (add_zero 0) (ev α.1 0 0 (by simp) X (𝟙 X)) (ev β.1 0 0 (by simp) X (𝟙 X)) = _
    rw [a1, b1]
    exact (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 X ζ
  · obtain ⟨α, hα, hαv⟩ := rootClass_spec 0 ζ
    have hE : Inv q (sch.obj X) := fun U ⟨x⟩ => unit_res (x : U ⟶ X) ζ.2.1
    rw [← hα]
    refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 _ hE α fun U x ξ => ?_
    refine (hαv U x).trans ?_
    exact (res_resGen (q := q) 0 (show U ⟶ X from x) ζ).trans (resGen_zero_eq _ _)

theorem one_mul_of_pair (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E) (n i : ℤ) (hn : 0 + n = n)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i))) (hμ : IsTwPair μ) (a : Ht q E n i) :
    μ.cup E hn (one q E) a = a := by
  obtain ⟨α, hα1, hαv⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).1 E hE
  obtain ⟨β, rfl⟩ := a.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) μ hn).1 α β
  rw [← hα1, (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) μ hn).2 α β γ hγ]
  obtain ⟨D, ι, hinj, hD⟩ := GlobalTheory.EtC.SuppSub.exists_supp_sub (ZMod q) (res _ (tw q i))
    (fun U => IsUnit (q : Γ(U, ⊤))) (fun V U g h => unit_res g h)
  obtain ⟨e, he, heι⟩ := supp_twres q i D ι hinj hD
  obtain ⟨u, hu⟩ := exists_unit_map q i i μ D ι hD
  have hom : Nonempty (Homotopy u ι) := ((GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i).2.2 e he).2 u ι fun U ζ => by
    rw [hu U ζ 0 (e U ζ), heι]
    exact hμ U ζ

  have hunit : ∀ (p : ℕ) (U : Scheme.{0}) (x : Sx E p U), IsUnit (q : Γ(U, ⊤)) :=
    fun p U x => hE U ⟨x.sub 0 0 (by omega)⟩
  obtain ⟨β', hβ'⟩ := factor_cochain ι hinj β.1 fun p s h U x =>
    (hD s U _).2 (loc_all fun V g => Or.inl (unit_res g (hunit p U x)))
  have hδ : δ n (n + 1) β' = 0 := by
    refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => hinj s U ?_
    rw [← (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2, ← δ_comp_ofHom, hβ', Cocycle.δ_eq_zero, ev_zero, ev_zero, smap_zero]
  set β'' : Cocycle ((chains (ZMod q)).obj E) D n := Cocycle.mk β' (n + 1) rfl hδ
  have hb : CohomologyClass.mk β = cpush _ ι n (CohomologyClass.mk β'') := by
    change _ = CohomologyClass.mk _
    congr 1
    exact Cocycle.ext hβ'.symm
  have hg : CohomologyClass.mk γ = cpush _ u n (CohomologyClass.mk β'') := by
    change _ = CohomologyClass.mk _
    congr 1
    refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun N w hw U x => ?_)
    change ev γ.1 N w hw U x = ev (β'.comp (Cochain.ofHom u) (add_zero n)) N w hw U x
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2, aw_zero_left μ hn (fun s U hs => (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 0) U).2.2.2 s hs)
      α.1 β.1 γ.1 hγ N w hw U x]
    refine ClsSpec.sep (ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 (hunit N U x)) fun V g hz => ?_)
    obtain ⟨ζ⟩ := hz
    rw [res_map, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β', hu V ζ w, ← hβ', (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2,
      μ.nat g, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1, res_map, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β', hαv V _ ζ]
  rw [hb, hg, ((GlobalTheory.EtC.ZcFun.main (ZMod q)).2.2.2.2 u ι hom _ n).2]

theorem main : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧ (∀ (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ), cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧ rootClass 0 ζ = one q (sch.obj X)) := by
  intro q _
  refine ⟨fun E hE => ?_, fun X ζ i j => root_mul q X ζ i j⟩
  intro n i a
  have key : ∀ (k : ℤ) (hk : i = k) (m : ℤ) (hm : 0 + n = m) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k))),
      IsTwPair μ → μ.cup E hm (one q E) a = a.cast (by omega) hk := by
    intro k hk m hm μ hμ
    subst hk
    obtain rfl : m = n := by omega
    exact one_mul_of_pair q E hE _ i hm μ hμ a
  exact key (0 + i) (by ring) (0 + n) rfl (twPair q 0 i) ((GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q 0 i).1)

end GlobalTheory.EtC.CupGen
