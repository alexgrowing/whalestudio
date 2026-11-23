import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSumSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.AdaptedBasis

private theorem isSemisimple_ringOfIntegers_action {E K V : Type} [Field E] [NumberField E] [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (r : 𝓞 E →+* Module.End K V) (a : 𝓞 E) : (r a).IsSemisimple := by
  have hi : IsIntegral ℤ a := RingOfIntegers.isIntegral a
  have hq : minpoly ℚ (algebraMap (𝓞 E) E a) = (minpoly ℤ a).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ E hi
  have hsep : (minpoly ℚ (algebraMap (𝓞 E) E a)).Separable := Algebra.IsSeparable.isSeparable ℚ _
  rw [hq] at hsep
  have hK := hsep.map (f := algebraMap ℚ K)
  rw [Polynomial.map_map,
    show (algebraMap ℚ K).comp (algebraMap ℤ ℚ) = algebraMap ℤ K from RingHom.ext_int _ _] at hK
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hK.squarefree ?_
  rw [Polynomial.aeval_map_algebraMap]
  have hz := Polynomial.aeval_algHom_apply r.toIntAlgHom a (minpoly ℤ a)
  rw [minpoly.aeval, map_zero] at hz
  exact hz

private theorem exists_ringHom_eq_eigenvalue {R K V : Type} [CommRing R] [Field K] [AddCommGroup V] [Module K V]
    (r : R →+* Module.End K V) {v : V} (hv : v ≠ 0) (χ : R → K) (h : ∀ a, r a v = χ a • v) :
    ∃ t : R →+* K, ∀ a, t a = χ a := by
  have inj : Function.Injective fun c : K => c • v := smul_left_injective K hv
  refine ⟨{ toFun := χ
            map_one' := inj ?_
            map_mul' := fun a b => inj ?_
            map_zero' := inj ?_
            map_add' := fun a b => inj ?_ }, fun _ => rfl⟩
  · show χ 1 • v = (1 : K) • v
    rw [← h, map_one, Module.End.one_apply, one_smul]
  · show χ (a * b) • v = (χ a * χ b) • v
    rw [← h, map_mul, Module.End.mul_apply, h b, map_smul, h a, smul_smul, mul_comm]
  · show χ 0 • v = (0 : K) • v
    rw [← h, map_zero, LinearMap.zero_apply, zero_smul]
  · show χ (a + b) • v = (χ a + χ b) • v
    rw [← h, map_add, LinearMap.add_apply, h a, h b, add_smul]

theorem exists_eigenbasis {E K V : Type} [Field E] [NumberField E] [Field K] [IsAlgClosed K] [CharZero K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] (r : 𝓞 E →+* Module.End K V) :
    ∃ (g : ℕ) (b : Module.Basis (Fin g) K V) (ty : Fin g → (𝓞 E →+* K)), ∀ a j, r a (b j) = ty j a • b j := by
  classical
  have hc : ∀ a c : 𝓞 E, Commute (r a) (r c) := fun a c => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ (a c : 𝓞 E) (z : K),
      Set.MapsTo (r a) ((r c).maxGenEigenspace z) ((r c).maxGenEigenspace z) :=
    fun a c z => Module.End.mapsTo_maxGenEigenspace_of_comm (hc c a) z
  let W : (𝓞 E → K) → Submodule K V := fun χ => ⨅ a, (r a).maxGenEigenspace (χ a)
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a => r a) hmaps)
      (Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun a => r a) hmaps
        fun a => Module.End.iSup_maxGenEigenspace_eq_top (r a))
  let B := hint.collectedBasis fun χ => Module.finBasis K (W χ)
  have : Finite (Σ χ, Fin (Module.finrank K (W χ))) := Module.Finite.finite_basis B
  let _ : Fintype (Σ χ, Fin (Module.finrank K (W χ))) := Fintype.ofFinite _
  have heig : ∀ s : (Σ χ, Fin (Module.finrank K (W χ))), ∀ a, r a (B s) = s.1 a • B s := by
    intro s a
    have hm : B s ∈ W s.1 := hint.collectedBasis_mem _ s
    have hm' : B s ∈ (r a).maxGenEigenspace (s.1 a) := (Submodule.mem_iInf _).1 hm a
    rw [(isSemisimple_ringOfIntegers_action r a).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hm'
    exact Module.End.mem_eigenspace_iff.1 hm'
  choose t ht using fun s : (Σ χ, Fin (Module.finrank K (W χ))) =>
    exists_ringHom_eq_eigenvalue r (B.ne_zero s) s.1 (heig s)
  let e := Fintype.equivFin (Σ χ, Fin (Module.finrank K (W χ)))
  refine ⟨Fintype.card _, B.reindex e, fun j => t (e.symm j), fun a j => ?_⟩
  rw [Module.Basis.reindex_apply, ht, heig]

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap IsUnivChart)

variable {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
  {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

include hx in

theorem exists_tangent_action {O : Type} [CommRing O] (act : OAct O G) :
    ∃ r : O →+* Module.End k (Fin n → k), ∀ a c, tvec (x := x) (r a c) = tvec (x := x) c ≫ act.act a := by
  have : ∀ a, IsMonHom (act.act a) := act.hom
  have hadd : ∀ a c, Chart.tmap hx (act.act (a + c)) = Chart.tmap hx (act.act a) + Chart.tmap hx (act.act c) :=
    fun a c => LinearMap.ext fun v => Chart.tvec_inj hx (by
      rw [LinearMap.add_apply, Chart.tvec_add hx, Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, act.add,
        MonObj.comp_mul])
  refine ⟨{ toFun := fun a => Chart.tmap hx (act.act a)
            map_one' := ?_
            map_mul' := fun a c => ?_
            map_zero' := ?_
            map_add' := hadd }, fun a c => Chart.tvec_tmap hx _ c⟩
  · refine LinearMap.ext fun v => Chart.tvec_inj hx ?_
    show tvec (x := x) (Chart.tmap hx (act.act 1) v) = tvec (x := x) v
    rw [Chart.tvec_tmap, act.one, Category.comp_id]
  · refine LinearMap.ext fun v => Chart.tvec_inj hx ?_
    show tvec (x := x) (Chart.tmap hx (act.act (a * c)) v) =
      tvec (x := x) (Chart.tmap hx (act.act a) (Chart.tmap hx (act.act c) v))
    rw [Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, mul_comm a c, act.mul, Category.assoc]
  · have h00 := hadd 0 0
    rw [add_zero] at h00
    show Chart.tmap hx (act.act 0) = 0
    exact add_left_cancel (by rw [add_zero]; exact h00.symm :
      Chart.tmap hx (act.act 0) + Chart.tmap hx (act.act 0) = Chart.tmap hx (act.act 0) + 0)

private theorem tvec_sum' {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    ∀ {N : ℕ} (f : Fin N → Fin n → k), (List.ofFn fun i => tvec (x := x) (f i)).prod = tvec (x := x) (∑ i, f i) := by
  have h0 : tvec (x := x) 0 = 1 := by
    have h := Chart.tvec_add hx (0 : Fin n → k) 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  intro N f
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [List.ofFn_succ, List.prod_cons, ih (fun i => f i.succ), Fin.sum_univ_succ, Chart.tvec_add hx]

include hx in

theorem isLieComb_tvec_iff {N : ℕ} (b : Fin N → Fin n → k) (c : Fin n → k) (d : Fin N → k) :
    IsLieComb d (fun i => tvec (x := x) (b i)) (tvec (x := x) c) ↔ c = ∑ i, d i • b i := by
  unfold IsLieComb
  have hs : ∀ i, tvec (x := x) (d i • b i) = Chart.spMap (scaleD (d i)) ≫ tvec (x := x) (b i) :=
    fun i => Chart.tvec_smul hx (d i) (b i)
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun i => tvec (x := x) (d i • b i) := by
      funext i
      apply Over.OverMorphism.ext
      rw [hu i, hs i, Over.comp_left]
      all_goals rfl
    subst hu'
    rw [tvec_sum' hx] at hw
    exact Chart.tvec_inj hx hw
  · rintro rfl
    refine ⟨fun i => tvec (x := x) (d i • b i), fun i => ?_, (tvec_sum' hx _).symm⟩
    show (tvec (x := x) (d i • b i)).left = spMap (epsScaleR (d i)) ≫ (tvec (x := x) (b i)).left
    rw [hs i, Over.comp_left]
    all_goals rfl

end GlobalTheory.AdaptedBasis

open ReciprocityTheory.ChartRestriction.G.Chart (tvec) in

theorem GlobalTheory.exists_adapted_lieBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (act : OAct (𝓞 E) G) (ρ : K), Smooth G.hom → DetCond D act (𝟙 (Sp K)) ρ → ∃ (g : ℕ) (v : Fin g → (epsR K ⟶ G)) (ty : Fin g → (𝓞 E →+* K)), IsLieBasis v ∧ (∀ τ : 𝓞 E →+* K, (τ H.rt = ρ → Nat.card {i // ty i = τ} = D.p) ∧ (τ H.rt ≠ ρ → Nat.card {i // ty i = τ} = D.q)) ∧ ∀ a j, IsLieComb (fun i => Matrix.diagonal (fun i => ty i a) i j) v (v j ≫ act.act a) := by
  intro E _ _ _ H D K _ _ _ G _ _ act ρ hsm hdet
  unfold DetCond at hdet
  obtain ⟨n, x, hx⟩ := Chart.univChartLoc G
  obtain ⟨r, hr⟩ := GlobalTheory.AdaptedBasis.exists_tangent_action hx act
  obtain ⟨g, b, ty, hb⟩ := GlobalTheory.AdaptedBasis.exists_eigenbasis (E := E) r
  have : ∀ a, IsMonHom (act.act a) := act.hom
  have hT : ∀ w : epsR K ⟶ G, IsTangent w ↔ Chart.IsTan w := by
    intro w
    unfold IsTangent Chart.IsTan
    have e1 : (Chart.spMap (Chart.fstD K)).left = spMap (TrivSqZeroExt.fstHom K K K).toRingHom := rfl
    have e2 : (Chart.sp (R₀ := K) K).hom = 𝟙 _ := by
      first
      | rfl
      | (unfold Chart.sp; simp)
      | (simp [Chart.sp, Algebra.id.map_eq_id])
    constructor
    · intro h
      apply Over.OverMorphism.ext
      rw [Over.comp_left, Chart.one_left', e1, h, e2, Category.id_comp]
    · intro h
      have h' := congrArg Over.Hom.left h
      rw [Over.comp_left, Chart.one_left', e1, e2, Category.id_comp] at h'
      exact h'
  have hcomb : ∀ a j, IsLieComb (fun i => Matrix.diagonal (fun i => ty i a) i j)
      (fun i => tvec (x := x) (b i)) (tvec (x := x) (b j) ≫ act.act a) := by
    intro a j
    rw [← hr, hb, GlobalTheory.AdaptedBasis.isLieComb_tvec_iff hx]
    simp [Matrix.diagonal_apply, ite_smul]
  have hex : ∀ w : epsR K ⟶ G, Chart.IsTan w → ∃ c, w = tvec (x := x) c := by
    intro w hw
    exact ⟨Chart.tcoord hx w hw, Chart.tcoord_spec hx w hw⟩
  have hbasis : IsLieBasis (fun i => tvec (x := x) (b i)) := by
    unfold IsLieBasis
    refine ⟨fun i => (hT _).2 (Chart.isTan_tvec hx (b i)), fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := hex w ((hT w).1 hw)
    refine ⟨fun i => b.repr c i, ?_, fun e he => ?_⟩
    · show IsLieComb (fun i => b.repr c i) (fun i => tvec (x := x) (b i)) (tvec (x := x) c)
      rw [GlobalTheory.AdaptedBasis.isLieComb_tvec_iff hx]
      exact (b.sum_repr c).symm
    · have he' : IsLieComb e (fun i => tvec (x := x) (b i)) (tvec (x := x) c) := he
      rw [GlobalTheory.AdaptedBasis.isLieComb_tvec_iff hx] at he'
      funext i
      rw [he', b.repr_sum_self]
  have heig : ∀ i a, ((fun i => tvec (x := x) (b i)) i ≫ act.act a).left =
      spMap (epsScale (ty i a)) ≫ ((fun i => tvec (x := x) (b i)) i).left := by
    intro i a
    show (tvec (x := x) (b i) ≫ act.act a).left = spMap (epsScale (ty i a)) ≫ (tvec (x := x) (b i)).left
    rw [← hr, hb, Chart.tvec_smul hx, Over.comp_left]
    all_goals rfl
  have hmult := GlobalTheory.lieMult_of_eigenbasis K (𝓞 E) G act g _ ty hsm hbasis heig
  refine ⟨g, fun i => tvec (x := x) (b i), ty, hbasis, fun τ => ⟨fun h1 => ?_, fun h2 => ?_⟩, hcomb⟩
  · exact ((GlobalTheory.DetExtend.lieMult_iff_finrank act hx τ _).1 (hmult τ)).symm.trans
      ((GlobalTheory.DetExtend.lieMult_iff_finrank act hx τ _).1 ((hdet τ).1 h1))
  · exact ((GlobalTheory.DetExtend.lieMult_iff_finrank act hx τ _).1 (hmult τ)).symm.trans
      ((GlobalTheory.DetExtend.lieMult_iff_finrank act hx τ _).1 ((hdet τ).2 h2))
